% считывание из файла
load_connections(File) :-
    retractall(connection(_, _, _)),
    open(File, read, Stream),
    load_facts(Stream),
    close(Stream).

% загрузка фактов
load_facts(Stream) :-
    read(Stream, Term),
    ( Term == end_of_file -> true
    ; assert(Term),
      load_facts(Stream)
    ).

% функция, которая вызывает для упрощения все остальные функции
reduce_circuit(Node1, Node2, Resistance) :-
    write("Start: "),
    print_all(0),
    simplify_circuit(0, Node1, Node2),
    connection1(Node1, Node2, R), Resistance is R, !.

% неориентированный граф
connection1(X, Y, L) :- connection(X, Y, L); connection(Y, X, L).

% подсчет числа соединений
number_of_connection(N) :- 
    findall(1, connection(_, _, _), L), length(L, N).

% для вывода все текущих соединений
print_all(L) :-
    findall([X, Y, R], connection(X, Y, R), L1), 
    write(L), write("\n"), write(L1), write("\n"), !.

% превращает все факты в список
make_list(L) :- findall([X, Y, R], connection(X, Y, R), L), !.

% обработка цепи
simplify_circuit(L, Node1, Node2) :-
    % меняем схему, пока в ней не останется одно соединение
    number_of_connection(N),
    N > 1,
    write("\nTransformation:   "),
    ((apply_series(Node1, Node2), !, write("series\n");
    apply_parallel, !, write("parallel\n");
    apply_isolated(Node1, Node2), !, write("isolated\n");
    apply_loop, !, write("loop\n")); 
    make_list(List), % сохранение текущей конфигурации для восстановления по бектрекингу
    !, apply_wye_delta(List, Node1, Node2), write("delta\n")),
    L1 is L + 1,
    write("Iteration:   "),
    print_all(L1),
    simplify_circuit(L1, Node1, Node2).

simplify_circuit(_, _, _) :- !.

% удаление факта
remove(X, Y, R) :- 
    (connection(X, Y, R), !, retract(connection(X, Y, R)));
    (connection(Y, X, R), retract(connection(Y, X, R))).

% последовательное соединение
apply_series(Node1, Node2) :-
    connection1(X, Y, R1),
    connection1(Y, Z, R2),
    Y \= Node1, Y \= Node2,
    dif(X, Z),
    findall(K, connection1(Y, K, _), L),
    length(L, 2),
    R is (R1 + R2),
    remove(X, Y, R1),
    remove(Y, Z, R2),
    assert(connection(X, Z, R)), !.

% параллельное соединение
apply_parallel :-
    connection1(X, Y, R1),
    remove(X, Y, R1),
    (connection1(X, Y, R2),
    (R1 =:= 0,
    assert(connection(X, Y, R1)),
    remove(X, Y, R2), !;
    R2 =:= 0, !;
    R is (1 / ((1 / R1) + (1 / R2))),
    remove(X, Y, R2),
    assert(connection(X, Y, R)), !
    )
    ;
    assert(connection(X, Y, R1)), fail). % поиск другого параллельного соединения

% проверка, является ли вершина изолированной
is_isolated(V) :-
    findall(V1, connection1(V, V1, _), Neighbors),
    length(Neighbors, 1).

% удаление изолированной
apply_isolated(Node1, Node2):-
    connection1(V, W, R),
    V \= Node1, V \= Node2,
    is_isolated(V),
    remove(V, W, R), !.

% удаление петли
apply_loop :-
    connection(X, X, _), 
    retract(connection(X, X, _)), !.

assert_all([]).
assert_all([[X, Y, R] | T]) :- assert(connection(X, Y, R)), assert_all(T).

remove_all([]) :- !.
remove_all([[X, Y, R] | T]) :- remove(X, Y, R), remove_all(T).

% отдельная обработка для "пустой" звезды
change_connections(A, B) :- 
    findall([A, Y, R], (connection1(A, Y, R), dif(Y, B)), L),
    remove_all(L),
    findall([B, Y1, R1], member([_, Y1, R1], L), L1),
    assert_all(L1).

% преобразование звезда-треуголник
apply_wye_delta(List, Node1, Node2):-
    find_stars(Set, Node1, Node2),
    member(V, Set), % вот тут бектрекинг для преобразования звезда-треуголник 
    retractall(connection(_, _, _)),
    assert_all(List),
    connection1(V, X, R1),
    connection1(V, Y, R2),
    connection1(V, Z, R3),
    dif(X, Y), dif(Y, Z), dif(X, Z), 
    dif(X, V), dif(Y, V), dif(Z, V),
    ( % обработка "пустой" звезды
    Tmp is R1 * R2 * R3, Tmp =:= 0,
    (
    R1 =:= 0,
    remove(X, V, R1),
    change_connections(V, X);
    R2 =:= 0,
    remove(Y, V, R2),
    change_connections(V, Y);
    remove(Z, V, R3),
    change_connections(V, Z)
    )
    ;
    wye_to_delta(R1, R2, R3, R11, R22, R33), 
    remove(V, X, R1),
    remove(V, Y, R2),
    remove(V, Z, R3),
    assert(connection(Y, Z, R11)),
    assert(connection(X, Z, R22)),
    assert(connection(X, Y, R33))
    ).

% проверка, что соединений не больше трех
check_delta(V, X, Y, Z) :-
    connection1(V, Tmp, _),
    dif(X, Tmp), dif(Y, Tmp), dif(Z, Tmp), !.

set([], []).
set([H|T], X):- member(H, T), !, set(T, X).
set([H|T], [H|X]):- set(T, X).

% поиск всех вершин для преобразования звезда-треугольник
find_stars(Set, Node1, Node2) :-
    findall(V,
    (
    connection1(V, X, _),
    connection1(V, Y, _),
    connection1(V, Z, _),
    V \= Node1, V \= Node2,
    dif(X, Y), dif(Y, Z), dif(X, Z),
    dif(X, V), dif(Y, V), dif(Z, V), not(check_delta(V, X, Y, Z))), 
    SetTmp),
    set(SetTmp, Set), !.

% вычисление новых сопротивлений в преобразовании звезда-треуголник
wye_to_delta(R1, R2, R3, R11, R22, R33) :-
    Denom is ((R1 * R2) + (R1 * R3) + (R2 * R3)),
    R11 is (Denom / R1),
    R22 is (Denom / R2),
    R33 is (Denom / R3).

% основная функция
main(Node1, Node2, Resistance) :-
    (   exists_file("connections.txt")
    ->  (   load_connections("connections.txt"),
            (   reduce_circuit(Node1, Node2, Resistance)
            ->  format('Total resistance between ~w and ~w: ~2f~n', [Node1, Node2, Resistance])
            ;   writeln("\nCan not simplify the circuit!!!!!!!!!!!"),
                fail
            )
        )
    ;   writeln("No file connections.txt was found!"),
        fail
    ).
