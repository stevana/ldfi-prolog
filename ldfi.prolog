:- set_prolog_flag(answer_write_options, [max_depth(0)]).

% The SUTs are in separate files:

:- ensure_loaded(round1).
:- ensure_loaded(round2).
:- ensure_loaded(round3).
:- ensure_loaded(round4).
:- ensure_loaded(round5).

% ----------------------------------------------------------------------

% To find the lineage of successful runs we use a meta-interpreter from the "The
% Art of Prolog"" book, p. 326.

% solve(Goal, Tree) - Tree is a proof tree for Goal given the program defined by
% clause/2.
solve(true, true) :- !.
solve((A, B), (ProofA, ProofB)) :-
    !,
    solve(A, ProofA),
    solve(B, ProofB).
solve(A, (A :- builtin)) :-
    builtin(A), !, A.
solve(A, (A :- Proof)) :-
    clause(A, B), solve(B, Proof).

builtin((\+ _)).
builtin(succ(_, _)).

% solve(log(c, 'Hello world!', 3), B).

% log(c, 'Hello world!', 3) :-
%   succ(2, 3):-builtin,
% log(c, 'Hello world!', 2) :-
%   succ(1, 2):-builtin
%   bcast(a, 'Hello world!', 1) :- true
% node(a, c, 1):-true,
%   clock(a, c, 1):-true
%   clock(c, c, 2):-true

clocks(true, []).
clocks((S, T), Cs) :-
    clocks(S, Cs1),
    clocks(T, Cs2),
    append(Cs1, Cs2, Cs).
clocks(_ :- builtin, []).
clocks(clock(From, From, _) :- true, []) :- !.
clocks(clock(From, To, Time) :- true, [clock(From, To, Time)|Cs]) :-
    possible_crashes(From, Time, Cs).
clocks(_ :- Proof, Cs) :-
    clocks(Proof, Cs).

possible_crashes(From, Time, Cs) :-
    % We should enum from 1 (not sure why the enum from 0 in the paper), and the
    % precondition should filter those crashes out, but I can't get that to
    % work...
    enum_from_to(2, Time, Ts),
    crashes_helper(From, Ts, Cs).

crashes_helper(_, [], []).
crashes_helper(Node, [Time|Times], [crash(Node, Time)|Cs]) :-
    crashes_helper(Node, Times, Cs).

enum_from_to(From, To, []) :-
    From > To,
    !.
enum_from_to(0, 0, [0]).
enum_from_to(From, To, [From|Xs]) :-
    succ(From, SuccFrom),
    enum_from_to(SuccFrom, To, Xs).

% ----------------------------------------------------------------------

% Import SAT solver.
:- ensure_loaded(sat).

test_sat(X, Y) :-
    sat(X*Y + X*Z), labeling([X,Y,Z]).
%?- test_sat(X, Y).
%@ X = 1,
%@ Y = 0 ;
%@ X = Y, Y = 1 ;
%@ X = Y, Y = 1.

%    write is stable
%     /        \
%   stored      stored
%   on rep A    on rep B
%     | \      /  |
%     |  \    /   |
%    bcast1   bcast2
%     |         |
%    client   client

% What would have to go wrong?
% (RepA OR bcast1)
% AND (RepA OR bcast2)
% AND (RepB OR bcast2)
% AND (RepB OR bcast1)
test_sat2(RepA, RepB, Bcast1, Bcast2) :-
    min_sat((RepA + Bcast1) * (RepA + Bcast2) * (RepB + Bcast2) * (RepB + Bcast1),
            [RepA, RepB, Bcast1, Bcast2]).
%?- test_sat2(RepA, RepB, Bcast1, Bcast2).
%@ RepA = RepB, RepB = 0,
%@ Bcast1 = Bcast2, Bcast2 = 1 ;
%@ RepA = RepB, RepB = 1,
%@ Bcast1 = Bcast2, Bcast2 = 0.

% ----------------------------------------------------------------------
% Round 1

s1(Node, Pload, Time, Cs) :-
    % XXX: Where should pre be asserted?
    % pre(Node, Pload),
    solve(post1(Node, Pload, Time), P),
    clocks(P, Cs).

%?- s1(b, 'Hello world!', 4, Cs).
%@ Cs = [clock(a,b,1)] ;
%@ Cs = [].

% There's exactly one fault that will cause `post1(b, 'Hello world', 4)` to
% fail. We can verify this by commenting out `clock(a, b, 1)` and running
% `solve(post1(b, 'Hello world!', 4))`.

% Temporarily remove the `clock(a, b, 1)` fact and make sure that the
% post-condition is false:

:- dynamic clock/3.

test_round1 :-
    retract(clock(a, b, 1)),
    ( solve(post1(b, 'Hello world!', 4), _) -> assert(clock(a, b, 1))
    ; assert(clock(a, b, 1)), fail
    ).

% ----------------------------------------------------------------------
% Round 2

s2(Node, Pload, Time, Cs) :-
    % XXX: Where should pre be asserted?
    % pre(Node, Pload),
    solve(post2(Node, Pload, Time), P),
    clocks(P, Cs).
%?- s2(b, 'Hello world!', 4, Cs).
%@ Cs = [clock(a,b,1)] ;
%@ Cs = [] ;
%@ Cs = [clock(a,b,1),clock(a,b,2),crash(a,2)] ;
%@ Cs = [clock(a,b,1)] ;
%@ Cs = [clock(a,b,2),crash(a,2)] ;
%@ Cs = [] ;
%@ Cs = [clock(a,b,1),clock(a,b,2),crash(a,2),clock(a,b,3),crash(a,2),crash(a,3)] ;
%@ Cs = [clock(a,b,1),clock(a,b,2),crash(a,2)] ;
%@ Cs = [clock(a,b,1),clock(a,b,3),crash(a,2),crash(a,3)] ;
%@ Cs = [clock(a,b,1)] ;
%@ Cs = [clock(a,b,2),crash(a,2),clock(a,b,3),crash(a,2),crash(a,3)] ;
%@ Cs = [clock(a,b,2),crash(a,2)] ;
%@ Cs = [clock(a,b,3),crash(a,2),crash(a,3)] ;
%@ Cs = [] .

vars(clock(From, To, Time), S) :-
    format(string(S), "O~w~w~w", [From, To, Time]).
vars(crash(From, Time), S) :-
    format(string(S), "C~w~w", [From, Time]).

mapvars([], []).
mapvars([X|Xs], [V|Vs]) :-
    vars(X, V),
    mapvars(Xs, Vs).

sum([], []).
sum([Xs|Xss], [+(Vs)|Ss]) :-
    mapvars(Xs, Vs),
    sum(Xss, Ss).

isEmpty([]).

cnf(Xss, *(Zss)) :-
    exclude(isEmpty, Xss, Yss),
    sum(Yss, Zss).

round1(Cnf) :-
    findall(Cs, s1(b, 'Hello world!', 4, Cs), Css),
    cnf(Css, Cnf).

round2(Cnf) :-
    findall(Cs, s2(b, 'Hello world!', 4, Cs), Css),
    cnf(Css, Cnf).
%?- round2(Cnf).
%@ Cnf = *([+[Oab1],+[Oab1,Oab2,Ca2],+[Oab1],+[Oab2,Ca2],+[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],+[Oab1,Oab2,Ca2],+[Oab1,Oab3,Ca2,Ca3],+[Oab1],+[Oab2,Ca2,Oab3,Ca2,Ca3],+[Oab2,Ca2],+[Oab3,Ca2,Ca3]]).

unique_vars(Css, Vars) :-
    flatten(Css, Ds),
    sort(Ds, Sorted),
    maplist(vars, Sorted, Vars).

unique_vars2(Vars) :-
    findall(Cs, s2(b, 'Hello world!', 4, Cs), Css),
    unique_vars(Css, Vars).

%?- unique_vars2(Vars).
%@ Vars = [Ca2,Ca3,Oab1,Oab2,Oab3].

sat_round2(Oab1, Oab2, Oab3, Ca2, Ca3) :-
    min_sat(% No message omissions after time 2:
        ~Oab3 *
        % Max one crash:
        ((~Ca2 * ~Ca3) +
          (Ca2 * ~Ca3) +
         (~Ca2 * Ca3)) *
        % The below formula is copy-pasted from `round2(Cnf)`:
        *([+[Oab1], +[Oab1,Oab2,Ca2], +[Oab1], +[Oab2,Ca2],
        +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3],
        +[Oab1], +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3]]),
        [Oab1, Oab2, Oab3, Ca2, Ca3]).

%?- sat_round2(Oab1, Oab2, Oab3, Ca2, Ca3).
%@ Oab1 = Ca2, Ca2 = 1,
%@ Oab2 = Oab3, Oab3 = Ca3, Ca3 = 0.

% The above, Oab1 = Ca2 = 1, is the minimal counterexample from the paper.

% Ca2 means node A crashes at time 2, which we can simulate by removing all
% `clock(a, Node, U)` facts, where Node is any node and U >= 2.

:- use_module(library(clpfd)).

crash_clocks(Node, Time, Clocks) :-
    U #>= Time,
    findall(clock(Node, OtherNode, U), clock(Node, OtherNode, U), Clocks).

test_round2 :-
    retract(clock(a, b, 1)),
    crash_clocks(a, 2, CrashClocks),
    maplist(retract, CrashClocks),
    ( solve(post2(b, 'Hello world!', 4), _) -> assert(clock(a, b, 1)),
                                               maplist(assert, CrashClocks)
    ; assert(clock(a, b, 1)),
      maplist(assert, CrashClocks),
      fail
    ).

% ----------------------------------------------------------------------
% Round 3

s3(Node, Pload, Time, Cs) :-
    % XXX: Where should pre be asserted?
    % pre(Node, Pload),
    solve(post3(Node, Pload, Time), P),
    clocks(P, Cs).

round3(Cnf) :-
    findall(Cs, s3(b, 'Hello world!', 4, Cs), Css),
    cnf(Css, Cnf).

unique_vars3(Vars) :-
    findall(Cs, s3(b, 'Hello world!', 4, Cs), Css),
    unique_vars(Css, Vars).
%?- unique_vars3(Vars).
%@ Vars = [Ca2,Ca3,Cc2,Cc3,Oab1,Oab2,Oab3,Oac1,Ocb1,Ocb2,Ocb3].

sat_round3(Oab1, Oab2, Oab3, Ca2, Ca3, Ocb1, Ocb2, Ocb3, Cc2, Cc3) :-
    min_sat(% Max one crash:
        ((~Ca2 * ~Ca3 * ~Cc2 * ~Cc3) +
         (Ca2 * ~Ca3 * ~Cc2 * ~Cc3) +
         (~Ca2 * Ca3 * ~Cc2 * ~Cc3) +
         (~Ca2 * ~Ca3 * Cc2 * ~Cc3) +
         (~Ca2 * ~Ca3 * ~Cc2 * Cc3)
         ) *
        % No message loss after logical time 2:
        (~Oab3 * ~Ocb3) *

        % The following is copy pasted output from `round3`:
        *([+[Oab1], +[Oab1],
        +[Oab1], +[Oab1,Oab2,Ca2], +[Oab1], +[Oab2,Ca2], +[Oab1,Oab2,Ca2],
        +[Oab1], +[Oab2,Ca2], +[Oab1], +[Oab1], +[Oab1,Oab2,Ca2], +[Oab1],
        +[Oab2,Ca2], +[Oab1,Oab2,Ca2], +[Oab1], +[Oab2,Ca2],
        +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3],
        +[Oab1], +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3],
        +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3],
        +[Oab1], +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3],
        +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3],
        +[Oab1], +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3],
        +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3],
        +[Oab1], +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3],
        +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3],
        +[Oab1], +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3],
        +[Oab1], +[Oac1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oac1,Ocb1,Ocb2,Cc2],
        +[Oac1,Ocb1,Ocb3,Cc2,Cc3], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac1,Ocb2,Cc2], +[Oac1,Ocb3,Cc2,Cc3], +[Oac1],
        +[Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb1,Ocb2,Cc2], +[Ocb1,Ocb3,Cc2,Cc3],
        +[Ocb1], +[Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb2,Cc2], +[Ocb3,Cc2,Cc3]]),
        [Oab1, Oab2, Oab3, Ca2, Ca3, Ocb1, Ocb2, Ocb3, Cc2, Cc3]).

%?- sat_round3(Oab1, Oab2, Oab3, Ca2, Ca3, Ocb1, Ocb2, Ocb3, Cc2, Cc3).
% false.

% There's no counterexample for this round.

% ------------------------------------------------------------------------
% Round 4

s4(Node, Pload, Time, Cs) :-
    % XXX: Where should pre be asserted?
    % pre(Node, Pload),
    solve(post4(Node, Pload, Time), P),
    clocks(P, Cs).

round4(Cnf, Time) :-
    findall(Cs, s4(b, 'Hello world!', Time, Cs), Css),
    cnf(Css, Cnf).

unique_vars4(Vars, Time) :-
    findall(Cs, s4(b, 'Hello world!', Time, Cs), Css),
    unique_vars(Css, Vars).
%?- unique_vars4(V, 4).
%@V = [Ca2,Cb2,Cc2,Cc3,Oab1,Oab2,Oac1,Oac2,Obc1,Obc2,Ocb1,Ocb2,Ocb3].

sat_round4(Oab1, Oab2, Oac1, Oac2, Obc1, Obc2, Ocb1, Ocb2, Ocb3, Ca2, Cb2, Cc2, Cc3) :-
    min_sat(% Max one crash:
        ((~Ca2 * ~Cb2 * ~Cc2 * ~Cc3) +
         (Ca2 * ~Cb2 * ~Cc2 * ~Cc3) +
         (~Ca2 * Cb2 * ~Cc2 * ~Cc3) +
         (~Ca2 * ~Cb2 * Cc2 * ~Cc3) +
         (~Ca2 * ~Cb2 * ~Cc2 * Cc3)
        ) *
        % No message loss after logical time 2:
        (~Ocb3) *

        % round4(Cnf, 4):
        *([+[Oab1], +[Oab1,Oab2,Ca2], +[Oab1], +[Oab2,Ca2], +[Oab1],
        +[Oac1,Ocb1,Ocb2,Cc2], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2], +[Oac1],
        +[Ocb1,Ocb2,Cc2], +[Ocb1], +[Ocb2,Cc2], +[Oab1],
        +[Oac1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oac1,Ocb1,Ocb2,Cc2],
        +[Oac1,Ocb1,Ocb3,Cc2,Cc3], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac1,Ocb2,Cc2], +[Oac1,Ocb3,Cc2,Cc3], +[Oac1],
        +[Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb1,Ocb2,Cc2], +[Ocb1,Ocb3,Cc2,Cc3],
        +[Ocb1], +[Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb2,Cc2], +[Ocb3,Cc2,Cc3],
        +[Oab1,Oab2,Ca2], +[Oab1], +[Oab2,Ca2],
        +[Oac1,Oac2,Ca2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac1,Oac2,Ca2,Ocb1,Ocb2,Cc2], +[Oac1,Oac2,Ca2,Ocb1,Ocb3,Cc2,Cc3],
        +[Oac1,Oac2,Ca2,Ocb1], +[Oac1,Oac2,Ca2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac1,Oac2,Ca2,Ocb2,Cc2], +[Oac1,Oac2,Ca2,Ocb3,Cc2,Cc3],
        +[Oac1,Oac2,Ca2], +[Oac1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac1,Ocb1,Ocb2,Cc2], +[Oac1,Ocb1,Ocb3,Cc2,Cc3], +[Oac1,Ocb1],
        +[Oac1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oac1,Ocb2,Cc2], +[Oac1,Ocb3,Cc2,Cc3],
        +[Oac1], +[Oac2,Ca2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac2,Ca2,Ocb1,Ocb2,Cc2], +[Oac2,Ca2,Ocb1,Ocb3,Cc2,Cc3],
        +[Oac2,Ca2,Ocb1], +[Oac2,Ca2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac2,Ca2,Ocb2,Cc2], +[Oac2,Ca2,Ocb3,Cc2,Cc3], +[Oac2,Ca2],
        +[Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb1,Ocb2,Cc2], +[Ocb1,Ocb3,Cc2,Cc3],
        +[Ocb1], +[Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb2,Cc2], +[Ocb3,Cc2,Cc3],
        +[Oab1], +[Oab1,Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2],
        +[Oab1,Obc1,Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3], +[Oab1,Obc1,Obc2,Cb2,Ocb1],
        +[Oab1,Obc1,Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc1,Obc2,Cb2,Ocb2,Cc2], +[Oab1,Obc1,Obc2,Cb2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc1,Obc2,Cb2], +[Oab1,Obc1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc1,Ocb1,Ocb2,Cc2], +[Oab1,Obc1,Ocb1,Ocb3,Cc2,Cc3],
        +[Oab1,Obc1,Ocb1], +[Oab1,Obc1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc1,Ocb2,Cc2], +[Oab1,Obc1,Ocb3,Cc2,Cc3], +[Oab1,Obc1],
        +[Oab1,Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc2,Cb2,Ocb1,Ocb2,Cc2], +[Oab1,Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3],
        +[Oab1,Obc2,Cb2,Ocb1], +[Oab1,Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc2,Cb2,Ocb2,Cc2], +[Oab1,Obc2,Cb2,Ocb3,Cc2,Cc3],
        +[Oab1,Obc2,Cb2], +[Oab1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oab1,Ocb1,Ocb2,Cc2], +[Oab1,Ocb1,Ocb3,Cc2,Cc3], +[Oab1,Ocb1],
        +[Oab1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oab1,Ocb2,Cc2], +[Oab1,Ocb3,Cc2,Cc3],
        +[Oab1], +[Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2], +[Obc1,Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3],
        +[Obc1,Obc2,Cb2,Ocb1], +[Obc1,Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Obc1,Obc2,Cb2,Ocb2,Cc2], +[Obc1,Obc2,Cb2,Ocb3,Cc2,Cc3],
        +[Obc1,Obc2,Cb2], +[Obc1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Obc1,Ocb1,Ocb2,Cc2], +[Obc1,Ocb1,Ocb3,Cc2,Cc3], +[Obc1,Ocb1],
        +[Obc1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Obc1,Ocb2,Cc2], +[Obc1,Ocb3,Cc2,Cc3],
        +[Obc1], +[Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Obc2,Cb2,Ocb1,Ocb2,Cc2], +[Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3],
        +[Obc2,Cb2,Ocb1], +[Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Obc2,Cb2,Ocb2,Cc2], +[Obc2,Cb2,Ocb3,Cc2,Cc3], +[Obc2,Cb2],
        +[Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb1,Ocb2,Cc2], +[Ocb1,Ocb3,Cc2,Cc3],
        +[Ocb1], +[Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb2,Cc2], +[Ocb3,Cc2,Cc3],
        +[Oac1,Ocb1,Ocb2,Cc2], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2], +[Oac1],
        +[Ocb1,Ocb2,Cc2], +[Ocb1], +[Ocb2,Cc2],
        +[Oac1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oac1,Ocb1,Ocb2,Cc2],
        +[Oac1,Ocb1,Ocb3,Cc2,Cc3], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
        +[Oac1,Ocb2,Cc2], +[Oac1,Ocb3,Cc2,Cc3], +[Oac1],
        +[Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb1,Ocb2,Cc2], +[Ocb1,Ocb3,Cc2,Cc3],
        +[Ocb1], +[Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb2,Cc2], +[Ocb3,Cc2,Cc3]]),
        [Oab1, Oab2, Oac1, Oac2, Obc1, Obc2, Ocb1, Ocb2, Ocb3, Ca2, Cb2, Cc2, Cc3]).

% Paper says the fault should be:
% O(a, b, 1) /\ (O(a, c, 1) \/ O(c, b, 2))

% But we don't get a formula that small:

%?- sat_round4(Oab1, Oab2, Oac1, Oac2, Obc1, Obc2, Ocb1, Ocb2, Ocb3, Ca2, Cb2, Cc2, Cc3).
% @Oab1 = Oab2, Oab2 = Oac1, Oac1 = Oac2, Oac2 = Obc1, Obc1 = Obc2, Obc2 = Ocb1, Ocb1 = Cc2, Cc2 = 1,
% @Ocb2 = Ocb3, Ocb3 = Ca2, Ca2 = Cb2, Cb2 = Cc3, Cc3 = 0.

% Oab1 and Oac1 or Oab1 and Ocb2, are true in all three cases above though...

% Here are tests ensuring that if Oab1 and Oac1 or Oab1 and Ocb2 happen then the
% post-condition fails:

test_round4a :-
    retract(clock(a, b, 1)),
    retract(clock(a, c, 1)),
    ( solve(post4(b, 'Hello world!', 4), _) -> assert(clock(a, b, 1)),
                                               assert(clock(a, c, 1))
    ; assert(clock(a, b, 1)),
      assert(clock(a, c, 1)),
      fail
    ).

test_round4b :-
    retract(clock(a, b, 1)),
    retract(clock(c, b, 2)),
    ( solve(post4(b, 'Hello world!', 4), _) -> assert(clock(a, b, 1)),
                                               assert(clock(c, b, 2))
    ; assert(clock(a, b, 1)),
      assert(clock(c, b, 2)),
      fail
    ).

% From the paper:

% "It chooses this set of failures to inject, but in the subsequent run the
% failures trigger additional broadcast attempts—which occur when ACKs are not
% received—and provide additional support for the outcome. The adversary gets as
% many chances as it likes, but each time At each round the adversary “cuts”
% some edge and injects the corresponding failures; in the subsequent run new
% edges appear. Eventually it gives up, when the agreed-upon failure model
% permits no more moves. The programmer wins again."

% I'm not sure what "subsequent run" refers to? If we change the time in the
% post-conditions above, e.g. `post4(b, 'Hello world!', 6)`, it still fails.

% Maybe we need to step though time:

%?- \+ pre4(b, 'Hello world!') ; round4(Cnf, 1).
% true ;
% Cnf = *([]).
%
%?- \+ pre4(b, 'Hello world!') ; round4(Cnf, 2).
% true ;
% Cnf = *([+[Oab1]]).
%
%?- \+ pre4(b, 'Hello world!') ; (retract(clock(a, b, 1)), round4(Cnf, 3)).
% true ;
% Cnf = *([+[Oac1,Ocb1,Ocb2,Cc2],+[Oac1,Ocb1],+[Oac1,Ocb2,Cc2],+[Oac1],+[Ocb1,Ocb2,Cc2],+[Ocb1],+[Ocb2,Cc2]]).

sat_round4_at_3(Ca2,Cc2,Oab1,Oab2,Oac1,Ocb1,Ocb2) :-
  min_sat(% max one crash:
      ((~Ca2 * ~Cc2) +
        (Ca2 * ~Cc2) +
       (~Ca2 * Cc2)) *

     % round4(Cnf, 3)
     % \+ pre4(b, 'Hello world!') ; (retract(clock(a, b, 1)), round4(Cnf, 3)).
     % ((Oac1+(Ocb1+(Ocb2+(Cc2+0))))*((Oac1+(Ocb1+0))*((Oac1+(Ocb2+(Cc2+0)))*((Oac1+0)*((Ocb1+(Ocb2+(Cc2+0)))*((Ocb1+0)*((Ocb2+(Cc2+0))*1)))))))),
     *([+[Oac1,Ocb1,Ocb2,Cc2],+[Oac1,Ocb1],+[Oac1,Ocb2,Cc2],+[Oac1],+[Ocb1,Ocb2,Cc2],+[Ocb1],+[Ocb2,Cc2]]),
      [Ca2,Cc2,Oab1,Oab2,Oac1,Ocb1,Ocb2]).

% ?- sat_round4_at_3(Ca2,Cc2,Oab1,Oab2,Oac1,Ocb1,Ocb2).
% @Ca2 = Cc2, Cc2 = Oab1, Oab1 = Oab2, Oab2 = 0,
% @Oac1 = Ocb1, Ocb1 = Ocb2, Ocb2 = 1 ;
% @Ca2 = Oab1, Oab1 = Oab2, Oab2 = Ocb2, Ocb2 = 0,
% @Cc2 = Oac1, Oac1 = Ocb1, Ocb1 = 1.

% Again not quite as short as in the paper: O(a, b, 1) /\ (O(a, c, 1) \/ O(c, b, % 2)) ...

% ----------------------------------------------------------------------
% Round 5

s5(Node, Pload, Time, Cs) :-
    % XXX: Where should pre be asserted?
    % pre(Node, Pload),
    solve(post5(Node, Pload, Time), P),
    clocks(P, Cs).

round5(Cnf) :-
    findall(Cs, s5(b, 'Hello world!', 4, Cs), Css),
    cnf(Css, Cnf).

unique_vars5(Vars) :-
    findall(Cs, s5(b, 'Hello world!', 4, Cs), Css),
    unique_vars(Css, Vars).

sat_round5(Ca2,Ca3,Cb2,Cc2,Cc3,Oab1,Oab2,Oab3,Oac1,Oba1,Oba2,
           Obc1,Obc2,Oca1,Oca2,Ocb1,Ocb2,Ocb3) :-
    min_sat( % Max one crash:
        ((~Ca2 * ~Ca3 * ~Cb2 * ~Cc2 * ~Cc3) +
         ( Ca2 * ~Ca3 * ~Cb2 * ~Cc2 * ~Cc3) +
         (~Ca2 *  Ca3 * ~Cb2 * ~Cc2 * ~Cc3) +
         (~Ca2 * ~Ca3 *  Cb2 * ~Cc2 * ~Cc3) +
         (~Ca2 * ~Ca3 * ~Cb2 *  Cc2 * ~Cc3) +
         (~Ca2 * ~Ca3 * ~Cb2 * ~Cc2 *  Cc3)
         ) *
         % No message loss after logical time 2:
         (~Oab3 * ~Ocb3) *

         % Output from round5(Cnf):
        *([+[Oab1,Oba1,Oba2,Cb2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oba1,Oba2,Cb2,Oab1,Oab2,Ca2],
           +[Oab1,Oba1,Oba2,Cb2,Oab1,Oab3,Ca2,Ca3], +[Oab1,Oba1,Oba2,Cb2,Oab1],
           +[Oab1,Oba1,Oba2,Cb2,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oba1,Oba2,Cb2,Oab2,Ca2], +[Oab1,Oba1,Oba2,Cb2,Oab3,Ca2,Ca3],
           +[Oab1,Oba1,Oba2,Cb2], +[Oab1,Oba1,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oba1,Oab1,Oab2,Ca2], +[Oab1,Oba1,Oab1,Oab3,Ca2,Ca3],
           +[Oab1,Oba1,Oab1], +[Oab1,Oba1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oba1,Oab2,Ca2], +[Oab1,Oba1,Oab3,Ca2,Ca3], +[Oab1,Oba1],
           +[Oab1,Oba2,Cb2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oba2,Cb2,Oab1,Oab2,Ca2], +[Oab1,Oba2,Cb2,Oab1,Oab3,Ca2,Ca3],
           +[Oab1,Oba2,Cb2,Oab1], +[Oab1,Oba2,Cb2,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oba2,Cb2,Oab2,Ca2], +[Oab1,Oba2,Cb2,Oab3,Ca2,Ca3],
           +[Oab1,Oba2,Cb2], +[Oab1,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oab1,Oab2,Ca2], +[Oab1,Oab1,Oab3,Ca2,Ca3], +[Oab1,Oab1],
           +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab1,Oab2,Ca2],
           +[Oab1,Oab3,Ca2,Ca3], +[Oab1],
           +[Oba1,Oba2,Cb2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oba1,Oba2,Cb2,Oab1,Oab2,Ca2], +[Oba1,Oba2,Cb2,Oab1,Oab3,Ca2,Ca3],
           +[Oba1,Oba2,Cb2,Oab1], +[Oba1,Oba2,Cb2,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oba1,Oba2,Cb2,Oab2,Ca2], +[Oba1,Oba2,Cb2,Oab3,Ca2,Ca3],
           +[Oba1,Oba2,Cb2], +[Oba1,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oba1,Oab1,Oab2,Ca2], +[Oba1,Oab1,Oab3,Ca2,Ca3], +[Oba1,Oab1],
           +[Oba1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oba1,Oab2,Ca2],
           +[Oba1,Oab3,Ca2,Ca3], +[Oba1],
           +[Oba2,Cb2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oba2,Cb2,Oab1,Oab2,Ca2],
           +[Oba2,Cb2,Oab1,Oab3,Ca2,Ca3], +[Oba2,Cb2,Oab1],
           +[Oba2,Cb2,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oba2,Cb2,Oab2,Ca2],
           +[Oba2,Cb2,Oab3,Ca2,Ca3], +[Oba2,Cb2], +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3], +[Oab1],
           +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3], +[Oab1],
           +[Oab1,Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2],
           +[Oab1,Obc1,Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3], +[Oab1,Obc1,Obc2,Cb2,Ocb1],
           +[Oab1,Obc1,Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc1,Obc2,Cb2,Ocb2,Cc2], +[Oab1,Obc1,Obc2,Cb2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc1,Obc2,Cb2], +[Oab1,Obc1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc1,Ocb1,Ocb2,Cc2], +[Oab1,Obc1,Ocb1,Ocb3,Cc2,Cc3],
           +[Oab1,Obc1,Ocb1], +[Oab1,Obc1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc1,Ocb2,Cc2], +[Oab1,Obc1,Ocb3,Cc2,Cc3], +[Oab1,Obc1],
           +[Oab1,Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc2,Cb2,Ocb1,Ocb2,Cc2], +[Oab1,Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3],
           +[Oab1,Obc2,Cb2,Ocb1], +[Oab1,Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc2,Cb2,Ocb2,Cc2], +[Oab1,Obc2,Cb2,Ocb3,Cc2,Cc3],
           +[Oab1,Obc2,Cb2], +[Oab1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Oab1,Ocb1,Ocb2,Cc2], +[Oab1,Ocb1,Ocb3,Cc2,Cc3], +[Oab1,Ocb1],
           +[Oab1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oab1,Ocb2,Cc2],
           +[Oab1,Ocb3,Cc2,Cc3], +[Oab1],
           +[Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Obc1,Obc2,Cb2,Ocb1,Ocb2,Cc2], +[Obc1,Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3],
           +[Obc1,Obc2,Cb2,Ocb1], +[Obc1,Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Obc1,Obc2,Cb2,Ocb2,Cc2], +[Obc1,Obc2,Cb2,Ocb3,Cc2,Cc3],
           +[Obc1,Obc2,Cb2], +[Obc1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Obc1,Ocb1,Ocb2,Cc2], +[Obc1,Ocb1,Ocb3,Cc2,Cc3], +[Obc1,Ocb1],
           +[Obc1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Obc1,Ocb2,Cc2],
           +[Obc1,Ocb3,Cc2,Cc3], +[Obc1],
           +[Obc2,Cb2,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Obc2,Cb2,Ocb1,Ocb2,Cc2],
           +[Obc2,Cb2,Ocb1,Ocb3,Cc2,Cc3], +[Obc2,Cb2,Ocb1],
           +[Obc2,Cb2,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Obc2,Cb2,Ocb2,Cc2],
           +[Obc2,Cb2,Ocb3,Cc2,Cc3], +[Obc2,Cb2], +[Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Ocb1,Ocb2,Cc2], +[Ocb1,Ocb3,Cc2,Cc3], +[Ocb1],
           +[Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb2,Cc2], +[Ocb3,Cc2,Cc3],
           +[Oac1,Oca1,Oca2,Cc2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oac1,Oca1,Oca2,Cc2,Oab1,Oab2,Ca2],
           +[Oac1,Oca1,Oca2,Cc2,Oab1,Oab3,Ca2,Ca3], +[Oac1,Oca1,Oca2,Cc2,Oab1],
           +[Oac1,Oca1,Oca2,Cc2,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oac1,Oca1,Oca2,Cc2,Oab2,Ca2], +[Oac1,Oca1,Oca2,Cc2,Oab3,Ca2,Ca3],
           +[Oac1,Oca1,Oca2,Cc2], +[Oac1,Oca1,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oac1,Oca1,Oab1,Oab2,Ca2], +[Oac1,Oca1,Oab1,Oab3,Ca2,Ca3],
           +[Oac1,Oca1,Oab1], +[Oac1,Oca1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oac1,Oca1,Oab2,Ca2], +[Oac1,Oca1,Oab3,Ca2,Ca3], +[Oac1,Oca1],
           +[Oac1,Oca2,Cc2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oac1,Oca2,Cc2,Oab1,Oab2,Ca2], +[Oac1,Oca2,Cc2,Oab1,Oab3,Ca2,Ca3],
           +[Oac1,Oca2,Cc2,Oab1], +[Oac1,Oca2,Cc2,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oac1,Oca2,Cc2,Oab2,Ca2], +[Oac1,Oca2,Cc2,Oab3,Ca2,Ca3],
           +[Oac1,Oca2,Cc2], +[Oac1,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oac1,Oab1,Oab2,Ca2], +[Oac1,Oab1,Oab3,Ca2,Ca3], +[Oac1,Oab1],
           +[Oac1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oac1,Oab2,Ca2],
           +[Oac1,Oab3,Ca2,Ca3], +[Oac1],
           +[Oca1,Oca2,Cc2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oca1,Oca2,Cc2,Oab1,Oab2,Ca2], +[Oca1,Oca2,Cc2,Oab1,Oab3,Ca2,Ca3],
           +[Oca1,Oca2,Cc2,Oab1], +[Oca1,Oca2,Cc2,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oca1,Oca2,Cc2,Oab2,Ca2], +[Oca1,Oca2,Cc2,Oab3,Ca2,Ca3],
           +[Oca1,Oca2,Cc2], +[Oca1,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oca1,Oab1,Oab2,Ca2], +[Oca1,Oab1,Oab3,Ca2,Ca3], +[Oca1,Oab1],
           +[Oca1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oca1,Oab2,Ca2],
           +[Oca1,Oab3,Ca2,Ca3], +[Oca1],
           +[Oca2,Cc2,Oab1,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oca2,Cc2,Oab1,Oab2,Ca2],
           +[Oca2,Cc2,Oab1,Oab3,Ca2,Ca3], +[Oca2,Cc2,Oab1],
           +[Oca2,Cc2,Oab2,Ca2,Oab3,Ca2,Ca3], +[Oca2,Cc2,Oab2,Ca2],
           +[Oca2,Cc2,Oab3,Ca2,Ca3], +[Oca2,Cc2], +[Oab1,Oab2,Ca2,Oab3,Ca2,Ca3],
           +[Oab1,Oab2,Ca2], +[Oab1,Oab3,Ca2,Ca3], +[Oab1],
           +[Oab2,Ca2,Oab3,Ca2,Ca3], +[Oab2,Ca2], +[Oab3,Ca2,Ca3],
           +[Oac1,Ocb1,Ocb2,Cc2], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2], +[Oac1],
           +[Ocb1,Ocb2,Cc2], +[Ocb1], +[Ocb2,Cc2],
           +[Oac1,Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oac1,Ocb1,Ocb2,Cc2],
           +[Oac1,Ocb1,Ocb3,Cc2,Cc3], +[Oac1,Ocb1],
           +[Oac1,Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Oac1,Ocb2,Cc2],
           +[Oac1,Ocb3,Cc2,Cc3], +[Oac1], +[Ocb1,Ocb2,Cc2,Ocb3,Cc2,Cc3],
           +[Ocb1,Ocb2,Cc2], +[Ocb1,Ocb3,Cc2,Cc3], +[Ocb1],
           +[Ocb2,Cc2,Ocb3,Cc2,Cc3], +[Ocb2,Cc2], +[Ocb3,Cc2,Cc3], +[Oab1],
           +[Oac1,Ocb1,Ocb2,Cc2], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2], +[Oac1],
           +[Ocb1,Ocb2,Cc2], +[Ocb1], +[Ocb2,Cc2], +[Oab1], +[Oab1], +[Oab1],
           +[Oac1,Ocb1,Ocb2,Cc2], +[Oac1,Ocb1], +[Oac1,Ocb2,Cc2], +[Oac1],
           +[Ocb1,Ocb2,Cc2], +[Ocb1], +[Ocb2,Cc2]]),
    [Ca2,Ca3,Cb2,Cc2,Cc3,Oab1,Oab2,Oab3,Oac1,Oba1,Oba2,Obc1,Obc2,Oca1,Oca2,Ocb1,Ocb2,Ocb3]).

% The above gives false, but it should give OAB1, OCA2 and OCB2 according to the
% paper...

test_round5 :-
    retract(clock(a, b, 1)),
    retract(clock(c, a, 2)),
    retract(clock(c, b, 2)),
    ( solve(post5(b, 'Hello world!', 4), _) -> assert(clock(a, b, 1)),
                                               assert(clock(c, a, 2)),
                                               assert(clock(c, b, 2))
    ; assert(clock(a, b, 1)),
      assert(clock(c, a, 2)),
      assert(clock(c, b, 2)),
      fail
    ).

%?- test_round5.
%@ false.