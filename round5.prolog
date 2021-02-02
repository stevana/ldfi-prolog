% Round 5: "classic" broadcast (classic-deliv)
% https://github.com/palvaro/molly/blob/master/src/test/resources/examples_ft/delivery/classic_rb.ded

:- consult(node).
:- consult(clock).

% If some payload is broadcasted to some node at some time then it ends up in
% the log of that node.
log5(Node, Pload, Time) :- bcast5(Node, Pload, Time).
% The above in Dedalus: log(Node, Pload) :- bcast(Node, Pload).

% If a node persists a payload to the log it stays there.
log5(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log5(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: log(Node, Pload)@next :- log(Node, Pload).


log5(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    bcast5(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: log(N, P)@next :- bcast(N, P);

bcast5(Node2, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    bcast5(Node1, Pload, SndTime),
    node(Node1, Node2, SndTime),
    clock(Node1, Node2, SndTime).
% The above in Dedalus:
% bcast(Node2, Pload)@async :-
%    bcast(Node1, Pload),
%    node(Node1, Node2);

bcast5(a, 'Hello world!', 1).

missing_log5(Node, Pload, Time) :-
    log5(N, Pload, Time),
    node(N, Node, Time),
    \+ log5(Node, Pload, Time).

pre5(Node, Pload) :-
    log5(Node, Pload, 1),
    \+ bcast5(Node, Pload, 1),
    \+ crash(Node, _).

post5(Node, Pload, Time) :-
    log5(Node, Pload, Time),
    \+ missing_log5(_, Pload, Time).