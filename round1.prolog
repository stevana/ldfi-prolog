% Round1: naive broadcast (simple-deliv)

:- consult(node).
:- consult(clock).

% If some payload is broadcasted to some node at some time then it ends up in
% the log of that node.
log1(Node, Pload, Time) :- bcast1(Node, Pload, Time).
% The above in Dedalus: log(Node, Pload) :- bcast(Node, Pload).

% If a node persists a payload to the log it stays there.
log1(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log1(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: log(Node, Pload)@next :- log(Node, Pload).

% A node can broadcast a payload to another node, if they are connected.
log1(Node2, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    bcast1(Node1, Pload, SndTime),
    node(Node1, Node2, SndTime),
    clock(Node1, Node2, SndTime).
% The above in Dedalus:
% log(Node2, Pload)@async :-
%     bcast(Node1, Pload),
%     node(Node1, Node2).

bcast1(a, 'Hello world!', 1).

missing_log1(Node, Pload, Time) :-
    log1(N, Pload, Time),
    node(N, Node, Time),
    \+ log1(Node, Pload, Time).

pre1(Node, Pload) :-
    log1(Node, Pload, 1),
    \+ bcast1(Node, Pload, 1),
    \+ crash(Node, _).

post1(Node, Pload, Time) :-
    log1(Node, Pload, Time),
    \+ missing_log1(_, Pload, Time).