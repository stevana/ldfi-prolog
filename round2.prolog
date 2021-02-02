% Round 2: retrying broadcast (retry-deliv)

:- consult(node).
:- consult(clock).

% If some payload is broadcasted to some node at some time then it ends up in
% the log of that node.
log2(Node, Pload, Time) :- bcast2(Node, Pload, Time).
% The above in Dedalus: log(Node, Pload) :- bcast(Node, Pload).

% If a node persists a payload to the log it stays there.
log2(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log2(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: log(Node, Pload)@next :- log(Node, Pload).

% A node can broadcast a payload to another node, if they are connected.
log2(Node2, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    bcast2(Node1, Pload, SndTime),
    node(Node1, Node2, SndTime),
    clock(Node1, Node2, SndTime).
% The above in Dedalus:
% log(Node2, Pload)@async :-
%     bcast(Node1, Pload),
%     node(Node1, Node2).

bcast2(a, 'Hello world!', 1).

% The following line is the only difference compared to the simple-deliv:
bcast2(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    bcast2(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% Above in Dedalus: bcast(Node, Pload)@next :- bcast(Node, Pload).

missing_log2(Node, Pload, Time) :-
    log2(N, Pload, Time),
    node(N, Node, Time),
    \+ log2(Node, Pload, Time).

pre2(Node, Pload) :-
    log2(Node, Pload, 1),
    \+ bcast2(Node, Pload, 1),
    \+ crash(Node, _).

post2(Node, Pload, Time) :-
    log2(Node, Pload, Time),
    \+ missing_log2(_, Pload, Time).