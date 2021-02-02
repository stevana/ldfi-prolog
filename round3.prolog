% Round 3: redundant broadcast (redun-deliv)

:- consult(node).
:- consult(clock).

% If some payload is broadcasted to some node at some time then it ends up in
% the log of that node.
log3(Node, Pload, Time) :- bcast3(Node, Pload, Time).
% The above in Dedalus: log(Node, Pload) :- bcast(Node, Pload).

% If a node persists a payload to the log it stays there.
log3(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log3(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: log(Node, Pload)@next :- log(Node, Pload).

% A node can broadcast a payload to another node, if they are connected.
log3(Node2, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    bcast3(Node1, Pload, SndTime),
    node(Node1, Node2, SndTime),
    clock(Node1, Node2, SndTime).
% The above in Dedalus:
% log(Node2, Pload)@async :-
%     bcast(Node1, Pload),
%     node(Node1, Node2).

bcast3(a, 'Hello world!', 1).

bcast3(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    bcast3(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% Above in Dedalus: bcast(Node, Pload)@next :- bcast(Node, Pload).

% The following line is the only difference compared to the retry-deliv:
bcast3(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log3(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: bcast(Node, Pload)@next :- log(Node, Pload).

missing_log3(Node, Pload, Time) :-
    log3(N, Pload, Time),
    node(N, Node, Time),
    \+ log3(Node, Pload, Time).

pre3(Node, Pload) :-
    log3(Node, Pload, 1),
    \+ bcast3(Node, Pload, 1),
    \+ crash(Node, _).

post3(Node, Pload, Time) :-
    log3(Node, Pload, Time),
    \+ missing_log3(_, Pload, Time).