% Round 4: finite redundant broadcast (ack-deliv)
% https://github.com/palvaro/molly/blob/master/src/test/resources/examples_ft/delivery/ack_rb.ded

:- consult(node).
:- consult(clock).

% If a node persists a payload to the log it stays there.
log4(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log4(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: log(Node, Pload)@next :- log(Node, Pload).

log4(N, P, Time) :- rbcast(N, _, P, Time).
% The above in Dedalus: log(N, P) :- rbcast(N, _, P).

ack(S, H, P, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    ack(S, H, P, SndTime),
    clock(S, H, SndTime).
% The above in Dedalus: ack(S, H, P)@next :- ack(S, H, P).

ack(From, Host, Pl, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    rbcast(Host, From, Pl, SndTime),
    clock(From, Host, SndTime).
% In Dedalus: ack(From, Host, Pl)@async :- rbcast(Host, From, Pl).

rbcast(Node2, Node1, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log4(Node1, Pload, SndTime),
    node(Node1, Node2, SndTime),
    \+ ack(Node1, Node2, Pload, SndTime),
    clock(Node1, Node2, SndTime).
% The above in Dedalus:
% rbcast(Node2, Node1, Pload)@async :-
%     log(Node1, Pload),
%     node(Node1, Node2),
%     \+ ack(Node1, Node2, Pload).

rbcast(A, A, P, Time) :- bcast4(A, P, Time).
% The above in Dedalus: rbcast(A, A, P) :- bcast(A, P).

bcast4(a, 'Hello world!', 1).

missing_log4(Node, Pload, Time) :-
    log4(N, Pload, Time),
    node(N, Node, Time),
    \+ log4(Node, Pload, Time).

pre4(Node, Pload) :-
    log4(Node, Pload, 1),
    \+ bcast4(Node, Pload, 1),
    \+ crash(Node, _).

post4(Node, Pload, Time) :-
    log4(Node, Pload, Time),
    \+ missing_log4(_, Pload, Time) log3(Node, Pload, Time),
    \+ missing_log3(_, Pload, Time).
58 src/detsys/ldfi-prolog/round4.prolog
Viewed
@@ -0,0 +1,58 @@
% Round 4: finite redundant broadcast (ack-deliv)
% https://github.com/palvaro/molly/blob/master/src/test/resources/examples_ft/delivery/ack_rb.ded

:- consult(node).
:- consult(clock).

% If a node persists a payload to the log it stays there.
log4(Node, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log4(Node, Pload, SndTime),
    clock(Node, Node, SndTime).
% The above in Dedalus: log(Node, Pload)@next :- log(Node, Pload).

log4(N, P, Time) :- rbcast(N, _, P, Time).
% The above in Dedalus: log(N, P) :- rbcast(N, _, P).

ack(S, H, P, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    ack(S, H, P, SndTime),
    clock(S, H, SndTime).
% The above in Dedalus: ack(S, H, P)@next :- ack(S, H, P).

ack(From, Host, Pl, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    rbcast(Host, From, Pl, SndTime),
    clock(From, Host, SndTime).
% In Dedalus: ack(From, Host, Pl)@async :- rbcast(Host, From, Pl).

rbcast(Node2, Node1, Pload, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    log4(Node1, Pload, SndTime),
    node(Node1, Node2, SndTime),
    \+ ack(Node1, Node2, Pload, SndTime),
    clock(Node1, Node2, SndTime).
% The above in Dedalus:
% rbcast(Node2, Node1, Pload)@async :-
%     log(Node1, Pload),
%     node(Node1, Node2),
%     \+ ack(Node1, Node2, Pload).

rbcast(A, A, P, Time) :- bcast4(A, P, Time).
% The above in Dedalus: rbcast(A, A, P) :- bcast(A, P).

bcast4(a, 'Hello world!', 1).

missing_log4(Node, Pload, Time) :-
    log4(N, Pload, Time),
    node(N, Node, Time),
    \+ log4(Node, Pload, Time).

pre4(Node, Pload) :-
    log4(Node, Pload, 1),
    \+ bcast4(Node, Pload, 1),
    \+ crash(Node, _).

post4(Node, Pload, Time) :-
    log4(Node, Pload, Time),
    \+ missing_log4(_, Pload, Time).