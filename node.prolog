% node(Node1, Node2, Time) means that Node1 can communicate with Node2 at some
% point in time.
% node(a, a, 1).
node(a, b, 1).
node(a, c, 1).
node(b, a, 1).
node(b, b, 1).
node(b, c, 1).
node(c, a, 1).
node(c, b, 1).
node(c, c, 1).

% By induction nodes can continue to communicate in the future. (So long as they
% are in the clock relation, which we will get back to later.)
node(Node, Neighbor, SuccSndTime) :-
    succ(SndTime, SuccSndTime),
    node(Node, Neighbor, SndTime),
    clock(Node, Neighbor, SndTime).
%               ^---- This shouldn't be Node like in the paper, right?
% The above in Dedalus: node(Node, Neighbor)@next :- node(Node, Neighbor).

% Not defined anywhere?
% crash(???, Node, Time)?
crash(_, _) :- false.