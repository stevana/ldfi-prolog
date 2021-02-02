% EDB (extensional database) of clock facts.

% clock(From, To, SndTime) iff some node can communicate with another at some
% point in time. If there's an message omission between, e.g. node a and node b
% at time 1 then we should remove `clock(a, b, 1)`. Similar with crashes.
clock(a, a, 1).
clock(a, a, 2).
clock(a, a, 3).
clock(a, a, 4).
clock(a, a, 5).

clock(a, b, 1).
clock(a, b, 2).
clock(a, b, 3).
clock(a, b, 4).
clock(a, b, 5).

clock(a, c, 1).
clock(a, c, 2).
clock(a, c, 3).
clock(a, c, 4).
clock(a, c, 5).

clock(b, a, 1).
clock(b, a, 2).
clock(b, a, 3).
clock(b, a, 4).
clock(b, a, 5).

clock(b, b, 1).
clock(b, b, 2).
clock(b, b, 3).
clock(b, b, 4).
clock(b, b, 5).

clock(b, c, 1).
clock(b, c, 2).
clock(b, c, 3).
clock(b, c, 4).
clock(b, c, 5).

clock(c, a, 1).
clock(c, a, 2).
clock(c, a, 3).
clock(c, a, 4).
clock(c, a, 5).

clock(c, b, 1).
clock(c, b, 2).
clock(c, b, 3).
clock(c, b, 4).
clock(c, b, 5).

clock(c, c, 1).
clock(c, c, 2).
clock(c, c, 3).
clock(c, c, 4).
clock(c, c, 5).

% The above can be generated with:

product(Xs, Ys, Zs, XYZs) :-
    findall([X, Y, Z], (member(X, Xs), member(Y, Ys), member(Z, Zs)), XYZs).

generate_clock :-
    product([a, b, c], [a, b, c], [1,2,3,4,5], Ps),
    maplist(format("clock(~w, ~w, ~d).~n"), Ps).