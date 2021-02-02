:- use_module(library(clpb)).

replicate(N, X, Xs) :-
    length(Xs, N),
    maplist(=(X), Xs).

min_sat(Expr, Vs) :-
    sat(Expr),
    exclude(integer, Vs, Ws),
    length(Ws, N),
    replicate(N, -1, Coeffs),
    weighted_maximum(Coeffs, Ws, _).