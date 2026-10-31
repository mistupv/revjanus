/*  janus_store.pl -- stores

    A store is a total function from locations to values, with default 0 (Section 2 of
    the paper; Lean: `Store := Loc -> Value`, `Store.empty`). Locations are
      var(X)       a scalar variable x      (Lean: Loc.var x)
      cell(X, I)   an indexed variable x[i] (Lean: Loc.elem x i)
    Different functors, so a scalar x and the cells x[i] never alias.

    Representation: an AVL tree of library(assoc) holding only the NONZERO bindings.
    To make the representation canonical (equal stores are equal terms), every update
    rebuilds the tree with list_to_assoc/2 from the sorted list of bindings; for a given
    sorted list list_to_assoc/2 always builds the same tree. Setting a location to 0
    deletes its binding. (Rebuilding costs O(n) per update, which is fine for a
    prototype.)
*/

:- module(janus_store,
          [ store_empty/1,          % -Store
            store_get_var/3,        % +Store, +X, -V
            store_get_cell/4,       % +Store, +X, +I, -V
            store_set_var/4,        % +Store, +X, +V, -Store1
            store_set_cell/5,       % +Store, +X, +I, +V, -Store1
            store_to_list/2,        % +Store, -Pairs   (sorted Location-Value pairs)
            store_from_list/2       % +Pairs, -Store
          ]).

:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(apply)).

%!  store_empty(-Store) is det.
%   The empty store, mapping every location to 0.
store_empty(Store) :- empty_assoc(Store).

%!  store_get_var(+Store, +X, -V) is det.
store_get_var(Store, X, V) :- store_get(Store, var(X), V).

%!  store_get_cell(+Store, +X, +I, -V) is det.
store_get_cell(Store, X, I, V) :- store_get(Store, cell(X, I), V).

%!  store_set_var(+Store, +X, +V, -Store1) is det.
%   Store1 = Store[x -> V].
store_set_var(Store, X, V, Store1) :- store_set(Store, var(X), V, Store1).

%!  store_set_cell(+Store, +X, +I, +V, -Store1) is det.
%   Store1 = Store[x[I] -> V].
store_set_cell(Store, X, I, V, Store1) :- store_set(Store, cell(X, I), V, Store1).

%!  store_to_list(+Store, -Pairs) is det.
%   The nonzero bindings as Location-Value pairs, sorted by location (standard order).
store_to_list(Store, Pairs) :- assoc_to_list(Store, Pairs).

%!  store_from_list(+Pairs, -Store) is det.
%   Builds a store from Location-Value pairs (later pairs override earlier ones).
store_from_list(Pairs, Store) :-
    store_empty(S0),
    foldl(set_pair, Pairs, S0, Store).

set_pair(L-V, S0, S) :- store_set(S0, L, V, S).

% --- internal ------------------------------------------------------------------------

store_get(Store, Loc, V) :-
    (   get_assoc(Loc, Store, V0)
    ->  V = V0
    ;   V = 0
    ).

store_set(Store, Loc, V, Store1) :-
    assoc_to_list(Store, Pairs0),
    exclude_key(Pairs0, Loc, Pairs1),
    (   V =:= 0
    ->  Pairs2 = Pairs1
    ;   ord_union(Pairs1, [Loc-V], Pairs2)
    ),
    list_to_assoc(Pairs2, Store1).

exclude_key([], _, []).
exclude_key([K-V|Ps], Loc, Rest) :-
    (   K == Loc
    ->  Rest = Ps
    ;   Rest = [K-V|Rest1],
        exclude_key(Ps, Loc, Rest1)
    ).
