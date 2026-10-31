/*  janus_reversible.pl -- the reversible semantics of Janus (Section 4 of the paper,
    "A Reversible Semantics for Janus"): the forward rules (Subsection "The Forward
    Rules") and the backward rules (Subsection "The Backward Rules").

    A literal transcription of Figures "Reversible forward semantics: rules for basic
    constructs", "Reversible forward semantics: rules for if and for loop",
    "Reversible backward semantics: rules for basic constructs" and "Reversible
    backward semantics: rules for if and for loop". Each rule is ONE clause, with its
    premises in the order of the paper:
      fwd_step(Info, K, Rule, K1)     K  -> K1   (the relation written with a right
                                                  harpoon in the paper)  [FwdStep]
      bwd_step(Info, K, Rule, K1)     K  <- K1   (left harpoon; as in the paper, the
                                                  reduction goes from K to K1) [BwdStep]

    Configurations (Lean: RConfig in Forward.lean):
      rc(Sigma, L1, L2, Stack)    <sigma, l1, l2, pi>
        L1 is the label of the last executed statement, L2 the label of the next
        statement to be executed (the program counter).
    Stack items (Lean: RStackItem):
      call(L), uncall(L)                  call(l), uncall(l)
      if_true(L1, L2), if_false(L1, L2)   labels of the test and the assertion
      loop1(L1, S1, L2, S2), loop2(L1, S1, L2, S2)
                                          S1, S2 are the labeled statements of the loop

    Info is the program info of janus_labeled.pl (labeled program, block, ctx, CFG).
    "l -> l'" is edge(Info, l, l') (an edge of flow(p)); "l <-< l'" (an edge of the
    inverse CFG) is edge(Info, l', l).
*/

:- module(janus_reversible,
          [ fwd_step/4,             % +Info, +K, -Rule, -K1
            bwd_step/4,             % +Info, +K, -Rule, -K1
            rev_initial/2,          % +Info, -K
            rev_final/2,            % +Info, +K
            is_initial/2,           % +Info, +K
            fwd_run/4,              % +Info, +K, -Steps, -Result
            bwd_run/4,              % +Info, +K, -Steps, -Result
            run_program_rev/2,      % +Program, -FinalStore
            rc_text/2,              % +K, -String
            rstack_text/2           % +Stack, -String
          ]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(janus_arith).
:- use_module(janus_store).
:- use_module(janus_bigstep, [eval_expr/3]).
:- use_module(janus_labeled).
:- use_module(janus_trace, [store_text/2]).

% ======================================================================================
% Forward rules
% ======================================================================================

% --- Figure "Reversible forward semantics: rules for basic constructs" ---------------

% Rule AssVar (forward)
fwd_step(Info, rc(Sigma, _L, L1, Pi), 'AssVar', rc(Sigma1, L1, L2, Pi)) :-
    block(Info, L1, assign_var(X, Op, E)),
    eval_expr(Sigma, E, V),
    edge(Info, L1, L2),
    store_get_var(Sigma, X, A),
    apply_assign_op(Op, A, V, R),
    store_set_var(Sigma, X, R, Sigma1).
% Rule AssArr (forward)
fwd_step(Info, rc(Sigma, _L, L1, Pi), 'AssArr', rc(Sigma1, L1, L2, Pi)) :-
    block(Info, L1, assign_arr(X, El, Op, E)),
    eval_expr(Sigma, El, Vl),
    eval_expr(Sigma, E, V),
    edge(Info, L1, L2),
    store_get_cell(Sigma, X, Vl, A),
    apply_assign_op(Op, A, V, R),
    store_set_cell(Sigma, X, Vl, R, Sigma1).
% Rule Call (forward)
fwd_step(Info, rc(Sigma, _L, L1, Pi), 'Call', rc(Sigma, Ls, L2, [call(L1)|Pi])) :-
    block(Info, L1, call(Id)),
    proc_body(Info, Id, Body), entry(Body, Ls),
    edge(Info, Ls, L2).
% Rule Return1 (forward)
fwd_step(Info, rc(Sigma, _L, L1, [call(L2)|Pi]), 'Return1', rc(Sigma, L2, L3, Pi)) :-
    block(Info, L1, stop),
    edge(Info, L2, L3).
% Rule UnCall (forward)
fwd_step(Info, rc(Sigma, _L, L1, Pi), 'UnCall', rc(Sigma, Ls, L2, [uncall(L1)|Pi])) :-
    block(Info, L1, uncall(Id)),
    proc_body(Info, inv(Id), Body), entry(Body, Ls),
    edge(Info, Ls, L2).
% Rule Return2 (forward)
fwd_step(Info, rc(Sigma, _L, L1, [uncall(L2)|Pi]), 'Return2', rc(Sigma, L2, L3, Pi)) :-
    block(Info, L1, stop),
    edge(Info, L2, L3).
% Rule Skip (forward)
fwd_step(Info, rc(Sigma, _L, L1, Pi), 'Skip', rc(Sigma, L1, L2, Pi)) :-
    block(Info, L1, skip),
    edge(Info, L1, L2).

% --- Figure "Reversible forward semantics: rules for if and for loop" ----------------

% Rule IfTrue1 (forward)
fwd_step(Info, rc(Sigma, _L, L1, Pi), 'IfTrue1',
         rc(Sigma, L1, N1, [if_true(L1, L2)|Pi])) :-
    ctx(Info, L1, lif(E1, L1, S1, _S2, _E2, L2)),
    eval_expr(Sigma, E1, V1),
    is_true(V1),
    entry(S1, N1).
% Rule IfTrue2 (forward)
fwd_step(Info, rc(Sigma, _L, L2, [if_true(_L1, L2)|Pi]), 'IfTrue2', rc(Sigma, L2, L2b, Pi)) :-
    block(Info, L2, cond(E2)),
    eval_expr(Sigma, E2, V2),
    is_true(V2),
    edge(Info, L2, L2b).
% Rule IfFalse1 (forward)
fwd_step(Info, rc(Sigma, _L, L1, Pi), 'IfFalse1',
         rc(Sigma, L1, N2, [if_false(L1, L2)|Pi])) :-
    ctx(Info, L1, lif(E1, L1, _S1, S2, _E2, L2)),
    eval_expr(Sigma, E1, V1),
    is_false(V1),
    entry(S2, N2).
% Rule IfFalse2 (forward)
fwd_step(Info, rc(Sigma, _L, L2, [if_false(_L1, L2)|Pi]), 'IfFalse2', rc(Sigma, L2, L2b, Pi)) :-
    block(Info, L2, cond(E2)),
    eval_expr(Sigma, E2, V2),
    is_false(V2),
    edge(Info, L2, L2b).
% Rule LoopMain (forward)
fwd_step(Info, rc(Sigma, L, L1, Pi), 'LoopMain',
         rc(Sigma, L1, N1, [loop1(L1, S1, L2, S2)|Pi])) :-
    ctx(Info, L1, lloop(E1, L1, S1, S2, _E2, L2)),
    eval_expr(Sigma, E1, V1),
    is_true(V1),
    exit(S2, X2), L =\= X2,
    entry(S1, N1).
% Rule LoopBase (forward)
fwd_step(Info, rc(Sigma, _L, L2, [loop1(_L1, _S1, L2, S2)|Pi]), 'LoopBase',
         rc(Sigma, L2, L2b, Pi)) :-
    block(Info, L2, cond(E2)),
    eval_expr(Sigma, E2, V2),
    is_true(V2),
    edge(Info, L2, L2b),
    entry(S2, N2), L2b =\= N2.
% Rule Loop1 (forward)
fwd_step(Info, rc(Sigma, _L, L2, [loop1(L1, S1, L2, S2)|Pi]), 'Loop1',
         rc(Sigma, L2, N2, [loop2(L1, S1, L2, S2)|Pi])) :-
    block(Info, L2, cond(E2)),
    eval_expr(Sigma, E2, V2),
    is_false(V2),
    entry(S2, N2).
% Rule Loop2 (forward)
fwd_step(Info, rc(Sigma, _L, L1, [loop2(L1, S1, L2, S2)|Pi]), 'Loop2',
         rc(Sigma, L1, N1, [loop1(L1, S1, L2, S2)|Pi])) :-
    block(Info, L1, cond(E1)),
    eval_expr(Sigma, E1, V1),
    is_false(V1),
    entry(S1, N1).

% ======================================================================================
% Backward rules
% ======================================================================================

% --- Figure "Reversible backward semantics: rules for basic constructs" --------------

% Rule AssVar (backward)
bwd_step(Info, rc(Sigma, L1, _L2, Pi), 'AssVar', rc(Sigma1, L, L1, Pi)) :-
    block(Info, L1, assign_var(X, Op, E)),
    eval_expr(Sigma, E, V),
    edge(Info, L, L1),
    store_get_var(Sigma, X, A),
    inverse_assign_op(Op, IOp),
    apply_assign_op(IOp, A, V, R),
    store_set_var(Sigma, X, R, Sigma1).
% Rule AssArr (backward)
bwd_step(Info, rc(Sigma, L1, _L2, Pi), 'AssArr', rc(Sigma1, L, L1, Pi)) :-
    block(Info, L1, assign_arr(X, El, Op, E)),
    eval_expr(Sigma, El, Vl),
    eval_expr(Sigma, E, V),
    edge(Info, L, L1),
    store_get_cell(Sigma, X, Vl, A),
    inverse_assign_op(Op, IOp),
    apply_assign_op(IOp, A, V, R),
    store_set_cell(Sigma, X, Vl, R, Sigma1).
% Rule Call (backward)
bwd_step(Info, rc(Sigma, Ls, _L2, [call(L1)|Pi]), 'Call', rc(Sigma, L, L1, Pi)) :-
    block(Info, Ls, start),
    edge(Info, L, L1).
% Rule Return1 (backward)
bwd_step(Info, rc(Sigma, L2, _L3, Pi), 'Return1', rc(Sigma, L, X, [call(L2)|Pi])) :-
    block(Info, L2, call(Id)),
    proc_body(Info, Id, Body), exit(Body, X),
    edge(Info, L, X).
% Rule UnCall (backward)
bwd_step(Info, rc(Sigma, Ls, _L2, [uncall(L1)|Pi]), 'UnCall', rc(Sigma, L, L1, Pi)) :-
    block(Info, Ls, start),
    edge(Info, L, L1).
% Rule Return2 (backward)
bwd_step(Info, rc(Sigma, L2, _L3, Pi), 'Return2', rc(Sigma, L, X, [uncall(L2)|Pi])) :-
    block(Info, L2, uncall(Id)),
    proc_body(Info, inv(Id), Body), exit(Body, X),
    edge(Info, L, X).
% Rule Skip (backward)
bwd_step(Info, rc(Sigma, L1, _L2, Pi), 'Skip', rc(Sigma, L, L1, Pi)) :-
    block(Info, L1, skip),
    edge(Info, L, L1).

% --- Figure "Reversible backward semantics: rules for if and for loop" ---------------

% Rule IfTrue1 (backward)
bwd_step(Info, rc(Sigma, L1, _L1b, [if_true(L1, _L2)|Pi]), 'IfTrue1', rc(Sigma, L, L1, Pi)) :-
    block(Info, L1, cond(E1)),
    eval_expr(Sigma, E1, V1),
    is_true(V1),
    edge(Info, L, L1).
% Rule IfTrue2 (backward)
bwd_step(Info, rc(Sigma, L2, _L2b, Pi), 'IfTrue2', rc(Sigma, X1, L2, [if_true(L1, L2)|Pi])) :-
    ctx(Info, L2, lif(_E1, L1, S1, _S2, E2, L2)),
    eval_expr(Sigma, E2, V2),
    is_true(V2),
    exit(S1, X1).
% Rule IfFalse1 (backward)
bwd_step(Info, rc(Sigma, L1, _L1b, [if_false(L1, _L2)|Pi]), 'IfFalse1', rc(Sigma, L, L1, Pi)) :-
    block(Info, L1, cond(E1)),
    eval_expr(Sigma, E1, V1),
    is_false(V1),
    edge(Info, L, L1).
% Rule IfFalse2 (backward)
bwd_step(Info, rc(Sigma, L2, _L2b, Pi), 'IfFalse2', rc(Sigma, X2, L2, [if_false(L1, L2)|Pi])) :-
    ctx(Info, L2, lif(_E1, L1, _S1, S2, E2, L2)),
    eval_expr(Sigma, E2, V2),
    is_false(V2),
    exit(S2, X2).
% Rule LoopMain (backward)
bwd_step(Info, rc(Sigma, L1, _L1b, [loop1(L1, _S1, _L2, S2)|Pi]), 'LoopMain',
         rc(Sigma, L, L1, Pi)) :-
    block(Info, L1, cond(E1)),
    eval_expr(Sigma, E1, V1),
    is_true(V1),
    edge(Info, L, L1),
    exit(S2, X2), L =\= X2.
% Rule LoopBase (backward)
bwd_step(Info, rc(Sigma, L2, L2b, Pi), 'LoopBase',
         rc(Sigma, X1, L2, [loop1(L1, S1, L2, S2)|Pi])) :-
    ctx(Info, L2, lloop(_E1, L1, S1, S2, E2, L2)),
    eval_expr(Sigma, E2, V2),
    is_true(V2),
    entry(S2, N2), L2b =\= N2,
    exit(S1, X1).
% Rule Loop1 (backward)
bwd_step(Info, rc(Sigma, L2, _L, [loop2(L1, S1, L2, S2)|Pi]), 'Loop1',
         rc(Sigma, X1, L2, [loop1(L1, S1, L2, S2)|Pi])) :-
    block(Info, L2, cond(E2)),
    eval_expr(Sigma, E2, V2),
    is_false(V2),
    exit(S1, X1).
% Rule Loop2 (backward)
bwd_step(Info, rc(Sigma, L1, _L, [loop1(L1, S1, L2, S2)|Pi]), 'Loop2',
         rc(Sigma, X2, L1, [loop2(L1, S1, L2, S2)|Pi])) :-
    block(Info, L1, cond(E1)),
    eval_expr(Sigma, E1, V1),
    is_false(V1),
    exit(S2, X2).

% ======================================================================================
% Initial and final configurations, runs
% ======================================================================================

%!  rev_initial(+Info, -K) is semidet.
%   The initial configuration <eps, entry(s), l, []> of a program p = (s p1 ... pn),
%   where entry(s) -> l belongs to the CFG of the main program (s includes start and
%   stop, so entry(s) is the label of start and l the label of the first statement).
rev_initial(Info, rc(Sigma0, A, L, [])) :-
    info_lprog(Info, lprog(Main, _)),
    entry(Main, A),
    main_cfg(Info, Edges),
    memberchk(A-L, Edges),
    store_empty(Sigma0).

%!  is_initial(+Info, +K) is semidet.
%   K is the initial configuration, up to the store: the last executed label is the
%   start of the main program and the stack is empty.
is_initial(Info, rc(_, A, L, [])) :-
    rev_initial(Info, rc(_, A, L, [])).

%!  rev_final(+Info, +K) is semidet.
%   A final configuration <sigma, l', l'', []> with block(l'') = stop
%   (Lemma "forward-rev").
rev_final(Info, rc(_, _, L2, [])) :-
    block(Info, L2, stop).

%!  fwd_run(+Info, +K, -Steps, -Result) is det.
%   Applies forward rules until no rule applies. Steps is the list of
%   step(Rule, K1); Result is final(K) (Lemma "forward-rev": the program terminated)
%   or stuck(K) (no derivation: an assertion failed, a division by zero, ...).
%   The forward relation is deterministic, so the first applicable rule is the only
%   one.
fwd_run(Info, K, Steps, Result) :-
    (   fwd_step(Info, K, Rule, K1)
    ->  Steps = [step(Rule, K1)|Steps1],
        fwd_run(Info, K1, Steps1, Result)
    ;   rev_final(Info, K)
    ->  Steps = [], Result = final(K)
    ;   Steps = [], Result = stuck(K)
    ).

%!  bwd_run(+Info, +K, -Steps, -Result) is det.
%   Applies backward rules until no rule applies; Result is initial(K) if the
%   initial configuration has been reached, or stuck(K) otherwise.
bwd_run(Info, K, Steps, Result) :-
    (   bwd_step(Info, K, Rule, K1)
    ->  Steps = [step(Rule, K1)|Steps1],
        bwd_run(Info, K1, Steps1, Result)
    ;   is_initial(Info, K)
    ->  Steps = [], Result = initial(K)
    ;   Steps = [], Result = stuck(K)
    ).

%!  run_program_rev(+Program, -FinalStore) is semidet.
%   Runs a program with the forward rules from the initial configuration; fails if the
%   computation gets stuck before reaching the final stop (Lemma "forward-rev").
run_program_rev(Program, FinalStore) :-
    info_of_program(Program, Info),
    rev_initial(Info, K0),
    fwd_run(Info, K0, _, final(rc(FinalStore, _, _, []))).

% ======================================================================================
% Printing
% ======================================================================================

%!  rc_text(+K, -String) is det.   <{n=3}, 2, 3, call(3) : []>
rc_text(rc(Sigma, L1, L2, Pi), T) :-
    store_text(Sigma, ST),
    rstack_text(Pi, PT),
    format(string(T), "<~w, ~w, ~w, ~w>", [ST, L1, L2, PT]).

%!  rstack_text(+Stack, -String) is det.
rstack_text([], "[]").
rstack_text([I|Is], T) :-
    maplist(ritem_text, [I|Is], Ts),
    atomic_list_concat(Ts, ' : ', Inner),
    format(string(T), "~w : []", [Inner]).

ritem_text(call(L), T) :- format(string(T), "call(~w)", [L]).
ritem_text(uncall(L), T) :- format(string(T), "uncall(~w)", [L]).
ritem_text(if_true(L1, L2), T) :- format(string(T), "if_true(~w,~w)", [L1, L2]).
ritem_text(if_false(L1, L2), T) :- format(string(T), "if_false(~w,~w)", [L1, L2]).
ritem_text(loop1(L1, _, L2, _), T) :- format(string(T), "loop1(~w,s1,~w,s2)", [L1, L2]).
ritem_text(loop2(L1, _, L2, _), T) :- format(string(T), "loop2(~w,s1,~w,s2)", [L1, L2]).
