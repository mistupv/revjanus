/*  janus_trace.pl -- trace mode: the big-step derivation of a run.

    The trace is computed by a small meta-interpreter over the clauses of
    janus_bigstep.pl: each application of a rule of Figures "Semantics of expressions"
    and "Big-step semantics" becomes a node of the derivation tree. The rules are not
    duplicated, so the trace always follows exactly the same clauses as exec/4.

    Rule names are recovered from the clause heads (e.g. the clause of exec/4 whose
    statement is assign_var/3 is rule AssVar); IfTrue/IfFalse and LoopBase/LoopRec are
    told apart by their test premise (is_true/1 or is_false/1).

    If a program has no derivation, the trace shows the partial derivation that got
    furthest, and the premise that fails (an assertion, a division by zero, an
    undefined procedure, ...). Since the semantics is deterministic, this is the only
    rule application that could have succeeded up to that point.

    Derivation trees:
      node(Rule, Judgement, Children, Status)
        Rule      'AssVar', 'IfTrue', 'Bop', ...
        Judgement exec(Gamma, Sigma, Stmt, Sigma1)
                  exec_loop(Gamma, Sigma, E1, S1, E2, S2, Sigma1)
                  eval_expr(Sigma, Expr, V)
        Children  premises, in the order of the rule: nodes, or cond(Goal) for the
                  side conditions (store accesses, operator interpretation, is_true?,
                  Gamma(id), inversion)
        Status    ok | failed      (failed: the last child is the failing premise)
*/

:- module(janus_trace,
          [ trace_program/2,        % +Program, -Result
            print_trace/2,          % +Result, +Level   (Level: stmt or full)
            short_stmt/2,           % +Stmt, -String
            store_text/2            % +Store, -String
          ]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(janus_bigstep).
:- use_module(janus_store).
:- use_module(janus_parser, [pp_expr/1, binop_symbol/2, assign_symbol/2]).

%!  trace_program(+Program, -Result) is det.
%   Runs the main body from the empty store (as run_program/2) and returns
%   proof(FinalStore, Tree) or failure(PartialTree).
trace_program(program(Main, Procs), Result) :-
    store_empty(Sigma0),
    once(solve(exec(Procs, Sigma0, Main, Final), R)),   % det; once/1 drops choicepoints
    (   R = proof(Tree)
    ->  Result = proof(Final, Tree)
    ;   R = failure(Tree, _)
    ->  Result = failure(Tree)
    ).

% ======================================================================================
% Meta-interpreter
% ======================================================================================

% The judgements whose rules are interpreted (all others are side conditions).
judgement(exec(_, _, _, _)).
judgement(exec_loop(_, _, _, _, _, _, _)).
judgement(eval_expr(_, _, _)).

%  solve(+Goal, -Result): Result = proof(Node) or failure(Node, Progress).
solve(Goal, Result) :-
    functor(Goal, Name, Arity),
    functor(Head, Name, Arity),
    findall(Head-Body, clause(janus_bigstep:Head, Body), Clauses),
    attempts(Clauses, Goal, Failures, Result0),
    (   nonvar(Result0)
    ->  Result = Result0
    ;   best_failure(Failures, Goal, Result)
    ).

%  attempts(+Clauses, +Goal, -Failures, -Proof): tries the rules in order, stops at the
%  first one that succeeds (Proof = proof(Node)); otherwise collects the failures.
attempts([], _, [], _).
attempts([Head-Body|Cs], Goal, Failures, Proof) :-
    rule_name(Head, Body, Rule),
    copy_term(Goal, G),
    (   Head = G
    ->  conj_list(Body, Premises),
        premises(Premises, Children, Status, Progress),
        (   Status == ok
        ->  Goal = G,
            Proof = proof(node(Rule, G, Children, ok)),
            Failures = []
        ;   Failures = [failure(node(Rule, G, Children, failed), Progress)|Fs],
            attempts(Cs, Goal, Fs, Proof)
        )
    ;   attempts(Cs, Goal, Failures, Proof)
    ).

%  premises(+Goals, -Children, -Status, -Progress)
premises([], [], ok, 0).
premises([P|Ps], Children, Status, Progress) :-
    (   judgement(P)
    ->  solve(P, R),
        (   R = proof(Node)
        ->  Children = [Node|Cs],
            premises(Ps, Cs, Status, Progress0),
            Progress is Progress0 + 1
        ;   R = failure(Node, _),
            Children = [Node], Status = failed, Progress = 0
        )
    ;   (   call(janus_bigstep:P)
        ->  Children = [cond(P)|Cs],
            premises(Ps, Cs, Status, Progress0),
            Progress is Progress0 + 1
        ;   Children = [cond(P)], Status = failed, Progress = 0
        )
    ).

%  best_failure(+Failures, +Goal, -Result): the attempt that solved most premises.
best_failure([], Goal, failure(node(none, Goal, [], failed), 0)).
best_failure([F|Fs], _, Best) :-
    foldl(further, Fs, F, Best).

further(failure(N, P), failure(N0, P0), Best) :-
    (   P > P0
    ->  Best = failure(N, P)
    ;   Best = failure(N0, P0)
    ).

conj_list(true, []) :- !.
conj_list((A, B), Gs) :- !,
    conj_list(A, As), conj_list(B, Bs), append(As, Bs, Gs).
conj_list(G, [G]).

%  rule_name(+Head, +Body, -Name): the name of the rule of a clause.
rule_name(eval_expr(_, const(_), _), _, 'Con').
rule_name(eval_expr(_, var(_), _), _, 'Var').
rule_name(eval_expr(_, arr(_, _), _), _, 'Arr').
rule_name(eval_expr(_, binop(_, _, _), _), _, 'Bop').
rule_name(exec(_, _, assign_var(_, _, _), _), _, 'AssVar').
rule_name(exec(_, _, assign_arr(_, _, _, _), _), _, 'AssArr').
rule_name(exec(_, _, call(_), _), _, 'Call').
rule_name(exec(_, _, uncall(_), _), _, 'UnCall').
rule_name(exec(_, _, seq(_, _), _), _, 'Seq').
rule_name(exec(_, _, if_then_else(_, _, _, _), _), Body, Name) :-
    test_premise(Body, T),
    ( T == is_true -> Name = 'IfTrue' ; Name = 'IfFalse' ).
rule_name(exec(_, _, loop(_, _, _, _), _), _, 'LoopMain').
rule_name(exec(_, _, skip, _), _, 'Skip').
rule_name(exec_loop(_, _, _, _, _, _, _), Body, Name) :-
    test_premise(Body, T),
    ( T == is_true -> Name = 'LoopBase' ; Name = 'LoopRec' ).

% The second premise of IfTrue/IfFalse and LoopBase/LoopRec is the test.
test_premise(Body, T) :-
    conj_list(Body, [_, Test|_]),
    functor(Test, T, 1).

% ======================================================================================
% Printing
% ======================================================================================

%!  print_trace(+Result, +Level) is det.
%   Level = stmt: only statement-level rules (AssVar, ..., LoopRec);
%   Level = full: also expression evaluation (Con, Var, Arr, Bop) and side conditions.
print_trace(proof(_, Tree), Level) :-
    format("derivation:~n"),
    print_node(Tree, 1, Level).
print_trace(failure(Tree), Level) :-
    format("partial derivation (no derivation exists):~n"),
    print_node(Tree, 1, Level).

print_node(node(Rule, J, Children, Status), D, Level) :-
    (   ( shown(J, Level) ; Status == failed )
    ->  indent(D),
        judgement_text(J, Status, Text),
        format("~w: ~w~n", [Rule, Text]),
        D1 is D + 1
    ;   D1 = D
    ),
    forall(member(C, Children), print_child(C, Status, Children, D1, Level)).

print_child(node(R, J, Cs, S), _, _, D, Level) :-
    (   shown(J, Level) ; S == failed ; Level == full ), !,
    print_node(node(R, J, Cs, S), D, Level).
print_child(node(_, _, _, _), _, _, _, _).
print_child(cond(G), Status, Children, D, Level) :-
    (   Status == failed, last(Children, cond(G2)), G2 == G
    ->  indent(D), failure_text(G, T), format("FAILS: ~w~n", [T])
    ;   Level == full
    ->  indent(D), cond_text(G, T), format("where ~w~n", [T])
    ;   true
    ).

shown(eval_expr(_, _, _), full) :- !.
shown(eval_expr(_, _, _), _) :- !, fail.
shown(_, _).

indent(D) :- forall(between(1, D, _), write('  ')).

judgement_text(exec(_, S, St, S1), Status, T) :-
    store_text(S, ST), short_stmt(St, StT), result_text(S1, Status, store, RT),
    format(string(T), "<~w, ~w> => ~w", [ST, StT, RT]).
judgement_text(exec_loop(_, S, E1, S1, E2, S2, R), Status, T) :-
    store_text(S, ST), expr_text(E1, E1T), short_stmt(S1, S1T),
    expr_text(E2, E2T), short_stmt(S2, S2T), result_text(R, Status, store, RT),
    format(string(T), "<~w, (~w, ~w, ~w, ~w)> => ~w", [ST, E1T, S1T, E2T, S2T, RT]).
judgement_text(eval_expr(S, E, V), Status, T) :-
    store_text(S, ST), expr_text(E, ET), result_text(V, Status, value, VT),
    format(string(T), "<~w, ~w> => ~w", [ST, ET, VT]).

result_text(R, ok, store, T) :- !, store_text(R, T).
result_text(V, ok, value, T) :- !, format(string(T), "~w", [V]).
result_text(_, _, _, "(no derivation)").

%!  store_text(+Store, -Text): {x=1, a[2]=7}, sorted by name.
store_text(S, T) :-
    store_to_list(S, Pairs),
    maplist(binding_key, Pairs, Keyed),
    keysort(Keyed, Sorted),
    pairs_values(Sorted, Bs),
    atomic_list_concat(Bs, ', ', Inner),
    format(string(T), "{~w}", [Inner]).

binding_key(var(X)-V, k(X, 0, 0)-B) :- format(atom(B), "~w=~w", [X, V]).
binding_key(cell(X, I)-V, k(X, 1, I)-B) :- format(atom(B), "~w[~w]=~w", [X, I, V]).

expr_text(E, T) :- with_output_to(string(T), pp_expr(E)).

%!  short_stmt(+Stmt, -String): a one-line abbreviation of a statement.
short_stmt(assign_var(X, Op, E), T) :-
    assign_symbol(Op, O), expr_text(E, ET),
    format(string(T), "~w ~w ~w", [X, O, ET]).
short_stmt(assign_arr(X, E1, Op, E2), T) :-
    assign_symbol(Op, O), expr_text(E1, E1T), expr_text(E2, E2T),
    format(string(T), "~w[~w] ~w ~w", [X, E1T, O, E2T]).
short_stmt(if_then_else(E1, _, _, E2), T) :-
    expr_text(E1, E1T), expr_text(E2, E2T),
    format(string(T), "if ~w then ... else ... fi ~w", [E1T, E2T]).
short_stmt(loop(E1, _, _, E2), T) :-
    expr_text(E1, E1T), expr_text(E2, E2T),
    format(string(T), "from ~w do ... loop ... until ~w", [E1T, E2T]).
short_stmt(call(Id), T) :- format(string(T), "call ~w", [Id]).
short_stmt(uncall(Id), T) :- format(string(T), "uncall ~w", [Id]).
short_stmt(skip, "skip").
short_stmt(seq(S1, _), T) :-
    short_stmt(S1, T1),
    format(string(T), "~w ...", [T1]).

cond_text(store_get_var(_, X, V), T) :- format(string(T), "sigma(~w) = ~w", [X, V]).
cond_text(store_get_cell(_, X, I, V), T) :- format(string(T), "sigma(~w[~w]) = ~w", [X, I, V]).
cond_text(store_set_var(_, X, V, _), T) :- format(string(T), "update ~w -> ~w", [X, V]).
cond_text(store_set_cell(_, X, I, V, _), T) :- format(string(T), "update ~w[~w] -> ~w", [X, I, V]).
cond_text(apply_assign_op(Op, A, V, R), T) :-
    assign_symbol(Op, O), sub_atom(O, 0, 1, _, S),
    format(string(T), "[[~w]](~w, ~w) = ~w", [S, A, V, R]).
cond_text(apply_binop(Op, V1, V2, V), T) :-
    binop_symbol(Op, O),
    format(string(T), "[[~w]](~w, ~w) = ~w", [O, V1, V2, V]).
cond_text(is_true(V), T) :- format(string(T), "is_true?(~w)", [V]).
cond_text(is_false(V), T) :- format(string(T), "is_false?(~w)", [V]).
cond_text(gamma(_, Id, B), T) :-
    short_stmt(B, BT), format(string(T), "Gamma(~w) = ~w", [Id, BT]).
cond_text(invert_stmt(_, IB), T) :-
    short_stmt(IB, IBT), format(string(T), "inverted body: ~w", [IBT]).
cond_text(G, T) :- format(string(T), "~q", [G]).

failure_text(is_true(V), T) :- !,
    format(string(T), "is_true?(~w) does not hold", [V]).
failure_text(is_false(V), T) :- !,
    format(string(T), "is_false?(~w) does not hold", [V]).
failure_text(apply_binop(Op, V1, V2, _), T) :-
    memberchk(Op, [div, rem]), V2 =:= 0, !,
    binop_symbol(Op, O),
    format(string(T), "~w ~w ~w is undefined (division by zero)", [V1, O, V2]).
failure_text(gamma(_, Id, _), T) :- !,
    format(string(T), "procedure ~w is not defined", [Id]).
failure_text(G, T) :- format(string(T), "~q", [G]).
