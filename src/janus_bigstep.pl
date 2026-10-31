/*  janus_bigstep.pl -- big-step semantics of sequential Janus

    A literal transcription of Figures "Semantics of expressions" (rules Con, Var, Arr,
    Bop) and "Big-step semantics of sequential Janus" (rules AssVar, AssArr, Call,
    UnCall, Seq, IfTrue, IfFalse, LoopMain, LoopBase, LoopRec, Skip). Each rule is ONE
    clause, with its premises in the same order as in the paper.

    Judgements (Lean names in Semantics.lean in brackets):
      eval_expr(Sigma, E, V)                      <sigma, e> => v          [EvalExpr]
      exec(Gamma, Sigma, S, Sigma1)               <sigma, s> => sigma1     [BigStep .stmt]
      exec_loop(Gamma, Sigma, E1,S1,E2,S2, Sigma1)
                                    <sigma, (e1,s1,e2,s2)> => sigma1       [BigStep .loopCont]

    Gamma is the list of procedure declarations [proc(Id, Body), ...]; Gamma(id) is the
    body of the FIRST declaration named id (Lean: Program.procEnv); if there is none,
    rules Call and UnCall do not apply, so there is no derivation.

    No derivation (assertion failure, division by zero, undefined procedure,
    non-termination aside) means that the goal fails.
*/

:- module(janus_bigstep,
          [ eval_expr/3,            % +Sigma, +Expr, -V
            exec/4,                 % +Gamma, +Sigma, +Stmt, -Sigma1
            exec_loop/7,            % +Gamma, +Sigma, +E1, +S1, +E2, +S2, -Sigma1
            run_program/2,          % +Program, -FinalStore
            gamma/3                 % +Gamma, +Id, -Body   (Gamma(id))
          ]).

:- use_module(janus_arith).
:- use_module(janus_store).
:- use_module(janus_inverter, [invert_stmt/2]).

%!  gamma(+Gamma, +Id, -Body) is semidet.
%   Gamma(id): the body of the first procedure declared with name Id.
gamma(Gamma, Id, Body) :- memberchk(proc(Id, Body), Gamma).

% --- Figure "Semantics of expressions" -----------------------------------------------

% Rule Con
eval_expr(_Sigma, const(C), C).
% Rule Var
eval_expr(Sigma, var(X), V) :-
    store_get_var(Sigma, X, V).
% Rule Arr
eval_expr(Sigma, arr(X, E), V) :-
    eval_expr(Sigma, E, I),
    store_get_cell(Sigma, X, I, V).
% Rule Bop
eval_expr(Sigma, binop(Op, E1, E2), V) :-
    eval_expr(Sigma, E1, V1),
    eval_expr(Sigma, E2, V2),
    apply_binop(Op, V1, V2, V).

% --- Figure "Big-step semantics of sequential Janus" ---------------------------------

% Rule AssVar
exec(_Gamma, Sigma, assign_var(X, Op, E), Sigma1) :-
    eval_expr(Sigma, E, V),
    store_get_var(Sigma, X, A),
    apply_assign_op(Op, A, V, R),
    store_set_var(Sigma, X, R, Sigma1).
% Rule AssArr
exec(_Gamma, Sigma, assign_arr(X, El, Op, E), Sigma1) :-
    eval_expr(Sigma, El, Vl),
    eval_expr(Sigma, E, V),
    store_get_cell(Sigma, X, Vl, A),
    apply_assign_op(Op, A, V, R),
    store_set_cell(Sigma, X, Vl, R, Sigma1).
% Rule Call
exec(Gamma, Sigma, call(Id), Sigma1) :-
    gamma(Gamma, Id, Body),
    exec(Gamma, Sigma, Body, Sigma1).
% Rule UnCall
exec(Gamma, Sigma, uncall(Id), Sigma1) :-
    gamma(Gamma, Id, Body),
    invert_stmt(Body, InvBody),
    exec(Gamma, Sigma, InvBody, Sigma1).
% Rule Seq
exec(Gamma, Sigma, seq(S1, S2), Sigma2) :-
    exec(Gamma, Sigma, S1, Sigma1),
    exec(Gamma, Sigma1, S2, Sigma2).
% Rule IfTrue
exec(Gamma, Sigma, if_then_else(E1, S1, _S2, E2), Sigma1) :-
    eval_expr(Sigma, E1, V1),
    is_true(V1),
    exec(Gamma, Sigma, S1, Sigma1),
    eval_expr(Sigma1, E2, V2),
    is_true(V2).
% Rule IfFalse
exec(Gamma, Sigma, if_then_else(E1, _S1, S2, E2), Sigma1) :-
    eval_expr(Sigma, E1, V1),
    is_false(V1),
    exec(Gamma, Sigma, S2, Sigma1),
    eval_expr(Sigma1, E2, V2),
    is_false(V2).
% Rule LoopMain
exec(Gamma, Sigma, loop(E1, S1, S2, E2), Sigma2) :-
    eval_expr(Sigma, E1, V1),
    is_true(V1),
    exec(Gamma, Sigma, S1, Sigma1),
    exec_loop(Gamma, Sigma1, E1, S1, E2, S2, Sigma2).
% Rule Skip
exec(_Gamma, Sigma, skip, Sigma).

% Rule LoopBase
exec_loop(_Gamma, Sigma, _E1, _S1, E2, _S2, Sigma) :-
    eval_expr(Sigma, E2, V2),
    is_true(V2).
% Rule LoopRec
exec_loop(Gamma, Sigma, E1, S1, E2, S2, Sigma3) :-
    eval_expr(Sigma, E2, V2),
    is_false(V2),
    exec(Gamma, Sigma, S2, Sigma1),
    eval_expr(Sigma1, E1, V1),
    is_false(V1),
    exec(Gamma, Sigma1, S1, Sigma2),
    exec_loop(Gamma, Sigma2, E1, S1, E2, S2, Sigma3).

%!  run_program(+Program, -FinalStore) is semidet.
%   Runs the main body from the empty store, with Gamma built from the procedure
%   declarations. The semantics is deterministic (Lean: BigStep.det), so once/1 only
%   removes the choicepoints left by the pairs IfTrue/IfFalse and LoopBase/LoopRec;
%   it does not change the set of answers.
run_program(program(Main, Procs), FinalStore) :-
    store_empty(Sigma0),
    once(exec(Procs, Sigma0, Main, FinalStore)).
