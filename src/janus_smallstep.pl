/*  janus_smallstep.pl -- small-step semantics of sequential Janus (Section 3 of the
    paper, "A Small-Step Semantics for Janus").

    A literal transcription of Figures "Small-step semantics: rules for basic
    constructs" (AssVarS, AssArrS, CallS, UnCallS, Seq1, Seq2) and "Small-step semantics:
    rules for if and for loop" (IfTrue1, IfTrue2, IfFalse1, IfFalse2, LoopMainS,
    LoopBaseS, Loop1, Loop2). Each rule is ONE clause of ss_step/4, with its premises in
    the order of the paper. Expressions are evaluated with the rules of Figure
    "Semantics of expressions" (eval_expr/3 of janus_bigstep.pl), as in the paper.

    Configurations (Lean names in SmallStep.lean in brackets):
      conf(Sigma, S, Stack)          <sigma, s, pi>                      [SSConfig]
    Stack items                                                          [StackItem]
      seq(S2)                        seq(s2)
      if_true(E2), if_false(E2)      if_true(e2), if_false(e2)
      loop1(E1,S1,E2,S2)             loop1(e1,s1,e2,s2)
      loop2(E1,S1,E2,S2)             loop2(e1,s1,e2,s2)
    The head of the list is the top of the stack.

    Gamma is the list of procedure declarations [proc(Id, Body), ...] (as for the
    big-step semantics, janus_bigstep:gamma/3); if a procedure is not declared, rules
    CallS and UnCallS do not apply and the computation is stuck.
*/

:- module(janus_smallstep,
          [ ss_step/4,              % +Gamma, +Conf, -Rule, -Conf1
            ss_initial/2,           % +Program, -Conf
            ss_final/1,             % +Conf
            ss_run/4,               % +Gamma, +Conf, -Steps, -Result
            run_program_ss/2,       % +Program, -FinalStore
            ss_conf_text/2,         % +Conf, -String
            ss_stack_text/2         % +Stack, -String
          ]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(janus_arith).
:- use_module(janus_store).
:- use_module(janus_bigstep, [eval_expr/3, gamma/3]).
:- use_module(janus_inverter, [invert_stmt/2]).
:- use_module(janus_trace, [short_stmt/2, store_text/2]).
:- use_module(janus_parser, [pp_expr/1]).

% --- Figure "Small-step semantics: rules for basic constructs" ------------------------

% Rule AssVarS
ss_step(_Gamma, conf(Sigma, assign_var(X, Op, E), Pi), 'AssVarS',
        conf(Sigma1, skip, Pi)) :-
    eval_expr(Sigma, E, V),
    store_get_var(Sigma, X, A),
    apply_assign_op(Op, A, V, R),
    store_set_var(Sigma, X, R, Sigma1).
% Rule AssArrS
ss_step(_Gamma, conf(Sigma, assign_arr(X, El, Op, E), Pi), 'AssArrS',
        conf(Sigma1, skip, Pi)) :-
    eval_expr(Sigma, El, Vl),
    eval_expr(Sigma, E, V),
    store_get_cell(Sigma, X, Vl, A),
    apply_assign_op(Op, A, V, R),
    store_set_cell(Sigma, X, Vl, R, Sigma1).
% Rule CallS
ss_step(Gamma, conf(Sigma, call(Id), Pi), 'CallS', conf(Sigma, Body, Pi)) :-
    gamma(Gamma, Id, Body).
% Rule UnCallS
ss_step(Gamma, conf(Sigma, uncall(Id), Pi), 'UnCallS', conf(Sigma, InvBody, Pi)) :-
    gamma(Gamma, Id, Body),
    invert_stmt(Body, InvBody).
% Rule Seq1
ss_step(_Gamma, conf(Sigma, seq(S1, S2), Pi), 'Seq1', conf(Sigma, S1, [seq(S2)|Pi])).
% Rule Seq2
ss_step(_Gamma, conf(Sigma, skip, [seq(S2)|Pi]), 'Seq2', conf(Sigma, S2, Pi)).

% --- Figure "Small-step semantics: rules for if and for loop" -------------------------

% Rule IfTrue1
ss_step(_Gamma, conf(Sigma, if_then_else(E1, S1, _S2, E2), Pi), 'IfTrue1',
        conf(Sigma, S1, [if_true(E2)|Pi])) :-
    eval_expr(Sigma, E1, V1),
    is_true(V1).
% Rule IfTrue2
ss_step(_Gamma, conf(Sigma, skip, [if_true(E2)|Pi]), 'IfTrue2', conf(Sigma, skip, Pi)) :-
    eval_expr(Sigma, E2, V2),
    is_true(V2).
% Rule IfFalse1
ss_step(_Gamma, conf(Sigma, if_then_else(E1, _S1, S2, E2), Pi), 'IfFalse1',
        conf(Sigma, S2, [if_false(E2)|Pi])) :-
    eval_expr(Sigma, E1, V1),
    is_false(V1).
% Rule IfFalse2
ss_step(_Gamma, conf(Sigma, skip, [if_false(E2)|Pi]), 'IfFalse2', conf(Sigma, skip, Pi)) :-
    eval_expr(Sigma, E2, V2),
    is_false(V2).
% Rule LoopMainS
ss_step(_Gamma, conf(Sigma, loop(E1, S1, S2, E2), Pi), 'LoopMainS',
        conf(Sigma, S1, [loop1(E1, S1, E2, S2)|Pi])) :-
    eval_expr(Sigma, E1, V1),
    is_true(V1).
% Rule LoopBaseS
ss_step(_Gamma, conf(Sigma, skip, [loop1(_E1, _S1, E2, _S2)|Pi]), 'LoopBaseS',
        conf(Sigma, skip, Pi)) :-
    eval_expr(Sigma, E2, V2),
    is_true(V2).
% Rule Loop1
ss_step(_Gamma, conf(Sigma, skip, [loop1(E1, S1, E2, S2)|Pi]), 'Loop1',
        conf(Sigma, S2, [loop2(E1, S1, E2, S2)|Pi])) :-
    eval_expr(Sigma, E2, V2),
    is_false(V2).
% Rule Loop2
ss_step(_Gamma, conf(Sigma, skip, [loop2(E1, S1, E2, S2)|Pi]), 'Loop2',
        conf(Sigma, S1, [loop1(E1, S1, E2, S2)|Pi])) :-
    eval_expr(Sigma, E1, V1),
    is_false(V1).

% --- Runs ----------------------------------------------------------------------------

%!  ss_initial(+Program, -Conf) is det.
%   The initial configuration <eps, s, []> of a program p = (s p1 ... pn).
ss_initial(program(Main, _Procs), conf(Sigma0, Main, [])) :-
    store_empty(Sigma0).

%!  ss_final(+Conf) is semidet.
%   A final configuration <sigma, skip, []>.
ss_final(conf(_, skip, [])).

%!  ss_run(+Gamma, +Conf, -Steps, -Result) is det.
%   Applies the transition rules until a final configuration is reached or no rule
%   applies. Steps is the list of steps(Rule, Conf1) performed; Result is
%   final(Conf) or stuck(Conf). The transition relation is deterministic (Lean:
%   SmallStep.det), so the first applicable rule is the only one.
ss_run(Gamma, C, Steps, Result) :-
    (   ss_final(C)
    ->  Steps = [], Result = final(C)
    ;   ss_step(Gamma, C, Rule, C1)
    ->  Steps = [step(Rule, C1)|Steps1],
        ss_run(Gamma, C1, Steps1, Result)
    ;   Steps = [], Result = stuck(C)
    ).

%!  run_program_ss(+Program, -FinalStore) is semidet.
%   Runs a program with the small-step semantics; fails if it gets stuck
%   (Theorem "equiv": succeeds iff run_program/2 succeeds, with the same store).
run_program_ss(program(Main, Procs), FinalStore) :-
    ss_initial(program(Main, Procs), C0),
    ss_run(Procs, C0, _, final(conf(FinalStore, skip, []))).

% --- Printing ------------------------------------------------------------------------

%!  ss_conf_text(+Conf, -String) is det.
%   <{x=1}, x += 3, [seq(call f), loop1(...)]>
ss_conf_text(conf(Sigma, S, Pi), T) :-
    store_text(Sigma, ST),
    short_stmt(S, StT),
    ss_stack_text(Pi, PT),
    format(string(T), "<~w, ~w, ~w>", [ST, StT, PT]).

%!  ss_stack_text(+Stack, -String) is det.
ss_stack_text(Pi, T) :-
    maplist(item_text, Pi, Ts),
    atomic_list_concat(Ts, ' : ', Inner),
    (   Pi == []
    ->  T = "[]"
    ;   format(string(T), "~w : []", [Inner])
    ).

item_text(seq(S), T) :- short_stmt(S, ST), format(string(T), "seq(~w)", [ST]).
item_text(if_true(E), T) :- expr_text(E, ET), format(string(T), "if_true(~w)", [ET]).
item_text(if_false(E), T) :- expr_text(E, ET), format(string(T), "if_false(~w)", [ET]).
item_text(loop1(E1, _, E2, _), T) :-
    expr_text(E1, T1), expr_text(E2, T2),
    format(string(T), "loop1(~w,s1,~w,s2)", [T1, T2]).
item_text(loop2(E1, _, E2, _), T) :-
    expr_text(E1, T1), expr_text(E2, T2),
    format(string(T), "loop2(~w,s1,~w,s2)", [T1, T2]).

expr_text(E, T) :- with_output_to(string(T), pp_expr(E)).
