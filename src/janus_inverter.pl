/*  janus_inverter.pl -- the inverter function I of Figure 4 ("Inverter function for
    Janus statements"), clause by clause (Lean: ModOp.invert, Stmt.invert,
    ProcDecl.invert in Inverter.lean), and the well-formedness side condition of
    reversible assignments (Lean: Stmt.WellFormed in Syntax.lean).
*/

:- module(janus_inverter,
          [ invert_op/2,            % ?Op, ?InvOp
            invert_stmt/2,          % +Stmt, -InvStmt
            invert_proc/2,          % +Proc, -InvProc
            expr_vars/2,            % +Expr, -Vars
            well_formed_stmt/1,     % +Stmt
            well_formed_program/1   % +Program
          ]).

:- use_module(janus_arith, [inverse_assign_op/2]).

%!  invert_op(?Op, ?InvOp) is det.
%   I_op[[+]] = -,  I_op[[-]] = +,  I_op[[^]] = ^   (defined in janus_arith.pl).
invert_op(Op, InvOp) :- inverse_assign_op(Op, InvOp).

%!  invert_stmt(+Stmt, -InvStmt) is det.

% I[[x op= e]] = x I_op[[op]]= e
invert_stmt(assign_var(X, Op, E), assign_var(X, IOp, E)) :-
    invert_op(Op, IOp).
% I[[x[e1] op= e2]] = x[e1] I_op[[op]]= e2
invert_stmt(assign_arr(X, E1, Op, E2), assign_arr(X, E1, IOp, E2)) :-
    invert_op(Op, IOp).
% I[[if e1 then s1 else s2 fi e2]] = if e2 then I[[s1]] else I[[s2]] fi e1
invert_stmt(if_then_else(E1, S1, S2, E2), if_then_else(E2, IS1, IS2, E1)) :-
    invert_stmt(S1, IS1),
    invert_stmt(S2, IS2).
% I[[from e1 do s1 loop s2 until e2]] = from e2 do I[[s1]] loop I[[s2]] until e1
invert_stmt(loop(E1, S1, S2, E2), loop(E2, IS1, IS2, E1)) :-
    invert_stmt(S1, IS1),
    invert_stmt(S2, IS2).
% I[[call id]] = uncall id
invert_stmt(call(Id), uncall(Id)).
% I[[uncall id]] = call id
invert_stmt(uncall(Id), call(Id)).
% I[[skip]] = skip
invert_stmt(skip, skip).
% I[[s1 s2]] = I[[s2]] I[[s1]]
invert_stmt(seq(S1, S2), seq(IS2, IS1)) :-
    invert_stmt(S1, IS1),
    invert_stmt(S2, IS2).

%!  invert_proc(+Proc, -InvProc) is det.
%   I[[procedure id s]] = procedure id^-1 I[[s]]. The name id^-1 is represented by the
%   term inverse(Id). Not used by the semantics: rule UnCall inverts the body directly.
invert_proc(proc(Id, S), proc(inverse(Id), IS)) :-
    invert_stmt(S, IS).

%!  expr_vars(+Expr, -Vars) is det.
%   The variables (scalar or array names) occurring in Expr (Lean: Expr.vars).
expr_vars(const(_), []).
expr_vars(var(X), [X]).
expr_vars(arr(X, E), [X|Vs]) :- expr_vars(E, Vs).
expr_vars(binop(_, E1, E2), Vs) :-
    expr_vars(E1, Vs1),
    expr_vars(E2, Vs2),
    append(Vs1, Vs2, Vs).

%!  well_formed_stmt(+Stmt) is semidet.
%   In every reversible assignment x op= e (resp. x[e1] op= e2) the variable x does not
%   occur in e (resp. in e1 and e2) (Lean: Stmt.WellFormed). The big-step rules do not
%   check this condition; the inversion property needs it.
well_formed_stmt(assign_var(X, _, E)) :-
    expr_vars(E, Vs), \+ memberchk(X, Vs).
well_formed_stmt(assign_arr(X, E1, _, E2)) :-
    expr_vars(E1, Vs1), \+ memberchk(X, Vs1),
    expr_vars(E2, Vs2), \+ memberchk(X, Vs2).
well_formed_stmt(if_then_else(_, S1, S2, _)) :-
    well_formed_stmt(S1), well_formed_stmt(S2).
well_formed_stmt(loop(_, S1, S2, _)) :-
    well_formed_stmt(S1), well_formed_stmt(S2).
well_formed_stmt(call(_)).
well_formed_stmt(uncall(_)).
well_formed_stmt(skip).
well_formed_stmt(seq(S1, S2)) :-
    well_formed_stmt(S1), well_formed_stmt(S2).

%!  well_formed_program(+Program) is semidet.
%   All statements are well formed and procedure names are pairwise distinct
%   (Lean: Program.WellFormed).
well_formed_program(program(Main, Procs)) :-
    well_formed_stmt(Main),
    forall(member(proc(_, Body), Procs), well_formed_stmt(Body)),
    findall(Id, member(proc(Id, _), Procs), Ids),
    sort(Ids, Sorted),
    length(Ids, N), length(Sorted, N).
