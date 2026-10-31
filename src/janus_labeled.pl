/*  janus_labeled.pl -- labeled programs and control-flow graphs (Section 4 of the
    paper, "A Reversible Semantics for Janus": Figures "Extended language syntax",
    "Entry and exit points" and "Control-flow graph of a Janus program").

    Labeled statements (Lean: LStmt Label in Labeled.lean), one functor per production
    of Figure "Extended language syntax":
      lassign_var(X, Op, E, L)            [x op= e]^l
      lassign_arr(X, E1, Op, E2, L)       [x[e1] op= e2]^l
      lif(E1, L1, S1, S2, E2, L2)         if [e1]^l1 then s1 else s2 fi [e2]^l2
      lloop(E1, L1, S1, S2, E2, L2)       from [e1]^l1 do s1 loop s2 until [e2]^l2
      lcall(Id, L), luncall(Id, L)        [call id]^l, [uncall id]^l
      lskip(L), lstart(L), lstop(L)       [skip]^l, [start]^l, [stop]^l
      lseq(S1, S2)                        s1 s2
    Labels are the positive integers 1, 2, ...

    Elementary blocks o (block(l) = o):
      assign_var(X, Op, E), assign_arr(X, E1, Op, E2), cond(E), call(Id), uncall(Id),
      skip, start, stop.

    The labeled version of a program (Lean: Program.toLabeled) is obtained as in the
    paper: every body s (main program and procedures) becomes start (s stop); for each
    procedure "procedure id s" the inverse procedure "procedure id^-1 I[[start s stop]]"
    is added (with I[[start]] = stop and I[[stop]] = start); then labels are assigned
    consecutively, from 1, in textual order: main program, procedures, inverse
    procedures (this reproduces the labels of Figure "Sum3").

    Labeled programs:  lprog(Main, Procs), Procs = [lproc(Name, Body), ...] with
    Name = Id (procedure id) or inv(Id) (procedure id^-1, printed as rev-id).

    To avoid recomputing the CFG at every step, the reversible semantics works on a
    precomputed "program info" term (info_of_program/2):
      info(LProg, Blocks, Ctx, Succ, Pred)
    where Blocks maps each label to its block, Ctx maps the label of every test and
    assertion to the conditional or loop where it occurs (the partial function ctx),
    and Succ/Pred map each label to its successors/predecessors in flow(p), the union
    of the CFGs of the main program and of every (inverse) procedure.
*/

:- module(janus_labeled,
          [ invert_xstmt/2,         % +XStmt, -InvXStmt
            with_start_stop/2,      % +Stmt, -XStmt
            label_stmt/4,           % +XStmt, +N0, -LStmt, -N
            labeled_program/2,      % +Program, -LProg
            linvert/2,              % +LStmt, -InvLStmt (labels stay attached)
            lstmt_blocks/2,         % +LStmt, -Pairs  (Label-Block, textual order)
            lstmt_labels/2,         % +LStmt, -Labels
            lprog_blocks/2,         % +LProg, -Pairs
            entry/2,                % +LStmt, -Label
            exit/2,                 % +LStmt, -Label
            flow/2,                 % +LStmt, -Edges (ordered set of L1-L2)
            lprog_flow/2,           % +LProg, -Edges
            unique_labels/1,        % +LProg
            info_of_program/2,      % +Program, -Info
            info_lprog/2,           % +Info, -LProg
            block/3,                % +Info, +Label, -Block
            ctx/3,                  % +Info, +Label, -Stmt
            edge/3,                 % +Info, ?L1, ?L2   (L1 -> L2 in flow(p))
            proc_body/3,            % +Info, +Name, -Body  (Gamma(id), Gamma(id^-1))
            main_cfg/2,             % +Info, -Edges
            proc_cfg/3,             % +Info, +Name, -Edges
            pp_lprog/1,             % +LProg
            pp_lstmt/2,             % +Indent, +LStmt
            pp_lprog_marked/2,      % +LProg, +Marks
            lstmt_short/2,          % +LStmt, -String
            block_text/2,           % +Block, -String
            edges_text/2            % +Edges, -String
          ]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(janus_inverter, [invert_op/2]).
:- use_module(janus_parser, [pp_expr/1, assign_symbol/2]).

% ======================================================================================
% Unlabeled extended statements: the original syntax plus the atoms start and stop
% ======================================================================================

%!  invert_xstmt(+XStmt, -InvXStmt) is det.
%   The inverter of Figure 4, extended with I[[start]] = stop and I[[stop]] = start.
invert_xstmt(start, stop).
invert_xstmt(stop, start).
invert_xstmt(assign_var(X, Op, E), assign_var(X, IOp, E)) :- invert_op(Op, IOp).
invert_xstmt(assign_arr(X, E1, Op, E2), assign_arr(X, E1, IOp, E2)) :- invert_op(Op, IOp).
invert_xstmt(if_then_else(E1, S1, S2, E2), if_then_else(E2, IS1, IS2, E1)) :-
    invert_xstmt(S1, IS1), invert_xstmt(S2, IS2).
invert_xstmt(loop(E1, S1, S2, E2), loop(E2, IS1, IS2, E1)) :-
    invert_xstmt(S1, IS1), invert_xstmt(S2, IS2).
invert_xstmt(call(Id), uncall(Id)).
invert_xstmt(uncall(Id), call(Id)).
invert_xstmt(skip, skip).
invert_xstmt(seq(S1, S2), seq(IS2, IS1)) :-
    invert_xstmt(S1, IS1), invert_xstmt(S2, IS2).

%!  with_start_stop(+Stmt, -XStmt) is det.
%   A body s delimited by start and stop: start (s stop).
with_start_stop(S, seq(start, seq(S, stop))).

% ======================================================================================
% Labeling
% ======================================================================================

%!  label_stmt(+XStmt, +N0, -LStmt, -N) is det.
%   Labels the elementary blocks with N0, N0+1, ..., in textual order; N is the next
%   unused label (Lean: LStmt.labelFrom).
label_stmt(assign_var(X, Op, E), N0, lassign_var(X, Op, E, N0), N) :- N is N0 + 1.
label_stmt(assign_arr(X, E1, Op, E2), N0, lassign_arr(X, E1, Op, E2, N0), N) :- N is N0 + 1.
label_stmt(if_then_else(E1, S1, S2, E2), N0, lif(E1, N0, LS1, LS2, E2, L2), N) :-
    N1 is N0 + 1,
    label_stmt(S1, N1, LS1, N2),
    label_stmt(S2, N2, LS2, L2),
    N is L2 + 1.
label_stmt(loop(E1, S1, S2, E2), N0, lloop(E1, N0, LS1, LS2, E2, L2), N) :-
    N1 is N0 + 1,
    label_stmt(S1, N1, LS1, N2),
    label_stmt(S2, N2, LS2, L2),
    N is L2 + 1.
label_stmt(call(Id), N0, lcall(Id, N0), N) :- N is N0 + 1.
label_stmt(uncall(Id), N0, luncall(Id, N0), N) :- N is N0 + 1.
label_stmt(skip, N0, lskip(N0), N) :- N is N0 + 1.
label_stmt(start, N0, lstart(N0), N) :- N is N0 + 1.
label_stmt(stop, N0, lstop(N0), N) :- N is N0 + 1.
label_stmt(seq(S1, S2), N0, lseq(LS1, LS2), N) :-
    label_stmt(S1, N0, LS1, N1),
    label_stmt(S2, N1, LS2, N).

%!  labeled_program(+Program, -LProg) is det.
%   The labeled version of a program (Lean: Program.toLabeled).
labeled_program(program(Main, Procs), lprog(LMain, LProcs)) :-
    with_start_stop(Main, XMain),
    label_stmt(XMain, 1, LMain, N1),
    findall(Id-XBody,
            ( member(proc(Id, Body), Procs), with_start_stop(Body, XBody) ),
            Fwd),
    findall(inv(Id)-IBody,
            ( member(Id-XBody, Fwd), invert_xstmt(XBody, IBody) ),
            Inv),
    append(Fwd, Inv, XProcs),
    label_procs(XProcs, N1, LProcs).

label_procs([], _, []).
label_procs([Name-XBody|Ps], N0, [lproc(Name, LBody)|LPs]) :-
    label_stmt(XBody, N0, LBody, N1),
    label_procs(Ps, N1, LPs).

%!  linvert(+LStmt, -InvLStmt) is det.
%   The inverter on labeled statements; each label stays attached to its block
%   (Lean: LStmt.invert). Used to check the lemma flow^-1(s) = flow(I[[s]]).
linvert(lassign_var(X, Op, E, L), lassign_var(X, IOp, E, L)) :- invert_op(Op, IOp).
linvert(lassign_arr(X, E1, Op, E2, L), lassign_arr(X, E1, IOp, E2, L)) :- invert_op(Op, IOp).
linvert(lif(E1, L1, S1, S2, E2, L2), lif(E2, L2, IS1, IS2, E1, L1)) :-
    linvert(S1, IS1), linvert(S2, IS2).
linvert(lloop(E1, L1, S1, S2, E2, L2), lloop(E2, L2, IS1, IS2, E1, L1)) :-
    linvert(S1, IS1), linvert(S2, IS2).
linvert(lcall(Id, L), luncall(Id, L)).
linvert(luncall(Id, L), lcall(Id, L)).
linvert(lskip(L), lskip(L)).
linvert(lstart(L), lstop(L)).
linvert(lstop(L), lstart(L)).
linvert(lseq(S1, S2), lseq(IS2, IS1)) :- linvert(S1, IS1), linvert(S2, IS2).

% ======================================================================================
% Blocks, entry and exit points, CFG
% ======================================================================================

%!  lstmt_blocks(+LStmt, -Pairs) is det.
%   The pairs Label-Block such that [o]^l occurs in the statement, in textual order.
lstmt_blocks(S, Pairs) :- phrase(blocks(S), Pairs).

blocks(lassign_var(X, Op, E, L)) --> [L-assign_var(X, Op, E)].
blocks(lassign_arr(X, E1, Op, E2, L)) --> [L-assign_arr(X, E1, Op, E2)].
blocks(lif(E1, L1, S1, S2, E2, L2)) --> [L1-cond(E1)], blocks(S1), blocks(S2), [L2-cond(E2)].
blocks(lloop(E1, L1, S1, S2, E2, L2)) --> [L1-cond(E1)], blocks(S1), blocks(S2), [L2-cond(E2)].
blocks(lcall(Id, L)) --> [L-call(Id)].
blocks(luncall(Id, L)) --> [L-uncall(Id)].
blocks(lskip(L)) --> [L-skip].
blocks(lstart(L)) --> [L-start].
blocks(lstop(L)) --> [L-stop].
blocks(lseq(S1, S2)) --> blocks(S1), blocks(S2).

%!  lstmt_labels(+LStmt, -Labels) is det.
lstmt_labels(S, Ls) :- lstmt_blocks(S, Ps), pairs_keys(Ps, Ls).

%!  lprog_blocks(+LProg, -Pairs) is det.
lprog_blocks(lprog(Main, Procs), Pairs) :-
    lstmt_blocks(Main, P0),
    findall(P, ( member(lproc(_, B), Procs), lstmt_blocks(B, Ps), member(P, Ps) ), P1),
    append(P0, P1, Pairs).

%!  unique_labels(+LProg) is semidet.
%   "All labels are unique in a program."
unique_labels(LP) :-
    lprog_blocks(LP, Pairs),
    pairs_keys(Pairs, Ls),
    sort(Ls, Sorted),
    length(Ls, N), length(Sorted, N).

%!  entry(+LStmt, -Label) is det.   (Figure "Entry and exit points")
entry(lif(_, L1, _, _, _, _), L1).
entry(lloop(_, L1, _, _, _, _), L1).
entry(lseq(S1, _), L) :- entry(S1, L).
entry(lassign_var(_, _, _, L), L).
entry(lassign_arr(_, _, _, _, L), L).
entry(lcall(_, L), L).
entry(luncall(_, L), L).
entry(lskip(L), L).
entry(lstart(L), L).
entry(lstop(L), L).

%!  exit(+LStmt, -Label) is det.
exit(lif(_, _, _, _, _, L2), L2).
exit(lloop(_, _, _, _, _, L2), L2).
exit(lseq(_, S2), L) :- exit(S2, L).
exit(lassign_var(_, _, _, L), L).
exit(lassign_arr(_, _, _, _, L), L).
exit(lcall(_, L), L).
exit(luncall(_, L), L).
exit(lskip(L), L).
exit(lstart(L), L).
exit(lstop(L), L).

%!  flow(+LStmt, -Edges) is det.
%   The edges of the CFG of a statement (Figure "Control-flow graph of a Janus
%   program"), as an ordered set of pairs L1-L2.
flow(lif(_, L1, S1, S2, _, L2), Edges) :-
    entry(S1, N1), exit(S1, X1), entry(S2, N2), exit(S2, X2),
    flow(S1, F1), flow(S2, F2),
    list_to_ord_set([L1-N1, X1-L2, L1-N2, X2-L2], F0),
    ord_union([F0, F1, F2], Edges).
flow(lloop(_, L1, S1, S2, _, L2), Edges) :-
    entry(S1, N1), exit(S1, X1), entry(S2, N2), exit(S2, X2),
    flow(S1, F1), flow(S2, F2),
    list_to_ord_set([L1-N1, X1-L2, L2-N2, X2-L1], F0),
    ord_union([F0, F1, F2], Edges).
flow(lseq(S1, S2), Edges) :-
    exit(S1, X1), entry(S2, N2),
    flow(S1, F1), flow(S2, F2),
    ord_union([[X1-N2], F1, F2], Edges).
flow(lassign_var(_, _, _, _), []).
flow(lassign_arr(_, _, _, _, _), []).
flow(lcall(_, _), []).
flow(luncall(_, _), []).
flow(lskip(_), []).
flow(lstart(_), []).
flow(lstop(_), []).

%!  lprog_flow(+LProg, -Edges) is det.
%   flow(p): the union of the CFGs of the main program and of every procedure and
%   inverse procedure.
lprog_flow(lprog(Main, Procs), Edges) :-
    flow(Main, F0),
    findall(F, ( member(lproc(_, B), Procs), flow(B, F) ), Fs),
    ord_union([F0|Fs], Edges).

% ======================================================================================
% Program info
% ======================================================================================

%!  info_of_program(+Program, -Info) is det.
info_of_program(Program, info(LP, Blocks, Ctx, Succ, Pred)) :-
    labeled_program(Program, LP),
    lprog_blocks(LP, BPairs),
    list_to_assoc(BPairs, Blocks),
    LP = lprog(Main, Procs),
    findall(L-T,
            ( ( B = Main ; member(lproc(_, B), Procs) ),
              sub_cond(B, T),
              cond_labels(T, L) ),
            CPairs0),
    sort(CPairs0, CPairs),
    list_to_assoc(CPairs, Ctx),
    lprog_flow(LP, Edges),
    adjacency(Edges, Succ),
    findall(B2-A2, member(A2-B2, Edges), Rev0),
    sort(Rev0, Rev),
    adjacency(Rev, Pred).

%  sub_cond(+LStmt, -T): T is a conditional or a loop occurring in the statement.
sub_cond(T, T) :- functor(T, F, _), memberchk(F, [lif, lloop]).
sub_cond(lif(_, _, S1, S2, _, _), T) :- ( sub_cond(S1, T) ; sub_cond(S2, T) ).
sub_cond(lloop(_, _, S1, S2, _, _), T) :- ( sub_cond(S1, T) ; sub_cond(S2, T) ).
sub_cond(lseq(S1, S2), T) :- ( sub_cond(S1, T) ; sub_cond(S2, T) ).

cond_labels(lif(_, L1, _, _, _, L2), L) :- ( L = L1 ; L = L2 ).
cond_labels(lloop(_, L1, _, _, _, L2), L) :- ( L = L1 ; L = L2 ).

adjacency(Edges, Assoc) :-
    findall(A-B, member(A-B, Edges), Ps),
    group_pairs_by_key(Ps, Groups),
    list_to_assoc(Groups, Assoc).

%!  info_lprog(+Info, -LProg) is det.
info_lprog(info(LP, _, _, _, _), LP).

%!  block(+Info, +Label, -Block) is semidet.   block(l) = o
block(info(_, Blocks, _, _, _), L, B) :- get_assoc(L, Blocks, B).

%!  ctx(+Info, +Label, -Stmt) is semidet.   ctx(l) = t
ctx(info(_, _, Ctx, _, _), L, T) :- get_assoc(L, Ctx, T).

%!  edge(+Info, ?L1, ?L2) is nondet.
%   L1 -> L2 belongs to flow(p). At least one of L1, L2 must be bound.
edge(info(_, _, _, Succ, Pred), L1, L2) :-
    (   nonvar(L1)
    ->  get_assoc(L1, Succ, Ss), member(L2, Ss)
    ;   get_assoc(L2, Pred, Ps), member(L1, Ps)
    ).

%!  proc_body(+Info, +Name, -Body) is semidet.
%   Gamma(id) (Name = Id) and Gamma(id^-1) (Name = inv(Id)): the labeled body, with
%   start and stop, of the first procedure with that name.
proc_body(info(lprog(_, Procs), _, _, _, _), Name, Body) :-
    memberchk(lproc(Name, Body), Procs).

%!  main_cfg(+Info, -Edges) is det.
main_cfg(info(lprog(Main, _), _, _, _, _), Edges) :- flow(Main, Edges).

%!  proc_cfg(+Info, +Name, -Edges) is semidet.
proc_cfg(Info, Name, Edges) :- proc_body(Info, Name, B), flow(B, Edges).

% ======================================================================================
% Printing
% ======================================================================================

%!  pp_lprog(+LProg) is det.
%   Prints a labeled program as in Figure "Sum3".
pp_lprog(LP) :- pp_lprog_marked(LP, []).

%!  pp_lprog_marked(+LProg, +Marks) is det.
%   As pp_lprog/1, but every line whose label L has a pair L-Marker in Marks is
%   prefixed with Marker (used by the explorer to show the program counter).
pp_lprog_marked(lprog(Main, Procs), Marks) :-
    pp_lstmt_m(Marks, 0, Main),
    forall(member(lproc(Name, Body), Procs),
           ( name_text(Name, NT),
             line_prefix(Marks, none),
             format("procedure ~w~n", [NT]),
             pp_lstmt_m(Marks, 2, Body) )).

name_text(inv(Id), T) :- !, format(string(T), "rev-~w", [Id]).
name_text(Id, Id).

%!  pp_lstmt(+Indent, +LStmt) is det.
pp_lstmt(I, S) :- pp_lstmt_m([], I, S).

pp_lstmt_m(M, I, lseq(S1, S2)) :- !, pp_lstmt_m(M, I, S1), pp_lstmt_m(M, I, S2).
pp_lstmt_m(M, I, lif(E1, L1, S1, S2, E2, L2)) :- !,
    I2 is I + 2,
    line_prefix(M, L1), indent(I), write('if ['), pp_expr(E1), format("]^~w then~n", [L1]),
    pp_lstmt_m(M, I2, S1),
    line_prefix(M, none), indent(I), write(else), nl,
    pp_lstmt_m(M, I2, S2),
    line_prefix(M, L2), indent(I), write('fi ['), pp_expr(E2), format("]^~w~n", [L2]).
pp_lstmt_m(M, I, lloop(E1, L1, S1, S2, E2, L2)) :- !,
    I2 is I + 2,
    line_prefix(M, L1), indent(I), write('from ['), pp_expr(E1), format("]^~w do~n", [L1]),
    pp_lstmt_m(M, I2, S1),
    line_prefix(M, none), indent(I), write(loop), nl,
    pp_lstmt_m(M, I2, S2),
    line_prefix(M, L2), indent(I), write('until ['), pp_expr(E2), format("]^~w~n", [L2]).
pp_lstmt_m(M, I, S) :-
    lstmt_short(S, T), entry(S, L),
    line_prefix(M, L), indent(I), format("~w~n", [T]).

line_prefix([], _) :- !.
line_prefix(Marks, L) :-
    (   memberchk(L-Marker, Marks)
    ->  format("~w ", [Marker])
    ;   write('   ')
    ).

indent(I) :- forall(between(1, I, _), put_char(' ')).

%!  lstmt_short(+LStmt, -String) is det.
%   A one-line abbreviation of a labeled statement.
lstmt_short(lif(E1, L1, _, _, E2, L2), T) :- !,
    expr_text(E1, T1), expr_text(E2, T2),
    format(string(T), "if [~w]^~w then ... else ... fi [~w]^~w", [T1, L1, T2, L2]).
lstmt_short(lloop(E1, L1, _, _, E2, L2), T) :- !,
    expr_text(E1, T1), expr_text(E2, T2),
    format(string(T), "from [~w]^~w do ... loop ... until [~w]^~w", [T1, L1, T2, L2]).
lstmt_short(lseq(S1, _), T) :- !,
    lstmt_short(S1, T1), format(string(T), "~w ...", [T1]).
lstmt_short(S, T) :-
    lstmt_blocks(S, [L-B]),
    block_text(B, BT),
    format(string(T), "[~w]^~w", [BT, L]).

%!  block_text(+Block, -String) is det.
block_text(assign_var(X, Op, E), T) :-
    assign_symbol(Op, O), expr_text(E, ET), format(string(T), "~w ~w ~w", [X, O, ET]).
block_text(assign_arr(X, E1, Op, E2), T) :-
    assign_symbol(Op, O), expr_text(E1, T1), expr_text(E2, T2),
    format(string(T), "~w[~w] ~w ~w", [X, T1, O, T2]).
block_text(cond(E), T) :- expr_text(E, T).
block_text(call(Id), T) :- format(string(T), "call ~w", [Id]).
block_text(uncall(Id), T) :- format(string(T), "uncall ~w", [Id]).
block_text(skip, "skip").
block_text(start, "start").
block_text(stop, "stop").

%!  edges_text(+Edges, -String) is det.   {(1,2), (2,3)}
edges_text(Edges, T) :-
    maplist([A-B, S]>>format(string(S), "(~w,~w)", [A, B]), Edges, Ss),
    atomic_list_concat(Ss, ', ', Inner),
    format(string(T), "{~w}", [Inner]).

expr_text(E, T) :- with_output_to(string(T), pp_expr(E)).
