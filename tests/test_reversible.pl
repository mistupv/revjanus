/*  tests/test_reversible.pl -- plunit tests for the small-step semantics (Section 3),
    the labeled programs and CFGs, the reversible semantics (Section 4) and the
    explorer.

    Run with:   swipl -g run_tests -t halt tests/test_reversible.pl

    Besides the fixed tests (the examples, the Lean test programs and the Sum3
    figures of the paper), the unit "random" generates random programs with a fixed
    seed and checks, for each of them, that
      - big-step, small-step and reversible semantics agree (same final store, or all
        of them fail / get stuck)   [Theorem "equiv", Lemma "forward-rev"];
      - the small-step and the forward/backward reversible relations are
        deterministic;
      - every forward step k -> k' is undone by exactly one backward step k' -> k
        [Loop lemma], also in computations that get stuck;
      - running the backward rules from the last configuration reaches the initial
        configuration through the same configurations, in reverse order;
      - flow(I[s]) = swap(flow(s)) for every (labeled) procedure body, labels are
        unique, and "call m; uncall m" gives back the empty store.
*/

:- use_module('../src/janus').
:- use_module(library(plunit)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(random)).
:- use_module(library(time)).
:- use_module(library(process)).

% --- helpers ------------------------------------------------------------------------

examples_dir(Dir) :-
    source_file(examples_dir(_), File),
    file_directory_name(File, TestDir),
    directory_file_path(TestDir, '../examples', Dir).

example_file(Name, Path) :-
    examples_dir(Dir),
    directory_file_path(Dir, Name, Path).

%  janus_script(-Path): src/janus.pl (for the command-line tests).
janus_script(Path) :-
    examples_dir(Dir), directory_file_path(Dir, '../src/janus.pl', Path).

example_program(Name, P) :-
    example_file(Name, F), parse_file(F, P).

all_examples(['simple.jan', 'loops.jan', 'calls.jan', 'noprocs.jan', 'sum3.jan']).

% The programs of the Lean tests (as in test_janus.pl).
lean_programs([ "x += 3 x -= 1",
                "if x = 0 then x += 1 else x -= 1 fi x = 1",
                "if x != 0 then x += 1 else x -= 1 fi x = 1",
                "from i = 0 do skip loop i += 1 until i = 3",
                "call inc procedure inc x += 1",
                "uncall inc procedure inc x += 1",
                "a[i] ^= y y += 2 a[i + 1] -= y"
              ]).

% Programs without a derivation (Lean negative tests).
failing_programs([ "if x = 0 then x += 1 else skip fi x = 0",
                   "from i = 1 do skip loop skip until i = 0",
                   "call nope",
                   "uncall nope",
                   "x += 1 call f",
                   "x += 1 / 0",
                   "x += 1 % 0",
                   % the entry assertion holds again after s2: no rule applies
                   % (LoopMain requires that the previous label is not exit(s2))
                   "from x = 0 do skip loop skip until x = 1",
                   % uncall of a procedure whose inverse gets stuck
                   "uncall f procedure f if x = 0 then x += 1 else skip fi x = 1"
                 ]).

%  program(-Name, -Program): all the fixed test programs.
program(Src, P) :-
    lean_programs(Ps), member(Src, Ps), parse_program(Src, P).
program(N, P) :-
    all_examples(Ns), member(N, Ns), example_program(N, P).

%  The three semantics, with the final store as a sorted list, 'fail', or 'timeout'
%  (all the test programs terminate: a timeout means that a rule is wrong).
big(P, R) :-
    timed(( run_program(P, S) -> store_to_list(S, L), R = ok(L) ; R = fail ), R).
small(P, R) :-
    P = program(_, Procs),
    ss_initial(P, C0),
    timed(( ss_run(Procs, C0, _, Res),
            (   Res = final(conf(S, skip, [])) -> store_to_list(S, L), R = ok(L)
            ;   R = fail
            ) ), R).
rev(P, R) :-
    info_of_program(P, Info), rev_initial(Info, K0),
    timed(( fwd_run(Info, K0, _, Res),
            (   Res = final(rc(S, _, _, [])) -> store_to_list(S, L), R = ok(L)
            ;   R = fail
            ) ), R).

%  timed(:Goal, -R): runs Goal (which binds R) for at most 10 seconds; R = timeout
%  if the time limit is exceeded.
timed(Goal, R) :-
    catch(call_with_time_limit(10, Goal), time_limit_exceeded, R = timeout).

%  run_rev(+Info, +K, -Steps, -Res): fwd_run with a time limit (Res = timeout).
run_rev(Info, K, Steps, Res) :-
    catch(call_with_time_limit(10, fwd_run(Info, K, Steps, Res)),
          time_limit_exceeded, ( Steps = [], Res = timeout(K) )).

%  norm(+K, -K1): a configuration with the store as a list (two stores with the same
%  bindings can be different AVL trees).
norm(rc(S, L1, L2, Pi), rc(SL, L1, L2, Pi)) :- store_to_list(S, SL).

%  fwd_trace(+Info, -Ks): the configurations of the forward computation from the
%  initial configuration (normalized), and the result (final or stuck).
fwd_confs(Info, [K0|Ks], How) :-
    rev_initial(Info, K0),
    run_rev(Info, K0, Steps, Res),
    pairs_values_steps(Steps, Ks),
    functor(Res, How, 1).

pairs_values_steps([], []).
pairs_values_steps([step(_, K)|Ss], [K|Ks]) :- pairs_values_steps(Ss, Ks).

%  loop_lemma_ok(+Info, +Ks): for each pair of consecutive configurations k, k'
%  (a forward step), the only backward step from k' gives k.
loop_lemma_ok(_, [_]).
loop_lemma_ok(Info, [K, K1|Ks]) :-
    findall(N, ( bwd_step(Info, K1, _, B), norm(B, N) ), Bs),
    norm(K, NK),
    Bs == [NK],
    loop_lemma_ok(Info, [K1|Ks]).

%  fwd_deterministic(+Info, +Ks): at most one forward step from each configuration.
fwd_deterministic(Info, Ks) :-
    forall(member(K, Ks),
           ( findall(R, fwd_step(Info, K, R, _), Rs), length(Rs, N), N =< 1 )).

%  ss_deterministic(+P): at most one small-step transition from each configuration.
ss_deterministic(P) :-
    P = program(_, Procs),
    ss_initial(P, C0), ss_run(Procs, C0, Steps, _),
    findall(C, ( C = C0 ; member(step(_, C), Steps) ), Cs),
    forall(member(C, Cs),
           ( findall(R, ss_step(Procs, C, R, _), Rs), length(Rs, N), N =< 1 )).

%  backward_ok(+Info, +Ks): applying the backward rules from the last configuration
%  visits the same configurations in reverse order and ends in the initial
%  configuration (with the empty store), where no backward rule applies. (The walk is
%  bounded by the length of Ks, so a wrong rule cannot make the test loop.)
backward_ok(Info, Ks) :-
    reverse(Ks, [KLast|RKs]),
    bwd_walk(Info, KLast, RKs).

bwd_walk(Info, K, []) :-
    \+ bwd_step(Info, K, _, _),
    is_initial(Info, K),
    norm(K, rc([], _, _, [])).
bwd_walk(Info, K, [KPrev|Ks]) :-
    bwd_step(Info, K, _, B), !,
    norm(B, NB), norm(KPrev, NB),
    bwd_walk(Info, B, Ks).

swap_edges(Es, Ss) :-
    findall(B-A, member(A-B, Es), Ss0), sort(Ss0, Ss).

%  flow_inversion_ok(+P): flow(I[s]) = swap(flow(s)) for the main program and every
%  procedure body (labeled, with start and stop), and for the stored inverse bodies.
flow_inversion_ok(P) :-
    labeled_program(P, LP),
    LP = lprog(Main, Procs),
    forall(( S = Main ; member(lproc(_, S), Procs) ),
           ( linvert(S, IS), flow(IS, FI), flow(S, F), swap_edges(F, SF), FI == SF )),
    % the body of id^-1 is the inversion of the body of id, relabeled
    forall(( member(lproc(Id, B), Procs), atom(Id) ),
           ( memberchk(lproc(inv(Id), IB), Procs),
             flow(B, FB), flow(IB, FIB), length(FB, N), length(FIB, N) )).

%  call_uncall_ok(+P): if the main program s succeeds, then "call m uncall m", with
%  m declared as s, ends with the empty store (big-step and reversible semantics).
call_uncall_ok(P) :-
    P = program(Main, Procs),
    (   run_program(P, _)
    ->  Q = program(seq(call('m__'), uncall('m__')), [proc('m__', Main)|Procs]),
        big(Q, ok([])), rev(Q, ok([])), small(Q, ok([]))
    ;   true
    ).

%  check_program(+P, -Outcome): all the checks of the header; Outcome is ok or fail.
check_program(P, Outcome) :-
    big(P, B), small(P, S), rev(P, R),
    assertion(S == B), assertion(R == B),
    ( B = ok(_) -> Outcome = ok ; Outcome = fail ),
    info_of_program(P, Info),
    labeled_program(P, LP), assertion(unique_labels(LP)),
    fwd_confs(Info, Ks, How),
    assertion(( How == final -> B = ok(_) ; B == fail )),
    assertion(fwd_deterministic(Info, Ks)),
    assertion(loop_lemma_ok(Info, Ks)),
    assertion(backward_ok(Info, Ks)),
    assertion(ss_deterministic(P)),
    assertion(flow_inversion_ok(P)),
    assertion(call_uncall_ok(P)).


% =====================================================================================
:- begin_tests(smallstep).
% =====================================================================================

test(agrees_with_bigstep, [forall(program(Name, P))]) :-
    big(P, B), small(P, S),
    assertion(B = ok(_)),
    assertion(S == B),
    ignore(Name = Name).
test(fails_like_bigstep, [forall(( failing_programs(Ps), member(Src, Ps) ))]) :-
    parse_program(Src, P),
    big(P, B), small(P, S),
    assertion(B == fail), assertion(S == fail).
test(deterministic, [forall(program(_, P))]) :-
    ss_deterministic(P).
test(sum3_rules) :-
    example_program('sum3.jan', P), P = program(_, Procs),
    ss_initial(P, C0), ss_run(Procs, C0, Steps, final(_)),
    pairs_keys_steps(Steps, Rules),
    Rules = [R1, R2|_],
    assertion(R1 == 'Seq1'), assertion(R2 == 'AssVarS'),
    assertion(memberchk('CallS', Rules)),
    assertion(memberchk('LoopMainS', Rules)),
    assertion(memberchk('LoopBaseS', Rules)),
    aggregate_all(count, member('Loop2', Rules), N2),
    assertion(N2 == 2).                         % the loop body runs for i = 1, 2
test(uncall_inverts_body) :-
    parse_program("x += 5 uncall f procedure f x -= 2 y += x", P),
    small(P, S), assertion(S == ok([var(x)-7, var(y)-(-5)])).
test(final_config) :-
    store_empty(E), assertion(ss_final(conf(E, skip, []))),
    assertion(\+ ss_final(conf(E, skip, [seq(skip)]))).

pairs_keys_steps([], []).
pairs_keys_steps([step(R, _)|Ss], [R|Rs]) :- pairs_keys_steps(Ss, Rs).

:- end_tests(smallstep).


% =====================================================================================
:- begin_tests(labeled).
% =====================================================================================

test(sum3_labels) :-
    example_program('sum3.jan', P), labeled_program(P, LP),
    lprog_blocks(LP, Pairs), pairs_keys(Pairs, Ls),
    numlist(1, 26, Expected),
    assertion(Ls == Expected),
    assertion(unique_labels(LP)).
test(sum3_blocks) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    assertion(block(Info, 1, start)), assertion(block(Info, 4, stop)),
    assertion(block(Info, 3, call(sumMul3))),
    assertion(block(Info, 5, start)), assertion(block(Info, 15, stop)),
    assertion(block(Info, 10, skip)),
    assertion(block(Info, 16, start)), assertion(block(Info, 26, stop)),
    block(Info, 7, cond(E7)), assertion(E7 == binop(eq, var(i), const(1))),
    block(Info, 13, cond(E13)), assertion(E13 == binop(ge, var(i), var(n))),
    block(Info, 18, cond(E18)), assertion(E18 == E13),     % inverse loop: from i >= n
    block(Info, 24, cond(E24)), assertion(E24 == E7).      %               until i = 1
test(sum3_cfg_main) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    main_cfg(Info, E), assertion(E == [1-2, 2-3, 3-4]).
test(sum3_cfg_proc) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    proc_cfg(Info, sumMul3, E),
    assertion(E == [5-6, 6-7, 7-8, 8-9, 8-10, 9-11, 10-11, 11-13, 12-7, 13-12,
                    13-14, 14-15]).
test(sum3_cfg_inverse) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    proc_cfg(Info, inv(sumMul3), E),
    assertion(E == [16-17, 17-18, 18-19, 19-20, 19-21, 20-22, 21-22, 22-24, 23-18,
                    24-23, 24-25, 25-26]).
test(entry_exit) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    proc_body(Info, sumMul3, B), entry(B, En), exit(B, Ex),
    assertion(En == 5), assertion(Ex == 15).
test(ctx) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    ctx(Info, 8, S8), assertion(S8 = lif(_, 8, _, _, _, 11)),
    ctx(Info, 11, S11), assertion(S11 == S8),
    ctx(Info, 7, S7), assertion(S7 = lloop(_, 7, _, _, _, 13)),
    ctx(Info, 13, S13), assertion(S13 == S7),
    assertion(\+ ctx(Info, 9, _)).
test(flow_inversion, [forall(program(_, P))]) :-
    flow_inversion_ok(P).
test(linvert_involution, [forall(program(_, P))]) :-
    labeled_program(P, lprog(Main, _)),
    linvert(Main, I), linvert(I, II), assertion(II == Main).
test(start_stop) :-
    parse_program("x += 1", P), labeled_program(P, lprog(M, [])),
    assertion(M == lseq(lstart(1), lseq(lassign_var(x, add, const(1), 2), lstop(3)))).

:- end_tests(labeled).


% =====================================================================================
:- begin_tests(reversible).
% =====================================================================================

% Figure "Forward derivation with the reversible semantics" (Sum3): rule applied,
% last and next label, and stack shape (top items).
sum3_forward([ 'AssVar'-(2-3), 'Call'-(5-6), 'AssVar'-(6-7), 'LoopMain'-(7-8),
               'IfFalse1'-(8-10), 'Skip'-(10-11), 'IfFalse2'-(11-13), 'Loop1'-(13-12),
               'AssVar'-(12-7), 'Loop2'-(7-8), 'IfFalse1'-(8-10), 'Skip'-(10-11),
               'IfFalse2'-(11-13), 'Loop1'-(13-12), 'AssVar'-(12-7), 'Loop2'-(7-8),
               'IfTrue1'-(8-9), 'AssVar'-(9-11), 'IfTrue2'-(11-13), 'LoopBase'-(13-14),
               'AssVar'-(14-15), 'Return1'-(3-4) ]).

step_summary(step(R, rc(_, L1, L2, _)), R-(L1-L2)).

test(agrees_with_bigstep, [forall(program(_, P))]) :-
    big(P, B), rev(P, R),
    assertion(B = ok(_)), assertion(R == B).
test(fails_like_bigstep, [forall(( failing_programs(Ps), member(Src, Ps) ))]) :-
    parse_program(Src, P), rev(P, R), assertion(R == fail).
test(sum3_initial) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    rev_initial(Info, K0), norm(K0, N0), assertion(N0 == rc([], 1, 2, [])).
test(sum3_forward_derivation) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    rev_initial(Info, K0), fwd_run(Info, K0, Steps, final(K)),
    maplist(step_summary, Steps, Summary),
    sum3_forward(Expected),
    assertion(Summary == Expected),
    norm(K, NK),
    assertion(NK == rc([var(i)-3, var(n)-6, var(total)-3], 3, 4, [])).
test(sum3_stacks) :-
    example_program('sum3.jan', P), info_of_program(P, Info),
    rev_initial(Info, K0), fwd_run(Info, K0, Steps, _),
    nth1(2, Steps, step(_, rc(_, _, _, Pi2))), assertion(Pi2 == [call(3)]),
    nth1(4, Steps, step(_, rc(_, _, _, [I4|_]))), assertion(I4 = loop1(7, _, 13, _)),
    nth1(5, Steps, step(_, rc(_, _, _, [I5|_]))), assertion(I5 == if_false(8, 11)),
    nth1(8, Steps, step(_, rc(_, _, _, [I8|_]))), assertion(I8 = loop2(7, _, 13, _)),
    nth1(17, Steps, step(_, rc(_, _, _, [I17|_]))), assertion(I17 == if_true(8, 11)),
    nth1(20, Steps, step(_, rc(_, _, _, Pi20))), assertion(Pi20 == [call(3)]).
test(sum3_backward_derivation) :-
    % Figure "Backward derivation": the backward rules applied in reverse order
    example_program('sum3.jan', P), info_of_program(P, Info),
    rev_initial(Info, K0), fwd_run(Info, K0, _, final(K)),
    call_with_time_limit(10, bwd_run(Info, K, BSteps, initial(K0b))),
    findall(R, member(step(R, _), BSteps), BRules),
    sum3_forward(F), pairs_keys(F, FRules), reverse(FRules, Expected),
    assertion(BRules == Expected),
    norm(K0b, N0b), assertion(N0b == rc([], 1, 2, [])).
test(loop_lemma, [forall(program(_, P))]) :-
    info_of_program(P, Info), fwd_confs(Info, Ks, final),
    assertion(loop_lemma_ok(Info, Ks)).
test(backward_to_initial, [forall(program(_, P))]) :-
    info_of_program(P, Info), fwd_confs(Info, Ks, final),
    assertion(backward_ok(Info, Ks)).
test(stuck_then_backward, [forall(( failing_programs(Ps), member(Src, Ps) ))]) :-
    % a computation that gets stuck can still be undone
    parse_program(Src, P), info_of_program(P, Info), fwd_confs(Info, Ks, How),
    assertion(How == stuck),
    assertion(loop_lemma_ok(Info, Ks)),
    assertion(backward_ok(Info, Ks)).
test(deterministic, [forall(program(_, P))]) :-
    info_of_program(P, Info), fwd_confs(Info, Ks, _),
    assertion(fwd_deterministic(Info, Ks)),
    forall(member(K, Ks),
           ( findall(R, bwd_step(Info, K, R, _), Rs), length(Rs, N), assertion(N =< 1) )).
test(no_backward_from_initial, [forall(program(_, P))]) :-
    info_of_program(P, Info), rev_initial(Info, K0),
    assertion(\+ bwd_step(Info, K0, _, _)), assertion(is_initial(Info, K0)).
test(final_is_stop, [forall(program(_, P))]) :-
    info_of_program(P, Info), fwd_confs(Info, Ks, final), last(Ks, rc(_, _, L2, [])),
    assertion(block(Info, L2, stop)),
    info_lprog(Info, lprog(Main, _)), exit(Main, X), assertion(L2 == X).
test(uncall_runs_inverse) :-
    parse_program("x += 5 uncall f procedure f x -= 2 y += x", P),
    rev(P, R), assertion(R == ok([var(x)-7, var(y)-(-5)])),
    info_of_program(P, Info), fwd_confs(Info, Ks, final),
    % the computation goes through the inverse procedure (labels after f's)
    proc_body(Info, inv(f), IB), lstmt_labels(IB, ILs),
    assertion(( member(rc(_, _, L, _), Ks), memberchk(L, ILs) )),
    assertion(loop_lemma_ok(Info, Ks)).

:- end_tests(reversible).


% =====================================================================================
:- begin_tests(explore).
% =====================================================================================

sum3_info(Info) :- example_program('sum3.jan', P), info_of_program(P, Info).

% explore_session/4 with a time limit (a wrong backward rule could make "rewind" loop)
session(Info, Cmds, Events, Final) :-
    call_with_time_limit(10, explore_session(Info, Cmds, Events, Final)).

test(forward_backward) :-
    sum3_info(Info),
    session(Info, [fwd, fwd, fwd, bwd, bwd], Ev, st(K, N)),
    assertion(Ev == [step(fwd, 'AssVar'), step(fwd, 'Call'), step(fwd, 'AssVar'),
                     step(bwd, 'AssVar'), step(bwd, 'Call')]),
    assertion(N == 1),
    norm(K, NK), assertion(NK == rc([var(n)-3], 2, 3, [])).
test(blocked_at_initial) :-
    sum3_info(Info),
    session(Info, [bwd], Ev, st(K, N)),
    assertion(Ev == [blocked(bwd, initial)]), assertion(N == 0),
    explore_initial(Info, st(K0, 0)), assertion(K == K0).
test(run_and_rewind) :-
    sum3_info(Info),
    session(Info, [run, fwd, rewind, bwd], Ev, st(K, N)),
    assertion(Ev == [ran(fwd, 22, final), blocked(fwd, final), ran(bwd, 22, initial),
                     blocked(bwd, initial)]),
    assertion(N == 0),
    norm(K, NK), assertion(NK == rc([], 1, 2, [])).
test(back_from_the_end) :-
    sum3_info(Info),
    session(Info, [run, bwd, bwd, fwd], Ev, st(K, N)),
    assertion(Ev == [ran(fwd, 22, final), step(bwd, 'Return1'), step(bwd, 'AssVar'),
                     step(fwd, 'AssVar')]),
    assertion(N == 21),
    norm(K, NK), assertion(NK = rc([var(i)-3, var(n)-6, var(total)-3], 14, 15, _)).
test(stuck_program) :-
    parse_program("x += 1 if x = 1 then skip else skip fi x = 0", P),
    info_of_program(P, Info),
    session(Info, [run, fwd, rewind], Ev, st(_, N)),
    assertion(Ev = [ran(fwd, _, stuck), blocked(fwd, stuck), ran(bwd, _, initial)]),
    assertion(N == 0).
test(random_walk) :-
    % any sequence of moves keeps the step counter equal to the distance from the
    % initial configuration, and moving back to 0 gives the initial configuration
    sum3_info(Info),
    numlist(1, 60, Is),
    maplist([I, C]>>( I mod 7 =:= 3 -> C = bwd ; I mod 5 =:= 0 -> C = bwd ; C = fwd ),
            Is, Cmds),
    session(Info, Cmds, _, st(K, N)),
    fwd_confs(Info, Ks, final), maplist(norm, Ks, NKs),
    N1 is N + 1, nth1(N1, NKs, Expected),
    norm(K, NK), assertion(NK == Expected).
test(event_texts) :-
    event_text(step(fwd, 'Call'), T1), assertion(T1 == "forward step, rule Call (->)"),
    event_text(ran(bwd, 1, initial), T2), assertion(T2 == "1 backward step (initial)"),
    event_text(ran(fwd, 22, final), T3), assertion(T3 == "22 forward steps (final)").

:- end_tests(explore).


% =====================================================================================
:- begin_tests(cli).
% =====================================================================================

% The command-line interface (janus.pl), run as a separate process.

janus_cmd(Args, Out, Status) :-
    user:janus_script(Janus),
    process_create(path(swipl), ['-q', '-g', main, '-t', halt, Janus, '--'|Args],
                   [stdout(pipe(S)), stderr(null), stdin(null), process(Pid)]),
    output_of(Pid, S, Out, exit(Status)).

%  output_of(+Pid, +Stream, -Out, -Status): the output and exit status of a process,
%  which is killed after 30 seconds.
output_of(Pid, S, Out, Status) :-
    catch(call_with_time_limit(30, read_string(S, _, Out)), time_limit_exceeded,
          ( process_kill(Pid), Out = "" )),
    close(S),
    process_wait(Pid, Status).

test(small_and_rev_same_store, [forall(( all_examples(Ns), member(N, Ns) ))]) :-
    example_file(N, F),
    janus_cmd([F], O1, 0), janus_cmd(['--small', F], O2, 0), janus_cmd(['--rev', F], O3, 0),
    assertion(O2 == O1), assertion(O3 == O1).
test(rev_backward) :-
    example_file('calls.jan', F),
    janus_cmd(['--rev', '--backward', F], O, 0),
    assertion(sub_string(O, _, _, _, "initial configuration reached: yes")).
test(cfg) :-
    example_file('sum3.jan', F),
    janus_cmd(['--cfg', F], O, 0),
    assertion(sub_string(O, _, _, _, "main: {(1,2), (2,3), (3,4)}")),
    assertion(sub_string(O, _, _, _, "procedure rev-sumMul3")),
    assertion(sub_string(O, _, _, _, "rev-sumMul3: {(16,17)")),
    assertion(\+ sub_string(O, _, _, _, "^-1")).
test(explore_piped) :-
    example_file('sum3.jan', F),
    user:janus_script(Janus),
    process_create(path(swipl), ['-q', '-g', main, '-t', halt, Janus, '--', '--explore', F],
                   [stdin(pipe(In)), stdout(pipe(S)), stderr(null), process(Pid)]),
    format(In, "ff\e[C\e[De\e[Dq", []), close(In),
    output_of(Pid, S, O, exit(0)),
    assertion(sub_string(O, _, _, _, "step 3")),
    assertion(sub_string(O, _, _, _, "20 forward steps (final)")),
    assertion(sub_string(O, _, _, _, "backward step, rule Return1 (<-)")),
    assertion(sub_string(O, _, _, _, "bye")).
test(stuck_exit_code) :-
    tmp_file_stream(text, F, S), format(S, "x += 1 / 0~n", []), close(S),
    janus_cmd(['--small', F], _, 1), janus_cmd(['--rev', F], _, 1),
    delete_file(F).

:- end_tests(cli).


% =====================================================================================
:- begin_tests(random).
% =====================================================================================

% Random programs over the variables x, y, z and the array a. Every loop has the
% shape
%       from c = 0 do s1 loop c += 1 s2 until c = k     c -= k
% with a fresh counter c (never assigned elsewhere), so that it terminates; procedure
% p_i only calls p_j with j < i (no recursion). Conditionals use the entry test as
% exit assertion most of the time, but the branches may change its variables and
% some assertions are random, so many programs have no derivation: all semantics
% must then fail / get stuck. Some expressions divide.

gen_program(program(Main, Procs)) :-
    random_between(0, 2, NP),
    gen_procs(0, NP, [], Procs),
    findall(Id, member(proc(Id, _), Procs), Ids),
    gen_stmt(3, Ids, m, Main, 0, _).

gen_procs(I, N, Acc, Procs) :-
    (   I >= N
    ->  reverse(Acc, Procs)
    ;   findall(Id, member(proc(Id, _), Acc), Ids),
        atom_concat(p, I, Id),
        gen_stmt(2, Ids, Id, Body, 0, _),
        I1 is I + 1,
        gen_procs(I1, N, [proc(Id, Body)|Acc], Procs)
    ).

%  gen_stmt(+Depth, +Callable, +Prefix, -Stmt, +C0, -C): C0/C number the loop counters.
gen_stmt(D, Ids, Pre, S, C0, C) :-
    random_between(1, 3, N),
    gen_seq(N, D, Ids, Pre, S, C0, C).

gen_seq(1, D, Ids, Pre, S, C0, C) :- !, gen_simple(D, Ids, Pre, S, C0, C).
gen_seq(N, D, Ids, Pre, seq(S1, S), C0, C) :-
    gen_simple(D, Ids, Pre, S1, C0, C1),
    N1 is N - 1, gen_seq(N1, D, Ids, Pre, S, C1, C).

gen_simple(D, Ids, Pre, S, C0, C) :-
    random_between(1, 10, R),
    (   D > 0, R =:= 1
    ->  gen_if(D, Ids, Pre, S, C0, C)
    ;   D > 0, R =:= 2
    ->  gen_loop(D, Ids, Pre, S, C0, C)
    ;   Ids \== [], R =:= 3
    ->  random_member(Id, Ids), random_member(K, [call, uncall]), S =.. [K, Id], C = C0
    ;   R =:= 4
    ->  S = skip, C = C0
    ;   R =:= 5
    ->  gen_arr_assign(S), C = C0
    ;   gen_var_assign(S), C = C0
    ).

gen_var_assign(assign_var(X, Op, E)) :-
    random_member(X, [x, y, z]), random_member(Op, [add, sub, xor]),
    gen_expr(2, X, E).
gen_arr_assign(assign_arr(a, const(I), Op, E)) :-
    random_between(0, 2, I), random_member(Op, [add, sub, xor]),
    gen_expr(2, a, E).

gen_if(D, Ids, Pre, if_then_else(E1, S1, S2, E2), C0, C) :-
    gen_cond(E1),
    D1 is D - 1,
    gen_stmt(D1, Ids, Pre, S1, C0, C1),
    gen_stmt(D1, Ids, Pre, S2, C1, C),
    random_between(1, 6, R),
    ( R =:= 1 -> gen_cond(E2) ; E2 = E1 ).

gen_loop(D, Ids, Pre, seq(loop(E1, S1, seq(Inc, S2), E2), Dec), C0, C) :-
    format(atom(Ctr), "~w_c~w", [Pre, C0]),
    C1 is C0 + 1,
    random_between(0, 2, K),
    random_between(1, 5, R),
    (   R =:= 1
    ->  gen_cond(G), E1 = binop(lor, binop(eq, var(Ctr), const(0)), G)
    ;   E1 = binop(eq, var(Ctr), const(0))
    ),
    E2 = binop(eq, var(Ctr), const(K)),
    Inc = assign_var(Ctr, add, const(1)),
    Dec = assign_var(Ctr, sub, const(K)),
    D1 is D - 1,
    gen_stmt(D1, Ids, Pre, S1, C1, C2),
    gen_stmt(D1, Ids, Pre, S2, C2, C).

gen_cond(binop(Op, var(X), const(N))) :-
    random_member(Op, [eq, ne, lt, gt, le, ge]),
    random_member(X, [x, y, z]),
    random_between(-1, 2, N).

%  gen_expr(+Depth, +Forbidden, -E): an expression that does not mention the variable
%  or array Forbidden (the reversibility condition of assignments).
gen_expr(D, F, E) :-
    random_between(1, 6, R),
    (   D > 0, R =< 2
    ->  random_member(Op, [add, sub, mul, xor, div, rem, band, bor, lt, eq]),
        D1 is D - 1, gen_expr(D1, F, E1), gen_expr(D1, F, E2),
        E = binop(Op, E1, E2)
    ;   R =:= 3, F \== a
    ->  random_between(0, 2, I), E = arr(a, const(I))
    ;   R =< 4
    ->  random_between(-2, 3, N), E = const(N)
    ;   subtract([x, y, z], [F], Vs), random_member(X, Vs), E = var(X)
    ).

random_programs(N, Ps) :-
    set_random(seed(20261011)),
    length(Ps, N),
    maplist(gen_program, Ps).

test(random_programs) :-
    random_programs(400, Ps),
    maplist([P, O]>>call_with_time_limit(10, check_program(P, O)), Ps, Os),
    aggregate_all(count, member(ok, Os), NOk),
    aggregate_all(count, member(fail, Os), NFail),
    format(user_error, "~n  random programs: ~w with a derivation, ~w without~n",
           [NOk, NFail]),
    assertion(NOk >= 100), assertion(NFail >= 20).
test(random_programs_reach_constructs) :-
    % the generated programs exercise every forward rule
    random_programs(400, Ps),
    findall(R, ( member(P, Ps), info_of_program(P, Info), rev_initial(Info, K0),
                 fwd_run(Info, K0, Steps, _), member(step(R, _), Steps) ), Rs0),
    sort(Rs0, Rs),
    assertion(Rs == ['AssArr', 'AssVar', 'Call', 'IfFalse1', 'IfFalse2', 'IfTrue1',
                     'IfTrue2', 'Loop1', 'Loop2', 'LoopBase', 'LoopMain', 'Return1',
                     'Return2', 'Skip', 'UnCall']).

:- end_tests(random).
