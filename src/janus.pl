/*  janus.pl -- loads the Janus prototype and provides the command line.

    Usage:
      swipl -q -g main -t halt src/janus.pl -- [OPTIONS] FILE.jan

    Options:
      --parse-only        print the abstract syntax and stop
      --small             use the small-step semantics (Section 3) instead of the
                          big-step semantics
      --rev               use the forward rules of the reversible semantics (Section 4)
      --trace             print the derivation, then the final store:
                            big-step (default): the big-step derivation tree
                            (statement-level rules); if there is no derivation, the
                            partial derivation and the premise that fails;
                            --small: every small-step transition;
                            --rev: every forward transition (as in Example
                            "forward_trace" of the paper)
      --trace=full        big-step only: also the expression rules (Con, Var, Arr,
                          Bop) and the side conditions of every rule
      --backward          with --rev: after the forward derivation, undo it with the
                          backward rules (as in Example "backward_trace") and check
                          that the initial configuration is reached
      --cfg               print the labeled program (with start, stop and the inverse
                          procedures) and its CFGs, and stop
      --explore           explore the computation step by step with the reversible
                          semantics (right/left arrows: forward/backward step)
      --timeout=SECONDS   time limit (default 10)

    Prints the final store, one "x = v" (or "a[i] = v") line per nonzero location,
    sorted by name. Exit codes:
      0  success
      1  no derivation (assertion failed, division by zero, undefined procedure)
      2  timeout (reported as non-termination)
      3  syntax error
      4  usage error / file not found
*/

:- module(janus,
          [ main/0,
            run_file/2,             % +File, -FinalStore
            print_store/1           % +Store
          ]).

:- use_module(janus_arith).
:- use_module(janus_store).
:- use_module(janus_parser).
:- use_module(janus_inverter).
:- use_module(janus_bigstep).
:- use_module(janus_trace).
:- use_module(janus_smallstep).
:- use_module(janus_labeled).
:- use_module(janus_reversible).
:- use_module(janus_explore).

:- reexport(janus_arith).
:- reexport(janus_store).
:- reexport(janus_parser).
:- reexport(janus_inverter).
:- reexport(janus_bigstep).
:- reexport(janus_trace).
:- reexport(janus_smallstep).
:- reexport(janus_labeled).
:- reexport(janus_reversible).
:- reexport(janus_explore).

:- use_module(library(time)).
:- use_module(library(lists)).
:- use_module(library(apply)).

%!  run_file(+File, -FinalStore) is semidet.
run_file(File, FinalStore) :-
    parse_file(File, Program),
    run_program(Program, FinalStore).

%!  print_store(+Store) is det.
%   Prints "x = v" lines sorted by name; arrays as "a[i] = v" sorted by index.
print_store(Store) :-
    store_to_list(Store, Pairs),
    maplist(print_key, Pairs, Keyed),
    keysort(Keyed, Sorted),
    forall(member(_-Line, Sorted), format("~w~n", [Line])).

print_key(var(X)-V, k(X, 0, 0)-Line) :-
    format(string(Line), "~w = ~w", [X, V]).
print_key(cell(X, I)-V, k(X, 1, I)-Line) :-
    format(string(Line), "~w[~w] = ~w", [X, I, V]).

%!  main is det.
%   Command line entry point (see the header).
main :-
    current_prolog_flag(argv, Argv),
    (   parse_args(Argv, Opts, File)
    ->  run_main(File, Opts)
    ;   format(user_error,
               "usage: swipl -q -g main -t halt src/janus.pl -- [--parse-only | --cfg | --explore] [--small | --rev] [--trace | --trace=full] [--backward] [--timeout=SECONDS] FILE.jan~n",
               []),
        halt(4)
    ).

parse_args(Argv, Opts, File) :-
    partition([A]>>sub_atom(A, 0, _, _, '--'), Argv, Flags, Files),
    Files = [File],
    maplist(flag_option, Flags, Opts).

flag_option('--parse-only', parse_only).
flag_option('--trace', trace(stmt)).
flag_option('--trace=full', trace(full)).
flag_option('--small', semantics(small)).
flag_option('--rev', semantics(rev)).
flag_option('--backward', backward).
flag_option('--cfg', cfg).
flag_option('--explore', explore).
flag_option(Flag, timeout(T)) :-
    atom_concat('--timeout=', TA, Flag),
    atom_number(TA, T),
    T > 0.

run_main(File, Opts) :-
    (   exists_file(File)
    ->  true
    ;   format(user_error, "file not found: ~w~n", [File]),
        halt(4)
    ),
    catch(parse_file(File, Program), Error, true),
    (   nonvar(Error)
    ->  (   syntax_error_message(Error, Msg)
        ->  format(user_error, "~w: ~w~n", [File, Msg]),
            halt(3)
        ;   throw(Error)
        )
    ;   memberchk(parse_only, Opts)
    ->  print_term(Program, [right_margin(80)]), nl
    ;   memberchk(cfg, Opts)
    ->  print_cfg(Program)
    ;   memberchk(explore, Opts)
    ->  explore(Program, [])
    ;   ( memberchk(timeout(T), Opts) -> true ; T = 10 ),
        ( memberchk(semantics(Sem), Opts) -> true ; Sem = big ),
        run_semantics(Sem, T, Program, Opts)
    ).

%  run_semantics(+Semantics, +Timeout, +Program, +Options)
run_semantics(big, T, Program, Opts) :-
    (   memberchk(trace(Level), Opts)
    ->  trace_with_timeout(T, Program, Level)
    ;   run_with_timeout(T, Program, Result),
        report(Result, T)
    ).
run_semantics(small, T, Program, Opts) :-
    Program = program(_, Procs),
    ss_initial(Program, C0),
    catch(( call_with_time_limit(T, ss_run(Procs, C0, Steps, R)), Res = done(Steps, R) ),
          time_limit_exceeded, Res = timeout),
    (   Res = done(Steps, R)
    ->  (   memberchk(trace(_), Opts)
        ->  format("small-step derivation:~n"),
            ss_conf_text(C0, T0), format("           ~w~n", [T0]),
            forall(member(step(Rule, C), Steps),
                   ( ss_conf_text(C, CT), format("~w~t~11|~w~n", [Rule, CT]) ))
        ;   true
        ),
        (   R = final(conf(Final, _, _))
        ->  ( memberchk(trace(_), Opts) -> format("final store:~n") ; true ),
            report(ok(Final), T)
        ;   R = stuck(C),
            ss_conf_text(C, CT),
            format(user_error, "no rule applies to ~w~n", [CT]),
            report(no_derivation, T)
        )
    ;   report(timeout, T)
    ).
run_semantics(rev, T, Program, Opts) :-
    info_of_program(Program, Info),
    (   rev_initial(Info, K0)
    ->  true
    ;   format(user_error, "the main program has no statement~n", []), halt(4)
    ),
    catch(( call_with_time_limit(T, fwd_run(Info, K0, Steps, R)), Res = done(Steps, R) ),
          time_limit_exceeded, Res = timeout),
    (   Res = done(Steps, R)
    ->  ( memberchk(backward, Opts) -> Trace = true
        ; memberchk(trace(_), Opts) -> Trace = true
        ; Trace = false ),
        (   Trace == true
        ->  format("forward derivation:~n"),
            print_rev_steps(K0, Steps, '->')
        ;   true
        ),
        (   R = final(KF)
        ->  (   memberchk(backward, Opts)
            ->  bwd_run(Info, KF, BSteps, BR),
                format("backward derivation:~n"),
                print_rev_steps(KF, BSteps, '<-'),
                (   BR = initial(KI), KI == K0
                ->  format("initial configuration reached: yes~n")
                ;   format("initial configuration reached: NO~n")
                )
            ;   true
            ),
            KF = rc(Final, _, _, _),
            ( Trace == true -> format("final store:~n") ; true ),
            report(ok(Final), T)
        ;   R = stuck(K),
            rc_text(K, KT),
            format(user_error, "no forward rule applies to ~w~n", [KT]),
            report(no_derivation, T)
        )
    ;   report(timeout, T)
    ).

print_rev_steps(K0, Steps, Dir) :-
    rc_text(K0, T0), format("              ~w~n", [T0]),
    forall(member(step(Rule, K), Steps),
           ( rc_text(K, KT),
             format(atom(R), "~w~w", [Rule, Dir]),
             format("~w~t~14|~w~n", [R, KT]) )).

%  print_cfg(+Program): the labeled program and the CFGs of its bodies.
print_cfg(Program) :-
    info_of_program(Program, Info),
    info_lprog(Info, LP),
    format("labeled program:~n"),
    pp_lprog(LP),
    format("~nCFGs:~n"),
    main_cfg(Info, M), edges_text(M, MT),
    format("  main: ~w~n", [MT]),
    LP = lprog(_, Procs),
    forall(member(lproc(Name, B), Procs),
           ( flow(B, E), edges_text(E, ET),
             ( Name = inv(Id) -> format(atom(N), "rev-~w", [Id]) ; N = Name ),
             format("  ~w: ~w~n", [N, ET]) )).

%!  trace_with_timeout(+Seconds, +Program, +Level) is det.
%   Trace mode: prints the (partial) derivation, then the final store or the failure.
trace_with_timeout(T, Program, Level) :-
    catch(( call_with_time_limit(T, trace_program(Program, Trace)),
            Result = done(Trace) ),
          time_limit_exceeded,
          Result = timeout),
    (   Result = done(Trace)
    ->  print_trace(Trace, Level),
        (   Trace = proof(Final, _)
        ->  format("final store:~n"),
            report(ok(Final), T)
        ;   report(no_derivation, T)
        )
    ;   report(timeout, T)
    ).

%!  run_with_timeout(+Seconds, +Program, -Result) is det.
%   Result is ok(FinalStore), no_derivation or timeout.
run_with_timeout(T, Program, Result) :-
    catch(( call_with_time_limit(T, run_program(Program, Final))
          ->  Result = ok(Final)
          ;   Result = no_derivation
          ),
          time_limit_exceeded,
          Result = timeout).

report(ok(Final), _) :-
    print_store(Final).
report(no_derivation, _) :-
    format(user_error,
           "no derivation (assertion failed, division by zero, undefined procedure)~n", []),
    halt(1).
report(timeout, T) :-
    format(user_error, "non-termination: no result after ~w s (timeout)~n", [T]),
    halt(2).
