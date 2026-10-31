/*  janus_explore.pl -- interactive exploration of a computation with the reversible
    semantics: the user moves forward (forward rules) and backward (backward rules)
    one step at a time.

    Going back does NOT replay a history: it applies the backward rules of Section 4.2
    to the current configuration, so the explorer is also a way of observing the loop
    lemma (a forward step followed by a backward step gives back the same
    configuration).

    Keys (see explore_help/0):
      right arrow, f, n, space   one forward step
      left arrow, b, p           one backward step
      down arrow, e              run forward until the end (final stop or stuck)
      up arrow, a                run backward until the initial configuration
      l                          show/hide the labeled program
      h, ?                       help
      q, Ctrl-D                  quit

    The commands themselves are implemented by the pure predicate explore_command/5,
    which the tests use (explore_session/4); only explore/2 reads keys and prints.
*/

:- module(janus_explore,
          [ explore/2,              % +Program, +Options
            explore_command/5,      % +Info, +Cmd, +State, -State1, -Event
            explore_session/4,      % +Info, +Cmds, -Events, -FinalState
            explore_initial/2,      % +Info, -State
            event_text/2            % +Event, -String
          ]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(janus_labeled).
:- use_module(janus_reversible).

% ======================================================================================
% Commands (pure)
% ======================================================================================

% States: st(K, N), where K is the current configuration and N the number of forward
% steps from the initial configuration (backward steps decrease it).

%!  explore_initial(+Info, -State) is semidet.
explore_initial(Info, st(K0, 0)) :- rev_initial(Info, K0).

%!  explore_command(+Info, +Cmd, +State, -State1, -Event) is det.
%   Cmd is fwd, bwd, run (forward until no rule applies) or rewind (backward until no
%   rule applies). Event describes what happened:
%     step(fwd, Rule), step(bwd, Rule)   one step with that rule
%     blocked(fwd, final)                the program has terminated (final stop)
%     blocked(fwd, stuck)                no forward rule applies before the final stop
%     blocked(bwd, initial)              the initial configuration has been reached
%     blocked(bwd, stuck)                no backward rule applies
%     ran(fwd, Count, How), ran(bwd, Count, How)
%                                        Count steps, ending as How (final, stuck,
%                                        initial)
explore_command(Info, Cmd, S, S1, Event) :-
    command(Cmd, Info, S, S1, Event).       % first-argument indexing on Cmd

command(fwd, Info, st(K, N), S1, Event) :-
    (   fwd_step(Info, K, Rule, K1)
    ->  N1 is N + 1, S1 = st(K1, N1), Event = step(fwd, Rule)
    ;   S1 = st(K, N), fwd_blocked(Info, K, How), Event = blocked(fwd, How)
    ).
command(bwd, Info, st(K, N), S1, Event) :-
    (   bwd_step(Info, K, Rule, K1)
    ->  N1 is N - 1, S1 = st(K1, N1), Event = step(bwd, Rule)
    ;   S1 = st(K, N), bwd_blocked(Info, K, How), Event = blocked(bwd, How)
    ).
command(run, Info, st(K, N), st(K1, N1), ran(fwd, C, How)) :-
    fwd_run(Info, K, Steps, Result),
    length(Steps, C), N1 is N + C,
    result_conf(Result, How, K1).
command(rewind, Info, st(K, N), st(K1, N1), ran(bwd, C, How)) :-
    bwd_run(Info, K, Steps, Result),
    length(Steps, C), N1 is N - C,
    result_conf(Result, How, K1).

fwd_blocked(Info, K, How) :- ( rev_final(Info, K) -> How = final ; How = stuck ).
bwd_blocked(Info, K, How) :- ( is_initial(Info, K) -> How = initial ; How = stuck ).

result_conf(final(K), final, K).
result_conf(stuck(K), stuck, K).
result_conf(initial(K), initial, K).

%!  explore_session(+Info, +Cmds, -Events, -FinalState) is semidet.
%   Runs a list of commands from the initial configuration.
explore_session(Info, Cmds, Events, Final) :-
    explore_initial(Info, S0),
    foldl(session_step(Info), Cmds, Events, S0, Final).

session_step(Info, Cmd, Event, S0, S) :- explore_command(Info, Cmd, S0, S, Event).

%!  event_text(+Event, -String) is det.
event_text(step(fwd, R), T) :- format(string(T), "forward step, rule ~w (->)", [R]).
event_text(step(bwd, R), T) :- format(string(T), "backward step, rule ~w (<-)", [R]).
event_text(blocked(fwd, final), "the program has terminated: no forward step").
event_text(blocked(fwd, stuck),
           "no forward rule applies (an assertion fails, a division by zero, ...)").
event_text(blocked(bwd, initial), "initial configuration: no backward step").
event_text(blocked(bwd, stuck), "no backward rule applies").
event_text(ran(fwd, C, How), T) :-
    plural(C, step, S), format(string(T), "~w forward ~w (~w)", [C, S, How]).
event_text(ran(bwd, C, How), T) :-
    plural(C, step, S), format(string(T), "~w backward ~w (~w)", [C, S, How]).

plural(1, W, W) :- !.
plural(_, W, P) :- atom_concat(W, s, P).

% ======================================================================================
% Interactive loop
% ======================================================================================

%!  explore(+Program, +Options) is det.
%   Options: listing(Bool) (show the labeled program, default true).
explore(Program, Options) :-
    info_of_program(Program, Info),
    (   explore_initial(Info, S0)
    ->  ( memberchk(listing(L), Options) -> true ; L = true ),
        ( stream_property(user_output, tty(true)) -> Tty = true ; Tty = false ),
        explore_help,
        loop(Info, S0, "initial configuration", L, Tty)
    ;   format("the main program has no statement~n")
    ).

loop(Info, S, Msg, Listing, Tty) :-
    show(Info, S, Msg, Listing, Tty),
    read_key(Key),
    (   key_command(Key, Cmd)
    ->  (   Cmd == quit
        ->  format("bye~n")
        ;   Cmd == listing
        ->  negate(Listing, Listing1),
            loop(Info, S, "", Listing1, Tty)
        ;   Cmd == help
        ->  explore_help, loop(Info, S, "", Listing, Tty)
        ;   explore_command(Info, Cmd, S, S1, Event),
            event_text(Event, Msg1),
            loop(Info, S1, Msg1, Listing, Tty)
        )
    ;   loop(Info, S, "unknown key (press h for help)", Listing, Tty)
    ).

negate(true, false).
negate(false, true).

key_command(right, fwd).
key_command(left, bwd).
key_command(down, run).
key_command(up, rewind).
key_command(char(C), Cmd) :- char_command(C, Cmd).
key_command(eof, quit).

char_command(f, fwd).  char_command(n, fwd).  char_command(' ', fwd).
char_command(b, bwd).  char_command(p, bwd).
char_command(e, run).
char_command(a, rewind).
char_command(l, listing).
char_command(h, help).  char_command(?, help).
char_command(q, quit).

%  read_key(-Key): right, left, up, down, char(C) or eof. Arrow keys are the escape
%  sequences ESC [ C/D/A/B (or ESC O C/D/A/B).
read_key(Key) :-
    next_code(C),
    key_of_code(C, Key).

%  next_code(-C): the next key code. On a terminal, get_single_char/1 reads one key
%  without waiting for Enter; otherwise (e.g. piped input) codes are read one by one.
next_code(C) :-
    (   stream_property(user_input, tty(true))
    ->  get_single_char(C)
    ;   get_code(user_input, C)
    ).

key_of_code(C, eof) :- ( C =:= -1 ; C =:= 4 ), !.
key_of_code(27, Key) :- !,
    next_code(C2),
    (   ( C2 =:= 0'[ ; C2 =:= 0'O )
    ->  next_code(C3), arrow(C3, Key)
    ;   Key = char(escape)
    ).
key_of_code(C, Key) :- ( C =:= 13 ; C =:= 10 ), !, read_key(Key).  % ignore newlines
key_of_code(C, char(Ch)) :- char_code(Ch, C).

arrow(0'C, right) :- !.
arrow(0'D, left) :- !.
arrow(0'A, up) :- !.
arrow(0'B, down) :- !.
arrow(_, char(escape)).

show(Info, st(K, N), Msg, Listing, Tty) :-
    ( Tty == true -> format("\e[H\e[2J") ; nl ),
    K = rc(_, L1, L2, Pi),
    format("Janus reversible semantics -- step ~w~n", [N]),
    (   Msg \== "" -> format("~w~n", [Msg]) ; true ),
    rc_text(K, KT),
    format("configuration: ~w~n", [KT]),
    label_text(Info, L1, T1), label_text(Info, L2, T2),
    format("  last executed (l1):  ~w~n", [T1]),
    format("  next to execute (l2): ~w~n", [T2]),
    rstack_text(Pi, PT),
    format("  stack: ~w~n", [PT]),
    (   Listing == true
    ->  info_lprog(Info, LP),
        format("~nlabeled program (-> next, <- last):~n"),
        marks(L1, L2, Marks),
        pp_lprog_marked(LP, Marks)
    ;   true
    ),
    format("~n[-> forward  <- backward  down: run to end  up: back to start  l: listing  h: help  q: quit] "),
    flush_output.

marks(L, L, [L-'<>']) :- !.
marks(L1, L2, [L1-'<-', L2-'->']).

label_text(Info, L, T) :-
    (   block(Info, L, B)
    ->  block_text(B, BT), format(string(T), "[~w]^~w", [BT, L])
    ;   format(string(T), "~w", [L])
    ).

explore_help :-
    format("~nExplore a computation with the reversible semantics of Janus:~n"),
    format("  right arrow, f, n, space  one forward step~n"),
    format("  left arrow, b, p          one backward step (backward rules)~n"),
    format("  down arrow, e             run forward to the end~n"),
    format("  up arrow, a               run backward to the initial configuration~n"),
    format("  l                         show/hide the labeled program~n"),
    format("  h, ?                      this help~n"),
    format("  q, Ctrl-D                 quit~n").
