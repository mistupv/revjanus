/*  tests/test_janus.pl -- plunit tests for the Janus prototype.

    Run with:   swipl -g run_tests -t halt tests/test_janus.pl
*/

:- use_module('../src/janus').
:- use_module(library(plunit)).
:- use_module(library(lists)).
:- use_module(library(apply)).

% --- helpers ------------------------------------------------------------------------

%  examples_dir(-Dir): the directory examples, relative to this file.
examples_dir(Dir) :-
    source_file(examples_dir(_), File),
    file_directory_name(File, TestDir),
    directory_file_path(TestDir, '../examples', Dir).

example_file(Name, Path) :-
    examples_dir(Dir),
    directory_file_path(Dir, Name, Path).

all_examples(Names) :-
    Names = ['simple.jan', 'loops.jan', 'calls.jan', 'noprocs.jan', 'sum3.jan'].

parse(Src, P) :- parse_program(Src, P).

main_of(Src, Main) :- parse_program(Src, program(Main, [])).

expr_of(Src, E) :-
    string_concat("x += ", Src, Prog),
    parse_program(Prog, program(assign_var(x, add, E), [])).

%  run(Src, Pairs): run a program and return the final store as a sorted list.
run(Src, Pairs) :-
    parse_program(Src, P),
    run_program(P, S),
    store_to_list(S, Pairs).

%  syntax_error_line(Src, Line): parsing Src throws a syntax error at Line.
syntax_error_line(Src, Line) :-
    catch(( parse_program(Src, _), fail ),
          janus_syntax_error(Line, _),
          true).

empty_pairs(S) :- store_to_list(S, []).

% Programs used by the inverter and trace tests: the Lean test programs and all
% example files.
lean_programs([ "x += 3 x -= 1",
                "if x = 0 then x += 1 else x -= 1 fi x = 1",
                "if x != 0 then x += 1 else x -= 1 fi x = 1",
                "from i = 0 do skip loop i += 1 until i = 3",
                "call inc procedure inc x += 1",
                "uncall inc procedure inc x += 1",
                "a[i] ^= y y += 2 a[i + 1] -= y"
              ]).

program_source(Src) :-
    lean_programs(Ps), member(Src, Ps).
program_source(Src) :-
    all_examples(Ns), member(N, Ns),
    example_file(N, F), read_file_to_string(F, Src, []).


% =====================================================================================
:- begin_tests(parser).
% =====================================================================================

test(assign_ops) :-
    main_of("x += 1 y -= 2 z ^= 3", M),
    assertion(M == seq(assign_var(x,add,const(1)),
                       seq(assign_var(y,sub,const(2)), assign_var(z,xor,const(3))))).
test(assign_arr) :-
    main_of("a[i + 1] ^= b[0]", M),
    assertion(M == assign_arr(a, binop(add,var(i),const(1)), xor, arr(b,const(0)))).
test(if_then_else) :-
    main_of("if x = 0 then x += 1 else skip fi x = 1", M),
    assertion(M == if_then_else(binop(eq,var(x),const(0)), assign_var(x,add,const(1)),
                                skip, binop(eq,var(x),const(1)))).
test(loop) :-
    main_of("from i = 0 do skip loop i += 1 until i = 3", M),
    assertion(M == loop(binop(eq,var(i),const(0)), skip, assign_var(i,add,const(1)),
                        binop(eq,var(i),const(3)))).
test(call_uncall_skip) :-
    parse("call p uncall p skip procedure p skip", P),
    assertion(P == program(seq(call(p), seq(uncall(p), skip)), [proc(p, skip)])).
test(seq_right_nested) :-
    main_of("skip skip skip", M),
    assertion(M == seq(skip, seq(skip, skip))).
test(nested_sequences) :-
    main_of("if x = 0 then x += 1 x += 2 else skip skip fi x = 3", M),
    assertion(M == if_then_else(binop(eq,var(x),const(0)),
                                seq(assign_var(x,add,const(1)), assign_var(x,add,const(2))),
                                seq(skip, skip), binop(eq,var(x),const(3)))).
test(all_16_operators) :-
    forall(member(T-Op, ['+'-add, '-'-sub, '^'-xor, '*'-mul, '/'-div, '%'-rem,
                         '&'-band, '&&'-land, '||'-lor, '|'-bor, '<'-lt, '>'-gt,
                         '='-eq, '!='-ne, '<='-le, '>='-ge]),
           ( format(string(S), "a ~w b", [T]),
             expr_of(S, E),
             assertion(E == binop(Op, var(a), var(b))) )),
    findall(O, binop(O), Os), length(Os, 16).
test(precedence_chain) :-
    expr_of("a || b && c | d ^ e & f = g < h + i * j", E),
    assertion(E == binop(lor, var(a),
                     binop(land, var(b),
                      binop(bor, var(c),
                       binop(xor, var(d),
                        binop(band, var(e),
                         binop(eq, var(f),
                          binop(lt, var(g),
                           binop(add, var(h), binop(mul, var(i), var(j))))))))))).
test(precedence_reverse) :-
    expr_of("a * b + c < d = e & f ^ g | h && i || j", E),
    assertion(E == binop(lor,
                    binop(land,
                     binop(bor,
                      binop(xor,
                       binop(band,
                        binop(eq,
                         binop(lt, binop(add, binop(mul, var(a), var(b)), var(c)), var(d)),
                         var(e)),
                        var(f)),
                       var(g)),
                      var(h)),
                     var(i)),
                    var(j))).
test(left_assoc) :-
    expr_of("a - b - c", E1), assertion(E1 == binop(sub, binop(sub,var(a),var(b)), var(c))),
    expr_of("a / b % c", E2), assertion(E2 == binop(rem, binop(div,var(a),var(b)), var(c))),
    expr_of("a = b != c", E3), assertion(E3 == binop(ne, binop(eq,var(a),var(b)), var(c))),
    expr_of("a <= b >= c", E4), assertion(E4 == binop(ge, binop(le,var(a),var(b)), var(c))).
test(parentheses) :-
    expr_of("(a - b) * c", E),
    assertion(E == binop(mul, binop(sub,var(a),var(b)), var(c))).
test(negative_literals) :-
    expr_of("-1", E1), assertion(E1 == const(-1)),
    expr_of("1 - -2", E2), assertion(E2 == binop(sub, const(1), const(-2))),
    expr_of("y -1", E3), assertion(E3 == binop(sub, var(y), const(1))),
    expr_of("a[-1]", E4), assertion(E4 == arr(a, const(-1))),
    expr_of("-2147483648", E5), assertion(E5 == const(-2147483648)).
test(minus_with_space_is_not_a_literal) :-
    syntax_error_line("x += - 1", 1).
test(literal_out_of_range) :-
    syntax_error_line("x += 2147483648", 1).
test(equality_is_single_equals) :-
    main_of("if x = 1 then skip else skip fi x = 1", M),
    assertion(M == if_then_else(binop(eq,var(x),const(1)), skip, skip,
                                binop(eq,var(x),const(1)))).
test(error_double_equals_rejected) :-
    syntax_error_line("x += 1\nif x == 1 then skip else skip fi x = 1", 2).
test(comments) :-
    parse("// header\nx += 1 // trailing comment\n// x += 2\n", P),
    assertion(P == program(assign_var(x,add,const(1)), [])).
test(no_procedures) :-
    parse("x += 1", P),
    assertion(P == program(assign_var(x,add,const(1)), [])).
test(several_procedures) :-
    parse("call f procedure f x += 1 procedure g skip", P),
    assertion(P == program(call(f), [proc(f, assign_var(x,add,const(1))), proc(g, skip)])).
test(error_empty_procedure_body) :-
    syntax_error_line("x += 1\nprocedure p\n", 3).
test(error_empty_then_branch) :-
    syntax_error_line("if x = 0 then else skip fi x = 0", 1).
test(error_empty_program) :-
    syntax_error_line("// nothing\n", 2).
test(error_missing_fi) :-
    syntax_error_line("x += 1\nif x = 1 then\n  skip\nelse\n  skip\ny += 2\n", 7).
test(error_keyword_as_identifier) :-
    syntax_error_line("loop += 1", 1).
test(error_unexpected_character) :-
    syntax_error_line("x += 1\nx += $\n", 2).
test(round_trip, [forall((all_examples(Ns), member(N, Ns)))]) :-
    example_file(N, F),
    parse_file(F, P),
    pp_program_string(P, S),
    parse_program(S, P2),
    assertion(P2 == P).
test(round_trip_tricky) :-
    Src = "x += a - (b - c) - -1 * (d || e) / f[g + 1]\nif 0 - -1 then skip else skip fi -1 > -2",
    parse_program(Src, P),
    pp_program_string(P, S),
    parse_program(S, P2),
    assertion(P2 == P).

:- end_tests(parser).

% =====================================================================================
:- begin_tests(arith).
% =====================================================================================

test(add) :- apply_binop(add, 2, 3, V), assertion(V == 5).
test(div_mod_neg_pos) :-
    apply_binop(div, -7, 2, Q), assertion(Q == -4),
    apply_binop(rem, -7, 2, R), assertion(R == 1).
test(div_mod_pos_neg) :-
    apply_binop(div, 7, -2, Q), assertion(Q == -4),
    apply_binop(rem, 7, -2, R), assertion(R == -1).
test(div_mod_neg_neg) :-
    apply_binop(div, -7, -2, Q), assertion(Q == 3),
    apply_binop(rem, -7, -2, R), assertion(R == -1).
test(div_mod_pos_pos) :-
    apply_binop(div, 7, 2, Q), assertion(Q == 3),
    apply_binop(rem, 7, 2, R), assertion(R == 1).
test(div_mod_identity) :-
    forall(( member(A, [-7, 7, 0, 13, -13]), member(B, [2, -2, 3, -5]) ),
           ( apply_binop(div, A, B, Q), apply_binop(rem, A, B, R),
             assertion(A =:= Q*B + R),
             assertion((R =:= 0 ; sign(R) =:= sign(B))) )).
test(bitwise_negative) :-
    apply_binop(band, -1, 5, V1), assertion(V1 == 5),
    apply_binop(bor, -8, 3, V2), assertion(V2 == -5),
    apply_binop(xor, -1, 5, V3), assertion(V3 == -6).
test(div_by_zero_fails, [fail]) :- apply_binop(div, 7, 0, _).
test(mod_by_zero_fails, [fail]) :- apply_binop(rem, 7, 0, _).
test(div_by_zero_does_not_throw) :-
    catch(( apply_binop(div, 7, 0, _) -> R = value ; R = no_value ), _, R = exception),
    assertion(R == no_value).
test(no_overflow) :- apply_binop(add, 2147483647, 1, V), assertion(V == 2147483648).
test(comparisons_0_1) :-
    forall(member(Op-A-B-Exp, [lt-1-2-1, lt-2-1-0, gt-2-1-1, gt-1-2-0, eq-3-3-1, eq-3-4-0,
                              ne-3-4-1, ne-3-3-0, le-3-3-1, le-4-3-0, ge-3-3-1, ge-3-4-0]),
           ( apply_binop(Op, A, B, V), assertion(V == Exp) )).
test(logical_0_1) :-
    apply_binop(land, 2, 4, V1), assertion(V1 == 1),
    apply_binop(land, 2, 0, V2), assertion(V2 == 0),
    apply_binop(lor, 0, 4, V3), assertion(V3 == 1),
    apply_binop(lor, 0, 0, V4), assertion(V4 == 0),
    apply_binop(band, 2, 4, V5), assertion(V5 == 0),
    apply_binop(bor, 2, 4, V6), assertion(V6 == 6).
test(both_operands_evaluated, [fail]) :-
    % 0 && (1/0) has no value: && is not short-circuit
    store_empty(S),
    eval_expr(S, binop(land, const(0), binop(div, const(1), const(0))), _).
test(truth_values) :-
    assertion(is_true(1)), assertion(is_true(-3)), assertion(\+ is_true(0)),
    assertion(is_false(0)), assertion(\+ is_false(5)).
test(inverse_assign_op) :-
    forall(assign_op(Op),
           ( inverse_assign_op(Op, I), inverse_assign_op(I, Op2), assertion(Op2 == Op),
             forall(( member(A, [-5, 0, 7]), member(V, [-3, 0, 4]) ),
                    ( apply_assign_op(Op, A, V, R), apply_assign_op(I, R, V, A2),
                      assertion(A2 == A) )) )).

:- end_tests(arith).

% =====================================================================================
:- begin_tests(store).
% =====================================================================================

test(default_zero) :-
    store_empty(S),
    store_get_var(S, x, V1), assertion(V1 == 0),
    store_get_cell(S, a, 5, V2), assertion(V2 == 0).
test(get_after_set) :-
    store_empty(S0), store_set_var(S0, x, 7, S),
    store_get_var(S, x, V), assertion(V == 7).
test(canonical_order_independent) :-
    store_empty(S0),
    store_set_var(S0, x, 1, S1), store_set_var(S1, y, 2, S2), store_set_cell(S2, a, 3, 4, S3),
    store_set_cell(S0, a, 3, 4, T1), store_set_var(T1, y, 2, T2), store_set_var(T2, x, 1, T3),
    assertion(S3 == T3).
test(canonical_zero_deletes) :-
    store_empty(S0), store_set_var(S0, x, 5, S1), store_set_var(S1, x, 0, S2),
    assertion(S2 == S0).
test(no_aliasing_scalar_cell) :-
    store_empty(S0), store_set_var(S0, x, 5, S1),
    store_get_cell(S1, x, 0, C), assertion(C == 0),
    store_set_cell(S1, x, 0, 9, S2),
    store_get_var(S2, x, V), assertion(V == 5),
    store_to_list(S2, L), assertion(L == [var(x)-5, cell(x,0)-9]).
test(cells_independent) :-
    store_empty(S0), store_set_cell(S0, a, 1, 5, S1),
    store_get_cell(S1, a, 2, V), assertion(V == 0).
test(store_to_list_sorted) :-
    store_from_list([var(z)-1, var(a)-2, cell(b,2)-3, cell(b,1)-4], S),
    store_to_list(S, L),
    assertion(L == [var(a)-2, var(z)-1, cell(b,1)-4, cell(b,2)-3]).

:- end_tests(store).

% =====================================================================================
:- begin_tests(interpreter).
% =====================================================================================

% Same programs as the Lean tests (SyntaxChecks.lean / Examples.lean).
test(assign) :-                    % Lean: pos_assign
    run("x += 3 x -= 1", L), assertion(L == [var(x)-2]).
test(if_true_branch) :-            % Lean: pos_ifTrue
    run("if x = 0 then x += 1 else x -= 1 fi x = 1", L), assertion(L == [var(x)-1]).
test(if_false_branch) :-           % Lean: pos_ifFalse
    run("if x != 0 then x += 1 else x -= 1 fi x = 1", L), assertion(L == [var(x)-(-1)]).
test(loop) :-                      % Lean: pos_loop
    run("from i = 0 do skip loop i += 1 until i = 3", L), assertion(L == [var(i)-3]).
test(call_inc) :-                  % Lean: pos_call
    run("call inc procedure inc x += 1", L), assertion(L == [var(x)-1]).
test(uncall_inc) :-                % Lean: pos_uncall
    run("uncall inc procedure inc x += 1", L), assertion(L == [var(x)-(-1)]).
test(no_procedures) :-             % Lean: pos_onlyMain, Examples.onlyMain
    example_file('noprocs.jan', F), run_file(F, S), store_to_list(S, L),
    assertion(L == [var(x)-1]).
test(sum3) :-                      % Sum3 of the paper: n = 6, i = 3, total = 3
    example_file('sum3.jan', F), run_file(F, S), store_to_list(S, L),
    assertion(L == [var(i)-3, var(n)-6, var(total)-3]).
test(simple_example) :-
    example_file('simple.jan', F), run_file(F, S), store_to_list(S, L),
    assertion(L == [var(x)-2, var(y)-5, var(z)-69, cell(a,1)-(-2), cell(a,2)-7]).
test(calls_example) :-
    example_file('calls.jan', F), run_file(F, S), store_to_list(S, L),
    assertion(L == [var(x)-4, var(y)-8]).
test(loops_example) :-
    example_file('loops.jan', F), run_file(F, S), store_to_list(S, L),
    assertion(L == [var(i)-3, var(k)-5, var(s)-15]).
test(no_choicepoints) :-
    parse("if x = 0 then skip else skip fi x = 0", P),
    run_program(P, _).          % plunit warns if a choicepoint is left
test(neg_if_assertion, [fail]) :-        % Lean: neg_if
    run("if x = 0 then x += 1 else skip fi x = 0", _).
test(neg_loop_entry, [fail]) :-          % Lean: neg_loop_entry
    run("from i = 1 do skip loop skip until i = 0", _).
test(neg_call_undefined, [fail]) :-      % Lean: neg_call_undefined
    run("call nope", _).
test(neg_uncall_undefined, [fail]) :-    % Lean: neg_uncall_undefined
    run("uncall nope", _).
test(neg_call_no_procedures, [fail]) :-  % Lean: neg_onlyMain_call
    run("x += 1 call f", _).
test(neg_division_by_zero, [fail]) :-    % Lean: no_eval_div_zero
    run("x += 1 / 0", _).
test(neg_modulus_by_zero, [fail]) :-     % Lean: no_eval_rem_zero
    run("x += 1 % 0", _).

:- end_tests(interpreter).

% =====================================================================================
:- begin_tests(inverter).
% =====================================================================================

test(invert_op_involution) :-
    forall(assign_op(Op), (invert_op(Op, I), invert_op(I, Op2), assertion(Op2 == Op))).
test(figure4_clauses) :-
    invert_stmt(if_then_else(e1, skip, call(p), e2), I1),
    assertion(I1 == if_then_else(e2, skip, uncall(p), e1)),
    invert_stmt(loop(e1, uncall(p), skip, e2), I2),
    assertion(I2 == loop(e2, call(p), skip, e1)),
    invert_stmt(seq(assign_var(x,add,e), assign_arr(a,e1,xor,e2)), I3),
    assertion(I3 == seq(assign_arr(a,e1,xor,e2), assign_var(x,sub,e))).
test(invert_twice_identity, [forall(program_source(Src))]) :-
    parse_program(Src, program(Main, Procs)),
    invert_stmt(Main, IM), invert_stmt(IM, IIM), assertion(IIM == Main),
    forall(member(proc(_, B), Procs),
           ( invert_stmt(B, IB), invert_stmt(IB, IIB), assertion(IIB == B) )).
test(well_formedness) :-
    parse_program("x += x", P1), assertion(\+ well_formed_program(P1)),
    parse_program("a[a[0]] += 1", P2), assertion(\+ well_formed_program(P2)),
    parse_program("a[0] += a[1]", P3), assertion(\+ well_formed_program(P3)),
    parse_program("x += y a[i] += x", P4), assertion(well_formed_program(P4)).
% For the well-formed examples: if exec takes sigma to sigma1, then exec of the inverted
% statement takes sigma1 back to sigma (here sigma is the empty store).
test(semantic_inversion, [forall(program_source(Src))]) :-
    parse_program(Src, P),
    P = program(Main, Procs),
    (   well_formed_program(P)
    ->  store_empty(S0),
        once(exec(Procs, S0, Main, S1)),
        invert_stmt(Main, IMain),
        once(exec(Procs, S1, IMain, S2)),
        assertion(S2 == S0)
    ;   true
    ).
test(semantic_inversion_nonempty_start) :-
    store_from_list([var(x)-10, var(y)-(-4), cell(a,3)-7, var(i)-3], S0),
    parse_program("a[i] ^= y y += 2 a[i + 1] -= y x += a[3] * y", program(M, [])),
    once(exec([], S0, M, S1)),
    invert_stmt(M, IM),
    once(exec([], S1, IM, S2)),
    assertion(S2 == S0).

:- end_tests(inverter).

% =====================================================================================
:- begin_tests(trace).
% =====================================================================================

%  stmt_rules(+Tree, -Rules): the statement-level rule names, in pre-order.
stmt_rules(node(R, J, Cs, _), Rules) :-
    foldl(child_rules, Cs, Rs0, []),
    (   functor(J, eval_expr, 3)
    ->  Rules = Rs0
    ;   Rules = [R|Rs0]
    ).
stmt_rules(cond(_), []).
child_rules(C, Rs, Rs0) :- stmt_rules(C, R1), append(R1, Rs0, Rs).

%  failing_premise(+Tree, -Goal): the premise that fails in a partial derivation.
failing_premise(node(_, _, Cs, failed), G) :-
    last(Cs, Last),
    (   Last = cond(G0)
    ->  G = G0
    ;   failing_premise(Last, G)
    ).

test(same_result_as_run_program, [forall(program_source(Src))]) :-
    parse_program(Src, P),
    run_program(P, S),
    trace_program(P, proof(S1, _)),
    assertion(S1 == S).
test(loop_rule_sequence) :-            % LoopMain, then LoopRec three times, then LoopBase
    parse_program("from i = 0 do skip loop i += 1 until i = 3", P),
    trace_program(P, proof(_, T)),
    stmt_rules(T, Rs),
    assertion(Rs == ['LoopMain', 'Skip',
                     'LoopRec', 'AssVar', 'Skip',
                     'LoopRec', 'AssVar', 'Skip',
                     'LoopRec', 'AssVar', 'Skip',
                     'LoopBase']).
test(call_uncall_rules) :-
    parse_program("call inc uncall inc procedure inc x += 1", P),
    trace_program(P, proof(_, T)),
    stmt_rules(T, Rs),
    assertion(Rs == ['Seq', 'Call', 'AssVar', 'UnCall', 'AssVar']).
test(failure_assertion) :-
    parse_program("if x = 0 then x += 1 else skip fi x = 0", P),
    trace_program(P, failure(T)),
    T = node(Rule, _, _, failed), assertion(Rule == 'IfTrue'),
    failing_premise(T, G), assertion(G == is_true(0)).
test(failure_loop_entry) :-
    parse_program("from i = 1 do skip loop skip until i = 0", P),
    trace_program(P, failure(T)),
    failing_premise(T, G), assertion(G == is_true(0)).
test(failure_undefined_procedure) :-
    parse_program("call nope", P),
    trace_program(P, failure(T)),
    failing_premise(T, G), assertion(G = gamma(_, nope, _)).
test(failure_division_by_zero) :-
    parse_program("x += 2 y += x / (x - 2)", P),
    trace_program(P, failure(T)),
    failing_premise(T, G), assertion(G = apply_binop(div, 2, 0, _)).
test(print_trace_both_levels, [forall(program_source(Src))]) :-
    parse_program(Src, P),
    trace_program(P, R),
    with_output_to(string(S1), print_trace(R, stmt)),
    with_output_to(string(S2), print_trace(R, full)),
    string_length(S1, L1), string_length(S2, L2),
    assertion(L1 > 0), assertion(L2 >= L1).

:- end_tests(trace).
