# Janus in Prolog

This is an executable prototype of "A Reversible Semantics for Janus" (JLAMP version). It covers:
- the syntax, the semantics of expressions, the big-step semantics of sequential Janus and the inverter (Section 2);
- the small-step semantics (Section 3);
- labeled programs with `start`/`stop`, inverse procedures, `entry`/`exit`, `ctx` and control-flow graphs (Section 4, preliminaries);
- the reversible semantics: forward rules (Section 4.1) and backward rules (Section 4.2);
- an interactive explorer that moves forward and backward through a computation, one step at a time.

It mirrors the Lean 4 specification in `lean4/RequestProject/Janus/`. It is written in pure Prolog for SWI-Prolog (tested with 9.0.4): no `assert`/`retract`, and every rule of the paper is one Horn clause, with its premises in the paper's order, under a comment `% Rule <Name>`.

## Files

| File | Contents |
|---|---|
| `src/janus.pl` | loads everything; command line (`main/0`), `run_file/2`, `print_store/1` |
| `src/janus_parser.pl` | tokenizer, recursive-descent parser (`parse_program/2`, `parse_file/2`), pretty-printer (`pp_program/1`, `pp_program_string/2`) |
| `src/janus_arith.pl` | interpretation of operators: `apply_binop/4`, `apply_assign_op/4`, `inverse_assign_op/2`, `is_true/1`, `is_false/1` |
| `src/janus_store.pl` | stores: `store_empty/1`, `store_get_var/3`, `store_get_cell/4`, `store_set_var/4`, `store_set_cell/5`, `store_to_list/2`, `store_from_list/2` |
| `src/janus_bigstep.pl` | `eval_expr/3` (Fig. 2), `exec/4` and `exec_loop/7` (Fig. 3), `run_program/2` |
| `src/janus_trace.pl` | trace mode: `trace_program/2` builds the big-step derivation with a meta-interpreter over the clauses of `janus_bigstep.pl`; `print_trace/2` prints it |
| `src/janus_inverter.pl` | `invert_op/2`, `invert_stmt/2`, `invert_proc/2` (Fig. 4); `well_formed_stmt/1`, `well_formed_program/1` |
| `src/janus_smallstep.pl` | small-step semantics (Section 3): `ss_step/4` (one clause per rule), `ss_initial/2`, `ss_final/1`, `ss_run/4`, `run_program_ss/2` |
| `src/janus_labeled.pl` | labeled programs and CFGs (Section 4): `with_start_stop/2`, `invert_xstmt/2`, `label_stmt/4`, `labeled_program/2`, `linvert/2`, `entry/2`, `exit/2`, `flow/2`, `info_of_program/2`, `block/3`, `ctx/3`, `edge/3`, `proc_body/3`, `main_cfg/2`, `proc_cfg/3`, printing |
| `src/janus_reversible.pl` | reversible semantics: `fwd_step/4` (Section 4.1), `bwd_step/4` (Section 4.2), `rev_initial/2`, `rev_final/2`, `is_initial/2`, `fwd_run/4`, `bwd_run/4`, `run_program_rev/2` |
| `src/janus_explore.pl` | interactive explorer: `explore/2`; the commands themselves are the pure predicates `explore_command/5` and `explore_session/4` |
| `tests/test_janus.pl` | plunit tests: parser, arithmetic, stores, big-step semantics, inverter, trace |
| `tests/test_reversible.pl` | plunit tests: small-step semantics, labeled programs and CFGs, reversible semantics, explorer, command line, random programs |
| `examples/*.jan` | `simple.jan`, `loops.jan`, `calls.jan`, `noprocs.jan`, `sum3.jan` |

## How to run

From the repository root:

```
swipl -q -g main -t halt src/janus.pl -- examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --parse-only examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --trace examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --trace=full examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --timeout=5 FILE.jan
swipl -q -g main -t halt src/janus.pl -- --small examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --small --trace examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --cfg examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --rev examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --rev --trace examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --rev --backward examples/sum3.jan
swipl -q -g main -t halt src/janus.pl -- --explore examples/sum3.jan
swipl -g run_tests -t halt tests/test_janus.pl
swipl -g run_tests -t halt tests/test_reversible.pl
```

| Option | Effect |
|---|---|
| (none) | big-step semantics (Section 2) |
| `--small` | small-step semantics (Section 3); with `--trace`, one line `Rule <sigma, s, pi>` per step |
| `--rev` | forward rules of the reversible semantics (Section 4.1); with `--trace`, one line `Rule-> <sigma, l1, l2, pi>` per step |
| `--rev --backward` | runs forward, prints the forward derivation, then applies the backward rules (Section 4.2) from the final configuration and prints that derivation and `initial configuration reached: yes` (or `NO`) |
| `--cfg` | prints the labeled program (with `start`/`stop` and the inverse procedures) and the CFG of the main program and of every (inverse) procedure |
| `--explore` | interactive exploration (see below) |

All semantics print the same final store and use the same exit codes.

The interpreter prints the final store, one `x = v` line per nonzero variable, sorted by name. Array cells are printed as `a[i] = v`, sorted by name and then index. Exit codes:

| Code | Meaning |
|---|---|
| 0 | success |
| 1 | `no derivation (assertion failed, division by zero, undefined procedure)` |
| 2 | timeout, default 10 s via `call_with_time_limit/2`, reported as non-termination |
| 3 | syntax error, with line number |
| 4 | usage error or file not found |

Interactively:
```prolog
?- [src/janus].
?- parse_file('examples/sum3.jan', P), run_program(P, S), print_store(S).
```

## Trace mode

`--trace` prints the big-step derivation of the run, then the final store:

```
$ swipl -q -g main -t halt src/janus.pl -- --trace examples/calls.jan
derivation:
  Seq: <{}, x += 3 ...> => {x=4, y=8}
    AssVar: <{}, x += 3> => {x=3}
    Seq: <{x=3}, call inc ...> => {x=4, y=8}
      Call: <{x=3}, call inc> => {x=4}
        AssVar: <{x=3}, x += 1> => {x=4}
      ...
final store:
x = 4
y = 8
```

- **Reading the output.**
  - Each line is one rule application, `Rule: <sigma, s> => sigma'`, where `sigma` is written `{x=1, a[2]=7}` (bindings equal to 0 omitted). Loop configurations are written `<sigma, (e1, s1, e2, s2)> => sigma'`.
  - The premises of a rule are listed below it, indented, in the order of the rule. This is the derivation tree of Fig. 3, read top-down, i.e. the order in which the steps are evaluated.
  - Compound statements are abbreviated on one line: `if e1 then ... else ... fi e2`, `from e1 do ... loop ... until e2`, `s1 ...` for a sequence.
- **Levels.**
  - `--trace` shows the statement-level rules: AssVar, AssArr, Call, UnCall, Seq, IfTrue, IfFalse, LoopMain, LoopBase, LoopRec, Skip.
  - `--trace=full` also shows the expression rules (Con, Var, Arr, Bop) and, as `where ...` lines, the side conditions of every rule: store reads and updates, `[[op]](v1, v2) = v`, `is_true?(v)`, `Gamma(id) = ...`.
- **No derivation.** The trace shows the partial derivation that got furthest and marks the premise that fails, then exits with code 1. For example:
  ```
  partial derivation (no derivation exists):
    Seq: <{}, x += 2 ...> => (no derivation)
      AssVar: <{}, x += 2> => {x=2}
      AssVar: <{x=2}, y += x / (x - 2)> => (no derivation)
        Bop: <{x=2}, x / (x - 2)> => (no derivation)
          FAILS: 2 / 0 is undefined (division by zero)
  ```
  The other messages are `FAILS: is_true?(0) does not hold` (an assertion or an entry test), `FAILS: is_false?(1) does not hold` and `FAILS: procedure p is not defined`.
- **How it works.**
  - `janus_trace.pl` is a meta-interpreter that runs the clauses of `janus_bigstep.pl` themselves (`clause/2`). The rules are therefore not duplicated, and the trace always follows exactly the same rules as `exec/4`.
  - Rule names come from the clause heads. IfTrue/IfFalse and LoopBase/LoopRec are told apart by their test premise.
  - A test checks that the trace gives the same final store as `run_program/2` on all programs.
- **Size.** The trace of a long run can be very large: every loop iteration adds a few lines.

## Small-step semantics (`janus_smallstep.pl`)

- Configurations are `conf(Sigma, S, Stack)`, i.e. ⟨σ, s, π⟩. The stack items are `seq(S2)`, `if_true(E2)`, `if_false(E2)`, `loop1(E1,S1,E2,S2)`, `loop2(E1,S1,E2,S2)`; the head of the list is the top.
- `ss_step(Gamma, C, Rule, C1)` has one clause per rule of the two small-step figures: AssVarS, AssArrS, CallS, UnCallS, Seq1, Seq2, IfTrue1, IfTrue2, IfFalse1, IfFalse2, LoopMainS, LoopBaseS, Loop1, Loop2.
- A final configuration is ⟨σ, skip, []⟩. `ss_run/4` applies rules until a final configuration is reached (`final(C)`) or no rule applies (`stuck(C)`).

## Labeled programs and CFGs (`janus_labeled.pl`)

- Every body `s` (main program and procedures) becomes `start (s stop)`. The inverse procedure `id⁻¹` has body 𝓘⟦start s stop⟧, where 𝓘⟦start⟧ = stop and 𝓘⟦stop⟧ = start. In the output of `--cfg` and `--explore` it is printed as `procedure rev-id` (not a valid Janus identifier, so it cannot clash with a user procedure, and it cannot be confused with the `[block]^label` notation).
- Labels are assigned consecutively from 1, in textual order: the main program, then the procedures, then the inverse procedures. This reproduces the labels of the Sum3 figure (main 1–4, `sumMul3` 5–15, `sumMul3⁻¹` 16–26).
- Labeled statements: `lassign_var(X,Op,E,L)`, `lassign_arr(X,E1,Op,E2,L)`, `lif(E1,L1,S1,S2,E2,L2)`, `lloop(E1,L1,S1,S2,E2,L2)`, `lcall(Id,L)`, `luncall(Id,L)`, `lskip(L)`, `lstart(L)`, `lstop(L)`, `lseq(S1,S2)`; programs `lprog(Main, [lproc(Name, Body), ...])` with `Name = Id` or `inv(Id)`.
- `entry/2`, `exit/2`, `flow/2` follow the definitions of the paper; `flow(p)` is the union of the CFGs of the main program and of every (inverse) procedure. `ctx(Info, L, S)` gives the conditional or loop where the test or assertion with label `L` occurs.
- The reversible semantics works on a precomputed term `info(LProg, Blocks, Ctx, Succ, Pred)` (`info_of_program/2`), so that blocks, `ctx` and CFG edges are looked up in AVL trees.

## Reversible semantics (`janus_reversible.pl`)

- Configurations are `rc(Sigma, L1, L2, Stack)`, i.e. ⟨σ, ℓ₁, ℓ₂, π⟩: ℓ₁ is the last executed block and ℓ₂ the next one. Stack items: `call(L)`, `uncall(L)`, `if_true(L1,L2)`, `if_false(L1,L2)`, `loop1(L1,S1,L2,S2)`, `loop2(L1,S1,L2,S2)`.
- `fwd_step(Info, K, Rule, K1)` and `bwd_step(Info, K, Rule, K1)` have one clause per rule of the forward and backward figures: AssVar, AssArr, Call, Return1, UnCall, Return2, Skip, IfTrue1, IfTrue2, IfFalse1, IfFalse2, LoopMain, LoopBase, Loop1, Loop2.
- The initial configuration is ⟨ε, entry(s), ℓ, []⟩ with entry(s) → ℓ in the CFG of the main program. A forward computation ends successfully when the next block is the final `stop` of the main program, with an empty stack (Lemma "forward-rev").
- `fwd_run/4` returns `final(K)` or `stuck(K)`; `bwd_run/4` returns `initial(K)` or `stuck(K)`.

## Explorer (`--explore`)

```
swipl -q -g main -t halt src/janus.pl -- --explore examples/sum3.jan
```

The screen shows the step number (forward steps from the initial configuration), what the last command did, the configuration, the last (ℓ₁) and next (ℓ₂) blocks, the stack, and the labeled program with `<-` at ℓ₁ and `->` at ℓ₂ (`<>` if they coincide).

| Key | Command |
|---|---|
| right arrow, `f`, `n`, space | one forward step |
| left arrow, `b`, `p` | one backward step |
| down arrow, `e` | run forward to the end (final `stop`, or no rule applies) |
| up arrow, `a` | run backward to the initial configuration |
| `l` | show/hide the labeled program |
| `h`, `?` | help |
| `q`, Ctrl-D | quit |

Going back does not replay a history: the backward rules are applied to the current configuration, so the explorer also shows the loop lemma at work. A backward step is possible after the program has terminated, and also after a computation got stuck. On a terminal, keys are read with `get_single_char/1` (no Enter needed) and the screen is redrawn; with piped input (e.g. `printf 'ff\e[C\e[Dq' | swipl ...`) codes are read one by one and every screen is printed in sequence.

## Building the Lean 4 specification (`lean4/`)

The Lean development is a Lake project that depends on Mathlib. All versions are pinned: `lean-toolchain` fixes Lean 4.28.0, and `lake-manifest.json` fixes the exact commit of Mathlib and of each of its dependencies.

1. Install [elan](https://github.com/leanprover/elan), the Lean version manager. It installs the Lean version given in `lean-toolchain` automatically.
2. Download the prebuilt Mathlib and build the project:

```
cd lean4
lake exe cache get
lake build
```

`lake exe cache get` downloads the precompiled Mathlib files (about 7 GB on disk, in `lean4/.lake/`); without it, `lake build` compiles Mathlib from source, which takes hours. The development contains no `sorry` and no `axiom`.

## Abstract syntax: mapping to Lean (`Syntax.lean`, `Semantics.lean`, `Inverter.lean`)

| Paper | Lean | Prolog |
|---|---|---|
| `p ::= s (procedure id s)*` | `Program {main, procs}`, `ProcDecl {name, body}` | `program(Main, Procs)`, `Procs = [proc(Id, Body), ...]` (possibly `[]`) |
| `x ⊕= e` | `Stmt.assVar x op e` | `assign_var(X, Op, E)` |
| `x[e₁] ⊕= e₂` | `Stmt.assArr x e₁ op e₂` | `assign_arr(X, E1, Op, E2)` |
| `if e₁ then s₁ else s₂ fi e₂` | `Stmt.ite e₁ s₁ s₂ e₂` | `if_then_else(E1, S1, S2, E2)` |
| `from e₁ do s₁ loop s₂ until e₂` | `Stmt.loop e₁ s₁ s₂ e₂` | `loop(E1, S1, S2, E2)` |
| `call id`, `uncall id`, `skip` | `Stmt.call`, `Stmt.uncall`, `Stmt.skip` | `call(Id)`, `uncall(Id)`, `skip` |
| `s₁ s₂` | `Stmt.seq s₁ s₂` | `seq(S1, S2)` (the parser nests to the right) |
| `c` | `Expr.const (c : Int32)` | `const(N)` (the parser enforces the 32-bit range) |
| `x`, `x[e]`, `e₁ ⊙ e₂` | `Expr.var`, `Expr.arr`, `Expr.bin op e₁ e₂` | `var(X)`, `arr(X, E)`, `binop(Op, E1, E2)` |
| `⊕ ::= + \| - \| ^` | `ModOp.add/sub/xor` | `add`, `sub`, `xor` |
| `⊙` (16 operators) | `BinOp.mod op`, `mul`, `div`, `rem`, `band`, `land`, `lor`, `bor`, `lt`, `gt`, `eq`, `ne`, `le`, `ge` | `add sub xor mul div rem band land lor bor lt gt eq ne le ge` |
| locations `x`, `x[v]` | `Loc.var x`, `Loc.elem x v` | `var(X)`, `cell(X, I)` |
| ⟦⊕⟧, ⟦⊙⟧ | `ModOp.interp`, `BinOp.interp` | `apply_assign_op/4`, `apply_binop/4` |
| `is_true?`, `is_false?` | `IsTrue`, `IsFalse` | `is_true/1`, `is_false/1` |
| ⟨σ, e⟩ ⇓ v | `EvalExpr σ e v` | `eval_expr(Sigma, E, V)` |
| ⟨σ, s⟩ ⇓ σ′ | `BigStep Γ σ (.stmt s) σ′` (`Exec`) | `exec(Gamma, Sigma, S, Sigma1)` |
| ⟨σ, (e₁,s₁,e₂,s₂)⟩ ⇓ σ′ | `BigStep Γ σ (.loopCont e₁ s₁ e₂ s₂) σ′` | `exec_loop(Gamma, Sigma, E1, S1, E2, S2, Sigma1)` |
| Γ(id) | `Program.procEnv` (first declaration) | `gamma(Gamma, Id, Body)` (first declaration) |
| run from ε | `Program.Exec` | `run_program(Program, Store)` |
| 𝓘ₒₚ, 𝓘 | `ModOp.invert`, `Stmt.invert` | `invert_op/2` (= `inverse_assign_op/2`), `invert_stmt/2` |
| `procedure id⁻¹ 𝓘⟦s⟧` | `ProcDecl.invert invName` | `invert_proc(proc(Id,S), proc(inverse(Id), IS))` |
| side condition "x not in e" | `Stmt.WellFormed`, `Program.WellFormed` | `well_formed_stmt/1`, `well_formed_program/1` |

In Lean the three update operators appear inside `BinOp` as `BinOp.mod op`. In Prolog they are flattened into the 16 operator atoms of `binop/1`. Note also that the inverse of a sequence is `seq(IS2, IS1)`, so inverting a right-nested sequence gives a left-nested one. Both are valid terms: `seq` is binary, as in Lean.

## Concrete syntax conventions

- **Programs.** A program is a statement sequence (the main body) followed by zero or more sections `procedure id S`. Each body extends to the next `procedure` or to the end of file.
- **Sequences.**
  - Statements are separated by juxtaposition only, with no semicolons.
  - A sequence ends at `else`, `fi`, `loop`, `until`, `procedure` or end of file.
  - Empty sequences are a syntax error (write `skip`).
- **Statements:** `x += e`, `x -= e`, `x ^= e`, `x[e] += e`, `x[e] -= e`, `x[e] ^= e`, `if e then S else S fi e`, `from e do S loop S until e`, `call id`, `uncall id`, `skip`.
- **Operator precedence**, lowest to highest, all left-associative:
  `||` < `&&` < `|` < `^` < `&` < `= !=` < `< > <= >=` < `+ -` < `* / %`.
- **Equality** is written `=`, as in Fig. 1 and in the paper's Sum3 figure. `==` is rejected with the syntax error "'==' is not Janus syntax: equality is written '='". Assignments only have the forms `+=`, `-=`, `^=`, so `=` is never ambiguous.
- **Negative literals.** A `-` written immediately before digits, in operand position, is a negative literal. There is no unary minus. So `x - -1` is x − (−1), `x -1` is x − 1, and `- 1` in operand position is a syntax error.
- **Literal range.** Integer literals must lie in [−2147483648, 2147483647], as in Fig. 1. Values are unbounded (see below).
- **Identifiers** match `[A-Za-z_][A-Za-z0-9_]*`, excluding the keywords `if then else fi from do loop until call uncall skip procedure`. `//` starts a comment that runs to the end of the line.
- **Syntax errors** are thrown as `janus_syntax_error(Line, Message)`. The command line prints `FILE: syntax error at line L: ...`.
- **Pretty-printer.** `pp_program/1` prints one statement per line with minimal parentheses. Its output parses back to the same term; this is tested on all examples.

## Arithmetic (default behaviour of the Jana interpreter)

| Aspect | Prolog behaviour |
|---|---|
| Values | unbounded integers: `2147483647 + 1 = 2147483648` |
| `/`, `%` | floor division and modulus, i.e. SWI-Prolog `div` and `mod`: a = (a/b)·b + a%b, and a%b has the sign of b |
| Division by 0 | **no derivation**: `apply_binop/4` checks the divisor before calling `div`/`mod`, so it fails and never throws |
| `&`, `\|`, `^` | `/\`, `\/`, `xor`, on the two's complement representation with infinite sign extension |
| Comparisons, `&&`, `\|\|` | return 1 or 0; `&&` and `\|\|` test nonzero operands |
| Evaluation order | both operands of every binary operator are always evaluated (no short-circuit), as in rule `Bop` |
| Truth values | `is_true(V)` iff V ≠ 0, `is_false(V)` iff V = 0 |

Reference values (all tested): (−7)/2 = −4, (−7)%2 = 1; 7/(−2) = −4, 7%(−2) = −1; (−7)/(−2) = 3, (−7)%(−2) = −1; 7/2 = 3, 7%2 = 1; (−1)&5 = 5, (−8)|3 = −5, (−1)^5 = −6.

## Stores

- **Totality.** A store is a total function with default 0. Only nonzero bindings are kept, in a `library(assoc)` AVL tree with keys `var(X)` and `cell(X, I)`. A scalar `x` and the cells `x[i]` therefore never alias.
- **Canonical form.** Every update rebuilds the tree with `list_to_assoc/2` from the sorted binding list, and setting a location to 0 deletes its key. Hence equal stores are equal terms, which the tests compare with `==`.

## Semantics

`janus_bigstep.pl` transcribes the rules literally, one clause per rule.
- `IfTrue`/`IfFalse` evaluate the assertion e₂ in the store **after** s₁ (resp. s₂).
- `LoopRec` evaluates e₁ in the store after s₂.
- `Call`/`UnCall` fail if the procedure is undefined; `UnCall` runs `invert_stmt` of the body.
- No derivation means failure.
- `run_program/2` calls `once/1`. The semantics is deterministic (Lean `BigStep.det`), so this only removes the choicepoints left by the rule pairs IfTrue/IfFalse and LoopBase/LoopRec.

Cuts are used only in the tokenizer and parser, for deterministic dispatch on the next token, and in printing and key-reading helpers (pretty-printers, `janus_explore.pl`), which have no declarative reading. The big-step, small-step and reversible rules, the inverter, the labeling, `entry`/`exit`/`flow`, arithmetic and store use no cuts. If-then-else appears in `bool_value/2` (0/1 results), in the store helpers and in the drivers that apply rules until none applies (`ss_run/4`, `fwd_run/4`, `bwd_run/4`, `explore_command/5`); these commit to the first applicable rule, which is the only one since the relations are deterministic (checked by the tests).

## Tests: comparison with the Lean suite

Run with `swipl -g run_tests -t halt tests/test_janus.pl`. There are 132 tests in six units: parser, arith, store, interpreter, inverter, trace.

| Test | Lean (`SyntaxChecks.lean` / `Examples.lean`) | Prolog (`tests/test_janus.pl`) | Expected result |
|---|---|---|---|
| ⟦+⟧(2,3) | `interp_add` | `arith:add` | 5 |
| no overflow | `interp_no_overflow` | `arith:no_overflow` | 2147483647 + 1 = 2147483648 |
| (−7)/2, (−7)%2 | `interp_divmod_neg_pos` | `arith:div_mod_neg_pos` | −4, 1 |
| 7/(−2), 7%(−2) | `interp_divmod_pos_neg` | `arith:div_mod_pos_neg` | −4, −1 |
| (−7)/(−2), (−7)%(−2) | `interp_divmod_neg_neg` | `arith:div_mod_neg_neg` | 3, −1 |
| 7/2, 7%2 | `interp_divmod_pos_pos` | `arith:div_mod_pos_pos` | 3, 1 |
| bitwise on negatives | `interp_bitwise_neg` | `arith:bitwise_negative` | 5, −5, −6 |
| a = (a/b)·b + a%b | `div_mod_identity` | `arith:div_mod_identity` | holds (b ≠ 0) |
| `x / 0`, `x % 0` | `no_eval_div_zero`, `no_eval_rem_zero` | `arith:div_by_zero_fails`, `arith:mod_by_zero_fails`, `interpreter:neg_division_by_zero`, `interpreter:neg_modulus_by_zero` | no derivation |
| `0 && (1/0)` | `interp_land_strict` | `arith:both_operands_evaluated` | no value |
| comparisons, logical ops | `interp_lt`, `interp_land`, `interp_lor`, `interp_band`, `interp_bor`, `interp_xor` | `arith:comparisons_0_1`, `arith:logical_0_1` | 0/1, 0, 6, 5 |
| store get/set, no aliasing | `store_get_set`, `store_scalar_does_not_touch_cell`, … | `store:*` | as stated |
| `x += 3 x -= 1` | `pos_assign` | `interpreter:assign` | x = 2 |
| if, true branch | `pos_ifTrue` | `interpreter:if_true_branch` | x = 1 |
| if, false branch | `pos_ifFalse` | `interpreter:if_false_branch` | x = −1 |
| `from i = 0 do skip loop i += 1 until i = 3` | `pos_loop` | `interpreter:loop` | i = 3 |
| `call inc` (`inc: x += 1`) | `pos_call` | `interpreter:call_inc` | x = 1 |
| `uncall inc` | `pos_uncall` | `interpreter:uncall_inc` | x = −1 |
| no procedures (`x += 1`) | `pos_onlyMain`, `Examples.onlyMain` | `interpreter:no_procedures` | x = 1 |
| Sum3 | — | `interpreter:sum3` | n = 6, i = 3, total = 3 |
| if with disagreeing assertion | `neg_if` | `interpreter:neg_if_assertion` | no derivation |
| loop with e₁ false at entry | `neg_loop_entry` | `interpreter:neg_loop_entry` | no derivation |
| undefined `call` / `uncall` | `neg_call_undefined`, `neg_uncall_undefined`, `neg_onlyMain_call` | `interpreter:neg_call_undefined`, `neg_uncall_undefined`, `neg_call_no_procedures` | no derivation |
| 𝓘ₒₚ involution, 𝓘 involution | `inv_op_involution`, `inv_involution` | `inverter:invert_op_involution`, `inverter:invert_twice_identity` | identity |
| Fig. 4 clauses | `example`s in (e) | `inverter:figure4_clauses` | as in Fig. 4 |
| trace mode | — | `trace:*` | same final store as `run_program/2`; the loop derivation is LoopMain, 3 × LoopRec, LoopBase; failing premise identified |
| inversion of well-formed programs | `BigStep.assVar_invert`, `BigStep.assArr_invert`, `inverse_loop_concrete` | `inverter:semantic_inversion`, `semantic_inversion_nonempty_start` | back to the initial store |

## Tests of the small-step and reversible semantics

Run with `swipl -g run_tests -t halt tests/test_reversible.pl` (about 5 s). There are 181 tests in six units.

| Unit | What is checked |
|---|---|
| `smallstep` | the small-step semantics gives the same final store as the big-step semantics on the Lean test programs and all examples, and gets stuck exactly on the programs without a big-step derivation; it is deterministic; rule sequence of Sum3; `uncall` runs the inverted body |
| `labeled` | Sum3: labels 1–26, blocks, `ctx`, `entry`/`exit`, and the CFGs of `main`, `sumMul3` and `sumMul3⁻¹` exactly as in the paper; flow(𝓘⟦s⟧) = swap(flow(s)); 𝓘 is an involution on labeled statements; `start`/`stop` insertion |
| `reversible` | same final store as the big-step semantics (Lemma "forward-rev"), stuck on the failing programs; the Sum3 forward derivation (rule, ℓ₁, ℓ₂ of each of the 22 steps, stacks, final configuration ⟨{i=3, n=6, total=3}, 3, 4, []⟩) and the backward derivation (the same rules in reverse order, back to ⟨ε, 1, 2, []⟩) as in the two figures of the paper; loop lemma: every forward step k → k′ is undone by exactly one backward step k′ → k, also for computations that get stuck; forward and backward rules are deterministic; no backward step from the initial configuration |
| `explore` | command sequences (`explore_session/4`): forward/backward steps, blocked moves at both ends, run/rewind, backward from the final configuration, stuck programs, a 60-move walk |
| `cli` | `--small` and `--rev` print the same output as the big-step interpreter on all examples; `--rev --backward`; `--cfg`; `--explore` with piped arrow keys; exit code 1 when stuck |
| `random` | 400 random programs (fixed seed; variables, an array, nested conditionals and terminating loops, calls and uncalls of non-recursive procedures, divisions): for each, the three semantics agree (about 3/4 of the programs have a derivation, the rest get stuck in all three), the rules are deterministic, the loop lemma holds at every step, the backward rules go back to the initial configuration through the same configurations, labels are unique, flow(𝓘⟦s⟧) = swap(flow(s)), and `call m uncall m` gives back the empty store; all 15 forward rules are exercised |

All runs in the tests have a time limit, so a wrong rule makes a test fail instead of looping.
