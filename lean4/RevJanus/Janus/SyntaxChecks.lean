import RevJanus.Janus.Semantics

/-!
# Sanity checks for the first fragment (syntax, expressions, big-step semantics, inverter)

Audit file, not imported by any other file. It is built by `lake build` (the library
includes every file under `RevJanus/`); to check it on its own:

    lake env lean RevJanus/Janus/SyntaxChecks.lean

It only uses the project's own definitions. The auxiliary interpreter `run` below is
defined here (not in the project) and proved *sound* with respect to `BigStep`, so that
positive derivations can be checked by computation.
-/

namespace Janus.SyntaxChecks

open Janus

/-! ## (a) Stores -/

theorem store_get_set (σ : Store) (l : Loc) (v : Value) : σ.update l v l = v := by
  simp [Store.update]

-- Proofs of the store lemmas below: `Function.update_of_ne`, with `simp` discharging the
-- disequality of the two locations.
theorem store_set_other_var (σ : Store) (x y : Var) (h : x ≠ y) (v : Value) :
    σ.update (.var x) v (.var y) = σ (.var y) :=
  Function.update_of_ne (by simpa [eq_comm] using h) _ _

theorem store_scalar_does_not_touch_cell (σ : Store) (x : Var) (i v : Value) :
    σ.update (.var x) v (.elem x i) = σ (.elem x i) :=
  Function.update_of_ne (by simp) _ _

theorem store_cell_does_not_touch_scalar (σ : Store) (x : Var) (i v : Value) :
    σ.update (.elem x i) v (.var x) = σ (.var x) :=
  Function.update_of_ne (by simp) _ _

theorem store_cell_does_not_touch_other_cell (σ : Store) (x : Var) (i j v : Value)
    (h : i ≠ j) : σ.update (.elem x i) v (.elem x j) = σ (.elem x j) :=
  Function.update_of_ne (by simpa [eq_comm] using h) _ _

theorem store_empty_zero (l : Loc) : Store.empty l = 0 := rfl

/-! ## (b) Expression evaluation -/

/-- `x` with `x = 5`. -/
def σ5 : Store := Store.empty.update (.var "x") 5

theorem eval_var : EvalExpr σ5 (.var "x") 5 := evalExpr_iff_eval.2 (by decide)

theorem eval_unset_var : EvalExpr σ5 (.var "y") 0 := evalExpr_iff_eval.2 (by decide)

/-- Operand order of `-`: `x - 3 = 2` and `3 - x = -2` when `x = 5`. -/
theorem eval_sub_order₁ :
    EvalExpr σ5 (.bin (.mod .sub) (.var "x") (.const 3)) 2 := evalExpr_iff_eval.2 (by decide)

theorem eval_sub_order₂ :
    EvalExpr σ5 (.bin (.mod .sub) (.const 3) (.var "x")) (-2) := evalExpr_iff_eval.2 (by decide)

/-- Array access `a[x - 4]` reads cell `a[1]`. -/
theorem eval_arr :
    EvalExpr (σ5.update (.elem "a" 1) 7) (.arr "a" (.bin (.mod .sub) (.var "x") (.const 4))) 7 :=
  evalExpr_iff_eval.2 (by decide)

/-! ### Interpretation of operators: reference values (unbounded integers, as in Jana)

All values below are computed by `Expr.eval` on constant expressions and checked by `decide`
(the evaluation is reduced by the elaborator). The bitwise operations use `decide +kernel`:
`Int.land`/`Int.lor` go through `Nat.ldiff`, which only the kernel reduces. This is still a
kernel-checked proof, not `native_decide`. -/

/-- `⟦+⟧(2,3) = 5`. -/
theorem interp_add : (Expr.bin (.mod .add) (.const 2) (.const 3)).eval Store.empty = some 5 := by
  decide

/-- No wrap-around: `2147483647 + 1 = 2147483648`. -/
theorem interp_no_overflow :
    (Expr.bin (.mod .add) (.const 2147483647) (.const 1)).eval Store.empty = some 2147483648 := by
  decide

/-- Floor division and modulus: `(-7)/2 = -4`, `(-7)%2 = 1`. -/
theorem interp_divmod_neg_pos :
    (Expr.bin .div (.const (-7)) (.const 2)).eval Store.empty = some (-4) ∧
    (Expr.bin .rem (.const (-7)) (.const 2)).eval Store.empty = some 1 := by
  decide

/-- `7/(-2) = -4`, `7%(-2) = -1`. -/
theorem interp_divmod_pos_neg :
    (Expr.bin .div (.const 7) (.const (-2))).eval Store.empty = some (-4) ∧
    (Expr.bin .rem (.const 7) (.const (-2))).eval Store.empty = some (-1) := by
  decide

/-- `(-7)/(-2) = 3`, `(-7)%(-2) = -1`. -/
theorem interp_divmod_neg_neg :
    (Expr.bin .div (.const (-7)) (.const (-2))).eval Store.empty = some 3 ∧
    (Expr.bin .rem (.const (-7)) (.const (-2))).eval Store.empty = some (-1) := by
  decide

/-- `7/2 = 3`, `7%2 = 1`. -/
theorem interp_divmod_pos_pos :
    (Expr.bin .div (.const 7) (.const 2)).eval Store.empty = some 3 ∧
    (Expr.bin .rem (.const 7) (.const 2)).eval Store.empty = some 1 := by
  decide

/-- Bitwise operations on negative numbers (two's complement, infinite sign extension):
`(-1) & 5 = 5`, `(-8) | 3 = -5`, `(-1) ^ 5 = -6`. -/
theorem interp_bitwise_neg :
    (Expr.bin .band (.const (-1)) (.const 5)).eval Store.empty = some 5 ∧
    (Expr.bin .bor (.const (-8)) (.const 3)).eval Store.empty = some (-5) ∧
    (Expr.bin (.mod .xor) (.const (-1)) (.const 5)).eval Store.empty = some (-6) := by
  decide +kernel

theorem interp_div_zero : (Expr.bin .div (.const 7) (.const 0)).eval Store.empty = none := by
  decide
theorem interp_rem_zero : (Expr.bin .rem (.const 7) (.const 0)).eval Store.empty = none := by
  decide
theorem interp_lt : (Expr.bin .lt (.const 1) (.const 2)).eval Store.empty = some 1 := by decide
theorem interp_land : (Expr.bin .land (.const 2) (.const 4)).eval Store.empty = some 1 := by decide
theorem interp_band : (Expr.bin .band (.const 2) (.const 4)).eval Store.empty = some 0 := by
  decide +kernel
theorem interp_lor : (Expr.bin .lor (.const 0) (.const 4)).eval Store.empty = some 1 := by decide
theorem interp_bor : (Expr.bin .bor (.const 2) (.const 4)).eval Store.empty = some 6 := by
  decide +kernel
theorem interp_xor : (Expr.bin (.mod .xor) (.const 6) (.const 3)).eval Store.empty = some 5 := by
  decide +kernel
/-- `&&` is strict (not short-circuit): `0 && (1/0)` has no value. -/
theorem interp_land_strict :
    (Expr.bin .land (.const 0) (.bin .div (.const 1) (.const 0))).eval Store.empty = none := by
  decide

/-- `x / 0` has no derivation, in any store.
Proof: invert the `EvalExpr` derivation (`cases`): only rule `Bop` applies, the divisor is the
constant `0`, and `simp` shows that `⟦/⟧(v, 0)` is `none`, contradicting the premise. -/
theorem no_eval_div_zero (σ : Store) :
    ¬ ∃ v, EvalExpr σ (.bin .div (.var "x") (.const 0)) v := by
  rintro ⟨v, h⟩
  cases h with
  | bop _ h₂ hop => cases h₂; simp [BinOp.interp] at hop

/-- `x % 0` has no derivation, in any store (same proof as `no_eval_div_zero`). -/
theorem no_eval_rem_zero (σ : Store) :
    ¬ ∃ v, EvalExpr σ (.bin .rem (.var "x") (.const 0)) v := by
  rintro ⟨v, h⟩
  cases h with
  | bop _ h₂ hop => cases h₂; simp [BinOp.interp] at hop

/-- The identity `a = (a / b) * b + a % b` for `b ≠ 0`, stated for the interpretation of
`/` and `%`.
Proof: `simp` with `b ≠ 0` turns the two premises into `Int.fdiv a b = q` and
`Int.fmod a b = r`; after `subst`, the core lemma `Int.mul_fdiv_add_fmod`
(`b * a.fdiv b + a.fmod b = a`) and commutativity of `*` close the goal. -/
theorem div_mod_identity (a b q r : Int) (hb : b ≠ 0)
    (hq : BinOp.div.interp a b = some q) (hr : BinOp.rem.interp a b = some r) :
    a = q * b + r := by
  simp [BinOp.interp, hb] at hq hr
  subst hq hr
  rw [Int.mul_comm]
  exact (Int.mul_fdiv_add_fmod a b).symm

/-! ## An auxiliary interpreter, proved sound w.r.t. `BigStep` -/

/-- Fuel-based interpreter (local to this file). -/
def run : Nat → ProcEnv → Store → Code → Option Store
  | 0, _, _, _ => none
  | _ + 1, _, σ, .stmt (.assVar x op e) =>
      (e.eval σ).map fun v => σ.update (.var x) (op.interp (σ (.var x)) v)
  | _ + 1, _, σ, .stmt (.assArr x el op e) =>
      match el.eval σ, e.eval σ with
      | some vl, some v => some (σ.update (.elem x vl) (op.interp (σ (.elem x vl)) v))
      | _, _ => none
  | n + 1, Γ, σ, .stmt (.call id) =>
      match Γ id with
      | some s => run n Γ σ (.stmt s)
      | none => none
  | n + 1, Γ, σ, .stmt (.uncall id) =>
      match Γ id with
      | some s => run n Γ σ (.stmt s.invert)
      | none => none
  | n + 1, Γ, σ, .stmt (.seq s₁ s₂) =>
      match run n Γ σ (.stmt s₁) with
      | some σ' => run n Γ σ' (.stmt s₂)
      | none => none
  | n + 1, Γ, σ, .stmt (.ite e₁ s₁ s₂ e₂) =>
      match e₁.eval σ with
      | some v₁ =>
        if v₁ ≠ 0 then
          match run n Γ σ (.stmt s₁) with
          | some σ' => match e₂.eval σ' with
            | some v₂ => if v₂ ≠ 0 then some σ' else none
            | none => none
          | none => none
        else
          match run n Γ σ (.stmt s₂) with
          | some σ' => match e₂.eval σ' with
            | some v₂ => if v₂ = 0 then some σ' else none
            | none => none
          | none => none
      | none => none
  | n + 1, Γ, σ, .stmt (.loop e₁ s₁ s₂ e₂) =>
      match e₁.eval σ with
      | some v₁ =>
        if v₁ ≠ 0 then
          match run n Γ σ (.stmt s₁) with
          | some σ' => run n Γ σ' (.loopCont e₁ s₁ e₂ s₂)
          | none => none
        else none
      | none => none
  | _ + 1, _, σ, .stmt .skip => some σ
  | n + 1, Γ, σ, .loopCont e₁ s₁ e₂ s₂ =>
      match e₂.eval σ with
      | some v₂ =>
        if v₂ ≠ 0 then some σ
        else
          match run n Γ σ (.stmt s₂) with
          | some σ' => match e₁.eval σ' with
            | some v₁ =>
              if v₁ = 0 then
                match run n Γ σ' (.stmt s₁) with
                | some σ'' => run n Γ σ'' (.loopCont e₁ s₁ e₂ s₂)
                | none => none
              else none
            | none => none
          | none => none
      | none => none

/-- Soundness of the interpreter.
Proof: induction on the fuel (structural recursion), then case analysis on the code; in each
case `simp only [run]` unfolds one step, `split at h` follows the branches of the `match`es
and `if`s, failing branches are closed by `simp at h`, and the successful branch builds the
corresponding `BigStep` rule from the induction hypotheses and `evalExpr_iff_eval`. -/
theorem run_sound : ∀ (n : Nat) (Γ : ProcEnv) (σ : Store) (c : Code) (σ' : Store),
    run n Γ σ c = some σ' → BigStep Γ σ c σ'
  | 0, _, _, _, _, h => by simp [run] at h
  | n + 1, Γ, σ, c, σ', h => by
    have ih := run_sound n Γ
    match c with
    | .stmt (.assVar x op e) =>
      simp only [run, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact .assVar (evalExpr_iff_eval.2 hv)
    | .stmt (.assArr x el op e) =>
      simp only [run] at h
      split at h
      · rename_i vl v hl he; cases h; exact .assArr (evalExpr_iff_eval.2 hl) (evalExpr_iff_eval.2 he)
      · simp at h
    | .stmt (.call id) =>
      simp only [run] at h
      split at h
      · rename_i s hs; exact .call hs (ih _ _ _ h)
      · simp at h
    | .stmt (.uncall id) =>
      simp only [run] at h
      split at h
      · rename_i s hs; exact .uncall hs (ih _ _ _ h)
      · simp at h
    | .stmt (.seq s₁ s₂) =>
      simp only [run] at h
      split at h
      · rename_i σ₁ h₁; exact .seq (ih _ _ _ h₁) (ih _ _ _ h)
      · simp at h
    | .stmt (.ite e₁ s₁ s₂ e₂) =>
      simp only [run] at h
      split at h
      · rename_i v₁ he₁
        split at h
        · rename_i ht
          split at h
          · rename_i σ₁ h₁
            split at h
            · rename_i v₂ he₂
              split at h
              · rename_i ht₂; cases h
                exact .ifTrue (evalExpr_iff_eval.2 he₁) ht (ih _ _ _ h₁) (evalExpr_iff_eval.2 he₂) ht₂
              · simp at h
            · simp at h
          · simp at h
        · rename_i hf
          split at h
          · rename_i σ₁ h₁
            split at h
            · rename_i v₂ he₂
              split at h
              · rename_i hf₂; cases h
                exact .ifFalse (evalExpr_iff_eval.2 he₁) (by simpa [IsFalse] using hf)
                  (ih _ _ _ h₁) (evalExpr_iff_eval.2 he₂) hf₂
              · simp at h
            · simp at h
          · simp at h
      · simp at h
    | .stmt (.loop e₁ s₁ s₂ e₂) =>
      simp only [run] at h
      split at h
      · rename_i v₁ he₁
        split at h
        · rename_i ht
          split at h
          · rename_i σ₁ h₁
            exact .loopMain (evalExpr_iff_eval.2 he₁) ht (ih _ _ _ h₁) (ih _ _ _ h)
          · simp at h
        · simp at h
      · simp at h
    | .stmt .skip =>
      simp only [run, Option.some.injEq] at h
      subst h; exact .skip
    | .loopCont e₁ s₁ e₂ s₂ =>
      simp only [run] at h
      split at h
      · rename_i v₂ he₂
        split at h
        · rename_i ht; cases h; exact .loopBase (evalExpr_iff_eval.2 he₂) ht
        · rename_i hf
          split at h
          · rename_i σ₁ h₁
            split at h
            · rename_i v₁ he₁
              split at h
              · rename_i hf₁
                split at h
                · rename_i σ₂ h₂
                  exact .loopRec (evalExpr_iff_eval.2 he₂) (by simpa [IsFalse] using hf)
                    (ih _ _ _ h₁) (evalExpr_iff_eval.2 he₁) hf₁ (ih _ _ _ h₂) (ih _ _ _ h)
                · simp at h
              · simp at h
            · simp at h
          · simp at h
      · simp at h

/-- If the interpreter returns a store whose value at `l` is `v`, a derivation exists.
Proof: case analysis on the result of `run` and `run_sound`. Each positive test below then
only needs `decide` to evaluate the interpreter on a concrete program. -/
theorem exec_of_run {Γ : ProcEnv} {σ : Store} {s : Stmt} (n : Nat) {l : Loc} {v : Value}
    (h : ((run n Γ σ (.stmt s)).map fun σ' => σ' l) = some v) :
    ∃ σ', Exec Γ σ s σ' ∧ σ' l = v := by
  cases hr : run n Γ σ (.stmt s) with
  | none => simp [hr] at h
  | some σ' =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    exact ⟨σ', run_sound n Γ σ _ σ' hr, h⟩

/-! ## (c) Positive big-step derivations -/

def noProcs : ProcEnv := fun _ => none

/-- `x += 3; x -= 1` from `ε` gives `x = 2`. -/
def prog_assign : Stmt := .seq (.assVar "x" .add (.const 3)) (.assVar "x" .sub (.const 1))
theorem pos_assign : ∃ σ', Exec noProcs Store.empty prog_assign σ' ∧ σ' (.var "x") = 2 :=
  exec_of_run 10 (by decide)

/-- `if x = 0 then x += 1 else x -= 1 fi x = 1` (true branch, from ε): `x = 1`. -/
def prog_ifTrue : Stmt :=
  .ite (.bin .eq (.var "x") (.const 0)) (.assVar "x" .add (.const 1))
    (.assVar "x" .sub (.const 1)) (.bin .eq (.var "x") (.const 1))
theorem pos_ifTrue : ∃ σ', Exec noProcs Store.empty prog_ifTrue σ' ∧ σ' (.var "x") = 1 :=
  exec_of_run 10 (by decide)

/-- `if x != 0 then x += 1 else x -= 1 fi x = 1` (false branch, from ε): the test is false,
`x -= 1` gives `x = -1`, and the assertion `x = 1` is false, as required. -/
def prog_ifFalse : Stmt :=
  .ite (.bin .ne (.var "x") (.const 0)) (.assVar "x" .add (.const 1))
    (.assVar "x" .sub (.const 1)) (.bin .eq (.var "x") (.const 1))
theorem pos_ifFalse : ∃ σ', Exec noProcs Store.empty prog_ifFalse σ' ∧ σ' (.var "x") = -1 :=
  exec_of_run 10 (by decide)

/-- `from i = 0 do skip loop i += 1 until i = 3` (LoopMain, 3 × LoopRec, LoopBase). -/
def prog_loop : Stmt :=
  .loop (.bin .eq (.var "i") (.const 0)) .skip (.assVar "i" .add (.const 1))
    (.bin .eq (.var "i") (.const 3))
theorem pos_loop : ∃ σ', Exec noProcs Store.empty prog_loop σ' ∧ σ' (.var "i") = 3 :=
  exec_of_run 20 (by decide)

/-- Procedure `inc: x += 1`. -/
def incEnv : ProcEnv := fun id => if id = "inc" then some (.assVar "x" .add (.const 1)) else none
theorem pos_call : ∃ σ', Exec incEnv Store.empty (.call "inc") σ' ∧ σ' (.var "x") = 1 :=
  exec_of_run 10 (by decide)
theorem pos_uncall : ∃ σ', Exec incEnv Store.empty (.uncall "inc") σ' ∧ σ' (.var "x") = -1 :=
  exec_of_run 10 (by decide)

/-! ## (d) Negative tests: no derivation exists -/

/-- Value of an expression from its evaluation (via `evalExpr_iff_eval`). -/
theorem val_of {σ : Store} {e : Expr} {v w : Value} (h : EvalExpr σ e v)
    (hw : e.eval σ = some w) : v = w :=
  Option.some.inj ((evalExpr_iff_eval.1 h).symm.trans hw)

/-- `if x = 0 then x += 1 else skip fi x = 0` from ε: the test is true but the assertion
is false after the then-branch.
Proof: invert the derivation (`cases`). In `IfTrue`, inverting the then-branch fixes the
store, and `val_of` with `decide` computes the assertion as `0`, contradicting `IsTrue`. In
`IfFalse`, the test evaluates to `1`, contradicting `IsFalse` (`decide`). -/
theorem neg_if : ¬ ∃ σ', Exec noProcs Store.empty
    (.ite (.bin .eq (.var "x") (.const 0)) (.assVar "x" .add (.const 1)) .skip
      (.bin .eq (.var "x") (.const 0))) σ' := by
  rintro ⟨σ', h⟩
  cases h with
  | ifTrue he₁ ht₁ hs he₂ ht₂ =>
    cases hs with
    | assVar he =>
      cases he
      have := val_of he₂ (w := 0) (by decide)
      subst this; exact ht₂ rfl
  | ifFalse he₁ hf₁ _ _ _ =>
    have := val_of he₁ (w := 1) (by decide)
    subst this; exact absurd hf₁ (by decide)

/-- `from i = 1 do skip loop skip until i = 0` from ε: the entry assertion is false.
Proof: only `LoopMain` applies (`cases`); `val_of` with `decide` evaluates `i = 1` to `0`,
contradicting `IsTrue`. -/
theorem neg_loop_entry : ¬ ∃ σ', Exec noProcs Store.empty
    (.loop (.bin .eq (.var "i") (.const 1)) .skip .skip (.bin .eq (.var "i") (.const 0))) σ' := by
  rintro ⟨σ', h⟩
  cases h with
  | loopMain he₁ ht₁ _ _ =>
    have := val_of he₁ (w := 0) (by decide)
    subst this; exact ht₁ rfl

/-- `call nope` with no procedure defined.
Proof: only rule `Call` applies (`cases`), and its premise `Γ nope = some s` is false
(`simp`). The same proof works for `uncall`. -/
theorem neg_call_undefined : ¬ ∃ σ', Exec noProcs Store.empty (.call "nope") σ' := by
  rintro ⟨σ', h⟩
  cases h with
  | call hΓ _ => simp [noProcs] at hΓ

theorem neg_uncall_undefined : ¬ ∃ σ', Exec noProcs Store.empty (.uncall "nope") σ' := by
  rintro ⟨σ', h⟩
  cases h with
  | uncall hΓ _ => simp [noProcs] at hΓ

/-! ## (e) Inverter -/

theorem inv_op_involution (op : ModOp) : op.invert.invert = op := ModOp.invert_invert op
theorem inv_involution (s : Stmt) : s.invert.invert = s := Stmt.invert_invert s

-- Figure 4, clause by clause.
example : ModOp.add.invert = .sub := rfl
example : ModOp.sub.invert = .add := rfl
example : ModOp.xor.invert = .xor := rfl
example (x op e) : (Stmt.assVar x op e).invert = .assVar x op.invert e := rfl
example (x e₁ op e₂) : (Stmt.assArr x e₁ op e₂).invert = .assArr x e₁ op.invert e₂ := rfl
example (e₁ s₁ s₂ e₂) : (Stmt.ite e₁ s₁ s₂ e₂).invert = .ite e₂ s₁.invert s₂.invert e₁ := rfl
example (e₁ s₁ s₂ e₂) : (Stmt.loop e₁ s₁ s₂ e₂).invert = .loop e₂ s₁.invert s₂.invert e₁ := rfl
example (id) : (Stmt.call id).invert = .uncall id := rfl
example (id) : (Stmt.uncall id).invert = .call id := rfl
example : Stmt.skip.invert = .skip := rfl
example (s₁ s₂) : (Stmt.seq s₁ s₂).invert = .seq s₂.invert s₁.invert := rfl

/-! ## (f) Determinism (already proved in the project) and a concrete inversion check -/

theorem det_expr {σ : Store} {e : Expr} {v w : Value} (h₁ : EvalExpr σ e v)
    (h₂ : EvalExpr σ e w) : v = w := EvalExpr.det h₁ h₂

theorem det_bigstep {Γ : ProcEnv} {σ σ₁ σ₂ : Store} {c : Code}
    (h₁ : BigStep Γ σ c σ₁) (h₂ : BigStep Γ σ c σ₂) : σ₁ = σ₂ := BigStep.det h₁ h₂

/-- Running the inverse of the loop program from its final store gives back `i = 0`. -/
theorem inverse_loop_concrete :
    ∃ σ', Exec noProcs ((Store.empty).update (.var "i") 3) prog_loop.invert σ' ∧
      σ' (.var "i") = 0 :=
  exec_of_run 20 (by decide)

/-! ## (g) Programs without procedures (L2) -/

/-- A program consisting of the main body `x += 1` only. -/
def onlyMainProg : Program := { main := .assVar "x" .add (.const 1), procs := [] }

/-- Its execution from `ε` ends with `x = 1`. Proof: `Program.Exec` unfolds to `Exec`, then
`exec_of_run` and `decide`. -/
theorem pos_onlyMain : ∃ σ', onlyMainProg.Exec σ' ∧ σ' (.var "x") = 1 :=
  exec_of_run (Γ := onlyMainProg.procEnv) 10 (by decide)

/-- In such a program, `call` has no derivation. Proof: as `neg_call_undefined`, using
`Program.procEnv_of_procs_nil`. -/
theorem neg_onlyMain_call :
    ¬ ∃ σ', Exec onlyMainProg.procEnv Store.empty (.call "f") σ' := by
  rintro ⟨σ', h⟩
  cases h with
  | call hΓ _ => simp [Program.procEnv_of_procs_nil (p := onlyMainProg) rfl] at hΓ

/-! ## (h) Cancellation lemmas (L3) and assignment-level inversion (L5) -/

theorem cancel_invert_interp (op : ModOp) (a v : Int) :
    op.invert.interp (op.interp a v) v = a := ModOp.interp_invert_interp op a v
theorem cancel_interp_invert (op : ModOp) (a v : Int) :
    op.interp (op.invert.interp a v) v = a := ModOp.interp_interp_invert op a v

/-- Concrete instance of `BigStep.assVar_invert`: `x -= y` undone by `x += y`.
Proof: `decide` checks well-formedness (`x` does not occur in `y`). -/
theorem inv_assVar_example {σ σ' : Store}
    (h : Exec noProcs σ (.assVar "x" .sub (.var "y")) σ') :
    Exec noProcs σ' (.assVar "x" .add (.var "y")) σ :=
  BigStep.assVar_invert (by decide) h

/-- Concrete instance of `BigStep.assArr_invert`: `a[i] ^= y` is its own inverse. -/
theorem inv_assArr_example {σ σ' : Store}
    (h : Exec noProcs σ (.assArr "a" (.var "i") .xor (.var "y")) σ') :
    Exec noProcs σ' (.assArr "a" (.var "i") .xor (.var "y")) σ :=
  BigStep.assArr_invert (by decide) h

#print axioms store_get_set
#print axioms store_set_other_var
#print axioms store_scalar_does_not_touch_cell
#print axioms store_cell_does_not_touch_scalar
#print axioms store_cell_does_not_touch_other_cell
#print axioms store_empty_zero
#print axioms eval_sub_order₁
#print axioms eval_sub_order₂
#print axioms eval_arr
#print axioms interp_add
#print axioms interp_no_overflow
#print axioms interp_divmod_neg_pos
#print axioms interp_divmod_pos_neg
#print axioms interp_divmod_neg_neg
#print axioms interp_divmod_pos_pos
#print axioms interp_bitwise_neg
#print axioms interp_div_zero
#print axioms interp_rem_zero
#print axioms interp_lt
#print axioms interp_land
#print axioms interp_band
#print axioms interp_lor
#print axioms interp_bor
#print axioms interp_xor
#print axioms no_eval_div_zero
#print axioms no_eval_rem_zero
#print axioms div_mod_identity
#print axioms interp_land_strict
#print axioms run_sound
#print axioms pos_assign
#print axioms pos_ifTrue
#print axioms pos_ifFalse
#print axioms pos_loop
#print axioms pos_call
#print axioms pos_uncall
#print axioms neg_if
#print axioms neg_loop_entry
#print axioms neg_call_undefined
#print axioms neg_uncall_undefined
#print axioms inv_op_involution
#print axioms inv_involution
#print axioms det_expr
#print axioms det_bigstep
#print axioms inverse_loop_concrete
#print axioms pos_onlyMain
#print axioms neg_onlyMain_call
#print axioms cancel_invert_interp
#print axioms cancel_interp_invert
#print axioms inv_assVar_example
#print axioms inv_assArr_example
#print axioms eval_var
#print axioms eval_unset_var
#print axioms val_of
#print axioms exec_of_run
#print axioms Janus.ModOp.interp_invert_interp
#print axioms Janus.ModOp.interp_interp_invert
#print axioms Janus.Expr.eval_update
#print axioms Janus.EvalExpr.update_iff
#print axioms Janus.BigStep.assVar_invert
#print axioms Janus.BigStep.assArr_invert
#print axioms Janus.Program.procEnv_of_procs_nil

end Janus.SyntaxChecks
