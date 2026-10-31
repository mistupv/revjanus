module

public import RequestProject.Janus.Inverter

/-!
# Janus: big-step semantics

This file formalizes the standard big-step semantics of (sequential) Janus:

* stores (`Store`), mapping variables and indexed variables to values;
* the interpretation functions `⟦⊕⟧` (`ModOp.interp`) and `⟦⊙⟧` (`BinOp.interp`);
* the evaluation of expressions `⟨σ, e⟩ ⇓ v` (Figure "Semantics of expressions"),
  as the inductive relation `EvalExpr`, together with an equivalent evaluation
  function `Expr.eval`;
* the big-step semantics of statements `⟨σ, s⟩ ⇓ σ'` and of loop configurations
  `⟨σ, (e₁, s₁, e₂, s₂)⟩ ⇓ σ'` (Figure "Big-step semantics of sequential Janus"),
  as the inductive relation `BigStep`.

## Modelling choices

* Following the default behaviour of the Jana interpreter, values are unbounded integers
  (`Int`); a constant `c : Int32` denotes `c.toInt`. Arithmetic does not wrap around.
* Truth values follow the usual Janus convention: `is_true?(v)` iff `v ≠ 0` and
  `is_false?(v)` iff `v = 0`; relational and logical operators return `1` for true
  and `0` for false.
* The interpretation `⟦⊙⟧(v₁, v₂) = v` of binary operators is partial: division `/` and
  modulus `%` by zero are undefined (no value `v` exists, so rule `Bop` does not apply).
  `/` is floor division (`Int.fdiv`) and `%` the corresponding modulus (`Int.fmod`), so that
  `a = (a / b) * b + a % b` and `a % b` has the sign of `b`. Note that `Int.fdiv a 0 = 0`
  in Lean, hence the explicit side condition `v₂ ≠ 0`.
* `&`, `|` and `^` are bitwise operations on the two's complement representation
  (`Int.land`, `Int.lor`, `Int.xor`, from `Mathlib.Data.Int.Bitwise`).
* The procedure environment `Γ` is a partial map from identifiers to bodies; rules `Call`
  and `UnCall` only apply to declared procedures.
* The loop configuration `(e₁, s₁, e₂, s₂)` used by rules `LoopMain`, `LoopBase` and
  `LoopRec` is an auxiliary kind of code (`Code.loopCont`) besides statements
  (`Code.stmt`), so that the whole semantics is a single inductive relation.
-/

@[expose] public section

namespace Janus

/-! ### Stores -/

/-- Locations: variable names `x` and indexed variable names `x[v]`. -/
inductive Loc where
  /-- A (scalar) variable `x`. -/
  | var (x : Var)
  /-- An indexed variable (array element) `x[v]`. -/
  | elem (x : Var) (i : Value)
  deriving DecidableEq, Repr

/-- A store `σ` is a (total) function from variable names and indexed variable names to
values. Variables that are not explicitly initialized have value zero. -/
abbrev Store := Loc → Value

/-- The empty store `ε`, mapping every variable to zero. -/
def Store.empty : Store := fun _ => 0

/-- The store update `σ[ℓ ↦ v]`. -/
abbrev Store.update (σ : Store) (ℓ : Loc) (v : Value) : Store := Function.update σ ℓ v

/-! ### Interpretation of operators and truth values -/

/-- `is_true?(v)`: a value is true iff it is nonzero. -/
def IsTrue (v : Value) : Prop := v ≠ 0

/-- `is_false?(v)`: a value is false iff it is zero. -/
def IsFalse (v : Value) : Prop := v = 0

instance (v : Value) : Decidable (IsTrue v) := inferInstanceAs (Decidable (v ≠ 0))
instance (v : Value) : Decidable (IsFalse v) := inferInstanceAs (Decidable (v = 0))

theorem not_isTrue_iff_isFalse (v : Value) : ¬ IsTrue v ↔ IsFalse v := by
  simp [IsTrue, IsFalse]

/-- Encoding of booleans as values: `1` for true, `0` for false. -/
def ofBool (b : Bool) : Value := if b then 1 else 0

/-- Interpretation `⟦⊕⟧` of the update operators `+`, `-`, `^`. -/
def ModOp.interp : ModOp → Value → Value → Value
  | .add, v₁, v₂ => v₁ + v₂
  | .sub, v₁, v₂ => v₁ - v₂
  | .xor, v₁, v₂ => Int.xor v₁ v₂

/-! #### Cancellation lemmas (Fig. 4): `𝓘ₒₚ⟦⊕⟧` undoes `⊕` and vice versa -/

/-- Undoing an update: `⟦𝓘ₒₚ⟦⊕⟧⟧(⟦⊕⟧(a, v), v) = a`.
Proof: case analysis on the operator. For `+` and `-`, after unfolding, the goal is linear
integer arithmetic, closed by `omega` (the variables are typed `Int` rather than `Value`
because `omega` does not see through the abbreviation `Value`). For `^`, case analysis on the signs of `a` and
`v`, unfolding `Int.xor` and using `Nat.xor_xor_cancel_right`. -/
theorem ModOp.interp_invert_interp (op : ModOp) (a v : Int) :
    op.invert.interp (op.interp a v) v = a := by
  cases op
  · show (a + v : Int) - v = a; omega
  · show (a - v : Int) + v = a; omega
  · show Int.xor (Int.xor a v) v = a
    cases a <;> cases v <;> simp [Int.xor, Nat.xor_xor_cancel_right]

/-- Redoing after undoing: `⟦⊕⟧(⟦𝓘ₒₚ⟦⊕⟧⟧(a, v), v) = a`.
Proof: apply `ModOp.interp_invert_interp` to `op.invert`, using `ModOp.invert_invert`. -/
theorem ModOp.interp_interp_invert (op : ModOp) (a v : Int) :
    op.interp (op.invert.interp a v) v = a := by
  simpa using ModOp.interp_invert_interp op.invert a v

/-- Interpretation `⟦⊙⟧` of binary operators. It is partial: division and remainder by
zero are undefined. -/
def BinOp.interp : BinOp → Value → Value → Option Value
  | .mod op, v₁, v₂ => some (op.interp v₁ v₂)
  | .mul, v₁, v₂ => some (v₁ * v₂)
  | .div, v₁, v₂ => if v₂ = 0 then none else some (Int.fdiv v₁ v₂)
  | .rem, v₁, v₂ => if v₂ = 0 then none else some (Int.fmod v₁ v₂)
  | .band, v₁, v₂ => some (Int.land v₁ v₂)
  | .land, v₁, v₂ => some (ofBool (v₁ ≠ 0 && v₂ ≠ 0))
  | .lor, v₁, v₂ => some (ofBool (v₁ ≠ 0 || v₂ ≠ 0))
  | .bor, v₁, v₂ => some (Int.lor v₁ v₂)
  | .lt, v₁, v₂ => some (ofBool (v₁ < v₂))
  | .gt, v₁, v₂ => some (ofBool (v₁ > v₂))
  | .eq, v₁, v₂ => some (ofBool (v₁ = v₂))
  | .ne, v₁, v₂ => some (ofBool (v₁ ≠ v₂))
  | .le, v₁, v₂ => some (ofBool (v₁ ≤ v₂))
  | .ge, v₁, v₂ => some (ofBool (v₁ ≥ v₂))

/-! ### Semantics of expressions -/

/-- Evaluation of expressions: `EvalExpr σ e v` is the judgement `⟨σ, e⟩ ⇓ v`. -/
inductive EvalExpr (σ : Store) : Expr → Value → Prop where
  /-- Rule `Con`: `⟨σ, c⟩ ⇓ ⟦c⟧`, where `⟦c⟧ = c.toInt`. -/
  | con (c : Const) : EvalExpr σ (.const c) c.toInt
  /-- Rule `Var`: `⟨σ, x⟩ ⇓ σ(x)`. -/
  | var (x : Var) : EvalExpr σ (.var x) (σ (.var x))
  /-- Rule `Arr`: if `⟨σ, e⟩ ⇓ v` then `⟨σ, x[e]⟩ ⇓ σ(x[v])`. -/
  | arr {x : Var} {e : Expr} {v : Value} :
      EvalExpr σ e v → EvalExpr σ (.arr x e) (σ (.elem x v))
  /-- Rule `Bop`: if `⟨σ, e₁⟩ ⇓ v₁`, `⟨σ, e₂⟩ ⇓ v₂` and `⟦⊙⟧(v₁, v₂) = v`,
  then `⟨σ, e₁ ⊙ e₂⟩ ⇓ v`. -/
  | bop {op : BinOp} {e₁ e₂ : Expr} {v₁ v₂ v : Value} :
      EvalExpr σ e₁ v₁ → EvalExpr σ e₂ v₂ → op.interp v₁ v₂ = some v →
      EvalExpr σ (.bin op e₁ e₂) v

/-- Functional version of expression evaluation (`none` when the evaluation is
undefined, i.e. on division or remainder by zero). -/
def Expr.eval (σ : Store) : Expr → Option Value
  | .const c => some c.toInt
  | .var x => some (σ (.var x))
  | .arr x e => (e.eval σ).map fun v => σ (.elem x v)
  | .bin op e₁ e₂ => do
      let v₁ ← e₁.eval σ
      let v₂ ← e₂.eval σ
      op.interp v₁ v₂

/-- The evaluation relation agrees with the evaluation function. -/
theorem evalExpr_iff_eval {σ : Store} {e : Expr} {v : Value} :
    EvalExpr σ e v ↔ e.eval σ = some v := by
  constructor
  · intro h
    induction h with
    | con c => rfl
    | var x => rfl
    | arr _ ih => simp [Expr.eval, ih]
    | bop _ _ hop ih₁ ih₂ => simp [Expr.eval, ih₁, ih₂, hop]
  · induction e generalizing v with
    | const c => intro h; cases h; exact .con c
    | var x => intro h; cases h; exact .var x
    | arr x e ih =>
      intro h
      simp only [Expr.eval, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact .arr (ih hw)
    | bin op e₁ e₂ ih₁ ih₂ =>
      intro h
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨v₁, h₁, v₂, h₂, h⟩ := h
      exact .bop (ih₁ h₁) (ih₂ h₂) h

/-- Expression evaluation is deterministic. -/
theorem EvalExpr.det {σ : Store} {e : Expr} {v w : Value}
    (h₁ : EvalExpr σ e v) (h₂ : EvalExpr σ e w) : v = w := by
  rw [evalExpr_iff_eval] at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ### Big-step semantics of statements -/

/-- Procedure environments `Γ`, mapping (declared) procedure identifiers to their
bodies. -/
abbrev ProcEnv := ProcId → Option Stmt

/-- The code appearing in big-step judgements: either a statement `s`, or an auxiliary
loop configuration `(e₁, s₁, e₂, s₂)` (used by rules `LoopMain`, `LoopBase` and
`LoopRec`). -/
inductive Code where
  /-- A statement `s`. -/
  | stmt (s : Stmt)
  /-- A loop configuration `(e₁, s₁, e₂, s₂)` for `from e₁ do s₁ loop s₂ until e₂`,
  reached after the loop body `s₁` has been executed. -/
  | loopCont (e₁ : Expr) (s₁ : Stmt) (e₂ : Expr) (s₂ : Stmt)
  deriving DecidableEq, Repr

/-- The big-step semantics of Janus: `BigStep Γ σ c σ'` is the judgement `⟨σ, c⟩ ⇓ σ'`
(relative to the procedure environment `Γ`). -/
inductive BigStep (Γ : ProcEnv) : Store → Code → Store → Prop where
  /-- Rule `AssVar`. -/
  | assVar {σ : Store} {x : Var} {op : ModOp} {e : Expr} {v : Value} :
      EvalExpr σ e v →
      BigStep Γ σ (.stmt (.assVar x op e))
        (σ.update (.var x) (op.interp (σ (.var x)) v))
  /-- Rule `AssArr`. -/
  | assArr {σ : Store} {x : Var} {eₗ : Expr} {op : ModOp} {e : Expr} {vₗ v : Value} :
      EvalExpr σ eₗ vₗ → EvalExpr σ e v →
      BigStep Γ σ (.stmt (.assArr x eₗ op e))
        (σ.update (.elem x vₗ) (op.interp (σ (.elem x vₗ)) v))
  /-- Rule `Call`. -/
  | call {σ σ' : Store} {id : ProcId} {s : Stmt} :
      Γ id = some s →
      BigStep Γ σ (.stmt s) σ' →
      BigStep Γ σ (.stmt (.call id)) σ'
  /-- Rule `UnCall`: executes the inversion `𝓘⟦Γ(id)⟧` of the procedure body. -/
  | uncall {σ σ' : Store} {id : ProcId} {s : Stmt} :
      Γ id = some s →
      BigStep Γ σ (.stmt s.invert) σ' →
      BigStep Γ σ (.stmt (.uncall id)) σ'
  /-- Rule `Seq`. -/
  | seq {σ σ' σ'' : Store} {s₁ s₂ : Stmt} :
      BigStep Γ σ (.stmt s₁) σ' →
      BigStep Γ σ' (.stmt s₂) σ'' →
      BigStep Γ σ (.stmt (.seq s₁ s₂)) σ''
  /-- Rule `IfTrue`. -/
  | ifTrue {σ σ' : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ v₂ : Value} :
      EvalExpr σ e₁ v₁ → IsTrue v₁ →
      BigStep Γ σ (.stmt s₁) σ' →
      EvalExpr σ' e₂ v₂ → IsTrue v₂ →
      BigStep Γ σ (.stmt (.ite e₁ s₁ s₂ e₂)) σ'
  /-- Rule `IfFalse`. -/
  | ifFalse {σ σ' : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ v₂ : Value} :
      EvalExpr σ e₁ v₁ → IsFalse v₁ →
      BigStep Γ σ (.stmt s₂) σ' →
      EvalExpr σ' e₂ v₂ → IsFalse v₂ →
      BigStep Γ σ (.stmt (.ite e₁ s₁ s₂ e₂)) σ'
  /-- Rule `LoopMain`. -/
  | loopMain {σ σ' σ'' : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ : Value} :
      EvalExpr σ e₁ v₁ → IsTrue v₁ →
      BigStep Γ σ (.stmt s₁) σ' →
      BigStep Γ σ' (.loopCont e₁ s₁ e₂ s₂) σ'' →
      BigStep Γ σ (.stmt (.loop e₁ s₁ s₂ e₂)) σ''
  /-- Rule `LoopBase`. -/
  | loopBase {σ : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₂ : Value} :
      EvalExpr σ e₂ v₂ → IsTrue v₂ →
      BigStep Γ σ (.loopCont e₁ s₁ e₂ s₂) σ
  /-- Rule `LoopRec`. -/
  | loopRec {σ σ' σ'' σ''' : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ v₂ : Value} :
      EvalExpr σ e₂ v₂ → IsFalse v₂ →
      BigStep Γ σ (.stmt s₂) σ' →
      EvalExpr σ' e₁ v₁ → IsFalse v₁ →
      BigStep Γ σ' (.stmt s₁) σ'' →
      BigStep Γ σ'' (.loopCont e₁ s₁ e₂ s₂) σ''' →
      BigStep Γ σ (.loopCont e₁ s₁ e₂ s₂) σ'''
  /-- Rule `Skip`. -/
  | skip {σ : Store} : BigStep Γ σ (.stmt .skip) σ

/-- The judgement `⟨σ, s⟩ ⇓ σ'` for a statement `s`. -/
abbrev Exec (Γ : ProcEnv) (σ : Store) (s : Stmt) (σ' : Store) : Prop :=
  BigStep Γ σ (.stmt s) σ'

/-- The big-step semantics is deterministic. -/
theorem BigStep.det {Γ : ProcEnv} {σ σ₁ σ₂ : Store} {c : Code}
    (h₁ : BigStep Γ σ c σ₁) (h₂ : BigStep Γ σ c σ₂) : σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ with
  | assVar he => cases h₂ with | assVar he' => rw [he.det he']
  | assArr hl he =>
    cases h₂ with | assArr hl' he' => rw [hl.det hl', he.det he']
  | call hΓ _ ih =>
    cases h₂ with | call hΓ' h' => rw [hΓ] at hΓ'; cases hΓ'; exact ih h'
  | uncall hΓ _ ih =>
    cases h₂ with | uncall hΓ' h' => rw [hΓ] at hΓ'; cases hΓ'; exact ih h'
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with | seq h₁' h₂' => cases ih₁ h₁'; exact ih₂ h₂'
  | ifTrue he₁ ht₁ _ _ _ ih =>
    cases h₂ with
    | ifTrue _ _ h' _ _ => exact ih h'
    | ifFalse he₁' hf₁ _ _ _ => exact absurd (he₁.det he₁' ▸ hf₁) ht₁
  | ifFalse he₁ hf₁ _ _ _ ih =>
    cases h₂ with
    | ifTrue he₁' ht₁ _ _ _ => exact absurd (he₁'.det he₁ ▸ hf₁) ht₁
    | ifFalse _ _ h' _ _ => exact ih h'
  | loopMain _ _ _ _ ih₁ ih₂ =>
    cases h₂ with | loopMain _ _ h₁' h₂' => cases ih₁ h₁'; exact ih₂ h₂'
  | loopBase he₂ ht₂ =>
    cases h₂ with
    | loopBase _ _ => rfl
    | loopRec he₂' hf₂ _ _ _ _ _ => exact absurd (he₂.det he₂' ▸ hf₂) ht₂
  | loopRec he₂ hf₂ _ _ _ _ _ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | loopBase he₂' ht₂ => exact absurd (he₂'.det he₂ ▸ hf₂) ht₂
    | loopRec _ _ h₁' _ _ h₂' h₃' => cases ih₁ h₁'; cases ih₂ h₂'; exact ih₃ h₃'
  | skip => cases h₂; rfl

/-! ### Assignment-level inversion -/

/-- The variable name of a location: `x` for both `x` and `x[v]`. -/
def Loc.name : Loc → Var
  | .var x => x
  | .elem x _ => x

/-- Reading the updated location gives the new value. -/
theorem Store.update_apply_self (σ : Store) (ℓ : Loc) (a : Value) : σ.update ℓ a ℓ = a :=
  Function.update_self ℓ a σ

/-- Two consecutive updates of the same location: only the last one counts. -/
theorem Store.update_update_self (σ : Store) (ℓ : Loc) (a b : Value) :
    (σ.update ℓ a).update ℓ b = σ.update ℓ b :=
  Function.update_idem a b σ

/-- Updating a location with its current value does not change the store. -/
theorem Store.update_apply_eq (σ : Store) (ℓ : Loc) : σ.update ℓ (σ ℓ) = σ :=
  Function.update_eq_self ℓ σ

/-- Updating a location whose name does not occur in `e` does not change the value of `e`.
Proof: induction on `e`. For `x` and `x[e']`, the locations read are different from `ℓ`
because their name occurs in `e` (`Function.update_of_ne`); `simp` closes the remaining
goals using the induction hypotheses. -/
theorem Expr.eval_update {e : Expr} {σ : Store} {ℓ : Loc} {w : Value}
    (h : ℓ.name ∉ e.vars) : e.eval (σ.update ℓ w) = e.eval σ := by
  induction e with
  | const c => rfl
  | var x =>
    have hne : Loc.var x ≠ ℓ := by
      rintro rfl; simp [Loc.name, Expr.vars] at h
    simp [Expr.eval, Store.update, Function.update_of_ne hne]
  | arr x e ih =>
    simp only [Expr.vars, List.mem_cons, not_or] at h
    have hne : ∀ v, Loc.elem x v ≠ ℓ := by
      rintro v rfl; exact h.1 rfl
    simp [Expr.eval, ih h.2, Store.update, Function.update_of_ne (hne _)]
  | bin op e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.vars, List.mem_append, not_or] at h
    simp [Expr.eval, ih₁ h.1, ih₂ h.2]

/-- Relational version of `Expr.eval_update`. -/
theorem EvalExpr.update_iff {e : Expr} {σ : Store} {ℓ : Loc} {w v : Value}
    (h : ℓ.name ∉ e.vars) : EvalExpr (σ.update ℓ w) e v ↔ EvalExpr σ e v := by
  rw [evalExpr_iff_eval, evalExpr_iff_eval, Expr.eval_update h]

/-- Inversion of a well-formed variable assignment: if `⟨σ, x ⊕= e⟩ ⇓ σ'` then
`⟨σ', 𝓘⟦x ⊕= e⟧⟩ ⇓ σ`.
Proof: invert the derivation (`cases`); `e` has the same value `v` in `σ'` because `x` does
not occur in `e` (`EvalExpr.update_iff`); apply rule `AssVar` for `𝓘ₒₚ⟦⊕⟧` and show that the
resulting store is `σ` with the store lemmas and `ModOp.interp_invert_interp`. -/
theorem BigStep.assVar_invert {Γ : ProcEnv} {σ σ' : Store} {x : Var} {op : ModOp} {e : Expr}
    (hwf : (Stmt.assVar x op e).WellFormed) (h : Exec Γ σ (.assVar x op e) σ') :
    Exec Γ σ' (Stmt.assVar x op e).invert σ := by
  cases h with
  | assVar he =>
    rename_i v
    have he' := (EvalExpr.update_iff (ℓ := .var x)
      (w := op.interp (σ (.var x)) v) hwf).2 he
    have h' := BigStep.assVar (Γ := Γ) (x := x) (op := op.invert) he'
    rwa [Store.update_apply_self, Store.update_update_self, ModOp.interp_invert_interp,
      Store.update_apply_eq] at h'

/-- Inversion of a well-formed array assignment: if `⟨σ, x[eₗ] ⊕= e⟩ ⇓ σ'` then
`⟨σ', 𝓘⟦x[eₗ] ⊕= e⟧⟩ ⇓ σ`.
Proof: as for `BigStep.assVar_invert`; both `eₗ` and `e` keep their values in `σ'`, so the
inverse assignment updates the same cell `x[vₗ]`. -/
theorem BigStep.assArr_invert {Γ : ProcEnv} {σ σ' : Store} {x : Var} {eₗ : Expr} {op : ModOp}
    {e : Expr} (hwf : (Stmt.assArr x eₗ op e).WellFormed) (h : Exec Γ σ (.assArr x eₗ op e) σ') :
    Exec Γ σ' (Stmt.assArr x eₗ op e).invert σ := by
  cases h with
  | assArr hl he =>
    rename_i vₗ v
    have hl' := (EvalExpr.update_iff (ℓ := .elem x vₗ)
      (w := op.interp (σ (.elem x vₗ)) v) hwf.1).2 hl
    have he' := (EvalExpr.update_iff (ℓ := .elem x vₗ)
      (w := op.interp (σ (.elem x vₗ)) v) hwf.2).2 he
    have h' := BigStep.assArr (Γ := Γ) (x := x) (op := op.invert) hl' he'
    rwa [Store.update_apply_self, Store.update_update_self, ModOp.interp_invert_interp,
      Store.update_apply_eq] at h'

/-! ### Programs -/

/-- The procedure environment `Γ` of a program: it maps each declared identifier to the
body of (the first) procedure declared with that name. -/
def Program.procEnv (p : Program) : ProcEnv :=
  fun id => (p.procs.find? (·.name == id)).map (·.body)

/-- A program without procedure declarations has an empty procedure environment, so that
`call id` and `uncall id` have no derivation. -/
@[simp] theorem Program.procEnv_of_procs_nil {p : Program} (h : p.procs = []) (id : ProcId) :
    p.procEnv id = none := by
  simp [Program.procEnv, h]

/-- Execution of a program: running the main statement from the empty store `ε`
(with the procedure environment of the program) terminates in store `σ'`. -/
def Program.Exec (p : Program) (σ' : Store) : Prop :=
  Janus.Exec p.procEnv Store.empty p.main σ'

end Janus

end
