module

public import RequestProject.Janus.Forward
public import RequestProject.Janus.ForwardCFG

/-!
# Janus: the backward rules of the reversible semantics (Section "The Backward Rules")

This file formalizes the definitions of Subsection "The Backward Rules":

* the inverse CFG `flow⁻¹(s) = {(ℓ', ℓ) | (ℓ, ℓ') ∈ flow(s)}` of a statement
  (`LStmt.invFlow`) and of a program (`LProgram.invFlow`); an edge `ℓ ↢ ℓ'` of the inverse
  CFG is `(ℓ, ℓ') ∈ P.invFlow`, which is equivalent to `ℓ' ⟶ ℓ` (`LProgram.mem_invFlow`);
* the lemma `flow⁻¹(s) = flow(𝓘⟦s⟧)` (`LStmt.invFlow_eq_flow_invert`);
* the backward transition relation `↽` (`BwdStep`), with the rules of Figure "Reversible
  backward semantics: rules for basic constructs" (`AssVar⃖`, `AssArr⃖`, `Call⃖`, `Return1⃖`,
  `UnCall⃖`, `Return2⃖`, `Skip⃖`) and of Figure "Reversible backward semantics: rules for if
  and for loop" (`IfTrue1⃖`, `IfTrue2⃖`, `IfFalse1⃖`, `IfFalse2⃖`, `LoopMain⃖`, `LoopBase⃖`,
  `Loop1⃖`, `Loop2⃖`), and its reflexive–transitive closure (`BwdSteps`);
* the relation `⇌ = ⇀ ∪ ↽` (`RevStep`) and *reachable configurations* (Definition
  "reachable configuration", `LProgram.Reachable`).

The configuration `⟨σ, ℓ₁, ℓ₂, S⟩ ↽ ⟨σ', ℓ₁', ℓ₂', S'⟩` is written `BwdStep P k k'` with
`k = ⟨σ, ℓ₁, ℓ₂, S⟩` (the configuration before the backward step) and
`k' = ⟨σ', ℓ₁', ℓ₂', S'⟩` (the configuration after it): as in the paper, the reduction
proceeds from left to right.

The modelling choices are those of the forward rules (`RequestProject.Janus.Forward`):
`block(ℓ) = o` is `P.block ℓ = some o`, `ctx(ℓ) = t` is `P.ctx ℓ = some t`, and `Γ(id)`,
`Γ(id⁻¹)` are `P.proc (.fwd id)`, `P.proc (.inv id)`.
-/

@[expose] public section

namespace Janus

/-! ### The inverse CFG -/

/-- `flow⁻¹(s) = {(ℓ', ℓ) | (ℓ, ℓ') ∈ flow(s)}`: the inverse CFG of a statement. -/
def LStmt.invFlow (s : LStmt Label) : Finset (Label × Label) := s.flow.image Prod.swap

@[simp] theorem LStmt.mem_invFlow {s : LStmt Label} {ℓ ℓ' : Label} :
    (ℓ, ℓ') ∈ s.invFlow ↔ (ℓ', ℓ) ∈ s.flow := by
  simp [LStmt.invFlow]

/-- **Lemma.** Given a statement `s`, we have `flow⁻¹(s) = flow(𝓘⟦s⟧)`. -/
theorem LStmt.invFlow_eq_flow_invert (s : LStmt Label) : s.invFlow = s.invert.flow :=
  (LStmt.flow_invert s).symm

/-- The inverse CFG `flow⁻¹(p)` of a labeled program: all edges of `flow(p)` reversed. -/
def LProgram.invFlow (P : LProgram Label) : Finset (Label × Label) := P.flow.image Prod.swap

/-- `ℓ ↢ ℓ'` (an edge of the inverse CFG) is equivalent to `ℓ' ⟶ ℓ`. -/
@[simp] theorem LProgram.mem_invFlow {P : LProgram Label} {ℓ ℓ' : Label} :
    (ℓ, ℓ') ∈ P.invFlow ↔ (ℓ', ℓ) ∈ P.flow := by
  simp [LProgram.invFlow]

/-! ### The backward rules -/

/-- The backward transition relation `⟨σ, ℓ₁, ℓ₂, S⟩ ↽ ⟨σ', ℓ₁', ℓ₂', S'⟩` of the reversible
semantics of a labeled program `P` (`BwdStep P ⟨σ, ℓ₁, ℓ₂, S⟩ ⟨σ', ℓ₁', ℓ₂', S'⟩`). -/
inductive BwdStep (P : LProgram Label) : RConfig → RConfig → Prop where
  /-- Rule `AssVar⃖`. -/
  | assVar {σ : Store} {ℓ ℓ' ℓ'' : Label} {x : Var} {op : ModOp} {e : Expr} {v : Value}
      {S : RStack} :
      P.block ℓ' = some (.assVar x op e) → EvalExpr σ e v → (ℓ', ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓ', ℓ'', S⟩
        ⟨σ.update (.var x) (op.invert.interp (σ (.var x)) v), ℓ, ℓ', S⟩
  /-- Rule `AssArr⃖`. -/
  | assArr {σ : Store} {ℓ ℓ' ℓ'' : Label} {x : Var} {eₗ : Expr} {op : ModOp} {e : Expr}
      {vₗ v : Value} {S : RStack} :
      P.block ℓ' = some (.assArr x eₗ op e) → EvalExpr σ eₗ vₗ → EvalExpr σ e v →
      (ℓ', ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓ', ℓ'', S⟩
        ⟨σ.update (.elem x vₗ) (op.invert.interp (σ (.elem x vₗ)) v), ℓ, ℓ', S⟩
  /-- Rule `Call⃖`. -/
  | call {σ : Store} {ℓ ℓ' ℓ'' ℓₛ : Label} {S : RStack} :
      P.block ℓₛ = some .start → (ℓ', ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓₛ, ℓ'', .call ℓ' :: S⟩ ⟨σ, ℓ, ℓ', S⟩
  /-- Rule `Return1⃖`. -/
  | return1 {σ : Store} {ℓ ℓ'' ℓ''' : Label} {id : ProcId} {b : LStmt Label} {S : RStack} :
      P.block ℓ'' = some (.call id) → P.proc (.fwd id) = some b → (b.exit, ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓ'', ℓ''', S⟩ ⟨σ, ℓ, b.exit, .call ℓ'' :: S⟩
  /-- Rule `UnCall⃖`. -/
  | uncall {σ : Store} {ℓ ℓ' ℓ'' ℓₛ : Label} {S : RStack} :
      P.block ℓₛ = some .start → (ℓ', ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓₛ, ℓ'', .uncall ℓ' :: S⟩ ⟨σ, ℓ, ℓ', S⟩
  /-- Rule `Return2⃖`. -/
  | return2 {σ : Store} {ℓ ℓ'' ℓ''' : Label} {id : ProcId} {b : LStmt Label} {S : RStack} :
      P.block ℓ'' = some (.uncall id) → P.proc (.inv id) = some b → (b.exit, ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓ'', ℓ''', S⟩ ⟨σ, ℓ, b.exit, .uncall ℓ'' :: S⟩
  /-- Rule `Skip⃖`. -/
  | skip {σ : Store} {ℓ ℓ' ℓ'' : Label} {S : RStack} :
      P.block ℓ' = some .skip → (ℓ', ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓ', ℓ'', S⟩ ⟨σ, ℓ, ℓ', S⟩
  /-- Rule `IfTrue1⃖`. -/
  | ifTrue1 {σ : Store} {ℓ ℓ₁ ℓ₁' ℓ₂ : Label} {e₁ : Expr} {v₁ : Value} {S : RStack} :
      P.block ℓ₁ = some (.cond e₁) → EvalExpr σ e₁ v₁ → IsTrue v₁ → (ℓ₁, ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓ₁, ℓ₁', .ifTrue ℓ₁ ℓ₂ :: S⟩ ⟨σ, ℓ, ℓ₁, S⟩
  /-- Rule `IfTrue2⃖`. -/
  | ifTrue2 {σ : Store} {ℓ₁ ℓ₂ ℓ₂' : Label} {e₁ e₂ : Expr} {s₁ s₂ : LStmt Label} {v₂ : Value}
      {S : RStack} :
      P.ctx ℓ₂ = some (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) → EvalExpr σ e₂ v₂ → IsTrue v₂ →
      BwdStep P ⟨σ, ℓ₂, ℓ₂', S⟩ ⟨σ, s₁.exit, ℓ₂, .ifTrue ℓ₁ ℓ₂ :: S⟩
  /-- Rule `IfFalse1⃖`. -/
  | ifFalse1 {σ : Store} {ℓ ℓ₁ ℓ₁' ℓ₂ : Label} {e₁ : Expr} {v₁ : Value} {S : RStack} :
      P.block ℓ₁ = some (.cond e₁) → EvalExpr σ e₁ v₁ → IsFalse v₁ → (ℓ₁, ℓ) ∈ P.invFlow →
      BwdStep P ⟨σ, ℓ₁, ℓ₁', .ifFalse ℓ₁ ℓ₂ :: S⟩ ⟨σ, ℓ, ℓ₁, S⟩
  /-- Rule `IfFalse2⃖`. -/
  | ifFalse2 {σ : Store} {ℓ₁ ℓ₂ ℓ₂' : Label} {e₁ e₂ : Expr} {s₁ s₂ : LStmt Label} {v₂ : Value}
      {S : RStack} :
      P.ctx ℓ₂ = some (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) → EvalExpr σ e₂ v₂ → IsFalse v₂ →
      BwdStep P ⟨σ, ℓ₂, ℓ₂', S⟩ ⟨σ, s₂.exit, ℓ₂, .ifFalse ℓ₁ ℓ₂ :: S⟩
  /-- Rule `LoopMain⃖`. -/
  | loopMain {σ : Store} {ℓ ℓ' ℓ₁ ℓ₂ : Label} {e₁ : Expr} {s₁ s₂ : LStmt Label} {v₁ : Value}
      {S : RStack} :
      P.block ℓ₁ = some (.cond e₁) → EvalExpr σ e₁ v₁ → IsTrue v₁ → (ℓ₁, ℓ) ∈ P.invFlow →
      ℓ ≠ s₂.exit →
      BwdStep P ⟨σ, ℓ₁, ℓ', .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩ ⟨σ, ℓ, ℓ₁, S⟩
  /-- Rule `LoopBase⃖`. -/
  | loopBase {σ : Store} {ℓ₁ ℓ₂ ℓ₂' : Label} {e₁ e₂ : Expr} {s₁ s₂ : LStmt Label} {v₂ : Value}
      {S : RStack} :
      P.ctx ℓ₂ = some (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) → EvalExpr σ e₂ v₂ → IsTrue v₂ →
      ℓ₂' ≠ s₂.entry →
      BwdStep P ⟨σ, ℓ₂, ℓ₂', S⟩ ⟨σ, s₁.exit, ℓ₂, .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
  /-- Rule `Loop1⃖`. -/
  | loop1 {σ : Store} {ℓ' ℓ₁ ℓ₂ : Label} {e₂ : Expr} {s₁ s₂ : LStmt Label} {v₂ : Value}
      {S : RStack} :
      P.block ℓ₂ = some (.cond e₂) → EvalExpr σ e₂ v₂ → IsFalse v₂ →
      BwdStep P ⟨σ, ℓ₂, ℓ', .loop2 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
        ⟨σ, s₁.exit, ℓ₂, .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
  /-- Rule `Loop2⃖`. -/
  | loop2 {σ : Store} {ℓ' ℓ₁ ℓ₂ : Label} {e₁ : Expr} {s₁ s₂ : LStmt Label} {v₁ : Value}
      {S : RStack} :
      P.block ℓ₁ = some (.cond e₁) → EvalExpr σ e₁ v₁ → IsFalse v₁ →
      BwdStep P ⟨σ, ℓ₁, ℓ', .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
        ⟨σ, s₂.exit, ℓ₁, .loop2 ℓ₁ s₁ ℓ₂ s₂ :: S⟩

/-- The reflexive and transitive closure of the backward transition relation. -/
abbrev BwdSteps (P : LProgram Label) : RConfig → RConfig → Prop :=
  Relation.ReflTransGen (BwdStep P)

/-- `⇌ = ⇀ ∪ ↽`: a forward or a backward step. -/
def RevStep (P : LProgram Label) (k k' : RConfig) : Prop := FwdStep P k k' ∨ BwdStep P k k'

/-- **Definition (reachable configuration).** A configuration `⟨σ, ℓ₁', ℓ₂', S⟩` is
reachable if `⟨ε, ℓ₁, ℓ₂, []⟩ ⇌* ⟨σ, ℓ₁', ℓ₂', S⟩` for some labels `ℓ₁, ℓ₂` with
`(ℓ₁, ℓ₂) ∈ flow(p)`. -/
def LProgram.Reachable (P : LProgram Label) (k : RConfig) : Prop :=
  ∃ ℓ₁ ℓ₂, (ℓ₁, ℓ₂) ∈ P.flow ∧ Relation.ReflTransGen (RevStep P) ⟨Store.empty, ℓ₁, ℓ₂, []⟩ k

end Janus

end
