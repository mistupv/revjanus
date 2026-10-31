module

public import RequestProject.Janus.CFG
public import RequestProject.Janus.Semantics

/-!
# Janus: the forward rules of the reversible semantics (Section "The Forward Rules")

This file formalizes the definitions of Subsection "The Forward Rules":

* the CFG `flow(p)` of a labeled program (union of the CFGs of the main program and of every
  procedure and inverse procedure): `LProgram.flow`; and the procedure environment `Γ` of a
  labeled program, mapping `id` and `id⁻¹` to the (labeled) bodies: `LProgram.proc`;
* stack items `call(ℓ)`, `uncall(ℓ)`, `if_true(ℓ₁,ℓ₂)`, `if_false(ℓ₁,ℓ₂)`,
  `loop1(ℓ₁,s₁,ℓ₂,s₂)`, `loop2(ℓ₁,s₁,ℓ₂,s₂)` (`RStackItem`) and configurations
  `⟨σ, ℓ, ℓ', S⟩` (`RConfig`);
* the forward transition relation `⇀` (`FwdStep`), with the rules of Figure "Reversible
  forward semantics: rules for basic constructs" (`AssVar`, `AssArr`, `Call`, `Return1`,
  `UnCall`, `Return2`, `Skip`) and of Figure "Reversible forward semantics: rules for if and
  for loop" (`IfTrue1`, `IfTrue2`, `IfFalse1`, `IfFalse2`, `LoopMain`, `LoopBase`, `Loop1`,
  `Loop2`), and its reflexive–transitive closure `⇀*` (`FwdSteps`);
* initial configurations `⟨ε, entry(s), ℓ, []⟩` with `entry(s) ⟶ ℓ` in the CFG of the main
  program (`LProgram.IsInitial`).

The auxiliary notions used in the proof of Lemma "forward-rev" (the continuation `next(t)`,
Lemma "cfg-next", the relation `π ∼stack^{ℓₙ,ℓₑ} π'` and the relation `∼conf`) are formalized
in `RequestProject.Janus.ForwardPaper`.

## Modelling choices

* `ℓ ⟶ ℓ'` in the rules is membership of the edge `(ℓ, ℓ')` in `flow(p)` (`LProgram.flow`).
* `Γ(id)` and `Γ(id⁻¹)` are `P.proc (.fwd id)` and `P.proc (.inv id)`; they are the labeled
  bodies, including `start` and `stop`. As in the other semantics, `Γ` is partial: the rules
  `Call` and `UnCall` only apply to declared procedures.
* The premise `block(ℓ) = o` is `P.block ℓ = some o`, and `ctx(ℓ) = t` is
  `P.ctx ℓ = some t` (so that the rule does not apply if `block`/`ctx` is undefined).
-/

@[expose] public section

namespace Janus

namespace LProgram

/-- `flow(p)`: the union of the CFGs of the main program and of every procedure and inverse
procedure of a labeled program. -/
def flow (P : LProgram Label) : Finset (Label × Label) :=
  P.bodies.foldr (fun b acc => b.flow ∪ acc) ∅

/-- The procedure environment `Γ` of a labeled program: `Γ(n)` is the body of the (first)
procedure named `n` (`n = id` or `n = id⁻¹`), if any. -/
def proc (P : LProgram Label) (n : PName) : Option (LStmt Label) :=
  (P.procs.find? (·.name = n)).map (·.body)

end LProgram

/-- Stack items of the reversible semantics. -/
inductive RStackItem where
  /-- `call(ℓ)`: return point of a procedure call labeled `ℓ`. -/
  | call (ℓ : Label)
  /-- `uncall(ℓ)`: return point of a procedure uncall labeled `ℓ`. -/
  | uncall (ℓ : Label)
  /-- `if_true(ℓ₁,ℓ₂)`: labels of the test and assertion of a conditional whose
  then-branch is running. -/
  | ifTrue (ℓ₁ ℓ₂ : Label)
  /-- `if_false(ℓ₁,ℓ₂)`: labels of the test and assertion of a conditional whose
  else-branch is running. -/
  | ifFalse (ℓ₁ ℓ₂ : Label)
  /-- `loop1(ℓ₁,s₁,ℓ₂,s₂)`: the body `s₁` of `from [e₁]^ℓ₁ do s₁ loop s₂ until [e₂]^ℓ₂` is
  running. -/
  | loop1 (ℓ₁ : Label) (s₁ : LStmt Label) (ℓ₂ : Label) (s₂ : LStmt Label)
  /-- `loop2(ℓ₁,s₁,ℓ₂,s₂)`: the statement `s₂` of `from [e₁]^ℓ₁ do s₁ loop s₂ until [e₂]^ℓ₂`
  is running. -/
  | loop2 (ℓ₁ : Label) (s₁ : LStmt Label) (ℓ₂ : Label) (s₂ : LStmt Label)
  deriving DecidableEq, Repr

/-- Stacks of the reversible semantics (the head is the top of the stack). -/
abbrev RStack := List RStackItem

/-- Configurations `⟨σ, ℓ, ℓ', S⟩` of the reversible semantics: a store, the label of the
last executed statement, the label of the next statement to be executed, and a stack. -/
structure RConfig where
  /-- The store `σ`. -/
  store : Store
  /-- The label `ℓ` of the last executed statement. -/
  last : Label
  /-- The label `ℓ'` of the next statement to be executed (the program counter). -/
  next : Label
  /-- The stack `S`. -/
  stack : RStack

/-- The forward transition relation `⟨σ, ℓ, ℓ', S⟩ ⇀ ⟨σ', ℓ'', ℓ''', S'⟩` of the reversible
semantics of a labeled program `P`. -/
inductive FwdStep (P : LProgram Label) : RConfig → RConfig → Prop where
  /-- Rule `AssVar⃗`. -/
  | assVar {σ : Store} {ℓ ℓ' ℓ'' : Label} {x : Var} {op : ModOp} {e : Expr} {v : Value}
      {S : RStack} :
      P.block ℓ' = some (.assVar x op e) → EvalExpr σ e v → (ℓ', ℓ'') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ', S⟩ ⟨σ.update (.var x) (op.interp (σ (.var x)) v), ℓ', ℓ'', S⟩
  /-- Rule `AssArr⃗`. -/
  | assArr {σ : Store} {ℓ ℓ' ℓ'' : Label} {x : Var} {eₗ : Expr} {op : ModOp} {e : Expr}
      {vₗ v : Value} {S : RStack} :
      P.block ℓ' = some (.assArr x eₗ op e) → EvalExpr σ eₗ vₗ → EvalExpr σ e v →
      (ℓ', ℓ'') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ', S⟩
        ⟨σ.update (.elem x vₗ) (op.interp (σ (.elem x vₗ)) v), ℓ', ℓ'', S⟩
  /-- Rule `Call⃗`. -/
  | call {σ : Store} {ℓ ℓ' ℓ'' : Label} {id : ProcId} {b : LStmt Label} {S : RStack} :
      P.block ℓ' = some (.call id) → P.proc (.fwd id) = some b → (b.entry, ℓ'') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ', S⟩ ⟨σ, b.entry, ℓ'', .call ℓ' :: S⟩
  /-- Rule `Return1⃗`. -/
  | return1 {σ : Store} {ℓ ℓ' ℓ'' ℓ''' : Label} {S : RStack} :
      P.block ℓ' = some .stop → (ℓ'', ℓ''') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ', .call ℓ'' :: S⟩ ⟨σ, ℓ'', ℓ''', S⟩
  /-- Rule `UnCall⃗`. -/
  | uncall {σ : Store} {ℓ ℓ' ℓ'' : Label} {id : ProcId} {b : LStmt Label} {S : RStack} :
      P.block ℓ' = some (.uncall id) → P.proc (.inv id) = some b → (b.entry, ℓ'') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ', S⟩ ⟨σ, b.entry, ℓ'', .uncall ℓ' :: S⟩
  /-- Rule `Return2⃗`. -/
  | return2 {σ : Store} {ℓ ℓ' ℓ'' ℓ''' : Label} {S : RStack} :
      P.block ℓ' = some .stop → (ℓ'', ℓ''') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ', .uncall ℓ'' :: S⟩ ⟨σ, ℓ'', ℓ''', S⟩
  /-- Rule `Skip⃗`. -/
  | skip {σ : Store} {ℓ ℓ' ℓ'' : Label} {S : RStack} :
      P.block ℓ' = some .skip → (ℓ', ℓ'') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ', S⟩ ⟨σ, ℓ', ℓ'', S⟩
  /-- Rule `IfTrue1⃗`. -/
  | ifTrue1 {σ : Store} {ℓ ℓ₁ ℓ₂ : Label} {e₁ e₂ : Expr} {s₁ s₂ : LStmt Label} {v₁ : Value}
      {S : RStack} :
      P.ctx ℓ₁ = some (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) → EvalExpr σ e₁ v₁ → IsTrue v₁ →
      FwdStep P ⟨σ, ℓ, ℓ₁, S⟩ ⟨σ, ℓ₁, s₁.entry, .ifTrue ℓ₁ ℓ₂ :: S⟩
  /-- Rule `IfTrue2⃗`. -/
  | ifTrue2 {σ : Store} {ℓ ℓ₁ ℓ₂ ℓ₂' : Label} {e₂ : Expr} {v₂ : Value} {S : RStack} :
      P.block ℓ₂ = some (.cond e₂) → EvalExpr σ e₂ v₂ → IsTrue v₂ → (ℓ₂, ℓ₂') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ₂, .ifTrue ℓ₁ ℓ₂ :: S⟩ ⟨σ, ℓ₂, ℓ₂', S⟩
  /-- Rule `IfFalse1⃗`. -/
  | ifFalse1 {σ : Store} {ℓ ℓ₁ ℓ₂ : Label} {e₁ e₂ : Expr} {s₁ s₂ : LStmt Label} {v₁ : Value}
      {S : RStack} :
      P.ctx ℓ₁ = some (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) → EvalExpr σ e₁ v₁ → IsFalse v₁ →
      FwdStep P ⟨σ, ℓ, ℓ₁, S⟩ ⟨σ, ℓ₁, s₂.entry, .ifFalse ℓ₁ ℓ₂ :: S⟩
  /-- Rule `IfFalse2⃗`. -/
  | ifFalse2 {σ : Store} {ℓ ℓ₁ ℓ₂ ℓ₂' : Label} {e₂ : Expr} {v₂ : Value} {S : RStack} :
      P.block ℓ₂ = some (.cond e₂) → EvalExpr σ e₂ v₂ → IsFalse v₂ → (ℓ₂, ℓ₂') ∈ P.flow →
      FwdStep P ⟨σ, ℓ, ℓ₂, .ifFalse ℓ₁ ℓ₂ :: S⟩ ⟨σ, ℓ₂, ℓ₂', S⟩
  /-- Rule `LoopMain⃗`. -/
  | loopMain {σ : Store} {ℓ ℓ₁ ℓ₂ : Label} {e₁ e₂ : Expr} {s₁ s₂ : LStmt Label} {v₁ : Value}
      {S : RStack} :
      P.ctx ℓ₁ = some (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) → EvalExpr σ e₁ v₁ → IsTrue v₁ →
      ℓ ≠ s₂.exit →
      FwdStep P ⟨σ, ℓ, ℓ₁, S⟩ ⟨σ, ℓ₁, s₁.entry, .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
  /-- Rule `LoopBase⃗`. -/
  | loopBase {σ : Store} {ℓ ℓ₁ ℓ₂ ℓ₂' : Label} {e₂ : Expr} {s₁ s₂ : LStmt Label} {v₂ : Value}
      {S : RStack} :
      P.block ℓ₂ = some (.cond e₂) → EvalExpr σ e₂ v₂ → IsTrue v₂ → (ℓ₂, ℓ₂') ∈ P.flow →
      ℓ₂' ≠ s₂.entry →
      FwdStep P ⟨σ, ℓ, ℓ₂, .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩ ⟨σ, ℓ₂, ℓ₂', S⟩
  /-- Rule `Loop1⃗`. -/
  | loop1 {σ : Store} {ℓ ℓ₁ ℓ₂ : Label} {e₂ : Expr} {s₁ s₂ : LStmt Label} {v₂ : Value}
      {S : RStack} :
      P.block ℓ₂ = some (.cond e₂) → EvalExpr σ e₂ v₂ → IsFalse v₂ →
      FwdStep P ⟨σ, ℓ, ℓ₂, .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
        ⟨σ, ℓ₂, s₂.entry, .loop2 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
  /-- Rule `Loop2⃗`. -/
  | loop2 {σ : Store} {ℓ ℓ₁ ℓ₂ : Label} {e₁ : Expr} {s₁ s₂ : LStmt Label} {v₁ : Value}
      {S : RStack} :
      P.block ℓ₁ = some (.cond e₁) → EvalExpr σ e₁ v₁ → IsFalse v₁ →
      FwdStep P ⟨σ, ℓ, ℓ₁, .loop2 ℓ₁ s₁ ℓ₂ s₂ :: S⟩
        ⟨σ, ℓ₁, s₁.entry, .loop1 ℓ₁ s₁ ℓ₂ s₂ :: S⟩

/-- `⇀*`: the reflexive and transitive closure of the forward transition relation. -/
abbrev FwdSteps (P : LProgram Label) : RConfig → RConfig → Prop :=
  Relation.ReflTransGen (FwdStep P)

/-- Initial configurations `⟨ε, entry(s), ℓ, []⟩` of a labeled program `p = (s p₁ … pₙ)`,
where `entry(s) ⟶ ℓ` belongs to the CFG of the main program. -/
def LProgram.IsInitial (P : LProgram Label) (k : RConfig) : Prop :=
  k.store = Store.empty ∧ k.last = P.main.entry ∧ (P.main.entry, k.next) ∈ P.mainCFG ∧
    k.stack = []

/-! ### Basic properties of `flow(p)` -/

theorem LProgram.mem_flow {P : LProgram Label} {x : Label × Label} :
    x ∈ P.flow ↔ ∃ b ∈ P.bodies, x ∈ b.flow := by
  unfold flow
  induction P.bodies with
  | nil => simp
  | cons b bs ih => simp [ih]

end Janus

end
