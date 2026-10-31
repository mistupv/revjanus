module

public import RevJanus.Janus.Semantics

/-!
# Janus: small-step semantics

This file formalizes Section "A Small-Step Semantics for Janus" of the paper:

* stack items `seq(s₂)`, `if_true(e₂)`, `if_false(e₂)`, `loop1(e₁,s₁,e₂,s₂)`,
  `loop2(e₁,s₁,e₂,s₂)` (`StackItem`) and stacks (`Stack`);
* configurations `⟨σ, s, S⟩` (`SSConfig`), and initial configurations `⟨ε, s, []⟩`;
* the transition relation `⟨σ, s, S⟩ → ⟨σ', s', S'⟩` (`SmallStep`), with the rules of
  Figure "Small-step semantics: rules for basic constructs" (`AssVarS`, `AssArrS`, `CallS`,
  `UnCallS`, `Seq1`, `Seq2`) and Figure "Small-step semantics: rules for if and for loop"
  (`IfTrue1`, `IfTrue2`, `IfFalse1`, `IfFalse2`, `LoopMainS`, `LoopBaseS`, `Loop1`, `Loop2`);
* its reflexive and transitive closure `→*` (`SmallSteps`);
* balanced derivations (`Balanced`) and loop derivations (`LoopDerivation`).

## Modelling choices

* The sequence stack item `seq(s₂)` carries the statement `s₂` still to be executed.
* As in the big-step semantics, `Γ` is a partial map; rules `CallS` and `UnCallS` only apply
  to declared procedures.
* A stack `S'` *extends* a stack `S` when `S` is a suffix of `S'` (items are pushed on the
  front of the list), written `S <:+ S'`.
* A derivation is a `Relation.ReflTransGen` chain. "Every intermediate stack is equal to or
  extends the initial one" is captured by restricting the closure to steps whose target
  configuration satisfies the condition (the source of the first step is the initial
  configuration itself). For loop derivations, the final configuration (whose stack is `S`)
  is not intermediate, so the last step is kept outside of the restricted chain.
-/

@[expose] public section

namespace Janus

/-- Items of the small-step stack. -/
inductive StackItem where
  /-- `seq(s₂)`: the second statement of a sequence, still to be executed. -/
  | seq (s₂ : Stmt)
  /-- `if_true(e₂)`: the exit assertion of a conditional whose then-branch is running. -/
  | ifTrue (e₂ : Expr)
  /-- `if_false(e₂)`: the exit assertion of a conditional whose else-branch is running. -/
  | ifFalse (e₂ : Expr)
  /-- `loop1(e₁,s₁,e₂,s₂)`: the loop body `s₁` of `from e₁ do s₁ loop s₂ until e₂` is
  running. -/
  | loop1 (e₁ : Expr) (s₁ : Stmt) (e₂ : Expr) (s₂ : Stmt)
  /-- `loop2(e₁,s₁,e₂,s₂)`: the statement `s₂` of `from e₁ do s₁ loop s₂ until e₂` is
  running. -/
  | loop2 (e₁ : Expr) (s₁ : Stmt) (e₂ : Expr) (s₂ : Stmt)
  deriving DecidableEq, Repr

/-- Stacks: lists of stack items, the head being the top of the stack. -/
abbrev Stack := List StackItem

/-- Configurations `⟨σ, s, S⟩` of the small-step semantics: a global store, a statement
(the control) and a stack. -/
structure SSConfig where
  /-- The global store `σ`. -/
  store : Store
  /-- The control `s`. -/
  control : Stmt
  /-- The stack `S`. -/
  stack : Stack

/-- The initial configuration `⟨ε, s, []⟩` of a program `p = (s p₁ … pₙ)`. -/
def Program.initConfig (p : Program) : SSConfig := ⟨Store.empty, p.main, []⟩

/-- The transition relation `⟨σ, s, S⟩ → ⟨σ', s', S'⟩` of the small-step semantics
(relative to the procedure environment `Γ`). -/
inductive SmallStep (Γ : ProcEnv) : SSConfig → SSConfig → Prop where
  /-- Rule `AssVarS`. -/
  | assVarS {σ : Store} {x : Var} {op : ModOp} {e : Expr} {v : Value} {S : Stack} :
      EvalExpr σ e v →
      SmallStep Γ ⟨σ, .assVar x op e, S⟩
        ⟨σ.update (.var x) (op.interp (σ (.var x)) v), .skip, S⟩
  /-- Rule `AssArrS`. -/
  | assArrS {σ : Store} {x : Var} {eₗ : Expr} {op : ModOp} {e : Expr} {vₗ v : Value}
      {S : Stack} :
      EvalExpr σ eₗ vₗ → EvalExpr σ e v →
      SmallStep Γ ⟨σ, .assArr x eₗ op e, S⟩
        ⟨σ.update (.elem x vₗ) (op.interp (σ (.elem x vₗ)) v), .skip, S⟩
  /-- Rule `CallS`: `⟨σ, call id, S⟩ → ⟨σ, Γ(id), S⟩`. -/
  | callS {σ : Store} {id : ProcId} {s : Stmt} {S : Stack} :
      Γ id = some s →
      SmallStep Γ ⟨σ, .call id, S⟩ ⟨σ, s, S⟩
  /-- Rule `UnCallS`: `⟨σ, uncall id, S⟩ → ⟨σ, 𝓘⟦Γ(id)⟧, S⟩`. -/
  | uncallS {σ : Store} {id : ProcId} {s : Stmt} {S : Stack} :
      Γ id = some s →
      SmallStep Γ ⟨σ, .uncall id, S⟩ ⟨σ, s.invert, S⟩
  /-- Rule `Seq1`: `⟨σ, s₁ s₂, S⟩ → ⟨σ, s₁, seq(s₂) : S⟩`. -/
  | seq1 {σ : Store} {s₁ s₂ : Stmt} {S : Stack} :
      SmallStep Γ ⟨σ, .seq s₁ s₂, S⟩ ⟨σ, s₁, .seq s₂ :: S⟩
  /-- Rule `Seq2`: `⟨σ, skip, seq(s₂) : S⟩ → ⟨σ, s₂, S⟩`. -/
  | seq2 {σ : Store} {s₂ : Stmt} {S : Stack} :
      SmallStep Γ ⟨σ, .skip, .seq s₂ :: S⟩ ⟨σ, s₂, S⟩
  /-- Rule `IfTrue1`. -/
  | ifTrue1 {σ : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ : Value} {S : Stack} :
      EvalExpr σ e₁ v₁ → IsTrue v₁ →
      SmallStep Γ ⟨σ, .ite e₁ s₁ s₂ e₂, S⟩ ⟨σ, s₁, .ifTrue e₂ :: S⟩
  /-- Rule `IfTrue2`. -/
  | ifTrue2 {σ : Store} {e₂ : Expr} {v₂ : Value} {S : Stack} :
      EvalExpr σ e₂ v₂ → IsTrue v₂ →
      SmallStep Γ ⟨σ, .skip, .ifTrue e₂ :: S⟩ ⟨σ, .skip, S⟩
  /-- Rule `IfFalse1`. -/
  | ifFalse1 {σ : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ : Value} {S : Stack} :
      EvalExpr σ e₁ v₁ → IsFalse v₁ →
      SmallStep Γ ⟨σ, .ite e₁ s₁ s₂ e₂, S⟩ ⟨σ, s₂, .ifFalse e₂ :: S⟩
  /-- Rule `IfFalse2`. -/
  | ifFalse2 {σ : Store} {e₂ : Expr} {v₂ : Value} {S : Stack} :
      EvalExpr σ e₂ v₂ → IsFalse v₂ →
      SmallStep Γ ⟨σ, .skip, .ifFalse e₂ :: S⟩ ⟨σ, .skip, S⟩
  /-- Rule `LoopMainS`. -/
  | loopMainS {σ : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ : Value} {S : Stack} :
      EvalExpr σ e₁ v₁ → IsTrue v₁ →
      SmallStep Γ ⟨σ, .loop e₁ s₁ s₂ e₂, S⟩ ⟨σ, s₁, .loop1 e₁ s₁ e₂ s₂ :: S⟩
  /-- Rule `LoopBaseS`. -/
  | loopBaseS {σ : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₂ : Value} {S : Stack} :
      EvalExpr σ e₂ v₂ → IsTrue v₂ →
      SmallStep Γ ⟨σ, .skip, .loop1 e₁ s₁ e₂ s₂ :: S⟩ ⟨σ, .skip, S⟩
  /-- Rule `Loop1`. -/
  | loop1 {σ : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₂ : Value} {S : Stack} :
      EvalExpr σ e₂ v₂ → IsFalse v₂ →
      SmallStep Γ ⟨σ, .skip, .loop1 e₁ s₁ e₂ s₂ :: S⟩ ⟨σ, s₂, .loop2 e₁ s₁ e₂ s₂ :: S⟩
  /-- Rule `Loop2`. -/
  | loop2 {σ : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt} {v₁ : Value} {S : Stack} :
      EvalExpr σ e₁ v₁ → IsFalse v₁ →
      SmallStep Γ ⟨σ, .skip, .loop2 e₁ s₁ e₂ s₂ :: S⟩ ⟨σ, s₁, .loop1 e₁ s₁ e₂ s₂ :: S⟩

/-- `→*`: the reflexive and transitive closure of the transition relation. -/
abbrev SmallSteps (Γ : ProcEnv) : SSConfig → SSConfig → Prop :=
  Relation.ReflTransGen (SmallStep Γ)

/-- Transitions whose target stack satisfies the predicate `P` (used to express conditions
on all intermediate stacks of a derivation). -/
def SmallStepWithin (Γ : ProcEnv) (P : Stack → Prop) (c c' : SSConfig) : Prop :=
  SmallStep Γ c c' ∧ P c'.stack

/-- A balanced derivation `⟨σ, s, S⟩ →* ⟨σ', s', S'⟩`: `S = S'` and every intermediate
stack is equal to or extends the initial one `S`. -/
def Balanced (Γ : ProcEnv) (c c' : SSConfig) : Prop :=
  c.stack = c'.stack ∧
    Relation.ReflTransGen (SmallStepWithin Γ (fun S' => c.stack <:+ S')) c c'

/-- A loop derivation `⟨σ, skip, loop1(e₁,s₁,e₂,s₂) : S⟩ →* ⟨σ', skip, S⟩`: every
intermediate stack is equal to or extends `loop1(e₁,s₁,e₂,s₂) : S` or
`loop2(e₁,s₁,e₂,s₂) : S`. -/
def LoopDerivation (Γ : ProcEnv) (σ : Store) (e₁ : Expr) (s₁ : Stmt) (e₂ : Expr) (s₂ : Stmt)
    (S : Stack) (σ' : Store) : Prop :=
  ∃ c, Relation.ReflTransGen
      (SmallStepWithin Γ (fun S' => .loop1 e₁ s₁ e₂ s₂ :: S <:+ S' ∨
        .loop2 e₁ s₁ e₂ s₂ :: S <:+ S'))
      ⟨σ, .skip, .loop1 e₁ s₁ e₂ s₂ :: S⟩ c ∧
    SmallStep Γ c ⟨σ', .skip, S⟩

end Janus

end
