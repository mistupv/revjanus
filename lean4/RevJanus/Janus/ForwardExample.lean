module

public import RevJanus.Janus.ForwardProgram
public import RevJanus.Janus.CFGExample

/-!
# Janus: the forward derivation of Example "forward_trace"

We check the forward derivation of Figure "Forward derivation with the reversible semantics"
for the program Sum3 (Figure "Sum3", formalized in `RevJanus.Janus.CFGExample`):
each of the 22 transitions of the figure is a transition of the forward rules
(`step01`, …, `step22`), so that
`⟨ε, 1, 2, []⟩ ⇀* ⟨{n ↦ 6, i ↦ 3, total ↦ 3}, 3, 4, []⟩` (`forward_trace`), where `4` is the
label of the final `stop` of the main program. By Lemma "forward-rev", the small-step
semantics of Sum3 terminates in the same store (`smallSteps`).
-/

@[expose] public section

namespace Janus

namespace Sum3

/-- The labeled version of Sum3. -/
abbrev P : LProgram Label := program.toLabeled

/-- The body `s₁ = if [(i % 3) = 0]⁸ then [total += i]⁹ else [skip]¹⁰ fi [(i % 3) = 0]¹¹` of
the loop. -/
def s₁ : LStmt Label := .ite cond3 8 (.assVar "total" .add (.var "i") 9) (.skip 10) cond3 11

/-- The statement `s₂ = [i += 1]¹²` of the loop. -/
def s₂ : LStmt Label := .assVar "i" .add (.const 1) 12

/-- `{n ↦ 3}` -/
def σ₁ : Store := Store.empty.update (.var "n") 3
/-- `{n ↦ 3, i ↦ 1}` -/
def σ₂ : Store := σ₁.update (.var "i") 1
/-- `{n ↦ 3, i ↦ 2}` -/
def σ₃ : Store := σ₂.update (.var "i") 2
/-- `{n ↦ 3, i ↦ 3}` -/
def σ₄ : Store := σ₃.update (.var "i") 3
/-- `{n ↦ 3, i ↦ 3, total ↦ 3}` -/
def σ₅ : Store := σ₄.update (.var "total") 3
/-- `{n ↦ 6, i ↦ 3, total ↦ 3}` -/
def σ₆ : Store := σ₅.update (.var "n") 6

/-- Rule `AssVar⃗`, with the resulting store given explicitly. -/
theorem fwd_assVar {σ σ' : Store} {ℓ ℓ' ℓ'' : Label} {x : Var} {op : ModOp} {e : Expr}
    {v : Value} {S : RStack} (hb : P.block ℓ' = some (.assVar x op e))
    (he : e.eval σ = some v) (hf : (ℓ', ℓ'') ∈ P.flow)
    (hσ : σ.update (.var x) (op.interp (σ (.var x)) v) = σ') :
    FwdStep P ⟨σ, ℓ, ℓ', S⟩ ⟨σ', ℓ', ℓ'', S⟩ :=
  hσ ▸ .assVar hb (evalExpr_iff_eval.2 he) hf

theorem step01 : FwdStep P ⟨Store.empty, 1, 2, []⟩ ⟨σ₁, 2, 3, []⟩ :=
  fwd_assVar (x := "n") (op := .add) (e := .const 3) (v := 3) (by decide) rfl (by decide) rfl

theorem step02 : FwdStep P ⟨σ₁, 2, 3, []⟩ ⟨σ₁, 5, 6, [.call 3]⟩ :=
  .call (id := "sumMul3") (b := labeledSumMul3) (by decide) (by decide) (by decide)

theorem step03 : FwdStep P ⟨σ₁, 5, 6, [.call 3]⟩ ⟨σ₂, 6, 7, [.call 3]⟩ :=
  fwd_assVar (x := "i") (op := .add) (e := .const 1) (v := 1) (by decide) rfl (by decide) rfl

theorem step04 : FwdStep P ⟨σ₂, 6, 7, [.call 3]⟩
    ⟨σ₂, 7, 8, [.loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .loopMain (e₁ := condEntry) (e₂ := condExit) (s₁ := s₁) (s₂ := s₂) (v₁ := 1) (by decide) (evalExpr_iff_eval.2 rfl) (by decide) (by decide)

theorem step05 : FwdStep P ⟨σ₂, 7, 8, [.loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₂, 8, 10, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .ifFalse1 (e₁ := cond3) (e₂ := cond3) (s₁ := .assVar "total" .add (.var "i") 9)
    (s₂ := .skip 10) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem step06 : FwdStep P ⟨σ₂, 8, 10, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₂, 10, 11, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .skip (by decide) (by decide)

theorem step07 : FwdStep P ⟨σ₂, 10, 11, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₂, 11, 13, [.loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .ifFalse2 (e₂ := cond3) (v₂ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl (by decide)

theorem step08 : FwdStep P ⟨σ₂, 11, 13, [.loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₂, 13, 12, [.loop2 7 s₁ 13 s₂, .call 3]⟩ :=
  .loop1 (e₂ := condExit) (v₂ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem step09 : FwdStep P ⟨σ₂, 13, 12, [.loop2 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₃, 12, 7, [.loop2 7 s₁ 13 s₂, .call 3]⟩ :=
  fwd_assVar (x := "i") (op := .add) (e := .const 1) (v := 1) (by decide) rfl (by decide) rfl

theorem step10 : FwdStep P ⟨σ₃, 12, 7, [.loop2 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₃, 7, 8, [.loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .loop2 (e₁ := condEntry) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem step11 : FwdStep P ⟨σ₃, 7, 8, [.loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₃, 8, 10, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .ifFalse1 (e₁ := cond3) (e₂ := cond3) (s₁ := .assVar "total" .add (.var "i") 9)
    (s₂ := .skip 10) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem step12 : FwdStep P ⟨σ₃, 8, 10, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₃, 10, 11, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .skip (by decide) (by decide)

theorem step13 : FwdStep P ⟨σ₃, 10, 11, [.ifFalse 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₃, 11, 13, [.loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .ifFalse2 (e₂ := cond3) (v₂ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl (by decide)

theorem step14 : FwdStep P ⟨σ₃, 11, 13, [.loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₃, 13, 12, [.loop2 7 s₁ 13 s₂, .call 3]⟩ :=
  .loop1 (e₂ := condExit) (v₂ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem step15 : FwdStep P ⟨σ₃, 13, 12, [.loop2 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₄, 12, 7, [.loop2 7 s₁ 13 s₂, .call 3]⟩ :=
  fwd_assVar (x := "i") (op := .add) (e := .const 1) (v := 1) (by decide) rfl (by decide) rfl

theorem step16 : FwdStep P ⟨σ₄, 12, 7, [.loop2 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₄, 7, 8, [.loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .loop2 (e₁ := condEntry) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem step17 : FwdStep P ⟨σ₄, 7, 8, [.loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₄, 8, 9, [.ifTrue 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .ifTrue1 (e₁ := cond3) (e₂ := cond3) (s₁ := .assVar "total" .add (.var "i") 9)
    (s₂ := .skip 10) (v₁ := 1) (by decide) (evalExpr_iff_eval.2 rfl) (by decide)

theorem step18 : FwdStep P ⟨σ₄, 8, 9, [.ifTrue 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₅, 9, 11, [.ifTrue 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  fwd_assVar (x := "total") (op := .add) (e := .var "i") (v := 3) (by decide) rfl (by decide) rfl

theorem step19 : FwdStep P ⟨σ₅, 9, 11, [.ifTrue 8 11, .loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₅, 11, 13, [.loop1 7 s₁ 13 s₂, .call 3]⟩ :=
  .ifTrue2 (e₂ := cond3) (v₂ := 1) (by decide) (evalExpr_iff_eval.2 rfl) (by decide) (by decide)

theorem step20 : FwdStep P ⟨σ₅, 11, 13, [.loop1 7 s₁ 13 s₂, .call 3]⟩
    ⟨σ₅, 13, 14, [.call 3]⟩ :=
  .loopBase (e₂ := condExit) (v₂ := 1) (by decide) (evalExpr_iff_eval.2 rfl) (by decide) (by decide)
    (by decide)

theorem step21 : FwdStep P ⟨σ₅, 13, 14, [.call 3]⟩ ⟨σ₆, 14, 15, [.call 3]⟩ :=
  fwd_assVar (x := "n") (op := .add) (e := .var "total") (v := 3) (by decide) rfl (by decide) rfl

theorem step22 : FwdStep P ⟨σ₆, 14, 15, [.call 3]⟩ ⟨σ₆, 3, 4, []⟩ :=
  .return1 (by decide) (by decide)

/-- The forward derivation of Figure "Forward derivation with the reversible semantics". -/
theorem forward_trace : FwdSteps P ⟨Store.empty, 1, 2, []⟩ ⟨σ₆, 3, 4, []⟩ :=
  .head step01 <| .head step02 <| .head step03 <| .head step04 <| .head step05 <|
  .head step06 <| .head step07 <| .head step08 <| .head step09 <| .head step10 <|
  .head step11 <| .head step12 <| .head step13 <| .head step14 <| .head step15 <|
  .head step16 <| .head step17 <| .head step18 <| .head step19 <| .head step20 <|
  .head step21 <| .single step22

/-- `⟨ε, 1, 2, []⟩` is an initial configuration of Sum3. -/
theorem isInitial : P.IsInitial ⟨Store.empty, 1, 2, []⟩ := by
  refine ⟨rfl, ?_, ?_, rfl⟩ <;> decide

/-- The final store is `{n ↦ 6, i ↦ 3, total ↦ 3}`, and label `4` is the final `stop`. -/
theorem final_store : σ₆ (.var "n") = 6 ∧ σ₆ (.var "i") = 3 ∧ σ₆ (.var "total") = 3 ∧
    P.block 4 = some .stop := by
  refine ⟨rfl, rfl, rfl, by decide⟩

/-- By Lemma "forward-rev", the small-step semantics of Sum3 also terminates in store
`{n ↦ 6, i ↦ 3, total ↦ 3}`. -/
theorem smallSteps : SmallSteps program.procEnv ⟨Store.empty, program.main, []⟩
    ⟨σ₆, .skip, []⟩ :=
  (program.smallSteps_iff_fwdSteps_of_isInitial isInitial σ₆).2
    ⟨3, 4, forward_trace, final_store.2.2.2⟩

end Sum3

end Janus

end
