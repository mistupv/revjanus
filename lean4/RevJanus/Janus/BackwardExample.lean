module

public import RevJanus.Janus.LoopLemma
public import RevJanus.Janus.ForwardExample

/-!
# Janus: the backward derivation of Example "backward_trace"

Starting from the last configuration `⟨{n ↦ 6, i ↦ 3, total ↦ 3}, 3, 4, []⟩` of the forward
derivation of Example "forward_trace" (program Sum3), we check the backward derivation of
Figure "Backward derivation with the reversible semantics": each of its 22 transitions is a
transition of the backward rules (`bstep01`, …, `bstep22`), so that
`⟨{n ↦ 6, i ↦ 3, total ↦ 3}, 3, 4, []⟩ ↽* ⟨ε, 1, 2, []⟩` (`backward_trace`).

We also illustrate the loop lemma on this example: Sum3 is well formed, the configurations of
the derivations are reachable, and the first backward step is obtained from the last forward
step by the loop lemma (`bstep01_of_loop_lemma`).
-/

@[expose] public section

namespace Janus

namespace Sum3

/-- Rule `AssVar⃖`, with the resulting store given explicitly. -/
theorem bwd_assVar {σ σ' : Store} {ℓ ℓ' ℓ'' : Label} {x : Var} {op : ModOp} {e : Expr}
    {v : Value} {S : RStack} (hb : P.block ℓ' = some (.assVar x op e))
    (he : e.eval σ = some v) (hf : (ℓ, ℓ') ∈ P.flow)
    (hσ : σ.update (.var x) (op.invert.interp (σ (.var x)) v) = σ') :
    BwdStep P ⟨σ, ℓ', ℓ'', S⟩ ⟨σ', ℓ, ℓ', S⟩ :=
  hσ ▸ .assVar hb (evalExpr_iff_eval.2 he) (LProgram.mem_invFlow.2 hf)

/-- Proves an equation between explicit stores, pointwise. -/
local macro "store_eq" : tactic =>
  `(tactic| (funext l; simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, Store.empty, Function.update_apply,
    ModOp.invert, ModOp.interp]; all_goals (split_ifs <;> simp_all)))

/-- The loop stack items of the derivation. -/
abbrev L1 : RStackItem := .loop1 7 s₁ 13 s₂
/-- The loop stack items of the derivation. -/
abbrev L2 : RStackItem := .loop2 7 s₁ 13 s₂

theorem bstep01 : BwdStep P ⟨σ₆, 3, 4, []⟩ ⟨σ₆, 14, 15, [.call 3]⟩ :=
  .return1 (id := "sumMul3") (b := labeledSumMul3) (by decide) (by decide) (by decide)

theorem bstep02 : BwdStep P ⟨σ₆, 14, 15, [.call 3]⟩ ⟨σ₅, 13, 14, [.call 3]⟩ :=
  bwd_assVar (x := "n") (op := .add) (e := .var "total") (v := 3) (by decide) rfl (by decide)
    (by store_eq)

theorem bstep03 : BwdStep P ⟨σ₅, 13, 14, [.call 3]⟩ ⟨σ₅, 11, 13, [L1, .call 3]⟩ :=
  .loopBase (ℓ₁ := 7) (e₁ := condEntry) (s₁ := s₁) (s₂ := s₂) (e₂ := condExit) (v₂ := 1) (by decide) (evalExpr_iff_eval.2 rfl)
    (by decide) (by decide)

theorem bstep04 : BwdStep P ⟨σ₅, 11, 13, [L1, .call 3]⟩
    ⟨σ₅, 9, 11, [.ifTrue 8 11, L1, .call 3]⟩ :=
  .ifTrue2 (e₁ := cond3) (e₂ := cond3) (s₁ := .assVar "total" .add (.var "i") 9) (s₂ := .skip 10) (v₂ := 1)
    (by decide) (evalExpr_iff_eval.2 rfl) (by decide)

theorem bstep05 : BwdStep P ⟨σ₅, 9, 11, [.ifTrue 8 11, L1, .call 3]⟩
    ⟨σ₄, 8, 9, [.ifTrue 8 11, L1, .call 3]⟩ :=
  bwd_assVar (x := "total") (op := .add) (e := .var "i") (v := 3) (by decide) rfl (by decide)
    (by store_eq)

theorem bstep06 : BwdStep P ⟨σ₄, 8, 9, [.ifTrue 8 11, L1, .call 3]⟩ ⟨σ₄, 7, 8, [L1, .call 3]⟩ :=
  .ifTrue1 (e₁ := cond3) (v₁ := 1) (by decide) (evalExpr_iff_eval.2 rfl) (by decide)
    (by decide)

theorem bstep07 : BwdStep P ⟨σ₄, 7, 8, [L1, .call 3]⟩ ⟨σ₄, 12, 7, [L2, .call 3]⟩ :=
  .loop2 (e₁ := condEntry) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem bstep08 : BwdStep P ⟨σ₄, 12, 7, [L2, .call 3]⟩ ⟨σ₃, 13, 12, [L2, .call 3]⟩ :=
  bwd_assVar (x := "i") (op := .add) (e := .const 1) (v := 1) (by decide) rfl (by decide)
    (by store_eq)

theorem bstep09 : BwdStep P ⟨σ₃, 13, 12, [L2, .call 3]⟩ ⟨σ₃, 11, 13, [L1, .call 3]⟩ :=
  .loop1 (e₂ := condExit) (v₂ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem bstep10 : BwdStep P ⟨σ₃, 11, 13, [L1, .call 3]⟩
    ⟨σ₃, 10, 11, [.ifFalse 8 11, L1, .call 3]⟩ :=
  .ifFalse2 (e₁ := cond3) (e₂ := cond3) (s₁ := .assVar "total" .add (.var "i") 9) (s₂ := .skip 10) (v₂ := 0)
    (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem bstep11 : BwdStep P ⟨σ₃, 10, 11, [.ifFalse 8 11, L1, .call 3]⟩
    ⟨σ₃, 8, 10, [.ifFalse 8 11, L1, .call 3]⟩ :=
  .skip (by decide) (by decide)

theorem bstep12 : BwdStep P ⟨σ₃, 8, 10, [.ifFalse 8 11, L1, .call 3]⟩
    ⟨σ₃, 7, 8, [L1, .call 3]⟩ :=
  .ifFalse1 (e₁ := cond3) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl (by decide)

theorem bstep13 : BwdStep P ⟨σ₃, 7, 8, [L1, .call 3]⟩ ⟨σ₃, 12, 7, [L2, .call 3]⟩ :=
  .loop2 (e₁ := condEntry) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem bstep14 : BwdStep P ⟨σ₃, 12, 7, [L2, .call 3]⟩ ⟨σ₂, 13, 12, [L2, .call 3]⟩ :=
  bwd_assVar (x := "i") (op := .add) (e := .const 1) (v := 1) (by decide) rfl (by decide)
    (by store_eq)

theorem bstep15 : BwdStep P ⟨σ₂, 13, 12, [L2, .call 3]⟩ ⟨σ₂, 11, 13, [L1, .call 3]⟩ :=
  .loop1 (e₂ := condExit) (v₂ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem bstep16 : BwdStep P ⟨σ₂, 11, 13, [L1, .call 3]⟩
    ⟨σ₂, 10, 11, [.ifFalse 8 11, L1, .call 3]⟩ :=
  .ifFalse2 (e₁ := cond3) (e₂ := cond3) (s₁ := .assVar "total" .add (.var "i") 9) (s₂ := .skip 10) (v₂ := 0)
    (by decide) (evalExpr_iff_eval.2 rfl) rfl

theorem bstep17 : BwdStep P ⟨σ₂, 10, 11, [.ifFalse 8 11, L1, .call 3]⟩
    ⟨σ₂, 8, 10, [.ifFalse 8 11, L1, .call 3]⟩ :=
  .skip (by decide) (by decide)

theorem bstep18 : BwdStep P ⟨σ₂, 8, 10, [.ifFalse 8 11, L1, .call 3]⟩
    ⟨σ₂, 7, 8, [L1, .call 3]⟩ :=
  .ifFalse1 (e₁ := cond3) (v₁ := 0) (by decide) (evalExpr_iff_eval.2 rfl) rfl (by decide)

theorem bstep19 : BwdStep P ⟨σ₂, 7, 8, [L1, .call 3]⟩ ⟨σ₂, 6, 7, [.call 3]⟩ :=
  .loopMain (e₁ := condEntry) (v₁ := 1) (by decide) (evalExpr_iff_eval.2 rfl) (by decide)
    (by decide) (by decide)

theorem bstep20 : BwdStep P ⟨σ₂, 6, 7, [.call 3]⟩ ⟨σ₁, 5, 6, [.call 3]⟩ :=
  bwd_assVar (x := "i") (op := .add) (e := .const 1) (v := 1) (by decide) rfl (by decide)
    (by store_eq)

theorem bstep21 : BwdStep P ⟨σ₁, 5, 6, [.call 3]⟩ ⟨σ₁, 2, 3, []⟩ :=
  .call (by decide) (by decide)

theorem bstep22 : BwdStep P ⟨σ₁, 2, 3, []⟩ ⟨Store.empty, 1, 2, []⟩ :=
  bwd_assVar (x := "n") (op := .add) (e := .const 3) (v := 3) (by decide) rfl (by decide)
    (by store_eq)

/-- The backward derivation of Figure "Backward derivation with the reversible semantics",
starting from the last configuration of the forward derivation of Example
"forward_trace". -/
theorem backward_trace : BwdSteps P ⟨σ₆, 3, 4, []⟩ ⟨Store.empty, 1, 2, []⟩ :=
  .head bstep01 <| .head bstep02 <| .head bstep03 <| .head bstep04 <| .head bstep05 <|
  .head bstep06 <| .head bstep07 <| .head bstep08 <| .head bstep09 <| .head bstep10 <|
  .head bstep11 <| .head bstep12 <| .head bstep13 <| .head bstep14 <| .head bstep15 <|
  .head bstep16 <| .head bstep17 <| .head bstep18 <| .head bstep19 <| .head bstep20 <|
  .head bstep21 <| .single bstep22

/-- Sum3 is a well-formed program. -/
theorem wellFormed : program.WellFormed :=
  ⟨by decide, by simp only [program, List.mem_singleton, forall_eq]; decide, by decide⟩

/-- The last configuration of the forward derivation is reachable. -/
theorem reachable_final : P.Reachable ⟨σ₆, 3, 4, []⟩ :=
  ⟨1, 2, by decide, forward_trace.mono fun _ _ h => Or.inl h⟩

/-- The configuration `⟨{n ↦ 6, i ↦ 3, total ↦ 3}, 14, 15, [call(3)]⟩` is reachable. -/
theorem reachable_step21 : P.Reachable ⟨σ₆, 14, 15, [.call 3]⟩ :=
  ⟨1, 2, by decide, (Relation.ReflTransGen.head step01 <| .head step02 <| .head step03 <|
    .head step04 <| .head step05 <| .head step06 <| .head step07 <| .head step08 <|
    .head step09 <| .head step10 <| .head step11 <| .head step12 <| .head step13 <|
    .head step14 <| .head step15 <| .head step16 <| .head step17 <| .head step18 <|
    .head step19 <| .head step20 <| .single step21).mono fun _ _ h => Or.inl h⟩

/-- The loop lemma applied to the last forward step of Example "forward_trace" yields the
first backward step of Example "backward_trace". -/
theorem bstep01_of_loop_lemma : BwdStep P ⟨σ₆, 3, 4, []⟩ ⟨σ₆, 14, 15, [.call 3]⟩ :=
  (program.loop_lemma wellFormed reachable_step21 reachable_final).1 step22

end Sum3

end Janus

end
