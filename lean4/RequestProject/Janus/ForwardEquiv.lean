module

public import RequestProject.Janus.ForwardCFG
public import RequestProject.Janus.SmallStep

/-!
# Janus: equivalence between the small-step semantics and the forward rules

This file proves Lemma "forward-rev" of Subsection "The Forward Rules":

> Let `s` be a statement where `entry(s) ⟶ ℓ` belongs to the CFG. Then
> `⟨ε, s, []⟩ →* ⟨σ, skip, []⟩` iff there exist `ℓ'`, `ℓ''` such that
> `⟨ε, entry(s), ℓ, []⟩ ⇀* ⟨σ, ℓ', ℓ'', []⟩` with `block(ℓ'') = stop`.

As in the paper, the small-step semantics runs on the original program (without `start`
and `stop`, ignoring labels), while the forward rules run on its labeled version. The lemma
is proved for the labeled version `p.toLabeled` of any program `p`
(`Program.smallSteps_iff_fwdSteps`), as a consequence of a general version
(`smallSteps_iff_fwdSteps`) for any labeled program related to the original program by the
conditions `FwdWF` (unique labels, and bodies of the form `start s stop` that are labeled
versions of the original bodies).

## The proof

As in the paper, the proof is a simulation argument in both directions, with respect to a
relation between configurations `c` of the small-step semantics and configurations `k` of
the reversible semantics (`Corr`). `Corr` is the paper's relation `∼conf` (as revised): the
stack relation `StackCorr P S S' K E D` is the paper's `π ∼stack^{ℓₙ,ℓₑ} π'` of Figure
"eqstack" (with `K = ℓₙ` and `E = ℓₑ`), and the control relation `CtlCorr` gives the
paper's conditions (a) and (b), where the continuation `next(t) = K` is `OccK P t K`
(`RequestProject.Janus.ForwardCFG`). The only difference is that `StackCorr` and `CtlCorr`
also record a list `D` of labels (the labels of the statement whose execution is in
progress at the current level of the stack), which is used to prove the simulation steps.
This list is redundant: in `RequestProject.Janus.ForwardPaper`, the paper's relations are
formalized literally (`StackEquiv`, `ConfEquiv`), and it is proved that
`StackCorr P S S' K E D → StackEquiv P S S' K E`, `StackEquiv P S S' K E → ∃ D,
StackCorr P S S' K E D` and `Corr P c k ↔ ConfEquiv P c k`; the steps of the proof are then
restated with `∼conf` (`ConfEquiv.init`, `ConfEquiv.fwd_sim`, `ConfEquiv.back_sim`,
`ConfEquiv.final_fwd`, `ConfEquiv.final_back`, `ConfEquiv.smallSteps_iff_fwdSteps`).
-/

@[expose] public section

namespace Janus

variable {P : LProgram Label}

/-! ### Inversion of the forward rules according to the next block -/

namespace FwdStep

variable {σ : Store} {ℓ ℓ' : Label} {S : RStack} {k' : RConfig}

theorem cases_assVar (hP : P.UniqueLabels) {x : Var} {op : ModOp} {e : Expr}
    (hb : P.block ℓ' = some (.assVar x op e)) (h : FwdStep P ⟨σ, ℓ, ℓ', S⟩ k') :
    ∃ v ℓ'', EvalExpr σ e v ∧ (ℓ', ℓ'') ∈ P.flow ∧
      k' = ⟨σ.update (.var x) (op.interp (σ (.var x)) v), ℓ', ℓ'', S⟩ := by
  cases h with
  | assVar h1 h2 h3 => rw [hb] at h1; cases h1; exact ⟨_, _, h2, h3, rfl⟩
  | ifTrue1 h1 | ifFalse1 h1 | loopMain h1 =>
    obtain ⟨_, h⟩ := LProgram.block_of_ctx hP h1; simp_all
  | _ => simp_all

theorem cases_assArr (hP : P.UniqueLabels) {x : Var} {eₗ : Expr} {op : ModOp} {e : Expr}
    (hb : P.block ℓ' = some (.assArr x eₗ op e)) (h : FwdStep P ⟨σ, ℓ, ℓ', S⟩ k') :
    ∃ vₗ v ℓ'', EvalExpr σ eₗ vₗ ∧ EvalExpr σ e v ∧ (ℓ', ℓ'') ∈ P.flow ∧
      k' = ⟨σ.update (.elem x vₗ) (op.interp (σ (.elem x vₗ)) v), ℓ', ℓ'', S⟩ := by
  cases h with
  | assArr h1 h2 h3 h4 => rw [hb] at h1; cases h1; exact ⟨_, _, _, h2, h3, h4, rfl⟩
  | ifTrue1 h1 | ifFalse1 h1 | loopMain h1 =>
    obtain ⟨_, h⟩ := LProgram.block_of_ctx hP h1; simp_all
  | _ => simp_all

theorem cases_call (hP : P.UniqueLabels) {id : ProcId}
    (hb : P.block ℓ' = some (.call id)) (h : FwdStep P ⟨σ, ℓ, ℓ', S⟩ k') :
    ∃ b ℓ'', P.proc (.fwd id) = some b ∧ (b.entry, ℓ'') ∈ P.flow ∧
      k' = ⟨σ, b.entry, ℓ'', .call ℓ' :: S⟩ := by
  cases h with
  | call h1 h2 h3 => rw [hb] at h1; cases h1; exact ⟨_, _, h2, h3, rfl⟩
  | ifTrue1 h1 | ifFalse1 h1 | loopMain h1 =>
    obtain ⟨_, h⟩ := LProgram.block_of_ctx hP h1; simp_all
  | _ => simp_all

theorem cases_uncall (hP : P.UniqueLabels) {id : ProcId}
    (hb : P.block ℓ' = some (.uncall id)) (h : FwdStep P ⟨σ, ℓ, ℓ', S⟩ k') :
    ∃ b ℓ'', P.proc (.inv id) = some b ∧ (b.entry, ℓ'') ∈ P.flow ∧
      k' = ⟨σ, b.entry, ℓ'', .uncall ℓ' :: S⟩ := by
  cases h with
  | uncall h1 h2 h3 => rw [hb] at h1; cases h1; exact ⟨_, _, h2, h3, rfl⟩
  | ifTrue1 h1 | ifFalse1 h1 | loopMain h1 =>
    obtain ⟨_, h⟩ := LProgram.block_of_ctx hP h1; simp_all
  | _ => simp_all

theorem cases_skip (hP : P.UniqueLabels)
    (hb : P.block ℓ' = some .skip) (h : FwdStep P ⟨σ, ℓ, ℓ', S⟩ k') :
    ∃ ℓ'', (ℓ', ℓ'') ∈ P.flow ∧ k' = ⟨σ, ℓ', ℓ'', S⟩ := by
  cases h with
  | skip h1 h2 => exact ⟨_, h2, rfl⟩
  | ifTrue1 h1 | ifFalse1 h1 | loopMain h1 =>
    obtain ⟨_, h⟩ := LProgram.block_of_ctx hP h1; simp_all
  | _ => simp_all

theorem cases_stop (hP : P.UniqueLabels)
    (hb : P.block ℓ' = some .stop) (h : FwdStep P ⟨σ, ℓ, ℓ', S⟩ k') :
    (∃ ℓ'' ℓ''' S₀, S = .call ℓ'' :: S₀ ∧ (ℓ'', ℓ''') ∈ P.flow ∧ k' = ⟨σ, ℓ'', ℓ''', S₀⟩) ∨
    (∃ ℓ'' ℓ''' S₀, S = .uncall ℓ'' :: S₀ ∧ (ℓ'', ℓ''') ∈ P.flow ∧
      k' = ⟨σ, ℓ'', ℓ''', S₀⟩) := by
  cases h with
  | return1 h1 h2 => exact Or.inl ⟨_, _, _, rfl, h2, rfl⟩
  | return2 h1 h2 => exact Or.inr ⟨_, _, _, rfl, h2, rfl⟩
  | ifTrue1 h1 | ifFalse1 h1 | loopMain h1 =>
    obtain ⟨_, h⟩ := LProgram.block_of_ctx hP h1; simp_all
  | _ => simp_all

theorem cases_cond {e : Expr} (hb : P.block ℓ' = some (.cond e))
    (h : FwdStep P ⟨σ, ℓ, ℓ', S⟩ k') :
    (∃ e₁ s₁ s₂ e₂ ℓ₂ v₁, P.ctx ℓ' = some (.ite e₁ ℓ' s₁ s₂ e₂ ℓ₂) ∧ EvalExpr σ e₁ v₁ ∧
      IsTrue v₁ ∧ k' = ⟨σ, ℓ', s₁.entry, .ifTrue ℓ' ℓ₂ :: S⟩) ∨
    (∃ e₁ s₁ s₂ e₂ ℓ₂ v₁, P.ctx ℓ' = some (.ite e₁ ℓ' s₁ s₂ e₂ ℓ₂) ∧ EvalExpr σ e₁ v₁ ∧
      IsFalse v₁ ∧ k' = ⟨σ, ℓ', s₂.entry, .ifFalse ℓ' ℓ₂ :: S⟩) ∨
    (∃ e₁ s₁ s₂ e₂ ℓ₂ v₁, P.ctx ℓ' = some (.loop e₁ ℓ' s₁ s₂ e₂ ℓ₂) ∧ EvalExpr σ e₁ v₁ ∧
      IsTrue v₁ ∧ ℓ ≠ s₂.exit ∧ k' = ⟨σ, ℓ', s₁.entry, .loop1 ℓ' s₁ ℓ₂ s₂ :: S⟩) ∨
    (∃ ℓ₁ S₀ ℓ₂' v₂, S = .ifTrue ℓ₁ ℓ' :: S₀ ∧ EvalExpr σ e v₂ ∧ IsTrue v₂ ∧
      (ℓ', ℓ₂') ∈ P.flow ∧ k' = ⟨σ, ℓ', ℓ₂', S₀⟩) ∨
    (∃ ℓ₁ S₀ ℓ₂' v₂, S = .ifFalse ℓ₁ ℓ' :: S₀ ∧ EvalExpr σ e v₂ ∧ IsFalse v₂ ∧
      (ℓ', ℓ₂') ∈ P.flow ∧ k' = ⟨σ, ℓ', ℓ₂', S₀⟩) ∨
    (∃ ℓ₁ s₁ s₂ S₀ ℓ₂' v₂, S = .loop1 ℓ₁ s₁ ℓ' s₂ :: S₀ ∧ EvalExpr σ e v₂ ∧ IsTrue v₂ ∧
      (ℓ', ℓ₂') ∈ P.flow ∧ ℓ₂' ≠ s₂.entry ∧ k' = ⟨σ, ℓ', ℓ₂', S₀⟩) ∨
    (∃ ℓ₁ s₁ s₂ S₀ v₂, S = .loop1 ℓ₁ s₁ ℓ' s₂ :: S₀ ∧ EvalExpr σ e v₂ ∧ IsFalse v₂ ∧
      k' = ⟨σ, ℓ', s₂.entry, .loop2 ℓ₁ s₁ ℓ' s₂ :: S₀⟩) ∨
    (∃ s₁ ℓ₂ s₂ S₀ v₁, S = .loop2 ℓ' s₁ ℓ₂ s₂ :: S₀ ∧ EvalExpr σ e v₁ ∧ IsFalse v₁ ∧
      k' = ⟨σ, ℓ', s₁.entry, .loop1 ℓ' s₁ ℓ₂ s₂ :: S₀⟩) := by
  cases h with
  | ifTrue1 h1 h2 h3 => exact Or.inl ⟨_, _, _, _, _, _, h1, h2, h3, rfl⟩
  | ifFalse1 h1 h2 h3 => exact Or.inr (Or.inl ⟨_, _, _, _, _, _, h1, h2, h3, rfl⟩)
  | loopMain h1 h2 h3 h4 =>
    exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, h1, h2, h3, h4, rfl⟩))
  | ifTrue2 h1 h2 h3 h4 =>
    rw [hb] at h1; cases h1
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, h2, h3, h4, rfl⟩)))
  | ifFalse2 h1 h2 h3 h4 =>
    rw [hb] at h1; cases h1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, h2, h3, h4, rfl⟩))))
  | loopBase h1 h2 h3 h4 h5 =>
    rw [hb] at h1; cases h1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, _, _, _, _, _, rfl, h2, h3, h4, h5, rfl⟩)))))
  | loop1 h1 h2 h3 =>
    rw [hb] at h1; cases h1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, _, _, _, _, rfl, h2, h3, rfl⟩))))))
  | loop2 h1 h2 h3 =>
    rw [hb] at h1; cases h1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨_, _, _, _, _, rfl, h2, h3, rfl⟩))))))
  | _ => simp_all

end FwdStep

/-! ### Well-formed labeled programs -/

/-- The conditions relating a labeled program `P` (run by the forward rules) to the
procedure environment `Γ` and the main statement `main` of an original program (run by the
small-step semantics): labels are unique, the main body of `P` is `start m stop` where `m` is
a labeled version of `main`, the procedure `id` (resp. `id⁻¹`) is declared in `P` iff `id`
is declared in `Γ`, and its body is `start m stop` where `m` is a labeled version of
`Γ(id)` (resp. `𝓘⟦Γ(id)⟧`). -/
structure FwdWF (P : LProgram Label) (Γ : ProcEnv) (main : Stmt) : Prop where
  unique : P.UniqueLabels
  main_shape : ∃ a m z, BodyShape P.main a m z ∧ LRepr m main
  fwd_some : ∀ id s, Γ id = some s → ∃ b, P.proc (.fwd id) = some b
  fwd_body : ∀ id b, P.proc (.fwd id) = some b →
    ∃ s a m z, Γ id = some s ∧ BodyShape b a m z ∧ LRepr m s
  inv_some : ∀ id s, Γ id = some s → ∃ b, P.proc (.inv id) = some b
  inv_body : ∀ id b, P.proc (.inv id) = some b →
    ∃ s a m z, Γ id = some s ∧ BodyShape b a m z ∧ LRepr m s.invert

/-! ### The simulation relation -/

/-- `StackCorr P S S' K E D` relates a small-step stack `S` and a stack `S'` of the
reversible semantics. `K` is the label of the next block to be executed once the current
statement is completed, `E` is the label of the last executed block at that point, and `D`
contains the labels of the statement currently being executed. -/
inductive StackCorr (P : LProgram Label) : Stack → RStack → Label → Label → List Label → Prop
  | nil {a z : Label} {m : LStmt Label} :
      BodyShape P.main a m z → StackCorr P [] [] z m.exit m.labels
  | seq {t₁ t₂ : LStmt Label} {s₂ : Stmt} {K : Label} {S : Stack} {S' : RStack}
      {D : List Label} :
      OccK P (.seq t₁ t₂) K → LRepr t₂ s₂ → StackCorr P S S' K t₂.exit D →
      (LStmt.seq t₁ t₂).labels ⊆ D →
      StackCorr P (.seq s₂ :: S) S' t₂.entry t₁.exit t₁.labels
  | ifTrue {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {K : Label} {S : Stack}
      {S' : RStack} {D : List Label} :
      OccK P (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K → StackCorr P S S' K ℓ₂ D →
      (LStmt.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂).labels ⊆ D →
      StackCorr P (.ifTrue e₂ :: S) (.ifTrue ℓ₁ ℓ₂ :: S') ℓ₂ t₁.exit t₁.labels
  | ifFalse {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {K : Label} {S : Stack}
      {S' : RStack} {D : List Label} :
      OccK P (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K → StackCorr P S S' K ℓ₂ D →
      (LStmt.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂).labels ⊆ D →
      StackCorr P (.ifFalse e₂ :: S) (.ifFalse ℓ₁ ℓ₂ :: S') ℓ₂ t₂.exit t₂.labels
  | loop1 {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {s₁ s₂ : Stmt} {K : Label}
      {S : Stack} {S' : RStack} {D : List Label} :
      OccK P (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K → LRepr t₁ s₁ → LRepr t₂ s₂ →
      StackCorr P S S' K ℓ₂ D → (LStmt.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂).labels ⊆ D →
      StackCorr P (.loop1 e₁ s₁ e₂ s₂ :: S) (.loop1 ℓ₁ t₁ ℓ₂ t₂ :: S') ℓ₂ t₁.exit t₁.labels
  | loop2 {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {s₁ s₂ : Stmt} {K : Label}
      {S : Stack} {S' : RStack} {D : List Label} :
      OccK P (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K → LRepr t₁ s₁ → LRepr t₂ s₂ →
      StackCorr P S S' K ℓ₂ D → (LStmt.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂).labels ⊆ D →
      StackCorr P (.loop2 e₁ s₁ e₂ s₂ :: S) (.loop2 ℓ₁ t₁ ℓ₂ t₂ :: S') ℓ₁ t₂.exit t₂.labels
  | call {id : ProcId} {ℓc K a z : Label} {b m : LStmt Label} {S : Stack} {S' : RStack}
      {D : List Label} :
      OccK P (.call id ℓc) K → StackCorr P S S' K ℓc D → P.proc (.fwd id) = some b →
      BodyShape b a m z → StackCorr P S (.call ℓc :: S') z m.exit m.labels
  | uncall {id : ProcId} {ℓc K a z : Label} {b m : LStmt Label} {S : Stack} {S' : RStack}
      {D : List Label} :
      OccK P (.uncall id ℓc) K → StackCorr P S S' K ℓc D → P.proc (.inv id) = some b →
      BodyShape b a m z → StackCorr P S (.uncall ℓc :: S') z m.exit m.labels

/-- The control part of the simulation relation: either the small-step control `s` is about
to be executed and corresponds to a labeled statement `t` (whose entry is the next label
`ℓn`), or it is completed (`s = skip`) and the reversible configuration is at the
transition `(E, K)`. -/
def CtlCorr (P : LProgram Label) (s : Stmt) (ℓp ℓn K E : Label) (D : List Label) : Prop :=
  (∃ t, OccK P t K ∧ LRepr t s ∧ t.exit = E ∧ ℓn = t.entry ∧ ℓp ∉ t.labels ∧ t.labels ⊆ D) ∨
  (s = .skip ∧ ℓp = E ∧ ℓn = K)

/-- The simulation relation between configurations of the small-step semantics and
configurations of the reversible semantics. -/
def Corr (P : LProgram Label) (c : SSConfig) (k : RConfig) : Prop :=
  c.store = k.store ∧
    ∃ K E D, StackCorr P c.stack k.stack K E D ∧ CtlCorr P c.control k.last k.next K E D

/-- The label that may not occur in the current statement, given the top of the stack. -/
def RStack.guard : RStack → Option Label
  | .ifTrue _ ℓ₂ :: _ => some ℓ₂
  | .ifFalse _ ℓ₂ :: _ => some ℓ₂
  | .loop1 _ _ ℓ₂ _ :: _ => some ℓ₂
  | .loop2 ℓ₁ _ _ _ :: _ => some ℓ₁
  | _ => none

theorem StackCorr.guard_not_mem (hP : P.UniqueLabels) {S : Stack} {S' : RStack}
    {K E : Label} {D : List Label} (h : StackCorr P S S' K E D) {ℓ : Label}
    (hg : RStack.guard S' = some ℓ) : ℓ ∉ D := by
  induction h with
  | nil => simp [RStack.guard] at hg
  | seq _ _ _ hD ih =>
    intro hm; exact ih hg (hD (by rw [LStmt.labels_seq]; exact List.mem_append_left _ hm))
  | ifTrue hK _ _ _ =>
    simp only [RStack.guard, Option.some.injEq] at hg; subst hg
    have hn := hK.nodup hP; rw [LStmt.labels_ite] at hn
    exact (LStmt.nodup_cons_append3 hn).2.2.1
  | ifFalse hK _ _ _ =>
    simp only [RStack.guard, Option.some.injEq] at hg; subst hg
    have hn := hK.nodup hP; rw [LStmt.labels_ite] at hn
    exact (LStmt.nodup_cons_append3 hn).2.2.2.1
  | loop1 hK _ _ _ _ _ =>
    simp only [RStack.guard, Option.some.injEq] at hg; subst hg
    have hn := hK.nodup hP; rw [LStmt.labels_loop] at hn
    exact (LStmt.nodup_cons_append3 hn).2.2.1
  | loop2 hK _ _ _ _ _ =>
    simp only [RStack.guard, Option.some.injEq] at hg; subst hg
    have hn := hK.nodup hP; rw [LStmt.labels_loop] at hn
    exact (LStmt.nodup_cons_append3 hn).2.1
  | call => simp [RStack.guard] at hg
  | uncall => simp [RStack.guard] at hg

/-! ### Auxiliary facts -/

theorem OccK.not_mem_seq (hP : P.UniqueLabels) {t₁ t₂ : LStmt Label} {K : Label}
    (h : OccK P (.seq t₁ t₂) K) : t₁.exit ∉ t₂.labels := by
  have hn := h.nodup hP
  rw [LStmt.labels_seq, List.nodup_append] at hn
  exact fun h' => hn.2.2 _ (LStmt.exit_mem_labels _) _ h' rfl

theorem OccK.ite_facts (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {t₁ t₂ : LStmt Label} {K : Label} (h : OccK P (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K) :
    ℓ₁ ∉ t₁.labels ∧ ℓ₁ ∉ t₂.labels ∧ ℓ₂ ∉ t₁.labels ∧ ℓ₂ ∉ t₂.labels ∧ ℓ₁ ≠ ℓ₂ := by
  have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := LStmt.nodup_cons_append3 hn
  exact ⟨h1, h2, h3, h4, h5⟩

theorem OccK.loop_facts (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {t₁ t₂ : LStmt Label} {K : Label} (h : OccK P (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K) :
    ℓ₁ ∉ t₁.labels ∧ ℓ₁ ∉ t₂.labels ∧ ℓ₂ ∉ t₁.labels ∧ ℓ₂ ∉ t₂.labels ∧ ℓ₁ ≠ ℓ₂ := by
  have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := LStmt.nodup_cons_append3 hn
  exact ⟨h1, h2, h3, h4, h5⟩

theorem OccK.ctx_ite (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {t₁ t₂ : LStmt Label} {K : Label} (h : OccK P (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K) :
    P.ctx ℓ₁ = some (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) ∧ P.ctx ℓ₂ = some (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) :=
  LProgram.ctx_ite hP h.occurs

theorem OccK.ctx_loop (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {t₁ t₂ : LStmt Label} {K : Label} (h : OccK P (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K) :
    P.ctx ℓ₁ = some (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) ∧ P.ctx ℓ₂ = some (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) :=
  LProgram.ctx_loop hP h.occurs

theorem RTG.head {α : Type} {r : α → α → Prop} {a b c : α} (h : r a b)
    (h' : Relation.ReflTransGen r b c) : Relation.ReflTransGen r a c :=
  Relation.ReflTransGen.head h h'

variable {Γ : ProcEnv} {main : Stmt}

/-! ### From small-step to forward rules -/

/-- Simulation of a small-step transition from a completed control. -/
theorem fwd_B (hW : FwdWF P Γ main) {S : Stack} {S' : RStack} {K E : Label} {D : List Label}
    (hS : StackCorr P S S' K E D) {σ : Store} {c' : SSConfig}
    (hc : SmallStep Γ ⟨σ, .skip, S⟩ c') :
    ∃ k', FwdSteps P ⟨σ, E, K, S'⟩ k' ∧ Corr P c' k' := by
  have hP := hW.unique
  induction hS generalizing c' with
  | nil => cases hc
  | @seq t₁ t₂ s₂ K S S' D hK hr hS hD _ =>
    cases hc
    exact ⟨_, .refl, rfl, K, _, D, hS, Or.inl ⟨t₂, hK.seqR, hr, rfl, rfl, hK.not_mem_seq hP,
      fun x hx => hD (by rw [LStmt.labels_seq]; exact List.mem_append_right _ hx)⟩⟩
  | @ifTrue e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ K S S' D hK hS hD _ =>
    cases hc with
    | ifTrue2 he ht =>
      refine ⟨_, .single (.ifTrue2 (hK.block hP (by simp [LStmt.blocks])) he ht
        hK.exit_edge), rfl, K, ℓ₂, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | @ifFalse e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ K S S' D hK hS hD _ =>
    cases hc with
    | ifFalse2 he ht =>
      refine ⟨_, .single (.ifFalse2 (hK.block hP (by simp [LStmt.blocks])) he ht
        hK.exit_edge), rfl, K, ℓ₂, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | @loop1 e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ K S S' D hK hr₁ hr₂ hS hD _ =>
    obtain ⟨-, -, -, h4, -⟩ := hK.loop_facts hP
    cases hc with
    | loopBaseS he ht =>
      have hne : K ≠ t₂.entry := fun h => hK.not_mem hP (by
        rw [h, LStmt.labels_loop]; simp [LStmt.entry_mem_labels])
      exact ⟨_, .single (.loopBase (hK.block hP (by simp [LStmt.blocks])) he ht
        hK.exit_edge hne), rfl, K, ℓ₂, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
    | loop1 he hf =>
      exact ⟨_, .single (.loop1 (hK.block hP (by simp [LStmt.blocks])) he hf), rfl, _, _, _,
        .loop2 hK hr₁ hr₂ hS hD,
        Or.inl ⟨t₂, hK.loopR, hr₂, rfl, rfl, h4, List.Subset.refl _⟩⟩
  | @loop2 e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ K S S' D hK hr₁ hr₂ hS hD _ =>
    obtain ⟨h1, -, -, -, -⟩ := hK.loop_facts hP
    cases hc with
    | loop2 he hf =>
      exact ⟨_, .single (.loop2 (hK.block hP (by simp [LStmt.blocks])) he hf), rfl, _, _, _,
        .loop1 hK hr₁ hr₂ hS hD,
        Or.inl ⟨t₁, hK.loopL, hr₁, rfl, rfl, h1, List.Subset.refl _⟩⟩
  | @call id ℓc K a z b m S S' D hK hS hpb hs ih =>
    obtain ⟨k', h1, h2⟩ := ih hc
    exact ⟨k', RTG.head (.return1 (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb))
      hK.exit_edge) h1, h2⟩
  | @uncall id ℓc K a z b m S S' D hK hS hpb hs ih =>
    obtain ⟨k', h1, h2⟩ := ih hc
    exact ⟨k', RTG.head (.return2 (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb))
      hK.exit_edge) h1, h2⟩

/-- Simulation of a small-step transition from a control that is about to be executed. -/
theorem fwd_A (hW : FwdWF P Γ main) {t : LStmt Label} {s : Stmt} {K E ℓp : Label}
    {D : List Label} {S : Stack} {S' : RStack} {σ : Store} {c' : SSConfig}
    (hK : OccK P t K) (hr : LRepr t s) (hE : t.exit = E) (hp : ℓp ∉ t.labels)
    (hD : t.labels ⊆ D) (hS : StackCorr P S S' K E D) (hc : SmallStep Γ ⟨σ, s, S⟩ c') :
    ∃ k', FwdSteps P ⟨σ, ℓp, t.entry, S'⟩ k' ∧ Corr P c' k' := by
  have hP := hW.unique
  subst hE
  cases hr with
  | assVar =>
    cases hc with
    | assVarS he =>
      exact ⟨_, .single (.assVar (hK.block hP (by simp [LStmt.blocks, LStmt.entry])) he hK.exit_edge),
        rfl, K, _, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | assArr =>
    cases hc with
    | assArrS he₁ he₂ =>
      exact ⟨_, .single (.assArr (hK.block hP (by simp [LStmt.blocks, LStmt.entry])) he₁ he₂
        hK.exit_edge), rfl, K, _, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | @ite e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ hr₁ hr₂ =>
    obtain ⟨h1, h2, -, -, -⟩ := hK.ite_facts hP
    cases hc with
    | ifTrue1 he ht =>
      exact ⟨_, .single (.ifTrue1 (hK.ctx_ite hP).1 he ht), rfl, _, _, _,
        .ifTrue hK hS hD, Or.inl ⟨t₁, hK.iteL, hr₁, rfl, rfl, h1, List.Subset.refl _⟩⟩
    | ifFalse1 he hf =>
      exact ⟨_, .single (.ifFalse1 (hK.ctx_ite hP).1 he hf), rfl, _, _, _,
        .ifFalse hK hS hD, Or.inl ⟨t₂, hK.iteR, hr₂, rfl, rfl, h2, List.Subset.refl _⟩⟩
  | @loop e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ hr₁ hr₂ =>
    obtain ⟨h1, -, -, -, -⟩ := hK.loop_facts hP
    cases hc with
    | loopMainS he ht =>
      have hne : ℓp ≠ t₂.exit := fun h => hp (by
        rw [h, LStmt.labels_loop]; simp [LStmt.exit_mem_labels])
      exact ⟨_, .single (.loopMain (hK.ctx_loop hP).1 he ht hne), rfl, _, _, _,
        .loop1 hK hr₁ hr₂ hS hD, Or.inl ⟨t₁, hK.loopL, hr₁, rfl, rfl, h1, List.Subset.refl _⟩⟩
  | @call id ℓc =>
    cases hc with
    | callS hΓ =>
      obtain ⟨b, hpb⟩ := hW.fwd_some _ _ hΓ
      obtain ⟨s', a, m, z, hΓ', hs, hr'⟩ := hW.fwd_body _ _ hpb
      rw [hΓ] at hΓ'; cases hΓ'
      have hb := LProgram.mem_bodies_of_proc hpb
      refine ⟨_, .single (.call (hK.block hP (by simp [LStmt.blocks, LStmt.entry])) hpb
        (by rw [hs.entry_eq]; exact hs.start_edge hb)), rfl, _, _, _, .call hK hS hpb hs,
        Or.inl ⟨m, hs.occK hb, hr', rfl, rfl, ?_, List.Subset.refl _⟩⟩
      rw [hs.entry_eq]; exact hs.start_not_mem hP hb
  | @uncall id ℓc =>
    cases hc with
    | uncallS hΓ =>
      obtain ⟨b, hpb⟩ := hW.inv_some _ _ hΓ
      obtain ⟨s', a, m, z, hΓ', hs, hr'⟩ := hW.inv_body _ _ hpb
      rw [hΓ] at hΓ'; cases hΓ'
      have hb := LProgram.mem_bodies_of_proc hpb
      refine ⟨_, .single (.uncall (hK.block hP (by simp [LStmt.blocks, LStmt.entry])) hpb
        (by rw [hs.entry_eq]; exact hs.start_edge hb)), rfl, _, _, _, .uncall hK hS hpb hs,
        Or.inl ⟨m, hs.occK hb, hr', rfl, rfl, ?_, List.Subset.refl _⟩⟩
      rw [hs.entry_eq]; exact hs.start_not_mem hP hb
  | @skip ℓs =>
    obtain ⟨k', h1, h2⟩ := fwd_B hW hS hc
    exact ⟨k', RTG.head (.skip (hK.block hP (by simp [LStmt.blocks, LStmt.entry])) hK.exit_edge) h1, h2⟩
  | @seq t₁ t₂ s₁ s₂ hr₁ hr₂ =>
    cases hc with
    | seq1 =>
      exact ⟨_, .refl, rfl, _, _, _, .seq hK hr₂ hS hD,
        Or.inl ⟨t₁, hK.seqL, hr₁, rfl, rfl,
          fun h => hp (by rw [LStmt.labels_seq]; exact List.mem_append_left _ h),
          List.Subset.refl _⟩⟩

theorem fwd_sim (hW : FwdWF P Γ main) {c c' : SSConfig} {k : RConfig} (h : Corr P c k)
    (hc : SmallStep Γ c c') : ∃ k', FwdSteps P k k' ∧ Corr P c' k' := by
  obtain ⟨σ, s, S⟩ := c
  obtain ⟨σ', ℓp, ℓn, S'⟩ := k
  obtain ⟨hσ, K, E, D, hS, hctl⟩ := h
  simp only at hσ hS hctl; subst hσ
  rcases hctl with ⟨t, hK, hr, hE, rfl, hp, hD⟩ | ⟨rfl, rfl, rfl⟩
  · exact fwd_A hW hK hr hE hp hD hS hc
  · exact fwd_B hW hS hc

theorem fwd_sims (hW : FwdWF P Γ main) {c c' : SSConfig} {k : RConfig} (h : Corr P c k)
    (hc : SmallSteps Γ c c') : ∃ k', FwdSteps P k k' ∧ Corr P c' k' := by
  induction hc with
  | refl => exact ⟨k, .refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨k₁, h₁, h₁'⟩ := ih
    obtain ⟨k₂, h₂, h₂'⟩ := fwd_sim hW h₁' hstep
    exact ⟨k₂, h₁.trans h₂, h₂'⟩

theorem fin_B (hW : FwdWF P Γ main) {S' : RStack} {K E : Label} {D : List Label}
    (hS : StackCorr P [] S' K E D) (σ : Store) :
    ∃ k', FwdSteps P ⟨σ, E, K, S'⟩ k' ∧ k'.store = σ ∧ k'.stack = [] ∧
      P.block k'.next = some .stop := by
  have hP := hW.unique
  generalize hS0 : ([] : Stack) = S at hS
  induction hS with
  | nil hs => exact ⟨_, .refl, rfl, rfl, hs.stop_block hP P.main_mem_bodies⟩
  | seq => cases hS0
  | ifTrue => cases hS0
  | ifFalse => cases hS0
  | loop1 => cases hS0
  | loop2 => cases hS0
  | call hK hS hpb hs ih =>
    obtain ⟨k', h1, h2⟩ := ih hS0
    exact ⟨k', RTG.head (.return1 (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb))
      hK.exit_edge) h1, h2⟩
  | uncall hK hS hpb hs ih =>
    obtain ⟨k', h1, h2⟩ := ih hS0
    exact ⟨k', RTG.head (.return2 (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb))
      hK.exit_edge) h1, h2⟩

theorem fwd_final (hW : FwdWF P Γ main) {σ : Store} {k : RConfig}
    (h : Corr P ⟨σ, .skip, []⟩ k) :
    ∃ k', FwdSteps P k k' ∧ k'.store = σ ∧ k'.stack = [] ∧ P.block k'.next = some .stop := by
  have hP := hW.unique
  obtain ⟨σ', ℓp, ℓn, S'⟩ := k
  obtain ⟨hσ, K, E, D, hS, hctl⟩ := h
  simp only at hσ hS hctl; subst hσ
  rcases hctl with ⟨t, hK, hr, hE, rfl, hp, hD⟩ | ⟨-, rfl, rfl⟩
  · cases hr with
    | skip =>
      subst hE
      obtain ⟨k', h1, h2⟩ := fin_B hW hS σ
      exact ⟨k', RTG.head (.skip (hK.block hP (by simp [LStmt.blocks, LStmt.entry])) hK.exit_edge) h1, h2⟩
  · exact fin_B hW hS σ

/-! ### From forward rules to small-step -/

/-- Simulation of a forward transition from a control that is about to be executed. -/
theorem back_A (hW : FwdWF P Γ main) {t : LStmt Label} {s : Stmt} (hr : LRepr t s)
    {K E ℓp : Label} {D : List Label} {S : Stack} {S' : RStack} {σ : Store} {k' : RConfig}
    (hK : OccK P t K) (hE : t.exit = E) (hp : ℓp ∉ t.labels)
    (hD : t.labels ⊆ D) (hS : StackCorr P S S' K E D)
    (hk : FwdStep P ⟨σ, ℓp, t.entry, S'⟩ k') :
    ∃ c', SmallSteps Γ ⟨σ, s, S⟩ c' ∧ Corr P c' k' := by
  have hP := hW.unique
  subst hE
  induction hr generalizing K ℓp D S S' k' with
  | @seq t₁ t₂ s₁ s₂ hr₁ hr₂ ih₁ _ =>
    obtain ⟨c', h1, h2⟩ := ih₁ hK.seqL
      (fun h => hp (by rw [LStmt.labels_seq]; exact List.mem_append_left _ h))
      (List.Subset.refl _) hk (.seq hK hr₂ hS hD)
    exact ⟨c', RTG.head .seq1 h1, h2⟩
  | @assVar x op e ℓa =>
    obtain ⟨v, ℓ'', he, hedge, rfl⟩ :=
      FwdStep.cases_assVar hP (hK.block hP (o := .assVar x op e) (by simp [LStmt.blocks, LStmt.entry])) hk
    obtain rfl := hK.succ_of_flow_empty hP rfl hedge
    exact ⟨_, .single (.assVarS he), rfl, _, _, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | @assArr x e₁ op e₂ ℓa =>
    obtain ⟨vₗ, v, ℓ'', he₁, he₂, hedge, rfl⟩ :=
      FwdStep.cases_assArr hP (hK.block hP (o := .assArr x e₁ op e₂) (by simp [LStmt.blocks, LStmt.entry])) hk
    obtain rfl := hK.succ_of_flow_empty hP rfl hedge
    exact ⟨_, .single (.assArrS he₁ he₂), rfl, _, _, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | @call id ℓc =>
    obtain ⟨b, ℓ'', hpb, hedge, rfl⟩ :=
      FwdStep.cases_call hP (hK.block hP (o := .call id) (by simp [LStmt.blocks, LStmt.entry])) hk
    obtain ⟨s', a, m, z, hΓ, hs, hr'⟩ := hW.fwd_body _ _ hpb
    have hb := LProgram.mem_bodies_of_proc hpb
    rw [hs.entry_eq] at hedge ⊢
    obtain rfl := hs.start_succ hP hb hedge
    exact ⟨_, .single (.callS hΓ), rfl, _, _, _, .call hK hS hpb hs,
      Or.inl ⟨m, hs.occK hb, hr', rfl, rfl, hs.start_not_mem hP hb, List.Subset.refl _⟩⟩
  | @uncall id ℓc =>
    obtain ⟨b, ℓ'', hpb, hedge, rfl⟩ :=
      FwdStep.cases_uncall hP (hK.block hP (o := .uncall id) (by simp [LStmt.blocks, LStmt.entry])) hk
    obtain ⟨s', a, m, z, hΓ, hs, hr'⟩ := hW.inv_body _ _ hpb
    have hb := LProgram.mem_bodies_of_proc hpb
    rw [hs.entry_eq] at hedge ⊢
    obtain rfl := hs.start_succ hP hb hedge
    exact ⟨_, .single (.uncallS hΓ), rfl, _, _, _, .uncall hK hS hpb hs,
      Or.inl ⟨m, hs.occK hb, hr', rfl, rfl, hs.start_not_mem hP hb, List.Subset.refl _⟩⟩
  | @skip ℓs =>
    obtain ⟨ℓ'', hedge, rfl⟩ :=
      FwdStep.cases_skip hP (hK.block hP (by simp [LStmt.blocks, LStmt.entry])) hk
    obtain rfl := hK.succ_of_flow_empty hP rfl hedge
    exact ⟨_, .refl, rfl, _, _, D, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
  | @ite e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ hr₁ hr₂ _ _ =>
    simp only [LStmt.entry] at hk
    obtain ⟨h1, h2, -, -, -⟩ := hK.ite_facts hP
    have hctx := (hK.ctx_ite hP).1
    have hmem : ℓ₁ ∈ D := hD (by rw [LStmt.labels_ite]; exact List.mem_cons_self)
    rcases FwdStep.cases_cond (hK.block hP (o := .cond e₁) (by simp [LStmt.blocks])) hk with
      ⟨_, _, _, _, _, v, hc, he, ht, rfl⟩ | ⟨_, _, _, _, _, v, hc, he, hf, rfl⟩ |
      ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩ |
      ⟨_, _, _, _, _, _, rfl, -⟩ | ⟨_, _, _, _, _, rfl, -⟩ | ⟨_, _, _, _, _, rfl, -⟩
    · rw [hctx] at hc; cases hc
      exact ⟨_, .single (.ifTrue1 he ht), rfl, _, _, _, .ifTrue hK hS hD,
        Or.inl ⟨t₁, hK.iteL, hr₁, rfl, rfl, h1, List.Subset.refl _⟩⟩
    · rw [hctx] at hc; cases hc
      exact ⟨_, .single (.ifFalse1 he hf), rfl, _, _, _, .ifFalse hK hS hD,
        Or.inl ⟨t₂, hK.iteR, hr₂, rfl, rfl, h2, List.Subset.refl _⟩⟩
    · rw [hctx] at hc; cases hc
    all_goals exact absurd hmem (hS.guard_not_mem hP rfl)
  | @loop e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ hr₁ hr₂ _ _ =>
    simp only [LStmt.entry] at hk
    obtain ⟨h1, -, -, -, -⟩ := hK.loop_facts hP
    have hctx := (hK.ctx_loop hP).1
    have hmem : ℓ₁ ∈ D := hD (by rw [LStmt.labels_loop]; exact List.mem_cons_self)
    rcases FwdStep.cases_cond (hK.block hP (o := .cond e₁) (by simp [LStmt.blocks])) hk with
      ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ |
      ⟨_, _, _, _, _, v, hc, he, ht, -, rfl⟩ | ⟨_, _, _, _, rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩ |
      ⟨_, _, _, _, _, _, rfl, -⟩ | ⟨_, _, _, _, _, rfl, -⟩ | ⟨_, _, _, _, _, rfl, -⟩
    · rw [hctx] at hc; cases hc
    · rw [hctx] at hc; cases hc
    · rw [hctx] at hc; cases hc
      exact ⟨_, .single (.loopMainS he ht), rfl, _, _, _, .loop1 hK hr₁ hr₂ hS hD,
        Or.inl ⟨t₁, hK.loopL, hr₁, rfl, rfl, h1, List.Subset.refl _⟩⟩
    all_goals exact absurd hmem (hS.guard_not_mem hP rfl)

/-- Simulation of a forward transition from a completed control. -/
theorem back_B (hW : FwdWF P Γ main) {S : Stack} {S' : RStack} {K E : Label}
    {D : List Label} (hS : StackCorr P S S' K E D) {σ : Store} {k' : RConfig}
    (hk : FwdStep P ⟨σ, E, K, S'⟩ k') :
    ∃ c', SmallSteps Γ ⟨σ, .skip, S⟩ c' ∧ Corr P c' k' := by
  have hP := hW.unique
  cases hS with
  | nil hs =>
    rcases FwdStep.cases_stop hP (hs.stop_block hP P.main_mem_bodies) hk with
      ⟨_, _, _, h, -⟩ | ⟨_, _, _, h, -⟩ <;> cases h
  | @seq t₁ t₂ s₂ K S S' D hK hr hS hD =>
    obtain ⟨c', h1, h2⟩ := back_A hW hr hK.seqR rfl (hK.not_mem_seq hP)
      (fun x hx => hD (by rw [LStmt.labels_seq]; exact List.mem_append_right _ hx)) hS hk
    exact ⟨c', RTG.head .seq2 h1, h2⟩
  | @ifTrue e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ K S S' D hK hS hD =>
    obtain ⟨-, -, -, -, hne⟩ := hK.ite_facts hP
    have hctx := (hK.ctx_ite hP).2
    rcases FwdStep.cases_cond (hK.block hP (o := .cond e₂) (by simp [LStmt.blocks])) hk with
      ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ |
      ⟨_, _, _, _, hst, he, ht, hedge, rfl⟩ | ⟨_, _, _, _, hst, -⟩ |
      ⟨_, _, _, _, _, _, hst, -⟩ | ⟨_, _, _, _, _, hst, -⟩ | ⟨_, _, _, _, _, hst, -⟩
    · rw [hctx] at hc; simp only [Option.some.injEq, LStmt.ite.injEq] at hc
      exact absurd hc.2.1 hne
    · rw [hctx] at hc; simp only [Option.some.injEq, LStmt.ite.injEq] at hc
      exact absurd hc.2.1 hne
    · rw [hctx] at hc; cases hc
    · cases hst
      obtain rfl := hK.succ_ite hP hedge
      exact ⟨_, .single (.ifTrue2 he ht), rfl, _, _, _, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
    all_goals cases hst
  | @ifFalse e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ K S S' D hK hS hD =>
    obtain ⟨-, -, -, -, hne⟩ := hK.ite_facts hP
    have hctx := (hK.ctx_ite hP).2
    rcases FwdStep.cases_cond (hK.block hP (o := .cond e₂) (by simp [LStmt.blocks])) hk with
      ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ |
      ⟨_, _, _, _, hst, -⟩ | ⟨_, _, _, _, hst, he, hf, hedge, rfl⟩ |
      ⟨_, _, _, _, _, _, hst, -⟩ | ⟨_, _, _, _, _, hst, -⟩ | ⟨_, _, _, _, _, hst, -⟩
    · rw [hctx] at hc; simp only [Option.some.injEq, LStmt.ite.injEq] at hc
      exact absurd hc.2.1 hne
    · rw [hctx] at hc; simp only [Option.some.injEq, LStmt.ite.injEq] at hc
      exact absurd hc.2.1 hne
    · rw [hctx] at hc; cases hc
    · cases hst
    · cases hst
      obtain rfl := hK.succ_ite hP hedge
      exact ⟨_, .single (.ifFalse2 he hf), rfl, _, _, _, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
    all_goals cases hst
  | @loop1 e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ K S S' D hK hr₁ hr₂ hS hD =>
    obtain ⟨-, -, -, h4, hne⟩ := hK.loop_facts hP
    have hctx := (hK.ctx_loop hP).2
    rcases FwdStep.cases_cond (hK.block hP (o := .cond e₂) (by simp [LStmt.blocks])) hk with
      ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ |
      ⟨_, _, _, _, hst, -⟩ | ⟨_, _, _, _, hst, -⟩ |
      ⟨_, _, _, _, _, _, hst, he, ht, hedge, hne', rfl⟩ | ⟨_, _, _, _, _, hst, he, hf, rfl⟩ |
      ⟨_, _, _, _, _, hst, -⟩
    · rw [hctx] at hc; cases hc
    · rw [hctx] at hc; cases hc
    · rw [hctx] at hc; simp only [Option.some.injEq, LStmt.loop.injEq] at hc
      exact absurd hc.2.1 hne
    · cases hst
    · cases hst
    · cases hst
      rcases hK.succ_loop hP hedge with rfl | h
      · exact ⟨_, .single (.loopBaseS he ht), rfl, _, _, _, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
      · exact absurd h hne'
    · cases hst
      exact ⟨_, .single (.loop1 he hf), rfl, _, _, _, .loop2 hK hr₁ hr₂ hS hD,
        Or.inl ⟨t₂, hK.loopR, hr₂, rfl, rfl, h4, List.Subset.refl _⟩⟩
    · cases hst
  | @loop2 e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ K S S' D hK hr₁ hr₂ hS hD =>
    obtain ⟨h1, -, -, -, -⟩ := hK.loop_facts hP
    have hctx := (hK.ctx_loop hP).1
    rcases FwdStep.cases_cond (hK.block hP (o := .cond e₁) (by simp [LStmt.blocks])) hk with
      ⟨_, _, _, _, _, v, hc, -⟩ | ⟨_, _, _, _, _, v, hc, -⟩ |
      ⟨_, _, _, _, _, v, hc, -, -, hne, -⟩ |
      ⟨_, _, _, _, hst, -⟩ | ⟨_, _, _, _, hst, -⟩ |
      ⟨_, _, _, _, _, _, hst, -⟩ | ⟨_, _, _, _, _, hst, -⟩ | ⟨_, _, _, _, _, hst, he, hf, rfl⟩
    · rw [hctx] at hc; cases hc
    · rw [hctx] at hc; cases hc
    · rw [hctx] at hc; cases hc; exact absurd rfl hne
    all_goals try cases hst
    exact ⟨_, .single (.loop2 he hf), rfl, _, _, _, .loop1 hK hr₁ hr₂ hS hD,
      Or.inl ⟨t₁, hK.loopL, hr₁, rfl, rfl, h1, List.Subset.refl _⟩⟩
  | @call id ℓc K a z b m S S' D hK hS hpb hs =>
    rcases FwdStep.cases_stop hP (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb)) hk with
      ⟨_, _, _, hst, hedge, rfl⟩ | ⟨_, _, _, hst, -⟩
    · cases hst
      obtain rfl := hK.succ_of_flow_empty hP rfl hedge
      exact ⟨_, .refl, rfl, _, _, _, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · cases hst
  | @uncall id ℓc K a z b m S S' D hK hS hpb hs =>
    rcases FwdStep.cases_stop hP (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb)) hk with
      ⟨_, _, _, hst, -⟩ | ⟨_, _, _, hst, hedge, rfl⟩
    · cases hst
    · cases hst
      obtain rfl := hK.succ_of_flow_empty hP rfl hedge
      exact ⟨_, .refl, rfl, _, _, _, hS, Or.inr ⟨rfl, rfl, rfl⟩⟩

theorem back_sim (hW : FwdWF P Γ main) {c : SSConfig} {k k' : RConfig} (h : Corr P c k)
    (hk : FwdStep P k k') : ∃ c', SmallSteps Γ c c' ∧ Corr P c' k' := by
  obtain ⟨σ, s, S⟩ := c
  obtain ⟨σ', ℓp, ℓn, S'⟩ := k
  obtain ⟨hσ, K, E, D, hS, hctl⟩ := h
  simp only at hσ hS hctl; subst hσ
  rcases hctl with ⟨t, hK, hr, hE, rfl, hp, hD⟩ | ⟨rfl, rfl, rfl⟩
  · exact back_A hW hr hK hE hp hD hS hk
  · exact back_B hW hS hk

theorem back_sims (hW : FwdWF P Γ main) {c : SSConfig} {k k' : RConfig} (h : Corr P c k)
    (hk : FwdSteps P k k') : ∃ c', SmallSteps Γ c c' ∧ Corr P c' k' := by
  induction hk with
  | refl => exact ⟨c, .refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨c₁, h₁, h₁'⟩ := ih
    obtain ⟨c₂, h₂, h₂'⟩ := back_sim hW h₁' hstep
    exact ⟨c₂, h₁.trans h₂, h₂'⟩

theorem back_final (hW : FwdWF P Γ main) {c : SSConfig} {σ : Store} {ℓ' ℓ'' : Label}
    (h : Corr P c ⟨σ, ℓ', ℓ'', []⟩) (hb : P.block ℓ'' = some .stop) :
    c = ⟨σ, .skip, []⟩ := by
  have hP := hW.unique
  obtain ⟨σ', s, S⟩ := c
  obtain ⟨hσ, K, E, D, hS, hctl⟩ := h
  simp only at hσ hS hctl; subst hσ
  rcases hctl with ⟨t, hK, hr, hE, rfl, hp, hD⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨o, ho, hne, -⟩ := hr.entry_block
    rw [hK.block hP ho] at hb; cases hb; exact absurd rfl hne
  · cases hS with
    | nil => rfl
    | seq hK hr _ _ =>
      obtain ⟨o, ho, hne, -⟩ := hr.entry_block
      rw [hK.seqR.block hP ho] at hb; cases hb; exact absurd rfl hne

/-! ### Lemma "forward-rev" -/

theorem corr_init (hW : FwdWF P Γ main) {ℓ : Label} (hℓ : (P.main.entry, ℓ) ∈ P.mainCFG) :
    Corr P ⟨Store.empty, main, []⟩ ⟨Store.empty, P.main.entry, ℓ, []⟩ := by
  have hP := hW.unique
  obtain ⟨a, m, z, hs, hr⟩ := hW.main_shape
  have hb := P.main_mem_bodies
  rw [hs.entry_eq] at hℓ ⊢
  obtain rfl := hs.start_succ hP hb (LProgram.flow_subset_of_mem hb hℓ)
  exact ⟨rfl, _, _, _, .nil hs,
    Or.inl ⟨m, hs.occK hb, hr, rfl, rfl, hs.start_not_mem hP hb, List.Subset.refl _⟩⟩

/-- Lemma "forward-rev", for any labeled program `P` related to the original program
`(main, Γ)` by `FwdWF`: if `entry(s) ⟶ ℓ` belongs to the CFG of the main program `s` of
`P`, then `⟨ε, main, []⟩ →* ⟨σ, skip, []⟩` iff `⟨ε, entry(s), ℓ, []⟩ ⇀* ⟨σ, ℓ', ℓ'', []⟩`
with `block(ℓ'') = stop`, for some `ℓ'`, `ℓ''`. -/
theorem smallSteps_iff_fwdSteps (hW : FwdWF P Γ main) {ℓ : Label}
    (hℓ : (P.main.entry, ℓ) ∈ P.mainCFG) (σ : Store) :
    SmallSteps Γ ⟨Store.empty, main, []⟩ ⟨σ, .skip, []⟩ ↔
      ∃ ℓ' ℓ'', FwdSteps P ⟨Store.empty, P.main.entry, ℓ, []⟩ ⟨σ, ℓ', ℓ'', []⟩ ∧
        P.block ℓ'' = some .stop := by
  constructor
  · intro h
    obtain ⟨k, hk, hc⟩ := fwd_sims hW (corr_init hW hℓ) h
    obtain ⟨⟨σ', ℓ', ℓ'', S'⟩, hk', rfl, rfl, hb⟩ := fwd_final hW hc
    exact ⟨ℓ', ℓ'', hk.trans hk', hb⟩
  · rintro ⟨ℓ', ℓ'', hk, hb⟩
    obtain ⟨c, hc, hcorr⟩ := back_sims hW (corr_init hW hℓ) hk
    rw [← back_final hW hcorr hb]
    exact hc

end Janus

end
