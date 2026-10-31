module

public import RevJanus.Janus.BackwardInv
public import RevJanus.Janus.ForwardProgram

/-!
# Janus: the loop lemma (Section "The Backward Rules")

> **Lemma (loop lemma).** Let `⟨σ, ℓ₁, ℓ₂, S⟩` and `⟨σ', ℓ₁', ℓ₂', S'⟩` be reachable
> configurations. Then `⟨σ, ℓ₁, ℓ₂, S⟩ ⇀ ⟨σ', ℓ₁', ℓ₂', S'⟩` iff
> `⟨σ', ℓ₁', ℓ₂', S'⟩ ↽ ⟨σ, ℓ₁, ℓ₂, S⟩`.

The lemma is proved for every labeled program satisfying the well-formedness conditions
`RevWF` (`loop_lemma`), and in particular for the labeled version `p.toLabeled` of every
well-formed program `p` (`Program.loop_lemma`). As in the paper, the well-formedness of `p`
(in every assignment `x ⊕= e`, the variable `x` does not occur in `e`) is needed for the
cases `AssVar` and `AssArr`.

As in the paper, the proof is a case distinction on the applied rule. Reachability is used
through the invariant `RInv` of `RevJanus.Janus.BackwardInv`: it provides the facts
that the paper's proof takes for granted, e.g. that the two labels of a configuration are
the two ends of an edge of the CFG, that the label preceding the assertion `ℓ₂` of a
conditional whose then-branch `s₁` is running is `exit(s₁)`, or that the stack item
`call(ℓ)` at the top of the stack refers to a `call id` statement whose procedure body is
the one being run.
-/

@[expose] public section

namespace Janus

variable {P : LProgram Label}

theorem LProgram.block_ite_test (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {s₁ s₂ : LStmt Label} (ho : LProgram.Occurs (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) P) {e : Expr}
    (hb : P.block ℓ₁ = some (.cond e)) : e = e₁ := by
  have h := LProgram.block_of_occurs hP ho (ℓ := ℓ₁) (o := .cond e₁) (by simp [LStmt.blocks])
  rw [hb] at h; cases h; rfl

theorem LProgram.block_ite_assert (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {s₁ s₂ : LStmt Label} (ho : LProgram.Occurs (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) P) {e : Expr}
    (hb : P.block ℓ₂ = some (.cond e)) : e = e₂ := by
  have h := LProgram.block_of_occurs hP ho (ℓ := ℓ₂) (o := .cond e₂) (by simp [LStmt.blocks])
  rw [hb] at h; cases h; rfl

theorem LProgram.block_loop_test (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {s₁ s₂ : LStmt Label} (ho : LProgram.Occurs (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) P) {e : Expr}
    (hb : P.block ℓ₁ = some (.cond e)) : e = e₁ := by
  have h := LProgram.block_of_occurs hP ho (ℓ := ℓ₁) (o := .cond e₁) (by simp [LStmt.blocks])
  rw [hb] at h; cases h; rfl

theorem LProgram.block_loop_assert (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {s₁ s₂ : LStmt Label} (ho : LProgram.Occurs (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) P) {e : Expr}
    (hb : P.block ℓ₂ = some (.cond e)) : e = e₂ := by
  have h := LProgram.block_of_occurs hP ho (ℓ := ℓ₂) (o := .cond e₂) (by simp [LStmt.blocks])
  rw [hb] at h; cases h; rfl

/-! ### From forward to backward steps -/

theorem fwd_to_bwd (hW : RevWF P) {k k' : RConfig} (hk : RInv P k) (h : FwdStep P k k') :
    BwdStep P k' k := by
  have hP := hW.unique
  obtain ⟨t, pr, K, hS, he⟩ := hk
  have hF := hS.frame hP
  have hfl := he.flow hF
  cases h with
  | @assVar σ ℓ ℓ' ℓ'' x op e v S hb hev hf =>
    have hx : (Loc.var x).name ∉ e.vars := hW.assVar_wf hb
    have hev' := (EvalExpr.update_iff (w := op.interp (σ (.var x)) v) hx).2 hev
    have h' := BwdStep.assVar (ℓ := ℓ) (ℓ'' := ℓ'') (S := S) hb hev'
      (LProgram.mem_invFlow.2 hfl)
    rwa [Store.update_apply_self, Store.update_update_self, ModOp.interp_invert_interp,
      Store.update_apply_eq] at h'
  | @assArr σ ℓ ℓ' ℓ'' x eₗ op e vₗ v S hb hevl hev hf =>
    have hx := hW.assArr_wf hb
    have hx₁ : (Loc.elem x vₗ).name ∉ eₗ.vars := hx.1
    have hx₂ : (Loc.elem x vₗ).name ∉ e.vars := hx.2
    have hevl' := (EvalExpr.update_iff (w := op.interp (σ (.elem x vₗ)) v) hx₁).2 hevl
    have hev' := (EvalExpr.update_iff (w := op.interp (σ (.elem x vₗ)) v) hx₂).2 hev
    have h' := BwdStep.assArr (ℓ := ℓ) (ℓ'' := ℓ'') (S := S) hb hevl' hev'
      (LProgram.mem_invFlow.2 hfl)
    rwa [Store.update_apply_self, Store.update_update_self, ModOp.interp_invert_interp,
      Store.update_apply_eq] at h'
  | call hb hpb hf =>
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine .call ?_ (LProgram.mem_invFlow.2 hfl)
    rw [hs.entry_eq]; exact hs.start_block hP (LProgram.mem_bodies_of_proc hpb)
  | uncall hb hpb hf =>
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine .uncall ?_ (LProgram.mem_invFlow.2 hfl)
    rw [hs.entry_eq]; exact hs.start_block hP (LProgram.mem_bodies_of_proc hpb)
  | @return1 σ ℓ ℓ' ℓ'' ℓ''' S hb hf =>
    cases hS with
    | @call _ _ _ _ _ _ b _ _ _ _ _ hbc hpb hs =>
      have hbb := LProgram.mem_bodies_of_proc hpb
      have hmem : ℓ' ∈ b.labels := by
        rw [hs.labels_eq]
        rcases he.tgt with h' | ⟨-, rfl⟩
        · simp [h']
        · simp
      obtain rfl : ℓ' = _ := by
        rcases hW.body_block hbb hs hmem hb with ⟨-, h'⟩ | ⟨h', -⟩ | ⟨-, -, h'⟩
        · cases h'
        · exact h'
        · exact absurd rfl h'
      have h' := BwdStep.return1 (σ := σ) (ℓ''' := ℓ''') (S := S) hbc hpb
        (ℓ := ℓ) (LProgram.mem_invFlow.2 (by rw [hs.exit_eq]; exact hfl))
      rwa [hs.exit_eq] at h'
  | @return2 σ ℓ ℓ' ℓ'' ℓ''' S hb hf =>
    cases hS with
    | @uncall _ _ _ _ _ _ b _ _ _ _ _ hbc hpb hs =>
      have hbb := LProgram.mem_bodies_of_proc hpb
      have hmem : ℓ' ∈ b.labels := by
        rw [hs.labels_eq]
        rcases he.tgt with h' | ⟨-, rfl⟩
        · simp [h']
        · simp
      obtain rfl : ℓ' = _ := by
        rcases hW.body_block hbb hs hmem hb with ⟨-, h'⟩ | ⟨h', -⟩ | ⟨-, -, h'⟩
        · cases h'
        · exact h'
        · exact absurd rfl h'
      have h' := BwdStep.return2 (σ := σ) (ℓ''' := ℓ''') (S := S) hbc hpb
        (ℓ := ℓ) (LProgram.mem_invFlow.2 (by rw [hs.exit_eq]; exact hfl))
      rwa [hs.exit_eq] at h'
  | skip hb hf => exact .skip hb (LProgram.mem_invFlow.2 hfl)
  | ifTrue1 hc hev ht =>
    exact .ifTrue1 (LProgram.block_of_occurs hP (LProgram.ctx_some hc).1
      (by simp [LStmt.blocks])) hev ht (LProgram.mem_invFlow.2 hfl)
  | ifFalse1 hc hev ht =>
    exact .ifFalse1 (LProgram.block_of_occurs hP (LProgram.ctx_some hc).1
      (by simp [LStmt.blocks])) hev ht (LProgram.mem_invFlow.2 hfl)
  | loopMain hc hev ht hne =>
    exact .loopMain (LProgram.block_of_occurs hP (LProgram.ctx_some hc).1
      (by simp [LStmt.blocks])) hev ht (LProgram.mem_invFlow.2 hfl) hne
  | ifTrue2 hb hev ht hf =>
    cases hS with
    | ifTrue hS' hu =>
      have ho := hS'.occurs_P hP hu
      obtain rfl := he.eq_exit hP hF
      obtain rfl := LProgram.block_ite_assert hP ho hb
      exact .ifTrue2 (LProgram.ctx_ite hP ho).2 hev ht
  | ifFalse2 hb hev ht hf =>
    cases hS with
    | ifFalse hS' hu =>
      have ho := hS'.occurs_P hP hu
      obtain rfl := he.eq_exit hP hF
      obtain rfl := LProgram.block_ite_assert hP ho hb
      exact .ifFalse2 (LProgram.ctx_ite hP ho).2 hev ht
  | loopBase hb hev ht hf hne =>
    cases hS with
    | loop1 hS' hu =>
      have ho := hS'.occurs_P hP hu
      obtain rfl := he.eq_exit hP hF
      obtain rfl := LProgram.block_loop_assert hP ho hb
      exact .loopBase (LProgram.ctx_loop hP ho).2 hev ht hne
  | loop1 hb hev hf =>
    cases hS with
    | loop1 hS' hu =>
      obtain rfl := he.eq_exit hP hF
      exact .loop1 hb hev hf
  | loop2 hb hev hf =>
    cases hS with
    | loop2 hS' hu =>
      obtain rfl := he.eq_exit hP hF
      exact .loop2 hb hev hf

/-! ### From backward to forward steps -/

theorem bwd_to_fwd (hW : RevWF P) {k k' : RConfig} (hk' : RInv P k') (h : BwdStep P k' k) :
    FwdStep P k k' := by
  have hP := hW.unique
  obtain ⟨t, pr, K, hS, he⟩ := hk'
  have hF := hS.frame hP
  have hfl := he.flow hF
  cases h with
  | @assVar σ ℓ ℓ' ℓ'' x op e v S hb hev hf =>
    have hx : (Loc.var x).name ∉ e.vars := hW.assVar_wf hb
    have hev' := (EvalExpr.update_iff (w := op.invert.interp (σ (.var x)) v) hx).2 hev
    have h' := FwdStep.assVar (ℓ := ℓ) (ℓ'' := ℓ'') (S := S) hb hev' hfl
    rwa [Store.update_apply_self, Store.update_update_self, ModOp.interp_interp_invert,
      Store.update_apply_eq] at h'
  | @assArr σ ℓ ℓ' ℓ'' x eₗ op e vₗ v S hb hevl hev hf =>
    have hx := hW.assArr_wf hb
    have hx₁ : (Loc.elem x vₗ).name ∉ eₗ.vars := hx.1
    have hx₂ : (Loc.elem x vₗ).name ∉ e.vars := hx.2
    have hevl' := (EvalExpr.update_iff (w := op.invert.interp (σ (.elem x vₗ)) v) hx₁).2 hevl
    have hev' := (EvalExpr.update_iff (w := op.invert.interp (σ (.elem x vₗ)) v) hx₂).2 hev
    have h' := FwdStep.assArr (ℓ := ℓ) (ℓ'' := ℓ'') (S := S) hb hevl' hev' hfl
    rwa [Store.update_apply_self, Store.update_update_self, ModOp.interp_interp_invert,
      Store.update_apply_eq] at h'
  | @call σ ℓ ℓ' ℓ'' ℓₛ S hb hf =>
    cases hS with
    | @call _ _ _ _ _ _ b _ _ _ _ _ hbc hpb hs =>
      have hbb := LProgram.mem_bodies_of_proc hpb
      have hmem : ℓₛ ∈ b.labels := by
        rw [hs.labels_eq]
        rcases he.src with h' | ⟨rfl, -⟩
        · simp [h']
        · simp
      obtain rfl : ℓₛ = _ := by
        rcases hW.body_block hbb hs hmem hb with ⟨h', -⟩ | ⟨-, h'⟩ | ⟨-, h', -⟩
        · exact h'
        · cases h'
        · exact absurd rfl h'
      have h' := FwdStep.call (σ := σ) (ℓ := ℓ) (S := S) hbc hpb (by rw [hs.entry_eq]; exact hfl)
      rwa [hs.entry_eq] at h'
  | @uncall σ ℓ ℓ' ℓ'' ℓₛ S hb hf =>
    cases hS with
    | @uncall _ _ _ _ _ _ b _ _ _ _ _ hbc hpb hs =>
      have hbb := LProgram.mem_bodies_of_proc hpb
      have hmem : ℓₛ ∈ b.labels := by
        rw [hs.labels_eq]
        rcases he.src with h' | ⟨rfl, -⟩
        · simp [h']
        · simp
      obtain rfl : ℓₛ = _ := by
        rcases hW.body_block hbb hs hmem hb with ⟨h', -⟩ | ⟨-, h'⟩ | ⟨-, h', -⟩
        · exact h'
        · cases h'
        · exact absurd rfl h'
      have h' := FwdStep.uncall (σ := σ) (ℓ := ℓ) (S := S) hbc hpb
        (by rw [hs.entry_eq]; exact hfl)
      rwa [hs.entry_eq] at h'
  | return1 hb hpb hf =>
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine .return1 ?_ hfl
    rw [hs.exit_eq]; exact hs.stop_block hP (LProgram.mem_bodies_of_proc hpb)
  | return2 hb hpb hf =>
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine .return2 ?_ hfl
    rw [hs.exit_eq]; exact hs.stop_block hP (LProgram.mem_bodies_of_proc hpb)
  | skip hb hf => exact .skip hb hfl
  | ifTrue1 hb hev ht hf =>
    cases hS with
    | ifTrue hS' hu =>
      have ho := hS'.occurs_P hP hu
      obtain rfl := he.eq_entry hF
      obtain rfl := LProgram.block_ite_test hP ho hb
      exact .ifTrue1 (LProgram.ctx_ite hP ho).1 hev ht
  | ifFalse1 hb hev ht hf =>
    cases hS with
    | ifFalse hS' hu =>
      have ho := hS'.occurs_P hP hu
      obtain rfl := he.eq_entry hF
      obtain rfl := LProgram.block_ite_test hP ho hb
      exact .ifFalse1 (LProgram.ctx_ite hP ho).1 hev ht
  | loopMain hb hev ht hf hne =>
    cases hS with
    | loop1 hS' hu =>
      have ho := hS'.occurs_P hP hu
      obtain rfl := he.eq_entry hF
      obtain rfl := LProgram.block_loop_test hP ho hb
      exact .loopMain (LProgram.ctx_loop hP ho).1 hev ht hne
  | ifTrue2 hc hev ht =>
    exact .ifTrue2 (LProgram.block_of_occurs hP (LProgram.ctx_some hc).1
      (by simp [LStmt.blocks])) hev ht hfl
  | ifFalse2 hc hev ht =>
    exact .ifFalse2 (LProgram.block_of_occurs hP (LProgram.ctx_some hc).1
      (by simp [LStmt.blocks])) hev ht hfl
  | loopBase hc hev ht hne =>
    exact .loopBase (LProgram.block_of_occurs hP (LProgram.ctx_some hc).1
      (by simp [LStmt.blocks])) hev ht hfl hne
  | loop1 hb hev hf =>
    cases hS with
    | loop2 hS' hu =>
      obtain rfl := he.eq_entry hF
      exact .loop1 hb hev hf
  | loop2 hb hev hf =>
    cases hS with
    | loop1 hS' hu =>
      obtain rfl := he.eq_entry hF
      exact .loop2 hb hev hf

/-! ### The loop lemma -/

/-- **Lemma (loop lemma).** Let `P` be a labeled program satisfying the well-formedness
conditions `RevWF`, and let `k = ⟨σ, ℓ₁, ℓ₂, S⟩` and `k' = ⟨σ', ℓ₁', ℓ₂', S'⟩` be reachable
configurations. Then `k ⇀ k'` iff `k' ↽ k`. -/
theorem loop_lemma (hW : RevWF P) {k k' : RConfig} (hk : P.Reachable k)
    (hk' : P.Reachable k') : FwdStep P k k' ↔ BwdStep P k' k :=
  ⟨fun h => fwd_to_bwd hW (hk.rInv hW) h, fun h => bwd_to_fwd hW (hk'.rInv hW) h⟩

/-! ### The labeled version of a program -/

theorem labelProcs_mem {α : Type} (ds : List (PName × LStmt α)) (n : Label)
    {d : LProcDecl Label} (h : d ∈ (labelProcs ds n).1) :
    ∃ x ∈ ds, ∃ k, d.body = (x.2.labelFrom k).1 := by
  induction ds generalizing n with
  | nil => simp [labelProcs] at h
  | cons d₀ ds ih =>
    simp only [labelProcs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨d₀, List.mem_cons_self, n, rfl⟩
    · obtain ⟨x, hx, k, hk⟩ := ih _ h
      exact ⟨x, List.mem_cons_of_mem _ hx, k, hk⟩

/-- The labeled version of a well-formed program satisfies the conditions `RevWF`. -/
theorem Program.revWF (p : Program) (hp : p.WellFormed) : RevWF p.toLabeled := by
  refine ⟨p.toLabeled_uniqueLabels, fun b hb => ?_⟩
  simp only [LProgram.bodies, List.mem_cons, List.mem_map] at hb
  rcases hb with rfl | ⟨d, hd, rfl⟩
  · obtain ⟨z, hz⟩ := p.main.withStartStop_labelFrom 1
    exact ⟨1, _, z, p.main, hz, LRepr.labelFrom _ _, hp.1⟩
  · obtain ⟨x, hx, k, hk⟩ := labelProcs_mem _ _ hd
    simp only [Program.xprocs, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨d₀, hd₀, rfl⟩ | ⟨d₀, hd₀, rfl⟩
    · obtain ⟨z, hz⟩ := d₀.body.withStartStop_labelFrom k
      exact ⟨k, _, z, d₀.body, hk ▸ hz, LRepr.labelFrom _ _, hp.2.1 d₀ hd₀⟩
    · obtain ⟨z, hz⟩ := d₀.body.withStartStop_invert_labelFrom k
      exact ⟨k, _, z, d₀.body.invert, hk ▸ hz, LRepr.labelFrom _ _,
        (hp.2.1 d₀ hd₀).invert⟩

/-- **Lemma (loop lemma)** for the labeled version `p.toLabeled` of a well-formed program
`p`: if `k = ⟨σ, ℓ₁, ℓ₂, S⟩` and `k' = ⟨σ', ℓ₁', ℓ₂', S'⟩` are reachable configurations,
then `k ⇀ k'` iff `k' ↽ k`. -/
theorem Program.loop_lemma (p : Program) (hp : p.WellFormed) {k k' : RConfig}
    (hk : p.toLabeled.Reachable k) (hk' : p.toLabeled.Reachable k') :
    FwdStep p.toLabeled k k' ↔ BwdStep p.toLabeled k' k :=
  Janus.loop_lemma (p.revWF hp) hk hk'

end Janus

end
