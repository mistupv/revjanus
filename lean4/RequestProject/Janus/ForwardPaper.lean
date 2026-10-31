module

public import RequestProject.Janus.ForwardEquiv

/-!
# Janus: the proof devices of Lemma "forward-rev", as stated in the paper

This file formalizes the notions introduced in the (revised) proof of Lemma "forward-rev"
of Subsection "The Forward Rules", and restates the steps of that proof with them:

* Definition "continuation" (`next(t)`): the relation `OccK P t K` ("`t` occurs in a body
  `[start]^a s [stop]^z` of `P`, and `next(t) = K`") of `RequestProject.Janus.ForwardCFG`,
  which has exactly the clauses of the definition; when labels are unique, it is functional
  (`OccK.next_unique`), so that `next` is well defined;
* Lemma "cfg-next": `cfg_next_1` … `cfg_next_5`;
* Figure "eqstack", the relation `π ∼stack^{ℓₙ,ℓₑ} π'`: `StackEquiv`;
* the relation `∼conf`, with conditions (a) and (b): `ConfEquiv`.

We then show that these notions match the simulation relation `StackCorr`/`Corr` used in
`RequestProject.Janus.ForwardEquiv` (`StackCorr.toStackEquiv`, `StackEquiv.toStackCorr`,
`corr_iff_confEquiv`), and derive the claims of the proof in terms of `∼conf`
(`ConfEquiv.init`, `ConfEquiv.fwd_sim`, `ConfEquiv.back_sim`, `ConfEquiv.final_fwd`,
`ConfEquiv.final_back`), and finally the lemma itself (`ConfEquiv.smallSteps_iff_fwdSteps`).

As in `RequestProject.Janus.ForwardEquiv`, the small-step configurations are the real
(unlabeled) small-step configurations, and the statements they contain are related to the
labeled statements of `P` by `LRepr` (the paper says that the small-step rules "simply ignore
the annotations"): "`s` is a statement occurring in `p`" in condition (a) of `∼conf` means
that the small-step control `s` is the unlabeled version of a labeled statement `t`
occurring in `P`.
-/

@[expose] public section

namespace Janus

variable {P : LProgram Label}

/-! ### Definition "continuation" -/

/-- **Definition "continuation"**: `OccK P t K` means that `t` occurs in the body
`[start]^a s [stop]^z` of the main program or of a (possibly inverse) procedure of `P`, and
that `next(t) = K`. Its constructors are exactly the clauses of the definition: `next(s) = z`
(`OccK.body`); `next(t₁) = entry(t₂)` and `next(t₂) = next(t)` for `t = t₁ t₂`
(`OccK.seqL`, `OccK.seqR`); `next(t₁) = next(t₂) = ℓ₂` for a conditional (`OccK.iteL`,
`OccK.iteR`); `next(t₁) = ℓ₂` and `next(t₂) = ℓ₁` for a loop (`OccK.loopL`, `OccK.loopR`).

This theorem states that, when all labels are unique, `next` is well defined: a statement
occurring in `P` has a single continuation. -/
theorem OccK.next_unique (hP : P.UniqueLabels) {t : LStmt Label} {K K' : Label}
    (h : OccK P t K) (h' : OccK P t K') : K = K' := by
  rcases h'.edge hP h.exit_edge (LStmt.exit_mem_labels _) with ⟨-, rfl⟩ | hx
  · rfl
  · exact absurd (LStmt.mem_labels_of_edge hx).2 (h.not_mem hP)

/-! ### Lemma "cfg-next" -/

/-- **Lemma "cfg-next" (1)**: `(exit(t), next(t)) ∈ flow(p)`. -/
theorem cfg_next_1 {t : LStmt Label} {K : Label} (h : OccK P t K) : (t.exit, K) ∈ P.flow :=
  h.exit_edge

/-- **Lemma "cfg-next" (2)**: if `t` is an assignment, a `call`, an `uncall` or a `skip`,
then `next(t)` is the only successor of `exit(t)` in `flow(p)`. -/
theorem cfg_next_2 (hP : P.UniqueLabels) {t : LStmt Label} {K : Label} (h : OccK P t K)
    (ht : (∃ x op e ℓ, t = .assVar x op e ℓ) ∨ (∃ x e₁ op e₂ ℓ, t = .assArr x e₁ op e₂ ℓ) ∨
      (∃ id ℓ, t = .call id ℓ) ∨ (∃ id ℓ, t = .uncall id ℓ) ∨ (∃ ℓ, t = .skip ℓ)) :
    (t.exit, K) ∈ P.flow ∧ ∀ x, (t.exit, x) ∈ P.flow → x = K := by
  refine ⟨h.exit_edge, fun _ hx => h.succ_of_flow_empty hP ?_ hx⟩
  rcases ht with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
    rfl

/-- **Lemma "cfg-next" (3)**: if `t = if [e₁]^ℓ₁ then t₁ else t₂ fi [e₂]^ℓ₂`, then `next(t)`
is the only successor of `ℓ₂` in `flow(p)`. -/
theorem cfg_next_3 (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {t₁ t₂ : LStmt Label} {K : Label} (h : OccK P (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K) :
    (ℓ₂, K) ∈ P.flow ∧ ∀ x, (ℓ₂, x) ∈ P.flow → x = K :=
  ⟨h.exit_edge, fun _ hx => h.succ_ite hP hx⟩

/-- **Lemma "cfg-next" (4)**: if `t = from [e₁]^ℓ₁ do t₁ loop t₂ until [e₂]^ℓ₂`, then the
only successors of `ℓ₂` in `flow(p)` are `next(t)` and `entry(t₂)`, and
`next(t) ≠ entry(t₂)`. -/
theorem cfg_next_4 (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
    {t₁ t₂ : LStmt Label} {K : Label} (h : OccK P (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K) :
    (ℓ₂, K) ∈ P.flow ∧ (ℓ₂, t₂.entry) ∈ P.flow ∧
      (∀ x, (ℓ₂, x) ∈ P.flow → x = K ∨ x = t₂.entry) ∧ K ≠ t₂.entry := by
  refine ⟨h.exit_edge, h.flow_subset (by simp [LStmt.flow]), fun _ hx => h.succ_loop hP hx,
    fun hK => h.not_mem hP ?_⟩
  rw [hK, LStmt.labels_loop]
  simp [LStmt.entry_mem_labels]

/-- **Lemma "cfg-next" (5)**: if `[start]^a s [stop]^z` is the main program or the body of a
(possibly inverse) procedure of `p`, then `entry(s)` is the only successor of `a` in
`flow(p)`. -/
theorem cfg_next_5 (hP : P.UniqueLabels) {b s : LStmt Label} {a z : Label}
    (hb : b ∈ P.bodies) (hs : BodyShape b a s z) :
    (a, s.entry) ∈ P.flow ∧ ∀ x, (a, x) ∈ P.flow → x = s.entry :=
  ⟨hs.start_edge hb, fun _ hx => hs.start_succ hP hb hx⟩

/-! ### Figure "eqstack": the relation `π ∼stack^{ℓₙ,ℓₑ} π'` -/

/-- The relation `π ∼stack^{ℓₙ,ℓₑ} π'` of Figure "eqstack" between a small-step stack `π`
and a stack `π'` of the reversible semantics (`StackEquiv P π π' ℓₙ ℓₑ`). Once the
statement currently being executed has been completed, `ℓₙ` is the label of the next block
to be executed and `ℓₑ` the label of the last executed block. The premise "`next(t) = K`"
is `OccK P t K` (which includes the fact that `t` occurs in `P`), and the small-step
stack items contain the unlabeled versions (`LRepr`) of the labeled statements. -/
inductive StackEquiv (P : LProgram Label) : Stack → RStack → Label → Label → Prop
  /-- Rule `Nil`: `[start]^a s [stop]^z` is the main program; `[] ∼stack^{z,exit(s)} []`. -/
  | nil {a z : Label} {s : LStmt Label} :
      BodyShape P.main a s z → StackEquiv P [] [] z s.exit
  /-- Rule `Seq`: `(t₁ t₂)` occurs in `p` and `π ∼stack^{next(t₁ t₂),exit(t₂)} π'`;
  `seq(t₂) : π ∼stack^{entry(t₂),exit(t₁)} π'`. -/
  | seq {t₁ t₂ : LStmt Label} {s₂ : Stmt} {K : Label} {S : Stack} {S' : RStack} :
      OccK P (.seq t₁ t₂) K → LRepr t₂ s₂ → StackEquiv P S S' K t₂.exit →
      StackEquiv P (.seq s₂ :: S) S' t₂.entry t₁.exit
  /-- Rule `IfTrue`: `ctx(ℓ₂) = t = if [e₁]^ℓ₁ then t₁ else t₂ fi [e₂]^ℓ₂` and
  `π ∼stack^{next(t),ℓ₂} π'`;
  `if_true([e₂]^ℓ₂) : π ∼stack^{ℓ₂,exit(t₁)} if_true(ℓ₁,ℓ₂) : π'`. -/
  | ifTrue {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {K : Label} {S : Stack}
      {S' : RStack} :
      P.ctx ℓ₂ = some (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) → OccK P (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K →
      StackEquiv P S S' K ℓ₂ →
      StackEquiv P (.ifTrue e₂ :: S) (.ifTrue ℓ₁ ℓ₂ :: S') ℓ₂ t₁.exit
  /-- Rule `IfFalse`: `ctx(ℓ₂) = t = if [e₁]^ℓ₁ then t₁ else t₂ fi [e₂]^ℓ₂` and
  `π ∼stack^{next(t),ℓ₂} π'`;
  `if_false([e₂]^ℓ₂) : π ∼stack^{ℓ₂,exit(t₂)} if_false(ℓ₁,ℓ₂) : π'`. -/
  | ifFalse {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {K : Label} {S : Stack}
      {S' : RStack} :
      P.ctx ℓ₂ = some (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) → OccK P (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K →
      StackEquiv P S S' K ℓ₂ →
      StackEquiv P (.ifFalse e₂ :: S) (.ifFalse ℓ₁ ℓ₂ :: S') ℓ₂ t₂.exit
  /-- Rule `Loop1`: `ctx(ℓ₂) = t = from [e₁]^ℓ₁ do t₁ loop t₂ until [e₂]^ℓ₂` and
  `π ∼stack^{next(t),ℓ₂} π'`; `loop1([e₁]^ℓ₁,t₁,[e₂]^ℓ₂,t₂) : π ∼stack^{ℓ₂,exit(t₁)}
  loop1(ℓ₁,t₁,ℓ₂,t₂) : π'`. -/
  | loop1 {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {s₁ s₂ : Stmt} {K : Label}
      {S : Stack} {S' : RStack} :
      P.ctx ℓ₂ = some (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) → OccK P (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K →
      LRepr t₁ s₁ → LRepr t₂ s₂ → StackEquiv P S S' K ℓ₂ →
      StackEquiv P (.loop1 e₁ s₁ e₂ s₂ :: S) (.loop1 ℓ₁ t₁ ℓ₂ t₂ :: S') ℓ₂ t₁.exit
  /-- Rule `Loop2`: `ctx(ℓ₂) = t = from [e₁]^ℓ₁ do t₁ loop t₂ until [e₂]^ℓ₂` and
  `π ∼stack^{next(t),ℓ₂} π'`; `loop2([e₁]^ℓ₁,t₁,[e₂]^ℓ₂,t₂) : π ∼stack^{ℓ₁,exit(t₂)}
  loop2(ℓ₁,t₁,ℓ₂,t₂) : π'`. -/
  | loop2 {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {s₁ s₂ : Stmt} {K : Label}
      {S : Stack} {S' : RStack} :
      P.ctx ℓ₂ = some (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) → OccK P (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) K →
      LRepr t₁ s₁ → LRepr t₂ s₂ → StackEquiv P S S' K ℓ₂ →
      StackEquiv P (.loop2 e₁ s₁ e₂ s₂ :: S) (.loop2 ℓ₁ t₁ ℓ₂ t₂ :: S') ℓ₁ t₂.exit
  /-- Rule `Call`: `block(ℓ) = call id`, `Γ(id) = [start]^a s [stop]^z` and
  `π ∼stack^{next([call id]^ℓ),ℓ} π'`; `π ∼stack^{z,exit(s)} call(ℓ) : π'`. -/
  | call {id : ProcId} {ℓ K a z : Label} {b s : LStmt Label} {S : Stack} {S' : RStack} :
      P.block ℓ = some (.call id) → OccK P (.call id ℓ) K → P.proc (.fwd id) = some b →
      BodyShape b a s z → StackEquiv P S S' K ℓ → StackEquiv P S (.call ℓ :: S') z s.exit
  /-- Rule `UnCall`: `block(ℓ) = uncall id`, `Γ(id⁻¹) = [start]^a s [stop]^z` and
  `π ∼stack^{next([uncall id]^ℓ),ℓ} π'`; `π ∼stack^{z,exit(s)} uncall(ℓ) : π'`. -/
  | uncall {id : ProcId} {ℓ K a z : Label} {b s : LStmt Label} {S : Stack} {S' : RStack} :
      P.block ℓ = some (.uncall id) → OccK P (.uncall id ℓ) K → P.proc (.inv id) = some b →
      BodyShape b a s z → StackEquiv P S S' K ℓ → StackEquiv P S (.uncall ℓ :: S') z s.exit

/-! ### The relation `∼conf` -/

/-- The relation `c ∼conf k` between a configuration `c = ⟨σ, s, π⟩` of the small-step
semantics and a configuration `k = ⟨σ', ℓ₁, ℓ₂, π'⟩` of the reversible semantics: `σ = σ'`
and there are labels `ℓₙ`, `ℓₑ` with `π ∼stack^{ℓₙ,ℓₑ} π'` and either
(a) `s` is (the unlabeled version of) a statement occurring in `p` with `next(s) = ℓₙ`,
    `exit(s) = ℓₑ`, `ℓ₂ = entry(s)` and `ℓ₁ ∉ labels(s)`; or
(b) `s = skip`, `ℓ₁ = ℓₑ` and `ℓ₂ = ℓₙ`. -/
def ConfEquiv (P : LProgram Label) (c : SSConfig) (k : RConfig) : Prop :=
  c.store = k.store ∧ ∃ ℓn ℓe, StackEquiv P c.stack k.stack ℓn ℓe ∧
    ((∃ t, OccK P t ℓn ∧ LRepr t c.control ∧ t.exit = ℓe ∧ k.next = t.entry ∧
        k.last ∉ t.labels) ∨
      (c.control = .skip ∧ k.last = ℓe ∧ k.next = ℓn))

/-! ### Correspondence with the simulation relation of `ForwardEquiv` -/

variable {Γ : ProcEnv} {main : Stmt}

/-! ### Auxiliary facts on occurrences -/

/-- In a statement with unique labels, two sub-statements sharing a label are nested. -/
theorem LStmt.Occurs.nested {m t u : LStmt Label} (hn : m.labels.Nodup)
    (ht : LStmt.Occurs t m) (hu : LStmt.Occurs u m) {x : Label} (hxt : x ∈ t.labels)
    (hxu : x ∈ u.labels) : LStmt.Occurs t u ∨ LStmt.Occurs u t := by
  induction ht generalizing u with
  | refl => exact Or.inr hu
  | @ite₁ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h ih =>
    rw [LStmt.labels_ite] at hn
    obtain ⟨-, -, -, -, -, hd, hn₁, -⟩ := LStmt.nodup_cons_append3 hn
    cases hu with
    | refl => exact Or.inl (.ite₁ h)
    | ite₁ hu => exact ih hn₁ hu hxu
    | ite₂ hu => exact absurd (hu.labels_subset hxu) (hd _ (h.labels_subset hxt))
  | @ite₂ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h ih =>
    rw [LStmt.labels_ite] at hn
    obtain ⟨-, -, -, -, -, hd, -, hn₂⟩ := LStmt.nodup_cons_append3 hn
    cases hu with
    | refl => exact Or.inl (.ite₂ h)
    | ite₁ hu => exact absurd (h.labels_subset hxt) (hd _ (hu.labels_subset hxu))
    | ite₂ hu => exact ih hn₂ hu hxu
  | @loop₁ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h ih =>
    rw [LStmt.labels_loop] at hn
    obtain ⟨-, -, -, -, -, hd, hn₁, -⟩ := LStmt.nodup_cons_append3 hn
    cases hu with
    | refl => exact Or.inl (.loop₁ h)
    | loop₁ hu => exact ih hn₁ hu hxu
    | loop₂ hu => exact absurd (hu.labels_subset hxu) (hd _ (h.labels_subset hxt))
  | @loop₂ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h ih =>
    rw [LStmt.labels_loop] at hn
    obtain ⟨-, -, -, -, -, hd, -, hn₂⟩ := LStmt.nodup_cons_append3 hn
    cases hu with
    | refl => exact Or.inl (.loop₂ h)
    | loop₁ hu => exact absurd (h.labels_subset hxt) (hd _ (hu.labels_subset hxu))
    | loop₂ hu => exact ih hn₂ hu hxu
  | @seq₁ s₁ s₂ h ih =>
    rw [LStmt.labels_seq, List.nodup_append] at hn
    cases hu with
    | refl => exact Or.inl (.seq₁ h)
    | seq₁ hu => exact ih hn.1 hu hxu
    | seq₂ hu => exact absurd rfl (hn.2.2 _ (h.labels_subset hxt) _ (hu.labels_subset hxu))
  | @seq₂ s₁ s₂ h ih =>
    rw [LStmt.labels_seq, List.nodup_append] at hn
    cases hu with
    | refl => exact Or.inl (.seq₂ h)
    | seq₁ hu => exact absurd rfl (hn.2.2 _ (hu.labels_subset hxu) _ (h.labels_subset hxt))
    | seq₂ hu => exact ih hn.2.1 hu hxu

/-- If a sub-statement `v` of a statement `t` with unique labels contains the exit of `t`,
then it has the same exit. -/
theorem LStmt.Occurs.exit_eq {v t : LStmt Label} (hn : t.labels.Nodup)
    (h : LStmt.Occurs v t) (hx : t.exit ∈ v.labels) : v.exit = t.exit := by
  induction h with
  | refl => rfl
  | @ite₁ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h _ =>
    rw [LStmt.labels_ite] at hn
    exact absurd (h.labels_subset hx) (LStmt.nodup_cons_append3 hn).2.2.1
  | @ite₂ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h _ =>
    rw [LStmt.labels_ite] at hn
    exact absurd (h.labels_subset hx) (LStmt.nodup_cons_append3 hn).2.2.2.1
  | @loop₁ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h _ =>
    rw [LStmt.labels_loop] at hn
    exact absurd (h.labels_subset hx) (LStmt.nodup_cons_append3 hn).2.2.1
  | @loop₂ e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ h _ =>
    rw [LStmt.labels_loop] at hn
    exact absurd (h.labels_subset hx) (LStmt.nodup_cons_append3 hn).2.2.2.1
  | @seq₁ s₁ s₂ h _ =>
    rw [LStmt.labels_seq, List.nodup_append] at hn
    exact absurd rfl (hn.2.2 _ (h.labels_subset hx) _ (LStmt.exit_mem_labels s₂))
  | @seq₂ s₁ s₂ _ ih =>
    rw [LStmt.labels_seq, List.nodup_append] at hn
    exact ih hn.2.1 hx

/-- A statement with a continuation occurs in the statement `m` of a body `start m stop`. -/
theorem OccK.in_body {t : LStmt Label} {K : Label} (h : OccK P t K) :
    ∃ b a m z, b ∈ P.bodies ∧ BodyShape b a m z ∧ LStmt.Occurs t m := by
  induction h with
  | body hb hs => exact ⟨_, _, _, _, hb, hs, .refl _⟩
  | seqL _ ih =>
    obtain ⟨b, a, m, z, hb, hs, ho⟩ := ih; exact ⟨b, a, m, z, hb, hs, (LStmt.Occurs.seq₁ (.refl _)).trans ho⟩
  | seqR _ ih =>
    obtain ⟨b, a, m, z, hb, hs, ho⟩ := ih; exact ⟨b, a, m, z, hb, hs, (LStmt.Occurs.seq₂ (.refl _)).trans ho⟩
  | iteL _ ih =>
    obtain ⟨b, a, m, z, hb, hs, ho⟩ := ih; exact ⟨b, a, m, z, hb, hs, (LStmt.Occurs.ite₁ (.refl _)).trans ho⟩
  | iteR _ ih =>
    obtain ⟨b, a, m, z, hb, hs, ho⟩ := ih; exact ⟨b, a, m, z, hb, hs, (LStmt.Occurs.ite₂ (.refl _)).trans ho⟩
  | loopL _ ih =>
    obtain ⟨b, a, m, z, hb, hs, ho⟩ := ih; exact ⟨b, a, m, z, hb, hs, (LStmt.Occurs.loop₁ (.refl _)).trans ho⟩
  | loopR _ ih =>
    obtain ⟨b, a, m, z, hb, hs, ho⟩ := ih; exact ⟨b, a, m, z, hb, hs, (LStmt.Occurs.loop₂ (.refl _)).trans ho⟩

theorem BodyShape.inj {b m m' : LStmt Label} {a a' z z' : Label} (h : BodyShape b a m z)
    (h' : BodyShape b a' m' z') : m = m' := by
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> simp_all

/-- Two statements with a continuation and a common label occur in the same body. -/
theorem OccK.same_body (hP : P.UniqueLabels) {t u : LStmt Label} {K K' : Label}
    (ht : OccK P t K) (hu : OccK P u K') {x : Label} (hxt : x ∈ t.labels)
    (hxu : x ∈ u.labels) :
    ∃ m : LStmt Label, m.labels.Nodup ∧ LStmt.Occurs t m ∧ LStmt.Occurs u m := by
  obtain ⟨b, a, m, z, hb, hs, ho⟩ := ht.in_body
  obtain ⟨b', a', m', z', hb', hs', ho'⟩ := hu.in_body
  have h1 : x ∈ b.labels := by
    rw [hs.labels_eq]; exact List.mem_cons_of_mem _ (List.mem_append_left _ (ho.labels_subset hxt))
  have h2 : x ∈ b'.labels := by
    rw [hs'.labels_eq]; exact List.mem_cons_of_mem _ (List.mem_append_left _ (ho'.labels_subset hxu))
  obtain rfl := LProgram.eq_of_mem_labels hP hb hb' h1 h2
  obtain rfl := hs.inj hs'
  exact ⟨m, LProgram.nodup_labels_of_occurs hP ⟨b, hb, hs.occurs⟩, ho, ho'⟩

/-- A statement with a continuation whose exit is the exit of the statement `m` of a body
`start m stop` occurs in `m`. -/
theorem OccK.labels_subset_body (hP : P.UniqueLabels) {t : LStmt Label} {K : Label}
    (ht : OccK P t K) {b m : LStmt Label} {a z : Label} (hb : b ∈ P.bodies)
    (hs : BodyShape b a m z) (hE : t.exit = m.exit) : t.labels ⊆ m.labels := by
  obtain ⟨b', a', m', z', hb', hs', ho'⟩ := ht.in_body
  have h1 : m.exit ∈ b.labels := by
    rw [hs.labels_eq]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (LStmt.exit_mem_labels _))
  have h2 : m.exit ∈ b'.labels := by
    rw [hs'.labels_eq, ← hE]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (ho'.labels_subset (LStmt.exit_mem_labels _)))
  obtain rfl := LProgram.eq_of_mem_labels hP hb hb' h1 h2
  obtain rfl := hs.inj hs'
  exact ho'.labels_subset

/-- If `u` is a sub-statement of a statement `w` with a continuation, with a different exit,
then every statement `t` with a continuation and the same exit as `u` that is contained
in `w` only if it is contained in `u` occurs in `u`. -/
theorem OccK.labels_subset_child (hP : P.UniqueLabels) {t u w : LStmt Label} {K Kw : Label}
    (ht : OccK P t K) (hw : OccK P w Kw) (hu : LStmt.Occurs u w) (hne : w.exit ≠ u.exit)
    (hE : t.exit = u.exit) (hin : LStmt.Occurs t w → LStmt.Occurs t u) :
    t.labels ⊆ u.labels := by
  have hxw : t.exit ∈ w.labels := hu.labels_subset (hE ▸ LStmt.exit_mem_labels u)
  obtain ⟨m, hn, htm, hwm⟩ := ht.same_body hP hw (LStmt.exit_mem_labels t) hxw
  rcases htm.nested hn hwm (LStmt.exit_mem_labels t) hxw with h | h
  · exact (hin h).labels_subset
  · exact absurd ((h.exit_eq (hn.sublist htm.labels_sublist) hxw).trans hE) hne

/-- The labels `D` recorded by `StackCorr` contain the labels of every statement occurring
in `P` whose exit is the label `E` of the last executed block. -/
theorem StackCorr.labels_subset (hP : P.UniqueLabels) {S : Stack} {S' : RStack}
    {K E : Label} {D : List Label} (h : StackCorr P S S' K E D) {t : LStmt Label} {K' : Label}
    (ht : OccK P t K') (hE : t.exit = E) : t.labels ⊆ D := by
  cases h with
  | nil hs => exact ht.labels_subset_body hP P.main_mem_bodies hs hE
  | call _ _ hpb hs => exact ht.labels_subset_body hP (LProgram.mem_bodies_of_proc hpb) hs hE
  | uncall _ _ hpb hs => exact ht.labels_subset_body hP (LProgram.mem_bodies_of_proc hpb) hs hE
  | @seq t₁ t₂ s₂ K S S' D hK _ _ _ =>
    have hd := hK.not_mem_seq hP
    have hd' : t.exit ∉ t₂.labels := hE ▸ hd
    refine ht.labels_subset_child hP hK (.seq₁ (.refl _))
      (fun h => hd (h ▸ LStmt.exit_mem_labels _)) hE fun ho => ?_
    cases ho with
    | refl => exact absurd (LStmt.exit_mem_labels t₂) hd'
    | seq₁ h => exact h
    | seq₂ h => exact absurd (h.labels_subset (LStmt.exit_mem_labels _)) hd'
  | @ifTrue e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ K S S' D hK _ _ =>
    have hn := hK.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨-, -, h3, -, -, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ht.labels_subset_child hP hK (.ite₁ (.refl _))
      (fun h => h3 (by have := LStmt.exit_mem_labels t₁; rw [← h] at this; exact this)) hE fun ho => ?_
    have hm : t.exit ∈ t₁.labels := hE ▸ LStmt.exit_mem_labels _
    cases ho with
    | refl => exact absurd hm h3
    | ite₁ h => exact h
    | ite₂ h => exact absurd (h.labels_subset (LStmt.exit_mem_labels _)) (h6 _ hm)
  | @ifFalse e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ K S S' D hK _ _ =>
    have hn := hK.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨-, -, -, h4, -, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ht.labels_subset_child hP hK (.ite₂ (.refl _))
      (fun h => h4 (by have := LStmt.exit_mem_labels t₂; rw [← h] at this; exact this)) hE fun ho => ?_
    have hm : t.exit ∈ t₂.labels := hE ▸ LStmt.exit_mem_labels _
    cases ho with
    | refl => exact absurd hm h4
    | ite₁ h => exact absurd hm (h6 _ (h.labels_subset (LStmt.exit_mem_labels _)))
    | ite₂ h => exact h
  | @loop1 e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ K S S' D hK _ _ _ _ =>
    have hn := hK.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨-, -, h3, -, -, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ht.labels_subset_child hP hK (.loop₁ (.refl _))
      (fun h => h3 (by have := LStmt.exit_mem_labels t₁; rw [← h] at this; exact this)) hE fun ho => ?_
    have hm : t.exit ∈ t₁.labels := hE ▸ LStmt.exit_mem_labels _
    cases ho with
    | refl => exact absurd hm h3
    | loop₁ h => exact h
    | loop₂ h => exact absurd (h.labels_subset (LStmt.exit_mem_labels _)) (h6 _ hm)
  | @loop2 e₁ e₂ ℓ₁ ℓ₂ t₁ t₂ s₁ s₂ K S S' D hK _ _ _ _ =>
    have hn := hK.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨-, -, -, h4, -, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ht.labels_subset_child hP hK (.loop₂ (.refl _))
      (fun h => h4 (by have := LStmt.exit_mem_labels t₂; rw [← h] at this; exact this)) hE fun ho => ?_
    have hm : t.exit ∈ t₂.labels := hE ▸ LStmt.exit_mem_labels _
    cases ho with
    | refl => exact absurd hm h4
    | loop₁ h => exact absurd hm (h6 _ (h.labels_subset (LStmt.exit_mem_labels _)))
    | loop₂ h => exact h

theorem StackCorr.toStackEquiv (hW : FwdWF P Γ main) {S : Stack} {S' : RStack}
    {K E : Label} {D : List Label} (h : StackCorr P S S' K E D) : StackEquiv P S S' K E := by
  have hP := hW.unique
  induction h with
  | nil hs => exact .nil hs
  | seq hK hr _ _ ih => exact .seq hK hr ih
  | ifTrue hK _ _ ih => exact .ifTrue (hK.ctx_ite hP).2 hK ih
  | ifFalse hK _ _ ih => exact .ifFalse (hK.ctx_ite hP).2 hK ih
  | loop1 hK hr₁ hr₂ _ _ ih => exact .loop1 (hK.ctx_loop hP).2 hK hr₁ hr₂ ih
  | loop2 hK hr₁ hr₂ _ _ ih => exact .loop2 (hK.ctx_loop hP).2 hK hr₁ hr₂ ih
  | call hK _ hpb hs ih => exact .call (hK.block hP (by simp [LStmt.blocks])) hK hpb hs ih
  | uncall hK _ hpb hs ih => exact .uncall (hK.block hP (by simp [LStmt.blocks])) hK hpb hs ih

theorem StackEquiv.toStackCorr (hW : FwdWF P Γ main) {S : Stack} {S' : RStack}
    {K E : Label} (h : StackEquiv P S S' K E) : ∃ D, StackCorr P S S' K E D := by
  have hP := hW.unique
  induction h with
  | nil hs => exact ⟨_, .nil hs⟩
  | seq hK hr _ ih =>
    obtain ⟨D, hD⟩ := ih; exact ⟨_, .seq hK hr hD (hD.labels_subset hP hK rfl)⟩
  | ifTrue _ hK _ ih =>
    obtain ⟨D, hD⟩ := ih; exact ⟨_, .ifTrue hK hD (hD.labels_subset hP hK rfl)⟩
  | ifFalse _ hK _ ih =>
    obtain ⟨D, hD⟩ := ih; exact ⟨_, .ifFalse hK hD (hD.labels_subset hP hK rfl)⟩
  | loop1 _ hK hr₁ hr₂ _ ih =>
    obtain ⟨D, hD⟩ := ih; exact ⟨_, .loop1 hK hr₁ hr₂ hD (hD.labels_subset hP hK rfl)⟩
  | loop2 _ hK hr₁ hr₂ _ ih =>
    obtain ⟨D, hD⟩ := ih; exact ⟨_, .loop2 hK hr₁ hr₂ hD (hD.labels_subset hP hK rfl)⟩
  | call _ hK hpb hs _ ih => obtain ⟨D, hD⟩ := ih; exact ⟨_, .call hK hD hpb hs⟩
  | uncall _ hK hpb hs _ ih => obtain ⟨D, hD⟩ := ih; exact ⟨_, .uncall hK hD hpb hs⟩

theorem corr_iff_confEquiv (hW : FwdWF P Γ main) {c : SSConfig} {k : RConfig} :
    Corr P c k ↔ ConfEquiv P c k := by
  constructor
  · rintro ⟨hσ, K, E, D, hS, hctl⟩
    refine ⟨hσ, K, E, hS.toStackEquiv hW, ?_⟩
    rcases hctl with ⟨t, h1, h2, h3, h4, h5, -⟩ | h
    · exact Or.inl ⟨t, h1, h2, h3, h4, h5⟩
    · exact Or.inr h
  · rintro ⟨hσ, K, E, hS, hctl⟩
    obtain ⟨D, hD⟩ := hS.toStackCorr hW
    refine ⟨hσ, K, E, D, hD, ?_⟩
    rcases hctl with ⟨t, h1, h2, h3, h4, h5⟩ | h
    · exact Or.inl ⟨t, h1, h2, h3, h4, h5, hD.labels_subset hW.unique h1 h3⟩
    · exact Or.inr h

/-! ### The proof of Lemma "forward-rev" with `∼conf` -/

/-- First paragraph of the proof: the initial configurations are related,
`⟨ε, s, []⟩ ∼conf ⟨ε, a, ℓ, []⟩`. -/
theorem ConfEquiv.init (hW : FwdWF P Γ main) {ℓ : Label}
    (hℓ : (P.main.entry, ℓ) ∈ P.mainCFG) :
    ConfEquiv P ⟨Store.empty, main, []⟩ ⟨Store.empty, P.main.entry, ℓ, []⟩ :=
  (corr_iff_confEquiv hW).1 (corr_init hW hℓ)

/-- The (⇒) direction: if `c₁ ∼conf k₁` and `c₁ → c₂`, then `k₁ ⇀* k₂` and `c₂ ∼conf k₂`
for some `k₂`. -/
theorem ConfEquiv.fwd_sim (hW : FwdWF P Γ main) {c₁ c₂ : SSConfig} {k₁ : RConfig}
    (h : ConfEquiv P c₁ k₁) (hc : SmallStep Γ c₁ c₂) :
    ∃ k₂, FwdSteps P k₁ k₂ ∧ ConfEquiv P c₂ k₂ := by
  obtain ⟨k₂, hk, hc₂⟩ := Janus.fwd_sim hW ((corr_iff_confEquiv hW).2 h) hc
  exact ⟨k₂, hk, (corr_iff_confEquiv hW).1 hc₂⟩

/-- The (⇐) direction: if `c₁ ∼conf k₁` and `k₁ ⇀ k₂`, then `c₁ →* c₂` and `c₂ ∼conf k₂`
for some `c₂`. -/
theorem ConfEquiv.back_sim (hW : FwdWF P Γ main) {c₁ : SSConfig} {k₁ k₂ : RConfig}
    (h : ConfEquiv P c₁ k₁) (hk : FwdStep P k₁ k₂) :
    ∃ c₂, SmallSteps Γ c₁ c₂ ∧ ConfEquiv P c₂ k₂ := by
  obtain ⟨c₂, hc, hc₂⟩ := Janus.back_sim hW ((corr_iff_confEquiv hW).2 h) hk
  exact ⟨c₂, hc, (corr_iff_confEquiv hW).1 hc₂⟩

/-- "Finally, …" paragraph of the (⇒) direction: if `⟨σ, skip, []⟩ ∼conf k`, then, after
the remaining administrative steps, `k ⇀* ⟨σ, ℓ', ℓ'', []⟩` with `block(ℓ'') = stop`. -/
theorem ConfEquiv.final_fwd (hW : FwdWF P Γ main) {σ : Store} {k : RConfig}
    (h : ConfEquiv P ⟨σ, .skip, []⟩ k) :
    ∃ k', FwdSteps P k k' ∧ k'.store = σ ∧ k'.stack = [] ∧ P.block k'.next = some .stop :=
  fwd_final hW ((corr_iff_confEquiv hW).2 h)

/-- "Finally, …" paragraph of the (⇐) direction: if `c ∼conf ⟨σ, ℓ', ℓ'', []⟩` with
`block(ℓ'') = stop`, then `c = ⟨σ, skip, []⟩`. -/
theorem ConfEquiv.final_back (hW : FwdWF P Γ main) {c : SSConfig} {σ : Store}
    {ℓ' ℓ'' : Label} (h : ConfEquiv P c ⟨σ, ℓ', ℓ'', []⟩) (hb : P.block ℓ'' = some .stop) :
    c = ⟨σ, .skip, []⟩ :=
  back_final hW ((corr_iff_confEquiv hW).2 h) hb

theorem ConfEquiv.fwd_sims (hW : FwdWF P Γ main) {c₁ c₂ : SSConfig} {k₁ : RConfig}
    (h : ConfEquiv P c₁ k₁) (hc : SmallSteps Γ c₁ c₂) :
    ∃ k₂, FwdSteps P k₁ k₂ ∧ ConfEquiv P c₂ k₂ := by
  induction hc with
  | refl => exact ⟨k₁, .refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨k, h₁, h₁'⟩ := ih
    obtain ⟨k₂, h₂, h₂'⟩ := h₁'.fwd_sim hW hstep
    exact ⟨k₂, h₁.trans h₂, h₂'⟩

theorem ConfEquiv.back_sims (hW : FwdWF P Γ main) {c₁ : SSConfig} {k₁ k₂ : RConfig}
    (h : ConfEquiv P c₁ k₁) (hk : FwdSteps P k₁ k₂) :
    ∃ c₂, SmallSteps Γ c₁ c₂ ∧ ConfEquiv P c₂ k₂ := by
  induction hk with
  | refl => exact ⟨c₁, .refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨c, h₁, h₁'⟩ := ih
    obtain ⟨c₂, h₂, h₂'⟩ := h₁'.back_sim hW hstep
    exact ⟨c₂, h₁.trans h₂, h₂'⟩

/-- Lemma "forward-rev", proved with the paper's relation `∼conf` (same statement as
`smallSteps_iff_fwdSteps`). -/
theorem ConfEquiv.smallSteps_iff_fwdSteps (hW : FwdWF P Γ main) {ℓ : Label}
    (hℓ : (P.main.entry, ℓ) ∈ P.mainCFG) (σ : Store) :
    SmallSteps Γ ⟨Store.empty, main, []⟩ ⟨σ, .skip, []⟩ ↔
      ∃ ℓ' ℓ'', FwdSteps P ⟨Store.empty, P.main.entry, ℓ, []⟩ ⟨σ, ℓ', ℓ'', []⟩ ∧
        P.block ℓ'' = some .stop := by
  constructor
  · intro h
    obtain ⟨k, hk, hc⟩ := (ConfEquiv.init hW hℓ).fwd_sims hW h
    obtain ⟨⟨σ', ℓ', ℓ'', S'⟩, hk', rfl, rfl, hb⟩ := hc.final_fwd hW
    exact ⟨ℓ', ℓ'', hk.trans hk', hb⟩
  · rintro ⟨ℓ', ℓ'', hk, hb⟩
    obtain ⟨c, hc, hconf⟩ := (ConfEquiv.init hW hℓ).back_sims hW hk
    rw [← hconf.final_back hW hb]
    exact hc

end Janus

end
