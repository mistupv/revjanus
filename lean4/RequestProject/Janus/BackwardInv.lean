module

public import RequestProject.Janus.Backward
public import RequestProject.Janus.ForwardPaper

/-!
# Janus: an invariant of the reachable configurations of the reversible semantics

Auxiliary material for the proof of the loop lemma (`RequestProject.Janus.LoopLemma`).

* `RevWF P`: the well-formedness conditions on labeled programs assumed by the loop lemma
  (unique labels; every body is `start m stop` where `m` is a labeled version of a
  well-formed statement of the original syntax).
* `StkInv P S t pr K` and `RInv P k`: an invariant satisfied by every reachable configuration
  `k` (`LProgram.Reachable.rInv`). It records, for the current level of the stack, a
  statement `t` (a body `m` of `start m stop`, or a branch of a conditional or loop),
  the label `pr` of the block executed just before `t` and the label `K` of the block
  executed just after `t`; the two labels of the configuration are the ends of an edge of
  `flow(t)`, or the edge `(pr, entry(t))`, or the edge `(exit(t), K)`. Each stack item
  is consistent with the statement of the level below it.
-/

@[expose] public section

namespace Janus

variable {P : LProgram Label}

/-! ### Well-formed labeled programs -/

/-- The well-formedness conditions assumed by the loop lemma: labels are unique, and every
body (main program, procedures and inverse procedures) has the form `start m stop`, where `m`
is a labeled version of a well-formed statement of the original syntax (so that `m` contains
neither `start` nor `stop`, and in every assignment `x ⊕= e` the variable `x` does not occur
in `e`). -/
structure RevWF (P : LProgram Label) : Prop where
  unique : P.UniqueLabels
  bodies : ∀ b ∈ P.bodies, ∃ a m z s, BodyShape b a m z ∧ LRepr m s ∧ s.WellFormed

/-! ### Basic facts -/

theorem LRepr.block_ne {m : LStmt Label} {s : Stmt} (h : LRepr m s) {ℓ : Label} {o : Block}
    (hm : (ℓ, o) ∈ m.blocks) : o ≠ .start ∧ o ≠ .stop := by
  induction h generalizing ℓ o with
  | ite _ _ ih₁ ih₂ | loop _ _ ih₁ ih₂ =>
    simp only [LStmt.blocks, List.mem_cons, List.mem_append, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨-, rfl⟩ | (hm | hm) | ⟨-, rfl⟩
    · simp
    · exact ih₁ hm
    · exact ih₂ hm
    · simp
  | seq _ _ ih₁ ih₂ =>
    simp only [LStmt.blocks, List.mem_append] at hm
    rcases hm with hm | hm
    · exact ih₁ hm
    · exact ih₂ hm
  | _ => simp_all [LStmt.blocks]

theorem LRepr.assVar_wf {m : LStmt Label} {s : Stmt} (h : LRepr m s) (hs : s.WellFormed)
    {ℓ : Label} {x : Var} {op : ModOp} {e : Expr} (hm : (ℓ, .assVar x op e) ∈ m.blocks) :
    x ∉ e.vars := by
  induction h generalizing ℓ with
  | ite _ _ ih₁ ih₂ | loop _ _ ih₁ ih₂ =>
    simp only [LStmt.blocks, List.mem_cons, List.mem_append, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨-, h⟩ | (hm | hm) | ⟨-, h⟩
    · cases h
    · exact ih₁ hs.1 hm
    · exact ih₂ hs.2 hm
    · cases h
  | seq _ _ ih₁ ih₂ =>
    simp only [LStmt.blocks, List.mem_append] at hm
    rcases hm with hm | hm
    · exact ih₁ hs.1 hm
    · exact ih₂ hs.2 hm
  | assVar =>
    simp only [LStmt.blocks, List.mem_singleton, Prod.mk.injEq, Block.assVar.injEq] at hm
    obtain ⟨-, rfl, -, rfl⟩ := hm
    exact hs
  | _ => simp_all [LStmt.blocks]

theorem LRepr.assArr_wf {m : LStmt Label} {s : Stmt} (h : LRepr m s) (hs : s.WellFormed)
    {ℓ : Label} {x : Var} {e₁ : Expr} {op : ModOp} {e₂ : Expr}
    (hm : (ℓ, .assArr x e₁ op e₂) ∈ m.blocks) : x ∉ e₁.vars ∧ x ∉ e₂.vars := by
  induction h generalizing ℓ with
  | ite _ _ ih₁ ih₂ | loop _ _ ih₁ ih₂ =>
    simp only [LStmt.blocks, List.mem_cons, List.mem_append, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨-, h⟩ | (hm | hm) | ⟨-, h⟩
    · cases h
    · exact ih₁ hs.1 hm
    · exact ih₂ hs.2 hm
    · cases h
  | seq _ _ ih₁ ih₂ =>
    simp only [LStmt.blocks, List.mem_append] at hm
    rcases hm with hm | hm
    · exact ih₁ hs.1 hm
    · exact ih₂ hs.2 hm
  | assArr =>
    simp only [LStmt.blocks, List.mem_singleton, Prod.mk.injEq, Block.assArr.injEq] at hm
    obtain ⟨-, rfl, rfl, -, rfl⟩ := hm
    exact hs
  | _ => simp_all [LStmt.blocks]

theorem BodyShape.blocks_eq {b m : LStmt Label} {a z : Label} (h : BodyShape b a m z) :
    b.blocks = (a, .start) :: (m.blocks ++ [(z, .stop)]) := by
  rcases h with rfl | rfl <;> simp [LStmt.blocks]

theorem BodyShape.start_block {b m : LStmt Label} {a z : Label} (hP : P.UniqueLabels)
    (hb : b ∈ P.bodies) (hs : BodyShape b a m z) : P.block a = some .start :=
  LProgram.block_of_occurs hP ⟨_, hb, .refl _⟩ (by rw [hs.blocks_eq]; simp)

namespace RevWF

variable (hW : RevWF P)
include hW

/-- A block of a body that is neither `start` nor `stop` comes from the statement `m` of
the body `start m stop`. -/
theorem block_mem {ℓ : Label} {o : Block} (h : P.block ℓ = some o) (h1 : o ≠ .start)
    (h2 : o ≠ .stop) : ∃ b a m z s, b ∈ P.bodies ∧ BodyShape b a m z ∧ LRepr m s ∧
      s.WellFormed ∧ (ℓ, o) ∈ m.blocks := by
  have h' := (LProgram.block_eq_some_iff hW.unique ℓ o).1 h
  rw [LProgram.blocks_eq_flatMap, List.mem_flatMap] at h'
  obtain ⟨b, hb, hm⟩ := h'
  obtain ⟨a, m, z, s, hs, hr, hwf⟩ := hW.bodies b hb
  rw [hs.blocks_eq] at hm
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨-, rfl⟩ | hm | ⟨-, rfl⟩
  · exact absurd rfl h1
  · exact ⟨b, a, m, z, s, hb, hs, hr, hwf, hm⟩
  · exact absurd rfl h2

/-- In every assignment `x ⊕= e` of the program, `x` does not occur in `e`. -/
theorem assVar_wf {ℓ : Label} {x : Var} {op : ModOp} {e : Expr}
    (h : P.block ℓ = some (.assVar x op e)) : x ∉ e.vars := by
  obtain ⟨b, a, m, z, s, -, -, hr, hwf, hm⟩ := hW.block_mem h (by simp) (by simp)
  exact hr.assVar_wf hwf hm

/-- In every assignment `x[e₁] ⊕= e₂` of the program, `x` does not occur in `e₁` and `e₂`. -/
theorem assArr_wf {ℓ : Label} {x : Var} {e₁ : Expr} {op : ModOp} {e₂ : Expr}
    (h : P.block ℓ = some (.assArr x e₁ op e₂)) : x ∉ e₁.vars ∧ x ∉ e₂.vars := by
  obtain ⟨b, a, m, z, s, -, -, hr, hwf, hm⟩ := hW.block_mem h (by simp) (by simp)
  exact hr.assArr_wf hwf hm

/-- The blocks of a body `start m stop`: `start`, `stop`, and the blocks of `m` (which are
neither `start` nor `stop`). -/
theorem body_block {b m : LStmt Label} {a z ℓ : Label} {o : Block} (hb : b ∈ P.bodies)
    (hs : BodyShape b a m z) (hℓ : ℓ ∈ b.labels) (hblk : P.block ℓ = some o) :
    (ℓ = a ∧ o = .start) ∨ (ℓ = z ∧ o = .stop) ∨ (ℓ ∈ m.labels ∧ o ≠ .start ∧ o ≠ .stop) := by
  obtain ⟨a', m', z', s', hs', hr', -⟩ := hW.bodies b hb
  obtain rfl := hs.inj hs'
  rw [hs.labels_eq] at hℓ
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | hℓ | rfl
  · left; refine ⟨rfl, ?_⟩
    rw [hs.start_block hW.unique hb] at hblk; exact (Option.some.inj hblk).symm
  · right; right
    obtain ⟨⟨_, o'⟩, hm, rfl⟩ := List.mem_map.1 hℓ
    have := LProgram.block_of_occurs hW.unique ⟨b, hb, hs.occurs⟩ hm
    rw [hblk] at this; cases this
    exact ⟨hℓ, hr'.block_ne hm⟩
  · right; left; refine ⟨rfl, ?_⟩
    rw [hs.stop_block hW.unique hb] at hblk; exact (Option.some.inj hblk).symm

end RevWF

/-! ### Predecessors in the CFG -/

/-- The edges of `flow(p)` entering the statement `m` of a body `start m stop` are those of
`flow(m)` and the edge `(start, entry(m))`. -/
theorem BodyShape.pred {b m : LStmt Label} {a z : Label} (hP : P.UniqueLabels)
    (hb : b ∈ P.bodies) (hs : BodyShape b a m z) {x y : Label} (hxy : (x, y) ∈ P.flow)
    (hy : y ∈ m.labels) : (x, y) ∈ m.flow ∨ (x = a ∧ y = m.entry) := by
  obtain ⟨b', hb', hx⟩ := LProgram.mem_flow.1 hxy
  have hyb : y ∈ b.labels :=
    hs.labels_eq ▸ List.mem_cons_of_mem _ (List.mem_append_left _ hy)
  obtain rfl := LProgram.eq_of_mem_labels hP hb hb' hyb (LStmt.mem_labels_of_edge hx).2
  have hn := LProgram.nodup_labels_of_occurs hP ⟨_, hb, .refl _⟩
  rw [hs.labels_eq, List.nodup_cons, List.nodup_append] at hn
  have hz : z ∉ m.labels := fun h' => hn.2.2.2 z h' z (by simp) rfl
  rcases hs.mem_flow.1 hx with h | h | h
  · simp only [Prod.mk.injEq] at h; exact Or.inr h
  · simp only [Prod.mk.injEq] at h; exact absurd (h.2 ▸ hy) hz
  · exact Or.inl h

namespace OccK

variable {t : LStmt Label} {K : Label}

/-- The edges of `flow(p)` entering a statement `t` with a continuation are the edges of
`flow(t)` and edges into `entry(t)`. -/
theorem pred (hP : P.UniqueLabels) (h : OccK P t K) {x y : Label} (hxy : (x, y) ∈ P.flow)
    (hy : y ∈ t.labels) : (x, y) ∈ t.flow ∨ y = t.entry := by
  induction h with
  | body hb hs =>
    rcases hs.pred hP hb hxy hy with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  | @seqL s₁ s₂ K h ih =>
    have hn := h.nodup hP
    rw [LStmt.labels_seq, List.nodup_append] at hn
    have hd : ∀ y ∈ s₁.labels, y ∉ s₂.labels := fun y hy hy' => hn.2.2 y hy y hy' rfl
    rcases ih (by rw [LStmt.labels_seq]; exact List.mem_append_left _ hy) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with (⟨-, rfl⟩ | hx) | hx
      · exact absurd (LStmt.entry_mem_labels _) (hd _ hy)
      · exact Or.inl hx
      · exact absurd (LStmt.mem_labels_of_edge hx).2 (hd _ hy)
    · exact Or.inr hx
  | @seqR s₁ s₂ K h ih =>
    have hn := h.nodup hP
    rw [LStmt.labels_seq, List.nodup_append] at hn
    have hd : ∀ y ∈ s₂.labels, y ∉ s₁.labels := fun y hy hy' => hn.2.2 y hy' y hy rfl
    rcases ih (by rw [LStmt.labels_seq]; exact List.mem_append_right _ hy) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with (⟨-, rfl⟩ | hx) | hx
      · exact Or.inr rfl
      · exact absurd (LStmt.mem_labels_of_edge hx).2 (hd _ hy)
      · exact Or.inl hx
    · simp only [LStmt.entry] at hx; subst hx
      exact absurd (LStmt.entry_mem_labels _) (hd _ hy)
  | @iteL e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_ite]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨-, rfl⟩ | ⟨-, rfl⟩) | (⟨-, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact Or.inr rfl
      · exact absurd hy h3
      · exact absurd (LStmt.entry_mem_labels _) (h6 _ hy)
      · exact absurd hy h3
      · exact Or.inl hx
      · exact absurd (LStmt.mem_labels_of_edge hx).2 (h6 _ hy)
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h1
  | @iteR e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_ite]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨-, rfl⟩ | ⟨-, rfl⟩) | (⟨-, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact absurd hy (h6 _ (LStmt.entry_mem_labels _))
      · exact absurd hy h4
      · exact Or.inr rfl
      · exact absurd hy h4
      · exact absurd hy (h6 _ (LStmt.mem_labels_of_edge hx).2)
      · exact Or.inl hx
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h2
  | @loopL e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_loop]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨-, rfl⟩ | ⟨-, rfl⟩) | (⟨-, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact Or.inr rfl
      · exact absurd hy h3
      · exact absurd (LStmt.entry_mem_labels _) (h6 _ hy)
      · exact absurd hy h1
      · exact Or.inl hx
      · exact absurd (LStmt.mem_labels_of_edge hx).2 (h6 _ hy)
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h1
  | @loopR e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_loop]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨-, rfl⟩ | ⟨-, rfl⟩) | (⟨-, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact absurd hy (h6 _ (LStmt.entry_mem_labels _))
      · exact absurd hy h4
      · exact Or.inr rfl
      · exact absurd hy h2
      · exact absurd hy (h6 _ (LStmt.mem_labels_of_edge hx).2)
      · exact Or.inl hx
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h2

/-- A sub-statement of a statement with a continuation has a continuation. -/
theorem of_occurs (h : OccK P t K) {u : LStmt Label} (hu : LStmt.Occurs u t) :
    ∃ K', OccK P u K' := by
  induction hu generalizing K with
  | refl => exact ⟨K, h⟩
  | ite₁ _ ih => exact ih h.iteL
  | ite₂ _ ih => exact ih h.iteR
  | loop₁ _ ih => exact ih h.loopL
  | loop₂ _ ih => exact ih h.loopR
  | seq₁ _ ih => exact ih h.seqL
  | seq₂ _ ih => exact ih h.seqR

end OccK

/-- If a sub-statement `t` of a conditional or loop `u` with unique labels contains the label
of the test or assertion of `u`, then `t = u`. -/
theorem LStmt.Occurs.eq_of_cond {t u : LStmt Label} (hn : u.labels.Nodup)
    (h : LStmt.Occurs t u) {ℓ : Label} (hl : ℓ ∈ u.condLabels) (ht : ℓ ∈ t.labels) : t = u := by
  cases h with
  | refl => rfl
  | ite₁ h | loop₁ h =>
    first | rw [LStmt.labels_ite] at hn | rw [LStmt.labels_loop] at hn
    obtain ⟨h1, -, h3, -⟩ := LStmt.nodup_cons_append3 hn
    simp only [LStmt.condLabels, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact absurd (h.labels_subset ht) h1
    · exact absurd (h.labels_subset ht) h3
  | ite₂ h | loop₂ h =>
    first | rw [LStmt.labels_ite] at hn | rw [LStmt.labels_loop] at hn
    obtain ⟨-, h2, -, h4, -⟩ := LStmt.nodup_cons_append3 hn
    simp only [LStmt.condLabels, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact absurd (h.labels_subset ht) h2
    · exact absurd (h.labels_subset ht) h4
  | seq₁ h | seq₂ h => simp [LStmt.condLabels] at hl

/-- If `ctx(ℓ) = u` and `ℓ` is a label of a statement `t` with a continuation, then `u` is a
sub-statement of `t`. -/
theorem OccK.occurs_of_ctx (hP : P.UniqueLabels) {t : LStmt Label} {K : Label}
    (ht : OccK P t K) {ℓ : Label} {u : LStmt Label} (hc : P.ctx ℓ = some u)
    (hℓ : ℓ ∈ t.labels) : LStmt.Occurs u t := by
  obtain ⟨⟨b', hb', hub⟩, hl⟩ := LProgram.ctx_some hc
  obtain ⟨b, a, m, z, hb, hs, htm⟩ := ht.in_body
  have hℓb : ℓ ∈ b.labels :=
    hs.labels_eq ▸ List.mem_cons_of_mem _ (List.mem_append_left _ (htm.labels_subset hℓ))
  have hℓb' : ℓ ∈ b'.labels := hub.labels_subset (LStmt.condLabels_subset _ hl)
  obtain rfl := LProgram.eq_of_mem_labels hP hb hb' hℓb hℓb'
  have hn : b.labels.Nodup := LProgram.nodup_labels_of_occurs hP ⟨b, hb, .refl _⟩
  have htb : LStmt.Occurs t b := htm.trans hs.occurs
  rcases htb.nested hn hub hℓ (LStmt.condLabels_subset _ hl) with h | h
  · obtain rfl := h.eq_of_cond (hn.sublist hub.labels_sublist) hl hℓ
    exact .refl _
  · exact h

/-! ### The invariant -/

/-- `EdgeIn t pr K x y`: `(x, y)` is an edge of `flow(t)`, or the edge `(pr, entry(t))`, or
the edge `(exit(t), K)`. -/
def EdgeIn (t : LStmt Label) (pr K x y : Label) : Prop :=
  (x, y) ∈ t.flow ∨ (x = pr ∧ y = t.entry) ∨ (x = t.exit ∧ y = K)

/-- `StkInv P S t pr K`: the stack `S` of the reversible semantics is consistent, and the
current level of the stack runs the statement `t`, preceded by the block `pr` and followed
by the block `K`. -/
inductive StkInv (P : LProgram Label) : RStack → LStmt Label → Label → Label → Prop
  | nil {b m : LStmt Label} {a z : Label} :
      b ∈ P.bodies → BodyShape b a m z → StkInv P [] m a z
  | call {S : RStack} {t : LStmt Label} {pr K ℓc : Label} {id : ProcId} {b m : LStmt Label}
      {a z : Label} :
      StkInv P S t pr K → ℓc ∈ t.labels → P.block ℓc = some (.call id) →
      P.proc (.fwd id) = some b → BodyShape b a m z → StkInv P (.call ℓc :: S) m a z
  | uncall {S : RStack} {t : LStmt Label} {pr K ℓc : Label} {id : ProcId} {b m : LStmt Label}
      {a z : Label} :
      StkInv P S t pr K → ℓc ∈ t.labels → P.block ℓc = some (.uncall id) →
      P.proc (.inv id) = some b → BodyShape b a m z → StkInv P (.uncall ℓc :: S) m a z
  | ifTrue {S : RStack} {t : LStmt Label} {pr K : Label} {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
      {s₁ s₂ : LStmt Label} :
      StkInv P S t pr K → LStmt.Occurs (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) t →
      StkInv P (.ifTrue ℓ₁ ℓ₂ :: S) s₁ ℓ₁ ℓ₂
  | ifFalse {S : RStack} {t : LStmt Label} {pr K : Label} {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
      {s₁ s₂ : LStmt Label} :
      StkInv P S t pr K → LStmt.Occurs (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) t →
      StkInv P (.ifFalse ℓ₁ ℓ₂ :: S) s₂ ℓ₁ ℓ₂
  | loop1 {S : RStack} {t : LStmt Label} {pr K : Label} {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
      {s₁ s₂ : LStmt Label} :
      StkInv P S t pr K → LStmt.Occurs (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) t →
      StkInv P (.loop1 ℓ₁ s₁ ℓ₂ s₂ :: S) s₁ ℓ₁ ℓ₂
  | loop2 {S : RStack} {t : LStmt Label} {pr K : Label} {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label}
      {s₁ s₂ : LStmt Label} :
      StkInv P S t pr K → LStmt.Occurs (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) t →
      StkInv P (.loop2 ℓ₁ s₁ ℓ₂ s₂ :: S) s₂ ℓ₂ ℓ₁

/-- The invariant of reachable configurations. -/
def RInv (P : LProgram Label) (k : RConfig) : Prop :=
  ∃ t pr K, StkInv P k.stack t pr K ∧ EdgeIn t pr K k.last k.next

/-- The properties of a level `(t, pr, K)` of a consistent stack. -/
structure FrameOK (P : LProgram Label) (t : LStmt Label) (pr K : Label) : Prop where
  occK : OccK P t K
  pr_not_mem : pr ∉ t.labels
  pr_edge : (pr, t.entry) ∈ P.flow
  pred : ∀ x y, (x, y) ∈ P.flow → y ∈ t.labels → (x, y) ∈ t.flow ∨ (x = pr ∧ y = t.entry)

theorem FrameOK.body {b m : LStmt Label} {a z : Label} (hP : P.UniqueLabels)
    (hb : b ∈ P.bodies) (hs : BodyShape b a m z) : FrameOK P m a z :=
  ⟨.body hb hs, hs.start_not_mem hP hb, hs.start_edge hb, fun _ _ hxy hy => hs.pred hP hb hxy hy⟩

theorem StkInv.frame (hP : P.UniqueLabels) {S : RStack} {t : LStmt Label} {pr K : Label}
    (h : StkInv P S t pr K) : FrameOK P t pr K := by
  induction h with
  | nil hb hs => exact .body hP hb hs
  | call _ _ _ hpb hs => exact .body hP (LProgram.mem_bodies_of_proc hpb) hs
  | uncall _ _ _ hpb hs => exact .body hP (LProgram.mem_bodies_of_proc hpb) hs
  | @ifTrue S t pr K e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ _ hu ih =>
    obtain ⟨K', hK⟩ := ih.occK.of_occurs hu
    have hn := hK.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ⟨hK.iteL, h1, hK.flow_subset (by simp [LStmt.flow]), fun x y hxy hy => ?_⟩
    rcases hK.pred hP hxy (by rw [LStmt.labels_ite]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨rfl, rfl⟩ | ⟨-, rfl⟩) | (⟨-, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd hy h3
      · exact absurd (LStmt.entry_mem_labels _) (h6 _ hy)
      · exact absurd hy h3
      · exact Or.inl hx
      · exact absurd (LStmt.mem_labels_of_edge hx).2 (h6 _ hy)
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h1
  | @ifFalse S t pr K e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ _ hu ih =>
    obtain ⟨K', hK⟩ := ih.occK.of_occurs hu
    have hn := hK.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ⟨hK.iteR, h2, hK.flow_subset (by simp [LStmt.flow]), fun x y hxy hy => ?_⟩
    rcases hK.pred hP hxy (by rw [LStmt.labels_ite]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨-, rfl⟩ | ⟨-, rfl⟩) | (⟨rfl, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact absurd hy (h6 _ (LStmt.entry_mem_labels _))
      · exact absurd hy h4
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd hy h4
      · exact absurd hy (h6 _ (LStmt.mem_labels_of_edge hx).2)
      · exact Or.inl hx
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h2
  | @loop1 S t pr K e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ _ hu ih =>
    obtain ⟨K', hK⟩ := ih.occK.of_occurs hu
    have hn := hK.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ⟨hK.loopL, h1, hK.flow_subset (by simp [LStmt.flow]), fun x y hxy hy => ?_⟩
    rcases hK.pred hP hxy (by rw [LStmt.labels_loop]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨rfl, rfl⟩ | ⟨-, rfl⟩) | (⟨-, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd hy h3
      · exact absurd (LStmt.entry_mem_labels _) (h6 _ hy)
      · exact absurd hy h1
      · exact Or.inl hx
      · exact absurd (LStmt.mem_labels_of_edge hx).2 (h6 _ hy)
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h1
  | @loop2 S t pr K e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ _ hu ih =>
    obtain ⟨K', hK⟩ := ih.occK.of_occurs hu
    have hn := hK.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    refine ⟨hK.loopR, h4, hK.flow_subset (by simp [LStmt.flow]), fun x y hxy hy => ?_⟩
    rcases hK.pred hP hxy (by rw [LStmt.labels_loop]; simp [hy]) with hx | hx
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨-, rfl⟩ | ⟨-, rfl⟩) | (⟨rfl, rfl⟩ | ⟨-, rfl⟩)) | hx) | hx
      · exact absurd hy (h6 _ (LStmt.entry_mem_labels _))
      · exact absurd hy h4
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd hy h2
      · exact absurd hy (h6 _ (LStmt.mem_labels_of_edge hx).2)
      · exact Or.inl hx
    · simp only [LStmt.entry] at hx; subst hx; exact absurd hy h2


/-! ### Facts on `EdgeIn` -/

theorem BodyShape.exit_eq {b m : LStmt Label} {a z : Label} (h : BodyShape b a m z) :
    b.exit = z := by
  rcases h with rfl | rfl <;> rfl

/-- The only predecessor of the final `stop` of a body `start m stop` is `exit(m)`. -/
theorem BodyShape.stop_pred {b m : LStmt Label} {a z : Label} (hP : P.UniqueLabels)
    (hb : b ∈ P.bodies) (hs : BodyShape b a m z) {x : Label} (hx : (x, z) ∈ P.flow) :
    x = m.exit := by
  obtain ⟨b', hb', hx'⟩ := LProgram.mem_flow.1 hx
  have hzb : z ∈ b.labels := hs.labels_eq ▸ by simp
  obtain rfl := LProgram.eq_of_mem_labels hP hb hb' hzb (LStmt.mem_labels_of_edge hx').2
  have hn := LProgram.nodup_labels_of_occurs hP ⟨_, hb, .refl _⟩
  rw [hs.labels_eq, List.nodup_cons, List.nodup_append] at hn
  have hz : z ∉ m.labels := fun h' => hn.2.2.2 z h' z (by simp) rfl
  rcases hs.mem_flow.1 hx' with h | h | h
  · simp only [Prod.mk.injEq] at h; exact absurd (h.2 ▸ LStmt.entry_mem_labels m) hz
  · simp only [Prod.mk.injEq] at h; exact h.1
  · exact absurd (LStmt.mem_labels_of_edge h).2 hz

namespace EdgeIn

variable {t : LStmt Label} {pr K x y : Label}

theorem flow (hF : FrameOK P t pr K) (h : EdgeIn t pr K x y) : (x, y) ∈ P.flow := by
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hF.occK.flow_subset h
  · exact hF.pr_edge
  · exact hF.occK.exit_edge

theorem of_src (hP : P.UniqueLabels) (hF : FrameOK P t pr K) (hx : x ∈ t.labels)
    (hxy : (x, y) ∈ P.flow) : EdgeIn t pr K x y := by
  rcases hF.occK.edge hP hxy hx with h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h

theorem of_tgt (hF : FrameOK P t pr K) (hy : y ∈ t.labels) (hxy : (x, y) ∈ P.flow) :
    EdgeIn t pr K x y := by
  rcases hF.pred x y hxy hy with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem tgt (h : EdgeIn t pr K x y) : y ∈ t.labels ∨ (x = t.exit ∧ y = K) := by
  rcases h with h | ⟨-, rfl⟩ | h
  · exact Or.inl (LStmt.mem_labels_of_edge h).2
  · exact Or.inl (LStmt.entry_mem_labels t)
  · exact Or.inr h

theorem src (h : EdgeIn t pr K x y) : x ∈ t.labels ∨ (x = pr ∧ y = t.entry) := by
  rcases h with h | h | ⟨rfl, -⟩
  · exact Or.inl (LStmt.mem_labels_of_edge h).1
  · exact Or.inr h
  · exact Or.inl (LStmt.exit_mem_labels t)

/-- From `pr`, the only edge of the level leads to `entry(t)`. -/
theorem eq_entry (hF : FrameOK P t pr K) (h : EdgeIn t pr K pr y) : y = t.entry := by
  rcases h with h | ⟨-, rfl⟩ | ⟨h, -⟩
  · exact absurd (LStmt.mem_labels_of_edge h).1 hF.pr_not_mem
  · rfl
  · exact absurd (h ▸ LStmt.exit_mem_labels t) hF.pr_not_mem

/-- The only edge of the level into `K` comes from `exit(t)`. -/
theorem eq_exit (hP : P.UniqueLabels) (hF : FrameOK P t pr K) (h : EdgeIn t pr K x K) :
    x = t.exit := by
  have hK := hF.occK.not_mem hP
  rcases h with h | ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd (LStmt.mem_labels_of_edge h).2 hK
  · exact absurd (h ▸ LStmt.entry_mem_labels t) hK
  · exact h

end EdgeIn

namespace StkInv

variable {S : RStack} {t : LStmt Label} {pr K : Label}

theorem occurs_P (h : StkInv P S t pr K) (hP : P.UniqueLabels) {u : LStmt Label}
    (hu : LStmt.Occurs u t) : LProgram.Occurs u P := by
  obtain ⟨b, hb, hob⟩ := (h.frame hP).occK.occurs
  exact ⟨b, hb, hu.trans hob⟩

/-- The block following a level is a `stop` or a condition. -/
theorem K_block (hP : P.UniqueLabels) (h : StkInv P S t pr K) :
    P.block K = some .stop ∨ ∃ e, P.block K = some (.cond e) := by
  cases h with
  | nil hb hs => exact Or.inl (hs.stop_block hP hb)
  | call _ _ _ hpb hs => exact Or.inl (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb))
  | uncall _ _ _ hpb hs => exact Or.inl (hs.stop_block hP (LProgram.mem_bodies_of_proc hpb))
  | @ifTrue _ _ _ _ _ e₂ _ _ _ _ h' hu | @ifFalse _ _ _ _ _ e₂ _ _ _ _ h' hu
  | @loop1 _ _ _ _ _ e₂ _ _ _ _ h' hu =>
    exact Or.inr ⟨e₂, LProgram.block_of_occurs hP (h'.occurs_P hP hu) (by simp [LStmt.blocks])⟩
  | @loop2 _ _ _ _ e₁ _ _ _ _ _ h' hu =>
    exact Or.inr ⟨e₁, LProgram.block_of_occurs hP (h'.occurs_P hP hu) (by simp [LStmt.blocks])⟩

/-- The block preceding a level is a `start` or a condition. -/
theorem pr_block (hW : RevWF P) (h : StkInv P S t pr K) :
    P.block pr = some .start ∨ ∃ e, P.block pr = some (.cond e) := by
  cases h with
  | nil hb hs => exact Or.inl (hs.start_block hW.unique hb)
  | call _ _ _ hpb hs =>
    exact Or.inl (hs.start_block hW.unique (LProgram.mem_bodies_of_proc hpb))
  | uncall _ _ _ hpb hs =>
    exact Or.inl (hs.start_block hW.unique (LProgram.mem_bodies_of_proc hpb))
  | @ifTrue _ _ _ _ e₁ _ _ _ _ _ h' hu | @ifFalse _ _ _ _ e₁ _ _ _ _ _ h' hu
  | @loop1 _ _ _ _ e₁ _ _ _ _ _ h' hu =>
    exact Or.inr ⟨e₁, LProgram.block_of_occurs hW.unique (h'.occurs_P hW.unique hu)
      (by simp [LStmt.blocks])⟩
  | @loop2 _ _ _ _ _ e₂ _ _ _ _ h' hu =>
    exact Or.inr ⟨e₂, LProgram.block_of_occurs hW.unique (h'.occurs_P hW.unique hu)
      (by simp [LStmt.blocks])⟩

/-- The target of an edge of the level whose block is neither `stop` nor a condition is a
label of `t`. -/
theorem tgt_mem (hP : P.UniqueLabels) (h : StkInv P S t pr K) {x y : Label} {o : Block}
    (he : EdgeIn t pr K x y) (hb : P.block y = some o) (h1 : o ≠ .stop)
    (h2 : ∀ e, o ≠ .cond e) : y ∈ t.labels := by
  rcases he.tgt with hy | ⟨-, rfl⟩
  · exact hy
  · rcases h.K_block hP with hK | ⟨e, hK⟩
    · rw [hK] at hb; cases hb; exact absurd rfl h1
    · rw [hK] at hb; cases hb; exact absurd rfl (h2 e)

/-- The source of an edge of the level whose block is neither `start` nor a condition is a
label of `t`. -/
theorem src_mem (hW : RevWF P) (h : StkInv P S t pr K) {x y : Label} {o : Block}
    (he : EdgeIn t pr K x y) (hb : P.block x = some o) (h1 : o ≠ .start)
    (h2 : ∀ e, o ≠ .cond e) : x ∈ t.labels := by
  rcases he.src with hx | ⟨rfl, -⟩
  · exact hx
  · rcases h.pr_block hW with hK | ⟨e, hK⟩
    · rw [hK] at hb; cases hb; exact absurd rfl h1
    · rw [hK] at hb; cases hb; exact absurd rfl (h2 e)

/-- Pushing a stack item in a forward step (rules `IfTrue1⃗`, `IfFalse1⃗`, `LoopMain⃗`): the
conditional or loop that is entered is a sub-statement of the current level. -/
theorem push_fwd (hP : P.UniqueLabels) (h : StkInv P S t pr K) {ℓ ℓ₁ : Label}
    (he : EdgeIn t pr K ℓ ℓ₁) {u : LStmt Label} (hc : P.ctx ℓ₁ = some u) (hent : u.entry = ℓ₁)
    (hloop : ∀ e₁ l₁ s₁ s₂ e₂ l₂, u = .loop e₁ l₁ s₁ s₂ e₂ l₂ → ℓ ≠ s₂.exit) :
    LStmt.Occurs u t := by
  have hF := h.frame hP
  refine hF.occK.occurs_of_ctx hP hc ?_
  rcases he.tgt with hm | ⟨hx, rfl⟩
  · exact hm
  · exfalso
    obtain ⟨e, hbe⟩ := LProgram.block_of_ctx hP hc
    cases h with
    | nil hb hs => rw [hs.stop_block hP hb] at hbe; cases hbe
    | call _ _ _ hpb hs =>
      rw [hs.stop_block hP (LProgram.mem_bodies_of_proc hpb)] at hbe; cases hbe
    | uncall _ _ _ hpb hs =>
      rw [hs.stop_block hP (LProgram.mem_bodies_of_proc hpb)] at hbe; cases hbe
    | ifTrue h' hu | ifFalse h' hu =>
      have hn := LProgram.nodup_labels_of_occurs hP (h'.occurs_P hP hu)
      rw [LStmt.labels_ite] at hn
      rw [(LProgram.ctx_ite hP (h'.occurs_P hP hu)).2] at hc; cases hc
      exact (LStmt.nodup_cons_append3 hn).2.2.2.2.1 hent
    | loop1 h' hu =>
      have hn := LProgram.nodup_labels_of_occurs hP (h'.occurs_P hP hu)
      rw [LStmt.labels_loop] at hn
      rw [(LProgram.ctx_loop hP (h'.occurs_P hP hu)).2] at hc; cases hc
      exact (LStmt.nodup_cons_append3 hn).2.2.2.2.1 hent
    | loop2 h' hu =>
      rw [(LProgram.ctx_loop hP (h'.occurs_P hP hu)).1] at hc; cases hc
      exact hloop _ _ _ _ _ _ rfl hx

/-- Pushing a stack item in a backward step (rules `IfTrue2⃖`, `IfFalse2⃖`, `LoopBase⃖`): the
conditional or loop that is entered (backwards) is a sub-statement of the current level. -/
theorem push_bwd (hW : RevWF P) (h : StkInv P S t pr K) {ℓ₂ ℓ₂' : Label}
    (he : EdgeIn t pr K ℓ₂ ℓ₂') {u : LStmt Label} (hc : P.ctx ℓ₂ = some u) (hex : u.exit = ℓ₂)
    (hloop : ∀ e₁ l₁ s₁ s₂ e₂ l₂, u = .loop e₁ l₁ s₁ s₂ e₂ l₂ → ℓ₂' ≠ s₂.entry) :
    LStmt.Occurs u t := by
  have hP := hW.unique
  have hF := h.frame hP
  refine hF.occK.occurs_of_ctx hP hc ?_
  rcases he.src with hm | ⟨rfl, hy⟩
  · exact hm
  · exfalso
    obtain ⟨e, hbe⟩ := LProgram.block_of_ctx hP hc
    cases h with
    | nil hb hs => rw [hs.start_block hP hb] at hbe; cases hbe
    | call _ _ _ hpb hs =>
      rw [hs.start_block hP (LProgram.mem_bodies_of_proc hpb)] at hbe; cases hbe
    | uncall _ _ _ hpb hs =>
      rw [hs.start_block hP (LProgram.mem_bodies_of_proc hpb)] at hbe; cases hbe
    | ifTrue h' hu | ifFalse h' hu =>
      have hn := LProgram.nodup_labels_of_occurs hP (h'.occurs_P hP hu)
      rw [LStmt.labels_ite] at hn
      rw [(LProgram.ctx_ite hP (h'.occurs_P hP hu)).1] at hc; cases hc
      exact (LStmt.nodup_cons_append3 hn).2.2.2.2.1 hex.symm
    | loop1 h' hu =>
      have hn := LProgram.nodup_labels_of_occurs hP (h'.occurs_P hP hu)
      rw [LStmt.labels_loop] at hn
      rw [(LProgram.ctx_loop hP (h'.occurs_P hP hu)).1] at hc; cases hc
      exact (LStmt.nodup_cons_append3 hn).2.2.2.2.1 hex.symm
    | loop2 h' hu =>
      rw [(LProgram.ctx_loop hP (h'.occurs_P hP hu)).2] at hc; cases hc
      exact hloop _ _ _ _ _ _ rfl hy

end StkInv

/-! ### Preservation of the invariant -/

namespace RInv

variable (hW : RevWF P)
include hW

theorem init {ℓ₁ ℓ₂ : Label} (h : (ℓ₁, ℓ₂) ∈ P.flow) :
    RInv P ⟨Store.empty, ℓ₁, ℓ₂, []⟩ := by
  obtain ⟨b, hb, hx⟩ := LProgram.mem_flow.1 h
  obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies b hb
  refine ⟨m, a, z, .nil hb hs, ?_⟩
  rcases hs.mem_flow.1 hx with h | h | h
  · simp only [Prod.mk.injEq] at h; exact Or.inr (Or.inl h)
  · simp only [Prod.mk.injEq] at h; exact Or.inr (Or.inr h)
  · exact Or.inl h

theorem fwd {k k' : RConfig} (hk : RInv P k) (h : FwdStep P k k') : RInv P k' := by
  have hP := hW.unique
  obtain ⟨t, pr, K, hS, he⟩ := hk
  have hF := hS.frame hP
  cases h with
  | assVar hb _ hf =>
    exact ⟨t, pr, K, hS, .of_src hP hF (hS.tgt_mem hP he hb (by simp) (by simp)) hf⟩
  | assArr hb _ _ hf =>
    exact ⟨t, pr, K, hS, .of_src hP hF (hS.tgt_mem hP he hb (by simp) (by simp)) hf⟩
  | skip hb hf =>
    exact ⟨t, pr, K, hS, .of_src hP hF (hS.tgt_mem hP he hb (by simp) (by simp)) hf⟩
  | call hb hpb hf =>
    have hm := hS.tgt_mem hP he hb (by simp) (by simp)
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine ⟨m, a, z, .call hS hm hb hpb hs, ?_⟩
    rw [hs.entry_eq] at hf ⊢
    rw [hs.start_succ hP (LProgram.mem_bodies_of_proc hpb) hf]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | uncall hb hpb hf =>
    have hm := hS.tgt_mem hP he hb (by simp) (by simp)
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine ⟨m, a, z, .uncall hS hm hb hpb hs, ?_⟩
    rw [hs.entry_eq] at hf ⊢
    rw [hs.start_succ hP (LProgram.mem_bodies_of_proc hpb) hf]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | return1 _ hf =>
    cases hS with
    | call hS' hm => exact ⟨_, _, _, hS', .of_src hP (hS'.frame hP) hm hf⟩
  | return2 _ hf =>
    cases hS with
    | uncall hS' hm => exact ⟨_, _, _, hS', .of_src hP (hS'.frame hP) hm hf⟩
  | ifTrue1 hc _ _ =>
    exact ⟨_, _, _, .ifTrue hS (hS.push_fwd hP he hc rfl (by intros; simp_all)),
      Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | ifFalse1 hc _ _ =>
    exact ⟨_, _, _, .ifFalse hS (hS.push_fwd hP he hc rfl (by intros; simp_all)),
      Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | loopMain hc _ _ hne =>
    refine ⟨_, _, _, .loop1 hS (hS.push_fwd hP he hc rfl ?_), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    intro _ _ _ _ _ _ heq; cases heq; exact hne
  | ifTrue2 _ _ _ hf =>
    cases hS with
    | ifTrue hS' hu =>
      exact ⟨_, _, _, hS', .of_src hP (hS'.frame hP)
        (hu.labels_subset (by simp [LStmt.labels, LStmt.blocks])) hf⟩
  | ifFalse2 _ _ _ hf =>
    cases hS with
    | ifFalse hS' hu =>
      exact ⟨_, _, _, hS', .of_src hP (hS'.frame hP)
        (hu.labels_subset (by simp [LStmt.labels, LStmt.blocks])) hf⟩
  | loopBase _ _ _ hf _ =>
    cases hS with
    | loop1 hS' hu =>
      exact ⟨_, _, _, hS', .of_src hP (hS'.frame hP)
        (hu.labels_subset (by simp [LStmt.labels, LStmt.blocks])) hf⟩
  | loop1 _ _ _ =>
    cases hS with
    | loop1 hS' hu => exact ⟨_, _, _, .loop2 hS' hu, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | loop2 _ _ _ =>
    cases hS with
    | loop2 hS' hu => exact ⟨_, _, _, .loop1 hS' hu, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem bwd {k k' : RConfig} (hk : RInv P k) (h : BwdStep P k k') : RInv P k' := by
  have hP := hW.unique
  obtain ⟨t, pr, K, hS, he⟩ := hk
  have hF := hS.frame hP
  cases h with
  | assVar hb _ hf =>
    exact ⟨t, pr, K, hS, .of_tgt hF (hS.src_mem hW he hb (by simp) (by simp))
      (LProgram.mem_invFlow.1 hf)⟩
  | assArr hb _ _ hf =>
    exact ⟨t, pr, K, hS, .of_tgt hF (hS.src_mem hW he hb (by simp) (by simp))
      (LProgram.mem_invFlow.1 hf)⟩
  | skip hb hf =>
    exact ⟨t, pr, K, hS, .of_tgt hF (hS.src_mem hW he hb (by simp) (by simp))
      (LProgram.mem_invFlow.1 hf)⟩
  | call _ hf =>
    cases hS with
    | call hS' hm => exact ⟨_, _, _, hS', .of_tgt (hS'.frame hP) hm (LProgram.mem_invFlow.1 hf)⟩
  | uncall _ hf =>
    cases hS with
    | uncall hS' hm =>
      exact ⟨_, _, _, hS', .of_tgt (hS'.frame hP) hm (LProgram.mem_invFlow.1 hf)⟩
  | return1 hb hpb hf =>
    have hm := hS.src_mem hW he hb (by simp) (by simp)
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine ⟨m, a, z, .call hS hm hb hpb hs, ?_⟩
    rw [hs.exit_eq] at hf ⊢
    rw [hs.stop_pred hP (LProgram.mem_bodies_of_proc hpb) (LProgram.mem_invFlow.1 hf)]
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | return2 hb hpb hf =>
    have hm := hS.src_mem hW he hb (by simp) (by simp)
    obtain ⟨a, m, z, s, hs, -, -⟩ := hW.bodies _ (LProgram.mem_bodies_of_proc hpb)
    refine ⟨m, a, z, .uncall hS hm hb hpb hs, ?_⟩
    rw [hs.exit_eq] at hf ⊢
    rw [hs.stop_pred hP (LProgram.mem_bodies_of_proc hpb) (LProgram.mem_invFlow.1 hf)]
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | ifTrue1 _ _ _ hf =>
    cases hS with
    | ifTrue hS' hu =>
      exact ⟨_, _, _, hS', .of_tgt (hS'.frame hP)
        (hu.labels_subset (by simp [LStmt.labels, LStmt.blocks])) (LProgram.mem_invFlow.1 hf)⟩
  | ifFalse1 _ _ _ hf =>
    cases hS with
    | ifFalse hS' hu =>
      exact ⟨_, _, _, hS', .of_tgt (hS'.frame hP)
        (hu.labels_subset (by simp [LStmt.labels, LStmt.blocks])) (LProgram.mem_invFlow.1 hf)⟩
  | loopMain _ _ _ hf _ =>
    cases hS with
    | loop1 hS' hu =>
      exact ⟨_, _, _, hS', .of_tgt (hS'.frame hP)
        (hu.labels_subset (by simp [LStmt.labels, LStmt.blocks])) (LProgram.mem_invFlow.1 hf)⟩
  | ifTrue2 hc _ _ =>
    exact ⟨_, _, _, .ifTrue hS (hS.push_bwd hW he hc rfl (by intros; simp_all)),
      Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  | ifFalse2 hc _ _ =>
    exact ⟨_, _, _, .ifFalse hS (hS.push_bwd hW he hc rfl (by intros; simp_all)),
      Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  | loopBase hc _ _ hne =>
    refine ⟨_, _, _, .loop1 hS (hS.push_bwd hW he hc rfl ?_), Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    intro _ _ _ _ _ _ heq; cases heq; exact hne
  | loop1 _ _ _ =>
    cases hS with
    | loop2 hS' hu => exact ⟨_, _, _, .loop1 hS' hu, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  | loop2 _ _ _ =>
    cases hS with
    | loop1 hS' hu => exact ⟨_, _, _, .loop2 hS' hu, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

end RInv

/-- Every reachable configuration satisfies the invariant. -/
theorem LProgram.Reachable.rInv (hW : RevWF P) {k : RConfig} (h : P.Reachable k) :
    RInv P k := by
  obtain ⟨ℓ₁, ℓ₂, hf, hr⟩ := h
  induction hr with
  | refl => exact RInv.init hW hf
  | tail _ hs ih =>
    rcases hs with hs | hs
    · exact RInv.fwd hW ih hs
    · exact RInv.bwd hW ih hs

end Janus

end
