module

public import RequestProject.Janus.Forward

/-!
# Janus: structural properties of labeled programs used for the forward rules

Auxiliary material for the proof of Lemma "forward-rev" (`RequestProject.Janus.ForwardEquiv`):

* `LRepr t s`: the labeled statement `t` is the statement `s` of the original syntax with
  labels added (and no `start`/`stop`);
* `OccK P t K`: the statement `t` occurs in (a body of) the labeled program `P`, and `K` is
  the label of the first block executed after `t` (its *continuation*);
* the CFG facts needed for the forward rules: the edges of `flow(p)` leaving a statement `t`
  with continuation `K` are those of `flow(t)` plus `(exit(t), K)` (`OccK.edge`);
* facts about `block` and `ctx`.
-/

@[expose] public section

namespace Janus

/-! ### Labeled versions of original statements -/

/-- `LRepr t s`: the labeled statement `t` is the original statement `s` with labels. -/
inductive LRepr : LStmt Label → Stmt → Prop where
  | assVar {x : Var} {op : ModOp} {e : Expr} {ℓ : Label} :
      LRepr (.assVar x op e ℓ) (.assVar x op e)
  | assArr {x : Var} {e₁ : Expr} {op : ModOp} {e₂ : Expr} {ℓ : Label} :
      LRepr (.assArr x e₁ op e₂ ℓ) (.assArr x e₁ op e₂)
  | ite {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {s₁ s₂ : Stmt} :
      LRepr t₁ s₁ → LRepr t₂ s₂ → LRepr (.ite e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) (.ite e₁ s₁ s₂ e₂)
  | loop {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {t₁ t₂ : LStmt Label} {s₁ s₂ : Stmt} :
      LRepr t₁ s₁ → LRepr t₂ s₂ → LRepr (.loop e₁ ℓ₁ t₁ t₂ e₂ ℓ₂) (.loop e₁ s₁ s₂ e₂)
  | call {id : ProcId} {ℓ : Label} : LRepr (.call id ℓ) (.call id)
  | uncall {id : ProcId} {ℓ : Label} : LRepr (.uncall id ℓ) (.uncall id)
  | skip {ℓ : Label} : LRepr (.skip ℓ) .skip
  | seq {t₁ t₂ : LStmt Label} {s₁ s₂ : Stmt} :
      LRepr t₁ s₁ → LRepr t₂ s₂ → LRepr (.seq t₁ t₂) (.seq s₁ s₂)

/-- Labeling a statement of the original syntax yields a labeled version of it. -/
theorem LRepr.labelFrom (s : Stmt) (n : Label) : LRepr (s.toX.labelFrom n).1 s := by
  induction s generalizing n with
  | ite e₁ s₁ s₂ e₂ ih₁ ih₂ => exact .ite (ih₁ _) (ih₂ _)
  | loop e₁ s₁ s₂ e₂ ih₁ ih₂ => exact .loop (ih₁ _) (ih₂ _)
  | seq s₁ s₂ ih₁ ih₂ => exact .seq (ih₁ _) (ih₂ _)
  | assVar => exact .assVar
  | assArr => exact .assArr
  | call => exact .call
  | uncall => exact .uncall
  | skip => exact .skip

/-- The first block of a labeled version of an original statement is neither `start` nor
`stop`. -/
theorem LRepr.entry_block {t : LStmt Label} {s : Stmt} (h : LRepr t s) :
    ∃ o, (t.entry, o) ∈ t.blocks ∧ o ≠ .stop ∧ o ≠ .start := by
  induction h with
  | seq _ _ ih₁ _ =>
    obtain ⟨o, ho, h1, h2⟩ := ih₁
    exact ⟨o, by simp [LStmt.blocks, LStmt.entry, ho], h1, h2⟩
  | @assVar x op e ℓ => exact ⟨.assVar x op e, by simp [LStmt.blocks, LStmt.entry], by simp, by simp⟩
  | @assArr x e₁ op e₂ ℓ =>
    exact ⟨.assArr x e₁ op e₂, by simp [LStmt.blocks, LStmt.entry], by simp, by simp⟩
  | @ite e₁ e₂ _ _ _ _ _ _ _ _ => exact ⟨.cond e₁, by simp [LStmt.blocks, LStmt.entry], by simp, by simp⟩
  | @loop e₁ e₂ _ _ _ _ _ _ _ _ => exact ⟨.cond e₁, by simp [LStmt.blocks, LStmt.entry], by simp, by simp⟩
  | @call id ℓ => exact ⟨.call id, by simp [LStmt.blocks, LStmt.entry], by simp, by simp⟩
  | @uncall id ℓ => exact ⟨.uncall id, by simp [LStmt.blocks, LStmt.entry], by simp, by simp⟩
  | skip => exact ⟨.skip, by simp [LStmt.blocks, LStmt.entry], by simp, by simp⟩

/-! ### Generic facts on occurrences and lists -/

namespace LStmt

variable {L : Type}

theorem Occurs.trans {t u s : LStmt L} (h₁ : Occurs t u) (h₂ : Occurs u s) : Occurs t s := by
  induction h₂ with
  | refl => exact h₁
  | ite₁ _ ih => exact .ite₁ ih
  | ite₂ _ ih => exact .ite₂ ih
  | loop₁ _ ih => exact .loop₁ ih
  | loop₂ _ ih => exact .loop₂ ih
  | seq₁ _ ih => exact .seq₁ ih
  | seq₂ _ ih => exact .seq₂ ih

theorem Occurs.blocks_sublist {t s : LStmt L} (h : Occurs t s) : t.blocks.Sublist s.blocks := by
  induction h with
  | refl => exact List.Sublist.refl _
  | ite₁ _ ih | loop₁ _ ih =>
    simp only [blocks]
    exact List.Sublist.cons _
      (ih.trans ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)))
  | ite₂ _ ih | loop₂ _ ih =>
    simp only [blocks]
    exact List.Sublist.cons _
      (ih.trans ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)))
  | seq₁ _ ih => exact ih.trans (List.sublist_append_left _ _)
  | seq₂ _ ih => exact ih.trans (List.sublist_append_right _ _)

theorem Occurs.labels_sublist {t s : LStmt L} (h : Occurs t s) :
    t.labels.Sublist s.labels :=
  h.blocks_sublist.map Prod.fst

theorem Occurs.flow_subset [DecidableEq L] {t s : LStmt L} (h : Occurs t s) :
    t.flow ⊆ s.flow := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | ite₁ _ ih | loop₁ _ ih =>
    intro x hx; have := ih hx; simp only [flow, Finset.mem_union]; tauto
  | ite₂ _ ih | loop₂ _ ih =>
    intro x hx; have := ih hx; simp only [flow, Finset.mem_union]; tauto
  | seq₁ _ ih =>
    intro x hx; have := ih hx; simp only [flow, Finset.mem_union]; tauto
  | seq₂ _ ih =>
    intro x hx; have := ih hx; simp only [flow, Finset.mem_union]; tauto

theorem src_mem_labels [DecidableEq L] {s : LStmt L} {a x : L} (h : (a, x) ∈ s.flow) :
    a ∈ s.labels :=
  (mem_labels_of_edge h).1

/-- Disjointness facts on the labels of a conditional or loop with unique labels. -/
theorem nodup_cons_append3 {a b : L} {l₁ l₂ : List L} (h : (a :: (l₁ ++ l₂ ++ [b])).Nodup) :
    a ∉ l₁ ∧ a ∉ l₂ ∧ b ∉ l₁ ∧ b ∉ l₂ ∧ a ≠ b ∧ (∀ x ∈ l₁, x ∉ l₂) ∧ l₁.Nodup ∧ l₂.Nodup := by
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_singleton,
    not_or] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5, h6⟩, -, h8⟩ := h
  refine ⟨h1, h2, fun hb => h8 b (Or.inl hb) b rfl rfl, fun hb => h8 b (Or.inr hb) b rfl rfl,
    h3, fun x hx hx' => h6 x hx x hx' rfl, h4, h5⟩

end LStmt

theorem List.sublist_flatMap_of_mem' {α β : Type} {l : List α} {f : α → List β} {a : α}
    (h : a ∈ l) : (f a).Sublist (l.flatMap f) := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

theorem List.eq_of_nodup_flatMap {α β : Type} {l : List α} {f : α → List β} {x y : α} {a : β}
    (hl : (l.flatMap f).Nodup) (hx : x ∈ l) (hy : y ∈ l) (hax : a ∈ f x) (hay : a ∈ f y) :
    x = y := by
  induction l with
  | nil => simp at hx
  | cons b l ih =>
    rw [List.flatMap_cons, List.nodup_append] at hl
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd rfl (hl.2.2 a hax a (List.mem_flatMap.2 ⟨y, hy', hay⟩))
    · exact absurd rfl (hl.2.2 a hay a (List.mem_flatMap.2 ⟨x, hx', hax⟩))
    · exact ih hl.2.1 hx' hy'

/-! ### Facts on labeled programs -/

namespace LProgram

variable {P : LProgram Label}

theorem blocks_eq_flatMap (P : LProgram Label) : P.blocks = P.bodies.flatMap LStmt.blocks := by
  simp [blocks, bodies, List.flatMap_map]

theorem flow_subset_of_mem {b : LStmt Label} (hb : b ∈ P.bodies) : b.flow ⊆ P.flow :=
  fun _ hx => mem_flow.2 ⟨b, hb, hx⟩

theorem nodup_labels_of_occurs (hP : P.UniqueLabels) {t : LStmt Label} (h : Occurs t P) :
    t.labels.Nodup := by
  obtain ⟨b, hb, ho⟩ := h
  unfold UniqueLabels at hP; rw [labels_eq_flatMap] at hP
  exact hP.sublist (ho.labels_sublist.trans (List.sublist_flatMap_of_mem' hb))

theorem block_of_occurs (hP : P.UniqueLabels) {t : LStmt Label} (h : Occurs t P) {ℓ : Label}
    {o : Block} (hm : (ℓ, o) ∈ t.blocks) : P.block ℓ = some o := by
  obtain ⟨b, hb, ho⟩ := h
  refine (block_eq_some_iff hP ℓ o).2 ?_
  rw [blocks_eq_flatMap]
  exact List.mem_flatMap.2 ⟨b, hb, ho.blocks_sublist.subset hm⟩

theorem eq_of_mem_labels (hP : P.UniqueLabels) {b b' : LStmt Label} (hb : b ∈ P.bodies)
    (hb' : b' ∈ P.bodies) {ℓ : Label} (h : ℓ ∈ b.labels) (h' : ℓ ∈ b'.labels) : b = b' := by
  unfold UniqueLabels at hP; rw [labels_eq_flatMap] at hP
  exact List.eq_of_nodup_flatMap hP hb hb' h h'

theorem mem_bodies_of_proc {n : PName} {b : LStmt Label} (h : P.proc n = some b) :
    b ∈ P.bodies := by
  unfold proc at h
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 h
  exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨d, List.mem_of_find?_eq_some hd, rfl⟩)

theorem main_mem_bodies (P : LProgram Label) : P.main ∈ P.bodies := List.mem_cons_self

end LProgram

/-! ### `ctx` -/

theorem LStmt.ctx_some {ℓ : Label} {s X : LStmt Label} (h : s.ctx ℓ = some X) :
    LStmt.Occurs X s ∧ ℓ ∈ X.condLabels := by
  induction s with
  | ite e₁ a s₁ s₂ e₂ b ih₁ ih₂ =>
    simp only [ctx] at h
    split_ifs at h with hc
    · cases h; exact ⟨.refl _, by simp [condLabels]; tauto⟩
    · rcases Option.or_eq_some_iff.1 h with h | ⟨-, h⟩
      · exact ⟨.ite₁ (ih₁ h).1, (ih₁ h).2⟩
      · exact ⟨.ite₂ (ih₂ h).1, (ih₂ h).2⟩
  | loop e₁ a s₁ s₂ e₂ b ih₁ ih₂ =>
    simp only [ctx] at h
    split_ifs at h with hc
    · cases h; exact ⟨.refl _, by simp [condLabels]; tauto⟩
    · rcases Option.or_eq_some_iff.1 h with h | ⟨-, h⟩
      · exact ⟨.loop₁ (ih₁ h).1, (ih₁ h).2⟩
      · exact ⟨.loop₂ (ih₂ h).1, (ih₂ h).2⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [ctx] at h
    rcases Option.or_eq_some_iff.1 h with h | ⟨-, h⟩
    · exact ⟨.seq₁ (ih₁ h).1, (ih₁ h).2⟩
    · exact ⟨.seq₂ (ih₂ h).1, (ih₂ h).2⟩
  | _ => simp [ctx] at h

namespace LProgram

variable {P : LProgram Label}

theorem ctx_some {ℓ : Label} {X : LStmt Label} (h : P.ctx ℓ = some X) :
    Occurs X P ∧ ℓ ∈ X.condLabels := by
  obtain ⟨b, hb, h⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨⟨b, hb, (LStmt.ctx_some h).1⟩, (LStmt.ctx_some h).2⟩

/-- If `ctx(ℓ)` is defined, then `ℓ` labels a condition. -/
theorem block_of_ctx (hP : P.UniqueLabels) {ℓ : Label} {X : LStmt Label}
    (h : P.ctx ℓ = some X) : ∃ e, P.block ℓ = some (.cond e) := by
  obtain ⟨ho, hl⟩ := ctx_some h
  cases X <;> simp only [LStmt.condLabels, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals
    rename_i e₁ _ _ _ e₂ _
    rcases hl with rfl | rfl
    · exact ⟨e₁, block_of_occurs hP ho (by simp [LStmt.blocks])⟩
    · exact ⟨e₂, block_of_occurs hP ho (by simp [LStmt.blocks])⟩

end LProgram

/-! ### Bodies delimited by `start` and `stop` -/

/-- The shape of the bodies of labeled programs: `start s stop`, either as
`[start]^a (m [stop]^z)` or as `([start]^a m) [stop]^z` (the latter is the shape of the
inverse procedures). -/
def BodyShape (b : LStmt Label) (a : Label) (m : LStmt Label) (z : Label) : Prop :=
  b = .seq (.start a) (.seq m (.stop z)) ∨ b = .seq (.seq (.start a) m) (.stop z)

namespace BodyShape

variable {b m : LStmt Label} {a z : Label}

theorem occurs (h : BodyShape b a m z) : LStmt.Occurs m b := by
  rcases h with rfl | rfl
  · exact .seq₂ (.seq₁ (.refl _))
  · exact .seq₁ (.seq₂ (.refl _))

theorem labels_eq (h : BodyShape b a m z) : b.labels = a :: (m.labels ++ [z]) := by
  rcases h with rfl | rfl <;> simp [LStmt.labels, LStmt.blocks]

theorem entry_eq (h : BodyShape b a m z) : b.entry = a := by
  rcases h with rfl | rfl <;> rfl

theorem mem_flow (h : BodyShape b a m z) {x : Label × Label} :
    x ∈ b.flow ↔ x = (a, m.entry) ∨ x = (m.exit, z) ∨ x ∈ m.flow := by
  rcases h with rfl | rfl
  · simp only [LStmt.flow, LStmt.exit, LStmt.entry, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, or_false]
  · simp only [LStmt.flow, LStmt.exit, LStmt.entry, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, or_false]
    tauto

theorem stop_mem_blocks (h : BodyShape b a m z) : (z, Block.stop) ∈ b.blocks := by
  rcases h with rfl | rfl <;> simp [LStmt.blocks]

end BodyShape

/-! ### Statements with their continuation -/

/-- `OccK P t K`: the statement `t` occurs in a body of the labeled program `P`, and `K` is
the label of the first block executed once `t` is completed. -/
inductive OccK (P : LProgram Label) : LStmt Label → Label → Prop where
  | body {b m : LStmt Label} {a z : Label} : b ∈ P.bodies → BodyShape b a m z → OccK P m z
  | seqL {s₁ s₂ : LStmt Label} {K : Label} : OccK P (.seq s₁ s₂) K → OccK P s₁ s₂.entry
  | seqR {s₁ s₂ : LStmt Label} {K : Label} : OccK P (.seq s₁ s₂) K → OccK P s₂ K
  | iteL {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {s₁ s₂ : LStmt Label} {K : Label} :
      OccK P (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) K → OccK P s₁ ℓ₂
  | iteR {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {s₁ s₂ : LStmt Label} {K : Label} :
      OccK P (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) K → OccK P s₂ ℓ₂
  | loopL {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {s₁ s₂ : LStmt Label} {K : Label} :
      OccK P (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) K → OccK P s₁ ℓ₂
  | loopR {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {s₁ s₂ : LStmt Label} {K : Label} :
      OccK P (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) K → OccK P s₂ ℓ₁

namespace OccK

variable {P : LProgram Label} {t : LStmt Label} {K : Label}

theorem occurs (h : OccK P t K) : LProgram.Occurs t P := by
  induction h with
  | body hb hs => exact ⟨_, hb, hs.occurs⟩
  | seqL _ ih =>
    obtain ⟨b, hb, ho⟩ := ih; exact ⟨b, hb, (LStmt.Occurs.seq₁ (.refl _)).trans ho⟩
  | seqR _ ih =>
    obtain ⟨b, hb, ho⟩ := ih; exact ⟨b, hb, (LStmt.Occurs.seq₂ (.refl _)).trans ho⟩
  | iteL _ ih =>
    obtain ⟨b, hb, ho⟩ := ih; exact ⟨b, hb, (LStmt.Occurs.ite₁ (.refl _)).trans ho⟩
  | iteR _ ih =>
    obtain ⟨b, hb, ho⟩ := ih; exact ⟨b, hb, (LStmt.Occurs.ite₂ (.refl _)).trans ho⟩
  | loopL _ ih =>
    obtain ⟨b, hb, ho⟩ := ih; exact ⟨b, hb, (LStmt.Occurs.loop₁ (.refl _)).trans ho⟩
  | loopR _ ih =>
    obtain ⟨b, hb, ho⟩ := ih; exact ⟨b, hb, (LStmt.Occurs.loop₂ (.refl _)).trans ho⟩

theorem nodup (hP : P.UniqueLabels) (h : OccK P t K) : t.labels.Nodup :=
  LProgram.nodup_labels_of_occurs hP h.occurs

theorem flow_subset (h : OccK P t K) : t.flow ⊆ P.flow := by
  obtain ⟨b, hb, ho⟩ := h.occurs
  exact ho.flow_subset.trans (LProgram.flow_subset_of_mem hb)

theorem block (hP : P.UniqueLabels) (h : OccK P t K) {ℓ : Label} {o : Block}
    (hm : (ℓ, o) ∈ t.blocks) : P.block ℓ = some o :=
  LProgram.block_of_occurs hP h.occurs hm

/-- The continuation of a statement is not one of its labels. -/
theorem not_mem (hP : P.UniqueLabels) (h : OccK P t K) : K ∉ t.labels := by
  induction h with
  | body hb hs =>
    have hn := LProgram.nodup_labels_of_occurs hP ⟨_, hb, .refl _⟩
    rw [hs.labels_eq] at hn
    simp only [List.nodup_cons, List.nodup_append, List.mem_singleton] at hn
    exact fun hz => hn.2.2.2 _ hz _ rfl rfl
  | seqL h _ =>
    have hn := h.nodup hP
    rw [LStmt.labels_seq, List.nodup_append] at hn
    exact fun hz => hn.2.2 _ hz _ (LStmt.entry_mem_labels _) rfl
  | seqR _ ih =>
    rw [LStmt.labels_seq] at ih
    exact fun hz => ih (List.mem_append_right _ hz)
  | iteL h _ =>
    have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
    exact (LStmt.nodup_cons_append3 hn).2.2.1
  | iteR h _ =>
    have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
    exact (LStmt.nodup_cons_append3 hn).2.2.2.1
  | loopL h _ =>
    have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
    exact (LStmt.nodup_cons_append3 hn).2.2.1
  | loopR h _ =>
    have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
    exact (LStmt.nodup_cons_append3 hn).2.1

/-- The edge from the exit of a statement to its continuation belongs to the CFG. -/
theorem exit_edge (h : OccK P t K) : (t.exit, K) ∈ P.flow := by
  induction h with
  | body hb hs => exact LProgram.flow_subset_of_mem hb (hs.mem_flow.2 (Or.inr (Or.inl rfl)))
  | seqL h _ => exact h.flow_subset (by simp [LStmt.flow])
  | seqR _ ih => simpa [LStmt.exit] using ih
  | iteL h _ => exact h.flow_subset (by simp [LStmt.flow])
  | iteR h _ => exact h.flow_subset (by simp [LStmt.flow])
  | loopL h _ => exact h.flow_subset (by simp [LStmt.flow])
  | loopR h _ => exact h.flow_subset (by simp [LStmt.flow])

/-- The edges of `flow(p)` leaving a label of a statement `t` with continuation `K` are the
edges of `flow(t)` and the edge `(exit(t), K)`. -/
theorem edge (hP : P.UniqueLabels) (h : OccK P t K) {a x : Label} (hax : (a, x) ∈ P.flow)
    (ha : a ∈ t.labels) : (a = t.exit ∧ x = K) ∨ (a, x) ∈ t.flow := by
  induction h with
  | @body b m a₀ z hb hs =>
    obtain ⟨b', hb', hx⟩ := LProgram.mem_flow.1 hax
    have hab : a ∈ b.labels :=
      hs.labels_eq ▸ List.mem_cons_of_mem _ (List.mem_append_left _ ha)
    obtain rfl := LProgram.eq_of_mem_labels hP hb hb' hab (LStmt.src_mem_labels hx)
    have hn := LProgram.nodup_labels_of_occurs hP ⟨_, hb, .refl _⟩
    rw [hs.labels_eq, List.nodup_cons] at hn
    rcases hs.mem_flow.1 hx with h | h | h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact absurd (List.mem_append_left _ ha) hn.1
    · simp only [Prod.mk.injEq] at h; exact Or.inl h
    · exact Or.inr h
  | @seqL s₁ s₂ K h ih =>
    have hn := h.nodup hP
    rw [LStmt.labels_seq, List.nodup_append] at hn
    have hd : ∀ y ∈ s₁.labels, y ∉ s₂.labels := fun y hy hy' => hn.2.2 y hy y hy' rfl
    rcases ih (by rw [LStmt.labels_seq]; exact List.mem_append_left _ ha) with
      ⟨rfl, -⟩ | hx
    · exact absurd (LStmt.exit_mem_labels _) (hd _ ha)
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with (hx | hx) | hx
      · exact Or.inl hx
      · exact Or.inr hx
      · exact absurd (LStmt.src_mem_labels hx) (hd _ ha)
  | @seqR s₁ s₂ K h ih =>
    have hn := h.nodup hP
    rw [LStmt.labels_seq, List.nodup_append] at hn
    have hd : ∀ y ∈ s₂.labels, y ∉ s₁.labels := fun y hy hy' => hn.2.2 y hy' y hy rfl
    rcases ih (by rw [LStmt.labels_seq]; exact List.mem_append_right _ ha) with
      ⟨rfl, rfl⟩ | hx
    · exact Or.inl ⟨rfl, rfl⟩
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with (⟨rfl, -⟩ | hx) | hx
      · exact absurd (LStmt.exit_mem_labels _) (hd _ ha)
      · exact absurd (LStmt.src_mem_labels hx) (hd _ ha)
      · exact Or.inr hx
  | @iteL e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_ite]; simp [ha]) with ⟨rfl, -⟩ | hx
    · exact absurd ha h3
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨rfl, -⟩ | ⟨rfl, rfl⟩) | (⟨rfl, -⟩ | ⟨rfl, -⟩)) | hx) | hx
      · exact absurd ha h1
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd ha h1
      · exact absurd (LStmt.exit_mem_labels _) (fun h' => h6 _ ha h')
      · exact Or.inr hx
      · exact absurd (LStmt.src_mem_labels hx) (h6 _ ha)
  | @iteR e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_ite]; simp [ha]) with ⟨rfl, -⟩ | hx
    · exact absurd ha h4
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨rfl, -⟩ | ⟨rfl, -⟩) | (⟨rfl, -⟩ | ⟨rfl, rfl⟩)) | hx) | hx
      · exact absurd ha h2
      · exact absurd ha (h6 _ (LStmt.exit_mem_labels _))
      · exact absurd ha h2
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd ha (h6 _ (LStmt.src_mem_labels hx))
      · exact Or.inr hx
  | @loopL e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_loop]; simp [ha]) with ⟨rfl, -⟩ | hx
    · exact absurd ha h3
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨rfl, -⟩ | ⟨rfl, rfl⟩) | (⟨rfl, -⟩ | ⟨rfl, -⟩)) | hx) | hx
      · exact absurd ha h1
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd ha h3
      · exact absurd (LStmt.exit_mem_labels _) (h6 _ ha)
      · exact Or.inr hx
      · exact absurd (LStmt.src_mem_labels hx) (h6 _ ha)
  | @loopR e₁ e₂ ℓ₁ ℓ₂ s₁ s₂ K h ih =>
    have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := LStmt.nodup_cons_append3 hn
    rcases ih (by rw [LStmt.labels_loop]; simp [ha]) with ⟨rfl, -⟩ | hx
    · exact absurd ha h4
    · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hx
      rcases hx with (((⟨rfl, -⟩ | ⟨rfl, -⟩) | (⟨rfl, -⟩ | ⟨rfl, rfl⟩)) | hx) | hx
      · exact absurd ha h2
      · exact absurd ha (h6 _ (LStmt.exit_mem_labels _))
      · exact absurd ha h4
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd ha (h6 _ (LStmt.src_mem_labels hx))
      · exact Or.inr hx

/-! ### Successors in the CFG -/

/-- The only successor of an elementary block (without internal edges) is its
continuation. -/
theorem succ_of_flow_empty (hP : P.UniqueLabels) (h : OccK P t K) (hf : t.flow = ∅)
    {x : Label} (hx : (t.exit, x) ∈ P.flow) : x = K := by
  rcases h.edge hP hx (LStmt.exit_mem_labels _) with ⟨-, rfl⟩ | h'
  · rfl
  · simp [hf] at h'

/-- The only successor of the assertion of a conditional is its continuation. -/
theorem succ_ite (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {s₁ s₂ : LStmt Label}
    (h : OccK P (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) K) {x : Label} (hx : (ℓ₂, x) ∈ P.flow) : x = K := by
  have hn := h.nodup hP; rw [LStmt.labels_ite] at hn
  obtain ⟨-, -, h3, h4, h5, -, -, -⟩ := LStmt.nodup_cons_append3 hn
  rcases h.edge hP hx (by rw [LStmt.labels_ite]; simp) with ⟨-, rfl⟩ | h'
  · rfl
  · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h'
    rcases h' with (((⟨h', -⟩ | ⟨h', -⟩) | (⟨h', -⟩ | ⟨h', -⟩)) | h') | h'
    · exact absurd h'.symm h5
    · exact absurd (by rw [h']; exact LStmt.exit_mem_labels s₁) h3
    · exact absurd h'.symm h5
    · exact absurd (by rw [h']; exact LStmt.exit_mem_labels s₂) h4
    · exact absurd (LStmt.src_mem_labels h') h3
    · exact absurd (LStmt.src_mem_labels h') h4

/-- The successors of the test of a loop are its continuation and the entry of `s₂`. -/
theorem succ_loop (hP : P.UniqueLabels) {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : Label} {s₁ s₂ : LStmt Label}
    (h : OccK P (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) K) {x : Label} (hx : (ℓ₂, x) ∈ P.flow) :
    x = K ∨ x = s₂.entry := by
  have hn := h.nodup hP; rw [LStmt.labels_loop] at hn
  obtain ⟨-, -, h3, h4, h5, -, -, -⟩ := LStmt.nodup_cons_append3 hn
  rcases h.edge hP hx (by rw [LStmt.labels_loop]; simp) with ⟨-, rfl⟩ | h'
  · exact Or.inl rfl
  · simp only [LStmt.flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h'
    rcases h' with (((⟨h', -⟩ | ⟨h', -⟩) | (⟨-, h'⟩ | ⟨h', -⟩)) | h') | h'
    · exact absurd h'.symm h5
    · exact absurd (by rw [h']; exact LStmt.exit_mem_labels s₁) h3
    · exact Or.inr h'
    · exact absurd (by rw [h']; exact LStmt.exit_mem_labels s₂) h4
    · exact absurd (LStmt.src_mem_labels h') h3
    · exact absurd (LStmt.src_mem_labels h') h4

end OccK

namespace BodyShape

variable {P : LProgram Label} {b m : LStmt Label} {a z : Label}

theorem start_not_mem (hP : P.UniqueLabels) (hb : b ∈ P.bodies) (hs : BodyShape b a m z) :
    a ∉ m.labels := by
  have hn := LProgram.nodup_labels_of_occurs hP ⟨_, hb, .refl _⟩
  rw [hs.labels_eq, List.nodup_cons] at hn
  exact fun h => hn.1 (List.mem_append_left _ h)

theorem stop_block (hP : P.UniqueLabels) (hb : b ∈ P.bodies) (hs : BodyShape b a m z) :
    P.block z = some .stop :=
  LProgram.block_of_occurs hP ⟨_, hb, .refl _⟩ hs.stop_mem_blocks

theorem start_edge (hb : b ∈ P.bodies) (hs : BodyShape b a m z) : (a, m.entry) ∈ P.flow :=
  LProgram.flow_subset_of_mem hb (hs.mem_flow.2 (Or.inl rfl))

/-- The only successor of `start` is the entry of the body. -/
theorem start_succ (hP : P.UniqueLabels) (hb : b ∈ P.bodies) (hs : BodyShape b a m z)
    {x : Label} (hx : (a, x) ∈ P.flow) : x = m.entry := by
  obtain ⟨b', hb', hx'⟩ := LProgram.mem_flow.1 hx
  have hab : a ∈ b.labels := by rw [hs.labels_eq]; exact List.mem_cons_self
  obtain rfl := LProgram.eq_of_mem_labels hP hb hb' hab (LStmt.src_mem_labels hx')
  have hna := hs.start_not_mem hP hb
  rcases hs.mem_flow.1 hx' with h | h | h
  · simp only [Prod.mk.injEq] at h; exact h.2
  · simp only [Prod.mk.injEq] at h; exact absurd (h.1 ▸ LStmt.exit_mem_labels m) hna
  · exact absurd (LStmt.src_mem_labels h) hna

theorem occK (hb : b ∈ P.bodies) (hs : BodyShape b a m z) : OccK P m z := .body hb hs

end BodyShape

end Janus

end
