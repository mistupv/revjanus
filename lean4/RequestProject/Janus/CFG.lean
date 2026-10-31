module

public import RequestProject.Janus.Labeled

/-!
# Janus: entry and exit points, contexts and control-flow graphs

This file formalizes the auxiliary functions of Section "A Reversible Semantics for Janus":

* `entry` and `exit` (Figure "Entry and exit points"): `LStmt.entry`, `LStmt.exit`;
* the partial function `ctx`, mapping the label of a test or assertion to the conditional
  or loop where it occurs: `LStmt.ctx` (for statements) and `LProgram.ctx` (for programs);
* `flow` (Figure "Control-flow graph of a Janus program"): `LStmt.flow`, a finite set of
  edges `(ℓ₁, ℓ₂)`, written `ℓ₁ ⟶[s] ℓ₂` (`LStmt.Edge`);
* the CFGs of the main program and of each (inverse) procedure: `LProgram.mainCFG`,
  `LProgram.procCFG`.

We also prove some sanity properties:
* the entry and exit points, and the endpoints of every CFG edge, are labels of the
  statement (`LStmt.entry_mem_labels`, `LStmt.exit_mem_labels`, `LStmt.mem_labels_of_edge`);
* the characterization of `ctx` given in the paper: if `if [e₁]^ℓ₁ … fi [e₂]^ℓ₂` (resp.
  `from [e₁]^ℓ₁ … until [e₂]^ℓ₂`) occurs in a program with unique labels, then
  `ctx(ℓ₁) = ctx(ℓ₂)` is this statement (`LProgram.ctx_ite`, `LProgram.ctx_loop`);
* the CFG of an inverted statement is the CFG of the statement with all edges reversed
  (`LStmt.flow_invert`).
-/

@[expose] public section

namespace Janus

namespace LStmt

variable {L : Type}

/-- The entry label of a statement (Figure "Entry and exit points"). -/
def entry : LStmt L → L
  | .ite _ ℓ₁ _ _ _ _ => ℓ₁
  | .loop _ ℓ₁ _ _ _ _ => ℓ₁
  | .seq s₁ _ => s₁.entry
  | .assVar _ _ _ ℓ => ℓ
  | .assArr _ _ _ _ ℓ => ℓ
  | .call _ ℓ => ℓ
  | .uncall _ ℓ => ℓ
  | .skip ℓ => ℓ
  | .start ℓ => ℓ
  | .stop ℓ => ℓ

/-- The exit label of a statement (Figure "Entry and exit points"). -/
def exit : LStmt L → L
  | .ite _ _ _ _ _ ℓ₂ => ℓ₂
  | .loop _ _ _ _ _ ℓ₂ => ℓ₂
  | .seq _ s₂ => s₂.exit
  | .assVar _ _ _ ℓ => ℓ
  | .assArr _ _ _ _ ℓ => ℓ
  | .call _ ℓ => ℓ
  | .uncall _ ℓ => ℓ
  | .skip ℓ => ℓ
  | .start ℓ => ℓ
  | .stop ℓ => ℓ

/-- `ctx`: the conditional or loop of a statement in which the label `ℓ` of a test or
assertion occurs (`none` if there is no such statement). -/
def ctx [DecidableEq L] (ℓ : L) : LStmt L → Option (LStmt L)
  | .ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ =>
    if ℓ = ℓ₁ ∨ ℓ = ℓ₂ then some (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) else (s₁.ctx ℓ).or (s₂.ctx ℓ)
  | .loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ =>
    if ℓ = ℓ₁ ∨ ℓ = ℓ₂ then some (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) else (s₁.ctx ℓ).or (s₂.ctx ℓ)
  | .seq s₁ s₂ => (s₁.ctx ℓ).or (s₂.ctx ℓ)
  | _ => none

/-- The edges of the control-flow graph of a statement (Figure "Control-flow graph of a
Janus program"). -/
def flow [DecidableEq L] : LStmt L → Finset (L × L)
  | .ite _ ℓ₁ s₁ s₂ _ ℓ₂ =>
    {(ℓ₁, s₁.entry), (s₁.exit, ℓ₂)} ∪ {(ℓ₁, s₂.entry), (s₂.exit, ℓ₂)} ∪ s₁.flow ∪ s₂.flow
  | .loop _ ℓ₁ s₁ s₂ _ ℓ₂ =>
    {(ℓ₁, s₁.entry), (s₁.exit, ℓ₂)} ∪ {(ℓ₂, s₂.entry), (s₂.exit, ℓ₁)} ∪ s₁.flow ∪ s₂.flow
  | .seq s₁ s₂ => {(s₁.exit, s₂.entry)} ∪ s₁.flow ∪ s₂.flow
  | _ => ∅

/-- An edge `ℓ₁ ⟶ ℓ₂` of the control-flow graph of `s`. -/
def Edge [DecidableEq L] (s : LStmt L) (ℓ₁ ℓ₂ : L) : Prop := (ℓ₁, ℓ₂) ∈ s.flow

@[inherit_doc] scoped notation:50 ℓ₁ " ⟶[" s "] " ℓ₂ => LStmt.Edge s ℓ₁ ℓ₂

/-- `t` occurs in `s` (`t` is a sub-statement of `s`). -/
inductive Occurs : LStmt L → LStmt L → Prop
  | refl (s : LStmt L) : Occurs s s
  | ite₁ {t e₁ ℓ₁ s₁ s₂ e₂ ℓ₂} : Occurs t s₁ → Occurs t (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂)
  | ite₂ {t e₁ ℓ₁ s₁ s₂ e₂ ℓ₂} : Occurs t s₂ → Occurs t (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂)
  | loop₁ {t e₁ ℓ₁ s₁ s₂ e₂ ℓ₂} : Occurs t s₁ → Occurs t (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂)
  | loop₂ {t e₁ ℓ₁ s₁ s₂ e₂ ℓ₂} : Occurs t s₂ → Occurs t (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂)
  | seq₁ {t s₁ s₂} : Occurs t s₁ → Occurs t (.seq s₁ s₂)
  | seq₂ {t s₁ s₂} : Occurs t s₂ → Occurs t (.seq s₁ s₂)

/-- The labels of the test and assertion of a conditional or loop (empty otherwise). -/
def condLabels : LStmt L → List L
  | .ite _ ℓ₁ _ _ _ ℓ₂ => [ℓ₁, ℓ₂]
  | .loop _ ℓ₁ _ _ _ ℓ₂ => [ℓ₁, ℓ₂]
  | _ => []

/-! ### Sanity properties -/

theorem entry_mem_labels (s : LStmt L) : s.entry ∈ s.labels := by
  induction s <;> simp_all [entry, labels, blocks]

theorem exit_mem_labels (s : LStmt L) : s.exit ∈ s.labels := by
  induction s <;> simp_all [exit, labels, blocks]

/-- Both endpoints of an edge of the CFG of `s` are labels of `s`. -/
theorem mem_labels_of_edge [DecidableEq L] {s : LStmt L} {ℓ₁ ℓ₂ : L}
    (h : ℓ₁ ⟶[s] ℓ₂) : ℓ₁ ∈ s.labels ∧ ℓ₂ ∈ s.labels := by
  unfold Edge at h
  induction s with
  | ite e₁ a s₁ s₂ e₂ b ih₁ ih₂ =>
    have := entry_mem_labels s₁; have := exit_mem_labels s₁
    have := entry_mem_labels s₂; have := exit_mem_labels s₂
    have key : ∀ x, x ∈ s₁.labels ∨ x ∈ s₂.labels ∨ x = a ∨ x = b →
        x ∈ (LStmt.ite e₁ a s₁ s₂ e₂ b).labels := by
      intro x hx
      simp only [labels, blocks, List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, List.map_nil, List.not_mem_nil] at hx ⊢
      tauto
    simp only [flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h
    rcases h with (((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) | h) | h
    all_goals exact ⟨key _ (by tauto), key _ (by tauto)⟩
  | loop e₁ a s₁ s₂ e₂ b ih₁ ih₂ =>
    have := entry_mem_labels s₁; have := exit_mem_labels s₁
    have := entry_mem_labels s₂; have := exit_mem_labels s₂
    have key : ∀ x, x ∈ s₁.labels ∨ x ∈ s₂.labels ∨ x = a ∨ x = b →
        x ∈ (LStmt.loop e₁ a s₁ s₂ e₂ b).labels := by
      intro x hx
      simp only [labels, blocks, List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, List.map_nil, List.not_mem_nil] at hx ⊢
      tauto
    simp only [flow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h
    rcases h with (((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) | h) | h
    all_goals exact ⟨key _ (by tauto), key _ (by tauto)⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    have := exit_mem_labels s₁; have := entry_mem_labels s₂
    have key : ∀ x, x ∈ s₁.labels ∨ x ∈ s₂.labels → x ∈ (LStmt.seq s₁ s₂).labels := by
      intro x hx
      simp only [labels, blocks, List.map_append, List.mem_append] at hx ⊢
      exact hx
    simp only [flow, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with (⟨rfl, rfl⟩ | h) | h
    all_goals exact ⟨key _ (by tauto), key _ (by tauto)⟩
  | _ => simp [flow] at h

theorem entry_invert (s : LStmt L) : s.invert.entry = s.exit := by
  induction s <;> simp_all [invert, entry, exit]

theorem exit_invert (s : LStmt L) : s.invert.exit = s.entry := by
  induction s <;> simp_all [invert, entry, exit]

/-- The CFG of `𝓘⟦s⟧` is the CFG of `s` with all edges reversed. -/
theorem flow_invert [DecidableEq L] (s : LStmt L) :
    s.invert.flow = s.flow.image Prod.swap := by
  induction s with
  | ite e₁ a s₁ s₂ e₂ b ih₁ ih₂ =>
    simp only [invert, flow, ih₁, ih₂, entry_invert, exit_invert, Finset.image_union,
      Finset.image_insert, Finset.image_singleton, Prod.swap_prod_mk]
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  | loop e₁ a s₁ s₂ e₂ b ih₁ ih₂ =>
    simp only [invert, flow, ih₁, ih₂, entry_invert, exit_invert, Finset.image_union,
      Finset.image_insert, Finset.image_singleton, Prod.swap_prod_mk]
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [invert, flow, ih₁, ih₂, entry_invert, exit_invert, Finset.image_union,
      Finset.image_singleton, Prod.swap_prod_mk]
    ext x; simp only [Finset.mem_union, Finset.mem_singleton]; tauto
  | _ => simp [invert, flow]

theorem condLabels_subset (s : LStmt L) : s.condLabels ⊆ s.labels := by
  cases s <;> simp [condLabels, labels, blocks, List.subset_def]

theorem Occurs.labels_subset {t s : LStmt L} (h : Occurs t s) : t.labels ⊆ s.labels := by
  induction h with
  | refl => exact List.Subset.refl _
  | ite₁ _ ih | ite₂ _ ih | loop₁ _ ih | loop₂ _ ih | seq₁ _ ih | seq₂ _ ih =>
    intro x hx
    have := ih hx
    simp only [labels, blocks, List.map_cons, List.map_append, List.mem_cons, List.mem_append,
      List.map_nil] at this ⊢
    tauto

theorem ctx_eq_none [DecidableEq L] {ℓ : L} {s : LStmt L} (h : ℓ ∉ s.labels) :
    s.ctx ℓ = none := by
  induction s <;> simp_all [ctx, labels, blocks]

private theorem nodup_aux {a b : L} {l₁ l₂ : List L} (h : (a :: (l₁ ++ l₂ ++ [b])).Nodup) :
    l₁.Nodup ∧ l₂.Nodup ∧ (∀ x ∈ l₁, x ≠ a ∧ x ≠ b ∧ x ∉ l₂) ∧
      (∀ x ∈ l₂, x ≠ a ∧ x ≠ b ∧ x ∉ l₁) := by
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_singleton,
    not_or] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, ⟨h4, h5, h6⟩, -, h8⟩ := h
  refine ⟨h4, h5, fun x hx => ⟨?_, ?_, ?_⟩, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · rintro rfl; exact h1 hx
  · exact h8 x (Or.inl hx) b rfl
  · exact fun hx' => h6 x hx x hx' rfl
  · rintro rfl; exact h2 hx
  · exact h8 x (Or.inr hx) b rfl
  · exact fun hx' => h6 x hx' x hx rfl

theorem labels_ite (e₁ : Expr) (a : L) (s₁ s₂ : LStmt L) (e₂ : Expr) (b : L) :
    (LStmt.ite e₁ a s₁ s₂ e₂ b).labels = a :: (s₁.labels ++ s₂.labels ++ [b]) := by
  simp [labels, blocks]

theorem labels_loop (e₁ : Expr) (a : L) (s₁ s₂ : LStmt L) (e₂ : Expr) (b : L) :
    (LStmt.loop e₁ a s₁ s₂ e₂ b).labels = a :: (s₁.labels ++ s₂.labels ++ [b]) := by
  simp [labels, blocks]

theorem labels_seq (s₁ s₂ : LStmt L) :
    (LStmt.seq s₁ s₂).labels = s₁.labels ++ s₂.labels := by
  simp [labels, blocks]

/-- If a conditional or loop `t` occurs in a statement `s` with unique labels, then
`ctx(ℓ) = t` for the labels `ℓ` of the test and of the assertion of `t`. -/
theorem ctx_of_occurs [DecidableEq L] {ℓ : L} {t s : LStmt L} (hs : s.labels.Nodup)
    (h : Occurs t s) (hℓ : ℓ ∈ t.condLabels) : s.ctx ℓ = some t := by
  have hmem : ℓ ∈ t.labels := t.condLabels_subset hℓ
  induction h with
  | refl => cases t <;> simp_all [condLabels, ctx]
  | @ite₁ e₁ a s₁ s₂ e₂ b h ih =>
    rw [labels_ite] at hs
    obtain ⟨hn₁, -, hd, -⟩ := nodup_aux hs
    obtain ⟨ha, hb, -⟩ := hd ℓ (h.labels_subset hmem)
    simp [ctx, ha, hb, ih hn₁]
  | @ite₂ e₁ a s₁ s₂ e₂ b h ih =>
    rw [labels_ite] at hs
    obtain ⟨-, hn₂, -, hd⟩ := nodup_aux hs
    obtain ⟨ha, hb, hn⟩ := hd ℓ (h.labels_subset hmem)
    simp [ctx, ha, hb, ih hn₂, ctx_eq_none hn]
  | @loop₁ e₁ a s₁ s₂ e₂ b h ih =>
    rw [labels_loop] at hs
    obtain ⟨hn₁, -, hd, -⟩ := nodup_aux hs
    obtain ⟨ha, hb, -⟩ := hd ℓ (h.labels_subset hmem)
    simp [ctx, ha, hb, ih hn₁]
  | @loop₂ e₁ a s₁ s₂ e₂ b h ih =>
    rw [labels_loop] at hs
    obtain ⟨-, hn₂, -, hd⟩ := nodup_aux hs
    obtain ⟨ha, hb, hn⟩ := hd ℓ (h.labels_subset hmem)
    simp [ctx, ha, hb, ih hn₂, ctx_eq_none hn]
  | @seq₁ s₁ s₂ h ih =>
    rw [labels_seq, List.nodup_append] at hs
    simp [ctx, ih hs.1]
  | @seq₂ s₁ s₂ h ih =>
    rw [labels_seq, List.nodup_append] at hs
    have hn : ℓ ∉ s₁.labels := fun h' => hs.2.2 _ h' _ (h.labels_subset hmem) rfl
    simp [ctx, ih hs.2.1, ctx_eq_none hn]

end LStmt

namespace LProgram

variable {L : Type}

/-- The bodies of a program: the main body and the procedure bodies. -/
def bodies (p : LProgram L) : List (LStmt L) := p.main :: p.procs.map (·.body)

/-- A statement `t` occurs in a program (in its main body or in a procedure body). -/
def Occurs (t : LStmt L) (p : LProgram L) : Prop := ∃ b ∈ p.bodies, LStmt.Occurs t b

/-- `ctx(ℓ)`: the conditional or loop of the program in which the label `ℓ` of a test or
assertion occurs (a partial function). -/
def ctx [DecidableEq L] (p : LProgram L) (ℓ : L) : Option (LStmt L) :=
  p.bodies.findSome? (LStmt.ctx ℓ)

/-- The CFG of the main program. -/
def mainCFG [DecidableEq L] (p : LProgram L) : Finset (L × L) := p.main.flow

/-- The CFG of the procedure (or inverse procedure) named `n`, if it is declared. -/
def procCFG [DecidableEq L] (p : LProgram L) (n : PName) : Option (Finset (L × L)) :=
  (p.procs.find? (·.name = n)).map (·.body.flow)

theorem labels_eq_flatMap (p : LProgram L) : p.labels = p.bodies.flatMap LStmt.labels := by
  simp [labels, blocks, bodies, LStmt.labels, List.map_flatMap, List.flatMap_map]

private theorem findSome_ctx [DecidableEq L] {ℓ : L} {t : LStmt L} :
    ∀ {bs : List (LStmt L)}, (bs.flatMap LStmt.labels).Nodup →
      (∃ b ∈ bs, LStmt.Occurs t b) → ℓ ∈ t.condLabels → bs.findSome? (LStmt.ctx ℓ) = some t
  | [], _, ⟨_, hb, _⟩, _ => by simp at hb
  | b :: bs, hn, ⟨b', hb', ho⟩, hℓ => by
    simp only [List.flatMap_cons, List.nodup_append] at hn
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · simp [LStmt.ctx_of_occurs hn.1 ho hℓ]
    · have h1 : ℓ ∈ b'.labels := ho.labels_subset (t.condLabels_subset hℓ)
      have hn₃ : ℓ ∉ b.labels := fun h' =>
        hn.2.2 _ h' _ (List.mem_flatMap.2 ⟨b', hb', h1⟩) rfl
      simp only [List.findSome?_cons, LStmt.ctx_eq_none hn₃]
      exact findSome_ctx hn.2.1 ⟨b', hb', ho⟩ hℓ

/-- The characterization of `ctx` given in the paper: in a program with unique labels, if
`if [e₁]^ℓ₁ then s₁ else s₂ fi [e₂]^ℓ₂` occurs in the program, then
`ctx(ℓ₁) = ctx(ℓ₂) = (if [e₁]^ℓ₁ then s₁ else s₂ fi [e₂]^ℓ₂)`. -/
theorem ctx_ite [DecidableEq L] {p : LProgram L} (hp : p.UniqueLabels)
    {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : L} {s₁ s₂ : LStmt L} (h : Occurs (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) p) :
    p.ctx ℓ₁ = some (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) ∧ p.ctx ℓ₂ = some (.ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) := by
  unfold UniqueLabels at hp; rw [labels_eq_flatMap] at hp
  exact ⟨findSome_ctx hp h (by simp [LStmt.condLabels]),
    findSome_ctx hp h (by simp [LStmt.condLabels])⟩

/-- The characterization of `ctx` given in the paper: in a program with unique labels, if
`from [e₁]^ℓ₁ do s₁ loop s₂ until [e₂]^ℓ₂` occurs in the program, then
`ctx(ℓ₁) = ctx(ℓ₂) = (from [e₁]^ℓ₁ do s₁ loop s₂ until [e₂]^ℓ₂)`. -/
theorem ctx_loop [DecidableEq L] {p : LProgram L} (hp : p.UniqueLabels)
    {e₁ e₂ : Expr} {ℓ₁ ℓ₂ : L} {s₁ s₂ : LStmt L} (h : Occurs (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) p) :
    p.ctx ℓ₁ = some (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) ∧ p.ctx ℓ₂ = some (.loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂) := by
  unfold UniqueLabels at hp; rw [labels_eq_flatMap] at hp
  exact ⟨findSome_ctx hp h (by simp [LStmt.condLabels]),
    findSome_ctx hp h (by simp [LStmt.condLabels])⟩

end LProgram

end Janus

end
