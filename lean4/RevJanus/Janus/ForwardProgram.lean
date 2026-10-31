module

public import RevJanus.Janus.ForwardEquiv
public import RevJanus.Janus.SmallStepEquiv

/-!
# Janus: Lemma "forward-rev" for the labeled version of a program

We show that the labeled version `p.toLabeled` of a program `p` (obtained as in the paper:
bodies delimited by `start`/`stop`, inverse procedures added, labels added) satisfies the
conditions `FwdWF` with respect to `p`, and deduce Lemma "forward-rev" for every program
(`Program.smallSteps_iff_fwdSteps`). Combined with the equivalence between the big-step and
the small-step semantics, this also relates the forward rules with the big-step semantics
(`Program.exec_iff_fwdSteps`).
-/

@[expose] public section

namespace Janus

/-! ### Procedures of the labeled version of a program -/

theorem labelProcs_find_some {α : Type} (ds : List (PName × LStmt α)) (n : Label) (x : PName)
    {d : LProcDecl Label} (h : (labelProcs ds n).1.find? (fun d => decide (d.name = x)) = some d) :
    ∃ s k, ds.find? (fun d => decide (d.1 = x)) = some (x, s) ∧ d.body = (s.labelFrom k).1 := by
  induction ds generalizing n with
  | nil => simp [labelProcs] at h
  | cons d₀ ds ih =>
    obtain ⟨y, s⟩ := d₀
    simp only [labelProcs, List.find?_cons] at h ⊢
    by_cases hy : y = x
    · subst hy
      simp only [decide_true, Option.some.injEq] at h ⊢
      subst h
      exact ⟨s, n, rfl, rfl⟩
    · simp only [hy, decide_false] at h ⊢
      exact ih _ h

theorem labelProcs_find_isSome {α : Type} (ds : List (PName × LStmt α)) (n : Label) (x : PName)
    {p : PName × LStmt α} (h : ds.find? (fun d => decide (d.1 = x)) = some p) :
    ∃ d, (labelProcs ds n).1.find? (fun d => decide (d.name = x)) = some d := by
  induction ds generalizing n with
  | nil => simp at h
  | cons d₀ ds ih =>
    obtain ⟨y, s⟩ := d₀
    simp only [labelProcs, List.find?_cons] at h ⊢
    by_cases hy : y = x
    · subst hy; simp
    · simp only [hy, decide_false] at h ⊢
      exact ih _ h

theorem Program.xprocs_find_fwd (p : Program) (id : ProcId) :
    p.xprocs.find? (fun d => decide (d.1 = PName.fwd id)) =
      (p.procs.find? (·.name == id)).map (fun d => (PName.fwd d.name, d.body.withStartStop)) := by
  unfold xprocs
  rw [List.find?_append, List.find?_map, List.find?_map]
  have h2 : List.find? ((fun d : PName × XStmt => decide (d.1 = PName.fwd id)) ∘
      fun d : ProcDecl => (PName.inv d.name, d.body.withStartStop.invert)) p.procs = none := by
    rw [List.find?_eq_none]; intro x _; simp
  rw [h2, Option.map_none, Option.or_none]
  congr 2
  funext d; simp only [Function.comp_apply, PName.fwd.injEq]; exact (beq_eq_decide _ _).symm

theorem Program.xprocs_find_inv (p : Program) (id : ProcId) :
    p.xprocs.find? (fun d => decide (d.1 = PName.inv id)) =
      (p.procs.find? (·.name == id)).map
        (fun d => (PName.inv d.name, d.body.withStartStop.invert)) := by
  unfold xprocs
  rw [List.find?_append, List.find?_map, List.find?_map]
  have h1 : List.find? ((fun d : PName × XStmt => decide (d.1 = PName.inv id)) ∘
      fun d : ProcDecl => (PName.fwd d.name, d.body.withStartStop)) p.procs = none := by
    rw [List.find?_eq_none]; intro x _; simp
  rw [h1, Option.map_none, Option.none_or]
  congr 2
  funext d; simp only [Function.comp_apply, PName.inv.injEq]; exact (beq_eq_decide _ _).symm

theorem Stmt.withStartStop_labelFrom (s : Stmt) (n : Label) :
    ∃ z, BodyShape (s.withStartStop.labelFrom n).1 n (s.toX.labelFrom (n + 1)).1 z :=
  ⟨_, Or.inl rfl⟩

theorem Stmt.withStartStop_invert_labelFrom (s : Stmt) (n : Label) :
    ∃ z, BodyShape (s.withStartStop.invert.labelFrom n).1 n (s.invert.toX.labelFrom (n + 1)).1 z := by
  simp only [Stmt.withStartStop, LStmt.invert, LStmt.labelFrom, ← Stmt.toX_invert]
  exact ⟨_, Or.inr rfl⟩

/-- The labeled version of a program satisfies the conditions `FwdWF` with respect to the
program. -/
theorem Program.fwdWF (p : Program) : FwdWF p.toLabeled p.procEnv p.main where
  unique := p.toLabeled_uniqueLabels
  main_shape := by
    obtain ⟨z, hz⟩ := p.main.withStartStop_labelFrom 1
    exact ⟨1, _, z, hz, LRepr.labelFrom _ _⟩
  fwd_some := by
    intro id s h
    simp only [procEnv, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, -⟩ := h
    have hx := p.xprocs_find_fwd id
    rw [hd, Option.map_some] at hx
    obtain ⟨d', hd'⟩ := labelProcs_find_isSome _ (p.main.withStartStop.labelFrom 1).2 _ hx
    exact ⟨d'.body, by simp only [LProgram.proc, toLabeled, hd', Option.map_some]⟩
  fwd_body := by
    intro id b h
    simp only [LProgram.proc, toLabeled, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    obtain ⟨s, k, hs, hb⟩ := labelProcs_find_some _ _ _ hd
    rw [p.xprocs_find_fwd, Option.map_eq_some_iff] at hs
    obtain ⟨d₀, hd₀, he⟩ := hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    obtain ⟨z, hz⟩ := d₀.body.withStartStop_labelFrom k
    refine ⟨d₀.body, k, _, z, ?_, hb ▸ hz, LRepr.labelFrom _ _⟩
    simp [procEnv, hd₀]
  inv_some := by
    intro id s h
    simp only [procEnv, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, -⟩ := h
    have hx := p.xprocs_find_inv id
    rw [hd, Option.map_some] at hx
    obtain ⟨d', hd'⟩ := labelProcs_find_isSome _ (p.main.withStartStop.labelFrom 1).2 _ hx
    exact ⟨d'.body, by simp only [LProgram.proc, toLabeled, hd', Option.map_some]⟩
  inv_body := by
    intro id b h
    simp only [LProgram.proc, toLabeled, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    obtain ⟨s, k, hs, hb⟩ := labelProcs_find_some _ _ _ hd
    rw [p.xprocs_find_inv, Option.map_eq_some_iff] at hs
    obtain ⟨d₀, hd₀, he⟩ := hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    obtain ⟨z, hz⟩ := d₀.body.withStartStop_invert_labelFrom k
    refine ⟨d₀.body, k, _, z, ?_, hb ▸ hz, LRepr.labelFrom _ _⟩
    simp [procEnv, hd₀]

/-! ### Lemma "forward-rev" -/

/-- **Lemma "forward-rev".** Let `p = (s p₁ … pₙ)` be a program, and `ℓ` a label such that
`entry(s) ⟶ ℓ` belongs to the CFG of the main program of its labeled version. Then
`⟨ε, s, []⟩ →* ⟨σ, skip, []⟩` (small-step semantics of `p`) iff there exist `ℓ'`, `ℓ''` such
that `⟨ε, entry(s), ℓ, []⟩ ⇀* ⟨σ, ℓ', ℓ'', []⟩` (forward rules on the labeled version of `p`)
with `block(ℓ'') = stop`. -/
theorem Program.smallSteps_iff_fwdSteps (p : Program) {ℓ : Label}
    (hℓ : (p.toLabeled.main.entry, ℓ) ∈ p.toLabeled.mainCFG) (σ : Store) :
    SmallSteps p.procEnv ⟨Store.empty, p.main, []⟩ ⟨σ, .skip, []⟩ ↔
      ∃ ℓ' ℓ'', FwdSteps p.toLabeled ⟨Store.empty, p.toLabeled.main.entry, ℓ, []⟩
          ⟨σ, ℓ', ℓ'', []⟩ ∧ p.toLabeled.block ℓ'' = some .stop :=
  Janus.smallSteps_iff_fwdSteps p.fwdWF hℓ σ

/-- Lemma "forward-rev" stated with initial configurations: for every initial configuration
`k` of the labeled version of `p`, `⟨ε, s, []⟩ →* ⟨σ, skip, []⟩` iff `k ⇀* ⟨σ, ℓ', ℓ'', []⟩`
with `block(ℓ'') = stop`. -/
theorem Program.smallSteps_iff_fwdSteps_of_isInitial (p : Program) {k : RConfig}
    (hk : p.toLabeled.IsInitial k) (σ : Store) :
    SmallSteps p.procEnv ⟨Store.empty, p.main, []⟩ ⟨σ, .skip, []⟩ ↔
      ∃ ℓ' ℓ'', FwdSteps p.toLabeled k ⟨σ, ℓ', ℓ'', []⟩ ∧
        p.toLabeled.block ℓ'' = some .stop := by
  obtain ⟨σ₀, ℓ₀, ℓ, S⟩ := k
  obtain ⟨h1, h2, h3, h4⟩ := hk
  simp only at h1 h2 h3 h4; subst h1 h2 h4
  exact p.smallSteps_iff_fwdSteps h3 σ

/-- Combined with the equivalence between the big-step and the small-step semantics: a
program terminates in store `σ` (big-step semantics) iff the forward rules reach, from an
initial configuration, a configuration `⟨σ, ℓ', ℓ'', []⟩` with `block(ℓ'') = stop`. -/
theorem Program.exec_iff_fwdSteps (p : Program) {ℓ : Label}
    (hℓ : (p.toLabeled.main.entry, ℓ) ∈ p.toLabeled.mainCFG) (σ : Store) :
    p.Exec σ ↔
      ∃ ℓ' ℓ'', FwdSteps p.toLabeled ⟨Store.empty, p.toLabeled.main.entry, ℓ, []⟩
          ⟨σ, ℓ', ℓ'', []⟩ ∧ p.toLabeled.block ℓ'' = some .stop := by
  rw [Program.exec_iff_smallSteps]
  exact p.smallSteps_iff_fwdSteps hℓ σ

end Janus

end
