module

public import RevJanus.Janus.SmallStep

/-!
# Janus: equivalence of the big-step and small-step semantics

* Lemma "From big-step to small-step" (completeness): `BigStep.toSmallSteps`.
* Lemma "soundness": `Balanced.toBigStep` and `LoopDerivation.toBigStep`.
* Theorem "equiv": `bigStep_iff_smallSteps` (and its program-level version).

Completeness follows the paper's proof (induction on the big-step derivation). For
soundness, instead of the paper's induction on the length of the derivation following the
trace grammar, we show that every transition reflects a big-step "completion" invariant
backwards (`SmallStep.completes_back`); the trace grammar itself is treated separately in
`SmallStepTraces.lean`.

Minor typos in the paper's proofs, which do not affect the results: in case `IfTrue` of the
completeness proof the last configuration should be `⟨σ', skip, S⟩` (not `⟨σ', s₂, S⟩`); in
case `LoopRec` the premise of `Loop2` is `⟨σ', e₁⟩ ⇓ v₁`; in case `CallS bal` of the
soundness proof the induction hypothesis gives `⟨σ, Γ(id)⟩ ⇓ σ'`.
-/

@[expose] public section

namespace Janus

open Relation

/-! ### Completeness -/

/-- Lemma "From big-step to small-step": if `⟨σ, s⟩ ⇓ σ'` then
(a) `⟨σ, s, S⟩ →* ⟨σ', skip, S⟩` if `s` is a proper statement, and
(b) `⟨σ, skip, loop1(e₁,s₁,e₂,s₂) : S⟩ →* ⟨σ', skip, S⟩` if `s = (e₁,s₁,e₂,s₂)`,
for an arbitrary stack `S`. -/
theorem BigStep.toSmallSteps {Γ : ProcEnv} {σ σ' : Store} {c : Code}
    (h : BigStep Γ σ c σ') :
    match c with
    | .stmt s => ∀ S, SmallSteps Γ ⟨σ, s, S⟩ ⟨σ', .skip, S⟩
    | .loopCont e₁ s₁ e₂ s₂ =>
        ∀ S, SmallSteps Γ ⟨σ, .skip, .loop1 e₁ s₁ e₂ s₂ :: S⟩ ⟨σ', .skip, S⟩ := by
  induction h with
  | assVar he => exact fun S => .single (.assVarS he)
  | assArr hl he => exact fun S => .single (.assArrS hl he)
  | call hΓ _ ih => exact fun S => .head (.callS hΓ) (ih S)
  | uncall hΓ _ ih => exact fun S => .head (.uncallS hΓ) (ih S)
  | seq _ _ ih₁ ih₂ =>
    exact fun S => .head .seq1 ((ih₁ _).trans (.head .seq2 (ih₂ S)))
  | ifTrue he₁ ht₁ _ he₂ ht₂ ih =>
    exact fun S => .head (.ifTrue1 he₁ ht₁) ((ih _).tail (.ifTrue2 he₂ ht₂))
  | ifFalse he₁ hf₁ _ he₂ hf₂ ih =>
    exact fun S => .head (.ifFalse1 he₁ hf₁) ((ih _).tail (.ifFalse2 he₂ hf₂))
  | loopMain he₁ ht₁ _ _ ih₁ ih₂ =>
    exact fun S => .head (.loopMainS he₁ ht₁) ((ih₁ _).trans (ih₂ S))
  | loopBase he₂ ht₂ => exact fun S => .single (.loopBaseS he₂ ht₂)
  | loopRec he₂ hf₂ _ he₁ hf₁ _ _ ih₁ ih₂ ih₃ =>
    exact fun S => .head (.loop1 he₂ hf₂)
      ((ih₁ _).trans (.head (.loop2 he₁ hf₁) ((ih₂ _).trans (ih₃ S))))
  | skip => exact fun S => .refl

/-- Completeness, part (a): `⟨σ, s⟩ ⇓ σ'` implies `⟨σ, s, S⟩ →* ⟨σ', skip, S⟩`. -/
theorem Exec.toSmallSteps {Γ : ProcEnv} {σ σ' : Store} {s : Stmt} (h : Exec Γ σ s σ')
    (S : Stack) : SmallSteps Γ ⟨σ, s, S⟩ ⟨σ', .skip, S⟩ :=
  BigStep.toSmallSteps h S

/-- Completeness, part (b): `⟨σ, (e₁,s₁,e₂,s₂)⟩ ⇓ σ'` implies
`⟨σ, skip, loop1(e₁,s₁,e₂,s₂) : S⟩ →* ⟨σ', skip, S⟩`. -/
theorem BigStep.loopCont_toSmallSteps {Γ : ProcEnv} {σ σ' : Store} {e₁ e₂ : Expr}
    {s₁ s₂ : Stmt} (h : BigStep Γ σ (.loopCont e₁ s₁ e₂ s₂) σ') (S : Stack) :
    SmallSteps Γ ⟨σ, .skip, .loop1 e₁ s₁ e₂ s₂ :: S⟩ ⟨σ', .skip, S⟩ :=
  BigStep.toSmallSteps h S

/-! ### Soundness

We give a big-step meaning to stack items and stack segments: `ItemExec Γ σ it σ'` states
that the remaining work recorded by the item `it` takes `σ` to `σ'`. A configuration
`⟨σ, s, F ++ S⟩` *completes* (above the base stack `S`) to `σf` if `⟨σ, s⟩ ⇓ σ₁` and the
items of `F` take `σ₁` to `σf`. Every transition between configurations whose stacks extend
`S` reflects completion backwards; this gives soundness for balanced and loop derivations. -/

/-- Big-step meaning of the remaining work recorded by a stack item. -/
def ItemExec (Γ : ProcEnv) (σ : Store) : StackItem → Store → Prop
  | .seq s₂, σ' => Exec Γ σ s₂ σ'
  | .ifTrue e₂, σ' => σ' = σ ∧ ∃ v, EvalExpr σ e₂ v ∧ IsTrue v
  | .ifFalse e₂, σ' => σ' = σ ∧ ∃ v, EvalExpr σ e₂ v ∧ IsFalse v
  | .loop1 e₁ s₁ e₂ s₂, σ' => BigStep Γ σ (.loopCont e₁ s₁ e₂ s₂) σ'
  | .loop2 e₁ s₁ e₂ s₂, σ' => ∃ v σm, EvalExpr σ e₁ v ∧ IsFalse v ∧ Exec Γ σ s₁ σm ∧
      BigStep Γ σm (.loopCont e₁ s₁ e₂ s₂) σ'

/-- Big-step meaning of a stack segment (top first). -/
def FramesExec (Γ : ProcEnv) : Store → Stack → Store → Prop
  | σ, [], σ' => σ' = σ
  | σ, it :: F, σ' => ∃ σ₁, ItemExec Γ σ it σ₁ ∧ FramesExec Γ σ₁ F σ'

/-- A configuration completes to `σf` above the base stack `S`. -/
def Completes (Γ : ProcEnv) (S : Stack) (σf : Store) (c : SSConfig) : Prop :=
  ∃ F σ₁, c.stack = F ++ S ∧ Exec Γ c.store c.control σ₁ ∧ FramesExec Γ σ₁ F σf

@[simp] theorem FramesExec.nil_iff {Γ : ProcEnv} {σ σ' : Store} :
    FramesExec Γ σ [] σ' ↔ σ' = σ := Iff.rfl

@[simp] theorem FramesExec.cons_iff {Γ : ProcEnv} {σ σ' : Store} {it : StackItem}
    {F : Stack} :
    FramesExec Γ σ (it :: F) σ' ↔ ∃ σ₁, ItemExec Γ σ it σ₁ ∧ FramesExec Γ σ₁ F σ' := Iff.rfl

/-- Helper for pop rules: popping the item `it` from `⟨σ, skip, it : T⟩`. -/
theorem completes_pop {Γ : ProcEnv} {S T F₁ : Stack} {σf σ σ₁ : Store} {it : StackItem}
    (hst : T = F₁ ++ S) (hit : ItemExec Γ σ it σ₁) (hfr : FramesExec Γ σ₁ F₁ σf) :
    Completes Γ S σf ⟨σ, .skip, it :: T⟩ :=
  ⟨it :: F₁, σ, by simp [hst], .skip, FramesExec.cons_iff.2 ⟨σ₁, hit, hfr⟩⟩

/-- Helper for push rules: the new frame segment is the old one with the pushed item. -/
theorem frames_of_push {S F₁ T : Stack} {it : StackItem} (hS : S <:+ T)
    (h : it :: T = F₁ ++ S) : ∃ F, T = F ++ S ∧ F₁ = it :: F := by
  obtain ⟨F, rfl⟩ := hS
  refine ⟨F, rfl, ?_⟩
  have : (it :: F) ++ S = F₁ ++ S := h
  exact (List.append_cancel_right this).symm

/-- Helper for rules `Loop1` and `Loop2`, which replace the top item by a different one. -/
theorem frames_of_swap {S T F₁ : Stack} {it it' : StackItem} (hne : it ≠ it')
    (hS : S <:+ it :: T) (h : it' :: T = F₁ ++ S) : ∃ F, F₁ = it' :: F ∧ T = F ++ S := by
  cases F₁ with
  | nil =>
    simp only [List.nil_append] at h
    subst h
    exact absurd (List.cons.inj (hS.eq_of_length (by simp))).1.symm hne
  | cons a F =>
    simp only [List.cons_append, List.cons.injEq] at h
    exact ⟨F, by rw [h.1], h.2⟩

/-- One transition reflects completion backwards (for configurations above the base stack
`S`). -/
theorem SmallStep.completes_back {Γ : ProcEnv} {S : Stack} {σf : Store} {c c' : SSConfig}
    (hstep : SmallStep Γ c c') (hS : S <:+ c.stack) (h : Completes Γ S σf c') :
    Completes Γ S σf c := by
  obtain ⟨F₁, σ₁, hst, hex, hfr⟩ := h
  cases hstep with
  | assVarS he =>
    cases hex
    exact ⟨F₁, _, hst, .assVar he, hfr⟩
  | assArrS hl he =>
    cases hex
    exact ⟨F₁, _, hst, .assArr hl he, hfr⟩
  | callS hΓ => exact ⟨F₁, σ₁, hst, .call hΓ hex, hfr⟩
  | uncallS hΓ => exact ⟨F₁, σ₁, hst, .uncall hΓ hex, hfr⟩
  | seq1 =>
    obtain ⟨F, hF, rfl⟩ := frames_of_push hS hst
    obtain ⟨σ₂, h₂, hfr₂⟩ := FramesExec.cons_iff.1 hfr
    exact ⟨F, σ₂, hF, .seq hex h₂, hfr₂⟩
  | seq2 => exact completes_pop hst hex hfr
  | ifTrue1 he₁ ht₁ =>
    obtain ⟨F, hF, rfl⟩ := frames_of_push hS hst
    obtain ⟨σ₂, ⟨rfl, v, he₂, ht₂⟩, hfr₂⟩ := FramesExec.cons_iff.1 hfr
    exact ⟨F, _, hF, .ifTrue he₁ ht₁ hex he₂ ht₂, hfr₂⟩
  | ifTrue2 he₂ ht₂ =>
    cases hex
    exact completes_pop hst ⟨rfl, _, he₂, ht₂⟩ hfr
  | ifFalse1 he₁ hf₁ =>
    obtain ⟨F, hF, rfl⟩ := frames_of_push hS hst
    obtain ⟨σ₂, ⟨rfl, v, he₂, hf₂⟩, hfr₂⟩ := FramesExec.cons_iff.1 hfr
    exact ⟨F, _, hF, .ifFalse he₁ hf₁ hex he₂ hf₂, hfr₂⟩
  | ifFalse2 he₂ hf₂ =>
    cases hex
    exact completes_pop hst ⟨rfl, _, he₂, hf₂⟩ hfr
  | loopMainS he₁ ht₁ =>
    obtain ⟨F, hF, rfl⟩ := frames_of_push hS hst
    obtain ⟨σ₂, h₂, hfr₂⟩ := FramesExec.cons_iff.1 hfr
    exact ⟨F, σ₂, hF, .loopMain he₁ ht₁ hex h₂, hfr₂⟩
  | loopBaseS he₂ ht₂ =>
    cases hex
    exact completes_pop hst (.loopBase he₂ ht₂) hfr
  | loop1 he₂ hf₂ =>
    obtain ⟨F, rfl, hF⟩ := frames_of_swap (by simp) hS hst
    obtain ⟨σ₂, ⟨v, σm, he₁, hf₁, hm, hl⟩, hfr₂⟩ := FramesExec.cons_iff.1 hfr
    exact completes_pop hF (.loopRec he₂ hf₂ hex he₁ hf₁ hm hl) hfr₂
  | loop2 he₁ hf₁ =>
    obtain ⟨F, rfl, hF⟩ := frames_of_swap (by simp) hS hst
    obtain ⟨σ₂, hl, hfr₂⟩ := FramesExec.cons_iff.1 hfr
    exact completes_pop hF ⟨_, _, he₁, hf₁, hex, hl⟩ hfr₂

/-- A derivation whose intermediate stacks all extend `S` reflects completion backwards. -/
theorem completes_back_of_within {Γ : ProcEnv} {S : Stack} {σf : Store} {P : Stack → Prop}
    (hP : ∀ T, P T → S <:+ T) {c c' : SSConfig}
    (h : ReflTransGen (SmallStepWithin Γ P) c c') (hc : S <:+ c.stack)
    (h' : Completes Γ S σf c') : Completes Γ S σf c := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact h'
  | head hstep _ ih => exact hstep.1.completes_back hc (ih (hP _ hstep.2))

/-- Lemma "soundness", balanced case: if `⟨σ, s, S₁⟩ →* ⟨σ', skip, S₂⟩` is balanced, then
`S₁ = S₂` and `⟨σ, s⟩ ⇓ σ'`. (Statements in configurations are always proper.) -/
theorem Balanced.toBigStep {Γ : ProcEnv} {σ σ' : Store} {s : Stmt} {S₁ S₂ : Stack}
    (h : Balanced Γ ⟨σ, s, S₁⟩ ⟨σ', .skip, S₂⟩) : S₁ = S₂ ∧ Exec Γ σ s σ' := by
  obtain ⟨hS, hd⟩ := h
  simp only at hS
  subst hS
  refine ⟨rfl, ?_⟩
  have := completes_back_of_within (σf := σ') (fun _ h => h) hd (List.suffix_refl _)
    ⟨[], σ', rfl, .skip, rfl⟩
  obtain ⟨F, σ₁, hF, hex, hfr⟩ := this
  have : F = [] := by simpa using hF
  subst this
  cases hfr
  exact hex

/-- Lemma "soundness", loop case: a loop derivation
`⟨σ, skip, loop1(e₁,s₁,e₂,s₂) : S⟩ →* ⟨σ', skip, S⟩` implies
`⟨σ, (e₁,s₁,e₂,s₂)⟩ ⇓ σ'`. -/
theorem LoopDerivation.toBigStep {Γ : ProcEnv} {σ σ' : Store} {e₁ e₂ : Expr} {s₁ s₂ : Stmt}
    {S : Stack} (h : LoopDerivation Γ σ e₁ s₁ e₂ s₂ S σ') :
    BigStep Γ σ (.loopCont e₁ s₁ e₂ s₂) σ' := by
  obtain ⟨c, hd, hlast⟩ := h
  have hsuf : ∀ T, (StackItem.loop1 e₁ s₁ e₂ s₂ :: S <:+ T ∨
      StackItem.loop2 e₁ s₁ e₂ s₂ :: S <:+ T) → S <:+ T := by
    rintro T (hT | hT) <;> exact (List.suffix_cons _ _).trans hT
  have hc : S <:+ c.stack := by
    cases hd.cases_tail with
    | inl h => subst h; exact List.suffix_cons _ _
    | inr h =>
      obtain ⟨b, _, hb⟩ := h
      exact hsuf _ hb.2
  have hcomp := hlast.completes_back hc ⟨[], σ', rfl, .skip, rfl⟩
  have := completes_back_of_within (σf := σ') hsuf hd (List.suffix_cons _ _) hcomp
  obtain ⟨F, σ₁, hF, hex, hfr⟩ := this
  cases hex
  have : F = [StackItem.loop1 e₁ s₁ e₂ s₂] := by
    have h' : [StackItem.loop1 e₁ s₁ e₂ s₂] ++ S = F ++ S := hF
    exact (List.append_cancel_right h').symm
  subst this
  obtain ⟨σ₂, h₂, rfl⟩ := hfr
  exact h₂

/-- Any derivation starting from an empty stack and ending with an empty stack is
balanced. -/
theorem balanced_of_nil {Γ : ProcEnv} {c c' : SSConfig} (h₁ : c.stack = [])
    (h₂ : c'.stack = []) (h : SmallSteps Γ c c') : Balanced Γ c c' := by
  refine ⟨h₁.trans h₂.symm, ?_⟩
  refine ReflTransGen.mono (fun a b hab => ⟨hab, ?_⟩) h
  rw [h₁]; exact List.nil_suffix

/-- A balanced derivation is in particular a derivation. -/
theorem Balanced.smallSteps {Γ : ProcEnv} {c c' : SSConfig} (h : Balanced Γ c c') :
    SmallSteps Γ c c' :=
  ReflTransGen.mono (fun _ _ h => h.1) h.2

/-! ### Equivalence -/

/-- Theorem "equiv": `⟨ε, s⟩ ⇓ σ` iff `⟨ε, s, []⟩ →* ⟨σ, skip, []⟩`. -/
theorem bigStep_iff_smallSteps {Γ : ProcEnv} {s : Stmt} {σ : Store} :
    Exec Γ Store.empty s σ ↔ SmallSteps Γ ⟨Store.empty, s, []⟩ ⟨σ, .skip, []⟩ :=
  ⟨fun h => h.toSmallSteps [],
   fun h => (Balanced.toBigStep (balanced_of_nil rfl rfl h)).2⟩

/-- Generalization of Theorem "equiv" to an arbitrary initial store and stack:
`⟨σ, s⟩ ⇓ σ'` iff there is a balanced derivation `⟨σ, s, S⟩ →* ⟨σ', skip, S⟩`. -/
theorem exec_iff_balanced {Γ : ProcEnv} {s : Stmt} {σ σ' : Store} {S : Stack} :
    Exec Γ σ s σ' ↔ Balanced Γ ⟨σ, s, S⟩ ⟨σ', .skip, S⟩ := by
  constructor
  · intro h
    refine ⟨rfl, ?_⟩
    -- re-run completeness, keeping track of the stack invariant
    have key : ∀ {σ σ' : Store} {c : Code}, BigStep Γ σ c σ' →
        match c with
        | .stmt s => ∀ S, ReflTransGen (SmallStepWithin Γ (fun S' => S <:+ S'))
            ⟨σ, s, S⟩ ⟨σ', .skip, S⟩
        | .loopCont e₁ s₁ e₂ s₂ => ∀ S, ReflTransGen (SmallStepWithin Γ
            (fun S' => S <:+ S')) ⟨σ, .skip, .loop1 e₁ s₁ e₂ s₂ :: S⟩ ⟨σ', .skip, S⟩ := by
      intro σ σ' c h
      have mono : ∀ {S : Stack} {it : StackItem} {a b : SSConfig},
          ReflTransGen (SmallStepWithin Γ (fun S' => it :: S <:+ S')) a b →
          ReflTransGen (SmallStepWithin Γ (fun S' => S <:+ S')) a b :=
        fun h => ReflTransGen.mono
          (fun _ _ h => ⟨h.1, (List.suffix_cons _ _).trans h.2⟩) h
      have sfx : ∀ {S : Stack} {it : StackItem}, S <:+ it :: S := List.suffix_cons _ _
      induction h with
      | assVar he => exact fun S => .single ⟨.assVarS he, List.suffix_refl _⟩
      | assArr hl he => exact fun S => .single ⟨.assArrS hl he, List.suffix_refl _⟩
      | call hΓ _ ih => exact fun S => .head ⟨.callS hΓ, List.suffix_refl _⟩ (ih S)
      | uncall hΓ _ ih => exact fun S => .head ⟨.uncallS hΓ, List.suffix_refl _⟩ (ih S)
      | seq _ _ ih₁ ih₂ =>
        exact fun S => .head ⟨.seq1, sfx⟩
          ((mono (ih₁ _)).trans (.head ⟨.seq2, List.suffix_refl _⟩ (ih₂ S)))
      | ifTrue he₁ ht₁ _ he₂ ht₂ ih =>
        exact fun S => .head ⟨.ifTrue1 he₁ ht₁, sfx⟩
          ((mono (ih _)).tail ⟨.ifTrue2 he₂ ht₂, List.suffix_refl _⟩)
      | ifFalse he₁ hf₁ _ he₂ hf₂ ih =>
        exact fun S => .head ⟨.ifFalse1 he₁ hf₁, sfx⟩
          ((mono (ih _)).tail ⟨.ifFalse2 he₂ hf₂, List.suffix_refl _⟩)
      | loopMain he₁ ht₁ _ _ ih₁ ih₂ =>
        exact fun S => .head ⟨.loopMainS he₁ ht₁, sfx⟩ ((mono (ih₁ _)).trans (ih₂ S))
      | loopBase he₂ ht₂ => exact fun S => .single ⟨.loopBaseS he₂ ht₂, List.suffix_refl _⟩
      | loopRec he₂ hf₂ _ he₁ hf₁ _ _ ih₁ ih₂ ih₃ =>
        exact fun S => .head ⟨.loop1 he₂ hf₂, sfx⟩
          ((mono (ih₁ _)).trans (.head ⟨.loop2 he₁ hf₁, sfx⟩ ((mono (ih₂ _)).trans (ih₃ S))))
      | skip => exact fun S => .refl
    exact key h S
  · intro h; exact h.toBigStep.2

/-- Theorem "equiv" for programs: running the main statement of `p` from the empty store
terminates in `σ` (big-step) iff the initial configuration `⟨ε, s, []⟩` of `p` reaches
`⟨σ, skip, []⟩` (small-step). -/
theorem Program.exec_iff_smallSteps (p : Program) (σ : Store) :
    p.Exec σ ↔ SmallSteps p.procEnv p.initConfig ⟨σ, .skip, []⟩ :=
  bigStep_iff_smallSteps

end Janus

end
