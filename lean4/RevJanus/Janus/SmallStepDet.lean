module

public import RevJanus.Janus.SmallStep

/-!
# Janus: determinism of the small-step semantics (sanity check)
-/

@[expose] public section

namespace Janus

/-- The transition relation `→` is deterministic. -/
theorem SmallStep.det {Γ : ProcEnv} {c c₁ c₂ : SSConfig}
    (h₁ : SmallStep Γ c c₁) (h₂ : SmallStep Γ c c₂) : c₁ = c₂ := by
  cases h₁ with
  | assVarS he => cases h₂ with | assVarS he' => rw [he.det he']
  | assArrS hl he => cases h₂ with | assArrS hl' he' => rw [hl.det hl', he.det he']
  | callS hΓ => cases h₂ with | callS hΓ' => rw [hΓ] at hΓ'; cases hΓ'; rfl
  | uncallS hΓ => cases h₂ with | uncallS hΓ' => rw [hΓ] at hΓ'; cases hΓ'; rfl
  | seq1 => cases h₂; rfl
  | seq2 => cases h₂; rfl
  | ifTrue1 he ht =>
    cases h₂ with
    | ifTrue1 => rfl
    | ifFalse1 he' hf => exact absurd (he.det he' ▸ hf) ht
  | ifTrue2 => cases h₂; rfl
  | ifFalse1 he hf =>
    cases h₂ with
    | ifTrue1 he' ht => exact absurd (he'.det he ▸ hf) ht
    | ifFalse1 => rfl
  | ifFalse2 => cases h₂; rfl
  | loopMainS => cases h₂; rfl
  | loopBaseS he ht =>
    cases h₂ with
    | loopBaseS => rfl
    | loop1 he' hf => exact absurd (he.det he' ▸ hf) ht
  | loop1 he hf =>
    cases h₂ with
    | loopBaseS he' ht => exact absurd (he'.det he ▸ hf) ht
    | loop1 => rfl
  | loop2 => cases h₂; rfl

end Janus

end
