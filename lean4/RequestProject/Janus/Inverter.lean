module

public import RequestProject.Janus.Syntax

/-!
# Janus: the inverter function `𝓘`

Figure "Inverter function for Janus statements" of the paper:

```
𝓘ₒₚ⟦+⟧ = -    𝓘ₒₚ⟦-⟧ = +    𝓘ₒₚ⟦^⟧ = ^
𝓘⟦x ⊕= e⟧                          = x 𝓘ₒₚ⟦⊕⟧= e
𝓘⟦x[e₁] ⊕= e₂⟧                     = x[e₁] 𝓘ₒₚ⟦⊕⟧= e₂
𝓘⟦if e₁ then s₁ else s₂ fi e₂⟧     = if e₂ then 𝓘⟦s₁⟧ else 𝓘⟦s₂⟧ fi e₁
𝓘⟦from e₁ do s₁ loop s₂ until e₂⟧  = from e₂ do 𝓘⟦s₁⟧ loop 𝓘⟦s₂⟧ until e₁
𝓘⟦call id⟧ = uncall id    𝓘⟦uncall id⟧ = call id    𝓘⟦skip⟧ = skip
𝓘⟦s₁ s₂⟧ = 𝓘⟦s₂⟧ 𝓘⟦s₁⟧
𝓘⟦procedure id s⟧ = procedure id⁻¹ 𝓘⟦s⟧
```
-/

@[expose] public section

namespace Janus

/-- Inversion of update operators, `𝓘ₒₚ`. -/
def ModOp.invert : ModOp → ModOp
  | .add => .sub
  | .sub => .add
  | .xor => .xor

/-- The inverter function `𝓘` on statements. -/
def Stmt.invert : Stmt → Stmt
  | .assVar x op e => .assVar x op.invert e
  | .assArr x e₁ op e₂ => .assArr x e₁ op.invert e₂
  | .ite e₁ s₁ s₂ e₂ => .ite e₂ s₁.invert s₂.invert e₁
  | .loop e₁ s₁ s₂ e₂ => .loop e₂ s₁.invert s₂.invert e₁
  | .call id => .uncall id
  | .uncall id => .call id
  | .skip => .skip
  | .seq s₁ s₂ => .seq s₂.invert s₁.invert

/-- Inversion of a procedure declaration: `𝓘⟦procedure id s⟧ = procedure id⁻¹ 𝓘⟦s⟧`.
The paper's name `id⁻¹` is a fresh name for the inverse procedure; it is supplied here
by the parameter `invName` (in the semantics, the inverse of `id` is always reached
through `uncall id`, which uses `Stmt.invert` directly). -/
def ProcDecl.invert (invName : ProcId → ProcId) (d : ProcDecl) : ProcDecl :=
  { name := invName d.name, body := d.body.invert }

@[simp] theorem ModOp.invert_invert (op : ModOp) : op.invert.invert = op := by
  cases op <;> rfl

/-- The inverter is an involution. -/
@[simp] theorem Stmt.invert_invert (s : Stmt) : s.invert.invert = s := by
  induction s <;> simp_all [Stmt.invert]

/-- Inversion preserves well-formedness. -/
theorem Stmt.WellFormed.invert {s : Stmt} (h : s.WellFormed) : s.invert.WellFormed := by
  induction s <;> simp_all [Stmt.invert, Stmt.WellFormed]

end Janus

end
