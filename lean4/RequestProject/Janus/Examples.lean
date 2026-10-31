module

public import RequestProject.Janus.Semantics

/-!
# Janus: sanity-check examples for the big-step semantics
-/

@[expose] public section

namespace Janus.Examples

open Janus

/-- `from i = 0 do i += 1 loop skip until i = 2` -/
def countLoop : Stmt :=
  .loop (.bin .eq (.var "i") (.const 0)) (.assVar "i" .add (.const 1)) .skip
    (.bin .eq (.var "i") (.const 2))

/-- Starting from the empty store, the loop terminates with `i = 2`. -/
example : Exec (fun _ => none) Store.empty countLoop
    ((Store.empty.update (.var "i") 1).update (.var "i") 2) := by
  refine .loopMain (v₁ := 1) (evalExpr_iff_eval.2 (by decide)) (by decide)
    (.assVar (v := 1) (.con 1)) ?_
  refine .loopRec (v₂ := 0) (v₁ := 0) (evalExpr_iff_eval.2 (by decide)) rfl .skip
    (evalExpr_iff_eval.2 (by decide)) rfl (.assVar (v := 1) (.con 1)) ?_
  have hσ : (Store.empty.update (.var "i") 1).update (.var "i") 2 =
      (Store.empty.update (.var "i") (ModOp.add.interp (Store.empty (.var "i")) 1)).update
        (.var "i") (ModOp.add.interp ((Store.empty.update (.var "i")
          (ModOp.add.interp (Store.empty (.var "i")) 1)) (.var "i")) 1) := by
    simp [Store.update, ModOp.interp, Store.empty]
  rw [hσ]
  exact BigStep.loopBase (v₂ := 1) (evalExpr_iff_eval.2 (by decide)) (by decide)

/-- Procedure `f`: `y += x * 2`. -/
def env : ProcEnv := fun id => if id = "f" then some (.assVar "y" .add
  (.bin .mul (.var "x") (.const 2))) else none

/-- `x += 3; call f; uncall f` ends with `x = 3`, `y = 0`. -/
example : Exec env Store.empty
    (.seq (.assVar "x" .add (.const 3)) (.seq (.call "f") (.uncall "f")))
    (Store.empty.update (.var "x") 3) := by
  refine .seq (.assVar (v := 3) (.con 3)) ?_
  refine .seq (.call rfl (.assVar (v := 6) (evalExpr_iff_eval.2 (by decide)))) ?_
  refine .uncall rfl ?_
  have key := BigStep.assVar (Γ := env) (x := "y") (op := ModOp.add.invert)
    (σ := ((Store.empty.update (.var "x") (ModOp.add.interp (Store.empty (.var "x")) 3)).update
      (.var "y") (ModOp.add.interp
        ((Store.empty.update (.var "x") (ModOp.add.interp (Store.empty (.var "x")) 3))
          (.var "y")) 6)))
    (e := .bin .mul (.var "x") (.const 2)) (v := 6) (evalExpr_iff_eval.2 (by decide))
  convert key using 1
  funext l
  by_cases h : l = .var "y"
  · subst h; decide
  · simp [h, Store.update, Function.update, ModOp.interp, Store.empty]

/-- A program with a main body only and no procedure declarations: `x += 1`. -/
def onlyMain : Program := { main := .assVar "x" .add (.const 1), procs := [] }

/-- Running `onlyMain` from the empty store `ε` gives `x = 1`.
Proof: rule `AssVar` with premise `Con`; its conclusion has the store
`ε[x ↦ ⟦+⟧(ε(x), ⟦1⟧)]`, and `h` (closed by `decide`) rewrites `⟦+⟧(ε(x), ⟦1⟧)` to `1`. -/
example : onlyMain.Exec (Store.empty.update (.var "x") 1) := by
  have h : ModOp.add.interp (Store.empty (.var "x")) (Int32.toInt 1) = 1 := by decide
  exact h ▸ BigStep.assVar (EvalExpr.con 1)

end Janus.Examples

end
