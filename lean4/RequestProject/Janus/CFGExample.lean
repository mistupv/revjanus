module

public import RequestProject.Janus.CFG

/-!
# Janus: the running example Sum3 (Figures "Sum3" and "CFGs for program Sum3")

We write the program Sum3 in the original syntax, and check that the construction of the
paper (`Program.toLabeled`: add `start`/`stop`, add inverse procedures, add labels)
produces the labeled program of Figure "Sum3" (labels `1`–`15`), and that `flow` computes
the two CFGs given in the paper:

```
CFG_main    = {(1,2), (2,3), (3,4)}
CFG_sumMul3 = {(5,6), (6,7), (7,8), (8,9), (8,10), (9,11), (10,11),
               (11,13), (13,12), (12,7), (13,14), (14,15)}
```
-/

@[expose] public section

namespace Janus

namespace Sum3

/-- `(i % 3) = 0` -/
def cond3 : Expr := .bin .eq (.bin .rem (.var "i") (.const 3)) (.const 0)
/-- `i = 1` -/
def condEntry : Expr := .bin .eq (.var "i") (.const 1)
/-- `i >= n` -/
def condExit : Expr := .bin .ge (.var "i") (.var "n")

/-- The body of procedure `sumMul3`, in the original syntax:
```
i += 1
from i = 1 do
  if (i % 3) = 0 then total += i else skip fi (i % 3) = 0
loop
  i += 1
until i >= n
n += total
```
-/
def sumMul3Body : Stmt :=
  .seq (.assVar "i" .add (.const 1))
    (.seq (.loop condEntry
            (.ite cond3 (.assVar "total" .add (.var "i")) .skip cond3)
            (.assVar "i" .add (.const 1))
            condExit)
      (.assVar "n" .add (.var "total")))

/-- The program Sum3, in the original syntax: main body `n += 3; call sumMul3`. -/
def program : Program where
  main := .seq (.assVar "n" .add (.const 3)) (.call "sumMul3")
  procs := [{ name := "sumMul3", body := sumMul3Body }]

/-- The labeled main program of Figure "Sum3":
`[start]¹ [n += 3]² [call sumMul3]³ [stop]⁴`. -/
def labeledMain : LStmt Label :=
  .seq (.start 1) (.seq (.seq (.assVar "n" .add (.const 3) 2) (.call "sumMul3" 3)) (.stop 4))

/-- The labeled procedure `sumMul3` of Figure "Sum3" (labels `5`–`15`). -/
def labeledSumMul3 : LStmt Label :=
  .seq (.start 5)
    (.seq
      (.seq (.assVar "i" .add (.const 1) 6)
        (.seq (.loop condEntry 7
                (.ite cond3 8 (.assVar "total" .add (.var "i") 9) (.skip 10) cond3 11)
                (.assVar "i" .add (.const 1) 12)
                condExit 13)
          (.assVar "n" .add (.var "total") 14)))
      (.stop 15))

/-- The construction of the paper yields the labeled main program of Figure "Sum3". -/
theorem toLabeled_main : program.toLabeled.main = labeledMain := by decide

/-- The construction of the paper yields the labeled procedure `sumMul3` of Figure "Sum3";
it is followed by the inverse procedure `sumMul3⁻¹`, i.e. `𝓘⟦sumMul3⟧` relabeled from `16`. -/
theorem toLabeled_procs :
    program.toLabeled.procs =
      [⟨.fwd "sumMul3", labeledSumMul3⟩,
       ⟨.inv "sumMul3", (labeledSumMul3.invert.labelFrom 16).1⟩] := by decide

/-- `CFG_main = {(1,2), (2,3), (3,4)}`. -/
theorem cfg_main : program.toLabeled.mainCFG = {(1, 2), (2, 3), (3, 4)} := by decide

/-- `CFG_sumMul3 = {(5,6), (6,7), (7,8), (8,9), (8,10), (9,11), (10,11), (11,13), (13,12),
(12,7), (13,14), (14,15)}`. -/
theorem cfg_sumMul3 :
    program.toLabeled.procCFG (.fwd "sumMul3") =
      some {(5, 6), (6, 7), (7, 8), (8, 9), (8, 10), (9, 11), (10, 11), (11, 13), (13, 12),
        (12, 7), (13, 14), (14, 15)} := by decide

/-- Some values of `block` and `ctx` on Sum3. -/
example : program.toLabeled.block 8 = some (.cond cond3) := by decide
example : program.toLabeled.block 9 = some (.assVar "total" .add (.var "i")) := by decide
example : program.toLabeled.ctx 11 =
    some (.ite cond3 8 (.assVar "total" .add (.var "i") 9) (.skip 10) cond3 11) := by decide
example : (program.toLabeled.ctx 7).map LStmt.entry = some 7 := by decide

end Sum3

end Janus

end
