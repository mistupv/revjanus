module

public import RequestProject.Janus.Inverter

/-!
# Janus: labeled syntax (Section "A Reversible Semantics for Janus")

This file formalizes the extended, labeled syntax of Figure "Extended language syntax":

```
p ::= s (procedure id s)*
s ::= [x ⊕= e]^ℓ | [x[e] ⊕= e]^ℓ | if [e]^ℓ then s else s fi [e]^ℓ
    | from [e]^ℓ do s loop s until [e]^ℓ | [call id]^ℓ | [uncall id]^ℓ | [skip]^ℓ | s s
    | [start]^ℓ | [stop]^ℓ
```

where expressions `e` and update operators `⊕` are as in the original syntax.

## Modelling choices

* Statements of the extended syntax are `LStmt L`, parametrized by the type `L` of the
  annotations attached to elementary blocks. The labeled statements of the paper are
  `LStmt Label`, with labels `ℓ ∈ 𝓛` taken to be natural numbers (`Label := ℕ`), as in the
  running example. The *unlabeled* extended syntax (original syntax plus `start`/`stop`),
  on which the inverter is applied before labels are added, is `LStmt Unit` (`XStmt`).
* Elementary blocks `o` (conditions, assignments, `call`, `uncall`, `skip`, `start`,
  `stop`) are `Block`. `LStmt.blocks` lists the pairs `(ℓ, o)` such that `[o]^ℓ` occurs in a
  statement, in textual order. `block(ℓ) = o` is `LProgram.block`; it is meaningful when
  "all labels are unique in a program", i.e. `LProgram.UniqueLabels`.
* The inverter is extended to the new syntax (`LStmt.invert`) with
  `𝓘⟦start⟧ = stop` and `𝓘⟦stop⟧ = start`; labels stay attached to their block.
* Labeled programs contain, for each procedure `procedure id s`, also its inverse
  `procedure id⁻¹ 𝓘⟦s⟧`. Procedure names in labeled programs are therefore `PName`:
  either `id` (`PName.fwd id`) or `id⁻¹` (`PName.inv id`).
* The three-step construction of the paper (add inverse procedures, add labels) is
  `Program.toLabeled`. Since the paper assumes that every program and procedure body starts
  with `start` and ends with `stop`, an original (unlabeled) body `s` becomes
  `start (s stop)` (`Stmt.withStartStop`). Labels are assigned consecutively, starting at
  `1`, in textual order: first the main program, then the procedures, then the inverse
  procedures. This reproduces the labels of the running example (Figure "Sum3").
  We prove that the resulting program has unique labels (`Program.toLabeled_uniqueLabels`).
-/

@[expose] public section

namespace Janus

/-- The domain of labels `𝓛`. -/
abbrev Label := Nat

/-- Statements of the extended syntax, whose elementary blocks carry an annotation of type
`L` (a label `ℓ` for `L = Label`; nothing for `L = Unit`). -/
inductive LStmt (L : Type) where
  /-- `[x ⊕= e]^ℓ` -/
  | assVar (x : Var) (op : ModOp) (e : Expr) (ℓ : L)
  /-- `[x[e₁] ⊕= e₂]^ℓ` -/
  | assArr (x : Var) (e₁ : Expr) (op : ModOp) (e₂ : Expr) (ℓ : L)
  /-- `if [e₁]^ℓ₁ then s₁ else s₂ fi [e₂]^ℓ₂` -/
  | ite (e₁ : Expr) (ℓ₁ : L) (s₁ s₂ : LStmt L) (e₂ : Expr) (ℓ₂ : L)
  /-- `from [e₁]^ℓ₁ do s₁ loop s₂ until [e₂]^ℓ₂` -/
  | loop (e₁ : Expr) (ℓ₁ : L) (s₁ s₂ : LStmt L) (e₂ : Expr) (ℓ₂ : L)
  /-- `[call id]^ℓ` -/
  | call (id : ProcId) (ℓ : L)
  /-- `[uncall id]^ℓ` -/
  | uncall (id : ProcId) (ℓ : L)
  /-- `[skip]^ℓ` -/
  | skip (ℓ : L)
  /-- `s₁ s₂` -/
  | seq (s₁ s₂ : LStmt L)
  /-- `[start]^ℓ` -/
  | start (ℓ : L)
  /-- `[stop]^ℓ` -/
  | stop (ℓ : L)
  deriving DecidableEq, Repr

/-- Unlabeled statements of the extended syntax (the original syntax plus `start` and
`stop`). -/
abbrev XStmt := LStmt Unit

/-- Elementary blocks `o`: conditions (tests and assertions), assignments, `call`,
`uncall`, `skip`, `start` and `stop`. -/
inductive Block where
  /-- `x ⊕= e` -/
  | assVar (x : Var) (op : ModOp) (e : Expr)
  /-- `x[e₁] ⊕= e₂` -/
  | assArr (x : Var) (e₁ : Expr) (op : ModOp) (e₂ : Expr)
  /-- A condition `e` (a test or an assertion of a conditional or loop). -/
  | cond (e : Expr)
  /-- `call id` -/
  | call (id : ProcId)
  /-- `uncall id` -/
  | uncall (id : ProcId)
  /-- `skip` -/
  | skip
  /-- `start` -/
  | start
  /-- `stop` -/
  | stop
  deriving DecidableEq, Repr

namespace LStmt

variable {L L' α : Type}

/-- The pairs `(ℓ, o)` such that `[o]^ℓ` occurs in a statement, in textual order. -/
def blocks : LStmt L → List (L × Block)
  | .assVar x op e ℓ => [(ℓ, .assVar x op e)]
  | .assArr x e₁ op e₂ ℓ => [(ℓ, .assArr x e₁ op e₂)]
  | .ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ => (ℓ₁, .cond e₁) :: (s₁.blocks ++ s₂.blocks ++ [(ℓ₂, .cond e₂)])
  | .loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ => (ℓ₁, .cond e₁) :: (s₁.blocks ++ s₂.blocks ++ [(ℓ₂, .cond e₂)])
  | .call id ℓ => [(ℓ, .call id)]
  | .uncall id ℓ => [(ℓ, .uncall id)]
  | .skip ℓ => [(ℓ, .skip)]
  | .seq s₁ s₂ => s₁.blocks ++ s₂.blocks
  | .start ℓ => [(ℓ, .start)]
  | .stop ℓ => [(ℓ, .stop)]

/-- The labels occurring in a statement, in textual order. -/
def labels (s : LStmt L) : List L := s.blocks.map Prod.fst

/-- Relabeling: apply `f` to every label. -/
def map (f : L → L') : LStmt L → LStmt L'
  | .assVar x op e ℓ => .assVar x op e (f ℓ)
  | .assArr x e₁ op e₂ ℓ => .assArr x e₁ op e₂ (f ℓ)
  | .ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ => .ite e₁ (f ℓ₁) (s₁.map f) (s₂.map f) e₂ (f ℓ₂)
  | .loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ => .loop e₁ (f ℓ₁) (s₁.map f) (s₂.map f) e₂ (f ℓ₂)
  | .call id ℓ => .call id (f ℓ)
  | .uncall id ℓ => .uncall id (f ℓ)
  | .skip ℓ => .skip (f ℓ)
  | .seq s₁ s₂ => .seq (s₁.map f) (s₂.map f)
  | .start ℓ => .start (f ℓ)
  | .stop ℓ => .stop (f ℓ)

/-- Forgetting the labels of a statement. -/
def erase (s : LStmt L) : XStmt := s.map fun _ => ()

/-- The inverter `𝓘` extended to the new syntax, with `𝓘⟦start⟧ = stop` and
`𝓘⟦stop⟧ = start`. Each label stays attached to its elementary block. -/
def invert : LStmt L → LStmt L
  | .assVar x op e ℓ => .assVar x op.invert e ℓ
  | .assArr x e₁ op e₂ ℓ => .assArr x e₁ op.invert e₂ ℓ
  | .ite e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ => .ite e₂ ℓ₂ s₁.invert s₂.invert e₁ ℓ₁
  | .loop e₁ ℓ₁ s₁ s₂ e₂ ℓ₂ => .loop e₂ ℓ₂ s₁.invert s₂.invert e₁ ℓ₁
  | .call id ℓ => .uncall id ℓ
  | .uncall id ℓ => .call id ℓ
  | .skip ℓ => .skip ℓ
  | .seq s₁ s₂ => .seq s₂.invert s₁.invert
  | .start ℓ => .stop ℓ
  | .stop ℓ => .start ℓ

/-- Labeling: `s.labelFrom n` replaces the annotations of the elementary blocks of `s` by
consecutive labels `n, n+1, …`, in textual order, and returns the next unused label. -/
def labelFrom : LStmt α → Label → LStmt Label × Label
  | .assVar x op e _, n => (.assVar x op e n, n + 1)
  | .assArr x e₁ op e₂ _, n => (.assArr x e₁ op e₂ n, n + 1)
  | .ite e₁ _ s₁ s₂ e₂ _, n =>
    let r₁ := s₁.labelFrom (n + 1)
    let r₂ := s₂.labelFrom r₁.2
    (.ite e₁ n r₁.1 r₂.1 e₂ r₂.2, r₂.2 + 1)
  | .loop e₁ _ s₁ s₂ e₂ _, n =>
    let r₁ := s₁.labelFrom (n + 1)
    let r₂ := s₂.labelFrom r₁.2
    (.loop e₁ n r₁.1 r₂.1 e₂ r₂.2, r₂.2 + 1)
  | .call id _, n => (.call id n, n + 1)
  | .uncall id _, n => (.uncall id n, n + 1)
  | .skip _, n => (.skip n, n + 1)
  | .seq s₁ s₂, n =>
    let r₁ := s₁.labelFrom n
    let r₂ := s₂.labelFrom r₁.2
    (.seq r₁.1 r₂.1, r₂.2)
  | .start _, n => (.start n, n + 1)
  | .stop _, n => (.stop n, n + 1)

/-! ### Basic properties -/

@[simp] theorem invert_invert (s : LStmt L) : s.invert.invert = s := by
  induction s <;> simp_all [invert]

theorem labelFrom_snd (s : LStmt α) (n : Label) :
    (s.labelFrom n).2 = n + s.blocks.length := by
  induction s generalizing n <;> simp_all [labelFrom, blocks] <;> ring

private theorem range'_split3 (n a b : ℕ) : List.range' n (a + b + 1 + 1) =
    n :: (List.range' (n + 1) a ++ List.range' (n + 1 + a) b ++ [n + 1 + a + b]) := by
  rw [List.range'_append_1, List.range'_succ, List.range'_concat]
  simp only [one_mul]
  congr 3; omega

/-- Labeling assigns the consecutive labels `n, …, n + k - 1`, in textual order, where `k`
is the number of elementary blocks. -/
theorem labels_labelFrom (s : LStmt α) (n : Label) :
    (s.labelFrom n).1.labels = List.range' n s.blocks.length := by
  induction s generalizing n with
  | ite e₁ _ s₁ s₂ e₂ _ ih₁ ih₂ =>
    simp only [labelFrom, labels, blocks, List.map_cons, List.map_append, List.map_nil,
      List.length_cons, List.length_append, List.length_nil, Nat.zero_add] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, labelFrom_snd, labelFrom_snd, range'_split3]
  | loop e₁ _ s₁ s₂ e₂ _ ih₁ ih₂ =>
    simp only [labelFrom, labels, blocks, List.map_cons, List.map_append, List.map_nil,
      List.length_cons, List.length_append, List.length_nil, Nat.zero_add] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, labelFrom_snd, labelFrom_snd, range'_split3]
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [labelFrom, labels, blocks, List.map_append] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, labelFrom_snd, List.length_append, List.range'_append_1]
  | _ => simp [labelFrom, labels, blocks]

/-- Labeling does not change the underlying (unlabeled) statement. -/
@[simp] theorem erase_labelFrom (s : LStmt α) (n : Label) :
    (s.labelFrom n).1.erase = s.erase := by
  induction s generalizing n <;> simp_all [labelFrom, erase, map]

end LStmt

/-! ### Embedding the original syntax -/

/-- The original statements are statements of the (unlabeled) extended syntax. -/
def Stmt.toX : Stmt → XStmt
  | .assVar x op e => .assVar x op e ()
  | .assArr x e₁ op e₂ => .assArr x e₁ op e₂ ()
  | .ite e₁ s₁ s₂ e₂ => .ite e₁ () s₁.toX s₂.toX e₂ ()
  | .loop e₁ s₁ s₂ e₂ => .loop e₁ () s₁.toX s₂.toX e₂ ()
  | .call id => .call id ()
  | .uncall id => .uncall id ()
  | .skip => .skip ()
  | .seq s₁ s₂ => .seq s₁.toX s₂.toX

/-- The extended inverter agrees with the original one on the original syntax. -/
theorem Stmt.toX_invert (s : Stmt) : s.invert.toX = s.toX.invert := by
  induction s <;> simp_all [Stmt.invert, Stmt.toX, LStmt.invert]

/-- A (main or procedure) body `s` of the original syntax, delimited by `start` and
`stop`: `start (s stop)`. -/
def Stmt.withStartStop (s : Stmt) : XStmt := .seq (.start ()) (.seq s.toX (.stop ()))

/-! ### Labeled programs -/

/-- Procedure names of labeled programs: a procedure `id` of the original program, or the
inverse procedure `id⁻¹` introduced for it. -/
inductive PName where
  /-- The procedure `id`. -/
  | fwd (id : ProcId)
  /-- The inverse procedure `id⁻¹`. -/
  | inv (id : ProcId)
  deriving DecidableEq, Repr

/-- A procedure declaration `procedure id s` of the extended syntax. -/
structure LProcDecl (L : Type) where
  /-- The procedure name (`id` or `id⁻¹`). -/
  name : PName
  /-- The procedure body. -/
  body : LStmt L
  deriving DecidableEq, Repr

/-- A program `p ::= s (procedure id s)*` of the extended syntax. -/
structure LProgram (L : Type) where
  /-- The main body. -/
  main : LStmt L
  /-- The procedure declarations. -/
  procs : List (LProcDecl L)
  deriving DecidableEq, Repr

namespace LProgram

variable {L : Type}

/-- The pairs `(ℓ, o)` such that `[o]^ℓ` belongs to the program. -/
def blocks (p : LProgram L) : List (L × Block) :=
  p.main.blocks ++ p.procs.flatMap fun d => d.body.blocks

/-- The labels of a program. -/
def labels (p : LProgram L) : List L := p.blocks.map Prod.fst

/-- "All labels are unique in a program." -/
def UniqueLabels (p : LProgram L) : Prop := p.labels.Nodup

/-- `block(ℓ) = o` if `[o]^ℓ` belongs to the program (a partial function). -/
def block [DecidableEq L] (p : LProgram L) (ℓ : L) : Option Block := p.blocks.lookup ℓ

/-- When labels are unique, `block(ℓ) = o` holds exactly when `[o]^ℓ` belongs to the
program. -/
theorem block_eq_some_iff [DecidableEq L] {p : LProgram L} (hp : p.UniqueLabels) (ℓ : L)
    (o : Block) : p.block ℓ = some o ↔ (ℓ, o) ∈ p.blocks := by
  unfold block
  unfold UniqueLabels labels at hp
  generalize p.blocks = bs at hp ⊢
  induction bs with
  | nil => simp [List.lookup]
  | cons b bs ih =>
    obtain ⟨k, v⟩ := b
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hp
    by_cases h : ℓ = k
    · subst h
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, List.mem_cons,
        Prod.mk.injEq, true_and]
      constructor
      · rintro rfl; exact Or.inl rfl
      · rintro (rfl | hm)
        · rfl
        · exact absurd ⟨_, hm, rfl⟩ hp.1
    · have : (ℓ == k) = false := by simpa using h
      simp only [List.lookup, this, List.mem_cons, Prod.mk.injEq, h, false_and, false_or]
      exact ih hp.2

end LProgram

/-- Labeling a list of procedure declarations, starting from label `n`. -/
def labelProcs {α : Type} : List (PName × LStmt α) → Label → List (LProcDecl Label) × Label
  | [], n => ([], n)
  | (id, s) :: ds, n =>
    let r := s.labelFrom n
    let rs := labelProcs ds r.2
    (⟨id, r.1⟩ :: rs.1, rs.2)

theorem labelProcs_snd {α : Type} (ds : List (PName × LStmt α)) (n : Label) :
    (labelProcs ds n).2 = n + (ds.flatMap fun d => d.2.blocks).length := by
  induction ds generalizing n with
  | nil => simp [labelProcs]
  | cons d ds ih =>
    simp [labelProcs, ih, LStmt.labelFrom_snd, Nat.add_assoc]

theorem labels_labelProcs {α : Type} (ds : List (PName × LStmt α)) (n : Label) :
    ((labelProcs ds n).1.flatMap fun d => d.body.blocks).map Prod.fst =
      List.range' n (ds.flatMap fun d => d.2.blocks).length := by
  induction ds generalizing n with
  | nil => simp [labelProcs]
  | cons d ds ih =>
    simp only [labelProcs, List.flatMap_cons, List.map_append, List.length_append]
    have h := LStmt.labels_labelFrom d.2 n
    simp only [LStmt.labels] at h
    rw [h, ih, LStmt.labelFrom_snd, List.range'_append_1]

/-- The procedures of the labeled version of a program, before labeling: each procedure
`procedure id s` together with its inverse `procedure id⁻¹ 𝓘⟦s⟧` (bodies delimited by
`start` and `stop`). The procedures come first, then the inverse procedures. -/
def Program.xprocs (p : Program) : List (PName × XStmt) :=
  p.procs.map (fun d => (PName.fwd d.name, d.body.withStartStop)) ++
  p.procs.map (fun d => (PName.inv d.name, d.body.withStartStop.invert))

/-- The labeled version of a program, obtained as in the paper:
1. for each procedure `procedure id s` an inverse procedure `procedure id⁻¹ 𝓘⟦s⟧` is
   introduced;
2. labels are added to each elementary block (consecutively from `1`, in textual order:
   main program, procedures, inverse procedures).

Bodies are delimited by `start` and `stop` (`Stmt.withStartStop`). -/
def Program.toLabeled (p : Program) : LProgram Label :=
  let m := p.main.withStartStop.labelFrom 1
  { main := m.1, procs := (labelProcs p.xprocs m.2).1 }

/-- The labels of the labeled version of a program are `1, 2, …, k`. -/
theorem Program.labels_toLabeled (p : Program) :
    p.toLabeled.labels =
      List.range' 1 (p.main.withStartStop.blocks.length +
        (p.xprocs.flatMap fun d => d.2.blocks).length) := by
  simp only [toLabeled, LProgram.labels, LProgram.blocks, List.map_append]
  have h := LStmt.labels_labelFrom p.main.withStartStop 1
  simp only [LStmt.labels] at h
  rw [h, labels_labelProcs, LStmt.labelFrom_snd, List.range'_append_1]

/-- All labels are unique in the labeled version of a program. -/
theorem Program.toLabeled_uniqueLabels (p : Program) : p.toLabeled.UniqueLabels := by
  unfold LProgram.UniqueLabels
  rw [Program.labels_toLabeled]
  exact List.nodup_range'

end Janus

end
