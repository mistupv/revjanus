module

public import Mathlib

/-!
# Janus: syntax

This file formalizes the syntax of (sequential) Janus, following Figure "Language syntax"
of the paper:

```
p ::= s (procedure id s)*
s ::= x ⊕= e | x[e] ⊕= e | if e then s else s fi e
    | from e do s loop s until e | call id | uncall id | skip | s s
e ::= c | x | x[e] | e ⊙ e                 ⊕ ::= + | - | ^
c ::= -2147483648 | … | 0 | … | 2147483647
⊙ ::= ⊕ | * | / | % | & | && | || | "|" | < | > | = | != | <= | >=
```

Constants are restricted to 32-bit signed integers, as in the grammar, so they are
typed `Int32` (`Const`). Following the default behaviour of the Jana interpreter, values
are unbounded integers (`Int`); a constant `c` denotes the integer `c.toInt`.

Besides the grammar, the paper imposes the side condition that, in a reversible
assignment `x ⊕= e` (resp. `x[e₁] ⊕= e₂`), the left-hand-side variable `x` does not
occur in `e` (resp. in `e₁` and `e₂`). This is not part of the grammar, so we capture it
by the well-formedness predicate `Stmt.WellFormed`.
-/

@[expose] public section

namespace Janus

/-- Variable names (both scalar variables and array names). -/
abbrev Var := String

/-- Procedure identifiers. -/
abbrev ProcId := String

/-- Values: unbounded integers (default behaviour of the Jana interpreter). -/
abbrev Value := Int

/-- Constants `c`: 32-bit signed integers, ranging from `-2147483648` to `2147483647`
(Figure "Language syntax"). A constant `c` denotes the value `c.toInt`. -/
abbrev Const := Int32

/-- Reversible update operators `⊕ ::= + | - | ^` (`^` is bitwise xor). -/
inductive ModOp where
  /-- `+` -/
  | add
  /-- `-` -/
  | sub
  /-- `^` (bitwise exclusive or) -/
  | xor
  deriving DecidableEq, Repr, Inhabited

/-- Binary operators `⊙ ::= ⊕ | * | / | % | & | && | || | "|" | < | > | = | != | <= | >=`. -/
inductive BinOp where
  /-- One of the reversible update operators `+`, `-`, `^`. -/
  | mod (op : ModOp)
  /-- `*` -/
  | mul
  /-- `/` -/
  | div
  /-- `%` -/
  | rem
  /-- `&` (bitwise and) -/
  | band
  /-- `&&` (logical and) -/
  | land
  /-- `||` (logical or) -/
  | lor
  /-- `|` (bitwise or) -/
  | bor
  /-- `<` -/
  | lt
  /-- `>` -/
  | gt
  /-- `=` -/
  | eq
  /-- `!=` -/
  | ne
  /-- `<=` -/
  | le
  /-- `>=` -/
  | ge
  deriving DecidableEq, Repr, Inhabited

/-- Expressions `e ::= c | x | x[e] | e ⊙ e`. -/
inductive Expr where
  /-- A constant `c`. -/
  | const (c : Const)
  /-- A variable `x`. -/
  | var (x : Var)
  /-- An array access `x[e]`. -/
  | arr (x : Var) (e : Expr)
  /-- A binary operation `e₁ ⊙ e₂`. -/
  | bin (op : BinOp) (e₁ e₂ : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- Statements
`s ::= x ⊕= e | x[e] ⊕= e | if e then s else s fi e | from e do s loop s until e
     | call id | uncall id | skip | s s`. -/
inductive Stmt where
  /-- Reversible assignment `x ⊕= e`. -/
  | assVar (x : Var) (op : ModOp) (e : Expr)
  /-- Reversible array-element assignment `x[e₁] ⊕= e₂`. -/
  | assArr (x : Var) (e₁ : Expr) (op : ModOp) (e₂ : Expr)
  /-- Reversible conditional `if e₁ then s₁ else s₂ fi e₂`
  (`e₁` is the test, `e₂` the exit assertion). -/
  | ite (e₁ : Expr) (s₁ s₂ : Stmt) (e₂ : Expr)
  /-- Reversible loop `from e₁ do s₁ loop s₂ until e₂`
  (`e₁` is the entry assertion, `e₂` the exit test). -/
  | loop (e₁ : Expr) (s₁ s₂ : Stmt) (e₂ : Expr)
  /-- Procedure call `call id`. -/
  | call (id : ProcId)
  /-- Procedure uncall `uncall id` (runs the inverse of the procedure). -/
  | uncall (id : ProcId)
  /-- `skip` -/
  | skip
  /-- Sequential composition `s₁ s₂`. -/
  | seq (s₁ s₂ : Stmt)
  deriving DecidableEq, Repr, Inhabited

/-- A procedure declaration `procedure id s`. As in the paper, procedures have
neither parameters nor local variables. -/
structure ProcDecl where
  /-- The procedure name `id`. -/
  name : ProcId
  /-- The procedure body `s`. -/
  body : Stmt
  deriving DecidableEq, Repr, Inhabited

/-- A program `p ::= s (procedure id s)*`: a main statement followed by a (possibly
empty) sequence of procedure declarations. -/
structure Program where
  /-- The main body. -/
  main : Stmt
  /-- The procedure declarations (possibly none). -/
  procs : List ProcDecl

/-! ### Variables and well-formedness -/

/-- The variables (scalar or array names) occurring in an expression. -/
def Expr.vars : Expr → List Var
  | .const _ => []
  | .var x => [x]
  | .arr x e => x :: e.vars
  | .bin _ e₁ e₂ => e₁.vars ++ e₂.vars

/-- Well-formedness of statements: in every reversible assignment `x ⊕= e`
(resp. `x[e₁] ⊕= e₂`) the left-hand-side variable `x` does not occur in `e`
(resp. in `e₁` and `e₂`). -/
def Stmt.WellFormed : Stmt → Prop
  | .assVar x _ e => x ∉ e.vars
  | .assArr x e₁ _ e₂ => x ∉ e₁.vars ∧ x ∉ e₂.vars
  | .ite _ s₁ s₂ _ => s₁.WellFormed ∧ s₂.WellFormed
  | .loop _ s₁ s₂ _ => s₁.WellFormed ∧ s₂.WellFormed
  | .call _ => True
  | .uncall _ => True
  | .skip => True
  | .seq s₁ s₂ => s₁.WellFormed ∧ s₂.WellFormed

instance Stmt.decidableWellFormed : (s : Stmt) → Decidable s.WellFormed
  | .assVar x _ e => inferInstanceAs (Decidable (x ∉ e.vars))
  | .assArr x e₁ _ e₂ => inferInstanceAs (Decidable (x ∉ e₁.vars ∧ x ∉ e₂.vars))
  | .ite _ s₁ s₂ _ =>
    have := Stmt.decidableWellFormed s₁; have := Stmt.decidableWellFormed s₂
    inferInstanceAs (Decidable (s₁.WellFormed ∧ s₂.WellFormed))
  | .loop _ s₁ s₂ _ =>
    have := Stmt.decidableWellFormed s₁; have := Stmt.decidableWellFormed s₂
    inferInstanceAs (Decidable (s₁.WellFormed ∧ s₂.WellFormed))
  | .call _ => isTrue trivial
  | .uncall _ => isTrue trivial
  | .skip => isTrue trivial
  | .seq s₁ s₂ =>
    have := Stmt.decidableWellFormed s₁; have := Stmt.decidableWellFormed s₂
    inferInstanceAs (Decidable (s₁.WellFormed ∧ s₂.WellFormed))

/-- A program is well formed when all its statements (main body and procedure bodies)
are well formed and procedure names are pairwise distinct. -/
def Program.WellFormed (p : Program) : Prop :=
  p.main.WellFormed ∧ (∀ d ∈ p.procs, d.body.WellFormed) ∧ (p.procs.map (·.name)).Nodup

end Janus

end
