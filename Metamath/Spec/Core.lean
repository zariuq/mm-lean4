/-
Core data types for Metamath specification.

This file contains the foundational types used throughout the Metamath
verification system. It has NO dependencies - pure type definitions only.

Per Metamath Specification Chapter 4:
- §4.2.1: Math symbols (constants and variables)
- §4.2.2: Floating hypotheses
- §4.2.3: Essential hypotheses and assertions
- §4.2.4: Frames (mandatory hypotheses)
- §4.2.5: Disjoint variable constraints
- §4.2.6: Substitutions
-/

namespace Metamath.Spec

/-! ## Core Types

Metamath has three kinds of symbols:
- Constants (declared with $c)
- Variables (declared with $v)
- Labels (for statements)
-/

abbrev Sym := String
abbrev Label := String

structure Constant where
  c : Sym
  deriving DecidableEq, Repr

@[simp] theorem beq_const_true_iff {c₁ c₂ : Constant} :
  (c₁ == c₂) = true ↔ c₁ = c₂ := by
  constructor
  · intro h
    cases decide_eq_true_eq.mp h
    rfl
  · intro h
    subst h
    exact decide_eq_true_eq.mpr rfl

structure Variable where
  v : Sym
  deriving DecidableEq, Repr

/-- Extensionality for Variables: two variables are equal iff their symbol fields are equal. -/
theorem Variable.ext (v w : Variable) : v.v = w.v → v = w := by
  intro h
  cases v
  cases w
  simp only at h
  rw [h]

/-! ## Expressions

An expression is a typecode followed by a sequence of symbols.
Per spec §4.2.2: "floating hypothesis has the form 'C v'"
Per spec §4.2.3: "essential hypothesis or assertion has typecode first"
-/

structure Expr where
  typecode : Constant
  syms : List Sym
  deriving Repr, DecidableEq

/-! ## Hypotheses and Frames

Per spec §4.2.4:
- Floating hypotheses: $f C v (associates variable with typecode)
- Essential hypotheses: $e C sym1 sym2... (logical assumptions)
- Frame: all mandatory hypotheses for an assertion, in appearance order
-/

inductive Hyp where
  | floating : Constant → Variable → Hyp
  | essential : Expr → Hyp
  deriving Repr, DecidableEq

structure Frame where
  /-- Mandatory hypotheses in appearance order (spec §4.2.4) -/
  mand : List Hyp
  /-- Disjoint variable constraints (spec §4.2.5) -/
  dv : List (Variable × Variable)
  deriving Repr, DecidableEq

/-- Extract the set of variables from a frame's floating hypotheses.
    Per §4.2.2: floating hypotheses declare variables. -/
def Frame.vars (fr : Frame) : List Variable :=
  fr.mand.filterMap fun h => match h with
    | Hyp.floating _ v => some v
    | Hyp.essential _ => none

/-! ## Substitutions

A substitution maps variables to expressions.
Per spec §4.2.6: substitutions must respect disjoint variable constraints.
-/

abbrev Subst := Variable → Expr

/-! ## Disjoint Variable Checking

Per spec §4.2.5: "Two variables are disjoint if they appear in a $d statement
together in the same frame."

For substitution σ to respect DV constraints:
- If (v,w) ∈ dv, then σ(v) and σ(w) share no variables

Per §4.2.1: "The characters making up a math symbol are irrelevant to Metamath."
Variables vs constants are determined by $v/$c declarations, NOT by symbol names.
Therefore we pass the active variable set explicitly.
-/

def varsInExpr (vars : List Variable) (e : Expr) : List Variable :=
  e.syms.filterMap fun s =>
    let v := Variable.mk s
    if v ∈ vars then some v else none

def dvRel (dv : List (Variable × Variable)) (v w : Variable) : Prop :=
  v ≠ w ∧ ((v, w) ∈ dv ∨ (w, v) ∈ dv)

def dvOK (vars : List Variable) (dvSource dvTarget : List (Variable × Variable)) (σ : Subst) : Prop :=
  ∀ (v w : Variable), (v, w) ∈ dvSource →
    let vs := varsInExpr vars (σ v)
    let ws := varsInExpr vars (σ w)
    ∀ x ∈ vs, ∀ y ∈ ws, dvRel dvTarget x y

/-- A substitution `σ` is the identity on a set of variables `vs` if
    for every `v ∈ vs`, we have `σ v = ⟨(σ v).typecode, [v.v]⟩`.

This is used for composition lemmas in KernelExtras. -/
def Subst.IdOn (σ : Subst) (vs : List Variable) : Prop :=
  ∀ v ∈ vs, σ v = ⟨(σ v).typecode, [v.v]⟩

/-! ## Substitution Application

Applying a substitution to an expression:
- Constants unchanged
- Variables (determined by membership in vars list) replaced by σ(v)

Per §4.2.1: symbol names are arbitrary; only $v/$c declarations matter.
-/

def applySubst (vars : List Variable) (σ : Subst) (e : Expr) : Expr :=
  { typecode := e.typecode
    syms := e.syms.flatMap fun s =>
      let v := Variable.mk s
      if v ∈ vars then (σ v).syms else [s] }

/-! ## Assertion Database

The database Γ maps labels to (frame, assertion).
Per spec §4.2.3:
- Axioms ($a): asserted without proof
- Theorems ($p): proved from axioms and previous theorems
-/

abbrev Database := Label → Option (Frame × Expr)

end Metamath.Spec
