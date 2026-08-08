/-
Core data types for Metamath specification.

This file contains the foundational types used throughout the Metamath
verification system. It has NO dependencies - pure type definitions only.

Per Metamath Specification Chapter 4:
- §4.2.2: Math symbols (constants and variables)
- §4.2.5: Floating hypotheses
- §4.2.5–4.2.6: Essential hypotheses and assertions
- §4.2.7: Frames (mandatory hypotheses)
- §4.2.4: Disjoint variable constraints
- §4.2.2, §4.1.4: Substitutions
-/

namespace Metamath.Spec

/-! ## Core Types

Metamath has three kinds of symbols:
- Constants (declared with $c)
- Variables (declared with $v)
- Labels (for statements)
-/

abbrev Sym := String

/-- Global constant set (as a predicate). -/
abbrev ConstSet := Sym → Prop
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
Per spec §4.2.5: "floating hypothesis has the form 'C v'"
Per spec §4.2.5–4.2.6: "essential hypothesis or assertion has typecode first"
-/

structure Expr where
  typecode : Constant
  syms : List Sym
  deriving Repr, DecidableEq

/-! ## Hypotheses and Frames

Per spec §4.2.5 (hypotheses) and §4.2.7 (frames):
- Floating hypotheses: $f C v (associates variable with typecode)
- Essential hypotheses: $e C sym1 sym2... (logical assumptions)
- Frame: all mandatory hypotheses for an assertion, in appearance order
-/

inductive Hyp where
  | floating : Constant → Variable → Hyp
  | essential : Expr → Hyp
  deriving Repr, DecidableEq

structure Frame where
  /-- Hypotheses in appearance order.
      When stored in Database: mandatory hypotheses (spec §4.2.7).
      When converted from scope frame: all active hypotheses (spec §4.2.7–4.2.8). -/
  hyps : List Hyp
  /-- Disjoint variable constraints (spec §4.2.4) -/
  dv : List (Variable × Variable)
  deriving Repr, DecidableEq

/-- Extract the set of variables from a frame's floating hypotheses.
    Per §4.2.5: floating hypotheses declare variables. -/
def Frame.vars (fr : Frame) : List Variable :=
  fr.hyps.filterMap fun h => match h with
    | Hyp.floating _ v => some v
    | Hyp.essential _ => none

/-! ## Substitutions

A substitution maps variables to expressions.
Per spec §4.2.4 and §4.1.4: substitutions must respect disjoint variable constraints.
-/

abbrev Subst := Variable → Expr

/-! ## Disjoint Variable Checking

Per spec §4.2.4: "Two variables are disjoint if they appear in a $d statement
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
Per spec §4.2.6:
- Axioms ($a): asserted without proof
- Theorems ($p): proved from axioms and previous theorems
-/

abbrev Database := Label → Option (Frame × Expr)

/-! ## Database Well-Formedness

A well-formed database satisfies key invariants:
1. Variables in expressions must have floating hypotheses in scope (§4.1.3)
2. Constants and variables are disjoint (global declaration)

These are enforced by the parser's insert function.
-/

/-- Variables in an expression must have floating hypotheses in the frame,
    or be declared constants.

    Per §4.1.3: "Each variable that occurs in the math symbol sequence of an
    assertion must have an active $f statement."
    Per §4.1.3: "$c declares constants, $v declares variables" (global sets). -/
def ExprVarsInScope (consts : ConstSet) (fr : Frame) (e : Expr) : Prop :=
  ∀ s ∈ e.syms, Variable.mk s ∈ fr.vars ∨ consts s

/-- All expressions in a frame (assertion + essential hypotheses) have variables in scope. -/
def FrameExprsInScope (consts : ConstSet) (fr : Frame) (e : Expr) : Prop :=
  ExprVarsInScope consts fr e ∧
  ∀ h ∈ fr.hyps, match h with
    | Hyp.essential e_hyp => ExprVarsInScope consts fr e_hyp
    | Hyp.floating _ _ => True

/-- Frame variables are disjoint from the global constant set. -/
def FrameVarsDisjointConsts (consts : ConstSet) (fr : Frame) : Prop :=
  ∀ v ∈ fr.vars, ¬ consts v.v

/-- A database is well-formed if all expressions have their variables in scope.
    This captures the Metamath invariant that the parser enforces. -/
def WellFormedDatabase (Γ : Database) (consts : ConstSet) : Prop :=
  (∀ l fr e, Γ l = some (fr, e) → FrameExprsInScope consts fr e) ∧
  (∀ l fr e, Γ l = some (fr, e) → FrameVarsDisjointConsts consts fr)

/-- Key consequence: if a symbol is not a variable in the frame, it is a constant. -/
theorem const_global_of_wellFormed {Γ : Database} {consts : ConstSet}
    {fr : Frame} {e : Expr} {l : Label}
    (h_wf : WellFormedDatabase Γ consts)
    (h_lookup : Γ l = some (fr, e))
    (s : Sym)
    (h_s_in : s ∈ e.syms)
    (h_not_var : Variable.mk s ∉ fr.vars) :
    consts s := by
  have h := (h_wf.1 l fr e h_lookup).1 s h_s_in
  cases h with
  | inl h_in => exact absurd h_in h_not_var
  | inr h_const => exact h_const

/-- Same property for essential hypothesis expressions. -/
theorem const_global_of_wellFormed_hyp {Γ : Database} {consts : ConstSet}
    {fr : Frame} {e e_hyp : Expr} {l : Label}
    (h_wf : WellFormedDatabase Γ consts)
    (h_lookup : Γ l = some (fr, e))
    (h_hyp_in : Hyp.essential e_hyp ∈ fr.hyps)
    (s : Sym)
    (h_s_in : s ∈ e_hyp.syms)
    (h_not_var : Variable.mk s ∉ fr.vars) :
    consts s := by
  have h_frame := (h_wf.1 l fr e h_lookup)
  have h_hyp := h_frame.2 (Hyp.essential e_hyp) h_hyp_in
  simp only at h_hyp
  have h := h_hyp s h_s_in
  cases h with
  | inl h_in => exact absurd h_in h_not_var
  | inr h_const => exact h_const

end Metamath.Spec

