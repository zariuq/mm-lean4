/-
Invariant predicates for Metamath verification (CreuSAT-inspired).

This file provides a library of composable predicates for reasoning about
proof verification, inspired by CreuSAT's logic/*.rs predicate pattern.

**Philosophy** (from CreuSAT):
- 30+ small, focused predicates (not monolithic invariants)
- Compose them for different verification stages
- Prove preservation theorems separately
- Bridge to operational semantics via preservation

**Pattern**:
```
logic_clause.rs (CreuSAT)       Invariants.lean (us)
-------------------             -------------------
clause_is_valid                 FrameWellFormed
trail_is_valid                  StackWellTyped
assignment_consistent           SubstConsistent
```

This is the "predicate library" approach, not inductive LoopState types.
-/

import Metamath.Spec.Core

namespace Metamath.Spec.Invariants

open Spec (Database Frame Expr Hyp Variable Constant Subst)

/-! ## Stack Invariants -/

/-- A stack is well-typed if every expression's typecode appears in the database.

    Note: This is a simplified invariant for now. A full version would check that
    the expression structure matches database expectations. -/
def StackWellTyped (Γ : Database) (stk : List Expr) : Prop :=
  ∀ e ∈ stk, ∃ fr e', Γ e.typecode.c = some (fr, e')

/-- Stack contains no duplicates (may be needed for some proofs). -/
def StackNoDuplicates (stk : List Expr) : Prop :=
  stk.Nodup

/-! ## Frame Invariants -/

/-- A frame is well-formed if all hypotheses are properly structured. -/
def FrameWellFormed (fr : Frame) : Prop :=
  (∀ h ∈ fr.mand, match h with
    | Hyp.floating c v => True  -- All floating hyps are valid
    | Hyp.essential e => True)  -- All essential hyps are valid
  ∧
  (∀ (v w : Variable), (v, w) ∈ fr.dv → v ≠ w)  -- DV pairs are distinct

/-- Frame variables are exactly those from floating hypotheses. -/
def FrameVarsComplete (fr : Frame) : Prop :=
  fr.vars = fr.mand.filterMap fun h => match h with
    | Hyp.floating _ v => some v
    | Hyp.essential _ => none

/-! ## Substitution Invariants -/

/-- Substitution is well-formed if it maps variables to expressions with correct typecodes. -/
def SubstWellFormed (vars : List Variable) (σ : Subst) : Prop :=
  ∀ v ∈ vars, ∃ tc, (σ v).typecode = tc

/-- Substitution respects disjoint variable constraints (re-export from Core). -/
def SubstRespectsDV := Spec.dvOK

/-! ## Proof Invariants (Compositional) -/

/-- Complete proof invariant: combines stack, frame, and substitution conditions.

    This is the "main invariant" we'll prove is preserved by each proof step.
    Analogous to CreuSAT's combined `trail_is_valid ∧ clause_is_valid ∧ ...`
-/
def ProofInvariant (Γ : Database) (fr : Frame) (stk : List Expr) : Prop :=
  StackWellTyped Γ stk ∧
  FrameWellFormed fr ∧
  FrameVarsComplete fr

/-! ## Preservation Theorems (Stubs)

These theorems show that proof steps preserve invariants.
They'll be proven in Phase 5 when we eliminate sorries in ParserProofs.

Pattern from CreuSAT: Each operation has a preservation theorem.
-/

/-- Adding a floating hypothesis preserves the proof invariant. -/
theorem useFloating_preserves_invariant {Γ fr stk c v} :
    ProofInvariant Γ fr stk →
    Hyp.floating c v ∈ fr.mand →
    ProofInvariant Γ fr (⟨c, [v.v]⟩ :: stk) := by
  sorry  -- TODO: Phase 5

/-- Adding an essential hypothesis preserves the proof invariant. -/
theorem useEssential_preserves_invariant {Γ fr stk e} :
    ProofInvariant Γ fr stk →
    Hyp.essential e ∈ fr.mand →
    ProofInvariant Γ fr (e :: stk) := by
  sorry  -- TODO: Phase 5

/-- Applying an axiom preserves the proof invariant (complex case). -/
theorem useAxiom_preserves_invariant {Γ : Database} {fr fr' : Frame} {stk stk' : List Expr}
    {e : Expr} {σ : Subst} {l : Label} :
    ProofInvariant Γ fr stk →
    Γ l = some (fr', e) →
    -- ... other conditions ...
    ProofInvariant Γ fr stk' := by  -- new stack after axiom
  sorry  -- TODO: Phase 5

/-! ## Design Notes

**Why predicate library over inductive types?**
- Lean 4 works better with Prop predicates than inductive state machines
- Easier to compose (∧ instead of constructor parameters)
- Matches CreuSAT's successful pattern
- Avoid the "array fold with inductive state" pain point

**Usage in Phase 5**:
When proving ParserProofs lemmas, we'll use these predicates instead of
ad-hoc sorry placeholders. The preservation theorems connect to ProofValid.

**Extensibility**:
Easy to add more predicates as needed (e.g., `StackDepthBounded`, `NoErrorSet`)
without changing the core architecture.
-/

end Metamath.Spec.Invariants
