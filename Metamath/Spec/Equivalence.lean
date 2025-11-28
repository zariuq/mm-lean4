/-
Bridge between Operational and Semantic layers.

This file proves the equivalence between:
- **Operational**: Our ProofValid (stack machine semantics)
- **Semantic**: Mario's Provable (declarative mathematics)

**The key theorem** (soundness + completeness):
```lean
theorem operational_iff_semantic :
  Operational.Provable Γ fr e ↔ Semantic.Provable (dbToAxioms Γ) (frameToContext fr vars) (exprToFormula e)
```

This is the architectural centerpiece connecting implementation to mathematics.
-/

import Metamath.Spec.Core
import Metamath.Spec.Operational
import Metamath.Spec.Semantic
import Metamath.Spec.Bridge

namespace Metamath.Spec.Equivalence

open Spec (Database Frame Expr Hyp Variable Constant Label Subst ProofValid Provable)
open Semantic (Provable)
open Bridge

/-! ## Helper Conversions

We need to convert between our operational types and Mario's semantic types.
Most conversions are in Bridge.lean, but we need additional context-dependent ones.
-/

/-- Convert our Database to Mario's axiom set.

    Our Database maps labels to (Frame, Expr).
    Mario's axiom set is (Statement → Prop).

    Strategy: A statement is an axiom if its label exists in our database. -/
noncomputable def dbToAxioms (Γ : Database) (vars : List MarioVR) : Semantic.Statement → Prop :=
  fun stmt => ∃ (l : Label) (fr : Frame) (e : Expr),
    Γ l = some (fr, e) ∧
    Frame.toMarioContext fr vars = stmt.ctx ∧
    -- Convert our Expr to Mario's Formula
    (∃ marioExpr, Expr.toMarioExpr e vars = marioExpr ∧
                  stmt.fmla = (e.typecode.c, marioExpr))

/-- Convert Frame to Context, given variable list for DJ conversion. -/
noncomputable def frameToContext (fr : Frame) (vars : List MarioVR) : Semantic.Context :=
  Frame.toMarioContext fr vars

/-- Convert Expr to Formula. -/
def exprToFormula (e : Expr) (vars : List MarioVR) : Semantic.Formula :=
  (e.typecode.c, Expr.toMarioExpr e vars)

/-! ## Relational Bridge Interface (Maximum Flexibility)

These relations provide a "simulation" view of the conversion, allowing more
flexible reasoning in complex proofs (CompCert-style forward simulation).
-/

/-- Bridge relation for expressions: relates our Expr to Mario's Formula given context -/
def ExprBridge (e : Expr) (f : MarioFormula) (vars : List MarioVR) : Prop :=
  exprToFormula e vars = f

/-- Bridge relation for hypotheses: relates our Hyp to Mario's Formula -/
def HypBridge (h : Hyp) (f : MarioFormula) (vars : List MarioVR) : Prop :=
  Hyp.toMarioFormula h vars = f

/-- Bridge relation for frames: relates our Frame to Mario's Context -/
def FrameBridge (fr : Frame) (ctx : MarioContext) (vars : List MarioVR) : Prop :=
  Frame.toMarioContext fr vars = ctx

/-! ## Helper Lemmas for Bridge Theorem

These lemmas prove that our conversions preserve structure correctly.
**Key for bridge theorem**: They show equivalences and preservation through conversions.
-/

/-- Essential hypothesis conversion matches exprToFormula -/
theorem Hyp.toMarioFormula_essential (e : Expr) (vars : List MarioVR) :
    Hyp.toMarioFormula (Hyp.essential e) vars = exprToFormula e vars := by
  unfold Hyp.toMarioFormula exprToFormula
  cases e with | mk typecode syms =>
  simp [Expr.toMarioExpr]

/-- Floating hypothesis for single-variable expression matches exprToFormula.

    This shows the correspondence between our floating hypothesis representation
    and the expression-based formula representation for single-variable expressions.

    **Well-formedness assumption**: The vars list must contain Variable.toMarioVR v c.c
    for this to hold. This is a reasonable assumption for well-formed contexts. -/
theorem Hyp.toMarioFormula_floating_expr (c : Constant) (v : Variable) (vars : List MarioVR)
    (h_wf : Variable.toMarioVR v c.c ∈ vars) :
    Hyp.toMarioFormula (Hyp.floating c v) vars = exprToFormula ⟨c, [v.v]⟩ vars := by
  -- Unfold both sides
  unfold exprToFormula Bridge.Hyp.toMarioFormula Bridge.Expr.toMarioExpr
  simp only [List.map]
  -- LHS: (c.c, [.const c.c, .var (Variable.toMarioVR v c.c)])
  -- RHS: (c.c, [.const c.c, String.toMarioSym v.v vars])
  -- These match IF String.toMarioSym v.v vars = .var (Variable.toMarioVR v c.c)
  congr 1
  congr 1
  -- Goal: String.toMarioSym v.v vars = .var (Variable.toMarioVR v c.c)
  exact Bridge.String.toMarioSym_finds_var v (Variable.toMarioVR v c.c) vars h_wf
          (Bridge.Variable.roundtrip v c.c)

/-! ## Forward Direction: ProofValid → Mario.Provable

The key challenge: Our ProofValid tracks the proof stack explicitly,
while Mario's Provable is purely declarative.

Strategy:
- Induction on ProofValid derivation
- Each constructor (nil, useEssential, useFloating, useAxiom) maps to Mario's constructors
- Use Bridge conversions to translate types
-/

/-- Forward direction: If we have a valid operational proof ending with [e],
    then e is provable in Mario's semantic system.

    This is the **soundness** direction we need for Phase 5.

    We use Frame.toVarList to construct the variable list from floating hypotheses,
    which guarantees well-formedness (proven by Frame.toVarList_complete).

    Proof strategy:
    1. Induct on ProofValid
    2. Each constructor maps to Mario's Provable constructors via Bridge conversions
    3. Show dbToAxioms correctly represents our Database -/
theorem proofValid_to_mario {Γ : Database} {fr : Frame} {e : Expr} {steps : List ProofStep} :
    ProofValid Γ fr [e] steps →
    Semantic.Provable (dbToAxioms Γ (Frame.toVarList fr)) (frameToContext fr (Frame.toVarList fr))
                       (exprToFormula e (Frame.toVarList fr)) := by
  intro h
  -- Induction on h, but we know the stack is [e] from the type
  -- Use cases to extract the structure
  cases h with
  | useEssential _ _ e h_in h_prev =>
      -- useEssential adds e to stack
      -- We have: h_in : Hyp.essential e ∈ fr.mand
      -- Goal: exprToFormula e (Frame.toVarList fr) ∈ (frameToContext fr (Frame.toVarList fr)).hyps
      -- Apply Mario's hyp constructor
      apply Metamath.Provable.hyp
      -- Goal: exprToFormula e (Frame.toVarList fr) ∈ (frameToContext fr (Frame.toVarList fr)).hyps
      unfold frameToContext
      -- Goal: exprToFormula e (Frame.toVarList fr) ∈ (Frame.toMarioContext fr (Frame.toVarList fr)).hyps
      -- Use helper lemmas to connect through Hyp.toMarioFormula
      rw [← Hyp.toMarioFormula_essential e (Frame.toVarList fr)]
      -- Goal: Hyp.toMarioFormula (Hyp.essential e) (Frame.toVarList fr) ∈ (Frame.toMarioContext fr (Frame.toVarList fr)).hyps
      exact Bridge.Hyp.toMarioFormula_mem h_in

  | useFloating _ _ c v h_in h_prev =>
      -- useFloating adds ⟨c, [v.v]⟩ to stack
      -- We have: h_in : Hyp.floating c v ∈ fr.mand
      -- Goal: exprToFormula ⟨c, [v.v]⟩ (Frame.toVarList fr) ∈ (frameToContext fr (Frame.toVarList fr)).hyps
      -- Apply Mario's hyp constructor
      apply Metamath.Provable.hyp
      unfold frameToContext
      -- Use Frame.toVarList_complete to get well-formedness
      have h_vr_in : Variable.toMarioVR v c.c ∈ Frame.toVarList fr :=
        Bridge.Frame.toVarList_complete fr c v h_in
      rw [← Hyp.toMarioFormula_floating_expr c v (Frame.toVarList fr) h_vr_in]
      -- Goal: Hyp.toMarioFormula (Hyp.floating c v) (Frame.toVarList fr) ∈ (Frame.toMarioContext fr (Frame.toVarList fr)).hyps
      exact Bridge.Hyp.toMarioFormula_mem h_in

  | useAxiom _ _ l frAx eAx σ h_ax h_dv h_dv' h_prev h_needed h_stack_eq =>
      -- useAxiom applies substitution σ to axiom (frAx, eAx) and adds to stack
      -- We have:
      --   h_ax : Γ l = some (frAx, eAx)
      --   h_dv : dvOK fr.vars fr.dv σ
      --   h_dv' : dvOK frAx.vars frAx.dv σ
      --   h_prev : ProofValid for previous stack
      --   h_needed : ∀ h ∈ frAx.mand, ProofValid ...
      --   h_stack_eq : describes final stack structure

      -- Convert our substitution to Mario's
      let σ_mario := Bridge.Subst.toMarioSubst σ vars

      -- Construct the axiom statement
      let ax_stmt : Semantic.Statement :=
        { ctx := frameToContext frAx vars
          fmla := exprToFormula eAx vars }

      -- Apply Mario's ax constructor
      sorry
      /-
      Strategy (substantive work remaining):

      1. Show ax_stmt ∈ dbToAxioms Γ vars (use h_ax)
      2. Show DJ preservation: (frameToContext frAx vars).dj.subst σ_mario (frameToContext fr vars).dj
         Use: Bridge.dvOK_implies_DJ_subst
      3. For each h ∈ frAx.mand:
         - h_needed gives ProofValid for hypothesis
         - Use IH (induction hypothesis) to get Mario's Provable
         - Show it matches after substitution using Bridge.applySubst_eq_mario_subst
      4. Apply Metamath.Provable.ax with all these pieces
      5. Show the result equals our goal using substitution lemma

      This is the core work - connecting our operational axiom application
      to Mario's declarative axiom instantiation!
      -/

/-! ## Backward Direction: Mario.Provable → ProofValid

This direction is trickier because Mario's system doesn't track the proof stack.
We need to show that IF something is provable in Mario's system,
THEN we can construct SOME operational proof (may not be the same steps).

This is the **completeness** direction - showing our verifier is complete with
respect to Mario's semantic specification.

**Status**: DEFERRED (less critical than soundness)

**Why deferred**:
1. Soundness (forward direction) is more important - ensures our verifier doesn't accept invalid proofs
2. Completeness is nice-to-have - ensures our verifier isn't artificially restrictive
3. More complex - requires reconstructing operational proof steps from declarative proof
4. Can be completed after forward direction is fully proven

**Strategy for future work**:
- Induction on Mario's Provable derivation
- For each Mario constructor (hyp, var, ax), construct corresponding ProofValid steps
- hyp case: Find the hypothesis in our frame, use useEssential or useFloating
- var case: Construct floating hypothesis for the variable
- ax case: Most complex - need to:
  * Find the axiom in our database (inverse of dbToAxioms)
  * Convert Mario's functional substitution to our Subst
  * Recursively construct proofs for needed hypotheses (IH)
  * Apply useAxiom with constructed substitution
-/

/-- Backward direction: If something is provable in Mario's semantic system,
    then we can construct an operational proof.

    This is **completeness** - Mario's spec is not stronger than our verifier.

    **DEFERRED**: This is less critical than soundness. The forward direction
    (soundness) ensures our verifier doesn't accept invalid proofs, which is
    the primary safety property. Completeness ensures we're not artificially
    restrictive, which can be proven later.

    Estimated effort: 4-6 hours (complex due to proof reconstruction) -/
theorem mario_to_proofValid {Γ : Database} {fr : Frame} {e : Expr}
    (h_mario : Semantic.Provable (dbToAxioms Γ (Frame.toVarList fr)) (frameToContext fr (Frame.toVarList fr))
                                   (exprToFormula e (Frame.toVarList fr))) :
    Provable Γ fr e := by
  sorry  -- DEFERRED: Completeness less critical than soundness

/-! ## Main Equivalence Theorem

Combines both directions to show operational ↔ semantic equivalence.
-/

/-- **MAIN THEOREM**: Operational and semantic provability are equivalent.

    This connects our verifier's operational semantics to Mario's mathematical foundations.

    - **Forward** (soundness): Verifier accepts → mathematically valid
    - **Backward** (completeness): Mathematically valid → verifier can accept

    We use Frame.toVarList to construct the variable list, ensuring well-formedness
    by construction (proven by Frame.toVarList_complete).

    Once proven, this enables:
    1. Using Mario's proven lemmas in our proofs
    2. Reasoning about our verifier using textbook mathematics
    3. Confidence that our operational model matches the spec
-/
theorem operational_iff_semantic {Γ : Database} {fr : Frame} {e : Expr} :
    Provable Γ fr e ↔
    Semantic.Provable (dbToAxioms Γ (Frame.toVarList fr)) (frameToContext fr (Frame.toVarList fr))
                       (exprToFormula e (Frame.toVarList fr)) := by
  constructor
  · -- Forward: Operational → Semantic
    intro ⟨steps, finalStack, h_valid, h_stack⟩
    rw [h_stack] at h_valid
    exact proofValid_to_mario h_valid
  · -- Backward: Semantic → Operational
    exact mario_to_proofValid

/-! ## Design Notes

**Why this is hard**:
1. **Type mismatch**: Mario uses indexed variables (VR), we use strings
2. **Stack vs declarative**: We track proof stack, Mario doesn't
3. **DJ vs dv list**: Different representations of disjoint variables
4. **Substitution**: Need to prove our applySubst matches Mario's Expr.subst

**Strategy**:
1. Use Bridge.lean conversions for type translation
2. Prove conversion lemmas (roundtrip theorems from Bridge)
3. Show each ProofValid constructor corresponds to Mario.Provable
4. For backward direction, reconstruct proof steps from Mario's derivation

**Current status**:
- Structure in place
- 4 sorries in forward direction (one per constructor case)
- 3 sorries in backward direction (one per constructor case)
- Need to prove conversion preserves semantics

**Next steps** (Phase 4 continuation):
1. Prove forward direction first (needed for soundness)
2. Fill in constructor cases using Bridge lemmas
3. Prove backward direction for completeness
-/

end Metamath.Spec.Equivalence
