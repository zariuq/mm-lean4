/-
Operational semantics for Metamath proof verification.

This file defines HOW a verifier checks proofs - the stack machine execution model.
It provides the operational foundation that bridges to the implementation (Verify.lean).

Per Metamath Specification (Chapter 4):
- §4.2.6: Assertions and proof structure
- §4.2.7: Frames (mandatory hypotheses + DV constraints)
- §4.3: Proof verification algorithm

This is the "small-step" operational semantics, as opposed to the "big-step"
semantic Provable in Mario's DeclarativeSpec.lean (which we'll bridge to).
-/

import Metamath.Spec.Core

namespace Metamath.Spec

/-! ## Proof Steps (Operational)

Per §4.3: A proof is a sequence of label references and hypothesis applications
that build up a stack of expressions.
-/

inductive ProofStep where
  | useHyp : Hyp → ProofStep
  | useAssertion : Label → Subst → ProofStep

/-! ## Stack Machine Semantics

The verifier maintains a stack of expressions and processes proof steps one by one.
This operational view directly corresponds to how Verify.lean executes.

**Design choice**: We use an inductive relation rather than a function because:
1. Easier to prove properties about (coinductive reasoning)
2. Closer to the spec's description as a sequence of valid steps
3. Separates specification from implementation
-/

/-- Operational proof execution: building up the proof stack.

    Per §4.3 of the Metamath spec:
    - Start with empty stack
    - Apply hypotheses → push to stack
    - Apply assertions → pop needed expressions, push conclusion
    - Valid proof ends with singleton stack containing the theorem
-/
inductive ProofValid (Γ : Database) : Frame → List Expr → List ProofStep → Prop where
  | nil : ∀ fr, ProofValid Γ fr [] []

  | useEssential : ∀ fr stack steps e,
      Hyp.essential e ∈ fr.hyps →
      ProofValid Γ fr stack steps →
      ProofValid Γ fr (e :: stack) (ProofStep.useHyp (Hyp.essential e) :: steps)

  | useFloating : ∀ fr stack steps c v,
      Hyp.floating c v ∈ fr.hyps →
      ProofValid Γ fr stack steps →
      ProofValid Γ fr (⟨c, [v.v]⟩ :: stack) (ProofStep.useHyp (Hyp.floating c v) :: steps)

  | useAxiom : ∀ fr stack steps l fr' e σ,
      Γ l = some (fr', e) →
      dvOK fr.vars fr'.dv fr.dv σ →  -- Per §4.2.4: callee DV in caller context
      -- Type preservation: substitution respects floating hypothesis typecodes
      (∀ c v, Hyp.floating c v ∈ fr'.hyps → (σ v).typecode = c) →
      ProofValid Γ fr stack steps →
      -- Pop fr'.hyps hypotheses (in reverse order per §4.3)
      ∀ needed : List Expr,
      needed = fr'.hyps.map (fun h => match h with
        | Hyp.essential e => applySubst fr'.vars σ e
        | Hyp.floating _ v => σ v) →
      ∀ remaining : List Expr,
      stack = needed.reverse ++ remaining →
      ProofValid Γ fr (applySubst fr'.vars σ e :: remaining) (ProofStep.useAssertion l σ :: steps)

/-! ## Provability (Operational Definition)

Per §4.2.6 and the formal verification algorithm in §4.1.4, an assertion is
provable if there exists a valid proof sequence that produces a singleton
stack containing the assertion.
-/

/-- An assertion is provable if there exists a valid proof.

    Per §4.2.6: "A proof demonstrates that a certain combination of math symbols
    follows from previous assertions."
-/
def Provable (Γ : Database) (fr : Frame) (e : Expr) : Prop :=
  ∃ (steps : List ProofStep) (finalStack : List Expr),
    ProofValid Γ fr finalStack steps ∧
    finalStack = [e]

/-! ## Proof Execution from an Initial Stack

`ProofValid` builds a stack from empty. For composition, we also use a
stack-relative variant that starts from an arbitrary initial stack. -/

inductive ProofValidFrom (Γ : Database) : Frame → List Expr → List Expr → List ProofStep → Prop where
  | nil : ∀ fr stk, ProofValidFrom Γ fr stk stk []

  | useEssential : ∀ fr stk stack steps e,
      Hyp.essential e ∈ fr.hyps →
      ProofValidFrom Γ fr stk stack steps →
      ProofValidFrom Γ fr stk (e :: stack) (ProofStep.useHyp (Hyp.essential e) :: steps)

  | useFloating : ∀ fr stk stack steps c v,
      Hyp.floating c v ∈ fr.hyps →
      ProofValidFrom Γ fr stk stack steps →
      ProofValidFrom Γ fr stk (⟨c, [v.v]⟩ :: stack) (ProofStep.useHyp (Hyp.floating c v) :: steps)

  | useAxiom : ∀ fr stk stack steps l fr' e σ,
      Γ l = some (fr', e) →
      dvOK fr.vars fr'.dv fr.dv σ →
      -- Type preservation: substitution respects floating hypothesis typecodes
      (∀ c v, Hyp.floating c v ∈ fr'.hyps → (σ v).typecode = c) →
      ProofValidFrom Γ fr stk stack steps →
      ∀ needed : List Expr,
      needed = fr'.hyps.map (fun h => match h with
        | Hyp.essential e => applySubst fr'.vars σ e
        | Hyp.floating _ v => σ v) →
      ∀ remaining : List Expr,
      stack = needed.reverse ++ remaining →
      ProofValidFrom Γ fr stk (applySubst fr'.vars σ e :: remaining)
        (ProofStep.useAssertion l σ :: steps)

theorem ProofValid.toFrom {Γ : Database} {fr : Frame} {stk : List Expr} {steps : List ProofStep} :
  ProofValid Γ fr stk steps → ProofValidFrom Γ fr [] stk steps := by
  intro h
  induction h with
  | nil =>
      exact ProofValidFrom.nil fr []
  | useEssential stack steps e h_in _ ih =>
      exact ProofValidFrom.useEssential fr [] stack steps e h_in ih
  | useFloating stack steps c v h_in _ ih =>
      exact ProofValidFrom.useFloating fr [] stack steps c v h_in ih
  | useAxiom stack steps l fr' e σ h_find h_dv h_typed _ needed h_needed remaining h_stack ih =>
      exact ProofValidFrom.useAxiom fr [] stack steps l fr' e σ h_find h_dv h_typed ih needed h_needed remaining h_stack

theorem ProofValidFrom.toProofValid
    {Γ : Database} {fr : Frame} {stk : List Expr} {steps : List ProofStep} :
  ProofValidFrom Γ fr [] stk steps → ProofValid Γ fr stk steps := by
  intro h
  induction h with
  | nil =>
      simpa using (ProofValid.nil fr)
  | useEssential stack steps e h_in _ ih =>
      exact ProofValid.useEssential fr stack steps e h_in ih
  | useFloating stack steps c v h_in _ ih =>
      exact ProofValid.useFloating fr stack steps c v h_in ih
  | useAxiom stack steps l fr' e σ h_find h_dv h_typed _ needed h_needed remaining h_stack ih =>
      exact ProofValid.useAxiom fr stack steps l fr' e σ h_find h_dv h_typed ih needed h_needed remaining h_stack

theorem ProofValidFrom.append_suffix
    {Γ : Database} {fr : Frame} {stk₁ stk₂ : List Expr} {steps : List ProofStep}
    (h : ProofValidFrom Γ fr stk₁ stk₂ steps) (suffix : List Expr) :
  ProofValidFrom Γ fr (stk₁ ++ suffix) (stk₂ ++ suffix) steps := by
  induction h with
  | nil =>
      simpa using (ProofValidFrom.nil fr (stk₁ ++ suffix))
  | useEssential stack steps e h_in _ ih =>
      simpa using (ProofValidFrom.useEssential fr (stk₁ ++ suffix) (stack ++ suffix) steps e h_in ih)
  | useFloating stack steps c v h_in _ ih =>
      simpa using (ProofValidFrom.useFloating fr (stk₁ ++ suffix) (stack ++ suffix) steps c v h_in ih)
  | useAxiom stack steps l fr' e σ h_find h_dv h_typed _ needed h_needed remaining h_stack ih =>
      -- Adjust the remaining suffix
      have h_stack' : stack ++ suffix = needed.reverse ++ (remaining ++ suffix) := by
        simpa [List.append_assoc] using congrArg (fun s => s ++ suffix) h_stack
      exact ProofValidFrom.useAxiom fr (stk₁ ++ suffix) (stack ++ suffix) steps l fr' e σ
        h_find h_dv h_typed ih needed h_needed (remaining ++ suffix) h_stack'

theorem ProofValidFrom.trans
    {Γ : Database} {fr : Frame} {stk₁ stk₂ stk₃ : List Expr}
    {steps₁ steps₂ : List ProofStep} :
    ProofValidFrom Γ fr stk₁ stk₂ steps₁ →
    ProofValidFrom Γ fr stk₂ stk₃ steps₂ →
  ProofValidFrom Γ fr stk₁ stk₃ (steps₂ ++ steps₁) := by
  intro h₁ h₂
  induction h₂ with
  | nil =>
      simpa using h₁
  | useEssential stack steps e h_in _ ih =>
      simpa using (ProofValidFrom.useEssential fr stk₁ stack (steps ++ steps₁) e h_in ih)
  | useFloating stack steps c v h_in _ ih =>
      simpa using (ProofValidFrom.useFloating fr stk₁ stack (steps ++ steps₁) c v h_in ih)
  | useAxiom stack steps l fr' e σ h_find h_dv h_typed _ needed h_needed remaining h_stack ih =>
      simpa [List.append_assoc] using
        (ProofValidFrom.useAxiom fr stk₁ stack (steps ++ steps₁) l fr' e σ
          h_find h_dv h_typed ih needed h_needed remaining h_stack)

/-! ## Key Theorems (Connecting Operational to Provable)

These bridge the inductive proof construction to the existential definition.
-/

/-- **PROVEN**: If we have a ProofValid that produces [e], we get Provable -/
theorem ProofValid.toProvable {Γ : Database} {fr : Frame} {e : Expr} {steps : List ProofStep} :
  ProofValid Γ fr [e] steps → Provable Γ fr e := by
  intro h_valid
  exact ⟨steps, [e], h_valid, rfl⟩

/-! ## Soundness Statement

The main theorem to prove: if our verifier accepts a proof, then the
assertion is semantically provable.

This connects the operational execution (Verify.lean) to the semantic
specification (Provable).
-/

theorem soundness_statement :
  ∀ (db : Database) (_l : Label) (fr : Frame) (e : Expr),
  (∃ steps, ProofValid db fr [e] steps) →
  Provable db fr e := by
  intro db _ fr e h
  rcases h with ⟨steps, h_valid⟩
  exact ProofValid.toProvable h_valid

/-! ## Design Notes

**Why ProofValid over a function?**

We could define proof checking as:
```lean
def checkProof : Database → Frame → List ProofStep → Option Expr
```

But the inductive Prop approach has advantages:
1. **Proof-oriented**: Properties easier to state and prove
2. **Spec clarity**: Describes "what is valid" not "how to compute"
3. **Implementation independence**: Verify.lean can use different data structures
4. **Composability**: Can compose proofs via inductive constructors

**Relationship to Metamath Specification**:
- §4.3 describes proof as "sequence of labels" - we model as ProofStep sequence
- §4.2.6 describes substitution constraints - we model in useAxiom constructor
- §4.2.7 describes frames - our Frame type directly corresponds

**Next layer up**: Mario's DeclarativeSpec.Provable provides the semantic "big-step" view.
We will prove ProofValid ↔ Mario.Provable in Equivalence.lean.
-/

/-! ## Database Monotonicity

If the axiom database grows (more entries), then any proof valid under the smaller
database is also valid under the larger one. This is because ProofValid only uses
Γ in the `useAxiom` constructor (to look up axiom frames/formulas), and the lookup
still succeeds in a larger database. -/

theorem ProofValid.mono_db
    {Γ₁ Γ₂ : Database} {fr : Frame} {stk : List Expr} {steps : List ProofStep}
    (h_sub : ∀ l x, Γ₁ l = some x → Γ₂ l = some x)
    (h_valid : ProofValid Γ₁ fr stk steps) :
    ProofValid Γ₂ fr stk steps := by
  induction h_valid with
  | nil => exact .nil _
  | useEssential _ _ _ h_mem _ ih => exact .useEssential _ _ _ _ h_mem ih
  | useFloating _ _ _ _ h_mem _ ih => exact .useFloating _ _ _ _ _ h_mem ih
  | useAxiom _ _ _ _ _ _ h_lookup h_dv h_type _ needed h_needed remaining h_remaining ih =>
      exact .useAxiom _ _ _ _ _ _ _ (h_sub _ _ h_lookup) h_dv h_type ih _ h_needed _ h_remaining

theorem Provable.mono_db
    {Γ₁ Γ₂ : Database} {fr : Frame} {e : Expr}
    (h_sub : ∀ l x, Γ₁ l = some x → Γ₂ l = some x)
    (h_prov : Provable Γ₁ fr e) :
    Provable Γ₂ fr e := by
  obtain ⟨steps, finalStack, h_valid, h_eq⟩ := h_prov
  exact ⟨steps, finalStack, h_valid.mono_db h_sub, h_eq⟩

end Metamath.Spec
