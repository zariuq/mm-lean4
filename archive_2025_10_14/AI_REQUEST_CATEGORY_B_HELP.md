# AI Expert Request: Category B Lemmas - Lean 4 Formal Verification

**Date:** 2025-10-14
**Project:** Formal verification of Metamath proof verifier in Lean 4
**Context:** Phase 3 - Connecting implementation to specification
**Status:** 4 sorries eliminated today, need help with 3 remaining Category B lemmas

---

## Project Overview

We're formally verifying a Metamath proof verifier implementation in Lean 4 by proving it sound with respect to a mathematical specification. The project has two main components:

1. **Spec.lean:** Mathematical specification of Metamath proof system (pure functional)
2. **Verify.lean:** Efficient implementation using Arrays, HashMaps (imperative style)
3. **Kernel.lean:** Bridge layer proving implementation matches specification

**Current Progress:**
- Phase 3: ~85% complete
- Main theorems: ✅ Complete (verify_impl_sound, fold_maintains_inv_and_provable)
- Today: Eliminated 4 sorries (3 in checkHyp integration, 1 in match/domain lemmas)
- Remaining: 19 sorries total, 3 in Category B need help

---

## What We Need Help With

**Category B: Match/Domain Lemmas** - Three interconnected lemmas involving list operations, substitutions, and structural reasoning. These are blocking progress and require either:
1. Additional infrastructure lemmas (flatMap, filterMap, list distinctness)
2. Design decisions (assumptions vs proofs)
3. Advanced Lean 4 proof techniques

---

## Problem 1: Line 460 - vars_apply_subset (flatMap/filterMap extraction)

### Context

**File:** Metamath/Kernel.lean, lines 430-495
**Theorem:** `vars_apply_subset`
**Goal:** Variables in σ(e) are subset of original vars union vars introduced by σ

### The Code

```lean
/-- Variables in σ(e) are subset of original vars union vars introduced by σ -/
theorem vars_apply_subset (vars : List Metamath.Spec.Variable) (σ : Metamath.Spec.Subst) (e : Metamath.Spec.Expr) :
  ∀ v ∈ Metamath.Spec.varsInExpr vars (Metamath.Spec.applySubst vars σ e),
    v ∈ Metamath.Spec.varsInExpr vars e ∨
    ∃ w ∈ Metamath.Spec.varsInExpr vars e, v ∈ Metamath.Spec.varsInExpr vars (σ w) := by
  intro v hv
  unfold Metamath.Spec.applySubst Metamath.Spec.varsInExpr at *
  simp [List.filterMap] at hv
  obtain ⟨s, hs_mem, hv_eq⟩ := hv
  by_cases h_var : Variable.mk s ∈ vars
  · -- s is a variable, so it was replaced by σ ⟨s⟩
    right
    exists Variable.mk s
    constructor
    · simp [List.filterMap]
      exists s
      constructor
      · exact hs_mem
      · simp [h_var]
    · -- Need to show: v ∈ varsInExpr vars (σ ⟨Variable.mk s⟩)
      -- We have:
      -- - hs_mem : s ∈ (applySubst vars σ e).syms
      -- - After unfolding applySubst: s ∈ e.syms.flatMap (...)
      -- - Since h_var holds, flatMap expands to (σ ⟨Variable.mk s⟩).syms
      simp [List.filterMap]
      exists s
      constructor
      · -- SORRY HERE: Show s ∈ (σ ⟨Variable.mk s⟩).syms
        unfold Metamath.Spec.applySubst at hs_mem
        simp only [List.mem_flatMap] at hs_mem
        obtain ⟨s', hs'_mem, hs_in⟩ := hs_mem
        by_cases h_s'_var : Variable.mk s' ∈ vars
        · simp [h_s'_var] at hs_in
          -- Now: s ∈ (σ ⟨Variable.mk s'⟩).syms
          -- Need: s ∈ (σ ⟨Variable.mk s⟩).syms
          -- Must show s' = s somehow
          sorry -- LINE 474
        · simp [h_s'_var] at hs_in
          simp at hs_in
          subst hs_in
          contradiction
      · simp [h_var]
        exact hv_eq
  · -- s is a constant, kept as [s]
    left
    -- This case works fine
```

### Key Definitions

```lean
-- From Spec.lean
def applySubst (vars : List Variable) (σ : Subst) (e : Expr) : Expr :=
  { typecode := e.typecode
    syms := e.syms.flatMap fun s =>
      let v := Variable.mk s
      if v ∈ vars then (σ v).syms else [s] }

def varsInExpr (vars : List Variable) (e : Expr) : List Variable :=
  e.syms.filterMap fun s =>
    let v := Variable.mk s
    if v ∈ vars then some v else none
```

### The Challenge

After extracting from `flatMap` at line 464, we get `s'` but need to show it equals `s`. The structure is:
1. `hs_mem : s ∈ (applySubst vars σ e).syms`
2. After flatMap extraction: `s ∈ (if Variable.mk s' ∈ vars then (σ ⟨s'⟩).syms else [s'])`
3. With `h_var : Variable.mk s ∈ vars`, we took the "then" branch
4. So `s ∈ (σ ⟨Variable.mk s'⟩).syms`
5. But we need `s ∈ (σ ⟨Variable.mk s⟩).syms`
6. **How do we show s' = s?**

### What We've Tried

- Direct reasoning from flatMap structure (gets stuck)
- Trying to use filterMap properties (doesn't connect cleanly)
- Looking for library lemmas about flatMap membership (none found)

### Questions for AI Experts

1. **Is there a standard Lean 4 lemma** for extracting from `flatMap` that we're missing?
2. **Should we prove a helper lemma** like `flatMap_mem_iff` first?
3. **Is there a way to "invert" the filterMap/flatMap relationship** to deduce s' = s?
4. **Alternative proof strategy?** Maybe induction on `e.syms` instead?
5. **Type-driven approach?** The fact that `Variable.mk s` succeeds tells us something about `s`

### Suggested Helper Lemma

```lean
-- Might this help?
theorem flatMap_mem_of_cond {α β : Type _} (xs : List α) (f : α → List β) (b : β) :
    b ∈ xs.flatMap f → ∃ a ∈ xs, b ∈ f a
```

**Desired:** A way to connect the symbol `s` back to its source symbol through the flatMap structure when filtering succeeds.

---

## Problem 2: Line 1137 - matchHyps Composition (disjoint variable domains)

### Context

**File:** Metamath/Kernel.lean, lines 1095-1145
**Theorem:** `matchHyps_sound`
**Goal:** If matching hypotheses succeeds, applying resulting substitution reconstructs stack

### The Code

```lean
theorem matchHyps_sound (vars : List Metamath.Spec.Variable) (hyps stack : List Metamath.Spec.Hyp) (σ : Metamath.Spec.Subst) :
  matchHyps hyps stack = some σ →
  hyps.map (Metamath.Spec.applySubst vars σ) = stack := by
  intro h_match
  induction hyps generalizing stack σ with
  | nil => -- Works fine
  | cons h hs ih =>
      cases stack with
      | nil => contradiction
      | cons e es =>
          unfold matchHyps at h_match
          cases h with
          | essential e_hyp =>
              -- σ = fun v => applySubst vars σ₂ (σ₁ v)
              -- where σ₁ from matching head, σ₂ from matching tail
              split at h_match
              · contradiction
              · next σ₁ h_match_expr =>
                  split at h_match
                  · contradiction
                  · next σ₂ h_match_hyps =>
                      simp at h_match
                      rw [← h_match]
                      constructor
                      · -- Head: applySubst vars (fun v => applySubst vars σ₂ (σ₁ v)) e_hyp = e
                        have h₁ := matchExpr_sound vars e_hyp e σ₁ h_match_expr
                        rw [← h₁]
                        rw [← subst_composition vars σ₁ σ₂ e_hyp]
                        -- Now need: applySubst vars σ₂ (applySubst vars σ₁ e_hyp) = applySubst vars σ₁ e_hyp
                        -- This requires that σ₂ doesn't affect variables in (applySubst vars σ₁ e_hyp)
                        sorry -- LINE 1137
                      · exact ih es σ₂ h_match_hyps
          | floating c v =>
              -- Floating case works fine
```

### Helper Lemma Used

```lean
-- Already proven in codebase
theorem subst_composition (vars : List Variable) (σ₁ σ₂ : Subst) (e : Expr) :
    applySubst vars (fun v => applySubst vars σ₂ (σ₁ v)) e =
    applySubst vars σ₂ (applySubst vars σ₁ e)
```

### The Challenge

After composition, we need:
```lean
applySubst vars σ₂ (applySubst vars σ₁ e_hyp) = applySubst vars σ₁ e_hyp
```

This is true if **σ₂ doesn't affect variables in `(applySubst vars σ₁ e_hyp)`**.

The comment says: "This needs additional assumptions about disjoint variable domains."

### Design Questions

1. **Should we add an assumption** that hypotheses have disjoint variable sets?
2. **Is there a weaker assumption** that's sufficient and provable from matchHyps structure?
3. **Alternative proof approach** that avoids this issue?
4. **Can we extract disjointness** from the fact that matchHyps succeeded?

### Context from Metamath Specification

In Metamath:
- Each hypothesis introduces variables
- Distinct Variable ($d) constraints ensure disjointness
- The `matchHyps` function processes hypotheses sequentially

### Questions for AI Experts

1. **What's the minimal assumption** needed here? Full disjointness, or something weaker?
2. **Can we refactor matchHyps** to track disjointness explicitly?
3. **Is there a standard pattern** in formalized mathematics for this kind of composition?
4. **Should we axiomatize this property** or prove it from matchHyps definition?
5. **How would Coq/Isabelle handle** similar composition reasoning?

### Possible Approaches

**Approach A:** Axiomatize as trusted property
```lean
axiom matchHyps_disjoint_domains :
  ∀ vars hyps stack σ₁ σ₂,
    matchHyps (h :: hs) (e :: es) = some (fun v => applySubst vars σ₂ (σ₁ v)) →
    ∀ v ∈ varsInExpr vars (applySubst vars σ₁ h), σ₂ v = ⟨typecode, [v.v]⟩
```

**Approach B:** Strengthen matchHyps to return disjointness witness
```lean
structure MatchResult where
  σ : Subst
  disjoint : ∀ v ∈ domain σ, ... -- some disjointness property
```

**Approach C:** Prove from matchHyps structure (but how?)

---

## Problem 3: Line 1229 - matchFloats Agreement (list distinctness)

### Context

**File:** Metamath/Kernel.lean, lines 1188-1230
**Theorem:** `matchFloats_sound`
**Goal:** If matching floats succeeds, σ binds each variable correctly

### The Code

```lean
theorem matchFloats_sound (floats : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (stack : List Metamath.Spec.Expr) (σ : Metamath.Spec.Subst) :
  matchFloats floats stack = some σ →
  floats.map (fun (tc, v) => σ v) = stack := by
  intro h_match
  induction floats generalizing stack σ with
  | nil => -- Works fine
  | cons ⟨tc, v⟩ fs ih =>
      cases stack with
      | nil => contradiction
      | cons e es =>
          unfold matchFloats at h_match
          split at h_match
          · contradiction
          · next h_tc_eq =>
              split at h_match
              · contradiction
              · next σ_rest h_match_rest =>
                  -- σ = fun w => if w = v then e else σ_rest w
                  simp at h_match
                  rw [← h_match]
                  simp [List.map]
                  constructor
                  · simp; exact h_tc_eq.symm
                  · -- Apply IH to tail
                    have ih_applied := ih es σ_rest h_match_rest
                    -- Need: fs.map (fun (tc, v') => σ v') = fs.map (fun (tc, v') => σ_rest v')
                    -- σ v' = (if v' = v then e else σ_rest v')
                    -- For v' in fs, need σ v' = σ_rest v'
                    -- This requires v' ≠ v (no duplicates in variable list)
                    congr 1
                    funext ⟨tc', v'⟩
                    simp
                    -- Need: v' ≠ v so the else branch is taken
                    sorry -- LINE 1229
```

### Helper Definition

```lean
-- From Spec.lean
def matchFloats : List (Constant × Variable) → List Expr → Option Subst
  | [], [] => some (fun v => ⟨defaultTypecode, [v.v]⟩)
  | [], _ :: _ => none
  | _ :: _, [] => none
  | (tc, v) :: fs, e :: es =>
      if e.typecode ≠ tc then none
      else do
        let σ_rest ← matchFloats fs es
        pure (fun w => if w = v then e else σ_rest w)
```

### The Challenge

We construct σ by extending σ_rest:
```lean
σ = fun w => if w = v then e else σ_rest w
```

For the inductive hypothesis to apply, we need:
```lean
∀ v' ∈ (variables in fs), σ v' = σ_rest v'
```

This requires `v' ≠ v` for all `v'` in the tail `fs`.

**This is equivalent to saying the variable list has no duplicates.**

### Questions for AI Experts

1. **Should we add a precondition** that `floats` has distinct variables?
2. **Can we prove distinctness** from matchFloats structure? (Seems unlikely)
3. **Is there a list distinctness lemma** we should prove first as infrastructure?
4. **Standard pattern** in Lean 4 for handling such list uniqueness constraints?
5. **Should we use `List.Nodup`** or similar from the standard library?

### Possible Solutions

**Solution A:** Add precondition
```lean
theorem matchFloats_sound (floats : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (stack : List Metamath.Spec.Expr) (σ : Metamath.Spec.Subst) :
  List.Nodup (floats.map Prod.snd) →  -- Add this assumption
  matchFloats floats stack = some σ →
  floats.map (fun (tc, v) => σ v) = stack
```

**Solution B:** Prove helper lemma first
```lean
-- Variables in tail are not equal to head
theorem tail_vars_ne_head {α : Type _} (head : α) (tail : List α) :
    List.Nodup (head :: tail) →
    ∀ x ∈ tail, x ≠ head
```

**Solution C:** Refactor to track distinctness in type
```lean
structure DistinctFloats where
  floats : List (Constant × Variable)
  distinct : List.Nodup (floats.map Prod.snd)
```

### Related Infrastructure Needed

```lean
-- Do these exist in Lean 4 Batteries/Std?
1. List.Nodup.tail : List.Nodup (h :: t) → List.Nodup t
2. List.mem_of_nodup_cons : List.Nodup (h :: t) → x ∈ t → x ≠ h
3. Function extensionality on if-then-else with membership
```

---

## What We've Accomplished Today (Context)

To help you understand our proof style and what infrastructure exists:

### Session 6 Successes (4 sorries eliminated)

**1. allM Extraction Infrastructure (Lines 1400-1479)**
```lean
-- Generic lemma (7 lines, heavy simp automation)
theorem List.allM_eq_some_true_iff_forall {α : Type _} (xs : List α) (p : α → Option Bool) :
    xs.allM p = some true ↔ ∀ x ∈ xs, p x = some true := by
  induction xs with
  | nil => simp [List.allM]
  | cons x xs ih => simp [List.allM, ih, Option.bind_eq_some_iff, Bool.and_eq_true]

-- Specialized lemma (3 lines)
theorem checkFloat_true_iff (σ_impl : ...) (c : ...) (v : ...) :
    checkFloat σ_impl (c, v) = some true ↔
    ∃ f e, σ_impl[v.v]? = some f ∧ toExprOpt f = some e ∧ e.typecode = c := by
  unfold checkFloat
  simp [Option.bind_eq_some_iff, beq_iff_eq]
```

**2. TypedSubst Witness Complete (Line 1449, 25 lines)**
- Used allM extraction lemmas
- Heavy Lean automation with `simp`
- Clean structure

**3. checkHyp_produces_TypedSubst (Line 2262, 19 lines)**
- Used **reverse direction** (.mpr) of allM lemma
- One-line conclusion: `simp only [toSubstTyped, Bridge.floats, h_allM]`

**4. matchExpr_sound symbols (Line 1031, 1 line!)**
```lean
-- Just needed to apply existing lemma
exact h_syms
```

### Our Proof Style

1. **Heavy automation:** Trust `simp` when goal is "obviously true after unfolding"
2. **Library lemmas first:** Always search for existing lemmas before manual proof
3. **Clean abstractions:** Break complex proofs into reusable helper lemmas
4. **Minimal manual work:** Let Lean handle routine structural reasoning

---

## Technical Environment

**Lean Version:** 4.20.0-rc2
**Dependencies:** Batteries (Lean 4 standard library extensions)
**Build System:** Lake
**Project Size:** ~4500 lines Kernel.lean, ~500 lines Spec.lean

**Available Infrastructure:**
- Bridge lemmas (floats_complete, floats_sound, essentials_complete, essentials_sound) ✅
- allM extraction lemmas ✅
- List.mem_filterMap, List.mem_flatMap (from Batteries)
- Option.bind_eq_some_iff
- Standard list lemmas

**Missing Infrastructure (that we've identified):**
- List distinctness/Nodup handling
- Advanced flatMap membership lemmas
- Disjoint domain reasoning for substitutions

---

## Questions for AI Experts

### High-Level Strategy Questions

1. **Design philosophy:** When should we add preconditions vs proving properties?
2. **Infrastructure timing:** Should we pause and build more helper lemmas first?
3. **Proof patterns:** Are there standard patterns for this kind of structural reasoning?
4. **Trade-offs:** Axiomatize some properties vs full proofs - what's reasonable?

### Specific Technical Questions

**For Problem 1 (flatMap extraction):**
- Best way to invert flatMap when filtering condition holds?
- Should we use dependent types to track the relationship?
- Alternative proof strategies that avoid the issue?

**For Problem 2 (composition/disjointness):**
- Standard way to handle disjoint variable domains in formal verification?
- Can we extract disjointness from matchHyps success?
- What would a minimal sufficient assumption look like?

**For Problem 3 (list distinctness):**
- Best Lean 4 idiom for "list has no duplicates"?
- Should we use List.Nodup or roll our own?
- How to integrate distinctness assumption cleanly?

### Lean 4 Specific Questions

1. **Are there relevant lemmas in Batteries** we should know about?
   - Advanced flatMap lemmas?
   - List distinctness utilities?
   - Function extensionality helpers?

2. **Best practices for assumptions:**
   - How to add preconditions without polluting all call sites?
   - Type-level encoding vs proof-level encoding?

3. **Proof automation tips:**
   - Tactics we should use more of?
   - `aesop`? `omega`? Custom decision procedures?

---

## How to Help

We would deeply appreciate help with any of:

1. **Complete solutions** for any of the three problems
2. **Proof sketches** showing the key steps
3. **Infrastructure lemmas** we should prove first
4. **Design recommendations** for handling assumptions
5. **Lean 4 idioms** we should know about
6. **Alternative approaches** we haven't considered
7. **References** to similar problems solved in other projects

**Format:** Lean 4 code snippets preferred, but high-level guidance also very helpful!

**Priority:** All three problems are equally important, but Problem 3 (list distinctness) seems most tractable.

---

## Additional Context Documents

If you want more context, we have comprehensive documentation:
- `PHASE3_SESSION6_FINAL_SUMMARY.md` - Today's progress (4 sorries eliminated)
- `PHASE3_COMPREHENSIVE_STATUS.md` - Overall project status (~85% complete)
- Full codebase available if needed for deeper analysis

---

## Thank You!

We're SO close to completing this formal verification! These three lemmas are the main blockers for Category B, and solving them would unlock significant progress. Any help is greatly appreciated! 🙏

**Expected impact of solving these:**
- Unlock 3 more sorries in Category B
- Possibly unblock similar patterns elsewhere
- Establish infrastructure for remaining work
- Bring project to ~87% complete

The formal verification sprint has been incredibly productive, and your expertise would help us reach the finish line! 🚀🐢✨
