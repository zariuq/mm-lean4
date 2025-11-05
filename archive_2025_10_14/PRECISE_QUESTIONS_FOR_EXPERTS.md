# Precise Questions for AI Experts - Lean 4 Implementation Blocks

**Date:** 2025-10-14
**Context:** Implementing Category B solutions from Grok and GPT-5/Oruži

---

## Problem 1: vars_apply_subset (Line 460) - BLOCKED

### Question 1.1: Tactic Sequence for flatMap Extraction

**Context:**
```lean
intro v hv
unfold Metamath.Spec.applySubst Metamath.Spec.varsInExpr at *
simp [List.filterMap] at hv
obtain ⟨s, hs_mem, hv_eq⟩ := hv
-- hs_mem : s ∈ (applySubst vars σ e).syms
-- but applySubst was unfolded at line 2 with "at *"
```

**Problem:** After `unfold ... at *`, then `simp [List.filterMap] at hv`, then `obtain`, the resulting `hs_mem` is not in a form that `rw [List.mem_flatMap]` or `simp only [List.mem_flatMap]` can work with.

**Specific Question:**
> In Lean 4.20, when you `unfold` a definition at `*` (all hypotheses), then use `simp [List.filterMap]` on one hypothesis and `obtain` to extract witnesses, what is the exact form of the extracted hypothesis? Specifically, if `applySubst vars σ e` unfolds to `{ syms := e.syms.flatMap f, typecode := ... }`, does `hs_mem : s ∈ (applySubst vars σ e).syms` after the above steps have the form that `List.mem_flatMap` can directly rewrite?

**What We Tried:**
1. `rw [List.mem_flatMap] at hs_mem` → "did not find instance of the pattern"
2. `simp only [List.mem_flatMap] at hs_mem` → "simp made no progress"
3. `unfold Metamath.Spec.applySubst at hs_mem` (after line 2) → "failed to unfold" (already unfolded)

**What We Need:**
Either:
- A) The correct tactic sequence to get `hs_mem` into the form `s ∈ e.syms.flatMap ...`
- B) A proof strategy that avoids this issue (e.g., using `have` statements to capture intermediate forms before `obtain`)

### Question 1.2: Alternative Witness Construction

**AI Expert Guidance:** "Choose `w := Variable.mk s'` where `s'` is the producing symbol from flatMap"

**Specific Question:**
> Given `hs_mem : s ∈ (applySubst vars σ e).syms` after unfolding and simplification, what is the most direct way in Lean 4.20 to extract the witness `s'` such that `s' ∈ e.syms` and `s ∈ (if Variable.mk s' ∈ vars then (σ ⟨Variable.mk s'⟩).syms else [s'])`?

Should we use:
- `have h_flatmap : ∃ s' ∈ e.syms, s ∈ ... := by ...` then `obtain`?
- Direct pattern matching?
- A helper lemma about filterMap + flatMap composition?

---

## Problem 3: matchFloats_sound (Line 1229) - 95% COMPLETE

### Question 3.1: Goal After congr 1 (RESOLVED - kept for reference)

**Context:**
```lean
simp [List.map]
congr 1
· -- Goal here: σ v = e or tail equality?
```

**Problem:** After `simp [List.map]` and `congr 1` on a list equality, what exactly is the first goal? We assumed it was the head equality `σ v = e`, but errors suggested it might be tail.

**Resolution:** The goal is actually the tail! `congr 1` on `a :: xs = b :: ys` generates two goals: head equality (`a = b`) and tail equality (`xs = ys`). Our first bullet point handles head.

### Question 3.2: Proving σ v = e (MINOR - nearly solved)

**Context:**
```lean
-- σ = fun w => if w = v then e else σ_rest w
-- Goal: σ v = e
```

**Specific Question:**
> For a function defined as `fun w => if w = v then e else f w`, what is the most direct tactic to prove `(fun w => if w = v then e else f w) v = e`?

**What We Tried:**
- `rfl` → failed (not definitionally equal before beta reduction?)
- `simp` → should work but got "simp made no progress" (might be indentation/context issue)

**What We Need:** Confirmation that `simp` is correct, or if we need `simp only [if_pos rfl]` or similar.

---

## Meta-Question: Proof Development Strategy

### Question M.1: Handling Complex Unfolding

**General Pattern We Encountered:**
1. Use `unfold defs at *` to unfold everywhere
2. Use `simp [lemmas] at hyp` to simplify one hypothesis
3. Use `obtain` to extract witnesses
4. Try to use extracted hypothesis → doesn't match expected pattern

**Specific Question:**
> What is the recommended Lean 4 pattern for proofs that need to:
> 1. Unfold recursive/complex definitions
> 2. Extract existential witnesses from list operations (flatMap, filterMap)
> 3. Use those witnesses in further reasoning
>
> Should we:
> - A) Use `have` statements to capture intermediate forms before `obtain`?
> - B) Avoid `unfold ... at *` and instead unfold selectively?
> - C) Use `conv` to control simplification more precisely?
> - D) Write helper lemmas for the specific patterns?

### Question M.2: When simp "Makes No Progress"

**Pattern We Saw:**
```lean
have h : P := ...
simp [relevant_lemma] at h
-- Error: "simp made no progress"
```

**Specific Question:**
> When `simp [lemma] at hyp` reports "made no progress", what are the most common reasons in Lean 4.20?
> 1. The hypothesis is already in simplified form?
> 2. The lemma doesn't match the hypothesis structure?
> 3. Missing simp lemmas in the simp set?
> 4. The hypothesis needs `simp only` with explicit lemmas?
>
> What's the diagnostic process to figure out why simp isn't working?

---

## Summary of Blockers

**Problem 1 (vars_apply_subset):**
- **Blocker:** Can't extract flatMap witness after unfold/simp/obtain sequence
- **Severity:** High (completely blocked)
- **Root Cause:** Tactic interaction complexity with unfold at *
- **Estimated Time to Resolve:** 1-2 hours with correct tactic sequence

**Problem 3 (matchFloats_sound):**
- **Blocker:** Minor tactic detail for σ v = e
- **Severity:** Low (90% complete, final polish)
- **Root Cause:** Unclear which tactic to use for if-then-else beta reduction
- **Estimated Time to Resolve:** 5-15 minutes

---

## Request for Experts

If you have experience with Lean 4 proof development, specifically:
1. **Extracting witnesses from flatMap/filterMap after complex unfolding**
2. **Best practices for unfold/simp/obtain patterns**
3. **Debugging "simp made no progress" errors**

We would greatly appreciate:
- Concrete tactic sequences for the patterns above
- Pointers to similar proofs in Lean 4 projects
- Helper lemmas we should prove for this pattern
- Alternative proof strategies that avoid these issues

**Thank you!** 🙏

These questions will help us complete the remaining 5-10% of the Category B implementations and establish patterns for future formal verification work.
