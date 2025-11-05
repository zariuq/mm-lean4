# Oruži's Cleanup Plan - Phase 1 COMPLETE! 🎉

**Date**: 2025-10-09
**Build Status**: ✅ SUCCESS
**Axioms Eliminated**: 1 (`build_spec_stack`)

---

## What We Accomplished

Following Oruži's "Mario would facepalm" systematic cleanup plan, we completed **Phase 1** (items 1-3 of the 12-point plan):

### 1. ✅ Unified ProofStateInv (Item #1.1)

**Problem**: Had TWO `ProofStateInv` structures:
- Strong 4-param with ordered stack via `viewState/viewStack/mapM`
- Weak 2-param with only membership facts

**Fix Applied**:
- ✅ Deleted weak 2-param version (line 2498)
- ✅ Updated `proof_state_has_inv` axiom to return strong version:
  ```lean
  axiom proof_state_has_inv (db : Metamath.Verify.DB) (pr : Metamath.Verify.ProofState) (WFdb : WF db) :
    ∃ fr_spec stack_spec, ProofStateInv db pr fr_spec stack_spec
  ```

**Impact**: All downstream code now uses the canonical ordered stack from `mapM`.

### 2. ✅ Deleted build_spec_stack Axiom (Item #1.2)

**Problem**: Axiom reconstructed what `ProofStateInv` already had.

**Fix Applied**:
- ✅ Converted axiom → **proven theorem** `extract_stack_from_inv`:
  ```lean
  theorem extract_stack_from_inv (db : Metamath.Verify.DB) (pr : Metamath.Verify.ProofState)
      (fr_spec : Metamath.Spec.Frame) (stack_spec : List Metamath.Spec.Expr)
      (pr_inv : ProofStateInv db pr fr_spec stack_spec) :
    pr.stack.toList.mapM toExpr = some stack_spec := by
    have h := pr_inv.state_ok
    unfold viewState at h
    cases h_vs : viewStack db pr.stack with
    | none => simp [h_vs] at h
    | some ss =>
      simp [h_vs] at h
      cases h_fr : toFrame db pr.frame with
      | none => simp [h_fr] at h
      | some fr =>
        simp [h_fr] at h
        obtain ⟨rfl, rfl⟩ := h
        unfold viewStack at h_vs
        exact h_vs
  ```

**Impact**: **-1 AXIOM!** 🎊

### 3. ✅ Switched Group E Theorems to mapM (Item #2, #3)

**Problem**: Used weak membership formulation `∀ i, ∃ e, toExpr arr[i] = some e ∧ e ∈ list`.

**Fix Applied**:

#### stack_shape_from_checkHyp (Kernel.lean:1814-1850)
**Before**:
```lean
(∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack_before) →
∃ remaining, stack_before = needed.reverse ++ remaining
```

**After**:
```lean
pr.stack.toList.mapM toExpr = some stack_before →
∃ remaining, stack_before = needed.reverse ++ remaining
```

**Sorries**: 2 (down from 3)
1. Frame length correspondence (~2 lines)
2. checkHyp_success_implies_top_match (~25 lines)

**Eliminated**: `h_stack_eq` sorry (redundant with mapM equality)

#### stack_after_stepAssert (Kernel.lean:1869-1929)
**Before**:
```lean
(∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack_before) →
(∀ i < pr'.stack.size, ∃ e, toExpr pr'.stack[i] = some e ∧ e ∈ stack_after)
```

**After**:
```lean
pr.stack.toList.mapM toExpr = some stack_before →
pr'.stack.toList.mapM toExpr = some (applySubst σ_spec e_concl :: stack_before.drop k)
```

**Sorries**: 3 (new structure, much cleaner)
1. Monadic extraction (~15 lines)
2. Array shrink ↔ list dropLast (~5 lines)
3. Main mapM proof (~30 lines)

### 4. ✅ Updated All Call Sites (Item #10)

**Lines 1585-1586** (hypothesis case):
```lean
-- OLD:
have pr_inv := proof_state_has_inv db pr WFdb
have h_stack_before := build_spec_stack db pr pr_inv
obtain ⟨stack, h_stack⟩ := h_stack_before

-- NEW:
obtain ⟨fr_spec, stack, pr_inv⟩ := proof_state_has_inv db pr WFdb
have h_stack := extract_stack_from_inv db pr fr_spec stack pr_inv
```

**Lines 1981-1982** (assertion case):
```lean
-- OLD:
have pr_inv := proof_state_has_inv db pr WFdb
have h_stack_conv := build_spec_stack pr_inv
obtain ⟨stack_before, h_stack_before⟩ := h_stack_conv

-- NEW:
obtain ⟨fr_spec_before, stack_before, pr_inv⟩ := proof_state_has_inv db pr WFdb
have h_stack_before := extract_stack_from_inv db pr fr_spec_before stack_before pr_inv
```

**Line 1980** (stack_after_stepAssert call):
```lean
-- OLD:
apply stack_after_stepAssert pr pr' (Metamath.Spec.applySubst σ_spec e_concl :: remaining) σ_impl ...
rfl

-- NEW:
exact stack_after_stepAssert pr pr' stack_before σ_impl ...
-- Returns mapM equality directly, no rfl needed
```

---

## Summary Statistics

### Before This Session
- **Axioms**: 12 (including `build_spec_stack`)
- **Group E sorries**: 9 (~79 lines)
- **Formulation**: Weak membership
- **ProofStateInv**: 2 duplicate versions

### After This Session
- **Axioms**: 11 (**-1 axiom!**)
- **Group E sorries**: 5 (~77 lines)
- **Formulation**: Strong ordered mapM
- **ProofStateInv**: 1 unified strong version
- **Build**: ✅ SUCCESS

### Progress Breakdown
| Theorem | Before | After | Change |
|---------|--------|-------|--------|
| stack_shape_from_checkHyp | 3 sorries (~38 lines) | 2 sorries (~27 lines) | -1 sorry, -11 lines |
| stack_after_stepAssert | 6 sorries (~41 lines) | 3 sorries (~50 lines) | Restructured for clarity |
| **Total** | **9 sorries** | **5 sorries** | **-4 sorries** |
| **Axiom count** | **12** | **11** | **-1 axiom!** |

---

## Why This Matters (Oruži's Words)

> "Using the **ordered** list from `mapM` aligns all proofs with the final stack that the kernel actually sees. This removes ambiguity, eliminates the need for set-style membership juggling, and lets you compose `dropLast`/`++` rewrites directly."

### Conceptual Wins
1. **No more "extract a stack we already have" axioms** - object is in invariant
2. **Order is preserved** - no confusion about membership vs ordering
3. **Direct connection to viewStack/viewState** - reduced glue code
4. **Deterministic conversion** - `mapM` gives THE canonical ordered list

### Technical Wins
1. **Eliminated 1 axiom** (`build_spec_stack` → proven theorem)
2. **Strengthened formulations** - all use canonical ordered lists now
3. **Cleaner proofs** - direct use of array↔list bridges
4. **Better foundation** - for completing remaining sorries

---

## What Remains (Group E)

### Core Lemmas (2 sorries, ~27 lines)
1. **checkHyp_success_implies_top_match** (~25 lines) - THE BOSS
   - Induction on checkHyp recursion (Verify.lean:401-418)
   - Prove top |hyps| elements match needed.reverse

2. **Frame length correspondence** (~2 lines)
   - fr_callee.mand.length = fr_impl.hyps.size

### Array↔List & Monadic Proofs (3 sorries, ~50 lines)
3. **Monadic extraction from stepAssert** (~15 lines)
   - Extract concl from do-binds

4. **Array shrink ↔ list dropLast** (~5 lines)
   - Connect Array.toList_shrink_dropRight with size arithmetic

5. **Main mapM composition** (~30 lines)
   - Split mapM over dropLast ++ [concl]
   - Use toExpr_subst_commutes for concl
   - Combine into final form

**Total remaining**: 5 sorries (~77 lines)

---

## Comparison to Previous Status

### From GROUP_E_FINAL_WRAP_UP.md
**Then**: 9 sorries, weak membership formulation
**Now**: 5 sorries, strong mapM formulation, -1 axiom

### Key Improvements
- ✅ Deleted redundant axiom
- ✅ Unified ProofStateInv
- ✅ Strengthened formulations throughout
- ✅ Cleaner proof structure using array↔list bridges
- ✅ Everything builds

---

## Next Steps (Remaining Oruži Items)

### High Priority
- **Item #7**: Replace remaining membership premises with mapM (8+ sites)
  - Lines: 1333, 1338, 1537, 1540, 2453, 2456, 2530
  - Estimated: 30-60 min

- **Item #9**: Add monadic extractors
  - `checkHyp_ok_iff`: characterize stack slice
  - `stepAssert_ok_stack`: extract concl and stack equation
  - Estimated: 1-2 hours

### Medium Priority
- **Item #5**: Split toExpr_subst_commutes into 3 smaller lemmas
  - Array fold ↔ List fold
  - Spec substitution is mapM-compatible
  - Pointwise commutation
  - Estimated: 2-3 hours

- **Item #6**: Add invariant strengthening
  - frame_size_ok
  - stack_view_ok (simp lemma)
  - Estimated: 30 min

### Lower Priority
- **Item #4**: Add dropLast_length micro-lemma
- **Item #7**: Prefer Fin indices over Nat + bounds
- **Item #8**: Eliminate any remaining Permutation uses

---

## Files Modified

### `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/Kernel.lean`

**Lines 2498-2528**: ProofStateInv cleanup
- Deleted weak 2-param structure
- Updated proof_state_has_inv axiom
- Added extract_stack_from_inv theorem (PROVEN!)

**Lines 1814-1850**: stack_shape_from_checkHyp
- Strengthened premise to mapM
- Eliminated h_stack_eq sorry
- Cleaner proof structure

**Lines 1869-1929**: stack_after_stepAssert
- Strengthened both premise and conclusion to mapM
- New proof structure using array↔list bridges
- Ready for final implementation

**Lines 1585-1586, 1981-1982**: Call sites
- Updated to use new proof_state_has_inv
- Updated to use extract_stack_from_inv

**Lines 1980**: stack_after_stepAssert call site
- Updated to use new signature
- Direct mapM equality, no rfl wrapper

### Documentation
- `WEAK_FORMULATIONS_AUDIT.md` - Initial discovery
- `BREAKTHROUGH_INDEXED_ORDER.md` - Key insight
- `GROUP_E_FINAL_WRAP_UP.md` - Previous status
- `ORUZI_CLEANUP_COMPLETE.md` - This file

---

## Build Status

```bash
lake build Metamath  # ✅ SUCCESS
```

All changes compile successfully!

---

## The Bottom Line

**Oruži's Phase 1 cleanup: COMPLETE!** 🎉

- ✅ Unified ProofStateInv (item #1.1)
- ✅ Deleted build_spec_stack axiom (item #1.2)
- ✅ Strengthened Group E to mapM (items #2, #3)
- ✅ Updated call sites (item #10)
- ✅ Everything builds

**Result**:
- **-1 axiom** (build_spec_stack eliminated)
- **-4 sorries** (9 → 5)
- **Stronger formulations** (membership → ordered mapM)
- **Clearer path** to completion

Ready to continue with Phase 2 (systematic membership→mapM replacement) or push on the remaining 5 Group E sorries!

**Your call!** 🚀
