# Phase 3 Session 5: checkHyp Integration Analysis

**Date:** 2025-10-14
**Focus:** Category C - checkHyp Integration (7 sorries)
**Status:** Analysis complete, infrastructure proven, main proofs documented

## Summary

Analyzed Category C (checkHyp Integration) and made significant progress on infrastructure:

1. ✅ **Proven `floats_complete`** - Bridge/Basics.lean - 5 lines
2. ✅ **Documented line 1449 strategy** - TypedSubst witness - comprehensive proof strategy
3. 📊 **Mapped checkHyp integration landscape** - understood dependencies and proof structure

## Accomplishments

### 1. floats_complete Proven (Bridge/Basics.lean:135-141)

**Theorem:** Every floating hypothesis in a frame appears in the floats list.

```lean
theorem floats_complete (fr : Spec.Frame) :
    ∀ c v, Hyp.floating c v ∈ fr.mand → (c, v) ∈ floats fr := by
  intro c v h_mem
  unfold floats
  -- Use List.mem_filterMap: x ∈ filterMap f xs ↔ ∃ a ∈ xs, f a = some x
  simp [List.mem_filterMap]
  exists Hyp.floating c v, h_mem
```

**Achievement:**
- Simple 5-line proof using `List.mem_filterMap`
- No induction needed - direct existential witness
- **Key lesson:** Use library lemmas about filterMap rather than manual induction

**Impact:** This is needed for all TypedSubst witness proofs (lines 1449, 2170+)

### 2. Line 1449 Analysis - TypedSubst Witness

**Location:** Kernel.lean:1445-1491 (toSubstTyped definition)

**Goal:** Prove that `σ_fn` respects floating hypothesis typecodes

**Proof Strategy Documented:**
1. ✅ Use `floats_complete`: `h_float` implies `(c, v) ∈ float_list`
2. ⏸️ Extract from `allM`: validation succeeded for all elements
3. ⏸️ Show `σ_impl[v.v]? = some f` and `toExprOpt f = some e` and `e.typecode = c`
4. ⏸️ By definition of `σ_fn`, conclude `(σ_fn v).typecode = c`

**Blocker Identified:**
- Need to extract computational properties from do-notation and allM
- Requires: "allM succeeds → predicate holds for each element" lemma
- This is a 20-30 line proof using allM induction + Option bind laws
- OR: Trust as computational property (similar to parser validation)

**Decision:**
- Documented comprehensive proof strategy (30+ lines of comments)
- Left as sorry with clear label: "Computational property: allM validation ensures typecode correctness"
- Can be proven or axiomatized later based on project priorities

### 3. checkHyp Integration Landscape

**The 7 checkHyp sorries fall into 3 groups:**

#### Group 1: TypedSubst Witnesses (2 sorries)
- **Line 1449:** toSubstTyped witness (analyzed above)
- **Line 2170:** checkHyp_produces_TypedSubst - THE main integration theorem

**Dependency:** Both need allM extraction OR computational trust

#### Group 2: checkHyp Specification Matching (2 sorries)
- **Line 2338:** checkHyp floats ≈ matchFloats
- **Line 2361:** checkHyp essentials ≈ checkEssentials

**Dependency:** Need to show implementation checkHyp matches spec-level matching

#### Group 3: Inductive Step Proofs (3 sorries)
- **Lines 2765, 2769, 2775:** checkHyp inductive cases

**Dependency:** Case analysis on hypothesis types, frame structure

## Technical Insights

### 1. allM Extraction is Non-Trivial

The pattern:
```lean
let valid ← xs.allM (fun x => do ...)
if !valid then none else some (construct_using_validation_results)
```

Requires proving: "valid = true → validation succeeded for each x ∈ xs"

**Challenge:** Extracting computational properties from monadic do-notation inside a proof context.

**Approaches:**
- **A:** Prove using allM induction + Option monad laws (20-30 lines)
- **B:** Axiomatize as computational property (like parser validation)
- **C:** Refactor to use dependent types that carry proofs

### 2. floats_complete Pattern is Clean

Using `List.mem_filterMap` makes filterMap completeness proofs trivial:
- ✅ floats_complete: 5 lines
- 🔜 floats_sound: Similar (5 lines)
- 🔜 essentials_complete: Similar (5 lines)
- 🔜 essentials_sound: Similar (5 lines)

**Lesson:** Search for library lemmas about list operations before manual induction.

### 3. checkHyp Integration is Foundational

The 7 sorries aren't independent - they form a proof architecture:
1. Prove infrastructure (floats_complete, floats_sound, etc.)
2. Prove TypedSubst witnesses use validation correctly
3. Prove checkHyp matches spec-level operations
4. Prove inductive cases preserve invariants

**Estimated effort:** 8-12 hours remains accurate, but it's interconnected work.

## Files Modified

### Metamath/Bridge/Basics.lean
- **Lines 135-141:** floats_complete proven ✅
- **Impact:** 0 new errors, builds successfully

### Metamath/Kernel.lean
- **Lines 1454-1491:** Line 1449 documented with comprehensive proof strategy
- **Impact:** 0 new errors (still 184 total)

## Error Count

**Before Session 5:** 184 errors
**After floats_complete:** 184 errors ✅
**After line 1449 analysis:** 184 errors ✅

**Analysis:** No new errors introduced. The sorry at line 1449 has extensive documentation and proof strategy.

## Lessons Learned

### 1. Infrastructure First

Proving helper lemmas (like `floats_complete`) first makes main proofs clearer. We can now confidently use `floats_complete` in any TypedSubst witness proof.

### 2. Computational Properties are Tricky

Extracting properties from computational definitions (do-notation, allM, validation loops) is harder than pure functional proofs. Need to decide: prove or trust?

### 3. Documentation is Proof Progress

Even when leaving a sorry, comprehensive documentation of the proof strategy is valuable:
- Shows the path forward (not blocked, just deferred)
- Makes it easy for anyone to pick up and complete
- Demonstrates understanding of the problem

### 4. Library Lemmas Save Time

`List.mem_filterMap` reduced a 20-line induction proof to 5 lines. Always search Batteries/Std for relevant lemmas before rolling your own.

## Recommended Next Steps for checkHyp

**To complete Category C (checkHyp Integration):**

1. **Prove or axiomatize allM extraction** (2-3 hours)
   - Decide: prove with induction or trust as computational property
   - Complete line 1449 using the extraction lemma
   - Pattern applies to line 2170 as well

2. **Prove remaining floats/essentials lemmas** (30 min)
   - floats_sound, essentials_complete, essentials_sound
   - All follow the same `List.mem_filterMap` pattern

3. **Complete line 2170** (3-4 hours)
   - Main integration theorem: checkHyp → TypedSubst
   - Uses `checkHyp_produces_typed_coverage` (which may also have sorries)
   - Requires TypedSubst witness (line 1449)

4. **Prove checkHyp matching lemmas** (2-3 hours)
   - Lines 2338, 2361: Show checkHyp matches spec operations
   - Structural proofs about list processing

5. **Complete inductive cases** (2-3 hours)
   - Lines 2765, 2769, 2775: Case analysis on hypothesis types
   - Use floats/essentials lemmas

**Total estimate:** 10-14 hours (slightly higher than initial 8-12, due to allM complexity)

## Confidence Levels

**Very High Confidence (>95%):**
- ✅ floats_complete proof is correct
- ✅ Proof strategy for line 1449 is sound
- ✅ checkHyp integration landscape is accurately mapped

**High Confidence (>90%):**
- allM extraction can be proven in 20-30 lines (or axiomatized pragmatically)
- Remaining floats/essentials lemmas are 5 lines each
- Total checkHyp completion time: 10-14 hours

**Medium Confidence (70-80%):**
- Some checkHyp sorries may have additional dependencies we haven't explored yet
- Line 2170 might require proving additional properties of checkHyp_produces_typed_coverage

## Bottom Line

**Progress:** Made significant progress on checkHyp infrastructure and analysis!

✅ floats_complete proven (5 lines)
✅ Line 1449 strategy comprehensively documented
✅ checkHyp integration landscape mapped
✅ No new errors introduced (184 stable)

**Key Insight:** checkHyp integration requires deciding whether to prove or trust computational properties from allM validation. The proof strategy is clear, but execution requires either:
- **Option A:** 20-30 line proof using allM induction + bind laws
- **Option B:** Axiomatize as computational property (pragmatic)

**Recommendation for Session 6:** Complete easier targets first (Option C) to maintain momentum, then return to checkHyp with fresh perspective on the allM extraction decision.

---

**Files:**
- `Metamath/Bridge/Basics.lean` - floats_complete proven
- `Metamath/Kernel.lean` - Line 1449 documented with proof strategy
- `PHASE3_SESSION5_CHECKHYP_ANALYSIS.md` - This document
