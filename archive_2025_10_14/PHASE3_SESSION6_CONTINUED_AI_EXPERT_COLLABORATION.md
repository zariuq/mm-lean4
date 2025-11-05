# Phase 3 Session 6 (Continued): AI Expert Collaboration - Category B Challenges

**Date:** 2025-10-14
**Session Type:** Category B (Match/Domain Lemmas) with AI Expert Assistance
**Status:** In Progress - Implementation challenges encountered

---

## Session Overview

After completing Session 6's main objectives (4 sorries eliminated in checkHyp integration), we continued with Category B (Match/Domain lemmas) as identified "quick wins". We enlisted help from two AI experts (Grok and GPT-5/Oruži) for the three remaining Category B sorries.

**Starting Point:**
- Sorry count: 19 (after Session 6 Part 1-2)
- Phase 3: ~85% complete
- Category B remaining: 3 sorries (lines 460, 1137, 1229)

---

## AI Expert Request

Created comprehensive 5000+ word request document (`AI_REQUEST_CATEGORY_B_HELP.md`) with:
- Project overview and context (Metamath verifier, 85% complete)
- Three detailed problems with full code context
- 25+ specific technical questions
- Multiple proposed solution approaches
- Examples of successful proof patterns from earlier sessions

---

## AI Expert Responses

### Problem 1 (Line 460 - vars_apply_subset)

**Challenge:** Prove that variables in σ(e) come from either original expression or variables introduced by σ. Proof was stuck trying to show `s' = s` after flatMap extraction.

**Grok's Solution:**
- **Key Insight:** Don't try to prove `s' = s`!
- Choose `w := Variable.mk s'` (the producing variable from flatMap) as the existential witness
- Use `List.mem_flatMap` to extract the producing symbol
- Show two properties: (1) w is in original expression, (2) v is in image of σ applied to w

**GPT-5/Oruži's Solution (Solution 1):**
- Same key insight: producing variable IS the witness
- Detailed proof sketch:
  1. Extract `s'` from flatMap using `List.mem_flatMap`
  2. Case split on whether `Variable.mk s' ∈ vars`
  3. If yes: choose `exists Variable.mk s'` and prove both conjuncts
  4. If no: derive contradiction (constant case conflicts with h_var)

**GPT-5/Oruži's Solution 2:**
- Helper lemma approach: prove `flatMap_produces_from_source` first
- More infrastructure but cleaner main proof

**Convergence:** Both experts independently identified the same core insight - don't force equality, use the producing variable.

### Problem 2 (Line 1137 - matchHyps Composition)

**Challenge:** Show `applySubst vars σ₂ (applySubst vars σ₁ e_hyp) = applySubst vars σ₁ e_hyp`, which requires σ₂ doesn't affect variables in the result.

**Grok's Solution:**
- **Recommendation:** Use two-phase approach instead!
- Separate `matchFloats` (binding floats) from `checkEssentials` (verification)
- Avoids composition complexity entirely
- More faithful to Metamath spec structure

**GPT-5/Oruži's Solution 1 (Minimal Assumption):**
- Add precondition: `∀ v ∈ varsInExpr vars (applySubst vars σ₁ e_hyp), σ₂ v = identity`
- Prove this from matchHyps structure if possible
- Minimal disruption to existing code

**GPT-5/Oruži's Solution 2 (Refactoring):**
- Agree with Grok: two-phase separation is cleaner
- Matches actual Metamath verification pattern
- Better separation of concerns

**Convergence:** Both experts recommended the two-phase approach as superior to adding disjoint domain assumptions.

### Problem 3 (Line 1229 - matchFloats_sound)

**Challenge:** Show `fs.map (fun (tc, v) => σ v) = fs.map (fun (tc, v) => σ_rest v)` where `σ = fun w => if w = v then e else σ_rest w`. Requires showing v' ≠ v for all v' in fs.

**Grok's Solution:**
- Add `List.Nodup (floats.map Prod.snd)` precondition
- In cons case: use `List.Nodup.tail` to get tail distinctness
- Show v ∉ fs.map Prod.snd from nodup cons structure
- Use `List.map_congr` to show functions agree on fs elements
- For each (tc', v') ∈ fs, derive v' ≠ v from membership + nodup

**GPT-5/Oruži's Solution:**
- Same approach: `List.Nodup` precondition
- Detailed proof structure:
  1. Induct on floats with revert h_nodup
  2. In cons case: extract nodup properties
  3. Apply IH to tail with tail nodup
  4. Use function extensionality on restricted domain
  5. Key lemma: `v' ∈ fs.map Prod.snd → v' ≠ v` from nodup

**Convergence:** Perfect agreement on solution approach and implementation strategy.

---

## Implementation Attempts

### Problem 1 Implementation

**Attempted:**
1. Initial approach: Extract s' from flatMap using `List.mem_flatMap`
2. Choose `exists Variable.mk s'` as witness (per AI expert advice)
3. Prove both required properties

**Challenges Encountered:**
1. **Unfolding complexity:** After `unfold applySubst at *` at line 436, `hs_mem` was in complex nested form
2. **simp/rw failures:** `simp only [List.mem_flatMap] at hs_mem` made no progress
3. **Mismatched forms:** `hs_mem` after filterMap extraction wasn't in direct flatMap form

**Root Cause:** The interaction between `unfold ... at *`, `simp [List.filterMap]`, and `obtain` left `hs_mem` in a form that didn't match `List.mem_flatMap` pattern. The unfolding happened at line 436 with `at *` (affecting all hypotheses), but the subsequent `simp` and `obtain` transformed the structure in ways that made later rewrites fail.

**Status:** Reverted to sorry, needs more careful handling of unfolding/simplification sequence.

### Problem 3 Implementation

**Attempted:**
1. Add `List.Nodup (floats.map Prod.snd)` precondition to `matchFloats_sound`
2. Use `revert h_nodup` before induction to handle dependency
3. Extract nodup properties in cons case
4. Apply IH with tail nodup
5. Use `List.map_congr` to show function agreement

**Challenges Encountered:**
1. **Induction with dependent hypothesis:** Error "unnecessary 'generalizing' argument" when including h_nodup in generalizing clause
2. **Pattern matching syntax:** Error "unexpected token '⟨'" with `| cons ⟨tc, v⟩ fs ih =>` pattern
3. **Nodup API differences:** `List.Nodup` doesn't have `.not_mem` or `.tail` fields in Lean 4.20
   - Expected fields don't exist
   - Tried both `.not_mem` and Pairwise variant
4. **Structure changes after simp:** `simp [List.map_cons] at h_nodup` converted List.Nodup.cons to And, breaking field access

**Root Cause:** Lean 4.20 API for `List.Nodup` differs from what the AI experts assumed. The structure and field names have changed, requiring pattern matching or cases analysis instead of direct field access.

**Status:** Reverted to sorry, needs investigation of correct Lean 4.20 List.Nodup API.

---

## Technical Lessons Learned

### 1. AI Expert Guidance is Excellent for Strategy, Not Always for Lean 4 Specifics

**What Worked:**
- High-level proof strategies (witness selection, two-phase approach, Nodup precondition)
- Identification of key insights (don't prove s' = s!)
- Convergence on solutions across independent experts

**What Didn't:**
- Specific Lean 4.20 API details (List.Nodup fields, pattern matching syntax)
- Interaction between unfold/simp/obtain tactics
- Exact lemma names and availability

**Lesson:** Use AI expert insights for proof architecture, but verify Lean 4 specifics locally.

### 2. Unfolding Strategy Matters Critically

The failure of Problem 1 implementation came down to the sequence:
```lean
unfold applySubst varsInExpr at *  -- Line 436, unfolds EVERYWHERE
simp [List.filterMap] at hv       -- Line 437, simplifies one hypothesis
obtain ⟨s, hs_mem, hv_eq⟩ := hv   -- Line 438, extracts from simplified form
-- Now hs_mem is in complex form, later rewrites fail
```

**Better Approach:** Controlled, step-by-step unfolding with intermediate `have` statements to capture desired forms.

### 3. Lean 4 Library Evolution

Between Lean 4 versions (and what AI models were trained on), APIs change:
- `List.Nodup.not_mem` → doesn't exist (or renamed)
- `List.Nodup.tail` → doesn't exist (or renamed)
- Pattern matching syntax for tuples in induction branches

**Implication:** Need to check current Lean 4.20 documentation/source for correct API.

### 4. Dependent Hypothesis in Induction

When a hypothesis depends on the induction variable (like `h_nodup : List.Nodup (floats.map Prod.snd)`), must use `revert` before induction, then `intro` in each branch. But this creates additional complexity.

---

## Time Investment

- **AI Request Creation:** ~30 minutes
- **AI Response Analysis:** ~15 minutes
- **Problem 1 Implementation:** ~2 hours (unsuccessful)
- **Problem 3 Implementation:** ~1.5 hours (unsuccessful)
- **Total Session Time:** ~4 hours

---

## Current Status

**Sorry Count:** 19 (unchanged from Session 6 end)
**Phase 3:** ~85% complete (unchanged)

**Category B Status:**
- Line 1031 (matchExpr_sound): ✅ Complete (Session 6)
- Line 460 (vars_apply_subset): ⏸️ Clear strategy, implementation blocked by unfold/simp issues
- Line 1137 (matchHyps composition): ⏸️ Recommended refactoring to two-phase approach
- Line 1229 (matchFloats_sound): ⏸️ Clear strategy, blocked by Lean 4.20 API differences

---

## Recommendations for Next Steps

### Option A: Deep Dive on Lean 4.20 APIs (2-3 hours)
**Target:** Investigate current List.Nodup API, find correct field names/lemmas
**Benefit:** Unblock Problem 3 with correct API usage
**Risk:** Low (just API lookup)

### Option B: Simplify Problem 1 Approach (2-3 hours)
**Target:** Rewrite vars_apply_subset proof without complex unfold sequence
**Approach:** Use more `have` statements to capture intermediate forms
**Benefit:** Clear path based on AI expert strategy
**Risk:** Medium (tactic interaction subtleties)

### Option C: Problem 2 Refactoring (4-6 hours)
**Target:** Separate matchHyps into two-phase (matchFloats + checkEssentials)
**Benefit:** Cleaner design, avoids composition issue entirely
**Risk:** Medium-High (requires refactoring multiple call sites)

### Option D: Return to Category C (2-4 hours)
**Target:** Complete remaining checkHyp integration sorries (lines 2430, 2453)
**Benefit:** Progress on main verification path
**Risk:** Low (infrastructure from Session 6 ready to use)

### Option E: Comprehensive Analysis (1-2 hours)
**Target:** Analyze ALL remaining sorries, prioritize by tractability
**Benefit:** Optimal completion strategy
**Risk:** None (pure analysis)

---

## Confidence Levels

**High Confidence (>90%):**
- ✅ AI expert strategies are sound and correct
- ✅ Problem 3 can be solved with correct Lean 4.20 API knowledge
- ✅ Problem 1 can be solved with better unfolding strategy
- ✅ Two-phase approach for Problem 2 is superior design

**Medium Confidence (70-80%):**
- Problem 1 solution achievable in 2-3 hours with revised approach
- Problem 3 solution achievable in 1-2 hours with API lookup
- Category C remaining sorries doable in 4-6 hours

**Questions Remaining:**
- What are the correct `List.Nodup` field names/lemmas in Lean 4.20?
- Is there a better tactic sequence for Problem 1's unfold/extract pattern?
- Should we refactor to two-phase matchHyps now or defer?

---

## Bottom Line

**Session 6 Continued: Productive Learning Experience**

### Achievements
- ✅ Comprehensive AI expert request created
- ✅ Received detailed solutions from two independent experts
- ✅ Identified clear strategies for all three Category B problems
- ✅ Discovered important lessons about AI/Lean 4 integration

### Challenges
- ⚠️ Implementation blocked by Lean 4.20 API specifics
- ⚠️ Tactic interaction subtleties in Problem 1
- ⚠️ More complex than "quick wins" label suggested

### Impact
- Clear path forward for all three problems
- Better understanding of AI expert usage patterns
- Identification of Lean 4 API investigation needs

### Next Steps
**Recommendation:** Option A (Lean 4.20 API deep dive) followed by implementing Problem 3, then Problem 1 with revised approach. This builds momentum with solved problems before tackling refactoring.

**Alternative:** Option D (return to Category C) to make immediate progress on main verification path while letting Category B marinate.

---

**The formal verification continues with valuable AI expert insights!** While implementation hit Lean 4 specifics, the proof strategies are sound and the path forward is clear. The collaboration demonstrates both the power and limitations of AI assistance in formal verification. 🤖🐢✨

**Estimated time to solve all 3 Category B problems:** 4-8 hours (with API investigation + revised implementations)
