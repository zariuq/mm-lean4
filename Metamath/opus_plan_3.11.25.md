 Opus Implementation Plan - Metamath Kernel Verification Completion

     Date: 2025-11-03
     Status: 88% Complete → Target 100%

     Executive Summary

     The project is in excellent shape with 3 major axioms eliminated. GPT-5 Pro (Oruži) has provided the exact solution for our main blocker (stepNormal_sound). I'll complete the critical path to full 
     soundness in this session.

     Phase 1: Fix stepNormal_sound (Immediate - 15 mins)

     Problem: Using split at h_step doesn't bind equations, causing contradiction failures
     Solution: Use cases h_find : db.find? label with pattern from preload_sound

     Actions:

     1. Replace lines 1798-1834 with Oruži's pattern
     2. Add equation binding for db.find? label
     3. Use simp [h_find] at h_step for contradictions
     4. Wire up float_step_ok and essential_step_ok properly

     Phase 2: Complete checkHyp_hyp_matches (30 mins)

     Location: Lines 1554-1574
     Pattern: Similar to checkHyp_validates_floats recursion

     Actions:

     1. Define recursion on checkHyp structure
     2. Use equation lemmas for essential hypotheses
     3. Build stack correspondence proof
     4. This unblocks assert_step_ok

     Phase 3: Complete assert_step_ok (45 mins)

     Location: Lines 1712-1777
     Dependencies: Needs checkHyp_hyp_matches

     Actions:

     1. Extract TypedSubst from checkHyp success
     2. Build "needed" list from stack window
     3. Prove frame preservation through monadic ops
     4. Complete stack correspondence

     Phase 4: Fix Array/List conversions (20 mins)

     Locations: Lines 1925-1927, other Array.size issues

     Actions:

     1. Add helper lemma for Array.size = toList.length
     2. Use existing Array utilities from KernelExtras
     3. Fix the viewStack singleton proof

     Phase 5: Complete fold_maintains_provable (30 mins)

     Location: Lines 1868-1958
     Using: GPT-5 Pro's array_foldlM_preserves approach

     Actions:

     1. Fix the step case (line 1888) using stepNormal_sound
     2. Build ProofValidSeq.cons properly
     3. Fix Array.toList_length issue
     4. Complete final stack extraction

     Phase 6: Documentation (10 mins)

     Create Opus_plan_3_11_25.md with:

     1. Complete implementation details
     2. Oruži's guidance incorporated
     3. Final axiom status
     4. Lessons learned

     Critical Path Summary

     stepNormal_sound (15m) → checkHyp_hyp_matches (30m) → assert_step_ok (45m) 
     → Array fixes (20m) → fold_maintains_provable (30m) → Documentation (10m)

     Total Time: ~2.5 hours
     Result: Main soundness theorem with only 1 documented axiom (frame validity)

     Key Insights from Oruži

     1. Equation binding pattern: cases h_find : expr with not split at
     2. Simplification at hypothesis: simp [h_find] at h_step exposes contradictions
     3. Array fold preservation: Use existing array_foldlM_preserves infrastructure
     4. Helper lemmas: Add small tactical lemmas for common patterns

     Success Metrics

     - Build compiles with 0 errors
     - stepNormal_sound complete (no sorries in dispatcher)
     - Main theorem depends on ≤1 axiom
     - All Phase 5 infrastructure proven
     - Documentation captures full journey

     This plan directly addresses the critical path with Oruži's precise guidance, focusing on what needs my architectural understanding rather than mechanical proof steps.


