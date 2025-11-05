# Sorry Dependency Analysis & Execution Order

**Date:** 2025-10-13
**Goal:** Solve sorries in dependency order, starting with foundations

---

## Dependency Layers

### **Layer 0: Pure Library Properties (No Dependencies)** - 3 sorries
These are standard library lemmas with no dependencies on domain code.

1. **List.mapM_length_option** (KernelExtras:16)
   - No dependencies
   - Standard List.mapM property

2. **List.foldl_and_eq_true** (KernelExtras:24)
   - No dependencies
   - Standard fold property

3. **List.foldl_all₂** (KernelExtras:32)
   - No dependencies (can use foldl_and_eq_true but not required)
   - Standard fold property

---

### **Layer 1: Foundation Library (Used by Key-Based Refactor)** - 2 sorries
These are used directly in the key-based refactor proof.

4. **Array.mem_toList_get** (KernelExtras:53)
   - No dependencies
   - **Used by:** Key-based refactor line 2465

5. **List.mapM_some_of_mem** (KernelExtras:39)
   - No dependencies
   - **Used by:** Key-based refactor line 2474

---

### **Layer 2: Key-Based Refactor Completion** - 1 sorry
Depends on Layer 1 being complete.

6. **Array.getElem! = getElem for Fin** (Kernel:2472)
   - **Depends on:** Layers 0-1 being solid
   - **Used by:** Key-based refactor base case (completes it!)

---

### **Layer 3: Bridge Helper Properties** - 3 sorries
Foundation for bridge correctness.

7. **HashMap.contains_eq_isSome** (Kernel:1825)
   - No dependencies
   - Standard HashMap property

8. **toFrame_preserves_floats** (Kernel:1813)
   - No dependencies on other sorries
   - Bridge property

9. **toExpr_typecode_from_FloatBindWitness** (Kernel:1840)
   - No dependencies on other sorries
   - Bridge property

---

### **Layer 4: Bridge Correctness Components** - 3 sorries
Depend on Layer 3 being complete.

10. **toFrame Phase 3 allM reasoning** (Kernel:1896)
    - **Depends on:** Layer 3 properties
    - Completes toFrame_sound proof

11. **checkHyp floats ≈ matchFloats** (Kernel:2064)
    - **Depends on:** Layer 3 properties
    - Bridge approximation

12. **checkHyp essentials ≈ checkEssentials** (Kernel:2087)
    - **Depends on:** Layer 3 properties
    - Bridge approximation

---

### **Layer 5: ViewStack & Helper Lemmas** - 5 sorries
Independent helper lemmas.

13. **viewStack append** (Kernel:3090)
    - No dependencies
    - Helper lemma

14. **viewStack dropLast** (Kernel:3102)
    - No dependencies
    - Helper lemma

15. **mapM index preservation** (Kernel:3465)
    - No dependencies
    - Helper lemma

16. **list_mapM_length** (Kernel:3469)
    - Could use Layer 0 mapM_length_option
    - Helper lemma

17. **for-loop analysis** (Kernel:3716)
    - No dependencies
    - Helper lemma

---

### **Layer 6: Complex Domain Proofs** - 17 sorries
High-complexity proofs, many depend on earlier layers.

18. **substitutionValid** (Kernel:206)
19. **matchFloats** (Kernel:336)
20. **foldlVars** (Kernel:420)
21. **checkEssentials** (Kernel:457)
22. **allMFresh** (Kernel:673)
23. **List distinctness** (Kernel:916)
24. **List distinctness #2** (Kernel:933)
25. **Vars parameter** (Kernel:968)
26. **distinctness property** (Kernel:1070)
27. **Sigma rest agreement** (Kernel:1151)
28. **Validation loop** (Kernel:1406)
29. **ProofStateInv** (Kernel:2864)
30. **runProofSteps** (Kernel:3608)

---

### **Layer 7: Inductive Step** - 4 sorries
Depends on understanding base case pattern (Layer 2).

31. **Inductive step entry** (Kernel:2496)
    - **Depends on:** Layer 2 complete (base case pattern)
    - Inductive case structure

32. **None case** (Kernel:2500)
    - **Depends on:** Layer 2 complete
    - Error path

33. **Non-hyp cases** (Kernel:2506)
    - **Depends on:** Layer 2 complete
    - Error paths

34. **Hyp case** (Kernel:2508)
    - **Depends on:** Layer 2 complete
    - Main inductive case

---

## Execution Strategy

### Phase 1: Foundation (Layers 0-2) 🎯 **HIGH PRIORITY**
**Goal:** Complete key-based refactor with zero library sorries
**Sorries:** 6 (3 + 2 + 1)
**Estimated Time:** 2-4 hours
**Impact:** ✅ Complete base case proof with zero TRUSTED assumptions!

### Phase 2: Bridge (Layers 3-4) 🎯 **MEDIUM PRIORITY**
**Goal:** Complete toFrame_sound proof
**Sorries:** 6 (3 + 3)
**Estimated Time:** 4-8 hours
**Impact:** ✅ End-to-end bridge verification

### Phase 3: Helpers (Layer 5) 🎯 **LOW PRIORITY**
**Goal:** Prove supporting lemmas
**Sorries:** 5
**Estimated Time:** 2-4 hours
**Impact:** ✅ Clean up technical debt

### Phase 4: Domain (Layer 6) 🎯 **DEFERRED**
**Goal:** Complete complex domain proofs
**Sorries:** 17
**Estimated Time:** 20-40 hours (very high complexity)
**Impact:** ✅ Full verification (long-term goal)

### Phase 5: Inductive (Layer 7) 🎯 **DEFERRED**
**Goal:** Complete inductive step
**Sorries:** 4
**Estimated Time:** 10-20 hours
**Impact:** ✅ Complete checkHyp_correct proof

---

## Recommended Execution Order

**Start with Phase 1 (Layers 0-2):**

1. ✅ List.mapM_length_option (Layer 0)
2. ✅ List.foldl_and_eq_true (Layer 0)
3. ✅ List.foldl_all₂ (Layer 0)
4. ✅ Array.mem_toList_get (Layer 1)
5. ✅ List.mapM_some_of_mem (Layer 1)
6. ✅ Array.getElem! = getElem (Layer 2)

**Then Phase 2 if time permits (Layers 3-4):**

7. HashMap.contains_eq_isSome (Layer 3)
8. toFrame_preserves_floats (Layer 3)
9. toExpr_typecode_from_FloatBindWitness (Layer 3)
10. toFrame Phase 3 allM (Layer 4)
11. checkHyp floats ≈ matchFloats (Layer 4)
12. checkHyp essentials ≈ checkEssentials (Layer 4)

---

**Let's start! 🚀**
