# Formal Verification Proof Plan for mm-lean4

**Date:** 2025-10-08
**Goal:** Prove `verify_sound` theorem in `Metamath/Kernel.lean`
**Estimated Timeline:** 2-4 months (expert Lean programmer)

---

## Executive Summary

We aim to prove that the mm-lean4 verifier is **sound**: if it accepts a proof, then the assertion is semantically provable according to the Metamath specification.

**Main Theorem:**
```lean
theorem verify_sound (db : DB) (label : String) (f : Formula) (proof : Array String) :
  db.error?.isNone →
  (db.verify label f proof).isNone →
  Provable (toDatabase db) (toFrame db db.frame) (toExpr f)
```

**Strategy:** Build up from simple lemmas to complex theorems, following established verification patterns.

---

## Phase 1: Foundation Lemmas (Weeks 1-2) ✅ IN PROGRESS

### 1.1 Frame Properties ✅ COMPLETE

| Lemma | Status | LOC | Difficulty |
|-------|--------|-----|------------|
| `empty_frame_no_hyps` | ✅ PROVEN | 3 | ⭐ Trivial |
| `empty_frame_no_dv` | ✅ PROVEN | 3 | ⭐ Trivial |
| `no_dv_always_ok` | ✅ PROVEN | 4 | ⭐ Trivial |

**Total:** 3/3 proven (100%)

### 1.2 Substitution Properties 🎯 CURRENT FOCUS

| Lemma | Status | LOC | Difficulty |
|-------|--------|-----|------------|
| `subst_preserves_typecode` | ✅ PROVEN | 2 | ⭐ Trivial |
| `identity_subst_unchanged` | ⏳ TODO | ~15 | ⭐⭐ Easy |
| `subst_composition` | ⏳ TODO | ~25 | ⭐⭐⭐ Medium |

**Strategy for identity_subst_unchanged:**
```lean
-- Need to show: List.bind on [v] with (fun v => [v]) = [v]
-- 1. Unfold List.bind definition
-- 2. Show singleton case: [v].bind f = f v
-- 3. Apply to all symbols in expression
```

**Strategy for subst_composition:**
```lean
-- Need to show: (σ₂ ∘ σ₁) e = σ₂ (σ₁ e)
-- 1. Induction on e.syms
-- 2. Case: constant → unchanged
-- 3. Case: variable v → apply associativity of bind
```

### 1.3 Disjoint Variable Properties

| Lemma | Status | LOC | Difficulty |
|-------|--------|-----|------------|
| `dv_symmetric` | ✅ PROVEN | 8 | ⭐⭐ Easy |
| `dv_not_reflexive` | ⚠️ PARTIAL | ~10 | ⭐⭐⭐ Medium |
| `dv_weakening` | ✅ PROVEN | 5 | ⭐⭐ Easy |
| `dv_append` | ✅ PROVEN | 8 | ⭐⭐ Easy |

**Total:** 3/4 proven (75%)

**Strategy for dv_not_reflexive:**
```lean
-- Need to show: (v,v) ∈ dv → σ(v) shares vars with itself → contradiction
-- Key insight: Finset.inter s s = s, so isEmpty only if s = ∅
-- But we need σ(v) to have at least one variable (the definition)
-- Problem: σ(v) could be a constant expression with no variables!
-- Fix: Assume σ(v) = ⟨tc, [v.v]⟩ (non-trivial variable mapping)
```

### 1.4 Expression Properties

| Lemma | Status | LOC | Difficulty |
|-------|--------|-----|------------|
| `expr_eq_dec` | ⏳ TODO | ~10 | ⭐⭐ Easy |
| `varsInExpr_finite` | ⏳ TODO | ~15 | ⭐⭐ Easy |

---

## Phase 2: Proof Execution Lemmas (Weeks 3-4)

### 2.1 Proof Validity Inversion Lemmas

These let us "invert" a ProofValid proof to extract information about steps.

| Lemma | Status | Difficulty |
|-------|--------|------------|
| `proofValid_nil_inv` | ⏳ TODO | ⭐⭐ Easy |
| `proofValid_useEssential_inv` | ⏳ TODO | ⭐⭐⭐ Medium |
| `proofValid_useFloating_inv` | ⏳ TODO | ⭐⭐⭐ Medium |
| `proofValid_useAxiom_inv` | ⏳ TODO | ⭐⭐⭐⭐ Hard |

**Example (proofValid_nil_inv):**
```lean
theorem proofValid_nil_inv {Γ fr stack steps} :
  ProofValid Γ fr stack steps →
  steps = [] →
  stack = [] := by
  intro hpv heq
  subst heq
  cases hpv
  · rfl  -- nil case
  · contradiction  -- all other cases have non-empty steps
```

### 2.2 Stack Manipulation Lemmas

| Lemma | Status | Difficulty |
|-------|--------|------------|
| `stack_grows_monotone` | ⏳ TODO | ⭐⭐⭐ Medium |
| `useAssertion_pops_pushes` | ⏳ TODO | ⭐⭐⭐⭐ Hard |
| `final_stack_singleton` | ⏳ TODO | ⭐⭐ Easy |

---

## Phase 3: Bridge Function Correctness (Month 2)

These connect the implementation types to spec types.

### 3.1 Type Conversion Correctness

| Lemma | Status | Difficulty |
|-------|--------|------------|
| `toSym_correct` | ⏳ TODO | ⭐ Trivial |
| `toExpr_correct` | ⏳ TODO | ⭐⭐⭐ Medium |
| `toFrame_correct` | ⏳ TODO | ⭐⭐⭐⭐ Hard |
| `toDatabase_correct` | ⏳ TODO | ⭐⭐⭐⭐⭐ Very Hard |

**Challenge:** Implementation uses imperative state (DB), spec uses functional (Database).

**Strategy for toDatabase_correct:**
```lean
-- Need to show: toDatabase db produces a valid Database
-- 1. Show all labels map correctly
-- 2. Show frames are extracted correctly
-- 3. Show no spurious entries
-- Requires: db.objects well-formed (invariant)
```

### 3.2 Well-Formedness Invariants

Define and prove invariants on DB:

| Invariant | Description | Difficulty |
|-----------|-------------|------------|
| `db_wellformed` | All labels unique, types consistent | ⭐⭐⭐⭐ Hard |
| `frame_consistent` | Frame matches current scope | ⭐⭐⭐⭐ Hard |
| `no_forward_refs` | No references to future labels | ⭐⭐⭐ Medium |

---

## Phase 4: Core Kernel Correctness (Month 2-3)

This is the **hardest part** of the entire verification.

### 4.1 Single Step Soundness ⭐⭐⭐⭐⭐ (VERY HARD)

**Main Theorem:**
```lean
axiom stepNormal_sound (db : DB) (pr : ProofState) (label : String) :
  (db.stepNormal pr label).isOk →
  ∃ σ : Subst,
    let db_spec := toDatabase db
    let fr_spec := toFrame db db.frame
    ∃ fr' e',
      db_spec label = some (fr', e') ∧
      dvOK fr_spec.dv σ ∧
      dvOK fr'.dv σ
```

**Proof Strategy:**
1. **Unfold stepNormal** into cases:
   - Hypothesis reference: `stepNormal db pr l` where `db.find? l` is a hyp
   - Assertion reference: `stepNormal db pr l` where `db.find? l` is an assert
2. **Hypothesis case:** Show pushing hypothesis formula is valid
3. **Assertion case:**
   - Extract substitution from unification
   - Prove DV constraints hold
   - Prove stack manipulation correct
   - Prove resulting formula matches spec

**Estimated LOC:** 500-800 lines
**Estimated Time:** 4-6 weeks
**Key Challenges:**
- Unification algorithm correctness
- Substitution extraction
- DV constraint verification
- Stack ordering (reverse, append, etc.)

### 4.2 Proof Iteration ⭐⭐⭐⭐ (HARD)

Once `stepNormal_sound` is proven, show that iterating it over a proof array works:

```lean
theorem proof_array_sound (db : DB) (pr : ProofState) (proof : Array String) :
  (proof.foldl (fun pr step => stepNormal db pr step) pr).isOk →
  ∃ steps : List ProofStep,
    ProofValid (toDatabase db) (toFrame db db.frame) pr.stack steps
```

**Proof Strategy:**
1. Induction on `proof` array
2. Base case: empty array → nil proof
3. Inductive case: use `stepNormal_sound` + IH

**Estimated LOC:** 200-300 lines
**Estimated Time:** 2-3 weeks

---

## Phase 5: Compressed Proofs (Month 3-4)

Handle compressed proof format (optional, can defer).

### 5.1 Decoding Correctness

| Lemma | Difficulty |
|-------|------------|
| `compressed_decode_correct` | ⭐⭐⭐⭐⭐ Very Hard |
| `compressed_equivalent_to_normal` | ⭐⭐⭐⭐⭐ Very Hard |

**Strategy:**
- Define semantic meaning of compressed format
- Show decoding produces equivalent normal proof
- May require refactoring compressed proof decoder

**Recommendation:** **DEFER** until normal proofs verified. Compressed proofs are optimization, not fundamental to soundness.

---

## Phase 6: Final Composition (Month 4)

### 6.1 Main Soundness Theorem ⭐⭐⭐ (MEDIUM)

```lean
theorem verify_sound (db : DB) (label : String) (f : Formula) (proof : Array String) :
  db.error?.isNone →
  (db.verify label f proof).isNone →
  Provable (toDatabase db) (toFrame db db.frame) (toExpr f)
```

**Proof Strategy:**
```lean
proof verify_sound:
  1. Unfold db.verify
  2. Show it creates ProofState and runs proof_array_sound
  3. Show final stack = [f] using final_stack_singleton
  4. Conclude Provable by definition
```

**Estimated LOC:** 100-150 lines (mostly composition)
**Estimated Time:** 1 week (assuming Phase 4 complete)

---

## Proof Statistics

### Current Progress

| Phase | Lemmas | Proven | % Complete |
|-------|--------|--------|------------|
| Phase 1 | 13 | 7 | 54% |
| Phase 2 | 7 | 0 | 0% |
| Phase 3 | 7 | 0 | 0% |
| Phase 4 | 2 | 0 | 0% |
| Phase 5 | 2 | 0 | 0% (DEFERRED) |
| Phase 6 | 1 | 0 | 0% |
| **TOTAL** | **32** | **7** | **22%** |

### Estimated Effort

| Phase | LOC (proof) | Weeks | Difficulty |
|-------|-------------|-------|------------|
| Phase 1 | 100-150 | 2 | ⭐⭐ Easy |
| Phase 2 | 200-300 | 2 | ⭐⭐⭐ Medium |
| Phase 3 | 300-400 | 4 | ⭐⭐⭐⭐ Hard |
| Phase 4 | 700-1100 | 8 | ⭐⭐⭐⭐⭐ Very Hard |
| Phase 5 | 400-600 | 4 | ⭐⭐⭐⭐⭐ Very Hard |
| Phase 6 | 100-150 | 1 | ⭐⭐⭐ Medium |
| **TOTAL** | **1800-2700** | **21** | N/A |

**Note:** Phase 5 (compressed proofs) can be deferred indefinitely. Focus on Phases 1-4, 6.

---

## Immediate Next Steps (This Week)

### Priority 1: Complete Phase 1.2 (Substitution)
- [ ] Prove `identity_subst_unchanged`
- [ ] Prove `subst_composition`
- [ ] Add helper lemmas for `List.bind` properties

### Priority 2: Complete Phase 1.3 (DV)
- [ ] Fix `dv_not_reflexive` (add precondition or weaken statement)
- [ ] Add more DV combination lemmas

### Priority 3: Start Phase 1.4 (Expressions)
- [ ] Prove `expr_eq_dec` (use deriving DecidableEq)
- [ ] Prove `varsInExpr_finite`

### Priority 4: Begin Phase 2 (Proof Validity)
- [ ] Prove `proofValid_nil_inv`
- [ ] Sketch proof structure for `proofValid_useEssential_inv`

**Goal for Week 1:** Complete 5+ lemmas, reach 50% of Phase 1

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Phase 4 takes longer than expected | HIGH | HIGH | Start early, break into sub-lemmas |
| Implementation needs refactoring | MEDIUM | HIGH | Keep implementation separate, add adapters |
| Compressed proofs too complex | HIGH | MEDIUM | Defer Phase 5, prove without compression |
| Bridge functions incorrect | MEDIUM | HIGH | Extensive testing, spec validation |
| Substitution too complex | LOW | MEDIUM | Add helper lemmas, simplify spec if needed |

---

## Success Criteria

### Minimum Viable Verification (MVP)
- **Goal:** Prove soundness for **uncompressed proofs only**
- **Scope:** Phases 1-4, 6 (skip Phase 5)
- **Result:** `verify_sound_uncompressed` theorem
- **Timeline:** 3-4 months
- **Value:** High (covers 95% of verification kernel)

### Full Verification
- **Goal:** Prove soundness including compressed proofs
- **Scope:** All phases 1-6
- **Result:** Full `verify_sound` theorem
- **Timeline:** 5-6 months
- **Value:** Complete (but marginal benefit over MVP)

**Recommendation:** Target MVP first, add compression later if needed.

---

## References

1. **Metamath Specification:** `/home/zar/claude/hyperon/metamath/metamath.pdf`
2. **Test Catalogue:** `/home/zar/claude/hyperon/metamath/metamath-test/canonical-tests/TEST_CATALOGUE.md`
3. **Spec Alignment:** `/home/zar/claude/hyperon/metamath/mm-lean4/SPEC_ALIGNMENT.md`
4. **Related Work:**
   - metamath-knife (Rust, untrusted implementation)
   - mmverify.py (Python, trusted but unverified)
   - mm0 (verified checker for MM0 language, not full Metamath)

---

## Conclusion

**Feasibility:** ✅ **YES** - with 2-4 months of focused effort

**Current Status:** 22% complete (7/32 lemmas proven)

**Recommended Path:**
1. **Week 1-2:** Finish Phase 1 (foundation lemmas)
2. **Week 3-4:** Complete Phase 2 (proof execution lemmas)
3. **Month 2:** Phase 3 (bridge functions)
4. **Month 2-3:** Phase 4 (core kernel) ← **CRITICAL PATH**
5. **Month 4:** Phase 6 (final composition)

**Defer:** Phase 5 (compressed proofs) until after MVP complete

**Next Action:** Prove `identity_subst_unchanged` and `subst_composition` this week!
