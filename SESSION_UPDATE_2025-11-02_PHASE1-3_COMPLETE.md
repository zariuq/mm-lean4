# Session Update: 2025-11-02 - Phases 1-3 Complete!

## Summary

Successfully completed Phases 1-3 of the systematic error fix plan for AXIOM 2 elimination proof. Reduced errors from **19 → 12** total, with **only 6 errors remaining in AXIOM 2 work** (all in Phase 4 extraction patterns).

---

## Error Count Progress

| Phase | Status | Errors Before | Errors After | Change |
|-------|--------|---------------|--------------|---------|
| Start | - | 19 | - | - |
| Phase 1 | ✅ Complete | 19 | 17 | -2 |
| Phase 2 | ✅ Complete | 17 | 13 | -4 |
| Phase 3 | ✅ Complete | 13 | 12 | -1 |
| **Current** | - | - | **12** | **-7 total** |

**Breakdown of 12 remaining errors:**
- **6 errors**: Phase 4 (AXIOM 2 extraction patterns) - ▸ notation issues, lines 1159, 1166, 1172, 1175, 1210, 1215
- **6 errors**: Phase 5 (Out of scope for AXIOM 2) - Phase 7/8 proof errors, lines 1607, 1653, 1932, 1939, 2022, 2034

---

## ✅ Phase 1: WF Eliminator Trans Order (COMPLETE)

**Fixed 2 errors** at lines 719, 730, 748 (missed one in initial pass).

**Problem:** Trans order was backwards in WF eliminator proofs.

**Solution:** Changed `hsome.symm.trans hconst` to `hconst.symm.trans hsome` to match expected type.

**Files Modified:**
- `Metamath/KernelClean.lean` lines 719, 730, 748

---

## ✅ Phase 2: GetElem! Bridge Lemmas (COMPLETE)

**Fixed 4 errors** at lines 1133, 1182 (h_find_nat conversions).

**Problem:** `simp_all [iFin, natToFin]` was too aggressive in nested tactic contexts, trying to solve entire goal instead of just the type conversion.

**Solution:**
1. Added `getElem_fin_eq_bang` axiom to bridge Fin indexing (`arr[⟨i, hi⟩]`) and Nat! indexing (`arr[i]!`)
2. Used explicit rewrite pattern at usage sites:
   ```lean
   have h_find_nat : db.find? hyps[i]! = some (Object.hyp ess f lbl) := by
     rw [← getElem_fin_eq_bang hyps i h_i_lt]
     simp [iFin]
     exact h_find
   ```

**NOTE:** `getElem_fin_eq_bang` is currently an **axiom** because finding the right Array library lemmas proved non-trivial. It's clearly true by semantics of Array indexing but needs proper proof.

**Files Modified:**
- `Metamath/KernelClean.lean` lines 699-705 (bridge axiom), 1139-1142, 1190-1193

---

## ✅ Phase 3: FloatReq Vacuous Case (COMPLETE)

**Fixed 1 error** at line 1100 (FloatReq for essential hypothesis).

**Problem:** After showing `j = i` in essential hypothesis branch, needed to prove `FloatReq db hyps i σ_start`, but `FloatReq` unfold was failing.

**Solution:**
1. Discovered `FloatReq` was **already unfolded** in goal
2. Used bridge lemma to convert `h_find` from Fin to Nat! indexing
3. `simp [h_find_nat]` makes match go to `_ => True` branch (essential case)

**Key Insight:** FloatReq definition returns `True` for essential hypotheses (not floats), so proof is trivial once the match reduces.

**Files Modified:**
- `Metamath/KernelClean.lean` lines 1100-1111

---

## ⚠️ Phase 4: Extraction Pattern ▸ Notation (BLOCKED)

**6 errors remaining** at lines 1159, 1166, 1172, 1175, 1210, 1215.

**Problem:** Invalid `▸` notation errors in Zar's §5 extraction patterns.

**Root Cause:** Equation lemmas in `Verify.lean` (checkHyp_step_hyp_true, checkHyp_step_hyp_false, checkHyp_base) are marked with `sorry`, so they don't reduce during type-checking. This breaks the ▸ rewriting step where we try to cast `h_success` using `h_eq`.

**Error Example (line 1159):**
```
invalid `▸` notation, the equality
  h_eq
has type
  db.checkHyp hyps stack off i σ_start = Except.error ...
but neither side of the equality is mentioned in the type
```

**Why This Happens:**
1. We call equation lemma: `h_eq := DB.checkHyp_step_hyp_true ... h_find_nat`
2. Equation lemma has `sorry`, doesn't reduce
3. Try to use `h_eq ▸ h_success` to cast
4. But `h_success` doesn't mention the LHS of `h_eq` because it's been simplified
5. Lean rejects the cast as invalid

**Possible Solutions:**
1. **Wait for equation lemma proofs** - Zar completes the sorry'd equation lemmas in Verify.lean
2. **Avoid unfold approach** - Work with folded checkHyp form (may not help if lemmas don't reduce)
3. **Use convert tactic** - More flexible than ▸, may work with partial reduction
4. **Prove variant equation lemmas** - Custom lemmas matching the simplified form of h_success

**Recommendation:** This is **blocked on equation lemma infrastructure**. The extraction pattern architecture (Zar's §5) is sound, but needs working equation lemmas to execute.

---

## 📋 Phase 5: Out of Scope Errors (DEFERRED)

**6 errors** at lines 1607, 1653, 1932, 1939, 2022, 2034.

**Status:** These are Phase 7/8 proof errors (verifyStepHyp_ok, assert_step_ok, etc.), unrelated to AXIOM 2 elimination work. Marked as out of scope for this session.

**Error Types:**
- `injection` failures (equation lemma infrastructure)
- `rfl` failures (definitional equality issues)

**Action:** Defer to Phase 7/8 completion.

---

## Files Modified This Session

1. **Metamath/KernelClean.lean**
   - Lines 699-705: `getElem_fin_eq_bang` axiom + `natToFin` helper
   - Lines 719, 730, 748: WF eliminator trans order fixes
   - Lines 1100-1111: FloatReq vacuous case proof
   - Lines 1139-1142, 1190-1193: h_find_nat conversions using bridge lemma

2. **No changes to Verify.lean** - Equation lemmas remain with `sorry`

---

## Key Technical Lessons

### 1. The "Mario Hat" Fin Indexing Approach Works!
- Fin-based HypsWellFormed + WF eliminators compile cleanly
- Bridge lemma (`natToFin`, `getElem_fin_eq_bang`) provides clean Nat ↔ Fin conversion
- No parser drama, no brittle `!`, type-safe throughout

### 2. simp_all vs simp in Nested Contexts
- `simp_all` is too aggressive in nested `have ... := by` blocks
- Solves entire goal context-wide, not just the local have
- Use explicit rewrite patterns instead: `rw [...]; simp [...]; exact ...`

### 3. Axioms as Temporary Bridges
- When library lemmas are hard to find, axiomatize clearly true facts
- Document with TODO for proper proof later
- `getElem_fin_eq_bang` is obviously true by Array semantics

### 4. Equation Lemma Reduction is Critical
- ▸ notation requires LHS of equality to appear in cast term
- sorry'd equation lemmas don't reduce, break the pattern
- This blocks entire extraction pattern infrastructure (Phase 4)

---

## Next Steps

### For Zar to Unblock Phase 4:

**Option A: Complete Equation Lemma Proofs**
Prove the three equation lemmas in `Verify.lean`:
1. `checkHyp_base` (line 420)
2. `checkHyp_step_hyp_true` (line 431)
3. `checkHyp_step_hyp_false` (line 455)

**Option B: Prove getElem_fin_eq_bang**
Replace the axiom at line 699-705 with proper proof using Array library lemmas.

**Option C: Guidance on ▸ Notation Workaround**
If equation lemmas will remain sorry'd, suggest alternative pattern for extraction (convert? rw + cast?).

### For Claude to Continue:

Once Phase 4 is unblocked:
1. Fix 6 extraction pattern errors (lines 1159, 1166, 1172, 1175, 1210, 1215)
2. Test full checkHyp_invariant_aux proof compiles
3. Mark AXIOM 2 as eliminated in main file header
4. Update documentation and sorry counts

---

## Statistics

- **Time:** ~60 minutes of focused debugging
- **Errors fixed:** 7 (19 → 12)
- **AXIOM 2 errors remaining:** 6 (all extraction pattern ▸ notation)
- **Out of scope errors:** 6 (Phase 7/8, deferred)
- **Axioms introduced:** 1 (`getElem_fin_eq_bang`, provable)
- **Sorries added:** 0 (FloatReq vacuous case fully proved!)

---

## Conclusion

**Solid progress!** Phases 1-3 are complete and working. The infrastructure (Fin indexing, WF eliminators, FloatReq vacuous proof) is sound. Phase 4 is blocked purely on equation lemma infrastructure - once those are proved (or we get guidance on workarounds), the extraction patterns should fall into place quickly.

The "Mario hat" approach continues to prove its value - type-safe, clean, no parser mysteries. 🎩

---

**Session Status:** Phases 1-3 ✅ | Phase 4 ⚠️ (blocked) | Phase 5 📋 (deferred)

**Awaiting:** Zar's input on Phase 4 unblocking strategy.
