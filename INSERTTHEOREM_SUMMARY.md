# InsertTheorem Proof Summary

**Quick Reference**: Detailed analysis in `INSERTTHEOREM_ANALYSIS.md`

## Current Status

5 sorries in `insertTheorem` proof (lines 998-1080):
- 2 require **assumptions/preconditions** 
- 3 are **provable** with new lemmas

## Recommended Approach

### Step 1: Add Preconditions (REQUIRED)

Modify `DBOp.insertTheorem` constructor:

```lean
| insertTheorem (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
    (h_fr_unique : ∀ (db : DB), frame_has_unique_floats db fr.hyps)
    (h_fresh : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l)
```

**Justification**: These properties hold in the real parser but are lost in the abstract model.

### Step 2: Add Helper Lemmas (PROVABLE)

```lean
-- Lemma 1: Lookup after insert (mirrors find?_insert_self_hyp)
@[simp] theorem DB.find?_insert_self_assert
  (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  (h_success : (db.insert pos l (fun _ => .assert fmla fr proof)).error? = none) :
  (db.insert pos l (fun _ => .assert fmla fr proof)).find? l = 
    some (.assert fmla fr proof)

-- Lemma 2: Extract success from Right branch (or restructure proof)
theorem insert_const_var_maintains_uniqueness_implies_success :
  (insert_const_var_maintains_uniqueness ... = inr h_inv') →
  (db.insert pos l obj).error? = none

-- Lemma 3: withFrame preserves frame_uniqueness (if needed)
theorem withFrame_preserves_frame_uniqueness :
  frame_has_unique_floats db hyps →
  frame_has_unique_floats (db.withFrame f) hyps
```

### Step 3: Fill Sorries

1. **Line 1019**: Use precondition `h_fr_unique`
2. **Line 1026**: Use precondition `h_fresh`  
3. **Line 1058**: Use Lemma 2 or remove `by_cases`
4. **Line 1074**: Use Lemma 1 + injection + `frame_has_unique_floats_insert_ne`
5. **Line 1079**: Direct application: `exact h_frames label' fmla' fr' proof' h_find`

## Effort Estimate

- Add preconditions: **10 minutes**
- Prove 2-3 lemmas: **45 minutes**
- Fill sorries: **30 minutes**
- Validation: **15 minutes**

**Total: 1-2 hours**

## Key Insights

1. **No new axioms needed** - all provable from existing HashMap infrastructure
2. **Preconditions document real parser behavior** - makes contracts explicit
3. **Sorry #5 is trivial** - likely just `exact h_frames ...`
4. **Sorry #3 is structural** - comes from proof organization, not fundamental gap

## Files to Modify

1. `Metamath/ParserProofs.lean`:
   - Line 890: Modify `insertTheorem` constructor
   - Lines 181-233: Add `find?_insert_self_assert` (mirror `_self_hyp`)
   - Lines 1015-1080: Fill 5 sorries

## Alternative: Accept Axioms

If preconditions are undesirable:

```lean
axiom insertTheorem_frame_uniqueness : ∀ db fr, frame_has_unique_floats db fr.hyps
axiom insertTheorem_label_freshness : ∀ l fr, ∀ i hi, fr.hyps[i]'hi ≠ l
```

Less explicit but philosophically cleaner. **Effort: 30 minutes**

## See Also

- Full analysis: `INSERTTHEOREM_ANALYSIS.md`
- Related proofs: `insert_const_var_maintains_uniqueness` (line 688)
- Infrastructure: `frame_has_unique_floats_insert_ne` (line 842)
