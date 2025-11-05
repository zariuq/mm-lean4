# InsertTheorem Completion Roadmap

**Visual guide to completing the insertTheorem proof**

```
Current State: 5 sorries
├── Sorry #1 (line 1019): frame_has_unique_floats db fr.hyps ───┐
├── Sorry #2 (line 1026): l ∉ fr.hyps                          │ PRECONDITIONS
├── Sorry #3 (line 1058): Insert success vs invariant          │ (Add to constructor)
├── Sorry #4 (line 1074): Lookup after insert                  │ 
└── Sorry #5 (line 1079): Old assertions preserved              │
                                                                 │
Target State: 0 sorries                                          │
├── 2 preconditions document contracts                          │
├── 3 lemmas prove technical details                            │
└── All sorries eliminated                                       ┘
```

## Phase-by-Phase Completion

### Phase 1: Infrastructure Setup (45 min)

**Task 1.1: Add DB.find?_insert_self_assert** (20 min)
```
Location: After line 233 (following DB.find?_insert_self_hyp)
Template: Mirror the _self_hyp proof structure
Steps:
  1. Copy lines 181-233 
  2. Replace .hyp ess f with .assert fmla fr proof
  3. Adapt duplicate check logic for assertions
  4. Test with #check
```

**Task 1.2: Add success extraction lemma** (15 min)
```
Location: After line 753 (following insert_const_var_maintains_uniqueness)
Two options:
  A. New lemma extracting success condition
  B. Restructure insertTheorem to avoid by_cases
Recommend: Option A for minimal changes
```

**Task 1.3: Add withFrame preservation lemma** (10 min, if needed)
```
Location: After line 95 (in helper lemmas section)
Simple proof: withFrame doesn't change objects → find? unchanged
```

### Phase 2: Add Preconditions (10 min)

**Task 2.1: Modify DBOp constructor**
```diff
Location: Line 890

- | insertTheorem (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
+ | insertTheorem (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
+     (h_fr_unique : ∀ (db : DB), frame_has_unique_floats db fr.hyps)
+     (h_fresh : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l)
```

**Task 2.2: Update DBOp.apply**
```
Location: Line 903-904
No change needed - apply doesn't use the preconditions
They're only checked at construction time
```

### Phase 3: Fill Sorries (30 min)

**Sorry #1: Line 1019** (2 min)
```diff
- sorry -- Assumption: frame_has_unique_floats db fr.hyps
+ apply h_fr_unique
```

**Sorry #2: Line 1026** (2 min)
```diff
- sorry -- Assumption: l ∉ fr.hyps
+ apply h_fresh
```

**Sorry #3: Line 1058** (10 min)
```diff
Strategy A: Use success extraction lemma
- sorry -- Need: db_has_unique_floats implies error? = none
+ have h_success_ins := insert_success_from_inr h_insert
+ exact frame_has_unique_floats_insert_ne ... h_success_ins

Strategy B: Remove by_cases (restructure lines 1052-1058)
- by_cases h_success_ins : ...
- · exact frame_has_unique_floats_insert_ne ...
- · sorry
+ have h_success_ins : ... := by <extract from h_inv_after>
+ exact frame_has_unique_floats_insert_ne ... h_success_ins
```

**Sorry #4: Line 1074** (10 min)
```diff
- sorry -- Need: lookup at l after insert gives inserted object
+ have h_inserted := DB.find?_insert_self_assert db pos l fmla fr proof h_success_ins
+ rw [h_inserted] at h_find
+ injection h_find with h_fmla h_fr h_proof
+ subst h_fmla h_fr h_proof
+ exact frame_has_unique_floats_insert_ne db pos l (fun _ => Object.assert fmla fr proof) 
+         fr.hyps h_fr_unique h_l_not_in_fr h_success_ins
```

**Sorry #5: Line 1079** (5 min)
```diff
- sorry -- Need: Use DB.find?_insert_ne to show h_find in old db
+ -- h_frames already gives us what we need for new_db!
+ exact h_frames label' fmla' fr' proof' h_find

If that fails (unlikely):
+ have h_uniq := h_frames label' fmla' fr' proof' h_find
+ unfold frame_has_unique_floats at h_uniq ⊢
+ intros i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
+ rw [DB.withFrame_find?] at h_fi h_fj  -- if withFrame lemma needed
+ exact h_uniq i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
```

### Phase 4: Validation (15 min)

```bash
# Build and check
cd /home/zar/claude/hyperon/metamath/mm-lean4
lake build Metamath.ParserProofs

# If errors, iterate on lemmas
# Common issues:
#   - Type mismatches in find?_insert_self_assert
#   - Simp lemma ordering
#   - withFrame handling in sorry #5

# Success indicators:
#   - No compilation errors
#   - All sorries eliminated
#   - No new axioms beyond HashMap
```

## Dependency Graph

```
KernelExtras.HashMap.find?_insert_self (AXIOM)
           ↓
DB.find?_insert_self_hyp (line 181, PROVEN)
           ↓
DB.find?_insert_self_assert (NEW LEMMA 1)
           ↓
insertTheorem sorry #4 ────────┐
                               ├──→ insertTheorem COMPLETE
DB.find?_insert_ne (line 250)  │
           ↓                   │
frame_has_unique_floats_insert_ne (line 842) ──┘
           ↓
insertTheorem sorry #3, #4

insert_const_var_maintains_uniqueness (line 688)
           ↓
h_inv_after (line 1039)
           ↓
insertTheorem sorry #5 ────────┘

Preconditions (NEW) ──→ insertTheorem sorry #1, #2
```

## Checklist

- [ ] Phase 1.1: Add `DB.find?_insert_self_assert`
- [ ] Phase 1.2: Add success extraction lemma OR restructure proof
- [ ] Phase 1.3: Add withFrame lemma (if needed for sorry #5)
- [ ] Phase 2.1: Modify `DBOp.insertTheorem` constructor
- [ ] Phase 3.1: Fill sorry #1 with `h_fr_unique`
- [ ] Phase 3.2: Fill sorry #2 with `h_fresh`
- [ ] Phase 3.3: Fill sorry #3 with success lemma
- [ ] Phase 3.4: Fill sorry #4 with `find?_insert_self_assert`
- [ ] Phase 3.5: Fill sorry #5 with direct application
- [ ] Phase 4: Build and validate

## Expected Outcome

```lean
theorem DBOp.preserves_invariant (op : DBOp) (db : DB)
  (h_inv : db_has_unique_floats db)
  (h_no_err : db.error? = none) :
  db_has_unique_floats (op.apply db) ∨ (op.apply db).error? ≠ none := by
  cases op with
  | ...
  | insertTheorem pos l fmla fr proof h_fr_unique h_fresh =>
      -- NO SORRIES - COMPLETE PROOF
      <proof using preconditions and new lemmas>
```

**Result**: Full proof of parser correctness for float uniqueness invariant!

## Notes

- **No axioms needed** beyond existing HashMap sorries
- **Preconditions are justified** by real parser behavior
- **Total time: 1.5-2 hours** for careful implementation
- **Alternative**: Accept 2 axioms if preconditions undesirable (30 min)

See `INSERTTHEOREM_ANALYSIS.md` for detailed rationale.
See `INSERTTHEOREM_SUMMARY.md` for quick reference.
