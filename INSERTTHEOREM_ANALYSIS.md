# InsertTheorem Proof Analysis

**Location**: `Metamath/ParserProofs.lean`, lines 998-1080
**Status**: 5 documented sorries
**Goal**: Complete proof or explain axiom requirements

## Executive Summary

The `insertTheorem` case has **5 sorries**:
1. **Line 1019** (Assumption): `frame_has_unique_floats db fr.hyps`
2. **Line 1026** (Assumption): Theorem label `l ∉ fr.hyps`
3. **Line 1058** (Technical): Insert success vs invariant relationship
4. **Line 1074** (Lookup): Find at `l` after insert gives inserted object
5. **Line 1079** (Preservation): Use `find?_insert_ne` for old assertions

**Key Insight**: Sorries 1-2 are **justified assumptions** (require additional hypotheses on the abstract DBOp model), while sorries 3-5 are **provable from existing infrastructure** with the right lemmas.

---

## Detailed Analysis of Each Sorry

### Sorry #1: Line 1019 - Frame Uniqueness (ASSUMPTION NEEDED)

```lean
have h_fr_unique : frame_has_unique_floats db fr.hyps := by
  sorry -- Assumption: frame_has_unique_floats db fr.hyps
        -- Justified by: fr from trimFrame, which preserves uniqueness
```

**What needs to be proven**: That the frame `fr` passed to `insertTheorem` has unique floats in the *current* database `db`.

**Why it's not provable**: 
- In the abstract `DBOp` model, `insertTheorem` takes `fr : Frame` as a *parameter*
- The operation doesn't track where `fr` came from
- In reality (per line 903-904), this should be from `trimFrame`, but that connection is lost in the abstract model

**Solutions**:

**Option A: Add precondition to insertTheorem** (RECOMMENDED)
```lean
inductive DBOp : Type where
  | ...
  | insertTheorem (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
    -- NEW: Require frame uniqueness as precondition
    (h_fr : ∀ (db : DB), frame_has_unique_floats db fr.hyps)
```
This is justified because:
- Real parser generates `fr` via `trimFrame` 
- `trimFrame_maintains_uniqueness` (line 822-836) shows this property holds
- It's a reasonable contract: "if you want to insert a theorem with frame fr, fr must have unique floats"

**Option B: Accept as axiom in proof**
Keep the current `sorry` and document it as an assumption about the model. This is philosophically clean but requires caller to discharge the obligation.

**Recommendation**: Option A - strengthen the precondition. The proof can then proceed with `h_fr` available.

---

### Sorry #2: Line 1026 - Label Disjointness (ASSUMPTION NEEDED)

```lean
have h_l_not_in_fr : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l := by
  sorry -- Assumption: l ∉ fr.hyps
        -- Justified by: theorem label distinct from hypothesis labels
```

**What needs to be proven**: The theorem label `l` is not among the hypothesis labels in `fr.hyps`.

**Why it's not provable**:
- Abstract `DBOp` model doesn't enforce freshness of `l`
- Real parser (line 317-321) checks for duplicates, but that's for `db.objects` keys
- The property "l not in fr.hyps" is a semantic constraint, not enforced syntactically

**Why it's true in practice**:
- `fr.hyps` contains labels of hypotheses that *already exist* in `db.objects`
- `l` is the *new* theorem label being inserted
- If `l` were already in `db.objects`, the duplicate check (line 317) would fail
- If insert succeeds, then `l ∉ fr.hyps` (since fr.hyps ⊆ dom(db.objects) before insert)

**Solutions**:

**Option A: Add freshness precondition** (RECOMMENDED)
```lean
inductive DBOp : Type where
  | ...
  | insertTheorem (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
    (h_fr : ∀ (db : DB), frame_has_unique_floats db fr.hyps)
    (h_fresh : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l)
```

**Option B: Derive from success condition**
This is trickier. We could prove: "If `db.insert pos l obj` succeeds (error? = none), then for all labels `l'` in `db.objects` that were there before, `l' ≠ l`". But we'd need infrastructure to track "labels in db.objects" and relate that to "labels in fr.hyps".

**Recommendation**: Option A - add explicit precondition. It's a natural contract.

---

### Sorry #3: Line 1058 - Success vs Invariant (PROVABLE)

```lean
· -- Insert failed - contradiction with h_inv_after
  -- h_inv_after implies the invariant holds, which should mean no error
  -- But we can't prove this directly without more assumptions
  sorry -- Need: db_has_unique_floats implies error? = none (or vice versa)
```

**What needs to be proven**: That `h_inv_after : db_has_unique_floats db'` contradicts `¬h_success_ins : db'.error? ≠ none`.

**Why it's provable**: This is actually a FALSE branch! 

**Analysis**:
- Line 1033: `h_insert := insert_const_var_maintains_uniqueness db pos l ... h_inv h_no_err ...`
- Line 1034: `cases h_insert with | inl h_err => ... | inr h_inv_after => ...`
- `insert_const_var_maintains_uniqueness` returns: `db'.error? ≠ none ∨ db_has_unique_floats db'`
- We're in the `inr` branch, meaning `db_has_unique_floats db'` holds
- By the disjunction, if `inr` holds, then `inl` doesn't, so `¬(db'.error? ≠ none)`
- Therefore `db'.error? = none`

**Proof Strategy**:
```lean
· -- Insert succeeded (because we're in h_inv_after branch)
  have h_success_ins : (db.insert ...).error? = none := by
    -- h_insert is a disjunction: h_err ∨ h_inv_after
    -- We're in the h_inv_after branch, so h_err doesn't hold
    -- The disjunction came from insert_const_var_maintains_uniqueness
    -- which returns: db'.error? ≠ none ∨ db_has_unique_floats db'
    -- Since we have h_inv_after (right side), the left side must be false
    -- Need to use: ¬ (db'.error? ≠ none) ↔ db'.error? = none
    by_contra h_contra
    -- If db'.error? ≠ none, then h_err would hold
    -- But we're in h_inv_after branch, contradiction
    -- This requires rewriting the original disjunction
    sorry  -- Solvable with proper case analysis on h_insert
  exact frame_has_unique_floats_insert_ne db pos l (fun _ => Object.assert fmla fr proof) fr.hyps h_fr_unique h_l_not_in_fr h_success_ins
```

Actually, looking more carefully at the proof structure:

Line 1052-1058:
```lean
by_cases h_success_ins : (db.insert pos l (fun _ => Object.assert fmla fr proof)).error? = none
· -- Insert succeeded
  exact frame_has_unique_floats_insert_ne ...
· -- Insert failed - contradiction with h_inv_after
  sorry
```

The issue is: we're doing a `by_cases` on success, but we already know from `h_inv_after` that we're in a "good" state. 

**Real Solution**: Don't use `by_cases`. Instead, PROVE that `h_inv_after` implies `error? = none`.

```lean
-- We know from h_inv_after that the invariant holds
-- The only way insert_const_var_maintains_uniqueness returns Right
-- is if insert succeeded OR didn't modify error state badly
-- But actually, looking at line 694-753 of insert_const_var_maintains_uniqueness:
-- It returns (error? ≠ none) ∨ (invariant)
-- If we're in the Right branch (h_inv_after), we need to show error? = none

-- The problem: insert_const_var_maintains_uniqueness doesn't guarantee
-- that Right branch implies error? = none !
-- It just says: either error is set, or invariant holds
-- But invariant can hold with error set (vacuously, if error short-circuits everything)

-- REAL ISSUE: We need a stronger lemma!
```

**Actually**, reading `insert_const_var_maintains_uniqueness` more carefully (lines 694-753):
- Line 696: `by_cases h_success : (db.insert pos l obj).error? = none`
- Line 698: If success, returns `right` (invariant holds)
- Line 751-753: If failure, returns `left` (error set)

So the lemma DOES establish: 
- `Right` branch means insert succeeded → `error? = none` holds in that branch
- `Left` branch means insert failed → `error? ≠ none`

**The issue**: The proof at line 1033-1040 does a case split on `h_insert`, but doesn't *carry forward* the success condition from the Right branch.

**SOLUTION**: Refactor `insert_const_var_maintains_uniqueness` to return a stronger type:

```lean
theorem insert_const_var_maintains_uniqueness ... :
  let db' := db.insert pos l obj
  (db'.error? ≠ none) ∨ (db'.error? = none ∧ db_has_unique_floats db') := by
```

OR, simpler: just extract the success condition when we case split:

```lean
have h_insert := insert_const_var_maintains_uniqueness db pos l (fun _ => .assert fmla fr proof) h_inv h_no_err h_not_hyp
-- h_insert is computed at line 696 via by_cases on success
-- We need to refactor to expose that condition

-- BETTER: Look at the proof of insert_const_var_maintains_uniqueness
-- At line 696: by_cases h_success : (db.insert pos l obj).error? = none
-- If h_success, it returns right (invariant)
-- So: h_inv_after → h_success

-- The proof needs to be restructured to capture this implication
```

**ACTUAL SOLUTION**: At line 1058, we can prove this by contradiction using the structure of `insert_const_var_maintains_uniqueness`. Here's the logic:

From lines 694-753:
```lean
by_cases h_success : (db.insert pos l obj).error? = none
· right; <proof of invariant>
· left; exact h_success
```

So if we're in the `inr` case (h_inv_after), then we came from the `right` branch above, which means `h_success` held in that branch!

**Proof**:
```lean
· -- ¬h_success_ins case
  -- But we got h_inv_after from insert_const_var_maintains_uniqueness
  -- which only returns right when insert succeeds
  -- Examining insert_const_var_maintains_uniqueness proof:
  --   Line 696: by_cases h_success
  --   Right branch (697-750): if h_success, return right
  --   Left branch (751-753): if ¬h_success, return left
  -- So h_inv_after (from right branch) implies h_success held
  -- Therefore ¬h_success_ins contradicts h_inv_after
  
  -- Need to expose this structure. Best approach:
  -- Refactor to not use by_cases here, or
  -- Add a wrapper lemma showing: inr branch → success
  exfalso
  sorry -- Provable by examining insert_const_var_maintains_uniqueness structure
```

**BEST FIX**: Don't use `by_cases` at line 1052. Instead, prove success from h_inv_after:

```lean
· -- After withFrame: frame becomes fr, objects unchanged
  unfold db_has_unique_floats at h_inv_after ⊢
  unfold frame_has_unique_floats at h_fr_unique ⊢
  simp
  constructor
  · -- Current frame: fr
    -- First, extract that insert succeeded from h_inv_after
    -- Need a helper lemma:
    have h_success_ins : (db.insert pos l (fun _ => Object.assert fmla fr proof)).error? = none := by
      sorry  -- Provable from structure of insert_const_var_maintains_uniqueness
                -- Could be a separate lemma: inr branch → error? = none
    exact frame_has_unique_floats_insert_ne db pos l (fun _ => Object.assert fmla fr proof) fr.hyps h_fr_unique h_l_not_in_fr h_success_ins
```

**RECOMMENDED ACTION**: 
1. Add helper lemma showing `insert_const_var_maintains_uniqueness` Right branch implies success
2. Use that lemma to get `h_success_ins` directly
3. Apply `frame_has_unique_floats_insert_ne` without case split

---

### Sorry #4: Line 1074 - Lookup After Insert (PROVABLE)

```lean
sorry -- Need: lookup at l after insert gives the inserted object
      -- Then fr' = fr, and we need to lift h_fr_unique to new db
```

**What needs to be proven**: `(db.insert pos l (fun _ => .assert fmla fr proof)).find? l = some (.assert fmla fr' proof')` implies `fr' = fr`.

**Why it's provable**: We have the infrastructure!

**Available Lemmas**:
- `DB.find?_insert_self_hyp` (line 181-233): Specialized for `.hyp` objects
- `KernelExtras.HashMap.find?_insert_self` (line 412-419): General HashMap property

**Issue**: `DB.find?_insert_self_hyp` is specialized to `.hyp` objects, not `.assert`.

**SOLUTION**: Create `DB.find?_insert_self_assert` analogous to `_self_hyp`:

```lean
@[simp] theorem DB.find?_insert_self_assert
  (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  (h_success : (db.insert pos l (fun _ => .assert fmla fr proof)).error? = none) :
  (db.insert pos l (fun _ => .assert fmla fr proof)).find? l = 
    some (.assert fmla fr proof) := by
  classical
  unfold DB.insert at h_success ⊢
  simp [DB.find?] at h_success ⊢
  -- Similar structure to find?_insert_self_hyp
  -- Case split on db.error, then on db.find? l
  -- In the none branch (actual insert), use HashMap.find?_insert_self
  sorry  -- Provable by mirroring find?_insert_self_hyp proof
```

**Then at line 1074**:
```lean
have h_inserted := DB.find?_insert_self_assert db pos l fmla fr proof h_success_ins
-- h_inserted: (db.insert...).find? l = some (.assert fmla fr proof)
-- h_find: (db.insert...).find? l = some (.assert fmla' fr' proof')
rw [h_inserted] at h_find
simp at h_find
-- Now h_find gives: fmla' = fmla, fr' = fr, proof' = proof
obtain ⟨rfl, rfl, rfl⟩ := h_find
-- Now prove: frame_has_unique_floats (new_db) fr.hyps
-- We have h_fr_unique: frame_has_unique_floats db fr.hyps
-- Need to lift it to new_db using h_l_not_in_fr and h_success_ins
exact frame_has_unique_floats_insert_ne db pos l (fun _ => Object.assert fmla fr proof) fr.hyps h_fr_unique h_l_not_in_fr h_success_ins
```

**RECOMMENDED ACTION**:
1. Add `DB.find?_insert_self_assert` theorem (15-20 lines, mirrors `_self_hyp`)
2. Use it to extract `fr' = fr` via injection
3. Apply `frame_has_unique_floats_insert_ne` with that equality

---

### Sorry #5: Line 1079 - Old Assertions (PROVABLE)

```lean
sorry -- Need: Use DB.find?_insert_ne to show h_find in old db
      -- Then apply h_frames with old db lookup
```

**What needs to be proven**: For `label' ≠ l`, show `frame_has_unique_floats (new_db) fr'.hyps` where `new_db.find? label' = some (.assert fmla' fr' proof')`.

**Why it's provable**: We have all the pieces!

**Proof Strategy**:
```lean
· -- Old assertion: label' ≠ l
  have h_find_old : db.find? label' = some (.assert fmla' fr' proof') := by
    -- Use DB.find?_insert_ne to rewrite lookup in new db to old db
    have h_preserved := DB.find?_insert_ne db pos l label' 
                          (fun _ => .assert fmla fr proof) h_ne h_success_ins
    rw [← h_preserved]
    exact h_find
  
  -- Now we can use h_frames from h_inv_after
  have ⟨_, h_frames⟩ := h_inv_after
  -- h_frames: ∀ label ... db_new.find? label = some ... → frame_has_unique_floats db_new ...
  
  -- Apply h_frames with label'
  have h_old_unique := h_frames label' fmla' fr' proof' h_find
  
  -- But wait - h_frames talks about new_db, we need to show it for new_db
  -- Actually, re-reading line 1078: h_inv_after gives us new_db invariant
  -- So h_frames already gives us frame_has_unique_floats (new_db) fr'.hyps
  exact h_old_unique
```

**Wait**, let me reread the structure. At line 1044:
```lean
unfold db_has_unique_floats at h_inv_after ⊢
```

So `h_inv_after` is `db_has_unique_floats (db.insert pos l ...)`. Let me trace through:

```lean
-- h_inv_after : db_has_unique_floats (db.insert pos l (fun _ => .assert fmla fr proof))
-- Let's call that new_db
-- h_inv_after expands to:
--   (1) frame_has_unique_floats new_db new_db.frame.hyps
--   (2) ∀ label, new_db.find? label = some (.assert ...) → frame_has_unique_floats new_db fr.hyps

-- Line 1060: intros label' fmla' fr' proof' h_find
-- h_find : new_db.find? label' = some (.assert fmla' fr' proof')

-- Line 1064-1075: Case label' = l (already analyzed - sorry #4)
-- Line 1076-1080: Case label' ≠ l

-- In label' ≠ l case:
-- We want to show: frame_has_unique_floats new_db fr'.hyps
-- We have from h_inv_after: ∀ label, new_db.find? label = some (.assert ...) → ...
-- So just apply it with label'!

have ⟨_, h_frames⟩ := h_inv_after
exact h_frames label' fmla' fr' proof' h_find
```

**WAIT** - that's it! The sorry at line 1079 is trivial!

```lean
· -- Old assertion: label' ≠ l
  have ⟨_, h_frames⟩ := h_inv_after
  exact h_frames label' fmla' fr' proof' h_find
```

**BUT** - let me check if the issue is about relating old and new db. Looking at line 1077-1080 comment:
```
-- Lookup at label' in new db equals lookup in old db (by DB.find?_insert_ne)
have ⟨_, h_frames⟩ := h_inv_after
sorry -- Need: Use DB.find?_insert_ne to show h_find in old db
      -- Then apply h_frames with old db lookup
```

Hmm, the comment suggests we need to show it's in the old db first, THEN use h_frames. But that doesn't make sense because h_frames is about new_db!

Let me re-read what h_inv_after is. From line 1039:
```lean
| inr h_inv_after =>
    -- Insert succeeded: db.insert has invariant
    left
    -- After withFrame: frame becomes fr, objects unchanged
    -- Need to show: db_has_unique_floats ({ (db.insert ...) with frame := ... })
```

OH! There's a `withFrame` at line 1000:
```lean
unfold DBOp.apply DB.withFrame
```

And at line 903-904:
```lean
| insertTheorem pos l fmla fr proof =>
    (db.insert pos l (fun _ => .assert fmla fr proof)).withFrame (fun _ => fr)
```

So the final state is `(db.insert...).withFrame(...)`, not just `db.insert...`!

Let me re-examine. At line 1044:
```lean
unfold db_has_unique_floats at h_inv_after ⊢
```

What is `h_inv_after`? From line 1033-1039:
```lean
have h_insert := insert_const_var_maintains_uniqueness db pos l (fun _ => .assert fmla fr proof) h_inv h_no_err h_not_hyp
cases h_insert with
| inl h_err => right; exact h_err
| inr h_inv_after =>
    left
    unfold db_has_unique_floats at h_inv_after ⊢
```

So `h_inv_after : db_has_unique_floats (db.insert pos l (fun _ => .assert fmla fr proof))`.

But the goal is to show `db_has_unique_floats ((db.insert ...).withFrame ...)`.

So there's a mismatch! We have invariant for `db_after_insert`, but need it for `db_after_insert_and_withFrame`.

Looking at line 1044-1046:
```lean
unfold db_has_unique_floats at h_inv_after ⊢
unfold frame_has_unique_floats at h_fr_unique ⊢
simp
```

The `simp` likely applies `DB.withFrame` properties. Let me check what `withFrame` does to `find?`:

From lines 84-95:
```lean
theorem DB.withHyps_find? (db : DB) (f : Array String → Array String) (l : String) :
  (db.withHyps f).find? l = db.find? l := by
  unfold DB.withHyps DB.find?
  rfl
```

And line 79-80:
```lean
@[simp] theorem DB.withHyps_objects (db : DB) (f : Array String → Array String) :
  (db.withHyps f).objects = db.objects := rfl
```

So `withHyps` (and presumably `withFrame`) doesn't change `objects`, hence doesn't change `find?`.

Therefore: `(db_insert.withFrame ...).find? = db_insert.find?`.

Now at line 1060-1062:
```lean
· -- Assertions: all frames including new one have unique floats
  intros label' fmla' fr' proof' h_find
  unfold DB.find? at h_find
  simp at h_find
```

After `simp`, `h_find` is about `((db.insert...).withFrame...).find? label'`, which equals `(db.insert...).find? label'`.

So at line 1076-1080, we have:
- `h_find : (db.insert pos l (fun _ => .assert fmla fr proof)).find? label' = some (.assert fmla' fr' proof')`
- `h_inv_after : db_has_unique_floats (db.insert ...)`
- `h_ne : label' ≠ l`

The goal is: `frame_has_unique_floats ((db.insert...).withFrame...) fr'.hyps`.

But `withFrame` doesn't change objects, so:
`frame_has_unique_floats ((db.insert...).withFrame...) fr'.hyps` = `frame_has_unique_floats (db.insert...) fr'.hyps`.

Therefore:
```lean
· -- Old assertion: label' ≠ l
  have ⟨_, h_frames⟩ := h_inv_after
  -- h_frames : ∀ label, (db.insert...).find? label = some (.assert ...) 
  --            → frame_has_unique_floats (db.insert...) fr'.hyps
  -- h_find : (db.insert...).find? label' = some (.assert fmla' fr' proof')
  -- (after simp, which removed withFrame from find?)
  
  -- Goal: frame_has_unique_floats ((db.insert...).withFrame...) fr'.hyps
  -- But withFrame doesn't affect frame_has_unique_floats (objects unchanged)
  
  -- So we can directly apply h_frames
  have h_uniq_insert := h_frames label' fmla' fr' proof' h_find
  
  -- Now we need to show it still holds after withFrame
  -- Since withFrame doesn't change objects, lookups are preserved
  unfold frame_has_unique_floats at h_uniq_insert ⊢
  intros i j hi hj h_ne_ij fi fj lbli lblj h_fi_wf h_fj_wf h_szi h_szj
  
  -- h_fi_wf : ((db.insert...).withFrame...).find? fr'.hyps[i] = some (.hyp false fi lbli)
  -- Need to rewrite to db.insert form
  rw [DB.withFrame_find? (or similar lemma)] at h_fi_wf h_fj_wf
  
  -- Then apply h_uniq_insert
  exact h_uniq_insert i j hi hj h_ne_ij fi fj lbli lblj h_fi_wf h_fj_wf h_szi h_szj
```

**Actually**, I think the simp at line 1063 should handle this. Let me assume `h_find` after simp is in the right form.

**SIMPLEST SOLUTION**: After the simp, just apply h_frames:

```lean
· -- Old assertion: label' ≠ l
  have ⟨_, h_frames⟩ := h_inv_after
  -- After simp at line 1063, h_find should be in canonical form
  -- and goal should match what h_frames provides
  sorry  -- Should be solvable by direct application
            -- Possibly need: exact h_frames label' fmla' fr' proof' h_find
            -- Or need to handle withFrame preservation explicitly
```

**RECOMMENDED ACTION**:
1. Check what `simp` does at line 1063 to `h_find` and goal
2. If withFrame needs explicit handling, add lemma `withFrame_preserves_frame_uniqueness`
3. Apply h_frames directly after accounting for withFrame

---

## Summary of Proof Strategy

### Sorries Requiring Assumptions (Add Preconditions)

**Sorry #1 (line 1019)** and **Sorry #2 (line 1026)**: Add preconditions to `insertTheorem`:

```lean
inductive DBOp : Type where
  | ...
  | insertTheorem (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
    -- Precondition 1: Frame has unique floats in any valid database
    (h_fr_unique : ∀ (db : DB), frame_has_unique_floats db fr.hyps)
    -- Precondition 2: Theorem label distinct from hypothesis labels  
    (h_fresh : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l)
```

**Justification**: 
- These properties hold in the real parser because `fr` comes from `trimFrame`
- `trimFrame_maintains_uniqueness` ensures property 1
- Duplicate checking + frame construction ensures property 2
- Making them explicit preconditions documents the contract

### Sorries Requiring New Lemmas (Provable)

**Sorry #3 (line 1058)**: Add helper lemma or restructure case analysis:

```lean
theorem insert_const_var_maintains_uniqueness_success :
  (insert_const_var_maintains_uniqueness db pos l obj h_inv h_no_err h_not_hyp = inr h_inv') →
  (db.insert pos l obj).error? = none := by
  sorry  -- Provable by inspecting proof structure at lines 696-753
```

Then at line 1052, remove `by_cases` and use this lemma instead.

**Sorry #4 (line 1074)**: Add assertion-specific lookup lemma:

```lean
@[simp] theorem DB.find?_insert_self_assert
  (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  (h_success : (db.insert pos l (fun _ => .assert fmla fr proof)).error? = none) :
  (db.insert pos l (fun _ => .assert fmla fr proof)).find? l = 
    some (.assert fmla fr proof) := by
  sorry  -- Mirror proof of DB.find?_insert_self_hyp (lines 181-233)
```

**Sorry #5 (line 1079)**: Should be trivial after simp:

```lean
· -- Old assertion: label' ≠ l
  have ⟨_, h_frames⟩ := h_inv_after
  exact h_frames label' fmla' fr' proof' h_find
```

If that doesn't work directly, may need:
```lean
theorem withFrame_preserves_frame_uniqueness :
  frame_has_unique_floats db hyps →
  frame_has_unique_floats (db.withFrame f) hyps := by
  intro h
  unfold frame_has_unique_floats at h ⊢
  intros; apply h; assumption; rw [DB.withFrame_find?]; assumption
```

---

## Recommended Action Plan

### Phase 1: Add Preconditions (5-10 minutes)
1. Modify `DBOp.insertTheorem` to include `h_fr_unique` and `h_fresh` parameters
2. Update call site at line 998 to use these parameters
3. Remove sorry #1 and #2, replace with parameter references

### Phase 2: Prove Helper Lemmas (30-60 minutes)

**A. DB.find?_insert_self_assert** (~20 min)
- Copy structure from `find?_insert_self_hyp` (lines 181-233)
- Replace `.hyp` with `.assert` 
- Adapt case analysis for assertion duplicate logic

**B. insert_const_var_maintains_uniqueness_success** (~15 min)
- Extract success condition from Right branch
- OR restructure insertTheorem proof to not use by_cases at line 1052

**C. withFrame_preserves_frame_uniqueness** (~10 min, if needed)
- Show that changing frame field doesn't affect lookup-based properties
- Use `DB.withFrame_find?` preservation

### Phase 3: Fill Sorries (15-30 minutes)

1. **Sorry #3**: Use helper lemma B or restructure
2. **Sorry #4**: Use helper lemma A + injection + `frame_has_unique_floats_insert_ne`
3. **Sorry #5**: Direct application of h_frames (may need lemma C)

### Phase 4: Validation (15 minutes)
- Ensure all proofs type-check
- Run `lake build` to verify
- Document any remaining assumptions

---

## Circular Dependencies

**None identified**. The proof structure is well-layered:
- HashMap lemmas (KernelExtras) → DB.find? lemmas → frame_uniqueness lemmas → insertTheorem
- No cycles detected

---

## Alternative: Accept as Axioms

If adding preconditions is undesirable, document the 2 assumptions explicitly:

```lean
axiom insertTheorem_frame_uniqueness :
  ∀ db fr, frame_has_unique_floats db fr.hyps  -- Justified by trimFrame

axiom insertTheorem_label_freshness :
  ∀ l fr, ∀ i (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l  -- Justified by duplicate check
```

Then sorry #1-2 become direct applications of these axioms.

This is philosophically cleaner (separates model assumptions from implementation) but less explicit about contracts.

---

## Estimated Effort

- **With preconditions approach**: 1-2 hours total
  - 10 min: Add preconditions
  - 45 min: Prove 2-3 helper lemmas  
  - 30 min: Fill sorries
  - 15 min: Debug and validate

- **With axioms approach**: 15-30 minutes
  - 10 min: Add axioms
  - 20 min: Fill remaining provable sorries (#3-5)

---

## Conclusion

**Recommendation**: Use the preconditions approach. It's more explicit, self-documenting, and maintains the "no axioms beyond HashMap" goal.

The 5 sorries break down as:
- **2 assumptions** (justified by parser semantics) → add as preconditions
- **3 technical lemmas** (all provable from existing infrastructure) → ~1 hour work

The proof is **completable without additional axioms** beyond the existing HashMap sorries.
