# Cascading Sorry Completion Plan

**Goal:** Complete all 32 sorries in `Kernel.lean` in dependency order, building on Oruži's proven foundation.

**Total Estimated Time:** 132 hours (3.3 weeks full-time)

## Phase 0: Foundation Setup (4-6 hours)

### Task 0.1: Integrate Oruži's KernelExtras Proofs (2 hours)
**File:** `Metamath/KernelExtras.lean`

**Action:**
```lean
-- Add at top of KernelExtras.lean
namespace Metamath.KernelExtras

private def mapMOption {α β} (f : α → Option β) : List α → Option (List β)
  | []      => some []
  | a :: xs =>
    match f a with
    | some b => match mapMOption f xs with
                | some ys => some (b :: ys)
                | none => none
    | none => none

private theorem mapMOption_length {α β} (f : α → Option β) :
    ∀ xs ys, mapMOption f xs = some ys → ys.length = xs.length
  | [],      ys, h => by cases h; rfl
  | a :: xs, ys, h => by
      simp [mapMOption] at h
      split at h <;> try contradiction
      next b hb =>
        split at h <;> try contradiction
        next ys' hys =>
          cases h
          simp [mapMOption_length xs ys' hys]

-- (Add remaining 5 theorems from Oruži's submission)
```

**Replace axioms:**
```lean
theorem List.mapM_length_option {α β} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length :=
  -- Use mapMOption_length with conversion

-- (Replace all 6 axioms)
```

**Test:** `lake build Metamath.KernelExtras` (should compile!)

**Dependencies:** None (foundational)

---

### Task 0.2: Add Missing MapM Helper Lemmas (2-4 hours)
**File:** `Metamath/KernelExtras.lean` (append to end)

**Add these 3 lemmas using mapMOption:**

```lean
/-- MapM preserves append structure -/
theorem list_mapM_append {α β} (f : α → Option β) (xs ys : List α) :
    (xs ++ ys).mapM f = do
      let xs' ← xs.mapM f
      let ys' ← ys.mapM f
      pure (xs' ++ ys') := by
  -- Proof via mapMOption
  induction xs with
  | nil => simp [mapMOption]
  | cons a xs ih =>
    simp [mapMOption, ih]
    -- Case split on f a and mapMOption xs/ys
    sorry  -- ~15 lines

/-- MapM preserves dropLast -/
theorem list_mapM_dropLast_of_mapM_some {α β} (f : α → Option β)
    (xs : List α) (ys : List β) (n : Nat) :
    xs.mapM f = some ys →
    (xs.dropLast n).mapM f = some (ys.dropLast n) := by
  -- Via mapMOption + List.dropLast properties
  intro h
  sorry  -- ~20 lines

/-- MapM preserves get indexing -/
theorem mapM_get_some {α β} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys →
    ∀ i : Fin xs.length, ∃ y, f xs[i] = some y ∧ ys[i] = y := by
  -- Via mapMOption induction
  intro h i
  sorry  -- ~25 lines
```

**Test:** `lake build Metamath.KernelExtras` (should still compile!)

**Dependencies:** Task 0.1 (uses mapMOption)

---

## Phase 1: HashMap & Array Foundation (20-25 hours)

### Task 1.1: Complete HashMap Helper Lemmas (8-10 hours)
**File:** `Metamath/Kernel.lean`, lines ~1420-1450

**Target sorries:** None yet (these are used by later sorries)

**Lemmas to complete:**
```lean
theorem HashMap.getElem?_insert_self {α β} [BEq α] [Hashable α] [LawfulBEq α]
    (m : HashMap α β) (k : α) (v : β) :
    (m.insert k v)[k]? = some v := by
  sorry  -- ~5 lines: HashMap insert spec

theorem HashMap.getElem?_insert_of_ne {α β} [BEq α] [Hashable α] [LawfulBEq α]
    (m : HashMap α β) (k k' : α) (v : β) (h : k ≠ k') :
    (m.insert k v)[k']? = m[k']? := by
  sorry  -- ~5 lines: HashMap insert disjoint case

-- Line 1825: For checkHyp_produces_typed_coverage
theorem HashMap.contains_eq_isSome {α β} [BEq α] [Hashable α]
    (m : HashMap α β) (k : α) :
    m.contains k = true ↔ m[k]?.isSome := by
  sorry  -- ~8 lines: HashMap contains spec
```

**Estimate:** 8-10 hours (depends on Batteries HashMap API)

**Dependencies:** None (uses Batteries HashMap lemmas)

---

### Task 1.2: Array Operation Proofs (12-15 hours)
**File:** `Metamath/Kernel.lean`, lines 2491-2503

**Target sorries:** 4 sorries in proof step handling

**Context:** These are in `stepProof_correct` and use Array indexing.

**Strategy:**
1. Use `Array.mem_toList_get` (now proven by Oruži!)
2. Use `Array.getBang_eq_get` (now proven by Oruži!)
3. Case analysis on proof step type

**Example (line 2491):**
```lean
-- Line 2491: const/var case
| const c, _ | var v, _ =>
  simp [stepProof, stepNormal]
  -- Now we can use mem_toList_get and getBang_eq_get!
  sorry  -- ~10 lines: show heap lookup correct
```

**Estimate:** 12-15 hours (4 related sorries)

**Dependencies:**
- Task 0.1 (Array lemmas proven)
- Task 1.1 (HashMap lemmas for substitution cases)

---

## Phase 2: CheckHyp Infrastructure (35-45 hours)

### Task 2.1: FloatBindWitness Properties (5-7 hours)
**File:** `Metamath/Kernel.lean`, line 1840

**Target sorry:** `toExpr_typecode_from_FloatBindWitness`

**Lemma:**
```lean
theorem toExpr_typecode_from_FloatBindWitness
    (witness : FloatBindWitness db hyps stack off i varname val)
    (e : Metamath.Spec.Expr) :
    toExprOpt val = some e →
    e.typecode.c = witness.f[0]!.value := by
  intro h_toExpr
  -- FloatBindWitness has: witness.typecode_eq : f[0]! == val[0]! = true
  -- toExprOpt val = some e means e.typecode = val[0]
  -- Combine to get e.typecode.c = f[0]!.value
  sorry  -- ~15-20 lines
```

**Estimate:** 5-7 hours

**Dependencies:** None (uses FloatBindWitness structure)

---

### Task 2.2: toFrame Preservation (10-12 hours)
**File:** `Metamath/Kernel.lean`, line 1813

**Target sorry:** `toFrame_preserves_floats` lemma

**Lemma:**
```lean
theorem toFrame_preserves_floats
    (db : Metamath.Verify.DB)
    (fr_impl : Frame)
    (fr_spec : Metamath.Spec.Frame) :
    toFrame db fr_impl = some fr_spec →
    ∀ c v, Hyp.floating c v ∈ fr_spec.mand →
    ∃ label ∈ fr_impl.hyps.toList, ∃ f_hyp,
      db.find? label = some (.hyp false f_hyp _) ∧
      f_hyp[1]!.value = v.v ∧
      f_hyp[0]!.value = c.c := by
  intro h_toFrame c v h_float
  -- Unfold toFrame definition
  -- Show it maps floating hyps bijectively
  sorry  -- ~30-40 lines
```

**Estimate:** 10-12 hours (requires understanding toFrame impl)

**Dependencies:** None (structural proof)

---

### Task 2.3: Complete checkHyp_produces_typed_coverage (8-10 hours)
**File:** `Metamath/Kernel.lean`, line 1813

**Target sorry:** Main theorem body (3 sub-sorries)

**Strategy:**
1. Use Task 2.2 (toFrame_preserves_floats) - now proven!
2. Use Task 1.1 (HashMap.contains_eq_isSome) - now proven!
3. Use Task 2.1 (toExpr_typecode_from_FloatBindWitness) - now proven!

**Current state:**
```lean
theorem checkHyp_produces_typed_coverage ... := by
  intro h_check h_stack h_frame c v h_float

  have h_label : ∃ label ∈ hyps.toList, ... := by
    sorry  -- NOW: Use toFrame_preserves_floats (Task 2.2)!

  have h_binding : ∃ f, σ[v.v]? = some f := by
    sorry  -- NOW: Use HashMap.contains_eq_isSome (Task 1.1)!

  have h_typecode : e.typecode = c := by
    sorry  -- NOW: Use toExpr_typecode_from_FloatBindWitness (Task 2.1)!
```

**Estimate:** 8-10 hours (combining proven pieces)

**Dependencies:**
- ✅ Task 1.1 (HashMap lemmas)
- ✅ Task 2.1 (FloatBindWitness)
- ✅ Task 2.2 (toFrame preservation)

---

### Task 2.4: Complete checkHyp_produces_TypedSubst (12-15 hours)
**File:** `Metamath/Kernel.lean`, line 1896

**Target sorry:** Integration theorem

**Strategy:**
```lean
theorem checkHyp_produces_TypedSubst ... := by
  intro h_check h_stack h_frame

  -- Use Task 2.3 (checkHyp_produces_typed_coverage)!
  unfold toSubstTyped

  -- Show the validation loop succeeds
  -- Because typed coverage guarantees all checks pass
  sorry  -- ~30-40 lines: allM reasoning
```

**Estimate:** 12-15 hours (needs careful allM unfolding)

**Dependencies:**
- ✅ Task 2.3 (checkHyp_produces_typed_coverage)

---

## Phase 3: Main Verification Theorems (40-50 hours)

### Task 3.1: ViewStack Preservation (15-18 hours)
**File:** `Metamath/Kernel.lean`, lines 3089, 3101

**Target sorries:** 2 sorries

**Strategy:**
```lean
-- Line 3089: viewStack preserves mapM
theorem viewStack_preserves_mapM ... := by
  unfold viewStack
  -- Use list_mapM_append (Task 0.2)!
  -- Use Array.toList properties
  sorry  -- ~25-30 lines

-- Line 3101: dropLast preservation
theorem some_other_viewStack_lemma ... := by
  -- Use list_mapM_dropLast_of_mapM_some (Task 0.2)!
  sorry  -- ~20-25 lines
```

**Estimate:** 15-18 hours (2 related proofs)

**Dependencies:**
- ✅ Task 0.2 (mapM append/dropLast lemmas)

---

### Task 3.2: MapM Index Preservation (10-12 hours)
**File:** `Metamath/Kernel.lean`, lines 3464, 3468

**Target sorries:** 2 sorries

**Strategy:**
```lean
-- Line 3464: mapM preserves indexing
theorem mapM_index_preservation ... := by
  -- Use mapM_get_some (Task 0.2)!
  sorry  -- ~40-60 lines

-- Line 3468: length preservation
theorem mapM_length_preservation ... := by
  -- Use list_mapM_Option_length (Task 0.1)!
  sorry  -- ~10-15 lines
```

**Estimate:** 10-12 hours

**Dependencies:**
- ✅ Task 0.1 (mapM length)
- ✅ Task 0.2 (mapM get)

---

### Task 3.3: Substitution Soundness (12-15 hours)
**File:** `Metamath/Kernel.lean`, line 206

**Target sorry:** `subst_sound` theorem

**Strategy:**
```lean
theorem subst_sound (vars : List Metamath.Spec.Variable)
    (σ_impl : Std.HashMap String Formula) (e : Formula) :
    ... := by
  -- Structural induction on Formula e
  induction e using Formula.rec with
  | var v =>
      -- Base case: HashMap lookup matches functional lookup
      -- Use Task 1.1 HashMap lemmas
      sorry  -- ~15-20 lines
  | app c args ih =>
      -- Inductive case: recursively apply substitution
      -- Use inductive hypotheses
      sorry  -- ~25-30 lines
```

**Estimate:** 12-15 hours

**Dependencies:**
- ✅ Task 1.1 (HashMap lemmas)
- Needs Formula.rec induction principle (may need to define)

---

### Task 3.4: Remaining Structural Proofs (13-15 hours)
**File:** `Metamath/Kernel.lean`, various lines

**Target sorries:**
- Line 336: `variable_wellformed` (3-4 hours)
- Line 1406: `toSubstTyped` validation (4-5 hours)
- Lines 2064, 2087: checkHyp float/essential matching (3-4 hours)
- Line 2863: ProofStateInv extraction (3-4 hours)

**Estimate:** 13-15 hours total

**Dependencies:** Various (mostly structural)

---

### Task 3.5: Final Integration Theorems (10-12 hours)
**File:** `Metamath/Kernel.lean`, lines 3607, 3715, 3748, 3756, 3805

**Target sorries:** 5 final integration sorries

**Strategy:**
- Use all previous proven lemmas
- Connect the pieces
- Final case analyses

**Estimate:** 10-12 hours (cleanup phase)

**Dependencies:**
- ✅ All previous tasks

---

## Dependency Graph

```
Phase 0 (Foundation Setup)
├─ Task 0.1: Oruži's KernelExtras ─────────────────┐
│  └─ Task 0.2: Missing MapM lemmas                │
│                                                   │
Phase 1 (HashMap & Array)                          │
├─ Task 1.1: HashMap lemmas ──────────────┐        │
├─ Task 1.2: Array operations (uses 0.1) ─┤        │
│                                          │        │
Phase 2 (CheckHyp Infrastructure)          │        │
├─ Task 2.1: FloatBindWitness              │        │
├─ Task 2.2: toFrame preservation          │        │
├─ Task 2.3: typed_coverage (uses 1.1, 2.1, 2.2)   │
├─ Task 2.4: TypedSubst (uses 2.3)         │        │
│                                          │        │
Phase 3 (Main Verification)                │        │
├─ Task 3.1: ViewStack (uses 0.2) ─────────┤        │
├─ Task 3.2: MapM index (uses 0.1, 0.2) ───┤        │
├─ Task 3.3: subst_sound (uses 1.1) ───────┤        │
├─ Task 3.4: Structural proofs (uses various)       │
└─ Task 3.5: Final integration (uses ALL) ─────────┘
```

## Execution Strategy

### Recommended Order

**Week 1 (40 hours):**
1. ✅ Task 0.1: Integrate Oruži's proofs (2h)
2. ✅ Task 0.2: Add missing mapM lemmas (4h)
3. ✅ Task 1.1: HashMap lemmas (10h)
4. ✅ Task 1.2: Array operations (15h)
5. ✅ Task 2.1: FloatBindWitness (7h)

**Week 2 (42 hours):**
6. ✅ Task 2.2: toFrame preservation (12h)
7. ✅ Task 2.3: typed_coverage (10h)
8. ✅ Task 2.4: TypedSubst (15h)
9. ✅ Task 3.4: Some structural proofs (5h)

**Week 3 (40 hours):**
10. ✅ Task 3.1: ViewStack (18h)
11. ✅ Task 3.2: MapM index (12h)
12. ✅ Task 3.4: Remaining structural (10h)

**Week 4 (10 hours):**
13. ✅ Task 3.3: subst_sound (15h - overflow from week 3)
14. ✅ Task 3.5: Final integration (12h)
15. ✅ Testing & cleanup (5h)

**Total:** 132 hours = 3.3 weeks full-time

## Risk Assessment

### Low Risk (High Confidence)
- Tasks 0.1, 0.2: Oruži's proofs are solid
- Tasks 1.1, 1.2: Standard library reasoning
- Task 2.1: Witness structure is clear

### Medium Risk
- Tasks 2.2, 2.3, 2.4: CheckHyp reasoning complex but structured
- Tasks 3.1, 3.2: MapM lemmas well-specified

### Higher Risk
- Task 3.3: Formula induction may need custom principle
- Task 3.4: Structural proofs depend on WF invariants
- Task 3.5: Integration may reveal gaps

## Mitigation Strategy

For higher-risk tasks:
1. **Prototype first:** Write the theorem statement and check it type-checks
2. **Admit early:** If stuck >2 hours, move to next task and revisit
3. **Document gaps:** If a helper lemma is needed, add as new task
4. **Ask Oruži:** For stuck proofs, request specific help

## Success Metrics

- ✅ Week 1 end: 0 axioms, Phase 1 complete (~20 sorries remaining)
- ✅ Week 2 end: Phase 2 complete (~12 sorries remaining)
- ✅ Week 3 end: Phase 3 mostly done (~5 sorries remaining)
- ✅ Week 4 end: 0 sorries, full compilation!

## Next Immediate Action

**Start with Task 0.1:** Integrate Oruži's KernelExtras proofs.

This is:
- ✅ Low risk (proofs provided)
- ✅ High value (eliminates 6 axioms)
- ✅ No dependencies
- ✅ Unblocks Phase 1

Estimated time: 2 hours

**Command to begin:**
```bash
# Edit Metamath/KernelExtras.lean
# Add Oruži's mapMOption and proofs
# Test: lake build Metamath.KernelExtras
```
