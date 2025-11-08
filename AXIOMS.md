# Axiom Inventory - MM-Lean4 Metamath Verifier

**Last Updated:** 2025-11-08
**Lean Version:** 4.24.0
**Batteries Version:** v4.24.0

This document tracks all axioms in the mm-lean4 codebase, categorizing them by provability and providing proof strategies.

---

## Executive Summary

**Total Axioms:** 20
**Recently Proven (Phase 1):** 3
**Target for Phase 2:** -5 to -10 (via Batteries)
**Target for Phase 3:** -5 to -8 (via proofs)

**Distribution:**
- Infrastructure (Array/List/mapM): 9 axioms
- Array extraction operations: 4 axioms
- List indexing: 1 axiom
- Parser invariants: 3 axioms
- Proof-specific (kernel): 3 axioms (+ 1 already proven)

---

## Recently Proven (Phase 1 - Nov 2025)

### ✅ mem_flatMap_iff
**File:** `Metamath/KernelExtras.lean:111`
**Status:** **PROVEN**
**Proof:** `by simp [List.mem_flatMap]`
**Impact:** Trivial 1-line proof using Batteries lemma

### ✅ mem_toList_get
**File:** `Metamath/KernelExtras.lean:210`
**Status:** **PROVEN**
**Proof:** Using `List.get_mem` with proper Fin construction
**Impact:** Standard array/list correspondence

### ✅ toList_get
**File:** `Metamath/KernelExtras.lean:286`
**Status:** **PROVEN**
**Proof:** `rfl` - definitional equality
**Impact:** Shows Array is essentially a List wrapper

---

## Infrastructure Axioms (Provable with Batteries 4.24.0)

These axioms capture standard properties of List.mapM and folding operations.

### List.mapM Properties (5 axioms)

#### 1. mapM_length_option
**File:** `Metamath/KernelExtras.lean:63`
**Statement:**
```lean
axiom mapM_length_option {α β : Type _} (f : α → Option β) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : xs.length = ys.length
```
**Category:** Infrastructure
**Provability:** **HIGH** - Standard mapM preservation property
**Proof Strategy:** Induction on `xs`, case analysis on `f x`, use Option.bind properties
**Priority:** HIGH
**Notes:** Oruži provided proof sketch, needs adaptation for Lean 4.24.0

#### 2. foldl_and_eq_true
**File:** `Metamath/KernelExtras.lean:74`
**Statement:**
```lean
axiom foldl_and_eq_true {α} {p : α → Bool} (xs : List α) :
    xs.foldl (fun b x => b && p x) true = true ↔
    ∀ x ∈ xs, p x = true
```
**Category:** Infrastructure
**Provability:** **HIGH** - Equivalent to `List.all`
**Proof Strategy:**
1. Use `List.all_eq_true` if available in Batteries
2. Otherwise: induction on `xs`, Bool.and_eq_true reasoning
**Priority:** HIGH
**Notes:** This is the boolean version of allM extraction

#### 3. foldl_all₂
**File:** `Metamath/KernelExtras.lean:86`
**Statement:**
```lean
axiom foldl_all₂ {α β} (xs : List α) (ys : List β) (p : α → β → Bool) :
  (xs.foldl (fun b x => ys.foldl (fun b' y => b' && p x y) b) true = true)
  ↔ (∀ x ∈ xs, ∀ y ∈ ys, p x y = true)
```
**Category:** Infrastructure
**Provability:** **MEDIUM** - Extension of `foldl_and_eq_true`
**Proof Strategy:**
1. Prove `foldl_and_eq_true` first
2. Apply it twice (outer and inner folds)
3. Use logical equivalence reasoning
**Priority:** MEDIUM
**Dependencies:** Requires `foldl_and_eq_true`

#### 4. mapM_some_of_mem
**File:** `Metamath/KernelExtras.lean:99`
**Statement:**
```lean
axiom mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b
```
**Category:** Infrastructure
**Provability:** **HIGH** - mapM success implies pointwise success
**Proof Strategy:**
1. Induction on `xs`
2. Case x = head: immediate from bind structure
3. Case x ∈ tail: induction hypothesis
**Priority:** HIGH

#### 5. list_mapM_append
**File:** `Metamath/KernelExtras.lean:193`
**Statement:**
```lean
axiom list_mapM_append {α β} (f : α → Option β) (xs ys : List α) (zs ws : List β)
    (hx : xs.mapM f = some zs) (hy : ys.mapM f = some ws) :
    (xs ++ ys).mapM f = some (zs ++ ws)
```
**Category:** Infrastructure
**Provability:** **HIGH** - mapM distributes over append
**Proof Strategy:**
1. Induction on `xs`
2. Base case: `[].mapM f = some [] → ([] ++ ys).mapM f = ys.mapM f`
3. Inductive case: use Option.bind and append properties
**Priority:** HIGH

### Additional List/mapM Axioms (4 axioms)

#### 6. mapM_get_some
**File:** `Metamath/KernelExtras.lean:182`
**Statement:**
```lean
axiom mapM_get_some {α β} (f : α → Option β) (xs : List α) (ys : List β) (i : Nat)
    (h_map : xs.mapM f = some ys) (h_i : i < xs.length) :
    ∃ (b : β) (h_ys : i < ys.length), f xs[i] = some b ∧ ys[i] = b
```
**Category:** Infrastructure
**Provability:** **MEDIUM** - Index preservation through mapM
**Proof Strategy:** Combine `mapM_length_option` with pointwise mapM properties
**Priority:** MEDIUM

#### 7. list_mapM_dropLastN_of_mapM_some
**File:** `Metamath/KernelExtras.lean:206`
**Statement:**
```lean
axiom list_mapM_dropLastN_of_mapM_some {α β} (f : α → Option β) (xs : List α) (ys : List β) (n : Nat)
    (h : xs.mapM f = some ys) :
    (xs.dropLastN n).mapM f = some (ys.dropLastN n)
```
**Category:** Infrastructure
**Provability:** **MEDIUM** - mapM commutes with dropLastN
**Proof Strategy:** Use list induction and dropLastN properties
**Priority:** MEDIUM

#### 8. filterMap_after_mapM_eq
**File:** `Metamath/KernelExtras.lean:232`
**Statement:**
```lean
axiom filterMap_after_mapM_eq {α β} (f : α → Option β) (p : β → Option β)
    (xs : List α) (ys : List β) (h_map : xs.mapM f = some ys)
    (h_filter : ∀ x, (do let y ← f x; p y) = f x) :
    ys.filterMap p = ys
```
**Category:** Infrastructure
**Provability:** **MEDIUM** - Category theory fusion law
**Proof Strategy:** Induction with filterMap/mapM composition reasoning
**Priority:** MEDIUM
**Notes:** This is a fusion optimization lemma

#### 9. getElem!_idxOf
**File:** `Metamath/KernelExtras.lean:121`
**Statement:**
```lean
axiom getElem!_idxOf {α : Type _} [BEq α] [Inhabited α] {xs : List α} {x : α} (h : x ∈ xs) :
  xs[xs.idxOf x]! = x
```
**Category:** List indexing
**Provability:** **MEDIUM** - Standard `idxOf` property
**Proof Strategy:** Use List.idxOf correctness theorem if available in Batteries
**Priority:** MEDIUM

---

## Array Extraction Axioms (Check Batteries 4.24.0)

These might already be in Batteries. **Action:** Search Batteries.Data.Array.Lemmas

#### 10. toList_extract_dropLastN
**File:** `Metamath/KernelExtras.lean:237`
**Statement:**
```lean
@[simp] axiom toList_extract_dropLastN {α} (a : Array α) (k : Nat) (h : k ≤ a.size) :
  (a.extract 0 (a.size - k)).toList = a.toList.dropLastN k
```
**Category:** Array/List bridge
**Provability:** **CHECK BATTERIES FIRST**, then **MEDIUM** to prove
**Proof Strategy:**
1. Search for `Array.toList_extract` in Batteries
2. If not found: prove via `toList_extract_take` + List.take/dropLastN equivalence
**Priority:** HIGH (needed for stack operations)

#### 11. toList_extract_take
**File:** `Metamath/KernelExtras.lean:248`
**Statement:**
```lean
@[simp] axiom toList_extract_take {α} (a : Array α) (n : Nat) :
  (a.extract 0 n).toList = a.toList.take n
```
**Category:** Array/List bridge
**Provability:** **CHECK BATTERIES FIRST**, then **HIGH**
**Proof Strategy:**
1. Search Batteries for `Array.toList_extract`
2. Fundamental property - may be definitional
**Priority:** HIGH

#### 12. shrink_toList
**File:** `Metamath/KernelExtras.lean:252`
**Statement:**
```lean
@[simp] axiom shrink_toList {α} (a : Array α) (n : Nat) :
  (a.shrink n).toList = a.toList.take n
```
**Category:** Array/List bridge
**Provability:** **CHECK BATTERIES FIRST**, then **HIGH**
**Proof Strategy:** Search for `Array.toList_shrink` in Batteries
**Priority:** HIGH

#### 13. window_toList_map
**File:** `Metamath/KernelExtras.lean:268`
**Statement:**
```lean
@[simp] axiom window_toList_map {α β}
  (a : Array α) (off len : Nat) (f : α → β) (h : off + len ≤ a.size) :
  (a.extract off (off + len)).toList.map f
  = (a.toList.drop off |>.take len).map f
```
**Category:** Array/List bridge
**Provability:** **MEDIUM** - Likely provable from `toList_extract` + List.map fusion
**Proof Strategy:**
1. Use general `Array.toList_extract` if available
2. Apply List.map_drop and List.map_take
**Priority:** MEDIUM
**Notes:** Used in checkHyp proofs

---

## Parser Invariant Axioms (Prove by Code Inspection)

These capture parser behavior from `Verify.lean` and should be proven by analyzing the parser code.

#### 14. parser_validates_all_float_structures
**File:** `Metamath/ParserInvariants.lean:54`
**Statement:**
```lean
axiom parser_validates_all_float_structures
  (db : DB) (h_success : db.error? = none) :
  ∀ label fmla fr,
    db.find? label = some (Object.float fmla fr) →
    floatStructureValid db.frames fr fmla
```
**Category:** Parser correctness
**Provability:** **PROVEN BY CODE INSPECTION**
**Proof Strategy:**
1. Analyze `Verify.lean` lines 561-567 (parser float handling)
2. Show parser enforces structure validation before inserting
3. Use parser state invariants
**Priority:** HIGH
**Estimated Effort:** 12-20 hours
**Notes:** Detailed strategy in ParserInvariants.lean comments

#### 15. parser_validates_float_uniqueness
**File:** `Metamath/ParserInvariants.lean:78`
**Statement:**
```lean
axiom parser_validates_float_uniqueness
  (db : DB) (h_success : db.error? = none) :
  uniqueFloats db.frames
```
**Category:** Parser correctness
**Provability:** **PROVEN BY CODE INSPECTION**
**Proof Strategy:**
1. Analyze `Verify.lean` lines 325-339 (float insertion logic)
2. Show parser checks for duplicates before inserting
3. Maintain invariant through parsing
**Priority:** HIGH
**Estimated Effort:** 8-12 hours

#### 16. float_key_not_rebound (implied)
**File:** `Metamath/ParserInvariants.lean:397`
**Statement:** Ensured by unique floats property
**Category:** Parser correctness
**Provability:** **FOLLOWS FROM** `parser_validates_float_uniqueness`
**Priority:** MEDIUM
**Notes:** May be eliminated once main float theorem is proven

---

## Proof-Specific Axioms (Kernel Verification)

These are complex axioms tied to specific verification phases. Not trivial to prove.

#### 17. subst_eq_foldlM
**File:** `Metamath/KernelClean.lean:306`
**Statement:**
```lean
axiom subst_eq_foldlM
    (σ : Std.HashMap String Formula) (f : Formula) :
    f.subst σ = f.toList.foldlM (substStep σ) #[]
```
**Category:** Phase 4 - Formula substitution semantics
**Provability:** **RESEARCH** - Requires proving implementation matches spec
**Proof Strategy:** Structural induction on Formula, case analysis on subst behavior
**Priority:** MEDIUM (Phase 4 completion)
**Estimated Effort:** 20-40 hours

#### 18. Verify.Formula.subst_ok_flatMap_tail
**File:** `Metamath/KernelClean.lean:331`
**Statement:**
```lean
axiom Verify.Formula.subst_ok_flatMap_tail
    (σ : Std.HashMap String Formula) (tail : List Verify.Symbol) :
    (tail.map Verify.symToFormula).flatMap (Verify.Formula.subst σ)
    = tail.flatMap fun sym => (Verify.symToFormula sym).subst σ
```
**Category:** Phase 4 - Formula manipulation
**Provability:** **MEDIUM** - List fusion property
**Proof Strategy:** Induction + List.flatMap_map equivalence
**Priority:** MEDIUM

#### 19. subst_preserves_head
**File:** `Metamath/KernelClean.lean:358`
**Statement:**
```lean
axiom subst_preserves_head
    (σ : Std.HashMap String Formula) (head : Verify.Symbol) (tail : List Verify.Symbol)
    (h_const : head.isConst) :
    ((Verify.symToFormula head :: tail.map Verify.symToFormula).flatMap
      (Verify.Formula.subst σ))[0]!.isConst
```
**Category:** Phase 4 - Type preservation
**Provability:** **MEDIUM** - Requires analyzing subst behavior on constants
**Proof Strategy:** Case analysis on head type, use substitution invariants
**Priority:** MEDIUM

---

## Already Proven (Not Axioms Anymore)

#### ✅ toFrame_float_correspondence
**File:** `Metamath/KernelClean.lean:557`
**Status:** **PROVEN** (filterMap fusion lemma)
**Notes:** Successfully eliminated in earlier work!

---

## Phase 2 Targets (Batteries Migration - Week 2)

**High Priority - Check Batteries First:**
1. `toList_extract_dropLastN` (line 237)
2. `toList_extract_take` (line 248)
3. `shrink_toList` (line 252)
4. `window_toList_map` (line 268)
5. `getElem!_idxOf` (line 121)

**Search Commands:**
```bash
# In Batteries source
grep -rn "toList.*extract\|extract.*toList" Batteries/Data/Array/
grep -rn "toList.*shrink\|shrink.*toList" Batteries/Data/Array/
grep -rn "idxOf" Batteries/Data/List/
```

---

## Phase 3 Targets (Prove Remaining - Weeks 3-4)

**Ordered by Priority:**
1. `foldl_and_eq_true` (line 74) - Enables boolean verification patterns
2. `mapM_length_option` (line 63) - Fundamental mapM property
3. `mapM_some_of_mem` (line 99) - Pointwise mapM success
4. `list_mapM_append` (line 193) - mapM distribution
5. `foldl_all₂` (line 86) - Depends on foldl_and_eq_true
6. `mapM_get_some` (line 182) - Index preservation
7. `list_mapM_dropLastN_of_mapM_some` (line 206) - mapM/dropLastN commutation
8. `filterMap_after_mapM_eq` (line 232) - Fusion optimization

---

## Axiom Reduction Progress

| Phase | Axioms Proven | Axioms Remaining | Notes |
|-------|--------------|------------------|-------|
| **Start (Lean 4.20.0-rc2)** | 0 | 26+ | Many trivial axioms |
| **Initial 4.24.0 upgrade** | 3 | 23 | foldlM infrastructure proven |
| **Phase 1 Complete** | 6 | 20 | 3 trivial proofs + duplicate removed |
| **Phase 2 Target** | 11-16 | 10-15 | Batteries migration |
| **Phase 3 Target** | 16-24 | 2-7 | mapM/fold proofs |
| **Stretch Goal** | 24+ | 0-2 | Only research axioms remain |

---

## Blocked Axioms (Waiting on Upstream)

#### HashMap.find?_insert_self, HashMap.find?_insert_ne
**File:** `Metamath/KernelExtras.lean:453, 470`
**Status:** Axiomatized with `sorry` proofs
**Blocking:** Std.HashMap theorems not yet available in Batteries
**Priority:** LOW (only 2 axioms, well-understood)
**Notes:** Will be proven when Std.HashMap gets more theorems

---

## TCB (Trusted Code Base) Summary

**Infrastructure Axioms:** 13 (all provable or check-able)
**Parser Axioms:** 3 (provable by code inspection)
**Kernel Axioms:** 4 (3 research + 1 proven)
**HashMap Axioms:** 2 (blocked on Std)

**Critical Path to Zero Axioms:**
1. Phase 2: Check Batteries (5 axioms, 1 week)
2. Phase 3: Prove mapM/fold (8 axioms, 2 weeks)
3. Parser proofs (3 axioms, 2-3 weeks)
4. Kernel research (3 axioms, 4-6 weeks)
5. HashMap unblocked (2 axioms, when Std ready)

---

## How to Contribute

1. **Pick an axiom** from Phase 2 or 3 targets
2. **Check the proof strategy** documented above
3. **Prove the axiom** in a separate branch
4. **Test the build** to ensure no breakage
5. **Submit a PR** with the proof and build verification

**Contact:** See project README for discussion channels

---

## References

- **Oruži's Proof Strategies:** Comments in KernelExtras.lean
- **Batteries Documentation:** https://github.com/leanprover-community/batteries
- **Lean 4 Documentation:** https://lean-lang.org/
- **Project Context:** See archive/codex_archive.tar.gz for historical development notes
