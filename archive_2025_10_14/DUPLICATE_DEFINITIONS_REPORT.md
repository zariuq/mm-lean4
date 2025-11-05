# Duplicate Definitions Report

**Date:** 2025-10-13
**Issue:** Found duplicate theorem definitions between KernelExtras.lean and Kernel.lean

## Summary

Two theorems are defined in BOTH files:
1. `list_mapM_append`
2. `list_mapM_dropLast_of_mapM_some`

**Impact:** Confusion, wasted effort, potential for inconsistency

## Duplicate 1: list_mapM_append

### KernelExtras.lean (line 168)
```lean
theorem list_mapM_append {α β} (f : α → Option β) (xs ys : List α) :
    (xs ++ ys).mapM f = do
      let xs' ← xs.mapM f
      let ys' ← ys.mapM f
      pure (xs' ++ ys') := by
  induction xs with
  | nil => simp [List.mapM]
  | cons x xs ih =>
      simp [List.mapM]
      cases hfx : f x with
      | none => simp [hfx]
      | some y =>
          simp [hfx]
          rw [ih]
          simp [pure, Bind.bind]
```
**Status:** ✅ Fully proven

### Kernel.lean (line 3435)
```lean
theorem list_mapM_append {α β : Type} (f : α → Option β) (xs ys : List α) :
  (xs ++ ys).mapM f = do
    xs' ← xs.mapM f
    ys' ← ys.mapM f
    pure (xs' ++ ys') := by
  induction xs with
  | nil => simp [List.mapM]
  | cons x xs ih =>
    simp [List.mapM, ih]
    cases hx : f x with
    | none => simp
    | some x' =>
      simp [hx]
```
**Status:** ✅ Fully proven (slightly different style)

### Usage Analysis
**In Kernel.lean:**
- Line 3093: Uses `list_mapM_append` (likely the KernelExtras version since import comes before)
- Line 3349, 3359: Comments reference KernelExtras version

**Conclusion:** The Kernel.lean version (line 3435) is **SHADOWING** the KernelExtras version and is likely **UNUSED** before its definition. It should be **REMOVED**.

---

## Duplicate 2: list_mapM_dropLast_of_mapM_some

### KernelExtras.lean (line 191)
```lean
theorem list_mapM_dropLast_of_mapM_some {α β} (f : α → Option β)
    (xs : List α) (ys : List β) (n : Nat) :
    xs.mapM f = some ys →
    (List.dropLast xs n).mapM f = some (List.dropLast ys n) := by
  intro h
  have h_len : ys.length = xs.length := mapM_length_option f h
  have hx : xs.dropLast n = xs.take (xs.length - n) := by
    simpa [List.dropLast_eq_take]
  have hy : ys.dropLast n = ys.take (ys.length - n) := by
    simpa [List.dropLast_eq_take]
  sorry  -- Depends on list_mapM_take_of_mapM_some
```
**Status:** ⚠️ Has sorry (documented dependency)

### Kernel.lean (line 3477)
```lean
theorem list_mapM_dropLast_of_mapM_some {α β : Type} (f : α → Option β)
    (xs : List α) (ys : List β) (k : Nat)
    (h : xs.mapM f = some ys) :
  (xs.dropLast k).mapM f = some (ys.dropLast k) := by
  have hx : xs.dropLast k = xs.take (xs.length - k) := by
    simpa [List.dropLast_eq_take]
  have hy : ys.dropLast k = ys.take (ys.length - k) := by
    simpa [List.dropLast_eq_take]
  have htake := list_mapM_take_of_mapM_some f xs ys (xs.length - k) h
  simpa [hx, hy] using htake
```
**Status:** ✅ Fully proven (uses `list_mapM_take_of_mapM_some`)

### Usage Analysis
**In Kernel.lean:**
- Line 3082: Uses `list_mapM_dropLast_of_mapM_some` (BEFORE line 3477!)
  - This means it's using the KernelExtras version
  - But KernelExtras version has sorry!
  - **This is a problem!**

**Timeline:**
1. Line 3082: First usage (must be KernelExtras version)
2. Line 3477: Kernel.lean defines its own version (proven)

**Conclusion:** This is **CONFUSING**. The early usage (line 3082) sees the KernelExtras version (with sorry), but later code would see the Kernel version (proven). This could cause issues.

---

## Recommendations

### Option A: Keep KernelExtras, Remove Kernel duplicates (RECOMMENDED)
**Action:**
1. Remove `list_mapM_append` from Kernel.lean (line 3435)
2. Keep `list_mapM_dropLast_of_mapM_some` in Kernel.lean (line 3477) since it's proven
3. Move `list_mapM_take_of_mapM_some` from Kernel.lean (line 3457) to KernelExtras
4. Complete KernelExtras version of `list_mapM_dropLast` using the proven strategy

**Benefit:**
- Clean separation: Foundation lemmas in KernelExtras
- No shadowing
- Clear dependencies

### Option B: Move all to KernelExtras
**Action:**
1. Move `list_mapM_take_of_mapM_some` to KernelExtras
2. Complete `list_mapM_dropLast_of_mapM_some` in KernelExtras using take theorem
3. Remove all duplicates from Kernel.lean

**Benefit:**
- Maximum organization
- All mapM lemmas in one place
- No duplicates anywhere

### Option C: Keep Kernel versions, remove KernelExtras sorries
**Action:**
1. Remove incomplete versions from KernelExtras
2. Keep all proven versions in Kernel.lean

**Downside:**
- Goes against the design (KernelExtras should be foundation)
- Kernel.lean becomes cluttered

---

## Other Findings

### Duplicate defs (not theorems)
```
def stepAssert (db : DB) (pr : ProofState) (f : Formula) : Frame → Except String ProofState
def Sym.isVar : Sym → Bool
```

These need investigation too!

---

## Action Plan

**Immediate (High Priority):**
1. ✅ Move `list_mapM_take_of_mapM_some` from Kernel.lean to KernelExtras
2. ✅ Complete KernelExtras `list_mapM_dropLast` using the take theorem
3. ✅ Remove `list_mapM_append` duplicate from Kernel.lean (line 3435)
4. ✅ Remove `list_mapM_dropLast` duplicate from Kernel.lean (line 3477)

**Estimated time:** 30-45 minutes

**Expected result:** Clean codebase, no shadowing, error count unchanged (all proofs work)

---

**Bottom Line:** Found 2 major duplicates causing confusion. Recommended action: Keep KernelExtras as source of truth, remove Kernel.lean duplicates after moving dependencies. Clean this up for maintainability! 🧹
