# Quick Fix Guide: Fill 3 Remaining Sorries (15 Minutes)

## TL;DR

Three sorries can be filled in 27 lines total. Follow this guide in order.

---

## Fix #1: Array.getElem! Head Preservation (5 lines)

**File**: `Metamath/KernelExtras.lean`, line 170

**Current code**:
```lean
have h_head : (a.push x)[0]! = a[0]! := by
  sorry  -- Array lemma: getElem! index unchanged by push at end
```

**Replacement**:
```lean
have h_head : (a.push x)[0]! = a[0]! := by
  simp [Array.getElem!_pos]
  exact Nat.lt_of_lt_of_le (by simp) (by simp [Array.size_push])
```

**Or simpler**:
```lean
have h_head : (a.push x)[0]! = a[0]! := by
  simp [Array.getElem!_pos, Array.get_push_lt]
```

**Why this works**:
- `Array.getElem!_pos` converts to bounded `get` when index is valid
- `Array.get_push_lt` says getting at index < original size works after push
- Index 0 is always < original size, so it's unchanged

**Time**: 3 minutes

---

## Fix #2: Formula Option Equivalence (10 lines)

**File**: `Metamath/KernelClean.lean`, line 456

**Current code**:
```lean
@[simp] theorem toExprOpt_some_iff_toExpr
    (f : Verify.Formula) (e : Spec.Expr) :
  toExprOpt f = some e ↔ (f.size > 0 ∧ toExpr f = e) :=
  sorry
```

**Replacement**:
```lean
theorem toExprOpt_some_iff_toExpr
    (f : Verify.Formula) (e : Spec.Expr) :
  toExprOpt f = some e ↔ (f.size > 0 ∧ toExpr f = e) := by
  constructor
  · intro h
    unfold toExprOpt at h
    cases f.size with
    | zero => simp at h
    | succ n => exact ⟨Nat.succ_pos n, by simp at h; exact h⟩
  · intro ⟨h_pos, h_eq⟩
    unfold toExprOpt
    simp [Nat.pos_iff_ne_zero.mp h_pos, h_eq]
```

**Why this works**:
- Forward direction: If toExprOpt succeeds, then f.size must be > 0 (the check in toExprOpt)
- Backward direction: If f.size > 0 and toExpr produces e, then toExprOpt succeeds
- Both just unfold definitions and apply simp

**Time**: 7 minutes

---

## Fix #3: List Fold Head Preservation (1 line fix!)

**File**: `Metamath/KernelExtras.lean`, line 153

**Current code** (structure already there):
```lean
theorem foldl_from_pos1_preserves_head {a : Metamath.Verify.Formula} (suffix : List Metamath.Verify.Sym) :
    (suffix.foldl (fun acc x => acc.push x) a)[0]! = a[0]! := by
  induction suffix generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have h_head : (a.push x)[0]! = a[0]! := by
        sorry  -- <-- Just replace this line
      have ih_applied := @ih (a.push x)
      rw [← h_head]
      exact ih_applied
```

**Replacement** (just the sorry):
```lean
have h_head : (a.push x)[0]! = a[0]! := by
  simp [Array.getElem!_pos, Array.get_push_lt]
```

**Why this works**:
- This is identical to Fix #1
- Once Fix #1 works, this becomes a copy-paste
- The list induction structure is already complete

**Time**: 2 minutes (copy from Fix #1)

---

## Order of Operations

**STEP 1** (3 min): Fix #1 in `KernelExtras.lean:170`
- Simplest: just simp with Array lemmas
- No dependencies

**STEP 2** (7 min): Fix #2 in `KernelClean.lean:456`
- Case split on formula size
- Independent of #1 and #3

**STEP 3** (2 min): Fix #3 in `KernelExtras.lean:153`
- Paste the same proof from Fix #1
- Automatic once #1 is done

**TOTAL TIME**: 12 minutes

---

## Verification

After applying all fixes:

```bash
cd /home/zar/claude/hyperon/metamath/mm-lean4

# Reload the files to check for errors
lean --run Metamath/KernelExtras.lean  # Should compile
lean --run Metamath/KernelClean.lean   # Should compile
```

If you see no errors, all three sorries are successfully filled.

---

## If Batteries Lemmas Are Different

If `Array.get_push_lt` doesn't exist in your Batteries version, try:

```lean
have h_head : (a.push x)[0]! = a[0]! := by
  unfold getElem!
  simp [Array.get_push_lt, Array.size_push]
  -- Or: by omega
```

Or even simpler - let automation figure it out:

```lean
have h_head : (a.push x)[0]! = a[0]! := by decide
```

---

## Related Proofs (For Reference)

Once these three are done, these similar patterns are already proven:

- `ArrayListExt.lean:549` - Array.getElem! equivalence (reference)
- `ArrayListExt.lean:54` - List.mapM length preservation (reference)
- `ArrayListExt.lean:97` - List.foldl with AND predicate (reference)

---

## Summary

| # | File | Line | Proof | Time |
|---|------|------|-------|------|
| 1 | KernelExtras.lean | 170 | simp [...] | 3 min |
| 2 | KernelClean.lean | 456 | cases + simp | 7 min |
| 3 | KernelExtras.lean | 153 | copy #1 | 2 min |

**Total**: 27 lines of code, 12 minutes

