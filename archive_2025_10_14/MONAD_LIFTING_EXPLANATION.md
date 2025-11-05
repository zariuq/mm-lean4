# Monad Lifting in Lean 4: Expert Explanation

**Source:** ChatGPT-5 / Lean Zulip expert response
**Date:** 2025-10-13
**Context:** Resolving the Phase 3 Session 1 blocker on `viewStack` and `mapM`

## The Core Issue

**There is NO automatic lifting from total functions to monadic functions in Lean 4.**

If you pass a total `toExpr : Formula → Expr` to `List.mapM`, Lean infers `m := Id`, giving you a plain `List Expr`, not `Option (List Expr)`. It will NOT silently wrap via `pure`.

## The Three Solutions for viewStack

```lean
-- Option A: Use partial function (RECOMMENDED) ✅
-- This is what we implemented in Session 2
def viewStack (stk : Array Formula) : Option (List Expr) :=
  stk.toList.mapM toExprOpt  -- toExprOpt : Formula → Option Expr

-- Option B: Explicit lifting with pure/some
def viewStack (stk : Array Formula) : Option (List Expr) :=
  stk.toList.mapM (m := Option) (fun f => some (toExpr f))

-- Option C: Skip mapM entirely
def viewStack (stk : Array Formula) : Option (List Expr) :=
  some (stk.toList.map toExpr)
```

**We chose Option A** in Session 2, which is the cleanest for fail-fast semantics.

## Why Lean Behaves This Way

```lean
mapM : {m : Type → Type} → [Monad m] → (α → m β) → List α → m (List β)
```

Lean infers `m` from either:
1. The type of the function argument `(α → m β)`, OR
2. The expected result type

If you pass a total `α → β`, Lean solves by `m := Id`. **There is no rule** "if `m` is `Option` then magically wrap with `pure`".

## Practical Proof Patterns

### Pattern 1: Normalization Lemma for Pure Lifting

```lean
@[simp] lemma List.mapM_pure (xs : List α) (f : α → β) :
  xs.mapM (m := Option) (fun a => some (f a)) = some (xs.map f) := by
  induction xs <;> simp [*]
```

This avoids `mapM.loop` entirely! After rewriting, all standard `map/append/take/dropLast` lemmas apply.

### Pattern 2: Append Lemma (Already in KernelExtras!)

```lean
@[simp] lemma List.mapM_append (f : α → Option β) (xs ys : List α) :
  (xs ++ ys).mapM f = do
    xs' ← xs.mapM f
    ys' ← ys.mapM f
    pure (xs' ++ ys') := by
  induction xs <;> simp [*]
```

**We already have this** in KernelExtras.lean at line 168! ✅

### Pattern 3: Length Preservation

```lean
lemma mapM_length_option {f : α → Option β}
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  revert ys; induction xs with
  | nil => intro ys; simpa using h
  | cons x xs ih =>
    intro ys; cases hfx : f x with
    | none   => simpa [List.mapM, hfx] using h
    | some y =>
      cases hxs : xs.mapM f with
      | none      => simpa [List.mapM, hfx, hxs] using h
      | some ys'  =>
        simp [List.mapM, hfx, hxs] at h
        cases h; simp [ih hxs]
```

**We already have this** in KernelExtras.lean at line 56! ✅

### Pattern 4: Membership → Success

```lean
lemma mapM_some_of_mem {f : α → Option β}
    {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) :
    ∃ b, f x = some b := by
  revert ys; induction xs with
  | nil => intro ys; cases hx
  | cons a as ih =>
    intro ys; cases hfa : f a with
    | none   => simpa [List.mapM, hfa] using h
    | some b =>
      cases hmap : as.mapM f with
      | none      => simpa [List.mapM, hfa, hmap] using h
      | some ys'  =>
        have := by simpa [List.mapM, hfa, hmap] using h
        cases this
        cases hx with
        | inl hx0 => subst hx0; exact ⟨b, hfa⟩
        | inr hx' => exact ih hmap hx'
```

**We already have this** in KernelExtras.lean at line 103! ✅

## Key Insight: Avoid mapM.loop

The proof patterns above work on Lean 4.20.0-rc2 because they:
- Never try to "simp through" the internal `mapM.loop`
- Stay at the two surface equations for `mapM` on `[]` and `x :: xs`
- Use `cases` to split on function results, then `simp [List.mapM, ...]`

**This is exactly what Oruži implemented in KernelExtras!** 🎯

## How This Resolved Our Blocker

### Session 1: The Confusion
- `viewStack` was defined as `stk.toList.mapM toExpr`
- `toExpr` is total: `Formula → Expr`
- But `viewStack` returns `Option (List Expr)`
- **Attempted 15+ proofs, all failed**

### Session 2: The Fix
- Changed to `stk.toList.mapM toExprOpt`
- `toExprOpt` is partial: `Formula → Option Expr`
- **Type-level correctness achieved**
- Proof strategies became obvious

### The Validation
Expert confirms: "Pick Option A (use partial function). This aligns with your Phase-3 fail-fast refactor and TypedSubst."

**We made the right choice!** ✅

## About the Six "Foundation" Axioms

The expert notes: "Those should NOT stay axioms."

**Status in our codebase:**
1. ✅ `mapM_length_option` - Fully proven (KernelExtras line 56)
2. ✅ `mapM_some_of_mem` - Fully proven (KernelExtras line 103)
3. ✅ `foldl_and_eq_true` - Fully proven (KernelExtras line 133)
4. ✅ `foldl_all₂_true` - Fully proven (KernelExtras line 144)
5. ✅ `Array.getBang_eq_get` - Fully proven (KernelExtras line 253)
6. ✅ `Array.mem_toList_get` - Fully proven (KernelExtras line 237)

**All axioms are eliminated!** Oruži's work is validated. 🎯

## Summary

**What we learned:**
- No automatic monad lifting exists in Lean 4
- Must explicitly choose monad and lift by hand
- Or use partial functions that match the target monad

**What we implemented:**
- Option A: Use `toExprOpt` with `mapM`
- Clean fail-fast semantics
- Type-correct at definition level

**What we validated:**
- KernelExtras proofs follow the expert-recommended patterns
- All six axioms are properly eliminated with proofs
- No reliance on `mapM.loop` internals

**Expert verdict:** "Keep going with phase 3!" ✅

---

**Bottom line:** Our Session 2 implementation is exactly right. The monad lifting mystery is solved, and we're using the expert-recommended patterns throughout. The foundation is solid! 🚀
