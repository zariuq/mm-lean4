# Phase 3 Task 3.1 Blocker Report

## Status: BLOCKED

**Date:** 2025-10-13
**Task:** Phase 3 Task 3.1 - ViewStack Preservation (lines 3333, 3355)
**Error Count:** 193 (unchanged)
**Time Invested:** ~1.5 hours

## Issue Summary

Both `viewStack_push` and `viewStack_popK` theorems are blocked by the same fundamental issue:
**Monad lifting for total functions in `mapM`**

### The Core Problem

`viewStack` is defined as:
```lean
def viewStack (db : Metamath.Verify.DB) (stk : Array Metamath.Verify.Formula)
    : Option (List Metamath.Spec.Expr) :=
  stk.toList.mapM toExpr
```

Where:
- `toExpr : Formula → Expr` (total function)
- Return type: `Option (List Expr)`
- Uses: `List.mapM` with a total function

### The Puzzle

1. `toExpr` is a **total** function: `Formula → Expr` (not `Formula → Option Expr`)
2. `mapM` typically requires monadic functions: `α → m β`
3. Yet `viewStack` compiles and returns `Option (List Expr)`

**How does this work?**

Hypothesis: Lean 4 is automatically lifting `toExpr` through some monad instance or coercion:
- Either: `mapM` uses Id monad for total functions, then coerces `Id (List Expr)` → `Option (List Expr)`
- Or: There's an automatic `pure` wrapper: `mapM (pure ∘ toExpr)`
- Or: Some `Traversable` / `LawfulMonad` instance handles the lifting

### What We Tried (15+ attempts)

1. ✗ Using `list_mapM_append` directly
2. ✗ Unfolding `viewStack` and rewriting
3. ✗ Using `show` to clarify goal type
4. ✗ calc chain with explicit steps
5. ✗ simp with various lemma combinations
6. ✗ Explicit monad bind operations
7. ✗ conv_lhs with List.mapM_eq_mapM'
8. ✗ Array.toList_push (doesn't exist in Lean 4.20.0-rc2)
9. ✗ List.mapM_append (type mismatch)
10. ✗ Explicit Option.bind_eq_bind

**Consistent error:** After unfolding, tactics fail to make progress or encounter type mismatches

### Theorems Affected

#### 1. viewStack_push (line 3333)

**Goal:** Prove that pushing an element onto the stack appends the converted expression.

```lean
theorem viewStack_push (db : DB) (stack : Array Formula) (f : Formula)
    (stkS : List Expr) (e : Expr)
    (h_stack : viewStack db stack = some stkS) (h_f : toExpr f = e) :
    viewStack db (stack.push f) = some (stkS ++ [e])
```

**Note:** Fixed hypothesis from `toExpr f = some e` to `toExpr f = e` (toExpr is total!)

**Strategy:**
1. Show: `(stack.push f).toList = stack.toList ++ [f]` (Array property)
2. Apply `list_mapM_append` for the lifted monadic function
3. Use `h_stack` and `h_f` to conclude

**Estimated:** 15-20 lines once monad lifting clarified

#### 2. viewStack_popK (line 3355)

**Goal:** Prove that extracting first n elements drops last k from converted stack.

```lean
theorem viewStack_popK (db : DB) (stack : Array Formula) (k : Nat)
    (stkS : List Expr)
    (h_stack : viewStack db stack = some stkS) (h_len : k ≤ stack.size) :
    viewStack db (stack.extract 0 (stack.size - k)) = some (stkS.dropLast k)
```

**Strategy:**
1. Show: `(stack.extract 0 (stack.size - k)).toList = stack.toList.dropLast k`
2. Apply `list_mapM_dropLast_of_mapM_some` from Phase 1
3. Use `h_stack` to conclude

**Estimated:** 20-25 lines once monad lifting clarified

### Dependencies Ready

From Phase 1 (KernelExtras.lean):
- ✅ `list_mapM_append` - fully proven for Option monad
- ⚠️ `list_mapM_dropLast_of_mapM_some` - structure + sorry (but available)

**Problem:** These lemmas are for `f : α → Option β`, but we need them for the lifted version of `toExpr : Formula → Expr`

### Impact on Cascading Plan

**Phase 3 Task 3.1:**
- ❌ viewStack_push - BLOCKED
- ❌ viewStack_popK - BLOCKED

**Downstream impact:** Limited
- These theorems are used in proof state invariant preservation
- But most of Phase 3 can proceed independently

### Possible Solutions

#### Option A: Understand Monad Lifting (Recommended)

Research how Lean 4 handles:
- `mapM` with total functions
- Coercions from `Id` to `Option`
- `Traversable` instances

**Action:**
1. Check Lean 4 docs on monadic lifting
2. Examine `List.mapM` definition in Batteries/Std
3. Find the specific instance or coercion being used
4. Adapt `list_mapM_append` to work with lifted functions

**Estimated time:** 2-3 hours research + 1 hour proof

#### Option B: Refactor viewStack

Change `viewStack` to explicitly use `toExprOpt` or `map` instead of `mapM`:

```lean
def viewStack (db : DB) (stk : Array Formula) : Option (List Expr) :=
  some (stk.toList.map toExpr)
```

**Pros:** Eliminates monad lifting confusion
**Cons:** May break existing uses of `viewStack`

**Estimated time:** 1-2 hours refactoring + testing

#### Option C: Axiomatize

Add axioms for these two specific theorems:

```lean
axiom viewStack_push : ...
axiom viewStack_popK : ...
```

**Pros:** Unblocks immediately
**Cons:** Not ideal for verification project

**Estimated time:** 5 minutes

#### Option D: Skip to Other Phase 3 Tasks

Move to Task 3.2 (MapM Index Preservation) or Task 3.3 (Substitution Soundness) which may not have this issue.

**Estimated time:** 0 (continue with plan)

### Recommendation

**Option D: Skip to Task 3.2**

Reasoning:
1. Task 3.1 is blocked on a deep Lean 4 monad theory question
2. Other Phase 3 tasks are independent
3. Can return to 3.1 once the monad lifting pattern is clarified
4. Making progress on other tasks maintains momentum

**Fallback:** If multiple Phase 3 tasks hit similar issues, then pursue Option A (understand lifting) or Option B (refactor).

### What We Learned

1. ✅ `toExpr` is total: `Formula → Expr`
2. ✅ Theorem signatures had wrong types (`toExpr f = some e` → `toExpr f = e`)
3. ✅ Array.toList_push doesn't exist in Lean 4.20.0-rc2
4. ✅ `list_mapM_append` from Phase 1 is proven and available
5. ⚠️ Monad lifting for total functions in `mapM` is non-trivial

### Files Modified

- `Metamath/Kernel.lean`:
  - Lines 3331: Fixed `viewStack_push` hypothesis type
  - Lines 3333-3343: Added detailed sorry with strategy
  - Lines 3355-3363: Added detailed sorry with strategy

### Next Steps

1. ✅ Document this blocker (this file)
2. ⏭️ Move to Phase 3 Task 3.2: MapM Index Preservation
3. 🔜 Return to Task 3.1 when monad lifting pattern is understood

---

**Status:** Ready to proceed with Task 3.2
**Error count stable:** 193
**No regressions introduced:** ✅

