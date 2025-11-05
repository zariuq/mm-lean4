# Stuck on Group E Theorem Formulation

**Status**: Made progress but hit a conceptual issue with theorem statements

---

## What I Completed ✅

1. **Added Array↔List bridge lemmas** (`/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/Kernel.lean:2192-2218`)
   - `Array.toList_shrink_dropRight`: shrink ↔ dropLast
   - `Array.toList_push`: push ↔ snoc
   - ✅ Builds successfully

2. **Understood Oruži's proof strategy**:
   - Use loop invariant: `P i := ∃ rest, pr.stack.toList = (needed.take i).reverse ++ rest`
   - Prove P 0, then P i → P (i+1), conclude P (needed.length)
   - This is elegant and should work!

---

## Where I'm Stuck ⚠️

### The Formulation Mismatch

**Current theorem** (Kernel.lean:1814-1836):
```lean
theorem stack_shape_from_checkHyp
  (stack_before : List Spec.Expr)
  (h_stack_conv : ∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack_before)
  ...
  : ∃ remaining, stack_before = needed.reverse ++ remaining
```

**The problem**:
- `h_stack_conv` only says each `pr.stack[i]` converts to *something IN* `stack_before`
- This is a MEMBERSHIP property, not an ORDERING property
- We're trying to prove something about the ORDER of `stack_before`
- **This is unprovable as stated!**

**What Oruži's proof needs**:
```lean
theorem stack_shape_from_checkHyp
  (stack_list : List Spec.Expr)
  (h_stack_list : pr.stack.toList.mapM toExpr = some stack_list)  -- ORDERED conversion!
  ...
  : ∃ remaining, stack_list = needed.reverse ++ remaining
```

### Why This Matters

In the current code:
1. `build_spec_stack` (Kernel.lean:2417) returns a list with only membership guarantees
2. It's used to get `stack_before` in the main proof (Kernel.lean:1910)
3. But `stack_shape_from_checkHyp` needs ORDERED correspondence

**We have two options**:

**Option A**: Use `viewStack` / `mapM` instead
- Replace `build_spec_stack` with `viewStack pr.stack = some stack_list`
- This gives ordered conversion via `mapM`
- Theorem becomes provable with Oruži's strategy

**Option B**: Fix the formulation of `build_spec_stack`
- Change it to return the *ordered* list of conversions
- E.g., `∃ stack, pr.stack.toList.mapM toExpr = some stack`
- Then reformulate theorem premises to use this

---

## The Core Issue

```lean
-- What we HAVE (too weak):
∀ i, ∃ e, toExpr stack[i] = some e ∧ e ∈ stack_before
-- Says: "each stack element converts to SOMETHING in the list"
-- Doesn't tell us WHERE in the list or the ORDER

-- What we NEED (ordered):
stack.toList.mapM toExpr = some stack_list
-- Says: "stack converts to stack_list IN ORDER"
-- Preserves the array→list correspondence
```

---

## The Fix (I think)

Looking at the code, we already have the right infrastructure:
- `viewStack` (Kernel.lean:2113) does `stk.toList.mapM toExpr`
- `array_mapM_succeeds` (Kernel.lean:2141) proves mapM succeeds when elements convert

So the fix is:

1. **Change the theorem statement**:
```lean
theorem stack_shape_from_checkHyp
  (pr : ProofState)
  (stack_list : List Spec.Expr)
  (σ_impl : HashMap String Formula)
  ...
  -- OLD: (∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack_before)
  -- NEW: pr.stack.toList.mapM toExpr = some stack_list
  (h_stack_mapM : pr.stack.toList.mapM toExpr = some stack_list)
  ...
  : ∃ remaining, stack_list = needed.reverse ++ remaining
```

2. **Update the call site** (Kernel.lean:1910):
```lean
-- OLD:
have pr_inv := proof_state_has_inv db pr WFdb
have h_stack_conv := build_spec_stack pr_inv
obtain ⟨stack_before, h_stack_before⟩ := h_stack_conv

-- NEW:
have h_stack_mapM : ∃ stack_list, pr.stack.toList.mapM toExpr = some stack_list := by
  apply array_mapM_succeeds
  intro i hi
  -- From WF: each stack element converts
  exact ... (from pr_inv or WFdb)
obtain ⟨stack_list, h_stack_mapM⟩ := h_stack_mapM
```

3. **Then Oruži's proof works**:
   - Loop invariant on `pr.stack.toList`
   - Use `matchRevPrefix_correct`
   - Extract the split

---

## What I Need

**From you (Zar/Oruži)**:

1. Confirm this diagnosis is correct
2. Should I:
   - a) Reformulate both theorems with `mapM` premises?
   - b) Keep current formulation but change what it means?
   - c) Something else?

3. How should I get the ordered stack conversion at the call site?
   - From `WFdb` / `pr_inv`?
   - Prove it locally using `array_mapM_succeeds`?

**I can implement the fix once I know the right formulation!**

---

## Time Spent

- ✅ Array helpers: 10 min
- ✅ Understanding strategy: 15 min
- ⚠️ Debugging formulation mismatch: 30 min
- **Total**: ~1 hour

Still on track if we can resolve this formulation issue.

---

## Next Steps

Once we fix the formulation:
1. Prove `stack_shape_from_checkHyp` with Oruži's loop invariant (~20-30 lines)
2. Prove `stack_after_stepAssert` using the above (~20-30 lines)
3. Keep `toExpr_subst_commutes` as axiom (or tackle later)

**Bottom line**: The proof strategy is sound, but the theorem statements need adjustment to match the strategy.
