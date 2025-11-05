# Breakthrough: Indexed Conversion Guarantees Order!

**Thanks to Zar's insight**: "Indexed stack entry SHOULD guarantee order in the stack, right?"

## The Realization ✨

### What I Was Missing

I thought:
```lean
∀ i < size, ∃ e, toExpr stack[i] = some e ∧ e ∈ stack_before
```
only gave MEMBERSHIP (elements are somewhere in `stack_before`).

But actually, **the INDEX `i` determines the ORDER**!

### The Bridge

From indexed facts, I can use my already-proven `array_mapM_succeeds`:

```lean
-- From indexed conversion facts
h_converts : ∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e

-- Get the canonical ordered list via mapM
obtain ⟨stack_list, h_mapM⟩ := array_mapM_succeeds pr.stack h_converts

-- Now: pr.stack.toList.mapM toExpr = some stack_list
-- This IS the ordered conversion!
```

### Why This Works

- `mapM toExpr` on `pr.stack.toList` processes elements **in order**
- Index `i` in the array corresponds to position `i` in `stack_list`
- The indexed facts `toExpr stack[i] = some e_i` determine `stack_list = [e_0, e_1, ..., e_n]`
- **Order is preserved!**

## The Fix Applied

**In `stack_shape_from_checkHyp`** (Kernel.lean:1831-1838):
```lean
-- Extract ordered list from indexed facts
have h_converts : ∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e := by
  intro i hi
  obtain ⟨e, he, _⟩ := h_stack_conv i hi
  exact ⟨e, he⟩

-- Get canonical ordered list
obtain ⟨stack_list, h_mapM⟩ := array_mapM_succeeds pr.stack h_converts

-- Now stack_list is the ordered conversion!
-- Can apply Oruži's loop invariant strategy
```

## Why I Was Stuck

I was treating `stack_before` as an arbitrary list where elements happen to be members. But:

1. **Truth**: Indexed facts `toExpr stack[i] = e_i` uniquely determine an ordered list
2. **Mechanism**: `mapM` extracts this ordered list from the indexed facts
3. **Bridge**: `array_mapM_succeeds` connects the two

The theorem was **using a weak formulation** (membership) when it had **strong premises** (indexed conversion).

## Path Forward

Now I can:

1. ✅ Extract `stack_list` from indexed facts via `mapM` (DONE)
2. ⬜ Prove `stack_list = stack_before` (they're both determined by same indexed facts)
3. ⬜ Apply Oruži's loop invariant: `P i := stack_list = (needed.take i).reverse ++ rest`
4. ⬜ Use `matchRevPrefix_correct` to build the proof

**Status**: Conceptual blockage removed! Now it's just the mechanical proof work.

## Build Status

✅ Code builds with the bridge in place (Kernel.lean:1831-1845)

**Next**: Implement Oruži's loop invariant proof (~30-40 lines)
