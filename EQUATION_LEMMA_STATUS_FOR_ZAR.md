# Equation Lemma Status - For Zar

## TL;DR

✅ **Do-notation reduction: SOLVED!**
⚠️ **Remaining gap: Array indexing notation mismatch** (1 technical detail)

---

## What Works

The equation lemma `checkHyp_step_hyp_true` now successfully:

1. ✅ Unfolds `checkHyp` definition
2. ✅ Specializes the pattern match using `h_find`
3. ✅ Reduces `if True then` from the specialization
4. ✅ Cases on `f.subst σ` to match structure
5. ✅ **Reduces do-notation** via `simp [h_subst, bind, Except.bind]`
   - `do { let x ← error e; ... }` → `error e` ✅
   - `do { let x ← ok s; ... }` → `(λ s => ...)(s)` ✅

**Current proof** (Metamath/Verify.lean, lines 431-467):
```lean
@[simp] theorem checkHyp_step_hyp_true ... := by
  unfold checkHyp
  simp only [h_i, dite_true, h_find, ↓reduceIte]
  cases h_subst : f.subst σ with
  | error e =>
    simp [h_subst, bind, Except.bind]
    -- ✅ Do-notation reduced!
    sorry  -- ⚠️ Array indexing gap
  | ok s =>
    simp [h_subst, bind, Except.bind]
    -- ✅ Do-notation reduced!
    sorry  -- ⚠️ Array indexing gap
```

**Status**: Compiles with warning about sorry ✅

---

## The Remaining Gap

### Error Case (line 458-462)
After `simp [h_subst, bind, Except.bind]`, the goal is:

```lean
⊢ (if (f[0]! == stack[off.val + i][0]!) = true then Except.error e
   else throw (...toString stack[off.val + i]...))
  =
  (if (f[0]! == stack[off.val + i]![0]!) = true then Except.error e
   else Except.error (...toString stack[off.val + i]!...))
```

**Difference**: `stack[off.val + i]` vs `stack[off.val + i]!`

### Why This Happens

Inside `checkHyp` definition (line 404-407):
```lean
let val := stack[off.1 + i]'(proof_that_i_in_bounds)
-- Then all references use `val`, not direct indexing
```

After unfold, the LHS has:
- `val` which is bound to `stack[off.1 + i]'(proof)`
- All references to stack go through `val`

But the RHS (equation lemma statement, line 441-450) uses:
- `stack[off.1 + i]!` directly (panic-safe indexing)

### Attempted Solutions

1. ❌ `simp only [GetElem.getElem, Array.get!, Array.get]` - didn't help
2. ❌ `dsimp only []` for zeta reduction - made no progress
3. ❌ `simp (config := {zeta := true}) only []` - made no progress
4. ❌ `rfl` - not definitionally equal

**Root cause**: The let-binding `val` prevents Lean from seeing that `val = stack[off.1 + i]!`

---

## What I Learned

### Array Indexing Notations in Lean 4

**Test case** (`/tmp/test_array_index.lean`):
```lean
-- With concrete values - these ARE definitionally equal:
example (h : 0 < test_arr.size) : test_arr[0]'h = test_arr[0]! := rfl  -- ✅ works

-- In general - they are NOT definitionally equal:
example {α} [Inhabited α] (arr : Array α) (i : Nat) (h : i < arr.size) :
  arr[i]'h = arr[i]! := rfl  -- ❌ fails
```

**Why**: `arr[i]!` is defined as:
```lean
if h : i < arr.size then arr[i]'h else panic! default
```

So they're **propositionally** equal when `h : i < arr.size` holds, but not **definitionally** equal in general.

### The Let-Binding Issue

Even when we HAVE `h_i : i < hyps.size` in scope, the let-binding prevents the simplifier from connecting:
```
val (where val := stack[i]'h_i)  ≟  stack[i]!
```

The zeta reduction config should unfold the let, but it's not working here (maybe because it's in a nested do-block context?).

---

## Possible Solutions

### Option A: Bridge Lemma (Cleanest)
Prove and mark `@[simp]`:
```lean
theorem array_get_proof_eq_bang {α} [Inhabited α] (arr : Array α) (i : Nat) (h : i < arr.size) :
  arr[i]'h = arr[i]! := by
  simp [GetElem.getElem]
  -- Should reduce to showing: arr.data[i] = if h : ... then arr.data[i] else panic
  sorry
```

Then add this to the `simp` call:
```lean
simp [h_subst, bind, Except.bind, array_get_proof_eq_bang]
```

**Status**: I couldn't figure out how to prove this lemma (got stuck on recursion depth or missing instances).

### Option B: Rewrite RHS (More Mechanical)
Change the equation lemma statement to match the internal form:

**Current RHS**:
```lean
if f[0]! == stack[off.1 + i]![0]! then
  match f.subst σ with ...
```

**New RHS** (match internal structure):
```lean
let val := stack[off.1 + i]'(proof)
if f[0]! == val[0]! then
  match f.subst σ with ...
```

**Pros**: Mechanically provable (just `rfl` after do-notation reduction)
**Cons**: Exposes implementation detail (the let-binding) in the equation lemma API

### Option C: Manual Conversion Tactic
Write a tactic that explicitly converts between the two forms:
```lean
have h_val_eq : val = stack[off.val + i]! := by
  simp only [val, GetElem.getElem]
  sorry  -- prove that arr[i]'proof = arr[i]!
rw [h_val_eq] at *
```

**Status**: Still requires solving the array indexing equality.

### Option D: Accept Axiomatization (Temporary)
Keep the equation lemmas as `axiom` temporarily, marking them with TODO.
- They're clearly true by inspection of the definition
- Unblocks AXIOM 2 elimination work in KernelClean
- Come back to prove them properly later

**Downside**: Adds 2 axioms (but they're clearly sound).

---

## Recommendation

**For Zar**: Please advise on the best path forward:

1. **If you know the array bridge lemma**: Please provide the correct statement and proof, or point me to the right library lemma
2. **If Option B is acceptable**: I can rewrite the RHS to expose the let-binding (less clean but provable)
3. **If Option D is acceptable**: Keep as axioms with clear TODO comments, move forward with AXIOM 2 elimination

The do-notation reduction technique is solid and will work for `checkHyp_step_hyp_false` (float case) as well. This is purely a notation/let-binding issue, not a conceptual problem.

---

## Files Modified This Session

1. **Metamath/Verify.lean** (lines 431-467)
   - `checkHyp_step_hyp_true`: Theorem with do-notation reduction working, 2 sorries for array indexing gap
   - **Status**: ✅ Compiles with warning

2. **SESSION_2025-11-02_DO_NOTATION_BREAKTHROUGH.md**
   - Documents the do-notation solution
   - Explains the remaining gap

3. **EQUATION_LEMMA_STATUS_FOR_ZAR.md** (this file)
   - Clear summary for Zar to unblock

4. **Test files**: `/tmp/test_bind.lean`, `/tmp/test_array_index.lean`
   - Experiments with do-notation and array indexing

---

## Next Steps (After Unblocking)

1. Apply Zar's solution to complete `checkHyp_step_hyp_true`
2. Prove `checkHyp_step_hyp_false` using same pattern
3. Verify both compile as `theorem` (not `axiom`)
4. Test in KernelClean.lean Phase 4 (extraction patterns)
5. Complete AXIOM 2 elimination!

---

**Current Build Status**: ✅ Compiles with 1 warning (sorry in theorem)
**Do-Notation Status**: ✅ Fully solved
**Remaining Blocker**: ⚠️ Array indexing notation (1 gap, clear solutions available)
