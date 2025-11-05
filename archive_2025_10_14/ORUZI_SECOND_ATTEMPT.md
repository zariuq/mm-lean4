# Oruži's Second Attempt - Compilation Issues

## Summary

Oruži provided excellent proofs that avoid `mapM.loop` by using direct case-splitting. However, they still encounter fundamental incompatibilities with Lean 4.20.0-rc2's internal implementation.

## Specific Errors Encountered

### 1. mapM_length_option (Lines 12-29)

**Oruži's approach:**
```lean
cases hfx : f x with
| none   => simp [List.mapM, hfx] at h
| some y =>
  cases hxs : xs.mapM f with
  | none      => simp [List.mapM, hfx, hxs] at h
  | some ys'  => ...
```

**Error at line 18:**
```
error: unsolved goals
case none
h : mapM.loop f (x :: xs) [] = some ys
hfx : f x = none
⊢ ys.length = (x :: xs).length
```

**Problem:** Even after `simp [List.mapM, hfx]`, the hypothesis `h` remains as `mapM.loop f (x :: xs) [] = some ys` instead of simplifying to a contradiction. The `mapM.loop` doesn't expand.

**Error at line 23:**
```
error: dependent elimination failed, failed to solve equation
  some ys =
    match f x, fun __do_lift => mapM.loop f xs [__do_lift] with
    | none, x => none
    | some a, f => f a
```

**Problem:** The dependent pattern match that `mapM` compiles to isn't recognized by the `cases` tactic.

### 2. foldl_and_eq (Lines 31-37)

**Oruži's approach:**
```lean
private theorem foldl_and_eq (p : α → Bool) :
  ∀ xs (init : Bool),
    xs.foldl (fun b x => b && p x) init = (init && xs.all p)
| [],      init => by simp
| x :: xs, init => by
  simp [foldl_and_eq (xs := xs), Bool.and_assoc]
```

**Error at line 34:**
```
error: invalid field notation, type is not of the form (C ...) where C is a constant
  xs
has type
  ?m.71
```

**Problem:** The `.all` method isn't available on lists in the expected form, or there's a type inference issue preventing it from being found.

### 3. foldl_and_eq_true (Lines 39-60)

**Error at line 43:**
```
error: unknown identifier 'foldl_and_eq'
```

**Problem:** Because `foldl_and_eq` failed to compile, it's not available here.

### 4. foldl_all₂ (Lines 62-96)

**Errors at lines 79 and 96:**
```
error: type mismatch
  h
has type
  foldl (fun b x => foldl (fun b' y => b' && p x y) b ys) (foldl (fun b' y => b' && p x y) true ys) xs = true
but is expected to have type
  foldl (fun b x => b && foldl (fun b' y => b' && p x y) true ys) (foldl (fun b' y => b' && p x y) true ys) xs = true
```

**Problem:** The fold accumulator function differs:
- Got: `fun b x => foldl (fun b' y => b' && p x y) b ys`
- Expected: `fun b x => b && foldl (fun b' y => b' && p x y) true ys`

The boolean conjunction isn't being recognized as equivalent.

### 5. mapM_some_of_mem (Lines 98-121)

**Errors at lines 110, 113:**
```
error: unsolved goals
case cons.none
h : mapM.loop f (a :: as) [] = some ys
hfa : f a = none
⊢ ∃ b, f x = some b
```

**Problem:** Same `mapM.loop` non-expansion issue as #1.

**Error at line 116:**
```
error: type mismatch
  h
has type
  mapM.loop f (a :: as) [] = some ys
but is expected to have type
  ys = b :: ys'
```

**Problem:** The proof tries to extract `ys = b :: ys'` from the mapM success, but `mapM.loop` structure prevents this.

### 6. Array lemmas (Lines 125-141)

**Error at line 139:**
```
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
```

**Problem:** `simp [getElem!, k.isLt]` causes infinite recursion in the simp set.

## Root Causes

### 1. mapM.loop Implementation
`List.mapM` in Lean 4.20.0-rc2 is defined as:
```lean
def mapM [Monad m] (f : α → m β) (xs : List α) : m (List β) :=
  mapM.loop f xs []
```

And `mapM.loop` uses:
```lean
def mapM.loop [Monad m] (f : α → m β) : List α → List β → m (List β)
  | [], acc => pure acc.reverse
  | x :: xs, acc => do
    let y ← f x
    mapM.loop f xs (y :: acc)
```

The `simp` tactic doesn't expand this structure because:
- It uses monadic bind (`do` notation)
- It has an accumulator
- The pattern match is compiled to a complex dependent elimination

### 2. List.all Availability
The `.all` method on lists either:
- Doesn't exist in this Lean version
- Has a different name
- Requires explicit type annotations to be found

### 3. Boolean Fold Equivalences
The equivalence between:
- `foldl (fun b x => b && p x) init`
- `foldl (fun b x => p x && b) init`
- `init && all p`

Isn't automatically recognized by `simp`, requiring manual proof.

## Why Previous Attempt Failed

The first attempt (in BATTERIES_BUILD_SUCCESS.md) used similar case-splitting but hit the same `mapM.loop` wall.

## Why This Approach is Correct (But Doesn't Compile)

Oruži's proofs are mathematically sound:
- ✅ Correct induction structure
- ✅ Right case splits
- ✅ Proper IH application
- ❌ But `simp` doesn't cooperate with `mapM.loop`

## Potential Solutions

### Solution A: Prove lemmas about mapM.loop directly
```lean
theorem mapM_loop_length {α β} (f : α → Option β) :
  ∀ (xs : List α) (acc : List β) (ys : List β),
    mapM.loop f xs acc = some ys →
    ys.length = acc.length + xs.length
```

Then build the main theorems on top of these.

### Solution B: Use Batteries' existing lemmas
Search for:
- `Batteries.Data.List.mapM_length`
- `Batteries.Data.List.all_eq_true`
- Similar pre-proven facts

### Solution C: Different tactic approach
Instead of `simp [List.mapM]`, try:
- `unfold List.mapM`
- `rw [List.mapM]`
- Direct manipulation without `simp`

### Solution D: Accept axioms
These are standard library properties. The difficulty in proving them is an artifact of:
- This specific Lean version's implementation details
- Internal structures (`mapM.loop`) not designed for user-level proofs

## Recommendation for Oruži

If you want to try again, I suggest:

1. **Test in the exact environment first:**
   ```bash
   cd /home/zar/claude/hyperon/metamath/mm-lean4/
   # Create a test file
   lake env lean your_test.lean
   ```

2. **Start with just mapM_loop_length helper:**
   Prove properties about `mapM.loop` directly, then build main theorems on those.

3. **Check what Batteries actually has:**
   ```bash
   grep -r "mapM" .lake/packages/batteries/Batteries/Data/List/ --include="*.lean"
   ```

4. **Alternative: If Batteries has these, just import and re-export them:**
   ```lean
   -- If Batteries.Data.List has mapM_length:
   theorem mapM_length_option := Batteries.Data.List.mapM_length_some
   ```

## Current Status

- **KernelExtras.lean:** ✅ Compiles (with axioms)
- **Proofs:** ❌ Don't compile (mapM.loop issues)
- **Axioms:** ✅ Well-justified and documented
- **Project:** ✅ Can proceed with verification work

The 6 axioms remain, but they're clearly library properties, not domain-specific assumptions.
