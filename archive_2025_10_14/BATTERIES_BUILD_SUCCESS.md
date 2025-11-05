# Batteries Build - Success with Remaining Issues

## Good News

✅ **Batteries built successfully** using `LEAN_JOBS=1 lake build batteries`
- Build completed in ~40 seconds
- No memory issues with single-threaded build
- 187 modules compiled successfully

## Remaining Issues

Even with Batteries available, Oruži's proofs still have fundamental compatibility issues with Lean 4.20.0-rc2:

### 1. **mapM.loop not expanding**
```lean
-- This doesn't work:
cases hfx : f x with
| none   => simp [List.mapM, hfx] at h  -- Doesn't simplify mapM.loop

-- Error: unsolved goals
h : mapM.loop f (x :: xs) [] = some ys
```

The problem: `List.mapM` is defined as `mapM f xs = mapM.loop f xs []`, and `mapM.loop` uses monadic bind that `simp` doesn't expand the way Oruži's proof expects.

### 2. **Bool.and_eq_true API difference**
```lean
-- Oruži's proof expects:
(and_eq_true b (p x)).mp hbp  -- Where hbp : (b && p x) = true

-- But Batteries has:
Bool.and_eq_true : (a && b) = true = (a = true ∧ b = true)  -- Prop equality, not ↔
```

### 3. **Private lemma scope issue**
```lean
private lemma inner_true_iff ...  -- Defined at line 70
...
exact (inner_true_iff ys ...).mp hx  -- Line 88: unknown identifier
```

The `private` keyword makes it invisible even within the same proof.

### 4. **Array simp loops**
```lean
simp [getElem!]  -- Causes: maximum recursion depth reached
```

## Why This Matters

These aren't minor syntax differences - they're fundamental mismatches between:
- The Lean version Oru\u017ei tested with
- Lean 4.20.0-rc2's actual API

## Your Options

### Option A: Keep axioms (RECOMMENDED)
The current state with 6 well-documented axioms is pragmatic:
- ✅ Project compiles
- ✅ Axioms are obviously true library properties
- ✅ Minimal TCB impact (standard List/Array operations)
- ✅ Can proceed with verification work
- ⚠️ 6 axioms remain (but they're not domain-specific)

### Option B: Ask Oruži for corrected proofs
Provide Oruži with:
1. Exact Lean version: 4.20.0-rc2
2. This exact project to test in
3. Specific API constraints:
   - `List.mapM` uses `mapM.loop` with bind
   - `Bool.and_eq_true` is Prop equality not ↔
   - Need workarounds for these specific issues
4. Request: test compilation before sending

### Option C: Manual proof development (4-8 hours)
I can work through each proof systematically:
1. Write helper lemmas about `mapM.loop` behavior
2. Prove accumulator properties
3. Build up from primitives
4. Test each step

This would give you fully proven lemmas but requires significant time.

### Option D: Use Batteries lemmas directly
Check if Batteries already has these exact lemmas:
```bash
grep -r "mapM.*length" .lake/packages/batteries/
grep -r "foldl.*and" .lake/packages/batteries/
```

If they exist, just import and use them directly.

## Current State

- **Batteries:** ✅ Built and available
- **KernelExtras:** ⚠️ Back to axioms (compiles)
- **Project:** ✅ Compiles fully
- **Proofs:** ❌ Need adaptation for this specific environment

## My Recommendation

**Go with Option D first, then Option A:**
1. Search Batteries for existing versions of these lemmas
2. If found, use them directly
3. If not found, keep the axioms

The axioms are standard library properties with clear justifications. The time spent trying to get proofs working could be better spent on the actual verification work.
