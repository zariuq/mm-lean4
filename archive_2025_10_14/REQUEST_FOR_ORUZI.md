# Request for Oruži/GPT-5: Adapted Proofs Needed

## Summary

You provided excellent proofs for 6 library lemmas, but they need adaptation to work in our specific environment (Lean 4.20.0-rc2 with Batteries).

## Environment Details

**Lean Version:** 4.20.0-rc2 (exact version)
```bash
Lean (version 4.20.0-rc2, x86_64-unknown-linux-gnu, commit fcb2f44cd3db, Release)
```

**Dependencies:**
- Batteries @ v4.20.0-rc2 (successfully built, 187 modules)
- No other dependencies

**Project:** `/home/zar/claude/hyperon/metamath/mm-lean4/`

**File:** `Metamath/KernelExtras.lean`

## Required Imports

```lean
import Batteries.Data.Array.Lemmas
import Batteries.Data.List.Lemmas
```

## The 6 Lemmas Needing Proofs

### 1. List.mapM_length_option
```lean
theorem mapM_length_option {α β : Type} (f : α → Option β) :
  ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
```

**Issue:** `List.mapM` is defined as `mapM f xs = mapM.loop f xs []`, and `mapM.loop` uses monadic bind that doesn't expand with simple `simp`.

### 2. List.foldl_and_eq_true
```lean
theorem foldl_and_eq_true {α} {p : α → Bool} (xs : List α) :
    xs.foldl (fun b x => b && p x) true = true ↔
    ∀ x ∈ xs, p x = true
```

**Issue:** `Bool.and_eq_true` in Batteries returns Prop equality (`=`), not `↔`.

### 3. List.foldl_all₂
```lean
theorem foldl_all₂ {α β} (xs : List α) (ys : List β) (p : α → β → Bool) :
  (xs.foldl (fun b x => ys.foldl (fun b' y => b' && p x y) b) true = true)
  ↔ (∀ x ∈ xs, ∀ y ∈ ys, p x y = true)
```

**Issue:** Depends on #2, plus `private` lemmas aren't visible in same proof.

### 4. List.mapM_some_of_mem
```lean
theorem mapM_some_of_mem {α β} (f : α → Option β)
  {xs : List α} {ys : List β} {x : α}
  (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b
```

**Issue:** Same `mapM.loop` issue as #1.

### 5. Array.mem_toList_get
```lean
@[simp] theorem mem_toList_get {α} [Inhabited α] (a : Array α) (k : Fin a.size) :
  a[k]! ∈ a.toList
```

**Issue:** `simp [getElem!]` causes infinite recursion in this Lean version.

### 6. Array.getBang_eq_get
```lean
@[simp] theorem getBang_eq_get {α} [Inhabited α] (a : Array α) (k : Fin a.size) :
  a[k]! = a[k]
```

**Issue:** Same simp loop issue.

## Specific API Constraints

### List Membership Constructors
```lean
-- Use these (Lean 4.20.0-rc2):
cases hx with
| head => ...
| tail _ hx' => ...

-- NOT these:
cases hx with
| inl => ...
| inr hx' => ...
```

### Bool.and_eq_true
```lean
-- Available in Batteries:
Bool.and_eq_true : (a && b) = true = (a = true ∧ b = true)

-- This is Prop equality, not ↔
-- You may need to work around this
```

### mapM.loop
```lean
-- List.mapM is defined as:
def mapM (f : α → Option β) (xs : List α) : Option (List β) :=
  mapM.loop f xs []

-- Where mapM.loop uses monadic bind
-- Direct case splitting on `mapM` doesn't work as expected
```

## What We Need

**For each of the 6 theorems above:**
1. A complete, working proof
2. That compiles in Lean 4.20.0-rc2 with Batteries
3. Using only the imports listed above
4. **Please test in this exact environment before sending**

## How to Test

```bash
# In the project directory:
cd /home/zar/claude/hyperon/metamath/mm-lean4/

# Test your proofs:
lake env lean Metamath/KernelExtras.lean

# Should output nothing (success)
# Any errors mean the proofs need more work
```

## Approaches That Might Work

### For mapM lemmas:
- Write helper lemmas about `mapM.loop` directly
- Use structural induction on the accumulator
- Avoid relying on `simp [List.mapM]` expanding cleanly

### For Bool lemmas:
- Define your own `and_eq_true_iff` as an intermediate lemma
- Use `cases a <;> cases b` for Bool reasoning
- Don't rely on `Bool.and_eq_true.mp` existing

### For Array lemmas:
- Avoid `simp [getElem!]` (causes loops)
- Use `split` tactic with explicit branches
- Prove properties about the underlying `data` list

## What We Tried

See **BATTERIES_BUILD_SUCCESS.md** for details on:
- Your original proofs (excellent structure!)
- Specific compilation errors we encountered
- Why each approach didn't work

## Why This Matters

These 6 lemmas are the last barrier to having a fully proven base case for the key-based HashMap refactor. They're standard library properties, not domain-specific assumptions.

## Thank You!

Your proofs had the right structure and ideas. We just need them adapted to this specific Lean version and API. If you can test in this exact environment, that would be ideal!

---

**Files to read for context:**
- This file (REQUEST_FOR_ORUZI.md)
- BATTERIES_BUILD_SUCCESS.md (detailed error analysis)
- Metamath/KernelExtras.lean (current axiom declarations)
