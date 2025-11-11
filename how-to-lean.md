# How to Lean: Practical Guide from the Metamath Verifier Project

**Quick reference for Lean 4 theorem proving techniques discovered while eliminating axioms from a Metamath verifier.**

---

## Table of Contents

1. [Induction Patterns (Core Techniques)](#induction)
2. [Working Around Parser Bugs](#parser-bug)
3. [Boolean vs Propositional Equality](#boolean-equality)
4. [GetElem Notation](#getelem-notation)
5. [Dependent Type Matching](#dependent-types)
6. [Complete Examples](#examples)
7. [Quick Reference](#quick-ref)

---

## <a name="induction"></a>1. Induction Patterns (CRITICAL)

### THE GOLDEN RULE: Generalize Accumulators

**When proving properties of folds, ALWAYS use `generalizing`:**

```lean
-- ❌ WRONG - IH won't apply to modified accumulator
theorem fold_bad (xs : List Nat) :
    xs.foldl (fun a x => a + x) 0 = xs.sum := by
  induction xs with
  | cons x xs ih =>
      -- ih : xs.foldl (fun a x => a + x) 0 = xs.sum
      -- But actual fold uses (0 + x), not 0!
      sorry

-- ✅ RIGHT - Generalize the accumulator
theorem fold_good (xs : List Nat) (acc : Nat) :
    xs.foldl (fun a x => a + x) acc = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp [List.foldl, List.sum]
  | cons x xs ih =>
      simp only [List.foldl, List.sum]
      rw [ih]  -- Now IH applies to (acc + x)!
      omega
```

**Why this matters:** Without `generalizing`, the induction hypothesis is specialized to the initial accumulator value and won't apply after the first fold step.

**See:** `Lean Curriculum/02_FoldInduction.lean` for complete examples

---

### Pattern 1: Basic List Induction

```lean
theorem example_list_induction (xs : List α) (P : List α → Prop) :
    P xs := by
  induction xs with
  | nil =>
      -- Base case: P []
      sorry
  | cons x xs ih =>
      -- Inductive case: P xs → P (x :: xs)
      -- ih : P xs
      sorry
```

**Use when:** Proving properties of recursive list operations

---

### Pattern 2: Monadic Fold Induction

```lean
-- When step function never fails
theorem foldlM_pattern (xs : List α) (init : β) :
    xs.foldlM f init = some result := by
  induction xs generalizing init with
  | nil =>
      simp [List.foldlM]
  | cons x xs ih =>
      simp [List.foldlM, f]
      rw [ih]  -- IH applies to f init x
      sorry
```

**Use when:** Proving properties of `List.foldlM` with Option/Except monad

**See:** `Lean Curriculum/03_MonadicFolds.lean` for working examples

---

### Pattern 3: Case Analysis in Monadic Folds

**When step function CAN fail, case on success/failure:**

```lean
theorem foldlM_with_failure (xs : List α) (h : xs.foldlM f init = .ok result) :
    property_of result := by
  -- Create helper with generalized accumulator
  have helper : ∀ (acc : β),
      xs.foldlM f acc = .ok result →
      property_of result := by
    intro acc h_fold
    induction xs generalizing acc result with
    | nil =>
        simp [List.foldlM] at h_fold
        exact h_fold ▸ ...
    | cons x xs ih =>
        simp [List.foldlM] at h_fold
        -- CRITICAL: Case on whether step succeeded
        cases h_step : f acc x with
        | error _ =>
            -- Fold failed, contradicts h_fold : ... = .ok
            simp [h_step] at h_fold
        | ok acc' =>
            -- Fold continued with acc'
            simp [h_step] at h_fold
            -- Use IH with new accumulator
            exact ih acc' h_fold
  -- Apply helper with initial accumulator
  exact helper init h
```

**Use when:** Proving properties when `foldlM` step can return `.error`

**See:** `Lean Curriculum/06_FoldWithCaseAnalysis.lean` for complete pattern

---

### Pattern 4: List Splitting (Array/List Bridge)

**Convert size bounds to structural patterns:**

```lean
-- Given: 0 < xs.length
-- Need: xs = head :: tail

theorem list_split_pattern (xs : List α) (h : 0 < xs.length) :
    ∃ head tail, xs = head :: tail := by
  cases xs with
  | nil =>
      -- 0 < [].length is false
      simp at h
  | cons head tail =>
      -- xs = head :: tail
      exact ⟨head, tail, rfl⟩
```

**Use when:** Working with array bounds (`0 < a.size`) but need list structure for induction

**See:** `Lean Curriculum/04_ListSplitting.lean`

---

## <a name="parser-bug"></a>2. Working Around Parser Bugs

### Lean 4.24.0 Nested Case Bug

**Problem:** After multiple nested `cases`, subsequent tactics fail with "unknown tactic" error.

**Solution:** Extract nested case analysis into helper function using term-mode `if-then-else`:

```lean
-- Main theorem delegates after safe case splits
theorem main_theorem : ... := by
  cases h1 with
  | inl ... => ...
  | inr h2 =>
      cases h2 with
      | inl ... => ...
      | inr h3 =>
          exact helper_function h3  -- Delegate here!

-- Helper uses term-mode (avoids tactic parser)
private theorem helper_function (h3 : ...) : ... :=
  if h : condition then
    -- True branch
    ⟨result1, by simp [h]⟩
  else
    -- False branch
    ⟨result2, by omega⟩
```

**Key:** Term-mode `if-then-else` avoids tactic-level machinery that triggers the bug.

**See:** `Metamath/ArrayListExt.lean:269-319` for `mapM_get_some_cons_helper`

---

## <a name="boolean-equality"></a>3. Boolean vs Propositional Equality

### The Bridge: LawfulBEq

Lean has two equality types:
- **Boolean**: `x == y : Bool` (computable, used by `List.idxOf`)
- **Propositional**: `x = y : Prop` (logical, used in theorems)

**Upgrade from boolean to propositional:**

```lean
-- Given: (x == y) = true
-- Want: x = y

have h_prop : x = y := LawfulBEq.eq_of_beq h_bool
```

**Reverse direction (propositional → boolean):**

```lean
-- Given: x = y
-- Want: (x == y) = true

have h_bool : (x == y) = true := by simp [h_prop]
```

**Reflexivity:**

```lean
-- (x == x) = true
-- No specific lemma, use simp:
have : (x == x) = true := by simp
```

### Common Pattern with idxOf

```lean
theorem getElem!_idxOf [BEq α] [LawfulBEq α] [Inhabited α]
    {xs : List α} {x : α} (hx : x ∈ xs) :
    xs[xs.idxOf x]! = x := by
  -- 1. Membership → valid index
  have hi : xs.idxOf x < xs.length :=
    List.idxOf_lt_length_iff.mpr hx

  -- 2. At that index, boolean equality holds
  have hbeq : (xs.get ⟨xs.idxOf x, hi⟩ == x) = true :=
    @List.findIdx_getElem _ (· == x) xs hi

  -- 3. Upgrade to propositional equality
  have hget : xs.get ⟨xs.idxOf x, hi⟩ = x :=
    LawfulBEq.eq_of_beq hbeq

  -- 4. Bridge notation (see next section)
  ...
```

**Key theorems:**
- `LawfulBEq.eq_of_beq : (x == y) = true → x = y`
- Use `simp [h]` for reverse direction

**See:** `Metamath/ArrayListExt.lean:227-255`

---

## <a name="getelem-notation"></a>4. GetElem Notation

### Bridging `xs[i]!` to `xs.get`

The notation `xs[i]!` is syntactic sugar that needs unfolding:

```lean
-- Goal: xs[i]! = x
-- Have: xs.get ⟨i, hi⟩ = x (where hi : i < xs.length)

-- Step 1: Unfold notation
unfold getElem! instGetElem?NatLtLength

-- Step 2: Simplify if-then-else using bounds
simp [hi]  -- where hi : i < xs.length

-- Step 3: Now xs[i] is definitionally xs.get ⟨i, hi⟩
exact hget
```

**Complete pattern:**

```lean
theorem getElem!_example {xs : List α} {i : Nat} {x : α}
    (hi : i < xs.length)
    (hget : xs.get ⟨i, hi⟩ = x) :
    xs[i]! = x := by
  unfold getElem! instGetElem?NatLtLength
  simp [hi]
  exact hget
```

---

## <a name="dependent-types"></a>5. Dependent Type Matching

### Using `subst` Effectively

```lean
theorem example (i : Fin n) (h : i = ⟨0, by simp⟩) : ... := by
  subst h  -- Replaces i everywhere with ⟨0, by simp⟩
  simp
```

**When NOT to use:** If equality is `some a = some b`, use `cases` to avoid variable renaming.

### Term-Mode vs Tactic-Mode

**Prefer term-mode for dependent matching:**

```lean
-- ✅ GOOD: Term-mode if-then-else
if h : i.val = 0 then
  have i_eq : i = ⟨0, by simp⟩ := Fin.ext h
  ⟨result, by subst i_eq; simp⟩
else
  have h_pos : 0 < i.val := Nat.pos_of_ne_zero h
  ⟨result, by omega⟩

-- ❌ AVOID: Tactic-mode cases (can trigger parser bugs)
cases i with
| zero => ...
| succ n => ...
```

---

## <a name="examples"></a>6. Complete Examples

### Example 1: Monadic Fold (No Failure)

```lean
def add_step (acc : Nat) (x : Nat) : Option Nat := some (acc + x)

theorem option_fold_sum (xs : List Nat) (init : Nat) :
    xs.foldlM add_step init = some (init + xs.sum) := by
  induction xs generalizing init with
  | nil =>
      simp [List.foldlM, List.sum]
  | cons x xs ih =>
      simp [List.foldlM, add_step]
      rw [ih]
      simp [List.sum]
      omega
```

**Key techniques:**
- `generalizing init` for accumulator threading
- `simp [List.foldlM]` to unfold monadic bind
- `rw [ih]` applies IH to new accumulator

**From:** `Lean Curriculum/03_MonadicFolds.lean:46-57`

---

### Example 2: BEq to Propositional Equality

```lean
theorem getElem!_idxOf [BEq α] [LawfulBEq α] [Inhabited α]
    {xs : List α} {x : α} (hx : x ∈ xs) :
    xs[xs.idxOf x]! = x := by
  -- Bound
  have hi : xs.idxOf x < xs.length :=
    List.idxOf_lt_length_iff.mpr hx

  -- Boolean equality at index
  have hbeq : (xs.get ⟨xs.idxOf x, hi⟩ == x) = true :=
    @List.findIdx_getElem _ (· == x) xs hi

  -- Upgrade to propositional
  have hget : xs.get ⟨xs.idxOf x, hi⟩ = x :=
    LawfulBEq.eq_of_beq hbeq

  -- Bridge notation
  unfold getElem! instGetElem?NatLtLength
  simp [hi]
  exact hget
```

**Key techniques:**
1. `idxOf_lt_length_iff` for bounds
2. `findIdx_getElem` for boolean predicate
3. `LawfulBEq.eq_of_beq` for upgrading equality
4. Unfold + simplify for notation bridging

**From:** `Metamath/ArrayListExt.lean:227-255`

---

### Example 3: Avoiding Parser Bug with Helper

```lean
-- Main theorem delegates after safe splits
theorem mapM_get_some : ... := by
  induction xs with
  | cons x xs ih =>
      cases hfx : f x with
      | some b =>
          cases h' : List.mapM f xs with
          | some ys' =>
              -- Delegate to avoid further nesting
              exact mapM_helper f x xs ih b hfx ys' h' ...

-- Helper uses term-mode
private theorem mapM_helper ... :=
  if h : i.val = 0 then
    have i_eq : i = ⟨0, by simp⟩ := Fin.ext h
    ⟨b, by subst i_eq; simp [hfx]⟩
  else
    have h_pos : 0 < i.val := Nat.pos_of_ne_zero h
    ⟨b', by omega⟩
```

**Key techniques:**
1. Extract to helper after 2-3 nested cases
2. Use term-mode `if-then-else`
3. Use `Fin.ext` for Fin equality
4. Use `subst` for clean dependent matching

**From:** `Metamath/ArrayListExt.lean:269-319`

---

## <a name="quick-ref"></a>7. Quick Reference

### Induction Patterns

```lean
-- Basic list induction
induction xs with | nil => | cons x xs ih =>

-- Fold induction (MUST generalize!)
induction xs generalizing acc with

-- Monadic fold (simple)
induction xs generalizing init with
| cons x xs ih => simp [List.foldlM, f]; rw [ih]

-- Monadic fold (with failure)
cases h_step : f acc x with
| error _ => simp [h_step] at h_fold  -- contradiction
| ok acc' => simp [h_step] at h_fold  -- continue
```

### Key Library Lemmas

```lean
-- List indexing and membership
List.idxOf_lt_length_iff : x ∈ xs ↔ xs.idxOf x < xs.length
List.findIdx_getElem : p (xs.get ⟨findIdx p xs, h⟩) = true

-- Boolean/Propositional bridge
LawfulBEq.eq_of_beq : (x == y) = true → x = y

-- Array/List interop
Array.getElem_eq_toList_getElem : xs[i] = xs.toList[i]
```

### Common Tactics

```lean
-- Unfold definitions
unfold getElem! instGetElem?NatLtLength

-- Simplify with context
simp [h1, h2]

-- Apply induction hypothesis
rw [ih]

-- Arithmetic reasoning
omega

-- Dependent equality
subst h  -- Replace all occurrences

-- Fin equality
Fin.ext : i.val = j.val → i = j
```

### Debugging Commands

```lean
-- See goal state
#check List.foldlM
trace "{goal}"

-- Get simp suggestions
simp?

-- Test typeclass resolution
#check (inferInstance : LawfulBEq Nat)
```

---

## Curriculum Resources

**Full learning path:** `/Lean Curriculum/`

- **Lesson 1**: Basic List Induction (foundation)
- **Lesson 2**: Fold Induction (generalizing pattern) ⭐
- **Lesson 3**: Monadic Folds (foldlM with Option/Except)
- **Lesson 4**: List Splitting (Array/List bridge)
- **Lesson 5**: Function Pattern Mismatch (lambda equivalence)
- **Lesson 6**: FoldlM Case Analysis (success/failure) ⭐

**Documentation:**
- `README.md` - Complete curriculum guide
- `STUCK_PROOF_PATTERNS.md` - Maps stuck proofs to lessons
- `PATTERN_VIOLATIONS.md` - Error isolation
- `QUICK_REFERENCE.md` - One-page cheat sheet

**Total:** 30+ working theorems with detailed examples

---

## Summary: The Three Most Important Patterns

### 1. ALWAYS Generalize Accumulators in Folds

```lean
induction xs generalizing acc with
```

Without this, your IH won't apply after the first fold step.

### 2. Case on Success/Failure in Monadic Folds

```lean
cases h_step : f acc x with
| error _ => simp [h_step] at h  -- contradiction
| ok acc' => exact ih acc' h     -- continue with new acc
```

### 3. Avoid Parser Bugs with Term-Mode

```lean
-- Extract to helper, use if-then-else instead of cases
if h : condition then ⟨result1, by simp⟩ else ⟨result2, by omega⟩
```

---

## Further Reading

- **Lean 4 Manual**: https://lean-lang.org/lean4/doc/
- **Theorem Proving in Lean 4**: https://lean-lang.org/theorem_proving_in_lean4/
- **Mathlib4 Docs**: https://leanprover-community.github.io/mathlib4_docs/
- **Zulip Chat**: https://leanprover.zulipchat.com/

---

**Document version:** 2.0 (2025-11-09)
- Added induction patterns section (curriculum insights)
- Corrected LawfulBEq documentation (removed non-existent `beq_of_eq`)
- Reorganized for quick reference
- Added curriculum resource pointers
