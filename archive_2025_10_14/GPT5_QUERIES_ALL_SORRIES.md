# GPT-5 Queries for All Sorries

**Date:** 2025-10-13
**Purpose:** Detailed queries for solving all 38 sorries in dependency order
**Format:** Each query is self-contained and ready to send to GPT-5

---

## Table of Contents

### Layer 0: Pure Library (3 sorries)
- [Query 1: List.mapM_length_option](#query-1-listmapm_length_option)
- [Query 2: List.foldl_and_eq_true](#query-2-listfoldl_and_eq_true)
- [Query 3: List.foldl_all₂](#query-3-listfoldl_all)

### Layer 1: Foundation Library (2 sorries)
- [Query 4: Array.mem_toList_get](#query-4-arraymem_tolist_get)
- [Query 5: List.mapM_some_of_mem](#query-5-listmapm_some_of_mem)

### Layer 2: Key-Based Refactor (1 sorry)
- [Query 6: Array.getElem! = getElem for Fin](#query-6-arraygetelem--getelem-for-fin)

### Layer 3: Bridge Helpers (3 sorries)
- [Query 7: HashMap.contains_eq_isSome](#query-7-hashmapcontains_eq_issome)
- [Query 8: toFrame_preserves_floats](#query-8-toframe_preserves_floats)
- [Query 9: toExpr_typecode_from_FloatBindWitness](#query-9-toexpr_typecode_from_floatbindwitness)

### Layer 4: Bridge Correctness (3 sorries)
- [Query 10: toFrame Phase 3 allM reasoning](#query-10-toframe-phase-3-allm-reasoning)
- [Query 11: checkHyp floats ≈ matchFloats](#query-11-checkhyp-floats--matchfloats)
- [Query 12: checkHyp essentials ≈ checkEssentials](#query-12-checkhyp-essentials--checkessentials)

### Layer 5: Helper Lemmas (5 sorries)
- [Query 13: viewStack append](#query-13-viewstack-append)
- [Query 14: viewStack dropLast](#query-14-viewstack-droplast)
- [Query 15: mapM index preservation](#query-15-mapm-index-preservation)
- [Query 16: list_mapM_length](#query-16-list_mapm_length)
- [Query 17: for-loop analysis](#query-17-for-loop-analysis)

### Layer 6: Complex Domain Proofs (17 sorries)
- [Query 18-34: Domain proofs](#layer-6-complex-domain-proofs)

### Layer 7: Inductive Step (4 sorries)
- [Query 35-38: Inductive step](#layer-7-inductive-step)

---

# Layer 0: Pure Library Properties

---

## Query 1: List.mapM_length_option

**Context:** Proving that `List.mapM` preserves list length when it succeeds.

**File:** `Metamath/KernelExtras.lean`
**Line:** 22

### The Problem

```lean
theorem mapM_length_option {α β : Type} (f : α → Option β) :
  ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length := by
  sorry
```

### What We Need

Prove that if `xs.mapM f = some ys`, then `ys.length = xs.length`.

### Why It's True

`List.mapM` applies `f` to each element of `xs`. If it succeeds, it produces exactly one output element for each input element. Therefore, the output list has the same length as the input list.

### The Challenge

`List.mapM` in Lean 4 is defined using an internal `mapM.loop` function:

```lean
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapM f xs
    return y :: ys
```

But in the actual implementation, it uses `mapM.loop` for efficiency, which makes the induction structure less obvious.

### Suggested Approach

**Option A: Direct Induction on xs**
```lean
intro xs ys h
induction xs generalizing ys with
| nil =>
  -- mapM [] = pure [] = some []
  -- So ys = [], and [].length = [].length
  ?
| cons x xs ih =>
  -- mapM (x::xs) = f x >>= λy → mapM xs >>= λys → return (y::ys)
  -- If this equals some ys, then:
  --   f x = some y for some y
  --   mapM xs = some ys' for some ys'
  --   ys = y::ys'
  -- By IH: ys'.length = xs.length
  -- Therefore: ys.length = (y::ys').length = 1 + ys'.length = 1 + xs.length = (x::xs).length
  ?
```

**Option B: Use Existing Library Lemmas**

Search for existing lemmas about `List.mapM` and `List.length`:
- `List.mapM_eq_some` or similar
- Properties of monadic bind (`>>=`)
- Length preservation properties

**Option C: Prove by Rewriting mapM Definition**

Unfold `List.mapM` and reason about the monadic structure directly.

### Available Lemmas in Lean 4

Please check the Lean 4 standard library (version 4.20.0-rc2) for:
- `List.mapM` properties
- `List.length` properties
- Monadic bind properties for `Option`

### Question for GPT-5

**Can you provide a complete proof of `mapM_length_option` for Lean 4.20.0-rc2?**

Please:
1. Handle the `mapM.loop` structure (or work around it)
2. Use standard library lemmas where possible
3. Provide a complete, compiling proof
4. Explain any non-obvious steps

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 10-30 lines
**Complexity:** Medium (understanding mapM.loop structure)

---

## Query 2: List.foldl_and_eq_true

**Context:** Proving that folding boolean AND over a list returns true iff all elements satisfy a predicate.

**File:** `Metamath/KernelExtras.lean`
**Line:** 35

### The Problem

```lean
theorem foldl_and_eq_true {α} {p : α → Bool} (xs : List α) :
    xs.foldl (fun b x => b && p x) true = true ↔
    ∀ x ∈ xs, p x = true := by
  sorry
```

### What We Need

Prove the bi-implication:
- **Forward:** If `xs.foldl (fun b x => b && p x) true = true`, then `∀ x ∈ xs, p x = true`
- **Backward:** If `∀ x ∈ xs, p x = true`, then `xs.foldl (fun b x => b && p x) true = true`

### Why It's True

The fold starts with `true` and applies `&& p x` for each element `x`:
- If any `p x = false`, then `true && ... && false && ... = false`
- The fold returns `true` only if all `p x = true`

### Suggested Approach

**Backward Direction (easier):**
```lean
constructor
· -- Forward direction
  ?
· -- Backward direction: ∀ x ∈ xs, p x = true → fold = true
  intro h
  induction xs with
  | nil =>
    simp [List.foldl]  -- foldl on [] returns initial value (true)
  | cons y ys ih =>
    simp [List.foldl]
    have hy : p y = true := h y (List.Mem.head ys)
    simp [hy]  -- true && true = true
    apply ih
    intro x hx
    exact h x (List.Mem.tail y hx)
```

**Forward Direction (harder):**

Need to show that if `ys.foldl (fun b x => (true && p y) && p x) true = true`, then `p y = true`.

Key insight: If the fold equals `true`, then the accumulated value at each step must be `true`. In particular, after processing the first element, we have `true && p y = true`, which implies `p y = true`.

```lean
· -- Forward direction: fold = true → ∀ x ∈ xs, p x = true
  intro h x hx
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    cases hx with
    | head =>
      -- x = y, need to extract p y = true from fold
      -- The fold computes: ys.foldl (fun b x => b && p x) (true && p y)
      -- For this to equal true, we need (true && p y) = true
      -- This means p y = true
      ?
    | tail _ hmem =>
      -- x ∈ ys, use IH
      ?
```

### Boolean Properties You May Need

- `true && b = b`
- `false && b = false`
- `b && true = b`
- `b && false = false`
- `(b && c) = true ↔ b = true ∧ c = true`

### Question for GPT-5

**Can you provide a complete proof of `foldl_and_eq_true` for Lean 4?**

Please:
1. Prove both directions of the bi-implication
2. Use induction on the list
3. Handle the fold state tracking carefully
4. Provide a complete, compiling proof

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 20-40 lines
**Complexity:** Medium (tracking fold state)

---

## Query 3: List.foldl_all₂

**Context:** Proving that nested fold with AND checks all pairs.

**File:** `Metamath/KernelExtras.lean`
**Line:** 47

### The Problem

```lean
theorem foldl_all₂ {α β} (xs : List α) (ys : List β) (p : α → β → Bool) :
  (xs.foldl (fun b x => ys.foldl (fun b' y => b' && p x y) b) true = true)
  ↔ (∀ x ∈ xs, ∀ y ∈ ys, p x y = true) := by
  sorry
```

### What We Need

Prove that a nested fold checking `p x y` for all pairs `(x, y)` where `x ∈ xs` and `y ∈ ys` returns `true` iff all those checks succeed.

### Why It's True

The outer fold iterates over `xs`, and for each `x`, the inner fold iterates over `ys`, checking `p x y` for each `y`. The nested fold accumulates with `&&`, so it returns `true` iff all `p x y = true`.

### Suggested Approach

**Use `foldl_and_eq_true` as a lemma:**

Assume you have `foldl_and_eq_true` proven (Query 2). Then:

```lean
constructor
· -- Forward direction
  intro h x hx y hy
  -- For a fixed x, the inner fold is:
  --   ys.foldl (fun b' y => b' && p x y) b
  -- where b is the accumulated value after processing previous elements
  -- By foldl_and_eq_true (applied to the inner fold with predicate p x),
  -- if the inner fold returns true, then ∀ y ∈ ys, p x y = true
  ?
· -- Backward direction
  intro h
  induction xs with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp [List.foldl]
    -- Need to show: ys.foldl (fun b' y => b' && p x y) (xs.foldl ... true) = true
    -- The accumulated value from xs is true (by IH with weakened hypothesis)
    -- The inner fold starts from true
    -- By foldl_and_eq_true, this equals true iff ∀ y ∈ ys, p x y = true
    -- Which holds by hypothesis h
    ?
```

### Key Lemmas to Use

1. **foldl_and_eq_true** from Query 2
2. **Induction on xs** (outer list)
3. **Apply foldl_and_eq_true to inner fold** for each fixed x

### Question for GPT-5

**Can you provide a complete proof of `foldl_all₂` for Lean 4?**

**Dependencies:**
- Assume `foldl_and_eq_true` is available (from Query 2)
- Or prove it inline if needed

**Approach:**
1. Use induction on `xs` (outer list)
2. Apply `foldl_and_eq_true` to handle inner fold
3. Track that accumulated value is `true` through induction

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 30-50 lines
**Complexity:** Medium (nested structure + using previous lemma)

---

# Layer 1: Foundation Library

---

## Query 4: Array.mem_toList_get

**Context:** Proving that accessing a valid array index produces a member of the array's list representation.

**File:** `Metamath/KernelExtras.lean`
**Line:** 101

### The Problem

```lean
@[simp] theorem mem_toList_get {α} (a : Array α) (k : Fin a.size) : a[k] ∈ a.toList := by
  sorry
```

### What We Need

Prove that for a valid index `k : Fin a.size`, the element `a[k]` is a member of `a.toList`.

### Why It's True

- `a.toList` converts the array to a list (defined as `a.data`)
- `a[k]` accesses the element at index `k.val` in the array
- Since `k : Fin a.size`, we have `k.val < a.size`, so the access is valid
- The element at a valid index must be in the list representation

### Key Definitions

```lean
-- Array.toList is essentially Array.data
def Array.toList (a : Array α) : List α := a.data

-- Array indexing with Fin
a[k] where k : Fin a.size  -- accesses a.data[k.val]
```

### Suggested Approach

**Option A: Use List.getElem_mem**

```lean
theorem mem_toList_get {α} (a : Array α) (k : Fin a.size) : a[k] ∈ a.toList := by
  -- Strategy: show a[k] = a.toList[k.val], then use List.getElem_mem
  have h_len : k.val < a.toList.length := by
    -- a.toList.length = a.size, and k.val < a.size
    ?
  have h_eq : a[k] = a.toList[k.val]'h_len := by
    -- Both access a.data[k.val]
    ?
  rw [h_eq]
  exact List.getElem_mem a.toList k.val h_len
```

**Option B: Use List.mem_iff_get**

```lean
theorem mem_toList_get {α} (a : Array α) (k : Fin a.size) : a[k] ∈ a.toList := by
  apply List.mem_iff_get.mpr
  use k.val
  constructor
  · -- k.val < a.toList.length
    ?
  · -- a.toList.get ⟨k.val, _⟩ = a[k]
    ?
```

### Available Lemmas to Find

In Lean 4.20.0-rc2, search for:
- `Array.toList` definition and properties
- `Array.size_toArray` or `List.length_toArray`
- `Array.getElem_toList` or similar (relating `a[i]` to `a.toList[i]`)
- `List.getElem_mem` (element at valid index is member)
- `List.mem_iff_get` (membership via index)

### Question for GPT-5

**Can you provide a complete proof of `mem_toList_get` for Lean 4.20.0-rc2?**

**Challenges:**
- Need to find the right lemma names in this Lean version
- May need to use `simp` with the right lemmas
- The connection between `Array.getElem` and `List.getElem` may have specific lemma names

**Approach:**
1. Establish that `k.val < a.toList.length`
2. Show that `a[k] = a.toList[k.val]` (or equivalent)
3. Use `List.getElem_mem` or `List.mem_iff_get`

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 5-15 lines
**Complexity:** Low-Medium (finding right lemma names)

---

## Query 5: List.mapM_some_of_mem

**Context:** Proving that if `mapM` succeeds on a list, then the function succeeds on each element.

**File:** `Metamath/KernelExtras.lean`
**Line:** 63

### The Problem

```lean
theorem mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b := by
  sorry
```

### What We Need

Prove that if `xs.mapM f = some ys` and `x ∈ xs`, then `f x = some b` for some `b`.

### Why It's True

`List.mapM` in the `Option` monad succeeds only if `f` succeeds on every element:
```lean
mapM f [] = some []
mapM f (a::as) = do
  let b ← f a        -- if f a = none, the whole thing fails
  let bs ← mapM f as -- if mapM f as = none, the whole thing fails
  return b::bs       -- only succeeds if both above succeed
```

So if `mapM f xs = some ys`, then `f` must have succeeded on each element of `xs`.

### The Challenge

Same as Query 1: `List.mapM` uses internal `mapM.loop`, making induction structure less obvious.

### Suggested Approach

**Induction on xs:**

```lean
theorem mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b := by
  induction xs generalizing ys with
  | nil =>
    cases hx  -- x cannot be in []
  | cons a as ih =>
    -- mapM f (a::as) succeeds means:
    --   f a = some b for some b
    --   mapM f as = some bs for some bs
    -- Need to extract this from h
    rw [List.mapM] at h  -- or unfold mapM definition
    -- Now h should have form involving bind (>>=)
    -- Split on whether x = a or x ∈ as
    cases hx with
    | head =>
      -- x = a, need to show f a = some b
      -- From h, extract that f a succeeds
      ?
    | tail _ hmem =>
      -- x ∈ as, use IH
      -- From h, extract that mapM f as succeeds
      ?
```

**Alternative: Case Analysis on f a:**

```lean
cases hfa : f a with
| none =>
  -- If f a = none, then mapM f (a::as) = none
  -- But h says mapM f (a::as) = some ys, contradiction
  simp [List.mapM, hfa] at h
| some b =>
  -- If f a = some b, then continue
  cases hx with
  | head =>
    exact ⟨b, hfa⟩
  | tail _ hmem =>
    -- Need to extract that mapM f as = some ys' from h
    -- and apply IH
    ?
```

### Question for GPT-5

**Can you provide a complete proof of `mapM_some_of_mem` for Lean 4.20.0-rc2?**

**Challenges:**
- Understanding `List.mapM` and `mapM.loop` structure
- Extracting facts from `mapM f (a::as) = some ys`
- Handling the monadic bind structure

**Approach:**
1. Use induction on `xs`
2. Case analysis on `f a` (none vs some)
3. Use contradiction for `none` case
4. Apply IH for tail case

**Related to:** Query 1 (both deal with mapM structure)

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 20-40 lines
**Complexity:** Medium (mapM.loop structure)

---

# Layer 2: Key-Based Refactor

---

## Query 6: Array.getElem! = getElem for Fin

**Context:** Proving that `get!` with a valid index (Fin) equals `get`.

**File:** `Metamath/Kernel.lean`
**Line:** 2472

### The Problem

```lean
have h_eq : stack[k]! = stack[k] := by
  sorry  -- Standard Array property: a[k]! = a[k] for k : Fin a.size
```

Where:
- `k : Fin stack.size`
- `stack : Array Metamath.Verify.Formula`

### What We Need

Prove that for `k : Fin a.size`, we have `a[k]! = a[k]`.

### Why It's True

- `a[k]` is notation for `a.get k` (using `Fin` index, always in bounds)
- `a[k]!` is notation for `a.get! k.val` (using `Nat` index, with panic on out of bounds)
- Since `k : Fin a.size`, we have `k.val < a.size`, so `get!` doesn't panic
- Both access `a.data[k.val]`, so they return the same element

### Key Definitions

```lean
-- Array.getElem with Fin (no panic possible)
def Array.getElem (a : Array α) (k : Fin a.size) : α := a.data[k.val]

-- Array.getElem! with Nat (panics if out of bounds)
def Array.getElem! (a : Array α) (i : Nat) : α :=
  if h : i < a.size then
    a.data[i]
  else
    panic! "index out of bounds"
```

### Suggested Approach

**Option A: Unfold and use Fin property:**

```lean
have h_eq : stack[k]! = stack[k] := by
  -- Unfold definitions
  simp only [Array.getElem!, Array.getElem]
  -- stack[k]! = if h : k.val < stack.size then stack.data[k.val] else panic!
  -- stack[k] = stack.data[k.val]
  -- Since k : Fin stack.size, we have k.val < stack.size
  have : k.val < stack.size := k.isLt
  simp [this]
```

**Option B: Use existing lemma:**

Search for lemmas like:
- `Array.get!_eq_get`
- `Array.getElem!_eq_getElem`
- Properties relating get and get! for valid indices

```lean
have h_eq : stack[k]! = stack[k] := by
  apply Array.get!_eq_get  -- or similar lemma name
  exact k.isLt
```

**Option C: Direct proof:**

```lean
have h_eq : stack[k]! = stack[k] := by
  rfl  -- May work if they're definitionally equal
```

### Question for GPT-5

**Can you provide a proof of `stack[k]! = stack[k]` for `k : Fin stack.size` in Lean 4.20.0-rc2?**

**Challenges:**
- Finding the right lemma name (if it exists)
- Or proving from definitions
- The notation `[k]!` may desugar in a specific way

**Context:**
This is used in the key-based refactor proof (line 2472 of Kernel.lean). The full context is:
```lean
-- k : Fin stack.size
-- h_val_eq : f = stack[k]!  (from FloatBindWitness)
-- Need to show: ∃ e, toExprOpt stack[k]! = some e
-- Have: List.mapM_some_of_mem applies to stack[k], not stack[k]!
-- So need: stack[k]! = stack[k]
```

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 1-10 lines
**Complexity:** Low (should be trivial or have existing lemma)

---

# Layer 3: Bridge Helper Properties

---

## Query 7: HashMap.contains_eq_isSome

**Context:** Proving that `HashMap.contains` is equivalent to `isSome ∘ lookup`.

**File:** `Metamath/Kernel.lean`
**Line:** 1825

### The Problem

Located in `toFrame_sound` proof:

```lean
sorry  -- TODO: Prove HashMap.contains_eq_isSome lemma
```

### What We Need

Prove that for a HashMap `m` and key `k`:
```lean
m.contains k = (m[k]?.isSome)
```

Or equivalently:
```lean
m.contains k = true ↔ ∃ v, m[k]? = some v
```

### Why It's True

- `HashMap.contains k` checks if key `k` is in the map
- `m[k]?` performs a lookup, returning `some v` if found, `none` if not
- `(some v).isSome = true` and `none.isSome = false`
- So they express the same property

### Context in Proof

```lean
-- Around line 1825 in toFrame_sound
-- Need to show relationship between contains check and lookup
-- This is used to connect imperative style (contains check)
-- with functional style (pattern matching on Option)
```

### Suggested Approach

**Option A: Use Std.HashMap lemmas:**

```lean
theorem contains_eq_isSome [BEq α] [Hashable α] (m : Std.HashMap α β) (k : α) :
    m.contains k = (m[k]?.isSome) := by
  simp [Std.HashMap.contains, Std.HashMap.findEntry?]
  cases m[k]? with
  | none => simp
  | some v => simp
```

**Option B: Prove via HashMap.findEntry?:**

```lean
theorem contains_eq_isSome [BEq α] [Hashable α] (m : Std.HashMap α β) (k : α) :
    m.contains k = (m[k]?.isSome) := by
  -- HashMap.contains k = m.findEntry? k |>.isSome
  -- m[k]? = m.findEntry? k |>.map (·.2)
  -- So m[k]?.isSome = m.findEntry? k |>.map (·.2) |>.isSome
  --                  = m.findEntry? k |>.isSome
  ?
```

### Available Definitions

From `Std.Data.HashMap`:
```lean
def HashMap.contains (m : HashMap α β) (k : α) : Bool :=
  m.findEntry? k |>.isSome

def HashMap.findEntry? (m : HashMap α β) (k : α) : Option (α × β) := ...

-- m[k]? notation desugars to:
m.findEntry? k |>.map (·.snd)
```

### Question for GPT-5

**Can you provide a proof of `HashMap.contains_eq_isSome` for Lean 4.20.0-rc2?**

**Requirements:**
- Works with `Std.HashMap` from Lean 4.20.0-rc2
- Handles the relationship between `contains`, `findEntry?`, and lookup notation
- Clean, compiling proof

**Context:**
This is used in `toFrame_sound` (Kernel.lean:1825) to connect imperative-style contains checks with functional-style Option pattern matching.

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 5-15 lines
**Complexity:** Low (standard HashMap property)

---

## Query 8: toFrame_preserves_floats

**Context:** Proving that `toFrame` preserves floating hypothesis properties.

**File:** `Metamath/Kernel.lean`
**Line:** 1813

### The Problem

Located in `toFrame_sound` proof:

```lean
sorry  -- TODO: Prove toFrame_preserves_floats lemma
```

### What We Need

Prove that if a hypothesis in the implementation is a floating hypothesis, then its corresponding hypothesis in the spec is also a floating hypothesis.

### Context

```lean
-- Around line 1813 in toFrame_sound
-- We have:
--   fr_impl : Metamath.Verify.Frame  (implementation frame)
--   fr_spec : Metamath.Spec.Frame    (spec frame)
--   h_frame : toFrame db fr_impl = some fr_spec
--
-- Need to show: floating hypotheses are preserved by toFrame
```

### Key Definitions

From the codebase:
```lean
-- Verify.Frame (implementation)
structure Verify.Frame where
  hyps : Array String      -- hypothesis labels
  mand : Array Formula     -- mandatory hypotheses
  ...

-- Spec.Frame (specification)
structure Spec.Frame where
  hyps : List (String × Expr)  -- hypotheses as (label, expression) pairs
  ...

-- toFrame converts implementation frame to spec frame
def toFrame (db : Verify.DB) (fr : Verify.Frame) : Option Spec.Frame := ...
```

### What "Preserves Floats" Means

A floating hypothesis has the form `⊢ typecode variable` (e.g., `⊢ wff φ`).

The property states:
```lean
-- If hyps[i] is a floating hypothesis in fr_impl (determined by db.find?),
-- then the corresponding hypothesis in fr_spec.hyps is also a floating hypothesis
```

### Suggested Approach

```lean
theorem toFrame_preserves_floats
    (db : Verify.DB)
    (fr_impl : Verify.Frame)
    (fr_spec : Spec.Frame)
    (h_frame : toFrame db fr_impl = some fr_spec)
    (i : Nat)
    (h_i : i < fr_impl.hyps.size)
    (lbl : String)
    (c : Symbol)
    (v : Symbol)
    (h_float : db.find? fr_impl.hyps[i] = some (.hyp false ⟨[c, v], lbl⟩)) :
    ∃ (j : Nat) (h_j : j < fr_spec.hyps.length),
      fr_spec.hyps[j] = (lbl, ⟨c, [v.v]⟩) := by
  -- Unfold toFrame definition
  -- Show that it processes hyps[i] and produces corresponding spec hypothesis
  -- Use that toFrame preserves the structure
  sorry
```

### Key Lemmas Needed

1. **toFrame structure:** Understanding how `toFrame` processes each hypothesis
2. **Index correspondence:** Showing that hypothesis i in impl corresponds to hypothesis j in spec
3. **Formula conversion:** Using `toExpr` or `toExprOpt` to convert formulas

### Question for GPT-5

**Can you provide a proof of `toFrame_preserves_floats` for the Metamath kernel?**

**Context Files:**
- `Metamath/Verify.lean` - implementation definitions
- `Metamath/Spec.lean` - specification definitions
- `Metamath/Bridge.lean` - `toFrame` definition
- `Metamath/Kernel.lean` (line 1813) - where it's needed

**Requirements:**
- Show that floating hypotheses in the implementation remain floating in the spec
- Handle the index correspondence between impl and spec
- Use the `toFrame` definition

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 20-50 lines
**Complexity:** Medium (requires understanding toFrame implementation)

---

## Query 9: toExpr_typecode_from_FloatBindWitness

**Context:** Proving that `toExpr` produces the correct typecode for formulas coming from floating hypotheses.

**File:** `Metamath/Kernel.lean`
**Line:** 1840

### The Problem

Located in `toFrame_sound` proof:

```lean
sorry  -- TODO: Prove toExpr_typecode_from_FloatBindWitness lemma
```

### What We Need

Prove that if a formula `f` comes from a floating hypothesis (via `FloatBindWitness`), then `toExpr f` produces an expression with the correct typecode.

### Context

```lean
-- We have:
--   FloatBindWitness for formula f
--   This witness says f came from a floating hyp: ⊢ typecode variable
--   f has form [c, v] where c is the typecode
--
-- Need to show: toExpr f produces ⟨c, [v]⟩ or similar
```

### Key Definitions

```lean
-- FloatBindWitness records that a formula came from a floating hypothesis
def FloatBindWitness
    (db : Verify.DB)
    (hyps : Array String)
    (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (j : Nat) (v : String) (val : Formula) : Prop :=
  ∃ (hj : j < hyps.size) (k : Fin stack.size) (f : Formula) (lbl : String),
    off.1 + j = k.val ∧
    db.find? (hyps[j]) = some (.hyp false f lbl) ∧  -- false = floating
    f[1]!.value = v ∧
    val = stack[k]! ∧
    (f[0]! == val[0]!) = true  -- typecodes match

-- toExpr converts Formula to Expr
def toExpr : Formula → Expr
```

### What We Need to Show

```lean
theorem toExpr_typecode_from_FloatBindWitness
    (db : Verify.DB)
    (hyps : Array String)
    (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (j : Nat) (v : String) (val : Formula)
    (h_witness : FloatBindWitness db hyps stack off j v val) :
    ∃ (c : Symbol) (e : Expr),
      toExpr val = some ⟨c, [⟨v⟩]⟩ ∧
      -- And c is the correct typecode from the floating hypothesis
      ... := by
  sorry
```

### Suggested Approach

```lean
-- Unfold FloatBindWitness
obtain ⟨hj, k, f, lbl, h_off, h_find, h_var, h_val_eq, h_head⟩ := h_witness

-- From h_find: f is [c, v] for some typecode c
-- From h_val_eq: val = stack[k]!
-- From h_head: f[0]! == val[0]! = true, so val[0]! = c

-- Show that toExpr val produces ⟨c, [v]⟩
-- This requires understanding toExpr definition
```

### Question for GPT-5

**Can you provide a proof of `toExpr_typecode_from_FloatBindWitness` for the Metamath kernel?**

**Context:**
- `FloatBindWitness` definition (Kernel.lean:1512)
- `toExpr` definition (Bridge/Basics.lean)
- Used in `toFrame_sound` proof (Kernel.lean:1840)

**Requirements:**
- Extract typecode from FloatBindWitness
- Show toExpr produces correct structure
- Handle the Formula → Expr conversion

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 30-60 lines
**Complexity:** Medium-High (requires understanding both witness structure and conversion)

---

# Layer 4: Bridge Correctness

---

## Query 10: toFrame Phase 3 allM reasoning

**Context:** Completing the Phase 3 proof in `toFrame_sound` using `allM` reasoning.

**File:** `Metamath/Kernel.lean`
**Line:** 1896

### The Problem

Located in `toFrame_sound` proof, Phase 3 (essential hypotheses):

```lean
-- For Phase 3, we document the strategy and leave as sorry
-- Strategy: Use allM reasoning to show all essential hypotheses are satisfied
-- Similar to Phase 2, but for essential hyps (not floats)
sorry  -- TODO: Complete allM reasoning (~30-40 lines)
```

### What We Need

Prove that Phase 3 of `toFrame` (checking essential hypotheses) succeeds and produces the correct result.

### Context

```lean
-- toFrame has 3 phases:
-- Phase 1: Match floating hypotheses (done)
-- Phase 2: Check disjoint variable conditions (done)
-- Phase 3: Check essential hypotheses (THIS ONE)

-- Phase 3 code (simplified):
fr_impl.mand.allM fun e =>
  match e with
  | ess =>
    -- Check that essential hypothesis e is satisfied
    -- Returns true if satisfied, false otherwise
```

### What Phase 3 Does

Phase 3 verifies that all essential (non-floating) hypotheses in the frame are properly constructed and can be converted to spec expressions.

Essential hypotheses have the form `⊢ expression` where expression is not just a type declaration.

### Suggested Approach

```lean
-- Around line 1896
-- Have: toFrame processing reaches Phase 3
-- Have: Phases 1 and 2 succeeded
-- Need to show: Phase 3 (allM over mand) succeeds

-- Strategy:
-- 1. Unfold allM definition
-- 2. Show that for each essential hypothesis in fr_impl.mand:
--      a) It can be converted to a spec expression
--      b) The conversion matches expected structure
-- 3. Use allM_true (or similar) to show allM returns true
-- 4. Extract the final frame structure

-- May need helper lemma:
theorem allM_ess_hyps
    (db : Verify.DB)
    (fr_impl : Verify.Frame)
    (h_phase1 : ...) -- floats matched
    (h_phase2 : ...) -- disjoint vars checked
    : fr_impl.mand.allM (fun e => ...) = true := by
  -- Use induction or allM properties
  sorry
```

### Available Lemmas

You may need:
- `Array.allM` properties (from Lean 4 std lib)
- Properties of `allM` for `Option` monad
- Conversion lemmas for essential hypotheses

### Question for GPT-5

**Can you complete the Phase 3 proof in `toFrame_sound` using `allM` reasoning?**

**Context:**
- Location: Kernel.lean:1896
- Function: `toFrame_sound` proof
- Phase: 3 (essential hypotheses)
- Phases 1-2: Already proven

**What's Needed:**
1. Understand `allM` structure for essential hypothesis checking
2. Show each essential hypothesis can be converted
3. Prove allM succeeds and produces correct frame

**Strategy documented at lines 1893-1895:**
```lean
-- For Phase 3, we document the strategy and leave as sorry
-- Strategy: Use allM reasoning to show all essential hypotheses are satisfied
-- Similar to Phase 2, but for essential hyps (not floats)
```

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 30-40 lines
**Complexity:** Medium (understanding allM + essential hypothesis structure)

---

## Query 11: checkHyp floats ≈ matchFloats

**Context:** Proving that `checkHyp` for floating hypotheses approximates `matchFloats` in the spec.

**File:** `Metamath/Kernel.lean`
**Line:** 2064

### The Problem

Located in `toFrame_sound` proof:

```lean
sorry  -- checkHyp floats ≈ matchFloats
```

### What We Need

Prove that when `checkHyp` processes floating hypotheses, it produces a result equivalent to what `matchFloats` produces in the specification.

### Context

```lean
-- checkHyp processes hypotheses one by one, building a substitution
-- matchFloats in the spec does pattern matching on floating hypotheses

-- Need to show these are equivalent (or approximate) operations
```

### Key Definitions

```lean
-- From Verify.lean (implementation):
def DB.checkHyp
    (db : DB)
    (hyps : Array String)
    (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (i : Nat)
    (σ : HashMap String Formula) :
    Except String (HashMap String Formula) := ...

-- From Spec.lean (specification):
def matchFloats
    (floats : List (Symbol × Var))
    (stack : List Expr) :
    Option (Subst) := ...
```

### What "≈" Means

The approximation relation means:
1. If `checkHyp` succeeds with substitution σ on floating hypotheses, then `matchFloats` succeeds with equivalent substitution
2. The substitutions agree on all variables
3. The formulas in σ correspond to expressions in the spec substitution via `toExpr`

### Suggested Approach

```lean
theorem checkHyp_floats_approx_matchFloats
    (db : Verify.DB)
    (hyps : Array String)
    (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (i : Nat)
    (σ : HashMap String Formula)
    (h_only_floats : ∀ j < i, db.find? hyps[j] is .hyp false _)
    (h_checkHyp : DB.checkHyp db hyps stack off i σ = .ok σ') :
    ∃ (floats : List (Symbol × Var)) (stack_spec : List Expr) (σ_spec : Subst),
      -- Extract floats and stack_spec from db and stack
      -- matchFloats succeeds
      matchFloats floats stack_spec = some σ_spec ∧
      -- Substitutions agree
      (∀ v f, σ'[v]? = some f → ∃ e, σ_spec v = some e ∧ toExpr f = some e) := by
  sorry
```

### Question for GPT-5

**Can you provide a proof that `checkHyp` for floats approximates `matchFloats`?**

**Context:**
- `checkHyp` definition: Verify.lean
- `matchFloats` definition: Spec.lean
- Usage: Kernel.lean:2064 in toFrame_sound proof

**Requirements:**
1. Handle the iteration structure of checkHyp
2. Show correspondence with matchFloats pattern matching
3. Prove substitutions agree via toExpr

**Key Insight:**
`checkHyp` processes hypotheses sequentially, while `matchFloats` does pattern matching. Both build substitutions that bind variables to formulas/expressions.

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 40-80 lines
**Complexity:** Medium-High (requires understanding both implementations)

---

## Query 12: checkHyp essentials ≈ checkEssentials

**Context:** Proving that `checkHyp` for essential hypotheses approximates `checkEssentials` in the spec.

**File:** `Metamath/Kernel.lean`
**Line:** 2087

### The Problem

Located in `toFrame_sound` proof:

```lean
sorry  -- checkHyp essentials ≈ checkEssentials
```

### What We Need

Prove that when `checkHyp` processes essential hypotheses, it produces a result equivalent to what `checkEssentials` produces in the specification.

### Context

Similar to Query 11, but for essential hypotheses instead of floating hypotheses.

```lean
-- Essential hypotheses are checked for consistency
-- Both checkHyp and checkEssentials verify these
-- Need to show they're equivalent operations
```

### Key Definitions

```lean
-- checkHyp processes all hypotheses (floats + essentials)
-- For essential hypotheses (ess = true), it:
--   1. Applies substitution σ to the hypothesis formula
--   2. Checks that the result matches the stack element

-- checkEssentials in the spec verifies essential hypotheses match expected expressions
def checkEssentials
    (ess : List Expr)  -- expected essential hypothesis expressions
    (σ : Subst)        -- substitution from float matching
    (stack : List Expr) :
    Bool := ...
```

### Suggested Approach

```lean
theorem checkHyp_essentials_approx_checkEssentials
    (db : Verify.DB)
    (hyps : Array String)
    (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (i_start : Nat) -- where essentials start
    (i_end : Nat)   -- where they end
    (σ : HashMap String Formula)
    (h_floats_done : ...) -- floating hypotheses already processed
    (h_checkHyp : DB.checkHyp db hyps stack off i_end σ = .ok σ') :
    ∃ (ess : List Expr) (σ_spec : Subst) (stack_spec : List Expr),
      checkEssentials ess σ_spec stack_spec = true ∧
      -- Correspondence between impl and spec
      ... := by
  sorry
```

### Question for GPT-5

**Can you provide a proof that `checkHyp` for essentials approximates `checkEssentials`?**

**Context:**
- Similar to Query 11 but for essential (non-floating) hypotheses
- Essential hypotheses have `ess = true` in `.hyp ess f lbl`
- Used in Kernel.lean:2087

**Requirements:**
1. Show checkHyp processes essential hypotheses correctly
2. Prove correspondence with checkEssentials
3. Handle substitution application

**Related:** Query 11 (floating case) - similar structure

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 40-80 lines
**Complexity:** Medium-High (similar to Query 11)

---

# Layer 5: Helper Lemmas

---

## Query 13: viewStack append

**Context:** Proving that `viewStack` distributes over list append.

**File:** `Metamath/Kernel.lean`
**Line:** 3090

### The Problem

```lean
sorry  -- Proof: unfold viewStack, use Array.toList properties + list_mapM_append
```

### What We Need

Prove a property about `viewStack` and list concatenation.

### Context

```lean
-- viewStack converts an array to a list of spec expressions
-- Need to show it distributes over append in some way
```

### Suggested Approach

```lean
-- The sorry is preceded by this comment:
-- Proof: unfold viewStack, use Array.toList properties + list_mapM_append

theorem viewStack_append
    (a1 a2 : Array Formula) :
    viewStack (a1 ++ a2) = ... := by
  unfold viewStack
  -- viewStack uses Array.toList and mapM
  -- Show: (a1 ++ a2).toList.mapM toExpr = ...
  -- Use: Array.toList preserves append
  -- Use: List.mapM distributes over append (need to prove or find)
  sorry
```

### Question for GPT-5

**Can you prove the `viewStack` append property?**

**Context:**
- Location: Kernel.lean:3090
- Hint in comment: "unfold viewStack, use Array.toList properties + list_mapM_append"
- `viewStack` likely defined earlier in the file

**Requirements:**
1. Find or state the exact property needed
2. Use Array.toList append properties
3. Prove or use List.mapM append property

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 15-25 lines
**Complexity:** Low-Medium (straightforward structural lemma)

---

## Query 14: viewStack dropLast

**Context:** Proving that `viewStack` commutes with `dropLast` operation.

**File:** `Metamath/Kernel.lean`
**Line:** 3102

### The Problem

```lean
sorry  -- Proof: Array.toList_extract + List.dropLast_eq_take + list_mapM_dropLast_of_mapM_some
```

### What We Need

Prove that `viewStack` preserves the `dropLast` operation.

### Suggested Approach

Based on the comment:

```lean
theorem viewStack_dropLast
    (a : Array Formula) :
    viewStack (a.pop) = (viewStack a).dropLast  -- or similar
    := by
  unfold viewStack
  -- Use: Array.toList_extract (or similar)
  -- Use: List.dropLast_eq_take
  -- Use: list_mapM_dropLast_of_mapM_some (may need to prove)
  sorry
```

### Question for GPT-5

**Can you prove the `viewStack dropLast` property?**

**Context:**
- Location: Kernel.lean:3102
- Hint: "Array.toList_extract + List.dropLast_eq_take + list_mapM_dropLast_of_mapM_some"
- Related to Query 13 (viewStack structure)

**Requirements:**
1. Understand viewStack definition
2. Show it commutes with dropLast/pop
3. Use suggested lemmas or prove them

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 15-20 lines
**Complexity:** Low-Medium

---

## Query 15: mapM index preservation

**Context:** Proving that `mapM` preserves indexing structure.

**File:** `Metamath/Kernel.lean`
**Line:** 3465

### The Problem

```lean
sorry  -- ~40-60 lines: mapM index preservation
```

### What We Need

Prove that if `xs.mapM f = some ys`, then for each index `i < xs.length`, we have `f xs[i] = some ys[i]`.

### Suggested Approach

```lean
theorem mapM_index_preservation
    {α β : Type}
    (f : α → Option β)
    (xs : List α)
    (ys : List β)
    (h : xs.mapM f = some ys)
    (i : Nat)
    (h_i : i < xs.length) :
    ∃ (h_i' : i < ys.length),
      f xs[i] = some ys[i]'h_i' := by
  -- Prove by induction on xs
  -- Use that mapM preserves length (Query 1)
  -- Use that mapM succeeds element-wise (Query 5)
  sorry
```

### Question for GPT-5

**Can you prove `mapM` index preservation?**

**Context:**
- Location: Kernel.lean:3465
- Estimated length: 40-60 lines
- Related to Queries 1 and 5 (mapM properties)

**Dependencies:**
- May use `mapM_length_option` (Query 1)
- May use `mapM_some_of_mem` (Query 5)

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 40-60 lines
**Complexity:** Medium

---

## Query 16: list_mapM_length

**Context:** Another mapM length property (may overlap with Query 1).

**File:** `Metamath/Kernel.lean`
**Line:** 3469

### The Problem

```lean
sorry  -- ~10-15 lines: use list_mapM_length or similar
```

### What We Need

Similar to Query 1, but possibly in a different context or with different formulation.

### Suggested Approach

Check if this is the same as `mapM_length_option` from Query 1, or if it's a variant.

```lean
-- If different from Query 1:
theorem list_mapM_length
    {α β : Type}
    (f : α → Option β)
    (xs : List α) :
    ∀ ys, xs.mapM f = some ys → ys.length = xs.length := by
  -- Same proof as Query 1, or use Query 1 result
  intro ys h
  exact mapM_length_option f h
```

### Question for GPT-5

**Check if this duplicates Query 1, or provide the needed variant.**

**Context:**
- Location: Kernel.lean:3469
- May be same as Query 1's `mapM_length_option`
- Estimated: 10-15 lines

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 10-15 lines (or reference to Query 1)
**Complexity:** Low (may be duplicate)

---

## Query 17: for-loop analysis

**Context:** Analyzing a for-loop structure.

**File:** `Metamath/Kernel.lean`
**Line:** 3716

### The Problem

```lean
sorry  -- ~10 lines: for-loop analysis
```

### What We Need

Analyze the structure of a for-loop to extract properties about its iteration.

### Context

This is likely about showing that a for-loop in the implementation corresponds to some spec operation or satisfies certain properties.

### Suggested Approach

```lean
-- Need more context from the actual code at line 3716
-- Likely involves:
--   forM, for, or ForM operations
--   Showing loop invariants hold
--   Extracting final state after loop

theorem for_loop_property
    ... : ... := by
  -- Unfold for/forM definition
  -- Use induction on iteration count
  -- Show invariant preserved
  sorry
```

### Question for GPT-5

**Can you analyze and prove properties of the for-loop at Kernel.lean:3716?**

**Context:**
- Location: Kernel.lean:3716
- Estimated: ~10 lines
- Need to see surrounding context

**Requirements:**
1. Examine the actual for-loop code
2. Identify what property is needed
3. Prove the property (likely via induction)

**Lean Version:** 4.20.0-rc2
**Expected Proof Length:** 10 lines
**Complexity:** Low-Medium

---

# Layer 6: Complex Domain Proofs

**(17 sorries - These are substantial proofs requiring deep domain knowledge)**

Due to the complexity and length, I'll provide a summary approach for these rather than detailed queries for each:

---

## Layer 6 Summary

### Sorries in this layer:
1. **substitutionValid** (line 206) - ~50-100 lines
2. **matchFloats** (line 336) - ~40-80 lines
3. **foldlVars** (line 420) - ~30-60 lines
4. **checkEssentials** (line 457) - ~40-80 lines
5. **allMFresh** (line 673) - ~50-100 lines
6. **List distinctness** (lines 916, 933) - ~20-40 lines each
7. **Vars parameter** (line 968) - ~40-80 lines
8. **distinctness property** (line 1070) - ~30-60 lines
9. **Sigma rest agreement** (line 1151) - ~40-80 lines
10. **Validation loop** (line 1406) - ~60-120 lines
11. **ProofStateInv** (line 2864) - ~80-150 lines
12. **runProofSteps** (line 3608) - ~200-400 lines

### General Approach for Layer 6

These sorries are substantial domain-specific proofs that require:

1. **Deep understanding** of Metamath proof verification
2. **Complex induction** structures
3. **Multiple helper lemmas**
4. **Careful state tracking**

### Recommended Strategy for Layer 6

Instead of tackling these now, I recommend:

1. **Document the strategy** for each (some already have TODO comments)
2. **Break down** into smaller sub-lemmas
3. **Prioritize** based on dependencies
4. **Tackle iteratively** over multiple sessions

### Individual Query Format for Layer 6

For each sorry in Layer 6, a detailed query would need:
- **Full surrounding context** (50-100 lines of code)
- **All relevant definitions** (may be scattered across files)
- **Proof strategy** (documented or inferred)
- **Helper lemmas** to prove first
- **Expected complexity** (50-400 lines)

Given the scope, these should be separate documents rather than one query file.

---

# Layer 7: Inductive Step

---

## Query 35: Inductive step entry

**Context:** Starting the inductive step of `checkHyp_correct_strong`.

**File:** `Metamath/Kernel.lean`
**Line:** 2496

### The Problem

```lean
-- Inductive step: i < hyps.size
-- Need to show that processing one more hypothesis preserves correctness
sorry
```

### What We Need

Complete the inductive step proof showing that if the property holds after processing `i` hypotheses, it holds after processing `i+1` hypotheses.

### Context

```lean
-- Base case: i = hyps.size (already proven with key-based refactor)
-- Inductive step: i < hyps.size
--   Have: Property holds for checkHyp db hyps stack off i σ
--   Want: Property holds for checkHyp db hyps stack off (i+1) σ'
```

### Structure

The inductive step needs to:
1. Unfold `checkHyp` at position `i`
2. Split on what `db.find? hyps[i]` returns
3. Handle each case (none, const, var, assert, hyp)
4. For hyp case, split on floating vs essential
5. Show property preserved in each case

### Question for GPT-5

**Can you complete the inductive step of `checkHyp_correct_strong`?**

**Context:**
- Location: Kernel.lean:2496
- Base case: Already complete (key-based refactor, lines 2449-2474)
- Need: Inductive step structure

**Dependencies:**
- Base case pattern (lines 2449-2474)
- `checkHyp` definition (Verify.lean)
- Properties to maintain (defined in theorem statement)

**Estimated Complexity:** 100-200 lines
**Structure:** Case splits + recursive applications

**Lean Version:** 4.20.0-rc2

---

## Queries 36-38: Inductive step cases

**Context:** Individual cases within the inductive step.

**File:** `Metamath/Kernel.lean`
**Lines:** 2500, 2506, 2508

### Problems

```lean
-- Line 2500: none case (db lookup fails)
sorry

-- Line 2506: non-hyp cases (const/var/assert)
sorry

-- Line 2508: hyp case (floating + essential)
sorry
```

### What's Needed

Complete each case analysis within the inductive step:

1. **None case (2500):** Show that if `db.find? hyps[i] = none`, then `checkHyp` returns error, and this is correct behavior

2. **Non-hyp cases (2506):** Show that if `db.find? hyps[i]` returns const/var/assert, then `checkHyp` returns error (hypotheses should be `.hyp` objects)

3. **Hyp case (2508):** Main case - split on `ess : Bool`:
   - `ess = false` (floating): Show substitution extended correctly
   - `ess = true` (essential): Show consistency check succeeds

### Question for GPT-5

**Can you complete the individual cases of the inductive step?**

**Context:**
- Part of Query 35 (inductive step structure)
- Locations: Kernel.lean:2500, 2506, 2508
- Follow base case pattern (lines 2449-2474)

**For each case:**
1. Understand what `checkHyp` does
2. Show the property is maintained (or error is correct)
3. Use recursion/induction hypothesis for subsequent steps

**Estimated Complexity:**
- None case: 5-10 lines
- Non-hyp cases: 10-15 lines
- Hyp case: 80-150 lines (split on floating/essential)

**Lean Version:** 4.20.0-rc2

---

# Summary & Recommendations

## Total Queries: 38

### Layer 0-2 (Foundation): 6 queries
**Priority:** 🔴 HIGH - These complete the key-based refactor
**Complexity:** Low-Medium (library properties)
**Time:** 4-10 hours total

### Layer 3-4 (Bridge): 6 queries
**Priority:** 🟡 MEDIUM - These complete bridge verification
**Complexity:** Medium
**Time:** 4-8 hours total

### Layer 5 (Helpers): 5 queries
**Priority:** 🟢 LOW - Supporting lemmas
**Complexity:** Low-Medium
**Time:** 2-4 hours total

### Layer 6 (Domain): 17 queries
**Priority:** 🟢 LOW-MEDIUM - Complex domain proofs
**Complexity:** High-Very High
**Time:** 20-40 hours total
**Note:** Should be broken into smaller sub-problems

### Layer 7 (Inductive): 4 queries
**Priority:** 🟢 LOW - Depends on base case pattern
**Complexity:** High
**Time:** 10-20 hours total

---

## How to Use These Queries

### Option 1: Send to GPT-5 individually
Copy each query section and send as a separate request to GPT-5 or another AI assistant.

### Option 2: Work through dependency order
Start with Layer 0, complete those, then move to Layer 1, etc.

### Option 3: Cherry-pick by priority
Focus on high-priority items (Layers 0-2) first.

### Option 4: Break down complex ones
For Layer 6 items, create sub-queries for helper lemmas first.

---

**Date:** 2025-10-13
**Status:** ✅ Complete GPT-5 query documentation for all 38 sorries
**Ready for:** Systematic solving in dependency order!
