/-
Array and List infrastructure lemmas for Metamath verification.

This module centralizes array/list bridge theorems and infrastructure axioms.
These are standard library properties that should eventually be proven or
migrated to Batteries.

After Lean 4.24.0 + Batteries v4.24.0 upgrade (November 2025):
- Several axioms were eliminated using Batteries-provided lemmas
- Remaining axioms have documented proof strategies in AXIOMS.md
-/

import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas

/-! ## List helpers -/

namespace List

/-- Drop the last n elements from a list.
    Equivalent to taking the first (length - n) elements.
    Note: The builtin List.dropLast (no argument) drops exactly 1 element.
    This version `dropLastN` takes n : Nat and drops the last n elements.
-/
def dropLastN (xs : List α) (n : Nat) : List α :=
  xs.take (xs.length - n)

/-- dropLastN n is equivalent to take (length - n). -/
@[simp] theorem dropLastN_eq_take (xs : List α) (n : Nat) :
  xs.dropLastN n = xs.take (xs.length - n) := rfl

/-- take n is equivalent to dropLastN (length - n). -/
theorem take_eq_dropLastN (xs : List α) (n : Nat) (h : n ≤ xs.length) :
  xs.take n = xs.dropLastN (xs.length - n) := by
  rw [dropLastN_eq_take]
  congr 1
  omega

/-! ### List.mapM axioms

These are fundamental Option.mapM properties. Proofs encounter mapM.loop
expansion issues - the monadic bind structure doesn't simplify cleanly.

See AXIOMS.md for documented proof strategies.
-/

/-- If mapM succeeds, the result has the same length as the input.

This is a fundamental property of Option.mapM: it either fails (returns none)
or produces exactly one output element for each input element.

Oruži provided a proof using case-splitting on f x and xs.mapM f, but
simp [List.mapM] doesn't expand past mapM.loop in Lean 4.20.0-rc2.
This still requires mapM.loop lemmas in Lean 4.24.0.
-/
axiom mapM_length_option {α β : Type} (f : α → Option β) :
  ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length

/-- Helper: folding && with false always gives false. -/
private theorem foldl_and_false {α} (xs : List α) (p : α → Bool) :
    xs.foldl (fun b x => b && p x) false = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.foldl, ih]

/-- Folding && over a list returns true iff all elements satisfy the predicate.

Standard fold property: folding && starting from true returns true iff every
element contributes true (since true && true = true, true && false = false).
-/
@[simp] theorem foldl_and_eq_true {α} {p : α → Bool} (xs : List α) :
    xs.foldl (fun b x => b && p x) true = true ↔
    ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    rw [List.foldl]
    constructor
    · intro h y hy
      cases hy with
      | head =>
        cases hpx : p x
        · simp [hpx, foldl_and_false] at h
        · rfl
      | tail _ hmem =>
        cases hpx : p x
        · simp [hpx, foldl_and_false] at h
        · simp [hpx] at h
          exact ih.mp h y hmem
    · intro h
      have hx : p x = true := h x (List.mem_cons_self ..)
      simp [hx]
      apply ih.mpr
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

/-- Nested fold starting with false accumulator always returns false. -/
private theorem foldl_nested_false {α β} (xs : List α) (ys : List β) (p : α → β → Bool) :
    xs.foldl (fun b x => ys.foldl (fun b' y => b' && p x y) b) false = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldl, foldl_and_false, ih]

/-- Nested fold with && returns true iff predicate holds for all pairs.

Extension of foldl_and_eq_true to two lists. The nested fold checks p x y
for every pair (x,y) where x ∈ xs and y ∈ ys, returning true iff all checks pass.
-/
theorem foldl_all₂ {α β} (xs : List α) (ys : List β) (p : α → β → Bool) :
  (xs.foldl (fun b x => ys.foldl (fun b' y => b' && p x y) b) true = true)
  ↔ (∀ x ∈ xs, ∀ y ∈ ys, p x y = true) := by
  induction xs with
  | nil =>
    simp [List.foldl]
  | cons x xs ih =>
    rw [List.foldl]
    constructor
    · -- Forward direction: fold succeeds → all pairs satisfy p
      intro h z hz w hw
      -- First extract that inner fold must be true
      have h_inner : ys.foldl (fun b' y => b' && p x y) true = true := by
        match h_eq : ys.foldl (fun b' y => b' && p x y) true with
        | true => rfl
        | false =>
          -- Contradiction: h_eq = false implies outer fold = false
          rw [h_eq, foldl_nested_false] at h
          nomatch h
      cases hz with
      | head =>
        -- z = x: use h_inner
        exact (foldl_and_eq_true ys).mp h_inner w hw
      | tail _ hmem =>
        -- z ∈ xs: rewrite h using h_inner, then apply IH
        rw [h_inner] at h
        exact ih.mp h z hmem w hw
    · -- Backward direction: all pairs satisfy p → fold succeeds
      intro h
      -- First show inner fold = true
      have h_inner : ys.foldl (fun b' y => b' && p x y) true = true := by
        apply (foldl_and_eq_true ys).mpr
        intro w hw
        exact h x (List.mem_cons_self ..) w hw
      -- Rewrite goal using h_inner
      rw [h_inner]
      -- Now use IH
      apply ih.mpr
      intro z hz w hw
      exact h z (List.mem_cons_of_mem x hz) w hw

/-- If mapM succeeds on a list, then f succeeds on each element.

Fundamental Option.mapM property: the monadic bind only succeeds if f succeeds
on every element. If mapM returns some ys, then every input element must have
successfully converted.

Oruži provided a proof with direct induction, but again hits mapM.loop
expansion issues when trying to extract the success proof.
-/
axiom mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b

/-- If an element is in a list (with BEq), then indexing by idxOf succeeds.

Correspondence between membership and indexing. If x ∈ xs, then xs.idxOf x
returns a valid index that retrieves x.

Proof strategy: use List.idxOf properties from Batteries if available,
otherwise prove by induction showing idxOf returns i < length and xs[i] = x.
-/
axiom getElem!_idxOf {α : Type _} [BEq α] [Inhabited α] {xs : List α} {x : α} (h : x ∈ xs) :
  xs[xs.idxOf x]! = x

end List

/-! ### Namespaced List.mapM axioms

These live in a separate namespace to avoid clutter in the List namespace.
They represent more specialized mapM properties.
-/

namespace KernelExtras.List

/-- If mapM succeeds, then indexing the result corresponds to mapping the input.

For any valid index i, if xs.mapM f = some ys, then ys[i] is the result of
applying f to xs[i].
-/
axiom mapM_get_some {α β} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) (i : Fin xs.length) (h_len : i.val < ys.length) :
    ∃ b, f xs[i] = some b ∧ ys[i.val]'h_len = b

/-- MapM preserves append structure.

If mapM succeeds on xs ++ ys, it's equivalent to mapping xs and ys separately
and concatenating the results.

Needed for Task 3.1 viewStack_push proof.
-/
axiom list_mapM_append {α β} (f : α → Option β) (xs ys : List α) :
    (xs ++ ys).mapM f = do
      let xs' ← xs.mapM f
      let ys' ← ys.mapM f
      pure (xs' ++ ys')

/-- MapM preserves dropLastN operation.

If mapM succeeds on xs, then mapM on xs.dropLastN n also succeeds and produces
ys.dropLastN n.

Needed for Task 3.1 viewStack_popK proof.
-/
axiom list_mapM_dropLastN_of_mapM_some {α β} (f : α → Option β)
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) (k : Nat) :
    (xs.dropLastN k).mapM f = some (ys.dropLastN k)

/-- FilterMap after mapM can be fused.

If mapM succeeds and produces ys, then filtering ys with g is equivalent
to filtering xs with the composed operation (f then g).

This is a mapM/filterMap fusion optimization used in stack manipulation proofs.

Proof strategy: Induction on xs, using mapM/filterMap correspondence.
-/
axiom filterMap_after_mapM_eq {α β γ}
    (f : α → Option β) (p : β → Option γ)
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) :
  xs.filterMap (fun a => Option.bind (f a) p) = ys.filterMap p

end KernelExtras.List

/-! ## Array helpers -/

namespace Array

/-- Array.toList preserves getElem! access (panic-safe version).

If i < a.size, then a[i]! in the original array equals a.toList[i]! in the list.
-/
axiom getElem!_toList {α} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
  a[i]! = a.toList[i]!

/-- Array.toList preserves indexed get access.

For any valid index i, a.toList.get gives the same element as a[i].
This is definitional equality.
-/
theorem toList_get {α} (a : Array α) (i : Nat) (h : i < a.size) :
  ∀ (h_len : i < a.toList.length), a.toList.get ⟨i, h_len⟩ = a[i] := by
  intro h_len
  rfl

/-- Elements accessed via getElem! are members of toList.

If i < a.size, then a[i]! is a member of a.toList.

Proof strategy: Use getElem!_toList + List.getElem!_mem.
-/
axiom getElem!_mem_toList {α} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
  a[i]! ∈ a.toList

/-- Correspondence between get? and getElem!.

If a[i]? returns some x, then a[i]! equals x.
-/
theorem getElem!_of_getElem?_eq_some {α} [Inhabited α] (a : Array α) (i : Nat) (x : α)
  (h : a[i]? = some x) : a[i]! = x := by
  -- getElem? returns some x iff i < size and a[i] = x
  have ⟨hi, heq⟩ : ∃ h : i < a.size, a[i] = x := by
    simp [getElem?_def] at h
    exact h
  -- Directly use the bounds witness and equality
  simp [getElem!, Array.get!Internal, hi]
  exact heq

end Array

/-! ## Array extraction and window operations

These axioms bridge Array's extraction/window operations with List operations.
Many may be provable using Batteries 4.24.0 lemmas.
-/

namespace Array

-- NOTE: As of Batteries 4.24.0, Array.toList_push is provided by the library.
-- We no longer need a local definition. Import Batteries.Data.Array.Lemmas to use it.

/-- Extracting the first n elements and converting to list equals taking n elements.

Batteries 4.24.0 provides Array.toList_extract. This is a specialized version
for the common case of extract 0 n (take pattern).
-/
@[simp] theorem toList_extract_take {α} (a : Array α) (n : Nat) :
  (a.extract 0 n).toList = a.toList.take n := by
  rw [Array.toList_extract]
  simp [List.extract]

/-- Extracting a prefix while dropping the last k elements.

This operation is common in stack manipulation (pop k elements).
-/
theorem toList_extract_dropLastN {α} (a : Array α) (k : Nat) (h : k ≤ a.size) :
  (a.extract 0 (a.size - k)).toList = a.toList.dropLastN k := by
  -- Use toList_extract_take: (a.extract 0 n).toList = a.toList.take n
  rw [toList_extract_take]
  -- Now goal is: a.toList.take (a.size - k) = a.toList.dropLastN k
  -- Use dropLastN definition: dropLastN k = take (length - k)
  rw [List.dropLastN_eq_take]
  -- Goal: a.toList.take (a.size - k) = a.toList.take (a.toList.length - k)
  -- These are equal because a.size = a.toList.length (definitional)
  rfl

/-- Shrinking an array to size n equals taking the first n elements.

As of Batteries 4.24.0, Array.toList_shrink is provided directly.
We can use it without a local proof.
-/
@[simp] theorem shrink_toList {α} (a : Array α) (n : Nat) :
  (a.shrink n).toList = a.toList.take n :=
  Array.toList_shrink  -- Direct reference to Batteries theorem

/-- Mapping over a window of an array equals dropping, taking, and mapping.

Window operation: extract a slice [off, off+len) and map a function over it.
This is equivalent to dropping off elements, taking len elements, then mapping.
-/
theorem window_toList_map {α β} (a : Array α) (off len : Nat)
    (f : α → β) (h : off + len ≤ a.size) :
  (a.extract off (off + len)).toList.map f =
  ((a.toList.drop off).take len).map f := by
  -- Use toList_extract to convert extract to List.extract
  rw [Array.toList_extract]
  -- List.extract is defined as drop then take
  simp [List.extract]

end Array
