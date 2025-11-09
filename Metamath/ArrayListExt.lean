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

Proven using a helper lemma about mapM.loop that tracks the accumulator.
-/
private theorem mapM_loop_length {α β} (f : α → Option β) :
  ∀ (xs : List α) (acc : List β) (ys : List β),
    List.mapM.loop f xs acc = some ys →
    ys.length = acc.length + xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases h
    simp
  | cons a xs' ih =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases hfa : f a with
    | none =>
      simp [hfa] at h
    | some b =>
      simp [hfa] at h
      have := ih (b :: acc) ys h
      simp at this ⊢
      omega

theorem mapM_length_option {α β : Type _} (f : α → Option β) :
  ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length := by
  intro xs ys h
  unfold List.mapM at h
  have := mapM_loop_length f xs [] ys h
  simp at this
  exact this

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

Proven using a helper lemma about mapM.loop that handles membership.
-/
private theorem mapM_loop_some_of_mem {α β} (f : α → Option β) :
  ∀ (xs : List α) (acc : List β) (ys : List β) (x : α),
    List.mapM.loop f xs acc = some ys →
    x ∈ xs →
    ∃ b, f x = some b := by
  intro xs
  induction xs with
  | nil =>
    intro acc ys x h hmem
    cases hmem
  | cons a xs' ih =>
    intro acc ys x h hmem
    simp [List.mapM.loop] at h
    cases hfa : f a with
    | none =>
      simp [hfa] at h
    | some b =>
      simp [hfa] at h
      cases hmem with
      | head =>
        -- x = a, so f x = f a = some b
        exact ⟨b, hfa⟩
      | tail _ hmem' =>
        -- x ∈ xs', use IH
        exact ih (b :: acc) ys x h hmem'

theorem mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b := by
  unfold List.mapM at h
  exact mapM_loop_some_of_mem f xs [] ys x h hx

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

Provided directly by Batteries 4.24.0 as List.mapM_append for LawfulMonad.
Option is a LawfulMonad, so this is just a direct application.
-/
abbrev list_mapM_append {α β} (f : α → Option β) (xs ys : List α) :=
  @List.mapM_append Option α β _ _ (f := f) (l₁ := xs) (l₂ := ys)

/-- MapM preserves dropLastN operation.

If mapM succeeds on xs, then mapM on xs.dropLastN n also succeeds and produces
ys.dropLastN n.

Proven by decomposing xs using take/drop, applying mapM_append, and showing
that the first part corresponds to dropLastN.
-/
theorem list_mapM_dropLastN_of_mapM_some {α β} (f : α → Option β)
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) (k : Nat) :
    (xs.dropLastN k).mapM f = some (ys.dropLastN k) := by
  unfold List.dropLastN
  have hlen := @List.mapM_length_option α β f xs ys h
  rw [hlen]
  -- Strategy: rewrite xs as xs.take n ++ xs.drop n
  let n := xs.length - k
  have split_xs : xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
  rw [split_xs] at h
  -- Now use mapM_append to decompose h
  rw [List.mapM_append] at h
  -- h now says: (xs.take n).mapM f >>= ... = some ys
  -- We need to extract that (xs.take n).mapM f = some (ys.take n)
  simp [pure] at h
  -- h : bind (xs.take n).mapM f (...) = some ys
  cases hxs_take : (xs.take n).mapM f with
  | none =>
    simp [hxs_take] at h
  | some ys₁ =>
    simp [hxs_take] at h
    cases hxs_drop : (xs.drop n).mapM f with
    | none =>
      simp [hxs_drop] at h
    | some ys₂ =>
      simp [hxs_drop] at h
      -- h : some (ys₁ ++ ys₂) = some ys
      cases h
      -- ys = ys₁ ++ ys₂
      -- Need to show ys₁ = ys.take n
      have hlen₁ := @List.mapM_length_option α β f (xs.take n) ys₁ hxs_take
      have hlen₂ := @List.mapM_length_option α β f (xs.drop n) ys₂ hxs_drop
      -- ys₁.length = (xs.take n).length
      simp at hlen₁ hlen₂
      -- Show that ys₁.length = xs.length - k (which is n)
      have n_le : n ≤ xs.length := Nat.sub_le xs.length k
      have hlen₁' : ys₁.length = n := by
        rw [hlen₁]
        exact Nat.min_eq_left n_le
      -- Now show (ys₁ ++ ys₂).take (xs.length - k) = ys₁
      have take_eq : (ys₁ ++ ys₂).take ys₁.length = ys₁ := by
        induction ys₁ with
        | nil => rfl
        | cons y ys₁' ih => simp
      -- Combine: hlen₁' : ys₁.length = n = xs.length - k
      congr 1
      symm
      show List.take (xs.length - k) (ys₁ ++ ys₂) = ys₁
      calc List.take (xs.length - k) (ys₁ ++ ys₂)
          _ = List.take n (ys₁ ++ ys₂) := by rfl
          _ = List.take ys₁.length (ys₁ ++ ys₂) := by rw [← hlen₁']
          _ = ys₁ := take_eq

/-- FilterMap after mapM can be fused.

If mapM succeeds and produces ys, then filtering ys with g is equivalent
to filtering xs with the composed operation (f then g).

Proven using a helper lemma about mapM.loop that tracks the accumulator.
The key insight: mapM.loop accumulates results in reverse, so we track
filterMap through this reverse accumulation.
-/
private theorem mapM_loop_filterMap_eq {α β γ} (f : α → Option β) (p : β → Option γ) :
  ∀ (xs : List α) (acc : List β) (ys : List β),
    List.mapM.loop f xs acc = some ys →
    ys.filterMap p = acc.reverse.filterMap p ++ xs.filterMap (fun a => Option.bind (f a) p) := by
  intro xs
  induction xs with
  | nil =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases h
    simp
  | cons a xs' ih =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases hfa : f a with
    | none =>
      rw [hfa] at h
      simp at h
    | some b =>
      rw [hfa] at h
      simp at h
      have ih_result := ih (b :: acc) ys h
      rw [ih_result]
      rw [List.reverse_cons]
      rw [List.filterMap_append]
      rw [List.filterMap]
      cases hpb : p b with
      | none =>
        simp [List.filterMap]
        simp [hfa, Option.bind, hpb]
      | some c =>
        simp [List.filterMap]
        simp [hfa, Option.bind, hpb]

theorem filterMap_after_mapM_eq {α β γ}
    (f : α → Option β) (p : β → Option γ)
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) :
  xs.filterMap (fun a => Option.bind (f a) p) = ys.filterMap p := by
  unfold List.mapM at h
  have helper := mapM_loop_filterMap_eq f p xs [] ys h
  simp at helper
  exact helper.symm

end KernelExtras.List

/-! ## Array helpers -/

namespace Array

/-- Array.toList preserves getElem! access (panic-safe version).

If i < a.size, then a[i]! in the original array equals a.toList[i]! in the list.

Uses Batteries 4.24's `getElem!_pos` lemma which says c[i]! = c[i] when i is valid.
-/
theorem getElem!_toList {α} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
  a[i]! = a.toList[i]! := by
  simp [getElem!_pos, h]

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

Proven using getElem!_pos to convert to bounded access, then standard membership.
-/
theorem getElem!_mem_toList {α} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
  a[i]! ∈ a.toList := by
  simp [getElem!_pos, h]

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
