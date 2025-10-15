/-
PHASE 2: allM Extraction Lemmas

These lemmas extract pointwise properties from monadic validation.
They are foundational for Phase 3 (toSubstTyped) and Phase 5 (checkHyp).

**Proof strategy:** Simple induction on list structure with case analysis on Option values.
-/

namespace List

/-! ## Main Extraction Lemma -/

/-- Extract pointwise property from monadic validation.

**Statement:** xs.allM p = some true ↔ (∀ x ∈ xs, p x = some true)

**Proof strategy:**
- Base case (nil): allM returns some true, forall vacuously true
- Cons case: allM succeeds iff head succeeds AND tail succeeds
  - Forward: allM = some true implies both p x = some true and tail allM = some true
  - Backward: both conditions imply allM = some true

**Key insight:** allM short-circuits on none/false, so success means ALL elements passed.
-/
theorem allM_true_iff_forall {α} (p : α → Option Bool) (xs : List α) :
  xs.allM p = some true ↔ (∀ x ∈ xs, p x = some true) := by
  induction xs with
  | nil =>
    -- Base case: empty list
    constructor
    · intro _
      intro x hx
      simp at hx  -- contradiction: x not in empty list
    · intro _
      simp [allM]
  | cons head tail ih =>
    -- Inductive case: head :: tail
    constructor
    · -- Forward: allM = some true → forall holds
      intro h_allM
      intro x hx
      -- allM definition: bind p head with tail
      simp [allM] at h_allM
      cases hp : p head with
      | none =>
        -- If p head = none, allM returns none (contradiction)
        simp [hp] at h_allM
      | some b =>
        -- If p head = some b, check b
        simp [hp] at h_allM
        cases b
        · -- If b = false, allM returns some false (contradiction)
          simp at h_allM
        · -- If b = true, allM continues with tail
          -- h_allM : tail.allM p = some true
          -- Now split on whether x = head or x ∈ tail
          cases hx with
          | head =>
            -- x = head, use hp : p head = some true
            exact hp
          | tail _ hx_tail =>
            -- x ∈ tail, use IH
            exact (ih.mp h_allM) x hx_tail
    · -- Backward: forall holds → allM = some true
      intro h_forall
      -- Get p head = some true from forall
      have hp : p head = some true := h_forall head (by simp)
      -- Get tail.allM p = some true from IH
      have h_tail : tail.allM p = some true := by
        apply ih.mpr
        intro y hy
        exact h_forall y (by simp [hy])
      -- Now compute allM
      simp [allM, hp, h_tail]

/-! ## Corollary: Membership Extraction -/

/-- If allM succeeds, then predicate holds for any member.

**Proof:** Direct application of allM_true_iff_forall forward direction.
-/
theorem allM_true_of_mem {α} (p : α → Option Bool) {xs : List α}
    (hall : xs.allM p = some true) {x} (hx : x ∈ xs) :
  p x = some true :=
  (allM_true_iff_forall p xs).mp hall x hx

/-! ## Lambda Normalization Helpers -/

/-- Pointwise equality between pair λ and fst/snd λ.

This eliminates eta-expansion issues when pattern-matching lambdas are
elaborated differently than projection lambdas.
-/
@[simp] theorem pair_eta₂ {α β γ} (f : α → β → γ) :
  (fun (p : α × β) => f p.fst p.snd) = (fun (a, b) => f a b) := rfl

/-- Congruence for allM in the function argument.

When two predicates are pointwise equal, allM results are equal.
-/
theorem allM_congr {α} {p q : α → Option Bool} (h : ∀ x, p x = q x) (xs : List α) :
    xs.allM p = xs.allM q := by
  induction xs with
  | nil => simp [allM]
  | cons x xs ih => simp [allM, h x, ih]

end List

/-! ## Phase 2 Complete

**What we proved:**
✅ allM_true_iff_forall: bidirectional extraction (some true ↔ forall)
✅ allM_true_of_mem: membership extraction corollary

**Why this matters:**
- Phase 3 (toSubstTyped): Extract type correctness from checkHyp's allM validation
- Phase 5 (checkHyp soundness): Prove that allM validation implies semantic properties

**Line count:** ~95 lines (including docs)
**Time spent:** ~1 hour (as planned)

**Dependencies:** Only List (stdlib)
**Used by:** Metamath.KernelClean (will remove AXIOM 1)

**Next step:** Phase 3 - Implement toSubstTyped using these lemmas
-/
