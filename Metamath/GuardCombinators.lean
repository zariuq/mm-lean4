/-
Guard Combinators for Evidence-Based Error Handling

This module provides `require` and `requireSome` combinators that wrap
the existing `DB.mkErrorFromEvidence` path with one-shot inversion lemmas.

**Motivation:** The parser currently uses an imperative `if db.error then db else ...`
pattern for error handling. Proof sites must manually unfold through
`mkErrorFromEvidence → mkErrorWithEvidence → ...` with 10+ symbol simp lists.
These combinators factor out the pattern so proofs can use compact `simp [require_true]`
or `simp [require_false]` instead of the full unfolding chain.

**Design:** Pure wrappers — no changes to Verify.lean or existing proofs.
Future parser refactors can adopt these incrementally, one gate at a time.

**Status:** Phase D — Error handling architecture hardening
-/

import Metamath.Verify

namespace Metamath.Guard

open Metamath.Verify

/-! ## Core Guard Combinators

These are thin wrappers around `DB.mkErrorFromEvidence`. Their value is in the
inversion lemmas below, which reduce proof obligations to simple `simp` calls.
-/

/-- Require a boolean condition, or emit evidence-based error.

    `require b db pos ev` returns `db` unchanged if `b = true`,
    or `db.mkErrorFromEvidence pos ev` if `b = false`.

    **Replaces:** `if condition then ... else db.mkErrorFromEvidence pos ev`
    **Proof benefit:** `simp [require_true]` / `simp [require_false]` -/
@[inline] def require (b : Bool) (db : DB) (pos : Pos)
    (ev : ErrorEvidence) : DB :=
  if b then db else db.mkErrorFromEvidence pos ev

/-- Require an Option to be some, or emit evidence-based error.

    `requireSome o db pos ev` returns `(some a, db)` if `o = some a`,
    or `(none, db.mkErrorFromEvidence pos ev)` if `o = none`.

    **Replaces:** `match lookup with | some a => ... | none => db.mkErrorFromEvidence pos ev`
    **Proof benefit:** `simp [requireSome_some]` / `simp [requireSome_none]` -/
@[inline] def requireSome (o : Option α) (db : DB) (pos : Pos)
    (ev : ErrorEvidence) : Option α × DB :=
  match o with
  | some a => (some a, db)
  | none => (none, db.mkErrorFromEvidence pos ev)

/-! ## One-Shot Inversion Lemmas (simp normal forms)

These are the key payoff: each lemma reduces a combinator application to either
the identity (success) or `mkErrorFromEvidence` (failure) in one `simp` step.
-/

@[simp] theorem require_true (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    require true db pos ev = db := rfl

@[simp] theorem require_false (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    require false db pos ev = db.mkErrorFromEvidence pos ev := rfl

@[simp] theorem requireSome_some (a : α) (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    requireSome (some a) db pos ev = (some a, db) := rfl

@[simp] theorem requireSome_none (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    requireSome (none : Option α) db pos ev = (none, db.mkErrorFromEvidence pos ev) := rfl

/-! ## Error Propagation Lemmas

When `require` / `requireSome` fail, the resulting DB carries the expected
evidence and error flag. These delegate to existing `mkErrorFromEvidence_*` simp lemmas.
-/

theorem require_err_evidence (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (require false db pos ev).errorEvidence? = some ev := by
  simp [require, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]

theorem require_err_error (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (require false db pos ev).error = true := by
  simp [require]

theorem requireSome_err_evidence (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (requireSome (none : Option α) db pos ev).2.errorEvidence? = some ev := by
  simp [requireSome, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]

theorem requireSome_err_error (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (requireSome (none : Option α) db pos ev).2.error = true := by
  simp [requireSome]

/-! ## Config Preservation

Guard combinators never modify the DB config, regardless of success or failure.
-/

theorem require_preserves_config (b : Bool) (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (require b db pos ev).config = db.config := by
  cases b <;> simp [require]

theorem requireSome_preserves_config (o : Option α) (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (requireSome o db pos ev).2.config = db.config := by
  cases o <;> simp [requireSome]

/-! ## OK-Path Inversion (with error-free precondition)

When the input DB has no prior error, we can characterize exactly when
`require` / `requireSome` return the input unchanged.
-/

/-- `require b db pos ev = db` iff `b = true` (given no prior error).

    The precondition `db.error = false` is necessary because if `db` already has
    an error, `mkErrorFromEvidence` might coincidentally produce the same DB
    (it only overwrites `error?` and `errorEvidence?` fields). -/
theorem require_ok_iff {b : Bool} (db : DB) (pos : Pos) (ev : ErrorEvidence)
    (h_no_err : db.error = false) :
    require b db pos ev = db ↔ b = true := by
  cases b with
  | true => simp [require]
  | false =>
    simp only [require_false]
    constructor
    · intro h
      have h1 : (db.mkErrorFromEvidence pos ev).error = true :=
        DB.mkErrorFromEvidence_error db pos ev
      rw [h] at h1
      simp [h_no_err] at h1
    · intro h; exact absurd h (by decide)

/-- `requireSome` returns `isSome` in the first component iff the input was `some`. -/
theorem requireSome_fst_isSome (o : Option α) (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (requireSome o db pos ev).1.isSome = true ↔ o.isSome = true := by
  cases o <;> simp [requireSome]

/-! ## Composition Helpers

Lemmas for composing guard combinators in sequential verification steps.
-/

/-- If require succeeds (returns same DB), the error flag is preserved. -/
theorem require_ok_error_preserved {b : Bool} (db : DB) (pos : Pos) (ev : ErrorEvidence)
    (h : require b db pos ev = db) :
    (require b db pos ev).error = db.error := by
  rw [h]

/-- `require false` always sets the error flag, regardless of prior state. -/
theorem require_false_sets_error (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    (require false db pos ev).error = true :=
  require_err_error db pos ev

/-! ## Pattern Equivalence

These theorems prove that `require`/`requireSome` are exact drop-in replacements
for the imperative `if`/`match` patterns used throughout the parser. This ensures
the combinators can be adopted incrementally without changing any behavior.
-/

/-- `require` is definitionally equal to the `if b then db else mkErrorFromEvidence` pattern.
    This means adoption is a pure refactor — no behavioral change, no proof impact. -/
theorem require_eq_if (b : Bool) (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    require b db pos ev = if b then db else db.mkErrorFromEvidence pos ev := rfl

/-- `requireSome` is definitionally equal to the `match o` pattern.
    This means adoption is a pure refactor — no behavioral change, no proof impact. -/
theorem requireSome_eq_match (o : Option α) (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    requireSome o db pos ev = match o with
      | some a => (some a, db)
      | none => (none, db.mkErrorFromEvidence pos ev) := rfl

/-- Error flag monotonicity: `require` never clears an existing error. -/
theorem require_error_monotone (b : Bool) (db : DB) (pos : Pos) (ev : ErrorEvidence)
    (h : db.error = true) :
    (require b db pos ev).error = true := by
  cases b with
  | true => simpa [require]
  | false => exact require_err_error db pos ev

end Metamath.Guard
