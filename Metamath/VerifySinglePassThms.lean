import Metamath.Verify

namespace Metamath
namespace Verify

/-! ## Theorem map (single-pass only)

This module contains only single-pass checker identity/canonicalization lemmas.
Legacy two-pass compatibility/equivalence theorems are isolated in
`Metamath/Legacy/CompatThms.lean`.
-/

/-- Single-pass post-processor maps include errors to canonical include-preprocess DBs. -/
@[simp] theorem finalizeSinglePassResult_error
    (config : ModeConfig) (err : IncludeError) :
    finalizeSinglePassResult config (.error err) = includePreprocessErrorDB config err := rfl

/-- A terminal parser error returned by the streaming include driver is
preserved exactly by finalization.  In particular, its source position and
the prefix database produced by the single pass are not re-encoded or fed a
second time. -/
theorem finalizeSinglePassResult_ok_of_parserError
    (config : ModeConfig) (s : ParserState) (base : Nat)
    (seen : Std.HashSet String) (h_error : s.db.error? ≠ none) :
    finalizeSinglePassResult config (.ok (s, base, seen)) = s.db := by
  have h_some : s.db.error?.isSome = true :=
    Option.isSome_iff_ne_none.mpr h_error
  have h_done : s.done base = s.db := by
    unfold ParserState.done
    simp [DB.error, h_some]
  simp [finalizeSinglePassResult, h_done, h_error]

/-- Flushing the sole token retained at a file boundary always restores the
character scanner to its whitespace state, so child-file processing can
resume without replaying any source byte. -/
@[simp] theorem flushPendingToken_charp (s : ParserState) :
    (flushPendingToken s).charp = .ws := by
  cases h : s.charp <;> simp [flushPendingToken, h]

/-- On a pending token, the EOF flush performs exactly one `feedToken`
transition and clears that buffer. -/
theorem flushPendingToken_of_token
    (s : ParserState) (pos : Nat) (tk : ByteSliceT)
    (h : s.charp = .token pos tk) :
    flushPendingToken s = { s.feedToken pos tk.toSlice with charp := .ws } := by
  simp [flushPendingToken, h]

/-- Single-pass file processor immediately returns the depth-limit include error when
called with zero fuel. -/
@[simp] theorem processFileSinglePass_zeroFuel
    (fname : String) (processing seen : Std.HashSet String) (config : ModeConfig)
    (s : ParserState) (base : Nat) :
    processFileSinglePass fname processing seen config 0 s base =
      pure (.error (.depthExceeded fname)) := by
  rfl

/-- Single-pass OK-branch normalization: feeding bytes from the canonical initial
state and finalizing matches `checkBytes` on the same bytes. -/
@[simp] theorem finalizeSinglePassResult_ok_initialFeedAll_eq_checkBytes
    (config : ModeConfig) (processed : ByteArray) (seen : Std.HashSet String) :
    finalizeSinglePassResult config
      (.ok ((singlePassInitialState config).feedAll 0 processed, processed.size, seen)) =
      checkBytes processed config := by
  unfold finalizeSinglePassResult checkBytes checkBytesCore singlePassInitialState singlePassInitialDB
  simp

/-- Default checker aliases the single-pass implementation. -/
@[simp] theorem check_eq_checkSinglePass_core
    (fname : String) (config : ModeConfig) :
    check fname config = checkSinglePass fname config := rfl

/-- `checkSinglePass` is definitionally `singlePassInitialResult` followed by
`finalizeSinglePassResult`. -/
@[simp] theorem checkSinglePass_eq_finalize_singlePassInitialResult
    (fname : String) (config : ModeConfig) :
    checkSinglePass fname config =
      (do
        let r ← singlePassInitialResult fname config
        pure (finalizeSinglePassResult config r)) := rfl

end Verify
end Metamath
