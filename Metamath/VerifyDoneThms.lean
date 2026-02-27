import Metamath.Verify

namespace Metamath
namespace Verify

/-- If parsing ends in `$d` mode at whitespace boundary, `done` reports unclosed `$d`. -/
theorem done_error_if_djvars_ws
    (s : ParserState) (base : Nat) (vars : Array String)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none)
    (h_tokp : s.tokp = .djvars vars) :
    (s.done base).error? ≠ none := by
  simp [ParserState.done, h_charp, h_no_err, h_tokp, DB.mkParseError, DB.mkErrorFromEvidence,
    DB.mkErrorWithEvidence, DB.error, Id.run]

/-- If parsing ends in `$d` mode after flushing a pending token, `done` reports unclosed `$d`. -/
theorem done_error_if_djvars_token
    (s : ParserState) (base : Nat) (pos : Nat) (tk : ByteSliceT) (vars : Array String)
    (h_charp : s.charp = .token pos tk)
    (h_no_err : s.db.error? = none)
    (h_feed_no_err : (s.feedToken pos tk.toSlice).db.error? = none)
    (h_tokp : (s.feedToken pos tk.toSlice).tokp = .djvars vars) :
    (s.done base).error? ≠ none := by
  simp [ParserState.done, h_charp, h_no_err, h_feed_no_err, h_tokp, DB.mkParseError,
    DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.error, Id.run]

/-- If parsing ends in `$d` mode at whitespace boundary, `done` reports code `unclosedDjvars`. -/
theorem done_errorCode_if_djvars_ws
    (s : ParserState) (base : Nat) (vars : Array String)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none)
    (h_tokp : s.tokp = .djvars vars) :
    (s.done base).parseErrorCode? = some .unclosedDjvars := by
  simp [ParserState.done, h_charp, h_no_err, h_tokp, DB.parseErrorCode?, DB.mkParseError,
    DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.error, Id.run]

/-- If parsing ends in `$d` mode after flushing a pending token, code is `unclosedDjvars`. -/
theorem done_errorCode_if_djvars_token
    (s : ParserState) (base : Nat) (pos : Nat) (tk : ByteSliceT) (vars : Array String)
    (h_charp : s.charp = .token pos tk)
    (h_no_err : s.db.error? = none)
    (h_feed_no_err : (s.feedToken pos tk.toSlice).db.error? = none)
    (h_tokp : (s.feedToken pos tk.toSlice).tokp = .djvars vars) :
    (s.done base).parseErrorCode? = some .unclosedDjvars := by
  simp [ParserState.done, h_charp, h_no_err, h_feed_no_err, h_tokp, DB.parseErrorCode?,
    DB.mkParseError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.error, Id.run]

/-- Parser-level soundness (ws branch): open `$d` at EOF yields `unclosedDjvars`
under the no-prior-error contract. -/
theorem done_unclosedDjvars_sound_ws
    (s : ParserState) (base : Nat)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none)
    (vars : Array String)
    (h_tokp : s.tokp = .djvars vars) :
    (s.done base).parseErrorCode? = some .unclosedDjvars := by
  exact done_errorCode_if_djvars_ws s base vars h_charp h_no_err h_tokp

/-- EOF inversion (whitespace case): `done` returns the code dictated by the current parser mode. -/
theorem done_parseErrorCode?_ws
    (s : ParserState) (base : Nat)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none) :
    (s.done base).parseErrorCode? =
      match s.tokp with
      | .start =>
          if s.db.scopes.size > 0 then some .unclosedBlock else none
      | .comment _ => some .unclosedComment
      | .const => some .unclosedConst
      | .var => some .unclosedVar
      | .djvars _ => some .unclosedDjvars
      | .math _ p =>
          match p.k with
          | .float => some .unclosedFloat
          | .ess => some .unclosedEss
          | .ax => some .unclosedAx
          | .thm => some .unclosedThm
      | .label _ _ => some .notACommand
      | .proof _ => some .unclosedProof := by
  unfold ParserState.done
  simp [h_charp, h_no_err, DB.error, DB.parseErrorCode?, DB.mkParseError, DB.mkErrorFromEvidence,
    DB.mkErrorWithEvidence, Id.run]
  cases h_tokp : s.tokp <;>
    simp
  case start =>
    by_cases h_scope : 0 < s.db.scopes.size
    · simp [h_scope]
    · simp [h_scope, h_no_err]
  case math a p =>
    cases h_k : p.k <;>
      simp
  case label pos lab =>
    simp [ErrorEvidence.code, TokenFormError.code]

/-- EOF inversion (token case): `done` returns the code dictated by the parser mode after
flushing the pending token, assuming no error was raised during the flush. -/
theorem done_parseErrorCode?_token
    (s : ParserState) (base : Nat) (pos : Nat) (tk : ByteSliceT)
    (h_charp : s.charp = .token pos tk)
    (h_no_err : s.db.error? = none)
    (h_feed_no_err : (s.feedToken pos tk.toSlice).db.error? = none) :
    (s.done base).parseErrorCode? =
      match (s.feedToken pos tk.toSlice).tokp with
      | TokenParser.start =>
          if (s.feedToken pos tk.toSlice).db.scopes.size > 0 then some .unclosedBlock else none
      | TokenParser.comment _ => some .unclosedComment
      | TokenParser.const => some .unclosedConst
      | TokenParser.var => some .unclosedVar
      | TokenParser.djvars _ => some .unclosedDjvars
      | TokenParser.math _ p =>
          match p.k with
          | .float => some .unclosedFloat
          | .ess => some .unclosedEss
          | .ax => some .unclosedAx
          | .thm => some .unclosedThm
      | TokenParser.label _ _ => some .notACommand
      | TokenParser.proof _ => some .unclosedProof := by
  unfold ParserState.done
  simp [h_charp, h_no_err, h_feed_no_err, DB.error, DB.parseErrorCode?, DB.mkParseError,
    DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, Id.run]
  cases h_tokp : (s.feedToken pos tk.toSlice).tokp <;>
    simp
  case start =>
    by_cases h_scope : 0 < (s.feedToken pos tk.toSlice).db.scopes.size
    · simp [h_scope]
    · simp [h_scope, h_feed_no_err]
  case math a p =>
    cases h_k : p.k <;>
      simp
  case label pos lab =>
    simp [ErrorEvidence.code, TokenFormError.code]

end Verify
end Metamath
