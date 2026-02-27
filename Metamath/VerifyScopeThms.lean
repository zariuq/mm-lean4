import Metamath.Verify
import Metamath.VerifyDBPayloadThms

namespace Metamath
namespace Verify

namespace ParserState

theorem topLevelEssViolation?_eq_some_topLevelEssentialNotAllowed_iff
    (db : DB) :
    topLevelEssViolation? db = some .topLevelEssentialNotAllowed ↔
      (db.config.rejectToplevelEss && db.scopes.size == 0) = true := by
  unfold topLevelEssViolation?
  by_cases h : (db.config.rejectToplevelEss && db.scopes.size == 0) = true
  · simp [h]
  · simp [h]

theorem topLevelEssViolation?_implies_gateFacts
    (db : DB) :
    topLevelEssViolation? db = some .topLevelEssentialNotAllowed →
      db.config.rejectToplevelEss = true ∧ db.scopes.size = 0 := by
  intro h_top
  have h_gate := (topLevelEssViolation?_eq_some_topLevelEssentialNotAllowed_iff db).1 h_top
  have h_parts : (db.config.rejectToplevelEss = true) ∧ ((db.scopes.size == 0) = true) := by
    simpa [Bool.and_eq_true] using h_gate
  have h_scope : db.scopes.size = 0 := by
    simpa using h_parts.2
  exact ⟨h_parts.1, h_scope⟩

/-- Direct scope inversion: decoded `.tokenNotConstantOrVariable` yields lifted scope payload. -/
theorem DB.parseErrorCode?_tokenNotConstantOrVariable_gateWitness_of_mathGate
    (s : DB) :
    DB.parseErrorCode? s = some .tokenNotConstantOrVariable ->
    ∃ sym,
      s.errorEvidence? = some (.scopeDecl (.tokenNotConstantOrVariable sym)) := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotConstantOrVariable_payload_inversion (s := s) h_code

/-- Direct scope inversion: decoded `.tokenNotInScope` yields lifted scope payload. -/
theorem DB.parseErrorCode?_tokenNotInScope_gateWitness_of_djvarsGate
    (s : DB) :
    DB.parseErrorCode? s = some .tokenNotInScope ->
    ∃ sym,
      s.errorEvidence? = some (.scopeDecl (.tokenNotInScope sym)) := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotInScope_payload_inversion (s := s) h_code

/-- Direct scope inversion: decoded `.topLevelEssentialNotAllowed` yields lifted strict-mode payload. -/
theorem DB.parseErrorCode?_topLevelEssentialNotAllowed_gateFacts_of_topLevelGate
    (s : DB) :
    DB.parseErrorCode? s = some .topLevelEssentialNotAllowed ->
    s.errorEvidence? = some (.scopeDecl (.topLevelEssentialNotAllowed)) := by
  intro h_code
  exact DB.parseErrorCode?_topLevelEssentialNotAllowed_payload_inversion (s := s) h_code

end ParserState

theorem DB.parseErrorCode?_tokenNotConstantOrVariable_guardFacts
    (s : DB) :
    DB.parseErrorCode? s = some .tokenNotConstantOrVariable ->
    ∃ sym,
      s.errorEvidence? = some (.scopeDecl (.tokenNotConstantOrVariable sym)) := by
  intro h_code
  exact ParserState.DB.parseErrorCode?_tokenNotConstantOrVariable_gateWitness_of_mathGate s h_code

theorem DB.parseErrorCode?_tokenNotInScope_guardFacts
    (s : DB) :
    DB.parseErrorCode? s = some .tokenNotInScope ->
    ∃ sym,
      s.errorEvidence? = some (.scopeDecl (.tokenNotInScope sym)) := by
  intro h_code
  exact ParserState.DB.parseErrorCode?_tokenNotInScope_gateWitness_of_djvarsGate s h_code

theorem DB.parseErrorCode?_topLevelEssentialNotAllowed_guardFacts
    (s : DB) :
    DB.parseErrorCode? s = some .topLevelEssentialNotAllowed ->
    s.errorEvidence? = some (.scopeDecl (.topLevelEssentialNotAllowed)) := by
  intro h_code
  exact ParserState.DB.parseErrorCode?_topLevelEssentialNotAllowed_gateFacts_of_topLevelGate s h_code

theorem checkBytes_parseErrorCode?_tokenNotConstantOrVariable_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable ->
    ∃ sym,
      (checkBytes arr config).errorEvidence? =
        some (.scopeDecl (.tokenNotConstantOrVariable sym)) := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotConstantOrVariable_guardFacts
    (s := checkBytes arr config) h_code

theorem checkBytes_parseErrorCode?_tokenNotInScope_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope ->
    ∃ sym,
      (checkBytes arr config).errorEvidence? =
        some (.scopeDecl (.tokenNotInScope sym)) := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotInScope_guardFacts
    (s := checkBytes arr config) h_code

theorem checkBytes_parseErrorCode?_topLevelEssentialNotAllowed_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed ->
    (checkBytes arr config).errorEvidence? =
      some (.scopeDecl (.topLevelEssentialNotAllowed)) := by
  intro h_code
  exact DB.parseErrorCode?_topLevelEssentialNotAllowed_guardFacts
    (s := checkBytes arr config) h_code

/-- Backward-compatible alias for token-not-const/var guard facts. -/
theorem DB.parseErrorCode?_tokenNotConstantOrVariable_gateWitness_of_mathGate
    (s : DB) :
    DB.parseErrorCode? s = some .tokenNotConstantOrVariable ->
    ∃ sym,
      s.errorEvidence? = some (.scopeDecl (.tokenNotConstantOrVariable sym)) := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotConstantOrVariable_guardFacts (s := s) h_code

/-- Backward-compatible alias for token-not-in-scope guard facts. -/
theorem DB.parseErrorCode?_tokenNotInScope_gateWitness_of_djvarsGate
    (s : DB) :
    DB.parseErrorCode? s = some .tokenNotInScope ->
    ∃ sym,
      s.errorEvidence? = some (.scopeDecl (.tokenNotInScope sym)) := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotInScope_guardFacts (s := s) h_code

/-- Backward-compatible alias for top-level `$e` guard facts. -/
theorem DB.parseErrorCode?_topLevelEssentialNotAllowed_gateFacts_of_topLevelGate
    (s : DB) :
    DB.parseErrorCode? s = some .topLevelEssentialNotAllowed ->
    s.errorEvidence? = some (.scopeDecl (.topLevelEssentialNotAllowed)) := by
  intro h_code
  exact DB.parseErrorCode?_topLevelEssentialNotAllowed_guardFacts (s := s) h_code

/-- Backward-compatible alias for checkBytes token-not-const/var guard facts. -/
theorem checkBytes_parseErrorCode?_tokenNotConstantOrVariable_gateWitness_of_mathGate
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable ->
    ∃ sym,
      (checkBytes arr config).errorEvidence? =
        some (.scopeDecl (.tokenNotConstantOrVariable sym)) := by
  intro h_code
  exact checkBytes_parseErrorCode?_tokenNotConstantOrVariable_guardFacts arr config h_code

/-- Backward-compatible alias for checkBytes token-not-in-scope guard facts. -/
theorem checkBytes_parseErrorCode?_tokenNotInScope_gateWitness_of_djvarsGate
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope ->
    ∃ sym,
      (checkBytes arr config).errorEvidence? =
        some (.scopeDecl (.tokenNotInScope sym)) := by
  intro h_code
  exact checkBytes_parseErrorCode?_tokenNotInScope_guardFacts arr config h_code

/-- Backward-compatible alias for checkBytes top-level `$e` guard facts. -/
theorem checkBytes_parseErrorCode?_topLevelEssentialNotAllowed_gateFacts_of_topLevelGate
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed ->
    (checkBytes arr config).errorEvidence? =
      some (.scopeDecl (.topLevelEssentialNotAllowed)) := by
  intro h_code
  exact checkBytes_parseErrorCode?_topLevelEssentialNotAllowed_guardFacts arr config h_code

theorem checkBytes_parseErrorCode?_tokenNotInScope_payload_inversion
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).TokenNotInScopePayloadWitness := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotInScope_payload_inversion
    (s := checkBytes arr config) h_code

theorem checkBytes_parseErrorCode?_tokenNotConstantOrVariable_payload_inversion
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
    (checkBytes arr config).TokenNotConstantOrVariablePayloadWitness := by
  intro h_code
  exact DB.parseErrorCode?_tokenNotConstantOrVariable_payload_inversion
    (s := checkBytes arr config) h_code

end Verify
end Metamath
