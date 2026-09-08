import Metamath.VerifyDBSemanticThms

namespace Metamath
namespace Verify
namespace DB

/-- Inversion: decoded `.invalidLabel` carries the rejected label payload. -/
theorem parseErrorCode?_invalidLabel_payload_inversion
    (s : DB) :
    s.parseErrorCode? = some .invalidLabel →
    s.InvalidLabelPayloadWitness := by
  intro h_code
  have h_rule := parseErrorCode?_ruleSemantic_sound s .invalidLabel h_code
  rcases h_rule with ⟨err, h_ev, h_err_code⟩
  cases err with
  | notACommand lab => cases h_err_code
  | invalidLabel lab => exact ⟨lab, by simpa using h_ev⟩
  | invalidMathString tok => cases h_err_code
  | unknownStatementType ty => cases h_err_code
  | nestedCommentDelimiter => cases h_err_code

/-- Inversion: decoded `.topLevelEssentialNotAllowed` carries scope-decl payload. -/
theorem parseErrorCode?_topLevelEssentialNotAllowed_payload_inversion
    (s : DB) :
    s.parseErrorCode? = some .topLevelEssentialNotAllowed →
    s.TopLevelEssentialPayloadWitness := by
  intro h_code
  have h_rule := parseErrorCode?_ruleSemantic_sound s .topLevelEssentialNotAllowed h_code
  rcases h_rule with ⟨err, h_ev, h_err_code⟩
  cases err with
  | cantPopGlobalScope => cases h_err_code
  | constMustBeOutermost => cases h_err_code
  | duplicateSymbolOrAssert l => cases h_err_code
  | firstSymbolNotConstant => cases h_err_code
  | hypothesisSymbolsNotInFrame => cases h_err_code
  | expectedConstantAndVariable => cases h_err_code
  | variableAlreadyHasFloatHyp v => cases h_err_code
  | duplicateDisjointVariable sym => cases h_err_code
  | disjointStatementTooShort actual => cases h_err_code
  | tokenNotInScope sym =>
      simp [ScopeDeclError.code] at h_err_code
  | tokenNotVariable sym => cases h_err_code
  | tokenNotConstantOrVariable sym =>
      simp [ScopeDeclError.code] at h_err_code
  | topLevelEssentialNotAllowed =>
      exact h_ev
  | outOfOrderHypothesesInFrame => cases h_err_code

/-- Inversion: decoded `.tokenNotInScope` carries scope-decl symbol payload. -/
theorem parseErrorCode?_tokenNotInScope_payload_inversion
    (s : DB) :
    s.parseErrorCode? = some .tokenNotInScope →
    s.TokenNotInScopePayloadWitness := by
  intro h_code
  have h_rule := parseErrorCode?_ruleSemantic_sound s .tokenNotInScope h_code
  rcases h_rule with ⟨err, h_ev, h_err_code⟩
  cases err with
  | cantPopGlobalScope => cases h_err_code
  | constMustBeOutermost => cases h_err_code
  | duplicateSymbolOrAssert l => cases h_err_code
  | firstSymbolNotConstant => cases h_err_code
  | hypothesisSymbolsNotInFrame => cases h_err_code
  | expectedConstantAndVariable => cases h_err_code
  | variableAlreadyHasFloatHyp v => cases h_err_code
  | duplicateDisjointVariable sym => cases h_err_code
  | disjointStatementTooShort actual => cases h_err_code
  | tokenNotInScope sym =>
      simp [ScopeDeclError.code] at h_err_code
      exact ⟨sym, by simpa using h_ev⟩
  | tokenNotVariable sym => cases h_err_code
  | tokenNotConstantOrVariable sym =>
      simp [ScopeDeclError.code] at h_err_code
  | topLevelEssentialNotAllowed =>
      simp [ScopeDeclError.code] at h_err_code
  | outOfOrderHypothesesInFrame => cases h_err_code

/-- Inversion: decoded `.tokenNotConstantOrVariable` carries scope-decl symbol payload. -/
theorem parseErrorCode?_tokenNotConstantOrVariable_payload_inversion
    (s : DB) :
    s.parseErrorCode? = some .tokenNotConstantOrVariable →
    s.TokenNotConstantOrVariablePayloadWitness := by
  intro h_code
  have h_rule := parseErrorCode?_ruleSemantic_sound s .tokenNotConstantOrVariable h_code
  rcases h_rule with ⟨err, h_ev, h_err_code⟩
  cases err with
  | cantPopGlobalScope => cases h_err_code
  | constMustBeOutermost => cases h_err_code
  | duplicateSymbolOrAssert l => cases h_err_code
  | firstSymbolNotConstant => cases h_err_code
  | hypothesisSymbolsNotInFrame => cases h_err_code
  | expectedConstantAndVariable => cases h_err_code
  | variableAlreadyHasFloatHyp v => cases h_err_code
  | duplicateDisjointVariable sym => cases h_err_code
  | disjointStatementTooShort actual => cases h_err_code
  | tokenNotInScope sym =>
      simp [ScopeDeclError.code] at h_err_code
  | tokenNotVariable sym => cases h_err_code
  | tokenNotConstantOrVariable sym =>
      simp [ScopeDeclError.code] at h_err_code
      exact ⟨sym, by simpa using h_ev⟩
  | topLevelEssentialNotAllowed =>
      simp [ScopeDeclError.code] at h_err_code
  | outOfOrderHypothesesInFrame => cases h_err_code

/-- Inversion: decoded `.disjointStatementTooShort` retains the number of
variables consumed before the `$d` terminator. -/
theorem parseErrorCode?_disjointStatementTooShort_payload_inversion
    (s : DB) :
    s.parseErrorCode? = some .disjointStatementTooShort →
    s.DisjointStatementTooShortPayloadWitness := by
  intro h_code
  have h_rule := parseErrorCode?_ruleSemantic_sound s
    .disjointStatementTooShort h_code
  rcases h_rule with ⟨err, h_ev, h_err_code⟩
  cases err with
  | cantPopGlobalScope => cases h_err_code
  | constMustBeOutermost => cases h_err_code
  | duplicateSymbolOrAssert label => cases h_err_code
  | firstSymbolNotConstant => cases h_err_code
  | hypothesisSymbolsNotInFrame => cases h_err_code
  | outOfOrderHypothesesInFrame => cases h_err_code
  | expectedConstantAndVariable => cases h_err_code
  | variableAlreadyHasFloatHyp v => cases h_err_code
  | duplicateDisjointVariable v => cases h_err_code
  | disjointStatementTooShort actual =>
      exact ⟨actual, by simpa using h_ev⟩
  | tokenNotInScope v => cases h_err_code
  | tokenNotVariable v => cases h_err_code
  | tokenNotConstantOrVariable symbol => cases h_err_code
  | topLevelEssentialNotAllowed => cases h_err_code

/-- Inversion: decoded `.includeInInnerScope` carries include payload with position+depth. -/
theorem parseErrorCode?_includeInInnerScope_payload_inversion
    (s : DB) :
    s.parseErrorCode? = some .includeInInnerScope →
    s.IncludeInInnerScopePayloadWitness := by
  intro h_code
  have h_rule := parseErrorCode?_ruleSemantic_sound s .includeInInnerScope h_code
  rcases h_rule with ⟨err, h_ev, h_err_code⟩
  cases err with
  | cycleDetected path => cases h_err_code
  | depthExceeded path => cases h_err_code
  | inInnerScope pos depth inStatement allowIncludeInnerScopeWitness =>
      exact ⟨pos, depth, inStatement, allowIncludeInnerScopeWitness, by simpa using h_ev⟩
  | insideStatement pos scopeDepth inStatement allowTokenSplicingWitness =>
      cases h_err_code
  | extractedEmptyPath startPos endPos file => cases h_err_code
  | emptyPathBeforeNormalization file => cases h_err_code
  | pathEmptyAfterNormalization origPath file => cases h_err_code
  | readFailure name path err => cases h_err_code

/-- Inversion: decoded `.includeInsideStatement` carries include position payload. -/
theorem parseErrorCode?_includeInsideStatement_payload_inversion
    (s : DB) :
    s.parseErrorCode? = some .includeInsideStatement →
    s.IncludeInsideStatementPayloadWitness := by
  intro h_code
  have h_rule := parseErrorCode?_ruleSemantic_sound s .includeInsideStatement h_code
  rcases h_rule with ⟨err, h_ev, h_err_code⟩
  cases err with
  | cycleDetected path => cases h_err_code
  | depthExceeded path => cases h_err_code
  | inInnerScope pos depth inStatement allowIncludeInnerScopeWitness =>
      cases h_err_code
  | insideStatement pos scopeDepth inStatement allowTokenSplicingWitness =>
      exact ⟨pos, scopeDepth, inStatement, allowTokenSplicingWitness, by simpa using h_ev⟩
  | extractedEmptyPath startPos endPos file => cases h_err_code
  | emptyPathBeforeNormalization file => cases h_err_code
  | pathEmptyAfterNormalization origPath file => cases h_err_code
  | readFailure name path err => cases h_err_code

/-- Direct include inversion: decoded `.includeInInnerScope` yields guard facts. -/
theorem parseErrorCode?_includeInInnerScope_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .includeInInnerScope →
    ∃ pos depth inStatement allowIncludeInnerScopeWitness,
      s.errorEvidence? =
        some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness)) := by
  intro h_code
  exact parseErrorCode?_includeInInnerScope_payload_inversion (s := s) h_code

/-- Direct include inversion: decoded `.includeInsideStatement` yields guard facts. -/
theorem parseErrorCode?_includeInsideStatement_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .includeInsideStatement →
    ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
      s.errorEvidence? =
        some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness)) := by
  intro h_code
  exact parseErrorCode?_includeInsideStatement_payload_inversion (s := s) h_code

/-- Backward-compatible alias for include-in-inner-scope guard facts. -/
theorem parseErrorCode?_includeInInnerScope_guardFacts_of_gateWitness
    (s : DB) :
    s.parseErrorCode? = some .includeInInnerScope →
    ∃ pos depth inStatement allowIncludeInnerScopeWitness,
      s.errorEvidence? =
        some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness)) := by
  intro h_code
  exact parseErrorCode?_includeInInnerScope_guardFacts (s := s) h_code

/-- Backward-compatible alias for include-inside-statement guard facts. -/
theorem parseErrorCode?_includeInsideStatement_guardFacts_of_gateWitness
    (s : DB) :
    s.parseErrorCode? = some .includeInsideStatement →
    ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
      s.errorEvidence? =
        some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness)) := by
  intro h_code
  exact parseErrorCode?_includeInsideStatement_guardFacts (s := s) h_code

end DB
end Verify
end Metamath
