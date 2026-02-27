import Metamath.Verify
import Metamath.VerifyIncludeThms
import Metamath.VerifyScopeThms

namespace Metamath.Verify.FrontendCertified

/-- Certified-run invariant for lifting decoded `checkBytes` frontend-family codes to
live frontend gate facts.

This packages the two ingredients needed for non-shape semantic lifts:
1) emission-site gate facts (for the specific error family), and
2) post-error preservation of the relevant live DB fields. -/
structure CheckBytesFrontendCertifiedRun
    (arr : ByteArray) (config : ModeConfig) : Prop where
  topLevelEssential_gateFacts :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
      (checkBytes arr config).config.rejectToplevelEss = true ∧
      (checkBytes arr config).scopes.size = 0
  tokenNotConstOrVar_gateFacts :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
      ∃ sym,
        (checkBytes arr config).errorEvidence? =
          some (.scopeDecl (.tokenNotConstantOrVariable sym)) ∧
        (checkBytes arr config).isSym sym = false

/-- Canonical certification contract for the three front-end target families.

After canonical constructor lifting, certification is a direct code->evidence
shape implication without witness-parameter side conditions. -/
def FrontendEvidenceCertified (db : DB) : Prop :=
  (db.parseErrorCode? = some .topLevelEssentialNotAllowed →
    db.errorEvidence? = some (.scopeDecl .topLevelEssentialNotAllowed)) ∧
  (db.parseErrorCode? = some .tokenNotConstantOrVariable →
    ∃ sym, db.errorEvidence? = some (.scopeDecl (.tokenNotConstantOrVariable sym))) ∧
  (db.parseErrorCode? = some .tokenNotInScope →
    ∃ sym, db.errorEvidence? = some (.scopeDecl (.tokenNotInScope sym)))

/-- Global DB-level certification: decoded target codes always carry canonical evidence. -/
theorem frontendEvidenceCertified (db : DB) : FrontendEvidenceCertified db := by
  constructor
  · intro h_code
    exact DB.parseErrorCode?_topLevelEssentialNotAllowed_guardFacts (s := db) h_code
  · constructor
    · intro h_code
      exact DB.parseErrorCode?_tokenNotConstantOrVariable_guardFacts (s := db) h_code
    · intro h_code
      exact DB.parseErrorCode?_tokenNotInScope_guardFacts (s := db) h_code

/-- `feedToken` preserves top-level family certification when this family is emitted. -/
theorem feedToken_preserves_topLevelEssentialNotAllowed_certification
    (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (_h_code : (s.feedToken pos tk).db.parseErrorCode? = some .topLevelEssentialNotAllowed) :
    FrontendEvidenceCertified (s.feedToken pos tk).db := by
  exact frontendEvidenceCertified ((s.feedToken pos tk).db)

/-- `feedToken` preserves token-not-const/var family certification when emitted. -/
theorem feedToken_preserves_tokenNotConstantOrVariable_certification
    (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (_h_code : (s.feedToken pos tk).db.parseErrorCode? = some .tokenNotConstantOrVariable) :
    FrontendEvidenceCertified (s.feedToken pos tk).db := by
  exact frontendEvidenceCertified ((s.feedToken pos tk).db)

/-- `feedToken` preserves token-not-in-scope family certification when emitted. -/
theorem feedToken_preserves_tokenNotInScope_certification
    (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (_h_code : (s.feedToken pos tk).db.parseErrorCode? = some .tokenNotInScope) :
    FrontendEvidenceCertified (s.feedToken pos tk).db := by
  exact frontendEvidenceCertified ((s.feedToken pos tk).db)

/-- Code-only template theorem: top-level strict-mode code already yields certified front-end evidence. -/
theorem checkBytes_topLevelEssentialNotAllowed_codeOnly_template
    (arr : ByteArray) (config : ModeConfig)
    (_h_code : (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed) :
    FrontendEvidenceCertified (checkBytes arr config) := by
  exact frontendEvidenceCertified (checkBytes arr config)

/-- Global unconditional certification bundle for the three target front-end families. -/
theorem checkBytes_frontendEvidenceCertified
    (arr : ByteArray) (config : ModeConfig) :
    ((checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed ->
        FrontendEvidenceCertified (checkBytes arr config)
    ) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable ->
        FrontendEvidenceCertified (checkBytes arr config)
    ) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotInScope ->
        FrontendEvidenceCertified (checkBytes arr config)
    ) := by
  constructor
  · intro h_code
    exact frontendEvidenceCertified (checkBytes arr config)
  · constructor
    · intro h_code
      exact frontendEvidenceCertified (checkBytes arr config)
    · intro h_code
      exact frontendEvidenceCertified (checkBytes arr config)

/-- Include-family code-only template: include-in-inner-scope guard facts. -/
theorem checkBytes_includeInInnerScope_codeOnly_template
    (arr : ByteArray) (config : ModeConfig)
    (h_code : (checkBytes arr config).parseErrorCode? = some .includeInInnerScope) :
    ∃ pos depth inStatement allowIncludeInnerScopeWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness)) :=
  checkBytes_parseErrorCode?_includeInInnerScope_guardFacts arr config h_code

/-- Include-family code-only template: include-inside-statement guard facts. -/
theorem checkBytes_includeInsideStatement_codeOnly_template
    (arr : ByteArray) (config : ModeConfig)
    (h_code : (checkBytes arr config).parseErrorCode? = some .includeInsideStatement) :
    ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness)) :=
  checkBytes_parseErrorCode?_includeInsideStatement_guardFacts arr config h_code

end Metamath.Verify.FrontendCertified

namespace Metamath.FrontendCertified

export Metamath.Verify.FrontendCertified
  (CheckBytesFrontendCertifiedRun
   FrontendEvidenceCertified
   frontendEvidenceCertified
   feedToken_preserves_topLevelEssentialNotAllowed_certification
   feedToken_preserves_tokenNotConstantOrVariable_certification
   feedToken_preserves_tokenNotInScope_certification
   checkBytes_topLevelEssentialNotAllowed_codeOnly_template
   checkBytes_frontendEvidenceCertified
   checkBytes_includeInInnerScope_codeOnly_template
   checkBytes_includeInsideStatement_codeOnly_template)

end Metamath.FrontendCertified
