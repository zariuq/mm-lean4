import Metamath.FrontendBridge
import Metamath.FrontendCertified
import Metamath.VerifyEvidenceThms

namespace Metamath.Verify.FrontendAudit

open Metamath.Spec.Frontend
open Metamath.Verify.FrontendBridge

/-- Audit canary: local front-end gate equivalences compile together. -/
theorem audit_frontend_local_gate_equiv_bundle :
    (∀ (db : DB) (sym : String),
      db.djvarsScopeViolation? sym = none ↔
        DjvarsSymbolAdmissible (DB.toDjvarsState db) sym) ∧
    (∀ (db : DB) (sym : String),
      db.mathSymbolViolation? sym = none ↔
        MathSymbolAdmissible (DB.toMathSymbolState db) sym) ∧
    (∀ (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat),
      includeDirectiveViolation? config scopeDepth inStatement pos = none ↔
        IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement) ∧
    (∀ (db : DB),
      ParserState.topLevelEssViolation? db = none ↔
        TopLevelEssentialAdmissible (DB.toTopLevelEssState db)) := by
  constructor
  · intro db sym
    exact DB.djvarsScopeViolation?_none_iff_frontendAdmissible db sym
  · constructor
    · intro db sym
      exact DB.mathSymbolViolation?_none_iff_frontendAdmissible db sym
    · constructor
      · intro config scopeDepth inStatement pos
        exact includeDirectiveViolation?_none_iff_frontendAdmissible
          config scopeDepth inStatement pos
      · intro db
        exact topLevelEssViolation?_none_iff_frontendAdmissible db

/-- Audit canary: core scope-family decoded codes expose canonical certified witnesses. -/
theorem audit_checkBytes_scopeFamily_certifiedWitness_exists_bundle
    (arr : ByteArray) (config : ModeConfig) :
    ((checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
      ∃ rejectToplevelEssWitness scopeDepthWitness,
        (checkBytes arr config).errorEvidence? =
          some (.scopeDecl (.topLevelEssentialNotAllowed)) ∧
        rejectToplevelEssWitness = true ∧
        scopeDepthWitness = 0) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
      ∃ sym isSymWitness,
        (checkBytes arr config).errorEvidence? =
          some (.scopeDecl (.tokenNotConstantOrVariable sym)) ∧
        isSymWitness = false) := by
  constructor
  · intro h_code
    exact checkBytes_topLevelEssentialNotAllowed_certifiedWitness_exists arr config h_code
  · intro h_code
    exact checkBytes_tokenNotConstantOrVariable_certifiedWitness_exists arr config h_code

/-- Audit canary: include-family decoded codes expose canonical certified witnesses. -/
theorem audit_checkBytes_includeFamily_certifiedWitness_exists_bundle
    (arr : ByteArray) (config : ModeConfig) :
    ((checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
      ∃ pos depth inStatement allowIncludeInnerScopeWitness,
        (checkBytes arr config).errorEvidence? =
          some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness))) ∧
    ((checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
      ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
        (checkBytes arr config).errorEvidence? =
          some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness))) := by
  constructor
  · intro h_code
    exact checkBytes_includeInInnerScope_certifiedWitness_exists arr config h_code
  · intro h_code
    exact checkBytes_includeInsideStatement_certifiedWitness_exists arr config h_code

/-- Audit canary: decoded include codes at `checkExpandedResult` imply front-end inadmissibility. -/
theorem audit_checkExpandedResult_include_frontendNotAdmissible_bundle
    (config : ModeConfig) (pos depth scopeDepth : Nat) (inStatement : Bool)
    (h_allow_inner : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0)
    (h_allow_stmt : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    ((checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement) ∧
    ((checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement) := by
  constructor
  · intro h_code
    exact checkExpandedResult_inInnerScope_implies_frontendNotAdmissible
      config pos depth inStatement h_allow_inner h_depth h_code
  · intro h_code
    exact checkExpandedResult_insideStatement_implies_frontendNotAdmissible
      config pos scopeDepth inStatement h_allow_stmt h_stmt h_code

/-- Audit canary: include inadmissibility at `checkExpandedResult` can also be discharged
directly from pure include-gate witnesses (no manual boolean assumptions). -/
theorem audit_checkExpandedResult_include_frontendNotAdmissible_of_gate_bundle
    (config : ModeConfig) (pos depth scopeDepth : Nat) (inStatement : Bool)
    (h_gate_inner :
      includeDirectiveViolation? config depth inStatement pos =
        some (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))
    (h_gate_stmt :
      includeDirectiveViolation? config scopeDepth inStatement pos =
        some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)) :
    ((checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement) ∧
    ((checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement) := by
  constructor
  · intro h_code
    exact checkExpandedResult_inInnerScope_implies_frontendNotAdmissible_of_gate
      config pos depth inStatement h_gate_inner h_code
  · intro h_code
    exact checkExpandedResult_insideStatement_implies_frontendNotAdmissible_of_gate
      config pos scopeDepth inStatement h_gate_stmt h_code

/-- Audit canary: include-family decoded codes at `checkExpandedResult` are evidence-first
and exclude the legacy raw-error compatibility payload. -/
theorem audit_checkExpandedResult_include_nonInternal_evidenceFirst_bundle
    (config : ModeConfig) (pos depth scopeDepth : Nat) (inStatement : Bool) :
    ((checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope →
      ∃ ev,
        (checkExpandedResult config
          (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).errorEvidence? =
          some ev ∧
        ev ≠ .internalGate false false false) ∧
    ((checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement →
      ∃ ev,
        (checkExpandedResult config
          (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).errorEvidence? =
          some ev ∧
        ev ≠ .internalGate false false false) := by
  constructor
  · intro h_code
    exact checkExpandedResult_nonInternal_evidenceFirst
      config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))
      .includeInInnerScope h_code (by simp)
  · intro h_code
    exact checkExpandedResult_nonInternal_evidenceFirst
      config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))
      .includeInsideStatement h_code (by simp)

/-- Audit canary: include-family reachability boundary between parser core and include
preprocessor entrypoint.
`checkExpandedResult` is exactly `checkBytes` on `.ok` payloads and exactly
`includePreprocessErrorDB` on `.error` payloads. -/
theorem audit_includeFamily_reachability_boundary_checkBytes_vs_checkExpandedResult
    (config : ModeConfig) (processed : ByteArray)
    (seen : Std.HashSet String) (err : IncludeError) :
    (checkExpandedResult config (.ok (processed, seen)) = checkBytes processed config) ∧
    (checkExpandedResult config (.error err) = includePreprocessErrorDB config err) ∧
    ((checkExpandedResult config (.error err)).parseErrorCode? = some (IncludeError.code err)) := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp [checkExpandedResult, includePreprocessErrorDB_parseErrorCode]

/-- Audit canary: non-internal scope-family decoded codes exclude the legacy raw-error payload. -/
theorem audit_checkBytes_scopeFamily_nonInternal_excludes_legacy_internalGate_false_false_false
    (arr : ByteArray) (config : ModeConfig) :
    ((checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
      (checkBytes arr config).errorEvidence? ≠ some (.internalGate false false false)) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
      (checkBytes arr config).errorEvidence? ≠ some (.internalGate false false false)) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
      (checkBytes arr config).errorEvidence? ≠ some (.internalGate false false false)) := by
  constructor
  · intro h_code
    exact checkBytes_nonInternal_excludes_internalGate_false_false_false
      arr config .topLevelEssentialNotAllowed h_code (by simp)
  · constructor
    · intro h_code
      exact checkBytes_nonInternal_excludes_internalGate_false_false_false
        arr config .tokenNotConstantOrVariable h_code (by simp)
    · intro h_code
      exact checkBytes_nonInternal_excludes_internalGate_false_false_false
        arr config .tokenNotInScope h_code (by simp)

/-- Audit canary: decoded non-internal front-end families are evidence-first and
exclude the legacy raw-string-compatible internal payload. -/
theorem audit_checkBytes_nonInternal_evidenceFirst_bundle
    (arr : ByteArray) (config : ModeConfig) :
    ((checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
      ∃ ev,
        (checkBytes arr config).errorEvidence? = some ev ∧
        ev ≠ .internalGate false false false) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
      ∃ ev,
        (checkBytes arr config).errorEvidence? = some ev ∧
        ev ≠ .internalGate false false false) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
      ∃ ev,
        (checkBytes arr config).errorEvidence? = some ev ∧
        ev ≠ .internalGate false false false) ∧
    ((checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
      ∃ ev,
        (checkBytes arr config).errorEvidence? = some ev ∧
        ev ≠ .internalGate false false false) ∧
    ((checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
      ∃ ev,
        (checkBytes arr config).errorEvidence? = some ev ∧
        ev ≠ .internalGate false false false) := by
  constructor
  · intro h_code
    exact checkBytes_nonInternal_evidenceFirst
      arr config .topLevelEssentialNotAllowed h_code (by simp)
  · constructor
    · intro h_code
      exact checkBytes_nonInternal_evidenceFirst
        arr config .tokenNotConstantOrVariable h_code (by simp)
    · constructor
      · intro h_code
        exact checkBytes_nonInternal_evidenceFirst
          arr config .tokenNotInScope h_code (by simp)
      · constructor
        · intro h_code
          exact checkBytes_nonInternal_evidenceFirst
            arr config .includeInInnerScope h_code (by simp)
        · intro h_code
          exact checkBytes_nonInternal_evidenceFirst
            arr config .includeInsideStatement h_code (by simp)

/-- Audit bundle: consume the global dispatcher theorem from `FrontendCertified`. -/
theorem audit_checkBytes_frontendEvidenceCertified_bundle
    (arr : ByteArray) (config : ModeConfig) :
    ((checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
      Metamath.Verify.FrontendCertified.FrontendEvidenceCertified (checkBytes arr config)) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
      Metamath.Verify.FrontendCertified.FrontendEvidenceCertified (checkBytes arr config)) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
      Metamath.Verify.FrontendCertified.FrontendEvidenceCertified (checkBytes arr config)) :=
  Metamath.Verify.FrontendCertified.checkBytes_frontendEvidenceCertified arr config

/-- Audit bundle: code-only frontend inadmissibility lifts from `checkBytes`, under the
certified-run invariant contract. -/
theorem audit_checkBytes_scopeFamily_frontendNotAdmissible_via_certifiedRun
    (arr : ByteArray) (config : ModeConfig)
    (h_cert : Metamath.Verify.FrontendCertified.CheckBytesFrontendCertifiedRun arr config) :
    ((checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
      ¬ TopLevelEssentialAdmissible (DB.toTopLevelEssState (checkBytes arr config))) ∧
    ((checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
      ∃ sym, ¬ MathSymbolAdmissible (DB.toMathSymbolState (checkBytes arr config)) sym) := by
  constructor
  · intro h_code
    exact checkBytes_topLevelEssentialNotAllowed_implies_frontendNotAdmissible
      arr config h_cert h_code
  · intro h_code
    exact checkBytes_tokenNotConstantOrVariable_implies_frontendNotAdmissible
      arr config h_cert h_code

end Metamath.Verify.FrontendAudit
