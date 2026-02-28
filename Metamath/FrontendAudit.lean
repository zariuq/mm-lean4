import Metamath.FrontendBridge
import Metamath.FrontendCertified
import Metamath.VerifyEvidenceThms

namespace Metamath.Verify.FrontendAudit

open Metamath.Spec.Frontend
open Metamath.Verify.FrontendBridge

/-! Primary frontend audit module (single-pass/checkBytes-oriented).

`checkExpandedResult`-centric audit canaries are isolated in
`Metamath/Legacy/FrontendAudit.lean`.
-/

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

/-- Audit canary: default IO entrypoint is the single-pass include driver. -/
theorem audit_check_default_is_singlePass
    (fname : String) (config : ModeConfig) :
    check fname config = checkSinglePass fname config :=
  check_eq_checkSinglePass fname config

end Metamath.Verify.FrontendAudit
