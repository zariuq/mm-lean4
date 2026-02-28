import Metamath.FrontendAudit
import Metamath.Legacy.FrontendBridgeExpanded

namespace Metamath.Legacy.FrontendAudit

open Metamath.Spec.Frontend
open Metamath.Verify
open Metamath.Verify.FrontendBridge
open Metamath.Legacy.FrontendBridge

/-- Legacy-audit canary: decoded include codes at `checkExpandedResult` imply front-end
inadmissibility. -/
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

/-- Legacy-audit canary: include inadmissibility at `checkExpandedResult` can also be
discharged directly from pure include-gate witnesses. -/
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

/-- Legacy-audit canary: include-family decoded codes at `checkExpandedResult` are
evidence-first and exclude internal-compat payloads. -/
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

/-- Legacy-audit canary: include-family reachability boundary between parser core and
include-preprocessor entrypoint. -/
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

end Metamath.Legacy.FrontendAudit
