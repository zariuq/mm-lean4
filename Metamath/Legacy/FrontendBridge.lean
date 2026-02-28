import Metamath.FrontendBridge
import Metamath.Legacy.FrontendBridgeExpanded
import Metamath.Legacy.Runtime
import Metamath.Spec.Frontend

namespace Metamath.Legacy.FrontendBridge

open Metamath.Verify
open Metamath.Verify.FrontendBridge
open Metamath.Spec.Frontend

/-- Two-pass legacy bridge: include in-inner-scope expansion error binds result and
front-end inadmissibility. Kept in legacy module for compatibility only. -/
theorem checkTwoPassLegacy_inInnerScope_error_implies_frontendNotAdmissible
    (fname : String) (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_expand :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16) (Std.HashSet.emptyWithCapacity 16) config =
        pure (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)))
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    checkTwoPassLegacy fname config =
      pure (checkExpandedResult config
        (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))) ∧
    ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement := by
  constructor
  · unfold checkTwoPassLegacy
    rw [h_expand]
    rfl
  · have h_code :
        (checkExpandedResult config
          (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
          some .includeInInnerScope := by
      simp [checkExpandedResult, includePreprocessErrorDB_parseErrorCode, IncludeError.code]
    exact checkExpandedResult_inInnerScope_implies_frontendNotAdmissible
      config pos depth inStatement h_allow h_depth h_code

/-- Backward-compatible legacy theorem alias.
Prefer `checkSinglePass_inInnerScope_error_implies_frontendNotAdmissible`
for new single-pass integrations. -/
theorem check_inInnerScope_of_expandIncludes_error_implies_frontendNotAdmissible
    (fname : String) (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_expand :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16) (Std.HashSet.emptyWithCapacity 16) config =
        pure (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)))
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    checkTwoPassLegacy fname config =
      pure (checkExpandedResult config
        (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))) ∧
    ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement :=
  checkTwoPassLegacy_inInnerScope_error_implies_frontendNotAdmissible
    fname config pos depth inStatement h_expand h_allow h_depth

/-- Two-pass legacy bridge: include inside-statement expansion error binds result and
front-end inadmissibility. Kept in legacy module for compatibility only. -/
theorem checkTwoPassLegacy_insideStatement_error_implies_frontendNotAdmissible
    (fname : String) (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_expand :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16) (Std.HashSet.emptyWithCapacity 16) config =
        pure (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)))
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    checkTwoPassLegacy fname config =
      pure (checkExpandedResult config
        (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))) ∧
    ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  constructor
  · unfold checkTwoPassLegacy
    rw [h_expand]
    rfl
  · have h_code :
        (checkExpandedResult config
          (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
          some .includeInsideStatement := by
      simp [checkExpandedResult, includePreprocessErrorDB_parseErrorCode, IncludeError.code]
    exact checkExpandedResult_insideStatement_implies_frontendNotAdmissible
      config pos scopeDepth inStatement h_allow h_stmt h_code

/-- Backward-compatible legacy theorem alias.
Prefer `checkSinglePass_insideStatement_error_implies_frontendNotAdmissible`
for new single-pass integrations. -/
theorem check_insideStatement_of_expandIncludes_error_implies_frontendNotAdmissible
    (fname : String) (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_expand :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16) (Std.HashSet.emptyWithCapacity 16) config =
        pure (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)))
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    checkTwoPassLegacy fname config =
      pure (checkExpandedResult config
        (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))) ∧
    ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement :=
  checkTwoPassLegacy_insideStatement_error_implies_frontendNotAdmissible
    fname config pos scopeDepth inStatement h_expand h_allow h_stmt

end Metamath.Legacy.FrontendBridge
