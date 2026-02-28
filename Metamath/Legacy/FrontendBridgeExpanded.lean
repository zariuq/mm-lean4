import Metamath.FrontendBridge
import Metamath.VerifyIncludeBoundary

namespace Metamath.Legacy.FrontendBridge

open Metamath.Verify
open Metamath.Verify.FrontendBridge
open Metamath.Spec.Frontend

/-- `checkExpandedResult` in-inner-scope code implies front-end include inadmissibility. -/
theorem checkExpandedResult_inInnerScope_implies_frontendNotAdmissible
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    (checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_inInnerScope_guardFacts config pos depth inStatement h_allow h_depth h_code with
    ⟨h_allow, h_depth_ne_zero⟩
  have h_lhs_false : (!config.allowIncludeInnerScope && depth > 0) = false := h_adm.1
  have h_depth_pos : depth > 0 := Nat.pos_iff_ne_zero.mpr h_depth_ne_zero
  have h_lhs_true : (!config.allowIncludeInnerScope && depth > 0) = true := by
    simp [h_allow, h_depth_pos]
  simp [h_lhs_true] at h_lhs_false

/-- `checkExpandedResult` in-inner-scope code implies front-end include inadmissibility
from the pure include-gate witness. -/
theorem checkExpandedResult_inInnerScope_implies_frontendNotAdmissible_of_gate
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config depth inStatement pos =
        some (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)) :
    (checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_inInnerScope_guardFacts_of_gate
      config pos depth inStatement h_gate h_code with ⟨h_allow, h_depth_ne_zero⟩
  have h_lhs_false : (!config.allowIncludeInnerScope && depth > 0) = false := h_adm.1
  have h_depth_pos : depth > 0 := Nat.pos_iff_ne_zero.mpr h_depth_ne_zero
  have h_lhs_true : (!config.allowIncludeInnerScope && depth > 0) = true := by
    simp [h_allow, h_depth_pos]
  simp [h_lhs_true] at h_lhs_false

/-- `checkExpandedResult` inside-statement code implies front-end include inadmissibility. -/
theorem checkExpandedResult_insideStatement_implies_frontendNotAdmissible
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    (checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_insideStatement_guardFacts config pos scopeDepth inStatement h_allow h_stmt h_code with
    ⟨h_allow, h_stmt⟩
  have h_rhs_false : (!config.allowTokenSplicing && inStatement) = false := h_adm.2
  have h_rhs_true : (!config.allowTokenSplicing && inStatement) = true := by
    simp [h_allow, h_stmt]
  simp [h_rhs_true] at h_rhs_false

/-- `checkExpandedResult` inside-statement code implies front-end include inadmissibility
from the pure include-gate witness. -/
theorem checkExpandedResult_insideStatement_implies_frontendNotAdmissible_of_gate
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config scopeDepth inStatement pos =
        some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)) :
    (checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_insideStatement_guardFacts_of_gate
      config pos scopeDepth inStatement h_gate h_code with ⟨h_allow, h_stmt⟩
  have h_rhs_false : (!config.allowTokenSplicing && inStatement) = false := h_adm.2
  have h_rhs_true : (!config.allowTokenSplicing && inStatement) = true := by
    simp [h_allow, h_stmt]
  simp [h_rhs_true] at h_rhs_false

end Metamath.Legacy.FrontendBridge
