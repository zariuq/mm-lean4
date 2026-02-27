import Metamath.FrontendBridge

namespace Metamath.FrontendBridge.LegacyCompatibility

/- Legacy two-pass compatibility exports kept isolated from the main single-pass API.
Prefer `Metamath.FrontendBridge` exports for new integrations. -/
export Metamath.Verify.FrontendBridge
  (checkTwoPassLegacy_inInnerScope_error_implies_frontendNotAdmissible
   checkTwoPassLegacy_insideStatement_error_implies_frontendNotAdmissible
   check_inInnerScope_of_expandIncludes_error_implies_frontendNotAdmissible
   check_insideStatement_of_expandIncludes_error_implies_frontendNotAdmissible)

end Metamath.FrontendBridge.LegacyCompatibility
