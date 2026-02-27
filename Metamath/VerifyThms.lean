import Metamath.Verify
import Metamath.VerifyDBThms
import Metamath.VerifyConformanceThms
import Metamath.VerifyDoneThms
import Metamath.VerifyEvidenceThms
import Metamath.VerifyIncludeThms
import Metamath.VerifyPackagingThms
import Metamath.VerifyProofGuardThms
import Metamath.VerifyRuleCaseThms
import Metamath.VerifyScopeThms
import Metamath.VerifyStabilityThms
import Metamath.VerifyParserPostThms
import Metamath.VerifyParserStateThms
import Metamath.VerifyClauseThms

namespace Metamath
namespace Verify
-- high-level conformance wrappers (ModeConfig certification + §4.2 bridge theorems)
-- moved to `Metamath/VerifyConformanceThms.lean`.

-- evidence-first theorem family moved to `Metamath/VerifyEvidenceThms.lean`.

-- include parseError guard/payload/ruleClause/specClause theorem family moved to `Metamath/VerifyIncludeThms.lean`.
-- scope/topLevelEss guard+payload theorem family moved to `Metamath/VerifyScopeThms.lean`.
-- include evidence-first wrappers moved to `Metamath/VerifyIncludeThms.lean`.
-- ParserState.done EOF theorem family moved to `Metamath/VerifyDoneThms.lean`.

-- parser-entry packaging theorem family moved to `Metamath/VerifyPackagingThms.lean`.

-- parseErrorCode violation/ruleClause theorem family moved to `Metamath/VerifyRuleCaseThms.lean`.
-- proof-check/theorem-finality guard-facts theorem family moved to `Metamath/VerifyProofGuardThms.lean`.

-- parser-state/checkBytes stability & preservation theorem family moved to `Metamath/VerifyStabilityThms.lean`.

end Verify
end Metamath
