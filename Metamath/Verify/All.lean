import Metamath.Verify
import Metamath.Verify.DB
import Metamath.Verify.Conformance
import Metamath.Verify.Done
import Metamath.Verify.Evidence
import Metamath.Verify.Include
import Metamath.Verify.Packaging
import Metamath.Verify.ProofGuard
import Metamath.Verify.RuleCase
import Metamath.Verify.Scope
import Metamath.Verify.Stability
import Metamath.Verify.ParserPost
import Metamath.Verify.ParserState
import Metamath.Verify.Clause

namespace Metamath
namespace Verify
-- high-level conformance wrappers (ModeConfig certification + §4.2 bridge theorems)
-- moved to `Metamath/Verify/Conformance.lean`.

-- evidence-first theorem family moved to `Metamath/Verify/Evidence.lean`.

-- include parseError guard/payload/ruleClause/specClause theorem family moved to `Metamath/Verify/Include.lean`.
-- scope/topLevelEss guard+payload theorem family moved to `Metamath/Verify/Scope.lean`.
-- include evidence-first wrappers moved to `Metamath/Verify/Include.lean`.
-- ParserState.done EOF theorem family moved to `Metamath/Verify/Done.lean`.

-- parser-entry packaging theorem family moved to `Metamath/Verify/Packaging.lean`.

-- parseErrorCode violation/ruleClause theorem family moved to `Metamath/Verify/RuleCase.lean`.
-- proof-check/theorem-finality guard-facts theorem family moved to `Metamath/Verify/ProofGuard.lean`.

-- parser-state/checkBytes stability & preservation theorem family moved to `Metamath/Verify/Stability.lean`.

end Verify
end Metamath
