import Metamath.Verify
import Metamath.VerifyDBConfigThms
import Metamath.VerifyDBCheckHypThms
import Metamath.VerifyDBPredicateThms
import Metamath.VerifyDBSemanticThms
import Metamath.VerifyDBPayloadThms

namespace Metamath
namespace Verify

-- DB theorem families are split across focused modules:
-- - `VerifyDBConfigThms`: config-preservation and mkError/mutation shape lemmas
-- - `VerifyDBCheckHypThms`: checkHyp equation lemmas
-- - `VerifyDBPredicateThms`: symbol/djvars predicate and insert lookup lemmas
-- - `VerifyDBSemanticThms`: parseErrorCode semantic packaging/soundness lemmas
-- - `VerifyDBPayloadThms`: decoded error payload inversion lemmas

end Verify
end Metamath
