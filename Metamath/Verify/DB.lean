import Metamath.Verify
import Metamath.Verify.DBConfig
import Metamath.Verify.DBCheckHyp
import Metamath.Verify.DBPredicate
import Metamath.Verify.DBSemantic
import Metamath.Verify.DBPayload

namespace Metamath
namespace Verify

-- DB theorem families are split across focused modules:
-- - `Verify.DBConfig`: config-preservation and mkError/mutation shape lemmas
-- - `Verify.DBCheckHyp`: checkHyp equation lemmas
-- - `Verify.DBPredicate`: symbol/djvars predicate and insert lookup lemmas
-- - `Verify.DBSemantic`: parseErrorCode semantic packaging/soundness lemmas
-- - `Verify.DBPayload`: decoded error payload inversion lemmas

end Verify
end Metamath
