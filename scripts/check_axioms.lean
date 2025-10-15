import Metamath.Kernel

/-! # Axiom Audit Script

This script uses `#print axioms` to show all axioms that the main soundness theorems depend on.

Run with: `lake env lean scripts/check_axioms.lean`
-/

-- Print axioms for the main soundness theorem
#print axioms Metamath.Kernel.verify_impl_sound

-- Print axioms for supporting theorems
#print axioms Metamath.Kernel.fold_maintains_inv_and_provable
#print axioms Metamath.Kernel.stepNormal_preserves_inv
#print axioms Metamath.Kernel.checkHyp_produces_TypedSubst
