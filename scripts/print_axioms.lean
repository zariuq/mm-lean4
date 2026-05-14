import Metamath.KernelClean
import Metamath.ParserCorrectness
import Metamath.ErrorCodeSemantics
import Metamath.PrefixWitnessCheckBytes

/-! # Axiom Audit Script

This script prints the Lean `#print axioms` output for the main soundness and
certification theorems.

Run with: `lake env lean scripts/print_axioms.lean`
-/

-- Print axioms for the main soundness theorem
#print axioms Metamath.Kernel.verify_parser_acceptance_iff_spec_provable

-- Print axioms for supporting theorems
#print axioms Metamath.ParserCorrectness.structure_preserving_maintains_wf
#print axioms Metamath.ErrorCodeSemantics.checkBytes_parseErrorCode?_guardFacts_total
#print axioms Metamath.PrefixWitnessCheckBytes.checkBytes_prefix_provenance_certified
