import Metamath.KernelClean
import Metamath.ParserCorrectness
import Metamath.ErrorCodeSemantics
import Metamath.PrefixWitnessCheckBytes
import Metamath.IncludeInterpretation
import Metamath.StoredStatementSoundness
import Metamath.RunEmission

/-! # Axiom Audit Script

This script prints the Lean `#print axioms` output for the main soundness and
certification theorems.

Run with: `lake env lean scripts/print_axioms.lean`
-/

-- Print axioms for the main soundness theorem
#print axioms Metamath.Kernel.proofChecker_normal_acceptance_iff_specProvable_in_parsedDB

-- Print axioms for supporting theorems
#print axioms Metamath.ParserCorrectness.structure_preserving_maintains_wf
#print axioms Metamath.ErrorCodeSemantics.checkBytes_parseErrorCode?_guardFacts_total
#print axioms Metamath.PrefixWitnessCheckBytes.checkBytes_prefix_provenance_certified

-- Include-aware assertion-origin and registry-chronology theorems
#print axioms Metamath.PrefixWitnessCheckBytes.checkSinglePass_assert_origin_provable
#print axioms Metamath.PrefixWitnessCheckBytes.checkSinglePass_registry_chronology_exactly_one
#print axioms Metamath.PrefixWitnessCheckBytes.checkSinglePass_soundDefault_registry_chronology
#print axioms Metamath.PrefixWitnessCheckBytes.checkSinglePass_knife_registry_chronology

-- Declarative reference-policy selection and runtime binding
#print axioms Metamath.Verify.ModeConfig.exe_selects_metamathExeIncludePolicy
#print axioms Metamath.Verify.ModeConfig.knife_selects_metamathKnifeIncludePolicy
#print axioms Metamath.Verify.ModeConfig.knife_selects_metamathKnifeCompressedProofPolicy
#print axioms Metamath.Verify.ModeConfig.exe_selects_metamathExeAcceptanceRequirement
#print axioms Metamath.Verify.ModeConfig.knife_selects_metamathKnifeAcceptanceRequirement
#print axioms Metamath.Verify.ParserState.popExhaustedFrame_spliceExceptComments_rejects_comment
#print axioms Metamath.PrefixWitnessCheckBytes.checkSinglePass_assertions_selfCitable
#print axioms Metamath.PrefixWitnessCheckBytes.checkSinglePass_soundDefault_assertions_selfCitable
#print axioms Metamath.PrefixWitnessCheckBytes.checkSinglePass_knife_assertions_selfCitable

-- Exact stored-statement and source-$a-only soundness crowns
#print axioms Metamath.StoredStatementSoundness.Semantic.replaceDerivedAxioms
#print axioms Metamath.StoredStatementSoundness.Runtime.checkSinglePass_storedStatements_writtenProof
#print axioms Metamath.StoredStatementSoundness.Runtime.checkSinglePass_every_theorem_provable_from_trace_axiom_events

-- Execution-indexed emission chronology: refinement, determinism, and the
-- run-indexed derived-rule-elimination crown
#print axioms Metamath.RunEmission.checkSinglePass_emission_chronology
#print axioms Metamath.RunEmission.SinglePassEmission.unique
#print axioms Metamath.RunEmission.checkSinglePass_execution_chronology_exactly_one
#print axioms Metamath.RunEmission.checkSinglePass_every_theorem_provable_from_run_axiom_events
#print axioms Metamath.RunEmission.checkSinglePass_soundDefault_execution_chronology
#print axioms Metamath.RunEmission.checkSinglePass_knife_execution_chronology
