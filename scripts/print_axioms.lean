import Metamath.KernelCorrectness
import Metamath.ParserCorrectness
import Metamath.ErrorCodeSemantics
import Metamath.PrefixProvability.Checker
import Metamath.IncludeInterpretation
import Metamath.StoredStatementSoundness
import Metamath.RunEmission
import Metamath.CheckerCompleteness
import Metamath.Tests.CheckerCompletenessCalibration
import Metamath.Spec.FixedFrameCounterexample
import Metamath.SourceCompleteness

/-! # Axiom Audit Script

This script prints the Lean `#print axioms` output for the main adequacy,
completeness, and certification theorems.

Run with: `lake env lean scripts/print_axioms.lean`
-/

-- Proof runs (expression level) in a parsed database, and at any database state
#print axioms Metamath.Kernel.proofChecker_normal_acceptance_iff_specProvable_in_parsedDB
#print axioms Metamath.ParserEquivalence.normalFoldSucceeds_iff_specProvable
#print axioms Metamath.ParserEquivalence.anyFormatFoldSucceeds_iff_specProvable
#print axioms Metamath.ParserEquivalence.proofChecker_normal_iff_frameDerivable_in_parsedDB
#print axioms Metamath.ParserAnyFormatEquivalence.ProofReachableZ_iff_NormalProofReachable

-- The Metamath book's Appendix C (pre-statements, closure) as theorems about Mario Carneiro's
-- `Statement.Provable`
#print axioms Metamath.Statement.provable_iff_exists_extension
#print axioms Metamath.Statement.provable_iff_exists_finite_extension
#print axioms Metamath.Derivable.subst

-- Completeness for Mario Carneiro's declarative semantics, via extended frames
#print axioms Metamath.Spec.Completeness.statementProvable_iff_exists_extendedFrame
#print axioms Metamath.Spec.Completeness.originalStatementProvable_iff_exists_extendedFrame
#print axioms Metamath.Spec.Completeness.statementProvable_iff_exists_extendDummies
#print axioms Metamath.Spec.Completeness.exists_extendDummies_of_statementProvable
#print axioms Metamath.Spec.DummyExtension.exists_dummies_of_statementProvable
#print axioms Metamath.Spec.DeclarativeOriginal.provable_iff
#print axioms Metamath.Spec.DeclarativeOriginal.statementProvable_iff
#print axioms Metamath.Spec.Equivalence.dbToAxioms_trimmed
#print axioms Metamath.CheckerCompleteness.statementProvable_of_anyFormatFoldSucceeds

-- The checker at a database state between statements: acceptance after declaring dummy variables
-- iff provability in Mario Carneiro's semantics
#print axioms Metamath.CheckerCompleteness.acceptedWithDummies_iff_statementProvable
#print axioms Metamath.SourceCompleteness.acceptedWithDummies_iff_statementProvable_afterSource
#print axioms Metamath.AssertDv.feedAll_init_assertDvVarsInFrame
#print axioms Metamath.AssertDv.checkBytesCore_assertDvVarsInFrame?_eq_true
#print axioms Metamath.CheckerCompleteness.verify_impl_complete_exact
#print axioms Metamath.CheckerCompleteness.declareDummies_stateInv
#print axioms Metamath.CheckerCompleteness.trimFrame'_ok_of_dummy_floats
#print axioms Metamath.CheckerCompleteness.extendedFrame_of_trim
#print axioms Metamath.CheckerCompleteness.acceptedWithGeneratedDummies_of_statementProvable
#print axioms Metamath.Spec.Provable.dv_congr

-- Source text: the parser reads rendered declarations and a normal proof after a prefix and
-- stores exactly the claimed statement iff it is provable in Mario Carneiro's semantics
#print axioms Metamath.SourceCompleteness.statementProvable_iff_sourceAccepts
#print axioms Metamath.SourceCompleteness.statementProvable_iff_sourceAccepts_originalRule
#print axioms Metamath.SourceCompleteness.statementProvable_iff_fileAccepts_originalRule
#print axioms Metamath.SourceCompleteness.exists_toFrame_of_trim
#print axioms Metamath.SourceCompleteness.afterSource_declTokens
#print axioms Metamath.SourceCompleteness.sourceAccepts_toDatabaseTotal
#print axioms Metamath.SourceCompleteness.statementProvable_iff_fileAccepts
#print axioms Metamath.SourceCompleteness.fileAccepts_verified
#print axioms Metamath.SourceCompleteness.check_accepts_of_statementProvable
#print axioms Metamath.SourceCompleteness.statementProvable_of_checkBytes
#print axioms Metamath.SourceCompleteness.statementProvable_of_check
#print axioms Metamath.SourceCompleteness.checkBytes_errorNotRequest
#print axioms Metamath.SourceCompleteness.feed_noRequest
#print axioms Metamath.SourceCompleteness.runTokens_render
#print axioms Metamath.SourceCompleteness.afterSource_invariants
#print axioms Metamath.SourceCompleteness.feedAll_init_sourceInv
#print axioms Metamath.SourceCompleteness.afterSource_append_renderText
#print axioms Metamath.SourceCompleteness.feedToken_congr
#print axioms Metamath.SourceCompleteness.runTokens_declTokens
#print axioms Metamath.SourceCompleteness.runTokens_thmTokens_iff
#print axioms Metamath.WF.wellFormed?_of_wellFormedDB

-- `Verify.check` on a single root file, and the stored-`$d` invariant through the include driver
#print axioms Metamath.RootFileCheck.check_root_bridge
#print axioms Metamath.RootFileCheck.check_eq_checkBytes_of_ok
#print axioms Metamath.RootFileCheck.checkBytes_eq_of_check_ok
#print axioms Metamath.RootFileCheck.check_assertDvVarsInFrame
#print axioms Metamath.RootFileCheck.runDriverLoop_ok_dvDriverInv

-- At one fixed frame: a missing dummy variable, and a missing optional `$d`
#print axioms Metamath.Spec.FixedFrameCounterexample.not_specProvable_thm
#print axioms Metamath.Spec.FixedFrameCounterexample.not_specProvable_of_no_dv
#print axioms Metamath.Spec.FixedFrameCounterexample.exists_extendedFrame_with_dv

-- Print axioms for supporting theorems
#print axioms Metamath.ParserCorrectness.structure_preserving_maintains_wf
#print axioms Metamath.ErrorCodeSemantics.checkBytes_parseErrorCode?_guardFacts_total
#print axioms Metamath.PrefixProvability.Checker.checkBytes_prefix_provable_certified
#print axioms Metamath.PrefixProvability.Checker.checkBytes_finalState_finishProofEvent_certified
#print axioms Metamath.ErrorCodeSemantics.checkBytes_parseErrorCode?_fullyCertified

-- Include-aware assertion-origin and registry-chronology theorems
#print axioms Metamath.PrefixProvability.Checker.check_assert_origin_provable
#print axioms Metamath.PrefixProvability.Checker.check_registry_insertionHistory_exactly_one
#print axioms Metamath.PrefixProvability.Checker.check_sound_registry_insertionHistory
#print axioms Metamath.PrefixProvability.Checker.check_knife_registry_insertionHistory

-- Declarative reference-policy selection and runtime binding
#print axioms Metamath.Verify.ModeConfig.exe_selects_metamathExeIncludePolicy
#print axioms Metamath.Verify.ModeConfig.knife_selects_metamathKnifeIncludePolicy
#print axioms Metamath.Verify.ModeConfig.knife_selects_metamathKnifeCompressedProofPolicy
#print axioms Metamath.Verify.ModeConfig.exe_selects_metamathExeAcceptanceRequirement
#print axioms Metamath.Verify.ModeConfig.knife_selects_metamathKnifeAcceptanceRequirement
#print axioms Metamath.Verify.ParserState.popExhaustedFrame_spliceExceptComments_rejects_comment
#print axioms Metamath.PrefixProvability.Checker.check_assertions_selfCitable
#print axioms Metamath.PrefixProvability.Checker.check_sound_assertions_selfCitable
#print axioms Metamath.PrefixProvability.Checker.check_knife_assertions_selfCitable

-- Exact stored-statement and source-$a-only soundness crowns
#print axioms Metamath.Spec.StoredStatement.replaceDerivedAxioms
#print axioms Metamath.StoredStatementSoundness.Runtime.check_storedStatements_writtenProof
#print axioms Metamath.StoredStatementSoundness.Runtime.check_every_theorem_provable_from_trace_axiom_events

-- Execution-indexed emission chronology: refinement, determinism, and the
-- run-indexed derived-rule-elimination crown
#print axioms Metamath.RunEmission.check_emission_insertionHistory
#print axioms Metamath.RunEmission.SinglePassEmission.unique
#print axioms Metamath.RunEmission.check_execution_insertionHistory_exactly_one
#print axioms Metamath.RunEmission.check_every_theorem_provable_from_run_axiom_events
#print axioms Metamath.RunEmission.check_sound_execution_insertionHistory
#print axioms Metamath.RunEmission.check_knife_execution_insertionHistory
