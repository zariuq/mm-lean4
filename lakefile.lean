import Lake
open Lake DSL

package «mm-lean4» where
  -- TODO: Enable strict mode once Verify.lean is updated
  -- moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]

require batteries from git "https://github.com/leanprover-community/batteries" @ "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d"

@[default_target]
lean_lib Metamath where
  -- Not built: `Metamath.ZipperTest` (needs lean-auto).
  roots := #[
    -- Specification
    `Metamath.Spec,
    `Metamath.Spec.Derivable,
    `Metamath.Spec.StoredStatement,
    `Metamath.Spec.DummyExtension,
    `Metamath.Spec.DeclarativeOriginal,
    `Metamath.Spec.Completeness,
    `Metamath.Spec.FixedFrameCounterexample,
    -- Verifier
    `Metamath.ByteSliceCompat,
    `Metamath.Verify,
    `Metamath.VerifyIncludeBoundary,
    `Metamath.Verify.Clause,
    `Metamath.Verify.Conformance,
    `Metamath.Verify.DB,
    `Metamath.Verify.DBConfig,
    `Metamath.Verify.DBCheckHyp,
    `Metamath.Verify.DBPredicate,
    `Metamath.Verify.DBPayload,
    `Metamath.Verify.DBSemantic,
    `Metamath.Verify.Done,
    `Metamath.Verify.Evidence,
    `Metamath.Verify.Include,
    `Metamath.Verify.Packaging,
    `Metamath.Verify.ProofGuard,
    `Metamath.Verify.RuleCase,
    `Metamath.Verify.Scope,
    `Metamath.Verify.Check,
    `Metamath.Verify.Stability,
    `Metamath.Verify.ParserPost,
    `Metamath.Verify.ParserState,
    `Metamath.Verify.All,
    -- Completeness
    `Metamath.CheckerCompleteness.Declare,
    `Metamath.CheckerCompleteness.Exact,
    `Metamath.CheckerCompleteness.Trim,
    `Metamath.CheckerCompleteness.Frames,
    `Metamath.AssertDvInvariant,
    `Metamath.SourceCompleteness.Tokens,
    `Metamath.SourceCompleteness.Bytes,
    `Metamath.SourceCompleteness.Invariants,
    `Metamath.SourceCompleteness.Render,
    `Metamath.SourceCompleteness.Compose,
    `Metamath.SourceCompleteness.DeclTokens,
    `Metamath.SourceCompleteness.ThmTokens,
    `Metamath.RootFileCheck,
    `Metamath.SourceCompleteness.NoRequest,
    `Metamath.SourceCompleteness,
    `Metamath.CheckerCompleteness,
    -- Parser, kernel and soundness proofs
    `Metamath.WellFormedness,
    `Metamath.ParserBasics,
    `Metamath.ArrayListExt,
    `Metamath.Bridge,
    `Metamath.KernelExtras,
    `Metamath.DBLemmas,
    `Metamath.AllM,
    `Metamath.KernelCorrectness,
    `Metamath.ParserInvariants,
    `Metamath.HashMapLemmas,
    `Metamath.ParserCorrectness,
    `Metamath.ParserLoopInduction,
    `Metamath.LoopInvariant,
    `Metamath.DBCaseAnalysis,
    `Metamath.ParserInvariantsStep1,
    `Metamath.ParserInvariantPreservation,
    `Metamath.FrontendBridge,
    `Metamath.FrontendCertified,
    `Metamath.PrefixProvenance,
    `Metamath.PrefixTraceCompressed,
    `Metamath.ParserAnyFormatEquivalence,
    `Metamath.ParserEquivalence,
    `Metamath.ErrorCodeSemantics,
    `Metamath.PrefixProvability.Checker,
    `Metamath.StoredStatementSoundness,
    `Metamath.RunEmission,
    `Metamath.VariableActivity,
    `Metamath.IncludeInterpretation,
    `Metamath.ModeInterpretationOrder,
    -- Tests and examples
    `Metamath.ValidateDB,
    `Metamath.CounterexampleInsertError,
    `Metamath.Tests.FrontendSummary,
    `Metamath.Tests.CheckerCompletenessCalibration,
    `Metamath.Tests.SourceCompletenessCalibration,
    `Metamath.Tests.CommentPolicy,
    `Metamath.Tests.TypePolicy,
    `Metamath.ParserEquivalenceExamples,
    `Metamath.ParserSoundnessDemo
  ]

@[default_target]
lean_lib MetamathExperimental where
  roots := #[`Metamath.DeclarativeSpec, `Metamath.DeclarativeSpecDemo]

lean_lib MetamathLegacy where
  roots := #[`Metamath.Legacy.Runtime, `Metamath.Legacy.CompatThms, `Metamath.Legacy.FrontendBridgeExpanded, `Metamath.Legacy.FrontendBridge, `Metamath.Legacy.FrontendAudit, `Metamath.Legacy.All]

@[default_target]
lean_exe «mm-lean4» where
  root := `Metamath

lean_exe validateDB where
  root := `Metamath.ValidateDB
  supportInterpreter := true

lean_exe testCliErrorCode where
  root := `Metamath.Tests.CliErrorCodeFormat
  supportInterpreter := true

lean_exe testCheckSinglePassParity where
  root := `Metamath.Tests.CheckSinglePassParity
  supportInterpreter := true

lean_exe testParserInvariants where
  root := `Metamath.Tests.ParserInvariantTests
  supportInterpreter := true
