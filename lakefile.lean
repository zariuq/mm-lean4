import Lake
open Lake DSL

package «mm-lean4» where
  -- TODO: Enable strict mode once Verify.lean is updated
  -- moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.24.0"

@[default_target]
lean_lib Metamath where
  -- Active modules (all compile cleanly):
  -- Spec: Formal specification of Metamath verification
  -- ByteSliceCompat: Compatibility layer for Std.ByteSlice (Batteries 4.24.0+)
  -- Verify: Implementation of proof checker
  -- ArrayListExt: Centralized array/list infrastructure lemmas (Batteries 4.24.0+)
  -- Bridge: Implementation-to-spec bridge functions
  -- KernelExtras: Helper lemmas for kernel verification
  -- AllM: Phase 2 allM extraction lemmas
  -- KernelClean: Main kernel soundness proof (Phase 1-7)
  -- ValidateDB: Database format validation tests
  -- ParserInvariants: Parser correctness theorems (eliminate axioms!)
  -- ParserProofs: Proofs of parser axioms by code inspection
  roots := #[`Metamath.Spec, `Metamath.ByteSliceCompat, `Metamath.Verify, `Metamath.ArrayListExt, `Metamath.Bridge, `Metamath.KernelExtras, `Metamath.AllM, `Metamath.KernelClean, `Metamath.ValidateDB, `Metamath.ParserInvariants, `Metamath.ParserProofs]

@[default_target]
lean_lib MetamathExperimental where
  roots := #[`Metamath.Translate]

@[default_target]
lean_exe «mm-lean4» where
  root := `Metamath

lean_exe validateDB where
  root := `Metamath.ValidateDB
  supportInterpreter := true
