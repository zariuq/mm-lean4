import Lake
open Lake DSL

package «mm-lean4» where
  -- TODO: Enable strict mode once Verify.lean is updated
  -- moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.20.0-rc2"

@[default_target]
lean_lib Metamath where
  -- KernelClean: Phase 1 minimal axiomatic skeleton (bottom-up strategy)
  -- AllM: Phase 2 allM extraction lemmas
  -- KernelSkeleton: archived (parse errors)
  -- Kernel: archived (185 errors)
  roots := #[`Metamath.Spec, `Metamath.Verify, `Metamath.Bridge, `Metamath.KernelExtras, `Metamath.AllM, `Metamath.KernelClean]

@[default_target]
lean_lib MetamathExperimental where
  roots := #[`Metamath.Translate]

@[default_target]
lean_exe «mm-lean4» where
  root := `Metamath
