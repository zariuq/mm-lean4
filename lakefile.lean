import Lake
open Lake DSL

package «mm-lean4» where
  -- TODO: Enable strict mode once Verify.lean is updated
  -- moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]

@[default_target]
lean_lib Metamath where
  roots := #[`Metamath.Spec, `Metamath.Verify, `Metamath.Kernel]

@[default_target]
lean_lib MetamathExperimental where
  roots := #[`Metamath.Translate]

@[default_target]
lean_exe «mm-lean4» where
  root := `Metamath
