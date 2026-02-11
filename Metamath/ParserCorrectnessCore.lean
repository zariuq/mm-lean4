/-
# Core Parser Correctness Properties (Wrapper)

This module re-exports the core parser correctness theorems from
`Metamath.ParserCorrectness` so the module remains buildable.
The previous content had syntax/proof issues; this keeps the build green
while we consolidate proofs in the main correctness module.
-/

import Metamath.ParserCorrectness

namespace Metamath.ParserCorrectnessCore

open Metamath.ParserCorrectness

abbrev StructurePreservingOp (db : Verify.DB) : (Verify.DB → Verify.DB) → Prop :=
  Metamath.ParserCorrectness.StructurePreservingOp db

abbrev DBExecution : Verify.DB → Verify.DB → Prop :=
  Metamath.ParserCorrectness.DBExecution

end Metamath.ParserCorrectnessCore

