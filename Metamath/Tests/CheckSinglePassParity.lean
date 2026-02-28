import Metamath.Verify
import Metamath.Legacy.Runtime

namespace Metamath
namespace Tests

open Verify
open Legacy

/-- Compact observable DB projection used by runtime parity checks. -/
structure DBShape where
  hasError : Bool
  parseErrorCode : Option ParseErrorCode
  evidenceCode : Option ParseErrorCode
  objectsSize : Nat
  scopesSize : Nat
  frameHypsSize : Nat
  frameDjSize : Nat
  interrupt : Bool
  deriving DecidableEq, Repr

/-- Extract observable parser state needed for parity regression checks. -/
def dbShape (db : DB) : DBShape :=
  let evCode := db.errorEvidence?.map ErrorEvidence.code
  {
    hasError := db.error
    parseErrorCode := db.parseErrorCode?
    evidenceCode := evCode
    objectsSize := db.objects.size
    scopesSize := db.scopes.size
    frameHypsSize := db.frame.hyps.size
    frameDjSize := db.frame.dj.size
    interrupt := db.interrupt
  }

/-- Shape respects definitional equality. Useful when wiring wrapper lemmas. -/
theorem dbShape_congr {db1 db2 : DB} (h : db1 = db2) : dbShape db1 = dbShape db2 := by
  cases h
  rfl

private def assertShapeEq (label : String) (legacy single : DBShape) : IO Unit := do
  if legacy != single then
    throw <| IO.userError s!"{label}: shape mismatch\nlegacy={repr legacy}\nsingle={repr single}"

private def runParityCase (label path : String) (config : ModeConfig := {}) : IO Unit := do
  let dbLegacy ← checkTwoPassLegacy path config
  let dbSingle ← checkSinglePass path config
  assertShapeEq label (dbShape dbLegacy) (dbShape dbSingle)
  IO.println s!"✓ {label}"

private def runParityCaseExpectCode
    (label path : String) (expected : ParseErrorCode)
    (config : ModeConfig := {}) : IO Unit := do
  let dbLegacy ← checkTwoPassLegacy path config
  let dbSingle ← checkSinglePass path config
  assertShapeEq label (dbShape dbLegacy) (dbShape dbSingle)
  if dbLegacy.parseErrorCode? != some expected then
    throw <| IO.userError
      s!"{label}: legacy parseErrorCode mismatch, expected {repr expected}, got {repr dbLegacy.parseErrorCode?}"
  if dbSingle.parseErrorCode? != some expected then
    throw <| IO.userError
      s!"{label}: single-pass parseErrorCode mismatch, expected {repr expected}, got {repr dbSingle.parseErrorCode?}"
  IO.println s!"✓ {label}"

/-- Regression: include-depth fuel overflow must decode to includeCycleDetected.
Also checked for legacy/single-pass parity. -/
def runIncludeDepthOverflowRegression : IO Unit := do
  let path := "test_databases/include_depth/root_depth.mm"
  let cfg : ModeConfig := { maxIncludeDepth := 2 }
  let dbLegacy ← checkTwoPassLegacy path cfg
  let dbSingle ← checkSinglePass path cfg
  assertShapeEq "include-depth-overflow" (dbShape dbLegacy) (dbShape dbSingle)
  match dbSingle.parseErrorCode? with
  | some .includeCycleDetected =>
      IO.println "✓ include-depth-overflow decodes as includeCycleDetected"
  | code =>
      throw <| IO.userError
        s!"include-depth-overflow: expected includeCycleDetected, got {repr code}"

/-- End-to-end parity checks between two-pass legacy and single-pass checker. -/
def runCheckSinglePassParitySuite : IO Unit := do
  IO.println "=== checkTwoPassLegacy vs checkSinglePass parity ==="
  runParityCase "invalid_duplicate_floats" "test_databases/invalid_duplicate_floats.mm"
  runParityCase "include_depth_ok" "test_databases/include_depth/root_ok.mm"
  runParityCaseExpectCode
    "include_in_inner_scope_violation"
    "test_databases/include_policy/inner_scope_violation.mm"
    .includeInInnerScope
  runParityCaseExpectCode
    "include_inside_statement_violation"
    "test_databases/include_policy/inside_statement_violation.mm"
    .includeInsideStatement
  runParityCaseExpectCode
    "include_read_failure_violation"
    "test_databases/include_policy/missing_include_read_failure.mm"
    .includeReadFailure
  runParityCaseExpectCode
    "include_cycle_violation"
    "test_databases/include_cycle/root_cycle.mm"
    .includeCycleDetected
  runIncludeDepthOverflowRegression
  IO.println "=== parity suite passed ==="

end Tests
end Metamath

def main : IO Unit :=
  Metamath.Tests.runCheckSinglePassParitySuite
