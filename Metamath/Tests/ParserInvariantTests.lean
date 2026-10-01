/-
# Parser Invariant Tests

Executable tests for parser operations and invariant maintenance.

Following CreuSAT's approach: verification should be testable.
These tests check that parser operations maintain observable properties
that correspond to our formal WellFormedDB invariants.
-/

import Metamath.Verify

namespace Metamath
namespace Tests

open Verify

/-! ## Test Helpers -/

/-- Create a minimal valid DB for testing -/
def mkTestDB : DB := {
  error? := none
  frame := { hyps := #[], dj := #[] }
  scopes := #[]
  objects := Std.HashMap.emptyWithCapacity 8
  interrupt := false
}

/-- Check if DB has no error -/
def dbOk (db : DB) : Bool :=
  db.error?.isNone

/-! ## InsertConst Tests -/

/-- Test: insertConst maintains no-error state -/
def test_insertConst_maintains_ok : IO Unit := do
  let db := mkTestDB
  let pos : Pos := ⟨1, 1⟩
  let db' := db.insert pos "c1" (fun _ => .const "c1")

  -- Observable property: error? = none is preserved
  if !dbOk db' then
    throw <| IO.userError "insertConst should maintain ok state"

  IO.println "✓ insertConst maintains ok state"

/-- Test: insertConst adds object to database -/
def test_insertConst_adds_object : IO Unit := do
  let db := mkTestDB
  let pos : Pos := ⟨1, 1⟩
  let db' := db.insert pos "c1" (fun _ => .const "c1")

  -- Observable property: object exists after insert
  match db'.find? "c1" with
  | some (.const _) => IO.println "✓ insertConst adds object"
  | _ => throw <| IO.userError "insertConst should add const object"

/-! ## InsertVar Tests -/

/-- Test: insertVar maintains label=name invariant -/
def test_insertVar_label_matches_name : IO Unit := do
  let db := mkTestDB
  let pos : Pos := ⟨1, 1⟩
  let label := "v1"
  let db' := db.insert pos label (fun lbl => .var lbl)

  -- Observable property: var name = label
  match db'.find? label with
  | some (.var v) =>
    if v = label then
      IO.println "✓ insertVar maintains label=name"
    else
      throw <| IO.userError s!"insertVar: expected var name={label}, got {v}"
  | _ => throw <| IO.userError "insertVar should add var object"

/-! ## InsertHyp Tests (Float) -/

/-- Test: insertHyp with float checks structure -/
def test_insertHyp_float_structure : IO Unit := do
  let db := mkTestDB
  -- First add const and var
  let db := db.insert ⟨1, 1⟩ "wff" (fun _ => .const "wff")
  let db := db.insert ⟨2, 1⟩ "x" (fun lbl => .var lbl)

  -- Add float: wff x
  let pos : Pos := ⟨3, 1⟩
  let arr : Formula := #[.const "wff", .var "x"]
  let db' := db.insertHyp pos "fx" false arr

  -- Observable property: float is added
  match db'.find? "fx" with
  | some (.hyp false f _) =>
    if dbOk db' ∧ f = arr then
      IO.println "✓ insertHyp float has correct structure"
    else
      throw <| IO.userError "float should have structure (const, var)"
  | _ => throw <| IO.userError "insertHyp should add float"

/-- Test: insertHyp detects duplicate float variables (would set error) -/
def test_insertHyp_float_duplicate_detection : IO Unit := do
  let db := mkTestDB
  let db := db.insert ⟨1, 1⟩ "wff" (fun _ => .const "wff")
  let db := db.insert ⟨2, 1⟩ "x" (fun lbl => .var lbl)

  -- Add first float
  let arr : Formula := #[.const "wff", .var "x"]
  let db := db.insertHyp ⟨3, 1⟩ "fx" false arr

  -- Try to add duplicate float (same variable)
  let db' := db.insertHyp ⟨4, 1⟩ "fx2" false arr

  if db'.parseErrorCode? != some .variableAlreadyHasFloatHyp then
    throw <| IO.userError
      s!"insertHyp: expected variableAlreadyHasFloatHyp, got {repr db'.parseErrorCode?}"
  IO.println "✓ insertHyp detects duplicate float variables"

/-! ## Frame Tests -/

/-- Test: withHyps adds to frame -/
def test_withHyps_extends_frame : IO Unit := do
  let db := mkTestDB
  let db' := db.withHyps (·.push "h1")

  -- Observable property: frame.hyps contains new label
  if db'.frame.hyps.size = 1 ∧ db'.frame.hyps[0]! = "h1" then
    IO.println "✓ withHyps extends frame"
  else
    throw <| IO.userError "withHyps should add label to frame"

/-! ## Integration Tests -/

/-- Test: Complete float declaration sequence -/
def test_float_declaration_sequence : IO Unit := do
  let mut db := mkTestDB

  -- Sequence: $c wff $. $v x $. $f wff x $.
  db := db.insert ⟨1, 1⟩ "wff" (fun _ => .const "wff")
  db := db.insert ⟨2, 1⟩ "x" (fun lbl => .var lbl)

  let arr : Formula := #[.const "wff", .var "x"]
  db := db.insertHyp ⟨3, 1⟩ "fx" false arr

  -- Check all parts succeeded
  if !dbOk db then
    throw <| IO.userError "float declaration sequence failed"
  if db.objects.size ≠ 3 then
    throw <| IO.userError s!"expected 3 objects, got {db.objects.size}"
  IO.println "✓ Float declaration sequence succeeds"

/-- A float may follow an essential hypothesis that does not use its variable.
The assertion frame and proof must retain the source hypothesis order. -/
def test_interleaved_hypotheses : IO Unit := do
  let text := "$c wff |- $. $v x y $. fx $f wff x $. " ++
    "${ ex $e |- x $. fy $f wff y $. ax $a |- y $. " ++
    "th $p |- y $= fx ex fy ax $. $}"
  let db := checkBytes text.toUTF8
  if !dbOk db || !db.incompleteProofs.isEmpty then
    throw <| IO.userError s!"interleaved hypotheses rejected: {repr db.parseErrorCode?}"
  match db.find? "th" with
  | some (.assert _ fr _) =>
    if fr.hyps != #["fx", "ex", "fy"] then
      throw <| IO.userError s!"interleaved hypothesis order changed: {repr fr.hyps}"
  | _ => throw <| IO.userError "interleaved proof did not store its theorem"
  IO.println "✓ legal interleaving preserves hypothesis and proof order"

/-- An essential hypothesis cannot use a variable before its float hypothesis. -/
def test_essential_before_its_float : IO Unit := do
  let text := "$c wff |- $. $v x y $. fx $f wff x $. " ++
    "${ ey $e |- y $. fy $f wff y $. ax $a |- y $. $}"
  let db := checkBytes text.toUTF8
  if db.parseErrorCode? != some .hypothesisSymbolsNotInFrame then
    throw <| IO.userError
      s!"late float: expected hypothesisSymbolsNotInFrame, got {repr db.parseErrorCode?}"
  IO.println "✓ an essential hypothesis requires its variables' floats first"

/-! ## Main Test Runner -/

def runAllTests : IO Unit := do
  IO.println "=== Parser Invariant Tests ==="
  IO.println ""

  IO.println "## Basic Operations"
  test_insertConst_maintains_ok
  test_insertConst_adds_object
  test_insertVar_label_matches_name
  IO.println ""

  IO.println "## Float Hypotheses"
  test_insertHyp_float_structure
  test_insertHyp_float_duplicate_detection
  IO.println ""

  IO.println "## Frame Operations"
  test_withHyps_extends_frame
  IO.println ""

  IO.println "## Integration"
  test_float_declaration_sequence
  test_interleaved_hypotheses
  test_essential_before_its_float
  IO.println ""

  IO.println "=== All tests passed! ==="

end Tests
end Metamath

/-- Main entry point for test executable -/
def main : IO Unit :=
  Metamath.Tests.runAllTests
