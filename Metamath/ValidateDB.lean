/-
# Database Format Validation Tests

This module checks float-variable uniqueness in stored assertion frames.
The default runner uses in-tree normal and compressed proof fixtures and
requires the duplicate-float fixture to fail with its specific parser error.
These runtime checks supplement, rather than replace, the correctness proofs.
-/

import Metamath.Verify

namespace Metamath.Validate

open Verify

/-! ## Float Uniqueness Validation

Check that each float variable appears at most once in an assertion frame.
-/

/-- Check if a single frame has unique float variables. -/
def validateFloatUniqueness (db : DB) (hyps : Array String) : Bool :=
  let floatVars := hyps.toList.filterMap fun label =>
    match db.find? label with
    | some (.hyp false f _) =>
        -- Extract variable from float hypothesis
        match f.toList with
        | [.const _, .var v] => some v
        | _ => none  -- Malformed float
    | _ => none

  -- Check for duplicates
  let rec hasDuplicates : List String → Bool
    | [] => false
    | x :: xs => xs.contains x || hasDuplicates xs

  !hasDuplicates floatVars

/-- Collect all frames from a database and validate float uniqueness. -/
def validateAllFrames (db : DB) : Except String Unit := do
  let mut malformedFrames : List (String × String) := []

  -- Iterate through all objects looking for assertions (which have frames)
  for (label, obj) in db.objects.toList do
    match obj with
    | .assert _ fr _ =>
        if !validateFloatUniqueness db fr.hyps then
          malformedFrames := (label, "Float variable appears multiple times") :: malformedFrames
    | _ => continue

  if malformedFrames.isEmpty then
    return ()
  else
    let msg := s!"Found {malformedFrames.length} frames with duplicate float variables:\n" ++
               String.intercalate "\n" (malformedFrames.map fun (lbl, err) => s!"  {lbl}: {err}")
    throw msg

/-! ## Database Validation Entry Point -/

/-- Validate an entire database file. -/
def validateDatabase (filename : String) (config : ModeConfig := {}) : IO Unit := do
  IO.println s!"Validating Metamath database: {filename}"

  -- Parse database
  let db ← check filename config
  match db.error? with
  | some ⟨Error.error pos err, _⟩ =>
      IO.println s!"Parse error at {pos}: {err}"
      throw (IO.userError "Failed to parse database")
  | some _ => unreachable!
  | none =>
      IO.println s!"✓ Parsed successfully ({db.objects.size} objects)"
      unless db.incompleteProofs.isEmpty do
        IO.println s!"⚠ {db.incompleteProofs.size} incomplete proof(s) accepted (not verified): {String.intercalate " " db.incompleteProofs.toList}"

  -- Validate all frames
  match validateAllFrames db with
  | Except.ok () =>
      IO.println "✓ All frames have unique float variables"
  | Except.error msg =>
      IO.println s!"✗ Float uniqueness validation FAILED:\n{msg}"
      throw (IO.userError "Validation failed")

  IO.println s!"✓ Database validation PASSED: {filename}"

/-! ## Test Runner -/

/-- Require the intended parser rejection; I/O and setup failures propagate. -/
def validateRejection (filename : String) (expected : ParseErrorCode) : IO Unit := do
  let db ← check filename
  if db.parseErrorCode? != some expected then
    throw <| IO.userError
      s!"{filename}: expected rejection {repr expected}, got {repr db.parseErrorCode?}"
  IO.println s!"✓ Correctly rejected {filename}: {repr expected}"

/-- Run the in-tree validation fixtures. Every failed expectation propagates. -/
def runValidationTests
    (positiveFiles : List String := [
      "test_databases/incomplete_proofs/complete.mm",
      "test_databases/compressed_phase/positive_nonmandatory_header_hyp.mm"])
    (negativeFile : String := "test_databases/invalid_duplicate_floats.mm") : IO Unit := do
  IO.println "=== Metamath Database Validation Tests ==="
  IO.println ""

  for filename in positiveFiles do
    validateDatabase filename
    IO.println ""

  validateRejection negativeFile .variableAlreadyHasFloatHyp

  IO.println ""
  IO.println "=== Validation Complete ==="

end Metamath.Validate

/-! ## Main Entry Point -/

def main (args : List String) : IO UInt32 := do
  try
    if args.isEmpty then
      Metamath.Validate.runValidationTests
    else
      for filename in args do
        Metamath.Validate.validateDatabase filename
    pure 0
  catch e =>
    IO.eprintln s!"Database validation failed: {e}"
    pure 1

/-! ## Usage

From the project root, run the in-tree validation fixtures or validate explicit files:

```bash
lake build validateDB
lake exe validateDB
lake exe validateDB /path/to/database.mm
```
-/
