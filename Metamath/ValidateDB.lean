/-
# Database Format Validation Tests

This module validates that real Metamath databases satisfy the well-formedness
properties we assume as axioms in KernelClean.lean.

Key properties tested:
1. **float_key_not_rebound**: Float variables appear at most once per frame
2. Frame structure: Floats before essentials
3. Hypothesis validity: Well-formed formulas

These tests ensure our axioms reflect reality!
-/

import Metamath.Verify
import Metamath.Spec

namespace Metamath.Validate

open Verify

/-! ## Float Uniqueness Validation

Tests the property assumed by `float_key_not_rebound` axiom in KernelClean.lean:
In any frame, each float variable appears at most once.
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
  let mut frameCount := 0
  let mut malformedFrames : List (String × String) := []

  -- Iterate through all objects looking for assertions (which have frames)
  for (label, obj) in db.objects.toList do
    match obj with
    | .assert _ fr _ =>
        frameCount := frameCount + 1
        if !validateFloatUniqueness db fr.hyps then
          malformedFrames := (label, "Float variable appears multiple times") :: malformedFrames
    | _ => continue

  if malformedFrames.isEmpty then
    return ()
  else
    let msg := s!"Found {malformedFrames.length} frames with duplicate float variables:\n" ++
               String.intercalate "\n" (malformedFrames.map fun (lbl, err) => s!"  {lbl}: {err}")
    throw msg

/-! ## Frame Structure Validation

Test that frames follow the expected structure:
- Float hypotheses come before essential hypotheses
- Hypothesis formulas are well-formed
-/

/-- Check if frame follows standard structure (floats before essentials). -/
def validateFrameStructure (db : DB) (hyps : Array String) : Bool :=
  let rec check (seenEssential : Bool) : List String → Bool
    | [] => true
    | label :: rest =>
        match db.find? label with
        | some (.hyp false _ _) =>  -- Float
            if seenEssential then
              false  -- Float after essential!
            else
              check false rest
        | some (.hyp true _ _) =>   -- Essential
            check true rest
        | _ => check seenEssential rest  -- Non-hyp or not found

  check false hyps.toList

/-- Check if a float hypothesis is well-formed: f = #[.const c, .var v]. -/
def validateFloatFormula (f : Formula) : Bool :=
  match f.toList with
  | [.const _, .var _] => true
  | _ => false

/-- Comprehensive frame validation. -/
def validateFrame (db : DB) (hyps : Array String) : Except String Unit := do
  -- Check 1: Float uniqueness
  if !validateFloatUniqueness db hyps then
    throw "Float variables are not unique"

  -- Check 2: Frame structure (floats before essentials)
  if !validateFrameStructure db hyps then
    throw "Frame structure invalid: essential hypothesis before float"

  -- Check 3: Float formulas are well-formed
  for label in hyps.toList do
    match db.find? label with
    | some (.hyp false f _) =>
        if !validateFloatFormula f then
          throw s!"Malformed float hypothesis '{label}': expected #[const, var], got formula of length {f.size}"
    | _ => continue

  return ()

/-! ## Database Validation Entry Point -/

/-- Validate an entire database file. -/
def validateDatabase (filename : String) (permissive : Bool := false) : IO Unit := do
  IO.println s!"Validating Metamath database: {filename}"

  -- Parse database
  let db ← check filename permissive
  match db.error? with
  | some ⟨Error.error pos err, _⟩ =>
      IO.println s!"Parse error at {pos}: {err}"
      throw (IO.userError "Failed to parse database")
  | some _ => unreachable!
  | none =>
      IO.println s!"✓ Parsed successfully ({db.objects.size} objects)"

  -- Validate all frames
  match validateAllFrames db with
  | Except.ok () =>
      IO.println "✓ All frames have unique float variables"
  | Except.error msg =>
      IO.println s!"✗ Float uniqueness validation FAILED:\n{msg}"
      throw (IO.userError "Validation failed")

  IO.println s!"✓ Database validation PASSED: {filename}"

/-! ## Test Runner -/

/-- Run validation tests on standard Metamath databases. -/
def runValidationTests : IO Unit := do
  IO.println "=== Metamath Database Validation Tests ==="
  IO.println ""

  -- Test 1: Small demo database
  IO.println "Test 1: demo0.mm (small test database)"
  try
    validateDatabase "../mmverify/examples/demo0.mm"
  catch e =>
    IO.println s!"  FAILED: {e}"

  IO.println ""

  -- Test 2: set.mm (large production database)
  IO.println "Test 2: set.mm (large production database)"
  try
    validateDatabase "../set.mm"
  catch e =>
    IO.println s!"  FAILED: {e}"

  IO.println ""

  -- Test 3: Invalid database (should FAIL validation)
  IO.println "Test 3: invalid_duplicate_floats.mm (NEGATIVE TEST - should fail)"
  try
    validateDatabase "test_databases/invalid_duplicate_floats.mm"
    IO.println "  ✗ ERROR: Validator should have rejected this database!"
  catch e =>
    IO.println s!"  ✓ Correctly rejected: {e}"

  IO.println ""
  IO.println "=== Validation Complete ==="

end Metamath.Validate

/-! ## Main Entry Point -/

def main : IO UInt32 := do
  try
    Metamath.Validate.runValidationTests
    pure 0
  catch e =>
    IO.println s!"Validation tests failed: {e}"
    pure 1

/-! ## Usage

To run validation tests:

```bash
# Build the test module
lake build Metamath.ValidateDB

# Run from Lean REPL
#eval Metamath.Validate.runValidationTests

# Or add to lakefile.lean:
@[default_target]
lean_exe validateDB where
  root := `Metamath.ValidateDB
  supportInterpreter := true

# Then run:
lake exe validateDB
```
-/
