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

/-- Rejected runs agree on rejection observables.  Their partial database
states need not agree: the two-pass checker rejects before parsing, whereas
the single-pass checker retains the prefix consumed before the exact error
site. -/
private def assertErrorShapeEq
    (label : String) (legacy single : DBShape) : IO Unit := do
  if legacy.hasError != single.hasError ||
      legacy.parseErrorCode != single.parseErrorCode ||
      legacy.evidenceCode != single.evidenceCode then
    throw <| IO.userError
      s!"{label}: rejection mismatch\nlegacy={repr legacy}\nsingle={repr single}"

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
  assertErrorShapeEq label (dbShape dbLegacy) (dbShape dbSingle)
  if dbLegacy.parseErrorCode? != some expected then
    throw <| IO.userError
      s!"{label}: legacy parseErrorCode mismatch, expected {repr expected}, got {repr dbLegacy.parseErrorCode?}"
  if dbSingle.parseErrorCode? != some expected then
    throw <| IO.userError
      s!"{label}: single-pass parseErrorCode mismatch, expected {repr expected}, got {repr dbSingle.parseErrorCode?}"
  IO.println s!"✓ {label}"

private def runParityCaseExpectAccept
    (label path : String) (config : ModeConfig := {}) : IO Unit := do
  let dbLegacy ← checkTwoPassLegacy path config
  let dbSingle ← checkSinglePass path config
  assertShapeEq label (dbShape dbLegacy) (dbShape dbSingle)
  if dbLegacy.error then
    throw <| IO.userError
      s!"{label}: legacy checker rejected unexpectedly with {repr dbLegacy.parseErrorCode?}"
  if dbSingle.error then
    throw <| IO.userError
      s!"{label}: single-pass checker rejected unexpectedly with {repr dbSingle.parseErrorCode?}"
  IO.println s!"✓ {label}"

/-- Regression: include-depth fuel overflow must decode to includeDepthExceeded.
Also checked for legacy/single-pass parity. -/
def runIncludeDepthOverflowRegression : IO Unit := do
  let path := "test_databases/include_depth/root_depth.mm"
  let cfg : ModeConfig := { maxIncludeDepth := 2 }
  let dbLegacy ← checkTwoPassLegacy path cfg
  let dbSingle ← checkSinglePass path cfg
  assertShapeEq "include-depth-overflow" (dbShape dbLegacy) (dbShape dbSingle)
  match dbSingle.parseErrorCode? with
  | some .includeDepthExceeded =>
      IO.println "✓ include-depth-overflow decodes as includeDepthExceeded"
  | code =>
      throw <| IO.userError
        s!"include-depth-overflow: expected includeDepthExceeded, got {repr code}"

/-- A parser-originated include placement error must retain the exact position
computed during the streaming pass.  Re-encoding it as a driver error would
collapse this position to the generic preprocessing location. -/
def runSinglePassIncludePositionRegression : IO Unit := do
  let path := "test_databases/include_splicing/djvars_accept_main.mm"
  let db ← checkSinglePass path VerifierMode.zar.toConfig
  match db.error? with
  | some ⟨.error pos _, _⟩ =>
      if pos.line != 2 || pos.col != 5 then
        throw <| IO.userError
          s!"single-pass include position: expected 2:5, got {pos}"
      IO.println "✓ single-pass include error preserves parser position"
  | _ =>
      throw <| IO.userError
        "single-pass include position: expected positioned parser error"

/-- Regression for files whose last byte belongs to a token.  Every file in
this in-memory include chain deliberately has no trailing whitespace; the
single-pass driver must flush each pending token before popping its frame, and
must still dispatch an include whose closing `$]` is the root or child EOF. -/
def runNoTrailingWhitespaceNestedIncludeRegression : IO Unit := do
  let config := VerifierMode.zar.toConfig
  let reads ← IO.mkRef 0
  let realPath : String → IO System.FilePath :=
    fun path => pure (System.FilePath.mk path)
  let readFile : String → IO ByteArray := fun path => do
    reads.modify (· + 1)
    if path.endsWith "root.mm" then
      return "$[ child.mm $]".toUTF8
    else if path.endsWith "child.mm" then
      return "$[ leaf.mm $]".toUTF8
    else if path.endsWith "leaf.mm" then
      return "$c wff $.".toUTF8
    else
      throw <| IO.userError s!"unexpected in-memory include path: {path}"
  let st0 : IncludeDriverState := {
    parser := singlePassInitialState config
    base := 0
    processing := Std.HashSet.emptyWithCapacity 4
    seen := Std.HashSet.emptyWithCapacity 4
    stack := []
  }
  let result ← processFileSinglePassWithIO
    realPath readFile "root.mm" config config.maxIncludeDepth st0
  let projected : Except IncludeError (ParserState × Nat × Std.HashSet String) :=
    match result with
    | .error err => .error err
    | .ok st => .ok (st.parser, st.base, st.seen)
  let db := finalizeSinglePassResult config projected
  if db.error then
    match db.error? with
    | some ⟨.error pos msg, idx⟩ =>
        throw <| IO.userError
          s!"no-trailing-whitespace nested include rejected at {pos} (index {idx}): {msg}"
    | some ⟨.includeRequest sourceFile includePath, idx⟩ =>
        throw <| IO.userError
          s!"unconsumed include request at index {idx}: {sourceFile} -> {includePath}"
    | some ⟨.ax .., _⟩ =>
        throw <| IO.userError "unexpected axiom interrupt"
    | some ⟨.thm .., _⟩ =>
        throw <| IO.userError "unexpected theorem interrupt"
    | none =>
        throw <| IO.userError "database reports an error without an interrupt"
  if db.objects.size != 1 then
    throw <| IO.userError
      s!"no-trailing-whitespace nested include: expected one object, got {db.objects.size}"
  let readCount ← reads.get
  if readCount != 3 then
    throw <| IO.userError
      s!"single-pass read count: expected exactly three files once each, got {readCount} reads"
  IO.println "✓ nested EOF includes remain single-pass and preserve the final tokens"

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
  runParityCaseExpectAccept
    "token_splicing_resumes_djvars"
    "test_databases/include_splicing/djvars_accept_main.mm"
    VerifierMode.exe.toConfig
  runParityCaseExpectCode
    "empty_token_splice_preserves_unclosed_djvars"
    "test_databases/include_splicing/djvars_empty_main.mm"
    .unclosedDjvars
    VerifierMode.exe.toConfig
  runParityCaseExpectCode
    "strict_mode_rejects_djvars_splice"
    "test_databases/include_splicing/djvars_accept_main.mm"
    .includeInsideStatement
    VerifierMode.zar.toConfig
  runParityCaseExpectAccept
    "token_splicing_resumes_normal_proof_start"
    "test_databases/include_splicing/normal_start_main.mm"
    VerifierMode.exe.toConfig
  runParityCaseExpectAccept
    "token_splicing_resumes_active_normal_proof"
    "test_databases/include_splicing/normal_active_main.mm"
    VerifierMode.exe.toConfig
  runParityCaseExpectAccept
    "token_splicing_resumes_compressed_proof"
    "test_databases/include_splicing/compressed_main.mm"
    VerifierMode.exe.toConfig
  runSinglePassIncludePositionRegression
  runNoTrailingWhitespaceNestedIncludeRegression
  runIncludeDepthOverflowRegression
  IO.println "=== parity suite passed ==="

end Tests
end Metamath

def main : IO Unit :=
  Metamath.Tests.runCheckSinglePassParitySuite
