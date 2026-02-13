import Metamath.Verify

namespace Metamath
namespace Tests

open Verify

private def assertContains (label : String) (text needle : String) : IO Unit := do
  if !(text.contains needle) then
    throw <| IO.userError s!"expected {label} to contain '{needle}', got:\n{text}"

/-- Regression test for `--show-error-code` CLI format. -/
def runCliErrorCodeFormatTest : IO Unit := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #[
      "exe", "mm-lean4", "--show-error-code",
      "test_databases/invalid_duplicate_floats.mm"
    ]
  }
  if out.exitCode != 1 then
    throw <| IO.userError s!"expected exit code 1, got {out.exitCode}\nstderr:\n{out.stderr}\nstdout:\n{out.stdout}"

  let expectedCode := s!"[code #{ParseErrorCode.toNat .variableAlreadyHasFloatHyp}]"
  let expectedClause := s!"[clause {repr (ParseErrorCode.specClause .variableAlreadyHasFloatHyp)}]"
  let expectedTag := s!"[tag {repr (ParseErrorCode.variableAlreadyHasFloatHyp)}]"

  assertContains "stdout" out.stdout expectedCode
  assertContains "stdout" out.stdout expectedClause
  assertContains "stdout" out.stdout expectedTag
  assertContains "stdout" out.stdout "already has $f hypothesis"

  if out.stdout.contains "[unclassified]" then
    throw <| IO.userError s!"expected classified output, got:\n{out.stdout}"

  IO.println "CLI --show-error-code format regression passed"

end Tests
end Metamath

def main : IO Unit :=
  Metamath.Tests.runCliErrorCodeFormatTest
