import Metamath.Spec
import Metamath.Verify
import Metamath.DBLemmas  -- Basic DB operation lemmas
import Metamath.KernelExtras
import Metamath.KernelClean  -- Soundness proofs
import Metamath.ParserInvariantsStep1
-- import Metamath.ParserSoundnessDemo  -- Parser soundness demonstration (WIP)
-- import Metamath.KernelSkeleton  -- Archived (parse errors)
-- import Metamath.Kernel  -- Archived (185 errors)

open Metamath.Verify in
def main (args : List String) : IO UInt32 := do
  let showErrorCode := args.contains "--show-error-code" || args.contains "--error-code"
  let args := args.filter fun a => a != "--show-error-code" && a != "--error-code"

  -- Parse mode from args: --mode=zar|knife|exe|permissive or legacy --permissive
  -- The VerifierMode enum provides convenient CLI names that convert to ModeConfig
  let (mode, fname) := match args with
  | "--permissive" :: fname :: _ => (VerifierMode.permissive, fname)  -- Fully permissive
  | fname :: "--permissive" :: _ => (VerifierMode.permissive, fname)
  | "--mode=knife" :: fname :: _ => (VerifierMode.knife, fname)
  | fname :: "--mode=knife" :: _ => (VerifierMode.knife, fname)
  | "--mode=exe" :: fname :: _ => (VerifierMode.exe, fname)
  | fname :: "--mode=exe" :: _ => (VerifierMode.exe, fname)
  | "--mode=permissive" :: fname :: _ => (VerifierMode.permissive, fname)
  | fname :: "--mode=permissive" :: _ => (VerifierMode.permissive, fname)
  | "--mode=zar" :: fname :: _ => (VerifierMode.zar, fname)
  | fname :: "--mode=zar" :: _ => (VerifierMode.zar, fname)
  | fname :: _ => (VerifierMode.zar, fname)
  | [] => (VerifierMode.zar, "set.mm")

  let db ← check fname mode.toConfig
  match db.error? with
  | none =>
    IO.println s!"verified, {db.objects.size} objects"
    pure 0
  | some ⟨Error.error pos err, _⟩ =>
    if showErrorCode then
      match db.parseErrorCode? with
      | some code =>
          IO.println s!"at {pos}: [code #{ParseErrorCode.toNat code}] [clause {repr (ParseErrorCode.specClause code)}] [tag {repr code}] {err}"
      | none =>
          IO.println s!"at {pos}: [unclassified] {err}"
    else
      IO.println s!"at {pos}: {err}"
    pure 1
  | some _ => unreachable!
