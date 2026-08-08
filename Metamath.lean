import Metamath.Spec
import Metamath.Verify
import Metamath.DBLemmas  -- Basic DB operation lemmas
import Metamath.KernelExtras
import Metamath.KernelClean  -- Soundness proofs
import Metamath.FrontendBridge  -- Front-end gate/spec bridge theorems
import Metamath.ParserInvariantsStep1
import Metamath.ParserSoundnessDemo  -- Parser soundness demonstration
-- import Metamath.KernelSkeleton  -- Archived (parse errors)
-- import Metamath.Kernel  -- Archived (185 errors)

open Metamath.Verify in
def main (args : List String) : IO UInt32 := do
  let showErrorCode := args.contains "--show-error-code" || args.contains "--error-code"
  let args := args.filter fun a => a != "--show-error-code" && a != "--error-code"

  -- Operational resource bound (see README, conformance boundary): the number
  -- of include-directive resolutions the driver loop may perform.
  let budgetOverride := args.findSome? fun a =>
    if "--max-include-resolutions=".isPrefixOf a then
      (a.drop "--max-include-resolutions=".length).toNat?
    else none
  let args := args.filter fun a => !"--max-include-resolutions=".isPrefixOf a

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
  | "--mode=sound" :: fname :: _ => (VerifierMode.soundDefault, fname)
  | fname :: "--mode=sound" :: _ => (VerifierMode.soundDefault, fname)
  | "--mode=zar" :: fname :: _ => (VerifierMode.zar, fname)
  | fname :: "--mode=zar" :: _ => (VerifierMode.zar, fname)
  | fname :: _ => (VerifierMode.zar, fname)
  | [] => (VerifierMode.zar, "set.mm")

  let config := match budgetOverride with
    | some n => { mode.toConfig with maxIncludeResolutions := n }
    | none => mode.toConfig
  let db ← check fname config
  match db.error? with
  | none =>
    -- [MM 4.1.4] a proof may contain `?`; the verifier accepts it but must
    -- warn that it is incomplete.  A database holding any incomplete proof is
    -- *accepted*, never *verified*, in every mode.
    if db.incompleteProofs.isEmpty then
      IO.println s!"verified, {db.objects.size} objects"
    else
      IO.println s!"accepted, {db.objects.size} objects, {db.incompleteProofs.size} incomplete proof(s): {String.intercalate " " db.incompleteProofs.toList}"
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
