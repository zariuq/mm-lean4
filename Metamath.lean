import Metamath.Verify

open Metamath.Verify

/-- The options of one `mm-lean4` invocation. -/
structure CliOptions where
  mode : Option VerifierMode := none
  -- Operational resource bound (see README, conformance boundary): the number
  -- of include-directive resolutions the driver loop may perform.
  maxIncludeResolutions : Option Nat := none
  showErrorCode : Bool := false
  file : Option String := none

/-- The mode named by `--mode=<name>`. -/
def modeOfName? : String → Option VerifierMode
  | "zar" => some .zar
  | "sound" => some .sound
  | "knife" => some .knife
  | "exe" => some .exe
  | "permissive" => some .permissive
  | _ => none

/-- Record the mode that `arg` selects; a second, different mode is an error. -/
def CliOptions.setMode (o : CliOptions) (m : VerifierMode) (arg : String) :
    Except String CliOptions :=
  match o.mode with
  | none => .ok { o with mode := some m }
  | some m' => if m' = m then .ok o else .error s!"conflicting mode option {arg}"

/-- Read one argument. Each argument is an option or the database file. An unknown option, a
malformed value, a second file, or a second mode or budget that differs from the first is an
error, so a misspelt option never silently selects a different policy. -/
def CliOptions.add (o : CliOptions) (arg : String) : Except String CliOptions :=
  if arg == "--show-error-code" || arg == "--error-code" then
    .ok { o with showErrorCode := true }
  else if arg == "--permissive" then
    o.setMode .permissive arg
  else if let some name := arg.dropPrefix? "--mode=" then
    match modeOfName? name.copy with
    | some m => o.setMode m arg
    | none => .error s!"unknown mode in {arg} (expected zar, sound, knife, exe or permissive)"
  else if let some value := arg.dropPrefix? "--max-include-resolutions=" then
    let digits := value.copy
    match (if digits.all Char.isDigit then digits.toNat? else none), o.maxIncludeResolutions with
    | none, _ => .error s!"invalid number in {arg}"
    | some n, none => .ok { o with maxIncludeResolutions := some n }
    | some n, some k =>
      if k = n then .ok o else .error s!"conflicting include-resolution budget {arg}"
  else if arg.startsWith "-" then
    .error s!"unknown option {arg}"
  else
    match o.file with
    | none => .ok { o with file := some arg }
    | some f => .error s!"unexpected argument {arg}: the database file is already {f}"

def usage : String :=
  "usage: mm-lean4 [--mode=zar|sound|knife|exe|permissive] [--max-include-resolutions=N] " ++
    "[--show-error-code] [FILE]"

/-- Check the database (default `set.mm`) in the selected mode (default `zar`) and report the
result. -/
def run (o : CliOptions) : IO UInt32 := do
  let mode := o.mode.getD .zar
  let config := match o.maxIncludeResolutions with
    | some n => { mode.toConfig with maxIncludeResolutions := n }
    | none => mode.toConfig
  let db ← check (o.file.getD "set.mm") config
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
    if o.showErrorCode then
      match db.parseErrorCode? with
      | some code =>
          IO.println s!"at {pos}: [code #{ParseErrorCode.toNat code}] [clause {repr (ParseErrorCode.specClause code)}] [tag {repr code}] {err}"
      | none =>
          IO.println s!"at {pos}: [unclassified] {err}"
    else
      IO.println s!"at {pos}: {err}"
    pure 1
  | some _ => unreachable!

def main (args : List String) : IO UInt32 :=
  match args.foldlM CliOptions.add {} with
  | .ok o => run o
  | .error msg => do
    IO.eprintln s!"mm-lean4: {msg}"
    IO.eprintln usage
    pure 2
