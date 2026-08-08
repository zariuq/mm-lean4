/-
Declarative per-mode include semantics.

The Metamath specification (section 4.1.2) leaves two genuine freedoms to a
verifier, and every real verifier occupies a point in that freedom space:

* **File identity.**  "Only the first reference to a given file is included;
  any later references … cause the inclusion command to be ignored (treated
  like white space)."  The specification then licenses a coarse identity:
  "A verifier may assume that file names with different strings refer to
  different files for the purpose of ignoring later references."
  metamath.exe and metamath-knife take the license: identity is the include
  string exactly as written, so `x.mm` and `./x.mm` are two files.  The
  spec-faithful modes here canonicalize instead, so every spelling of one
  file is one file.

* **Path base.**  "It is currently unspecified if path references are
  relative to the process' current directory or the file's containing
  directory."  metamath.exe and metamath-knife resolve relative to the
  invocation directory; the spec-faithful modes here resolve relative to the
  including file.

Cycles are not a third freedom: "A file self-reference is ignored, as is any
reference to the top-level file (to avoid loops)."  Under literal identity
the string-keyed suppression realizes this silently for a same-spelling
reference, while a differently-spelled reference is (per the license) a
different file — it is re-included and the run fails naturally on the first
duplicate declaration.  Under canonical identity a cyclic reference is
recognized as a later reference and ignored; the spec-faithful modes add a
non-fatal warning because a cycle is almost always an authoring mistake.

Physical child-file finality is another implementation choice.  The
specification requires included files to contain complete statements.
`metamath-knife` enforces that boundary.  `metamath.exe` first scans each
physical file for includes and comments, then parses the concatenation: it
therefore rejects an unterminated child comment while allowing other parser
state to continue into the parent.

This module separates three kinds of evidence that must not be confused:

* policy records state the intended interpretation;
* selection theorems prove which policy a named `ModeConfig` chooses;
* runtime theorems below bind individual policy decisions to the functions
  the executable calls.

Agreement with an external executable is not a theorem of Lean and is never
claimed by an `rfl` equality here.  It is checked by the all-corpus
differential gate.
-/
import Metamath.Verify

namespace Metamath.Verify

/-- How a mode decides that two include references name the same file, for
the purpose of section 4.1.2's include-once suppression. -/
inductive FileIdentity where
  /-- The include string exactly as written.  This is metamath.exe's and
  metamath-knife's identity, licensed by the specification's "may assume that
  file names with different strings refer to different files". -/
  | literalString
  /-- Filesystem canonicalization (`realPath`): every spelling of one file is
  one file. -/
  | canonicalPath
  deriving DecidableEq, Repr

/-- The base against which an include string is resolved.  The specification
declares this "currently unspecified". -/
inductive PathBase where
  /-- The process' invocation directory — metamath.exe and metamath-knife. -/
  | invocationDir
  /-- The directory of the including file. -/
  | includerDir
  deriving DecidableEq, Repr

/-- What a mode does with a reference to a file whose first reference is
still being expanded. -/
inductive CyclePolicy where
  /-- The include-once suppression fires with no diagnostic — the reference
  implementations' behavior under literal identity. -/
  | ignoreSilently
  /-- Ignored per the specification ("treated like white space … to avoid
  loops"), with a non-fatal warning on standard error. -/
  | ignoreWithWarning
  /-- Hard error (`cycleDetected`).  Available to embedders via
  `ModeConfig.rejectIncludeCycles`; no shipped mode selects it. -/
  | reject
  deriving DecidableEq, Repr

/-- A mode's complete include interpretation. -/
structure IncludeInterpretation where
  identity : FileIdentity
  base : PathBase
  onCycle : CyclePolicy
  childBoundary : ChildFileBoundaryPolicy
  deriving DecidableEq, Repr

/-- Include behavior derived from the `metamath.exe` source and executable.
The record is a requirement for the `exe` mirror, not evidence that the mirror
satisfies it. -/
def metamathExeIncludePolicy : IncludeInterpretation :=
  { identity := .literalString
    base := .invocationDir
    onCycle := .ignoreSilently
    childBoundary := .spliceExceptComments }

/-- Include behavior derived from the `metamath-knife` source and executable.
Unlike `metamath.exe`, knife requires a strict child-file boundary. -/
def metamathKnifeIncludePolicy : IncludeInterpretation :=
  { identity := .literalString
    base := .invocationDir
    onCycle := .ignoreSilently
    childBoundary := .strict }

/-- Zar's interpretation of section 4.1.2: canonical file identity,
includer-relative lookup, cycles ignored with a warning, and complete child
files. -/
def zarIncludePolicy : IncludeInterpretation :=
  { identity := .canonicalPath
    base := .includerDir
    onCycle := .ignoreWithWarning
    childBoundary := .strict }

/-- The deliberately relaxed include policy used only by `permissive`. -/
def permissiveIncludePolicy : IncludeInterpretation :=
  { identity := .canonicalPath
    base := .includerDir
    onCycle := .ignoreWithWarning
    childBoundary := .spliceAll }

namespace ModeConfig

/-- The include interpretation a configuration realizes. -/
def includeInterpretation (c : ModeConfig) : IncludeInterpretation :=
  { identity := if c.literalIncludePaths then .literalString else .canonicalPath
    base := if c.literalIncludePaths then .invocationDir else .includerDir
    onCycle :=
      if c.rejectIncludeCycles then .reject
      else if c.literalIncludePaths then .ignoreSilently
      else .ignoreWithWarning
    childBoundary := c.childFileBoundary }

/-- Selection fact only: `exe` chooses the policy derived above.  External
agreement is established by the differential gate, not by this equality. -/
theorem exe_selects_metamathExeIncludePolicy :
    exe.includeInterpretation = metamathExeIncludePolicy := rfl

/-- Selection fact only: `knife` chooses the policy derived above. -/
theorem knife_selects_metamathKnifeIncludePolicy :
    knife.includeInterpretation = metamathKnifeIncludePolicy := rfl

/-- Selection fact: `zar` chooses Zar's declared section 4.1.2 policy. -/
theorem zar_selects_zarIncludePolicy :
    zar.includeInterpretation = zarIncludePolicy := rfl

/-- `soundDefault` changes proof completeness policy, not include policy. -/
theorem soundDefault_selects_zarIncludePolicy :
    soundDefault.includeInterpretation = zarIncludePolicy := rfl

/-- Selection fact: `permissive` deliberately permits all child splicing. -/
theorem permissive_selects_permissiveIncludePolicy :
    permissive.includeInterpretation = permissiveIncludePolicy := rfl

/-- Declarative compressed-proof policy.  It is separate from include policy
because the reference implementations disagree independently on this axis. -/
structure CompressedProofInterpretation where
  invalidBytes : CompressedInvalidBytePolicy
  deriving DecidableEq, Repr

/-- Knife's decoder silently ignores bytes outside `A`--`Z` and `?`; this is
visible in its source as the absence of a fallback branch. -/
def metamathKnifeCompressedProofPolicy : CompressedProofInterpretation :=
  { invalidBytes := .ignore }

/-- The specification, Zar, and metamath.exe reject such bytes. -/
def strictCompressedProofPolicy : CompressedProofInterpretation :=
  { invalidBytes := .reject }

def compressedProofInterpretation (c : ModeConfig) : CompressedProofInterpretation :=
  { invalidBytes := c.compressedInvalidBytes }

/-- Selection fact only; the decoder calls this configuration field directly. -/
theorem knife_selects_metamathKnifeCompressedProofPolicy :
    knife.compressedProofInterpretation = metamathKnifeCompressedProofPolicy := rfl

theorem exe_selects_strictCompressedProofPolicy :
    exe.compressedProofInterpretation = strictCompressedProofPolicy := rfl

theorem zar_selects_strictCompressedProofPolicy :
    zar.compressedProofInterpretation = strictCompressedProofPolicy := rfl

/-! ### Whole-mode acceptance policy

The records below put every semantic `ModeConfig` switch in one declarative
value.  Resource limits are intentionally absent: exhausting a depth or
resolution budget is an implementation outcome, not an interpretation of a
Metamath statement.  Consequently, “reference mirror” means agreement on this
acceptance policy for inputs that do not exhaust those explicit resources.

The reference requirement records were transcribed from the reference source
and executable probes.  The `*_selects_*` theorems only prove that our named
configuration selects the transcribed values.  The all-corpus differential is
the independent evidence that the resulting executable agrees with each
reference on the registered corpus. -/

/-- All statement-acceptance choices made by a verifier mode, excluding
implementation resource bounds. -/
structure AcceptanceInterpretation where
  rejectUnknownSteps : Bool
  rejectToplevelEss : Bool
  allowDuplicateFloat : Bool
  allowConstInnerScope : Bool
  allowIncludeInnerScope : Bool
  allowTokenSplicing : Bool
  includes : IncludeInterpretation
  compressedProofs : CompressedProofInterpretation
  deriving DecidableEq, Repr

/-- Project a runtime configuration onto its declarative acceptance policy. -/
def acceptanceInterpretation (c : ModeConfig) : AcceptanceInterpretation :=
  { rejectUnknownSteps := c.rejectUnknownSteps
    rejectToplevelEss := c.rejectToplevelEss
    allowDuplicateFloat := c.allowDuplicateFloat
    allowConstInnerScope := c.allowConstInnerScope
    allowIncludeInnerScope := c.allowIncludeInnerScope
    allowTokenSplicing := c.allowTokenSplicing
    includes := c.includeInterpretation
    compressedProofs := c.compressedProofInterpretation }

/-- Acceptance requirements derived for `metamath-knife`. -/
def metamathKnifeAcceptanceRequirement : AcceptanceInterpretation :=
  { rejectUnknownSteps := true
    rejectToplevelEss := true
    allowDuplicateFloat := false
    allowConstInnerScope := false
    allowIncludeInnerScope := false
    allowTokenSplicing := false
    includes := metamathKnifeIncludePolicy
    compressedProofs := metamathKnifeCompressedProofPolicy }

/-- Acceptance requirements derived for `metamath.exe`. -/
def metamathExeAcceptanceRequirement : AcceptanceInterpretation :=
  { rejectUnknownSteps := false
    rejectToplevelEss := false
    allowDuplicateFloat := true
    allowConstInnerScope := false
    allowIncludeInnerScope := true
    allowTokenSplicing := true
    includes := metamathExeIncludePolicy
    compressedProofs := strictCompressedProofPolicy }

/-- Zar's declared interpretation of the Metamath specification. -/
def zarAcceptancePolicy : AcceptanceInterpretation :=
  { rejectUnknownSteps := false
    rejectToplevelEss := false
    allowDuplicateFloat := false
    allowConstInnerScope := false
    allowIncludeInnerScope := false
    allowTokenSplicing := false
    includes := zarIncludePolicy
    compressedProofs := strictCompressedProofPolicy }

/-- The proof-certified default changes only unknown-proof acceptance. -/
def soundDefaultAcceptancePolicy : AcceptanceInterpretation :=
  { zarAcceptancePolicy with rejectUnknownSteps := true }

/-- Selection fact only: the `knife` preset selects the source-derived
requirement. -/
theorem knife_selects_metamathKnifeAcceptanceRequirement :
    knife.acceptanceInterpretation = metamathKnifeAcceptanceRequirement := rfl

/-- Selection fact only: the `exe` preset selects the source-derived
requirement. -/
theorem exe_selects_metamathExeAcceptanceRequirement :
    exe.acceptanceInterpretation = metamathExeAcceptanceRequirement := rfl

/-- Selection fact for Zar's specification interpretation. -/
theorem zar_selects_zarAcceptancePolicy :
    zar.acceptanceInterpretation = zarAcceptancePolicy := rfl

/-- Selection fact for the proof-certified default. -/
theorem soundDefault_selects_soundDefaultAcceptancePolicy :
    soundDefault.acceptanceInterpretation = soundDefaultAcceptancePolicy := rfl

end ModeConfig

/-! ### Binding path and identity declarations to executable helpers -/

@[simp] theorem includeLookupPath_literal (sourceFile includePath : String) :
    includeLookupPath true sourceFile includePath = System.FilePath.mk includePath := rfl

@[simp] theorem includeLookupPath_includer (sourceFile includePath : String) :
    includeLookupPath false sourceFile includePath =
      (System.FilePath.parent sourceFile |>.getD ".") / includePath := rfl

@[simp] theorem includeIdentityKey_literal (literal canonical : String) :
    includeIdentityKey true literal canonical = literal := rfl

@[simp] theorem includeIdentityKey_canonical (literal canonical : String) :
    includeIdentityKey false literal canonical = canonical := rfl

/-! ### Binding the declarations to the admission gate

`includeFrameGate` is the one decision point for include admission.  The
theorems below state the section 4.1.2 include-once discipline over the
identity key, for every interpretation, and pin the cycle policies: a
non-rejecting configuration never errors on an in-flight reference (it skips,
exactly the "treated like white space" clause), and the gate admits a fresh
key by registering it in both bookkeeping sets. -/

/-- Include-once, seen case: a key that was already fully included is
skipped. -/
theorem includeFrameGate_skips_seen (fname canonStr : String) (d : Nat)
    (rejectCycles : Bool) (processing seen : Std.HashSet String)
    (h_not_processing : processing.contains canonStr = false)
    (h_seen : seen.contains canonStr = true) :
    includeFrameGate fname canonStr (d + 1) rejectCycles processing seen
      = .ok .skipDuplicate := by
  simp [includeFrameGate, h_not_processing, h_seen]

/-- Include-once, cycle case: under a non-rejecting policy, a reference to a
key whose expansion is in flight is skipped, never an error — the
specification's "to avoid loops" clause. -/
theorem includeFrameGate_ignores_cycle (fname canonStr : String) (d : Nat)
    (processing seen : Std.HashSet String)
    (h_processing : processing.contains canonStr = true) :
    includeFrameGate fname canonStr (d + 1) false processing seen
      = .ok .skipCycle := by
  simp [includeFrameGate, h_processing]

/-- The embedder knob: a rejecting policy turns the in-flight case into the
diagnostic cycle error. -/
theorem includeFrameGate_rejects_cycle (fname canonStr : String) (d : Nat)
    (processing seen : Std.HashSet String)
    (h_processing : processing.contains canonStr = true) :
    includeFrameGate fname canonStr (d + 1) true processing seen
      = .error (.cycleDetected canonStr) := by
  simp [includeFrameGate, h_processing]

/-- First reference: a fresh key is admitted, and registered in both
bookkeeping sets so every later reference is suppressed. -/
theorem includeFrameGate_admits_fresh (fname canonStr : String) (d : Nat)
    (rejectCycles : Bool) (processing seen : Std.HashSet String)
    (h_not_processing : processing.contains canonStr = false)
    (h_not_seen : seen.contains canonStr = false) :
    includeFrameGate fname canonStr (d + 1) rejectCycles processing seen
      = .ok (.admit (d + 1) (processing.insert canonStr)
          (seen.insert canonStr)) := by
  simp [includeFrameGate, h_not_processing, h_not_seen]

/-- The depth backstop is an implementation resource bound, not part of any
include interpretation: it fires identically in every mode. -/
theorem includeFrameGate_depth_exhausted (fname canonStr : String)
    (rejectCycles : Bool) (processing seen : Std.HashSet String) :
    includeFrameGate fname canonStr 0 rejectCycles processing seen
      = .error (.depthExceeded fname) := rfl

end Metamath.Verify
