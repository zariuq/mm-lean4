import Std.Data.HashMap
import Std.Data.HashSet
import Metamath.ByteSliceCompat
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false


/-! ## Array Bridging Lemmas

These lemmas bridge between dependent indexing `arr[i]'h` and panic-safe indexing `arr[i]!`.
They are needed for equation lemmas that compare unfolded definitions (which use dependent
indexing internally) with user-facing specifications (which use `!` notation).
-/


namespace Metamath.Verify

def uint8ToChar (n : UInt8) : Char :=
  ⟨n.toUInt32, .inl (Nat.lt_trans n.toBitVec.isLt (by decide))⟩

end Metamath.Verify

namespace UInt8

def isUpper (c : UInt8) : Bool :=
  c ≥ 65 && c ≤ 90

def isLower (c : UInt8) : Bool :=
  c ≥ 97 && c ≤ 122

def isAlpha (c : UInt8) : Bool :=
  c.isUpper || c.isLower

def isDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

def isAlphanum (c : UInt8) : Bool :=
  c.isAlpha || c.isDigit

end UInt8

-- ByteSlice and ByteSliceT now use Std.ByteSlice (Batteries 4.24.0+)
-- Import the compatibility layer that provides the old API
-- (Custom definitions removed; now using library types)

namespace Metamath
namespace Verify

open Std (HashMap HashSet)

/-- Treatment of bytes outside `A`--`Z` and `?` in the body of a compressed
proof.  The Metamath specification rejects them.  `metamath-knife` instead
silently skips them because its decoder has no fallback branch; the knife
mirror records that reference behavior explicitly. -/
inductive CompressedInvalidBytePolicy where
  | reject
  | ignore
  deriving DecidableEq, Repr, Inhabited

/-- Finality policy at the physical end of an included file.

`strict` requires the child to end between statements at its entry scope.
`spliceExceptComments` models `metamath.exe`: parser state may continue into
the parent, but the reference include scanner diagnoses an unterminated
comment before concatenation.  `spliceAll` is the fully permissive policy. -/
inductive ChildFileBoundaryPolicy where
  | strict
  | spliceExceptComments
  | spliceAll
  deriving DecidableEq, Repr, Inhabited

/-- Configuration flags for spec interpretation choices.
    Each flag represents an independent policy decision.

    DESIGN: Modes are just named presets. Users can create custom
    configurations by setting individual flags. This is more extensible
    than bundling behaviors into "permissive" - each check is orthogonal. -/
structure ModeConfig where
  -- Stricter checks (reject more)
  rejectUnknownSteps     : Bool := false  -- Reject ? in proofs
  rejectToplevelEss      : Bool := false  -- Reject $e at top level

  -- Permissive checks (accept more)
  allowDuplicateFloat    : Bool := false  -- Allow multiple $f for same var
  allowConstInnerScope   : Bool := false  -- Allow $c in inner blocks
  allowIncludeInnerScope : Bool := false  -- Allow $[ $] in inner blocks
  allowTokenSplicing     : Bool := false  -- Allow include to split tokens
  childFileBoundary      : ChildFileBoundaryPolicy := .strict
  compressedInvalidBytes : CompressedInvalidBytePolicy := .reject
  maxIncludeDepth        : Nat := 100     -- Include expansion recursion bound
  maxIncludeResolutions  : Nat := 1000000 -- Include directive resolution budget (driver-loop fuel)
  -- [MM 4.1.2] "A file self-reference is ignored, as is any reference to the
  -- top-level file (to avoid loops)".  Non-rejecting modes suppress the
  -- identity key selected below.  Literal modes may still re-read the same
  -- physical file under a different spelling, matching their references.
  rejectIncludeCycles    : Bool := false  -- Embedder knob: hard-error on cyclic includes (no shipped mode sets it)
  -- Reference-mirror include semantics: resolve the include string literally,
  -- relative to the invocation directory, and key duplicate suppression on
  -- the string as written.  This is exactly what metamath.exe and
  -- metamath-knife do (the specification's "may assume that file names with
  -- different strings refer to different files" license).  Spec-faithful
  -- modes instead canonicalize (realPath) and resolve relative to the
  -- including file.
  literalIncludePaths    : Bool := false
  deriving DecidableEq, Repr

instance : Inhabited ModeConfig := ⟨{}⟩

namespace ModeConfig

/-- Zar's Metamath-specification interpretation: strict source boundaries,
canonical include identity, and the book's acceptance of incomplete proofs. -/
def zar : ModeConfig := {}

/-- `metamath-knife` acceptance-policy mirror.  Knife rejects incomplete proofs
and top-level `$e`, ignores non-code bytes in compressed proof bodies, and uses
literal include strings relative to the invocation directory. -/
def knife : ModeConfig := {
  rejectUnknownSteps := true
  rejectToplevelEss := true
  compressedInvalidBytes := .ignore
  literalIncludePaths := true
}

/-- `metamath.exe` acceptance-policy mirror.  The reference permits duplicate
`$f`, includes inside scopes/statements, and statement state to cross physical
file boundaries, while its per-file scanner still rejects an unterminated
comment.  It rejects direct `$c` in an inner scope and keys includes literally
from the invocation directory. -/
def exe : ModeConfig := {
  allowDuplicateFloat := true
  allowIncludeInnerScope := true
  allowTokenSplicing := true
  childFileBoundary := .spliceExceptComments
  literalIncludePaths := true
}

/-- Maximally permissive profile: every *flag-governed* check relaxed.

Variable activity ([MM §4.2.2]) is deliberately not among the flags.  Activity
decides which databases are well-formed at all — an inactive variable in a `$d`
or a math string names something that is not in scope, so no profile may admit
it.  `Metamath.VariableActivity` proves the activity gate implements the book's
block rule; what the flags below relax are placement and duplication policies,
not scope. -/
def permissive : ModeConfig := {
  allowDuplicateFloat := true
  allowConstInnerScope := true
  allowIncludeInnerScope := true
  allowTokenSplicing := true
  childFileBoundary := .spliceAll
}

/-- Sound default: Zar mode + reject incomplete proofs.
    Minimal restriction needed for prefix-provenance (every accepted `$p` theorem
    is `Spec.Provable` in the pre-insertion database). -/
def soundDefault : ModeConfig := {
  rejectUnknownSteps := true
}

/-- A config is prefix-certified when it rejects `?` steps and does not allow
    duplicate `$f` hypotheses. These are the minimal conditions under which the
    prefix-provenance event-lift theorems hold (see `PrefixWitnessCheckBytes`). -/
def prefixCertified (c : ModeConfig) : Prop :=
  c.rejectUnknownSteps = true ∧ c.allowDuplicateFloat = false


end ModeConfig

/-- Legacy enum for CLI convenience -/
inductive VerifierMode where
  | zar
  | knife
  | exe
  | permissive
  | soundDefault
  deriving DecidableEq, Repr, Inhabited

namespace VerifierMode

def toConfig : VerifierMode → ModeConfig
  | .zar => ModeConfig.zar
  | .knife => ModeConfig.knife
  | .exe => ModeConfig.exe
  | .permissive => ModeConfig.permissive
  | .soundDefault => ModeConfig.soundDefault

end VerifierMode

def isLabelChar (c : UInt8) : Bool :=
  c.isAlphanum || c == '-'.toUInt8 || c == '_'.toUInt8 || c == '.'.toUInt8

def isWhitespace (c : UInt8) : Bool :=
  c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\r'.toUInt8 || c == '\t'.toUInt8 ||
  c == (0x0c : UInt8)

/-- Metamath spec whitespace set (§4.1.1): space, tab, CR, LF, form feed. -/
def isSpecWhitespace (c : UInt8) : Bool :=
  c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\r'.toUInt8 || c == '\t'.toUInt8 ||
  c == (0x0c : UInt8)



def isPrintable (c : UInt8) : Bool := c >= 32 && c <= 126

def isMathChar (c : UInt8) : Bool := c ≠ '$'.toUInt8 && isPrintable c

def toLabel (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push (Metamath.Verify.uint8ToChar c)
    unless isLabelChar c do ok := false
  (ok, s)

def toMath (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push (Metamath.Verify.uint8ToChar c)
    unless isMathChar c do ok := false
  (ok, s)

structure Pos where (line col : Nat)

instance : ToString Pos := ⟨fun ⟨l, c⟩ => s!"{l}:{c}"⟩

def DJ := String × String
instance : BEq DJ := instBEqProd

structure Frame where
  dj : Array DJ
  hyps : Array String
  deriving Inhabited

def Frame.size : Frame → Nat × Nat
  | ⟨dj, hyps⟩ => (dj.size, hyps.size)

def Frame.shrink : Frame → Nat × Nat → Frame
  | ⟨dj, hyps⟩, (x, y) => ⟨dj.shrink x, hyps.shrink y⟩

instance : ToString Frame := ⟨fun fr => toString fr.hyps⟩

instance : LawfulBEq String where
  eq_of_beq := by
    intro a b hab
    simp [BEq.beq] at hab
    exact hab
  rfl := by
    intro a
    simp [BEq.beq]

inductive Sym
  | const (c : String)
  | var (v : String)
  deriving Inhabited, DecidableEq, Repr

def Sym.isVar : Sym → Bool
  | .const _ => false
  | .var _ => true

def Sym.value : Sym → String
  | .const c => c
  | .var v => v

instance : BEq Sym := ⟨fun a b =>
  match a, b with
  | .const c1, .const c2 => c1 == c2
  | .var v1, .var v2 => v1 == v2
  | _, _ => false⟩

instance : LawfulBEq Sym where
  eq_of_beq := by
    intro a b h
    cases a with
    | const c =>
        cases b with
        | const c' =>
            have h_eq := h
            simp [BEq.beq] at h_eq
            subst h_eq
            rfl
        | var v =>
            have h' := h
            simp [BEq.beq] at h'
    | var v =>
        cases b with
        | const c =>
            have h' := h
            simp [BEq.beq] at h'
        | var v' =>
            have h_eq := h
            simp [BEq.beq] at h_eq
            subst h_eq
            rfl
  rfl := by
    intro a
    cases a <;> simp [BEq.beq, -beq_iff_eq]

abbrev Formula := Array Sym

def Formula.hasConstHead (f : Formula) : Bool :=
  if 0 < f.size then
    match f[0]! with
    | .const _ => true
    | .var _ => false
  else
    false

def Formula.isFloatShape (f : Formula) : Bool :=
  if f.size = 2 then
    match f[0]!, f[1]! with
    | .const _, .var _ => true
    | _, _ => false
  else
    false

def Formula.floatVarName (f : Formula) : String :=
  match f[1]! with
  | .var v => v
  | _ => ""

def Formula.floatVarsDistinct? (f g : Formula) : Bool :=
  if _ : f.size ≥ 2 then
    if _ : g.size ≥ 2 then
      !(f.floatVarName == g.floatVarName)
    else
      true
  else
    true

instance : ToString Formula where
  toString f := Id.run do
    let s := f[0]!.value
    f.foldl (init := s) (start := 1) fun (s:String) v =>
      s ++ " " ++ v.value

/-- One-step substitution action. -/
def Formula.substStep (σ : HashMap String Formula)
    (acc : Formula) (s : Sym) : Except String Formula :=
  match s with
  | .const _ => .ok (acc.push s)
  | .var v   =>
    match σ[v]? with
    | none   => .error s!"variable {v} not found"
    | some e => .ok (e.foldl Array.push acc 1)

/-- Substitution is foldlM of substStep over the array.
    This definition makes substitution reasoning straightforward. -/
def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula :=
  f.foldlM (Formula.substStep σ) #[]

def Formula.foldlVars (self : Formula) (init : α) (f : α → String → α) : α :=
  self.foldl (init := init) (start := 1) fun a v =>
    match v with
    | .var v => f a v
    | _ => a

def Formula.varsList (self : Formula) : List String :=
  self.toList.tail.filterMap fun s =>
    match s with
    | .var v => some v
    | _ => none

def Formula.varsIn (self : Formula) (vars : List String) : List String :=
  self.toList.tail.filterMap fun s =>
    let name := s.value
    if name ∈ vars then some name else none

inductive Object
  | const : String → Object
  | var : String → Object
  | hyp : Bool → Formula → String → Object
  | assert : Formula → Frame → String → Object

inductive ProofTokenParser
  | start
  | preload
  | normal
  | compressed (chr : Nat)

inductive HeapEl
  | fmla (f : Formula)
  | assert (f : Formula) (fr : Frame)

instance : ToString HeapEl where
  toString
  | .fmla f => toString f
  | .assert f fr => s!"{fr} |- {f}"

structure ProofState where
  pos : Pos
  label : String
  fmla : Formula
  frame : Frame
  heap : Array HeapEl
  stack : Array Formula
  ptp : ProofTokenParser
  /-- [MM §4.1.4] a `?` step was accepted in this proof.  The book permits
  `?`, allows the verifier to ignore such a proof, and requires warning that
  it is incomplete; this flag carries that fact to the database. -/
  incomplete : Bool := false

instance : ToString ProofState where
  toString p := Id.run do
    let mut s := s!"at {p.pos}: {p.label}\n"
    let mut i := 0
    for el in p.heap do
      s := s ++ s!"heap {i} := {el}\n"
      i := i + 1
    s := s ++ "\n"
    for el in p.stack do
      s := s ++ s!"{el}\n"
    s

/-- Structured payload for compressed-proof save errors. -/
inductive CompressedSaveError where
  | cantSaveEmptyStack (stackSize : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace ProofState

def push (pr : ProofState) (f : Formula) : ProofState :=
  { pr with stack := pr.stack.push f }

def pushHeap (pr : ProofState) (el : HeapEl) : ProofState :=
  { pr with heap := pr.heap.push el }

def save (pr : ProofState) : Except CompressedSaveError ProofState :=
  if let some f := pr.stack.back? then
    pure <| pr.pushHeap (.fmla f)
  else
    throw (.cantSaveEmptyStack pr.stack.size)

end ProofState

inductive Error
  | error (pos : Pos) (msg : String)
  | ax (pos : Pos) (l : String) (f : Formula) (fr : Frame)
  | thm (pos : Pos) (l : String) (f : Formula) (fr : Frame)
  | includeRequest (sourceFile : String) (includePath : String)

/-- Structured parser error codes for theorem-friendly diagnostics. -/
inductive ParseErrorCode
  | cantSaveEmptyStack
  | unclosedBlock
  | unclosedComment
  | unclosedConst
  | unclosedVar
  | unclosedDjvars
  | unclosedFloat
  | unclosedEss
  | unclosedAx
  | unclosedThm
  | notACommand
  | unclosedProof
  | cantPopGlobalScope
  | constMustBeOutermost
  | duplicateSymbolOrAssert
  | firstSymbolNotConstant
  | hypothesisSymbolsNotInFrame
  | expectedConstantAndVariable
  | variableAlreadyHasFloatHyp
  | stackFormulaNoConstantHead
  | hypothesisNoConstantHead
  | typeErrorInSubstitution
  | badTypecodeInSubstitution
  | duplicateFloatVariable
  | disjointVariableViolation
  | assertionNoConstantHead
  | assertionVarsNotInFrame
  | stackUnderflow
  | proofBackrefIndexOutOfRange
  | invalidLabel
  | invalidMathString
  | duplicateDisjointVariable
  | disjointStatementTooShort
  | variableAlreadyActive
  | constantStatementEmpty
  | variableStatementEmpty
  | tokenNotInScope
  | inactiveMathSymbol
  | tokenNotVariable
  | unknownStepQuestionRejected
  | topLevelEssentialNotAllowed
  | proofParseError
  | theoremMoreThanOneStackElement
  | theoremClaimMismatch
  | nestedCommentDelimiter
  | tokenNotConstantOrVariable
  | unknownStatementType
  | internalIllFormedDatabaseAfterParse
  | includeCycleDetected
  | includeDepthExceeded
  | includeBudgetExhausted
  | includeInInnerScope
  | includeInsideStatement
  | includeExtractedEmptyPath
  | includeEmptyPathBeforeNormalization
  | includePathEmptyAfterNormalization
  | includeReadFailure
  | hypothesisNotInDatabaseScope
  | statementNotFound
  | mandatoryHypothesisNotFoundInDatabase
  | hypothesisNotFound
  | outOfOrderHypothesesInFrame
  deriving DecidableEq, Repr, Inhabited
/-- Reviewer-facing alias: verifier diagnostics include parse and proof-check phases. -/
abbrev VerifyErrorCode := ParseErrorCode


/-- Metamath-spec clause anchors used by parser diagnostics. -/
inductive SpecClause
  | sec4_1_1_whitespace
  | sec4_1_2_comments
  | sec4_1_2_includes
  | sec4_1_3_basicSyntax
  | sec4_2_1_labels
  | sec4_2_2_constantsVariables
  | sec4_2_3_c_v_declarations
  | sec4_2_4_djvars
  | sec4_2_5_f_e_hypotheses
  | sec4_2_6_assertions
  | sec4_2_7_frames
  | sec4_2_8_scoping
  | sec4_3_proofVerification
  | sec4_3_substitution
  | sec4_3_stackDiscipline
  | sec4_3_labelResolution
  | sec4_4_5_compressedProof
  | sec4_4_6_unknownProof
  | impl_internalConsistency
  /-- Operational resource bound of this implementation (include depth /
  include-resolution budget), not a Metamath source-conformance clause: the
  spec imposes no such limits. -/
  | impl_resourceBound
  deriving DecidableEq, Repr, Inhabited

namespace ParseErrorCode

@[simp] def message : ParseErrorCode → String
  | .cantSaveEmptyStack => "can't save empty stack"
  | .unclosedBlock => "unclosed block (missing $})"
  | .unclosedComment => "unclosed comment"
  | .unclosedConst => "unclosed $c"
  | .unclosedVar => "unclosed $v"
  | .unclosedDjvars => "unclosed $d"
  | .unclosedFloat => "unclosed $f"
  | .unclosedEss => "unclosed $e"
  | .unclosedAx => "unclosed $a"
  | .unclosedThm => "unclosed $p"
  | .notACommand => "not a command"
  | .unclosedProof => "unclosed $p proof"
  | .cantPopGlobalScope => "can't pop global scope"
  | .constMustBeOutermost => "$c must be in outermost block (spec Section 4.2.8)"
  | .duplicateSymbolOrAssert => "duplicate symbol/assert '<label>'"
  | .firstSymbolNotConstant => "first symbol is not a constant"
  | .hypothesisSymbolsNotInFrame => "hypothesis symbols not in frame"
  | .expectedConstantAndVariable => "expected a constant and a variable"
  | .variableAlreadyHasFloatHyp => "variable '<v>' already has $f hypothesis"
  | .stackFormulaNoConstantHead => "stack formula has no constant head"
  | .hypothesisNoConstantHead => "hypothesis has no constant head"
  | .typeErrorInSubstitution => "type error in substitution"
  | .badTypecodeInSubstitution => "bad typecode in substitution '<ctx>'"
  | .duplicateFloatVariable => "duplicate float variable"
  | .disjointVariableViolation => "disjoint variable violation"
  | .assertionNoConstantHead => "assertion has no constant head"
  | .assertionVarsNotInFrame => "assertion variables not in frame"
  | .stackUnderflow => "stack underflow"
  | .proofBackrefIndexOutOfRange => "proof backref index out of range"
  | .invalidLabel => "invalid label '<label>'"
  | .invalidMathString => "invalid math string '<math>'"
  | .duplicateDisjointVariable => "duplicate disjoint variable '<sym>'"
  | .disjointStatementTooShort => "$d statement must contain at least two variables"
  | .variableAlreadyActive => "variable is already active in an enclosing block"
  | .constantStatementEmpty => "$c statement must declare at least one constant"
  | .variableStatementEmpty => "$v statement must declare at least one variable"
  | .tokenNotInScope => "symbol '<sym>' not in scope"
  | .inactiveMathSymbol => "symbol '<sym>' is not active here"
  | .tokenNotVariable => "symbol '<sym>' is not a variable"
  | .unknownStepQuestionRejected => "unknown step '?' not allowed (config rejects incomplete proofs)"
  | .topLevelEssentialNotAllowed => "top-level $e not allowed (config requires $e inside blocks)"
  | .proofParseError => "proof parse error"
  | .theoremMoreThanOneStackElement => "more than one element on stack"
  | .theoremClaimMismatch => "theorem does not prove what it claims"
  | .nestedCommentDelimiter => "nested comment delimiter '$(' inside comment"
  | .tokenNotConstantOrVariable => "symbol '<sym>' is not a constant or variable"
  | .unknownStatementType => "unknown statement type '<type>'"
  | .internalIllFormedDatabaseAfterParse => "internal error: ill-formed database after parse"
  | .includeCycleDetected => "include cycle detected: '<path>' is already being processed"
  | .includeDepthExceeded => "include depth limit exceeded (increase maxIncludeDepth in ModeConfig)"
  | .includeBudgetExhausted => "include resolution budget exhausted (increase maxIncludeResolutions in ModeConfig)"
  | .includeInInnerScope => "include in inner scope (config requires outermost scope only, spec §4.1.2)"
  | .includeInsideStatement => "include inside statement (config forbids token splicing, spec §4.1.2)"
  | .includeExtractedEmptyPath => "extracted empty path from position <start> to <end> in <file>"
  | .includeEmptyPathBeforeNormalization => "extracted empty include path before normalization in <file>"
  | .includePathEmptyAfterNormalization => "include path became empty after normalizing './' prefix (original was '<path>') in <file>"
  | .includeReadFailure => "failed to read include file '<name>' (resolved to '<path>'): <error>"
  | .hypothesisNotInDatabaseScope => "hypothesis '<label>' not in database scope"
  | .statementNotFound => "statement '<label>' not found"
  | .mandatoryHypothesisNotFoundInDatabase => "mandatory hypothesis '<label>' not found in database"
  | .hypothesisNotFound => "hypothesis '<label>' not found"
  | .outOfOrderHypothesesInFrame => "out of order hypotheses in frame"


/-- Stable numeric ID for each parse error code. -/
def toNat : ParseErrorCode → Nat
  | .cantSaveEmptyStack => 0
  | .unclosedBlock => 1
  | .unclosedComment => 2
  | .unclosedConst => 3
  | .unclosedVar => 4
  | .unclosedDjvars => 5
  | .unclosedFloat => 6
  | .unclosedEss => 7
  | .unclosedAx => 8
  | .unclosedThm => 9
  | .notACommand => 10
  | .unclosedProof => 11
  | .cantPopGlobalScope => 12
  | .constMustBeOutermost => 13
  | .duplicateSymbolOrAssert => 14
  | .firstSymbolNotConstant => 15
  | .hypothesisSymbolsNotInFrame => 16
  | .expectedConstantAndVariable => 17
  | .variableAlreadyHasFloatHyp => 18
  | .stackFormulaNoConstantHead => 19
  | .hypothesisNoConstantHead => 20
  | .typeErrorInSubstitution => 21
  | .badTypecodeInSubstitution => 22
  | .duplicateFloatVariable => 23
  | .disjointVariableViolation => 24
  | .assertionNoConstantHead => 25
  | .assertionVarsNotInFrame => 26
  | .stackUnderflow => 27
  | .proofBackrefIndexOutOfRange => 28
  | .invalidLabel => 29
  | .invalidMathString => 30
  | .duplicateDisjointVariable => 31
  | .disjointStatementTooShort => 56
  | .variableAlreadyActive => 59
  | .constantStatementEmpty => 57
  | .variableStatementEmpty => 58
  | .tokenNotInScope => 32
  | .inactiveMathSymbol => 60
  | .tokenNotVariable => 33
  | .unknownStepQuestionRejected => 34
  | .topLevelEssentialNotAllowed => 35
  | .proofParseError => 36
  | .theoremMoreThanOneStackElement => 37
  | .theoremClaimMismatch => 38
  | .nestedCommentDelimiter => 39
  | .tokenNotConstantOrVariable => 40
  | .unknownStatementType => 41
  | .internalIllFormedDatabaseAfterParse => 42
  | .includeCycleDetected => 43
  | .includeDepthExceeded => 55
  | .includeBudgetExhausted => 61
  | .includeInInnerScope => 44
  | .includeInsideStatement => 45
  | .includeExtractedEmptyPath => 46
  | .includeEmptyPathBeforeNormalization => 47
  | .includePathEmptyAfterNormalization => 48
  | .includeReadFailure => 49
  | .hypothesisNotInDatabaseScope => 50
  | .statementNotFound => 51
  | .mandatoryHypothesisNotFoundInDatabase => 52
  | .hypothesisNotFound => 53
  | .outOfOrderHypothesesInFrame => 54

/-- Decode a stable numeric ID into a parse error code. -/
def ofNat? : Nat → Option ParseErrorCode
  | 0 => some .cantSaveEmptyStack
  | 1 => some .unclosedBlock
  | 2 => some .unclosedComment
  | 3 => some .unclosedConst
  | 4 => some .unclosedVar
  | 5 => some .unclosedDjvars
  | 6 => some .unclosedFloat
  | 7 => some .unclosedEss
  | 8 => some .unclosedAx
  | 9 => some .unclosedThm
  | 10 => some .notACommand
  | 11 => some .unclosedProof
  | 12 => some .cantPopGlobalScope
  | 13 => some .constMustBeOutermost
  | 14 => some .duplicateSymbolOrAssert
  | 15 => some .firstSymbolNotConstant
  | 16 => some .hypothesisSymbolsNotInFrame
  | 17 => some .expectedConstantAndVariable
  | 18 => some .variableAlreadyHasFloatHyp
  | 19 => some .stackFormulaNoConstantHead
  | 20 => some .hypothesisNoConstantHead
  | 21 => some .typeErrorInSubstitution
  | 22 => some .badTypecodeInSubstitution
  | 23 => some .duplicateFloatVariable
  | 24 => some .disjointVariableViolation
  | 25 => some .assertionNoConstantHead
  | 26 => some .assertionVarsNotInFrame
  | 27 => some .stackUnderflow
  | 28 => some .proofBackrefIndexOutOfRange
  | 29 => some .invalidLabel
  | 30 => some .invalidMathString
  | 31 => some .duplicateDisjointVariable
  | 56 => some .disjointStatementTooShort
  | 57 => some .constantStatementEmpty
  | 59 => some .variableAlreadyActive
  | 58 => some .variableStatementEmpty
  | 60 => some .inactiveMathSymbol
  | 32 => some .tokenNotInScope
  | 33 => some .tokenNotVariable
  | 34 => some .unknownStepQuestionRejected
  | 35 => some .topLevelEssentialNotAllowed
  | 36 => some .proofParseError
  | 37 => some .theoremMoreThanOneStackElement
  | 38 => some .theoremClaimMismatch
  | 39 => some .nestedCommentDelimiter
  | 40 => some .tokenNotConstantOrVariable
  | 41 => some .unknownStatementType
  | 42 => some .internalIllFormedDatabaseAfterParse
  | 43 => some .includeCycleDetected
  | 55 => some .includeDepthExceeded
  | 61 => some .includeBudgetExhausted
  | 44 => some .includeInInnerScope
  | 45 => some .includeInsideStatement
  | 46 => some .includeExtractedEmptyPath
  | 47 => some .includeEmptyPathBeforeNormalization
  | 48 => some .includePathEmptyAfterNormalization
  | 49 => some .includeReadFailure
  | 50 => some .hypothesisNotInDatabaseScope
  | 51 => some .statementNotFound
  | 52 => some .mandatoryHypothesisNotFoundInDatabase
  | 53 => some .hypothesisNotFound
  | 54 => some .outOfOrderHypothesesInFrame
  | _ => none


/-- Primary Metamath-spec clause associated to each parser error code. -/
def specClause : ParseErrorCode → SpecClause
  | .cantSaveEmptyStack => .sec4_4_5_compressedProof
  | .unclosedBlock => .sec4_2_8_scoping
  | .unclosedComment => .sec4_1_2_comments
  | .unclosedConst => .sec4_2_3_c_v_declarations
  | .unclosedVar => .sec4_2_3_c_v_declarations
  | .unclosedDjvars => .sec4_2_4_djvars
  | .unclosedFloat => .sec4_2_5_f_e_hypotheses
  | .unclosedEss => .sec4_2_5_f_e_hypotheses
  | .unclosedAx => .sec4_2_6_assertions
  | .unclosedThm => .sec4_2_6_assertions
  | .notACommand => .sec4_1_3_basicSyntax
  | .unclosedProof => .sec4_3_proofVerification
  | .cantPopGlobalScope => .sec4_2_8_scoping
  | .constMustBeOutermost => .sec4_2_8_scoping
  | .duplicateSymbolOrAssert => .sec4_2_1_labels
  | .firstSymbolNotConstant => .sec4_2_5_f_e_hypotheses
  | .hypothesisSymbolsNotInFrame => .sec4_2_7_frames
  | .expectedConstantAndVariable => .sec4_2_5_f_e_hypotheses
  | .variableAlreadyHasFloatHyp => .sec4_2_5_f_e_hypotheses
  | .stackFormulaNoConstantHead => .sec4_3_proofVerification
  | .hypothesisNoConstantHead => .sec4_3_proofVerification
  | .typeErrorInSubstitution => .sec4_3_substitution
  | .badTypecodeInSubstitution => .sec4_3_substitution
  | .duplicateFloatVariable => .sec4_2_5_f_e_hypotheses
  | .disjointVariableViolation => .sec4_3_substitution
  | .assertionNoConstantHead => .sec4_3_proofVerification
  | .assertionVarsNotInFrame => .sec4_3_proofVerification
  | .stackUnderflow => .sec4_3_stackDiscipline
  | .proofBackrefIndexOutOfRange => .sec4_4_5_compressedProof
  | .invalidLabel => .sec4_2_1_labels
  | .invalidMathString => .sec4_1_1_whitespace
  | .duplicateDisjointVariable => .sec4_2_4_djvars
  | .disjointStatementTooShort => .sec4_2_4_djvars
  | .variableAlreadyActive => .sec4_2_2_constantsVariables
  | .constantStatementEmpty => .sec4_2_2_constantsVariables
  | .variableStatementEmpty => .sec4_2_2_constantsVariables
  | .tokenNotInScope => .sec4_2_4_djvars
  | .inactiveMathSymbol => .sec4_2_2_constantsVariables
  | .tokenNotVariable => .sec4_2_4_djvars
  | .unknownStepQuestionRejected => .sec4_4_6_unknownProof
  | .topLevelEssentialNotAllowed => .sec4_2_8_scoping
  | .proofParseError => .sec4_3_proofVerification
  | .theoremMoreThanOneStackElement => .sec4_3_stackDiscipline
  | .theoremClaimMismatch => .sec4_3_proofVerification
  | .nestedCommentDelimiter => .sec4_1_2_comments
  | .tokenNotConstantOrVariable => .sec4_2_2_constantsVariables
  | .unknownStatementType => .sec4_1_3_basicSyntax
  | .internalIllFormedDatabaseAfterParse => .impl_internalConsistency
  | .includeCycleDetected => .sec4_1_2_includes
  | .includeDepthExceeded => .impl_resourceBound
  | .includeBudgetExhausted => .impl_resourceBound
  | .includeInInnerScope => .sec4_1_2_includes
  | .includeInsideStatement => .sec4_1_2_includes
  | .includeExtractedEmptyPath => .sec4_1_2_includes
  | .includeEmptyPathBeforeNormalization => .sec4_1_2_includes
  | .includePathEmptyAfterNormalization => .sec4_1_2_includes
  | .includeReadFailure => .sec4_1_2_includes
  | .hypothesisNotInDatabaseScope => .sec4_3_labelResolution
  | .statementNotFound => .sec4_3_labelResolution
  | .mandatoryHypothesisNotFoundInDatabase => .sec4_3_labelResolution
  | .hypothesisNotFound => .sec4_3_labelResolution
  | .outOfOrderHypothesesInFrame => .sec4_2_7_frames

/-- Option-valued compatibility wrapper (kept for existing callsites/tests). -/
def specClause? (code : ParseErrorCode) : Option SpecClause :=
  some (specClause code)


end ParseErrorCode

/-- Typed done/EOF closure errors emitted by `ParserState.done`. -/
inductive DoneModeError where
  | unclosedBlock
  | unclosedComment
  | unclosedConst
  | unclosedVar
  | unclosedDjvars
  | unclosedFloat
  | unclosedEss
  | unclosedAx
  | unclosedThm
  | unclosedProof
  deriving DecidableEq, Repr, Inhabited

namespace DoneModeError

@[simp] def code : DoneModeError → ParseErrorCode
  | .unclosedBlock => .unclosedBlock
  | .unclosedComment => .unclosedComment
  | .unclosedConst => .unclosedConst
  | .unclosedVar => .unclosedVar
  | .unclosedDjvars => .unclosedDjvars
  | .unclosedFloat => .unclosedFloat
  | .unclosedEss => .unclosedEss
  | .unclosedAx => .unclosedAx
  | .unclosedThm => .unclosedThm
  | .unclosedProof => .unclosedProof

@[simp] def message : DoneModeError → String
  | .unclosedBlock => ParseErrorCode.message .unclosedBlock
  | .unclosedComment => ParseErrorCode.message .unclosedComment
  | .unclosedConst => ParseErrorCode.message .unclosedConst
  | .unclosedVar => ParseErrorCode.message .unclosedVar
  | .unclosedDjvars => ParseErrorCode.message .unclosedDjvars
  | .unclosedFloat => ParseErrorCode.message .unclosedFloat
  | .unclosedEss => ParseErrorCode.message .unclosedEss
  | .unclosedAx => ParseErrorCode.message .unclosedAx
  | .unclosedThm => ParseErrorCode.message .unclosedThm
  | .unclosedProof => ParseErrorCode.message .unclosedProof

end DoneModeError

/-- Structured payload for token/statement form errors. -/
inductive TokenFormError where
  | notACommand (label : String)
  | invalidLabel (label : String)
  | invalidMathString (tok : String)
  | unknownStatementType (tok : String)
  | nestedCommentDelimiter
  deriving DecidableEq, Repr, Inhabited

namespace TokenFormError

def code : TokenFormError → ParseErrorCode
  | .notACommand _ => .notACommand
  | .invalidLabel _ => .invalidLabel
  | .invalidMathString _ => .invalidMathString
  | .unknownStatementType _ => .unknownStatementType
  | .nestedCommentDelimiter => .nestedCommentDelimiter

def message : TokenFormError → String
  | .notACommand _ => "not a command"
  | .invalidLabel label => "invalid label '" ++ label ++ "'"
  | .invalidMathString tok => "invalid math string '" ++ tok ++ "'"
  | .unknownStatementType tok => "unknown statement type '" ++ tok ++ "'"
  | .nestedCommentDelimiter => "nested comment delimiter '$(' inside comment"

end TokenFormError

/-- Structured payload for scope/declaration errors. -/
inductive ScopeDeclError where
  | cantPopGlobalScope
  | constMustBeOutermost
  | duplicateSymbolOrAssert (label : String)
  | firstSymbolNotConstant
  | hypothesisSymbolsNotInFrame
  | outOfOrderHypothesesInFrame
  | expectedConstantAndVariable
  | variableAlreadyHasFloatHyp (v : String)
  | duplicateDisjointVariable (sym : String)
  | disjointStatementTooShort (actual : Nat)
  | variableAlreadyActive (name : String)
  | constantStatementEmpty
  | variableStatementEmpty
  | tokenNotInScope (sym : String)
  | inactiveMathSymbol (sym : String)
  | tokenNotVariable (sym : String)
  | tokenNotConstantOrVariable (sym : String)
  | topLevelEssentialNotAllowed
  deriving DecidableEq, Repr, Inhabited

namespace ScopeDeclError

def code : ScopeDeclError → ParseErrorCode
  | .cantPopGlobalScope => .cantPopGlobalScope
  | .constMustBeOutermost => .constMustBeOutermost
  | .duplicateSymbolOrAssert _ => .duplicateSymbolOrAssert
  | .firstSymbolNotConstant => .firstSymbolNotConstant
  | .hypothesisSymbolsNotInFrame => .hypothesisSymbolsNotInFrame
  | .outOfOrderHypothesesInFrame => .outOfOrderHypothesesInFrame
  | .expectedConstantAndVariable => .expectedConstantAndVariable
  | .variableAlreadyHasFloatHyp _ => .variableAlreadyHasFloatHyp
  | .duplicateDisjointVariable _ => .duplicateDisjointVariable
  | .disjointStatementTooShort _ => .disjointStatementTooShort
  | .variableAlreadyActive _ => .variableAlreadyActive
  | .constantStatementEmpty => .constantStatementEmpty
  | .variableStatementEmpty => .variableStatementEmpty
  | .tokenNotInScope _ => .tokenNotInScope
  | .inactiveMathSymbol _ => .inactiveMathSymbol
  | .tokenNotVariable _ => .tokenNotVariable
  | .tokenNotConstantOrVariable _ => .tokenNotConstantOrVariable
  | .topLevelEssentialNotAllowed => .topLevelEssentialNotAllowed

def message : ScopeDeclError → String
  | .cantPopGlobalScope => "can't pop global scope"
  | .constMustBeOutermost => "$c must be in outermost block (spec Section 4.2.8)"
  | .duplicateSymbolOrAssert label => "duplicate symbol/assert '" ++ label ++ "'"
  | .firstSymbolNotConstant => "first symbol is not a constant"
  | .hypothesisSymbolsNotInFrame => "hypothesis symbols not in frame"
  | .outOfOrderHypothesesInFrame => "out of order hypotheses in frame"
  | .expectedConstantAndVariable => "expected a constant and a variable"
  | .variableAlreadyHasFloatHyp v => "variable '" ++ v ++ "' already has $f hypothesis"
  | .duplicateDisjointVariable sym => "duplicate disjoint variable '" ++ sym ++ "'"
  | .disjointStatementTooShort actual =>
      "$d statement must contain at least two variables (found " ++
        toString actual ++ ")"
  | .variableAlreadyActive name =>
      "variable '" ++ name ++ "' is already active in an enclosing block"
  | .constantStatementEmpty =>
      "$c statement must declare at least one constant"
  | .variableStatementEmpty =>
      "$v statement must declare at least one variable"
  | .tokenNotInScope sym => "symbol '" ++ sym ++ "' not in scope"
  | .inactiveMathSymbol sym => "symbol '" ++ sym ++ "' is not active here"
  | .tokenNotVariable sym => "symbol '" ++ sym ++ "' is not a variable"
  | .tokenNotConstantOrVariable sym => "symbol '" ++ sym ++ "' is not a constant or variable"
  | .topLevelEssentialNotAllowed => "top-level $e not allowed (config requires $e inside blocks)"

end ScopeDeclError

/-- Structured payload for proof-checking errors. -/
inductive ProofCheckError where
  | stackFormulaNoConstantHead
  | hypothesisNoConstantHead
  | typeErrorInSubstitution
  | badTypecodeInSubstitution (ctx : String)
  | duplicateFloatVariable
  | disjointVariableViolation
  | assertionNoConstantHead
  | assertionVarsNotInFrame
  | stackUnderflow (needed : Nat) (haveSize : Nat)
  | proofBackrefIndexOutOfRange (index : Nat) (heapSize : Nat)
  | proofParseError
  | unknownStepQuestionRejected
  | hypothesisNotInDatabaseScope (label : String)
  | statementNotFound (label : String)
  | mandatoryHypothesisNotFoundInDatabase (label : String)
  | hypothesisNotFound (label : String)
  deriving DecidableEq, Repr, Inhabited

namespace ProofCheckError

def code : ProofCheckError → ParseErrorCode
  | .stackFormulaNoConstantHead => .stackFormulaNoConstantHead
  | .hypothesisNoConstantHead => .hypothesisNoConstantHead
  | .typeErrorInSubstitution => .typeErrorInSubstitution
  | .badTypecodeInSubstitution _ => .badTypecodeInSubstitution
  | .duplicateFloatVariable => .duplicateFloatVariable
  | .disjointVariableViolation => .disjointVariableViolation
  | .assertionNoConstantHead => .assertionNoConstantHead
  | .assertionVarsNotInFrame => .assertionVarsNotInFrame
  | .stackUnderflow _ _ => .stackUnderflow
  | .proofBackrefIndexOutOfRange _ _ => .proofBackrefIndexOutOfRange
  | .proofParseError => .proofParseError
  | .unknownStepQuestionRejected => .unknownStepQuestionRejected
  | .hypothesisNotInDatabaseScope _ => .hypothesisNotInDatabaseScope
  | .statementNotFound _ => .statementNotFound
  | .mandatoryHypothesisNotFoundInDatabase _ => .mandatoryHypothesisNotFoundInDatabase
  | .hypothesisNotFound _ => .hypothesisNotFound

def message : ProofCheckError → String
  | .stackFormulaNoConstantHead => "stack formula has no constant head"
  | .hypothesisNoConstantHead => "hypothesis has no constant head"
  | .typeErrorInSubstitution => "type error in substitution"
  | .badTypecodeInSubstitution ctx => "bad typecode in substitution '" ++ ctx ++ "'"
  | .duplicateFloatVariable => "duplicate float variable"
  | .disjointVariableViolation => "disjoint variable violation"
  | .assertionNoConstantHead => "assertion has no constant head"
  | .assertionVarsNotInFrame => "assertion variables not in frame"
  | .stackUnderflow _ _ => "stack underflow"
  | .proofBackrefIndexOutOfRange _ _ => "proof backref index out of range"
  | .proofParseError => "proof parse error"
  | .unknownStepQuestionRejected =>
      "unknown step '?' not allowed (config rejects incomplete proofs)"
  | .hypothesisNotInDatabaseScope label => "hypothesis '" ++ label ++ "' not in database scope"
  | .statementNotFound label => "statement '" ++ label ++ "' not found"
  | .mandatoryHypothesisNotFoundInDatabase label =>
      "mandatory hypothesis '" ++ label ++ "' not found in database"
  | .hypothesisNotFound label => "hypothesis '" ++ label ++ "' not found"

end ProofCheckError

/-- Structured payload for theorem-finality errors. -/
inductive TheoremFinalityError where
  | theoremMoreThanOneStackElement (stackSize : Nat)
  | theoremClaimMismatch (claim : Formula) (top : Formula)
  deriving DecidableEq, Repr, Inhabited

namespace TheoremFinalityError

def code : TheoremFinalityError → ParseErrorCode
  | .theoremMoreThanOneStackElement _ => .theoremMoreThanOneStackElement
  | .theoremClaimMismatch _ _ => .theoremClaimMismatch

def message : TheoremFinalityError → String
  | .theoremMoreThanOneStackElement _ => "more than one element on stack"
  | .theoremClaimMismatch _ _ => "theorem does not prove what it claims"

end TheoremFinalityError

namespace CompressedSaveError

def code : CompressedSaveError → ParseErrorCode
  | .cantSaveEmptyStack _ => .cantSaveEmptyStack

def message : CompressedSaveError → String
  | .cantSaveEmptyStack _ => "can't save empty stack"

end CompressedSaveError

/-- Structured payload for include errors. -/
inductive IncludeError where
  | cycleDetected (path : String)
  | depthExceeded (path : String)
  | budgetExhausted (path : String)
  | inInnerScope (pos : Nat) (scopeDepth : Nat) (inStatement : Bool) (allowIncludeInnerScopeWitness : Bool)
  | insideStatement (pos : Nat) (scopeDepth : Nat) (inStatement : Bool) (allowTokenSplicingWitness : Bool)
  | extractedEmptyPath (startPos endPos file : String)
  | emptyPathBeforeNormalization (file : String)
  | pathEmptyAfterNormalization (origPath file : String)
  | readFailure (name path err : String)
  deriving DecidableEq, Repr, Inhabited

namespace IncludeError

def code : IncludeError → ParseErrorCode
  | .cycleDetected _ => .includeCycleDetected
  | .depthExceeded _ => .includeDepthExceeded
  | .budgetExhausted _ => .includeBudgetExhausted
  | .inInnerScope _ _ _ _ => .includeInInnerScope
  | .insideStatement _ _ _ _ => .includeInsideStatement
  | .extractedEmptyPath _ _ _ => .includeExtractedEmptyPath
  | .emptyPathBeforeNormalization _ => .includeEmptyPathBeforeNormalization
  | .pathEmptyAfterNormalization _ _ => .includePathEmptyAfterNormalization
  | .readFailure _ _ _ => .includeReadFailure

def message : IncludeError → String
  | .cycleDetected path =>
      "include cycle detected: '" ++ path ++ "' is already being processed"
  | .depthExceeded path =>
      "include depth limit exceeded while processing '" ++ path ++ "' (increase ModeConfig.maxIncludeDepth)"
  | .budgetExhausted path =>
      "include resolution budget exhausted while processing '" ++ path ++ "' (increase ModeConfig.maxIncludeResolutions)"
  | .inInnerScope _ _ _ _ =>
      "include in inner scope (config requires outermost scope only, spec §4.1.2)"
  | .insideStatement _ _ _ _ =>
      "include inside statement (config forbids token splicing, spec §4.1.2)"
  | .extractedEmptyPath startPos endPos file =>
      "extracted empty path from position " ++ startPos ++ " to " ++ endPos ++ " in " ++ file
  | .emptyPathBeforeNormalization file =>
      "extracted empty include path before normalization in " ++ file
  | .pathEmptyAfterNormalization origPath file =>
      "include path became empty after normalizing './' prefix (original was '" ++
        origPath ++ "') in " ++ file
  | .readFailure name path err =>
      "failed to read include file '" ++ name ++ "' (resolved to '" ++ path ++ "'): " ++ err

end IncludeError

/-- Gate checks for include directives (spec §4.1.2 policy constraints). -/
def includeDirectiveViolation? (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool)
    (pos : Nat) : Option IncludeError :=
  if !config.allowIncludeInnerScope && scopeDepth > 0 then
    some (.inInnerScope pos scopeDepth inStatement config.allowIncludeInnerScope)
  else if !config.allowTokenSplicing && inStatement then
    some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)
  else
    none

structure Interrupt where
  e : Error
  idx : Nat

/-- Structured evidence for parser errors (used for semantic inversion). -/
inductive ErrorEvidence where
  | doneMode (err : DoneModeError)
  | tokenForm (err : TokenFormError)
  | scopeDecl (err : ScopeDeclError)
  | includeErr (err : IncludeError)
  | proofCheck (err : ProofCheckError)
  | theoremFinality (err : TheoremFinalityError)
  | compressedSave (err : CompressedSaveError)
  | internalGate (allowDup : Bool) (wellFormed : Bool) (assertDv : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace ErrorEvidence

def code : ErrorEvidence → ParseErrorCode
  | doneMode err => DoneModeError.code err
  | tokenForm err => TokenFormError.code err
  | scopeDecl err => ScopeDeclError.code err
  | .includeErr err => IncludeError.code err
  | proofCheck err => ProofCheckError.code err
  | theoremFinality err => TheoremFinalityError.code err
  | compressedSave err => CompressedSaveError.code err
  | internalGate _ _ _ => .internalIllFormedDatabaseAfterParse
def message : ErrorEvidence → String
  | doneMode err => DoneModeError.message err
  | tokenForm err => TokenFormError.message err
  | scopeDecl err => ScopeDeclError.message err
  | .includeErr err => IncludeError.message err
  | proofCheck err => ProofCheckError.message err
  | theoremFinality err => TheoremFinalityError.message err
  | compressedSave err => CompressedSaveError.message err
  | internalGate _ _ _ => ParseErrorCode.message .internalIllFormedDatabaseAfterParse

def allowed : ErrorEvidence → Prop
  | _ => True

end ErrorEvidence



/-- Unified failure type for proof-checking and related scope/stack errors. -/
inductive ProofCheckFail where
  | tokenForm (err : TokenFormError)
  | scopeDecl (err : ScopeDeclError)
  | proofCheck (err : ProofCheckError)
  | compressedSave (err : CompressedSaveError)
  deriving DecidableEq, Repr, Inhabited

namespace ProofCheckFail

def code : ProofCheckFail → ParseErrorCode
  | tokenForm err => TokenFormError.code err
  | scopeDecl err => ScopeDeclError.code err
  | proofCheck err => ProofCheckError.code err
  | compressedSave err => CompressedSaveError.code err

def message : ProofCheckFail → String
  | tokenForm err => TokenFormError.message err
  | scopeDecl err => ScopeDeclError.message err
  | proofCheck err => ProofCheckError.message err
  | compressedSave err => CompressedSaveError.message err

def evidence : ProofCheckFail → ErrorEvidence
  | tokenForm err => .tokenForm err
  | scopeDecl err => .scopeDecl err
  | proofCheck err => .proofCheck err
  | compressedSave err => .compressedSave err

end ProofCheckFail

structure DB where
  frame : Frame
  scopes : Array (Nat × Nat)
  /-- Active `$v` declarations, each tagged with the block depth at which it
  was declared ([MM §4.2.2]: a variable is active from its `$v` to the end of
  the enclosing block).  The tag makes the stack self-describing, so closing a
  block drops exactly its declarations without a parallel snapshot stack and
  without any separate `active` flag that could drift from the registry.
  `objects` remains the global name/kind registry; this is activity. -/
  activeVars : Array (String × Nat) := #[]
  objects : HashMap String Object
  interrupt : Bool
  error? : Option Interrupt
  errorEvidence? : Option ErrorEvidence := none
  config : ModeConfig := {}
  /-- Labels of accepted-but-incomplete (`?`-containing) proofs, in insertion
  order.  Nonempty means the database is *accepted*, not *verified*. -/
  incompleteProofs : Array String := #[]
  deriving Inhabited

namespace DB

@[inline] def error (s : DB) : Bool := s.error?.isSome


/-- Error constructor that records structured evidence alongside the message. -/
def mkErrorWithEvidence (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) : DB :=
  { s with error? := some ⟨.error pos msg, default⟩, errorEvidence? := some ev }

/-- Fallback message-only error constructor.
This keeps the message payload and assigns the internal fallback evidence tag so
all emitted errors remain evidence-carrying. -/
def mkError (s : DB) (pos : Pos) (msg : String) : DB :=
  s.mkErrorWithEvidence pos msg (.internalGate false false false)


/-- Error constructor that derives the message from evidence. -/
def mkErrorFromEvidence (s : DB) (pos : Pos) (ev : ErrorEvidence) : DB :=
  s.mkErrorWithEvidence pos (ErrorEvidence.message ev) ev

/-- Parser-specific done/EOF error constructor with stable code mapping. -/
def mkParseError (s : DB) (pos : Pos) (err : DoneModeError) : DB :=
  s.mkErrorFromEvidence pos (.doneMode err)


/-- Decode parser error code (when present) from the DB interrupt payload. -/
def parseErrorCode? (s : DB) : Option ParseErrorCode :=
  match s.error? with
  | some ⟨.error _ _, _⟩ =>
      match s.errorEvidence? with
      | some (.doneMode err) => some err.code
      | some ev => some ev.code
      | none => none
  | _ => none


/-- Declarative parser-level violation witness for a decoded parser error code. -/
def ParserSpecViolation (s : DB) (code : ParseErrorCode) : Prop :=
  ∃ pos msg idx ev,
    s.error? = some ⟨.error pos msg, idx⟩ ∧
    s.errorEvidence? = some ev ∧
    ev.code = code

/-- Parser-level witness lifted to a concrete Metamath-spec clause. -/
def ParserSpecClauseViolation (s : DB) (clause : SpecClause) : Prop :=
  ∃ code, s.parseErrorCode? = some code ∧ ParseErrorCode.specClause code = clause

/-- Concrete parser violations for token/statement form errors. -/
def TokenFormViolation (s : DB) (code : ParseErrorCode) : Prop :=
  ∃ err,
    s.errorEvidence? = some (.tokenForm err) ∧
    TokenFormError.code err = code

/-- Concrete parser violations for scope/declaration/symbol-activity errors. -/
def ScopeDeclViolation (s : DB) (code : ParseErrorCode) : Prop :=
  ∃ err,
    s.errorEvidence? = some (.scopeDecl err) ∧
    ScopeDeclError.code err = code

/-- Concrete parser violations for include directive semantics (non-IO). -/
def IncludeViolation (s : DB) (code : ParseErrorCode) : Prop :=
  ∃ err,
    s.errorEvidence? = some (.includeErr err) ∧
    IncludeError.code err = code

/-- Concrete parser violations for include IO failures. -/
def IncludeReadFailureViolation (s : DB) : Prop :=
  s.IncludeViolation .includeReadFailure

/-- Concrete parser violations for proof checking and substitution failures. -/
def ProofCheckViolation (s : DB) (code : ParseErrorCode) : Prop :=
  ∃ err,
    s.errorEvidence? = some (.proofCheck err) ∧
    ProofCheckError.code err = code

/-- Concrete parser violations for theorem end/finality errors. -/
def TheoremFinalityViolation (s : DB) (code : ParseErrorCode) : Prop :=
  ∃ err,
    s.errorEvidence? = some (.theoremFinality err) ∧
    TheoremFinalityError.code err = code

/-- Concrete parser violations for compressed-proof save errors. -/
def CompressedSaveViolation (s : DB) : Prop :=
  ∃ err,
    s.errorEvidence? = some (.compressedSave err) ∧
    CompressedSaveError.code err = .cantSaveEmptyStack

/-- Concrete parser violation for label syntax. -/
def InvalidLabelViolation (s : DB) : Prop :=
  s.TokenFormViolation .invalidLabel

/-- Concrete parser violation for duplicate `$d` symbols. -/
def DuplicateDisjointVariableViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .duplicateDisjointVariable

/-- Concrete parser violation for a `$d` statement with fewer than two
variables, as required by Metamath book Section 4.2.4. -/
def DisjointStatementTooShortViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .disjointStatementTooShort

/-- Concrete parser violation for redeclaring a variable that is still
active, forbidden by Metamath book Section 4.2.2. -/
def VariableAlreadyActiveViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .variableAlreadyActive

/-- Concrete parser violation for a `$c` statement declaring no constants,
as required by Metamath book Section 4.2.1 (`constant+`). -/
def ConstantStatementEmptyViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .constantStatementEmpty

/-- Concrete parser violation for a `$v` statement declaring no variables,
as required by Metamath book Section 4.2.2 (`variable+`). -/
def VariableStatementEmptyViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .variableStatementEmpty

/-- Concrete parser violation for out-of-scope `$d` symbol use ([MM §4.2.4]).
This is the `$d` fault only; the math-string counterpart is
`InactiveMathSymbolViolation`. -/
def TokenNotInScopeViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .tokenNotInScope

/-- Concrete parser violation for a declared-but-inactive variable occurring in
an ordinary math string (`$f`/`$e`/`$a`/`$p`), governed by [MM §4.2.2]. -/
def InactiveMathSymbolViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .inactiveMathSymbol

/-- Metamath book §4.1.1 predicate for label-token syntax violations. -/
def Sec4_2_1_LabelSyntaxViolation (s : DB) : Prop :=
  s.InvalidLabelViolation

/-- Metamath book §4.2.4 predicate for duplicate `$d` variable entries. -/
def Sec4_2_4_DjvarsDuplicateViolation (s : DB) : Prop :=
  s.DuplicateDisjointVariableViolation

/-- Metamath book §4.2.4 predicate for a `$d` statement with fewer than two variables. -/
def Sec4_2_4_DjvarsArityViolation (s : DB) : Prop :=
  s.DisjointStatementTooShortViolation

/-- Metamath book §4.2.4 predicate for `$d` variable scope violations. -/
def Sec4_2_4_DjvarsScopeViolation (s : DB) : Prop :=
  s.TokenNotInScopeViolation

/-- Payload witness for `.invalidLabel` carrying the concrete rejected token. -/
def InvalidLabelPayloadWitness (s : DB) : Prop :=
  ∃ label, s.errorEvidence? = some (.tokenForm (.invalidLabel label))

/-- Payload witness for `.topLevelEssentialNotAllowed` carrying strict-mode gate values. -/
def TopLevelEssentialPayloadWitness (s : DB) : Prop :=
  s.errorEvidence? = some (.scopeDecl (.topLevelEssentialNotAllowed))

/-- Payload witness for a degenerate `$d` statement, retaining the number of
variables seen before the terminator. -/
def DisjointStatementTooShortPayloadWitness (s : DB) : Prop :=
  ∃ actual,
    s.errorEvidence? = some (.scopeDecl (.disjointStatementTooShort actual))

/-- Payload witness for `.tokenNotInScope` carrying symbol + gate booleans. -/
def TokenNotInScopePayloadWitness (s : DB) : Prop :=
  ∃ sym,
    s.errorEvidence? = some (.scopeDecl (.tokenNotInScope sym))

/-- Payload witness for `.inactiveMathSymbol` carrying the offending symbol. -/
def InactiveMathSymbolPayloadWitness (s : DB) : Prop :=
  ∃ sym,
    s.errorEvidence? = some (.scopeDecl (.inactiveMathSymbol sym))

/-- Payload witness for `.tokenNotConstantOrVariable` carrying symbol + gate boolean. -/
def TokenNotConstantOrVariablePayloadWitness (s : DB) : Prop :=
  ∃ sym,
    s.errorEvidence? = some (.scopeDecl (.tokenNotConstantOrVariable sym))

/-- Payload witness for `.includeInInnerScope` carrying position + scope + in-statement. -/
def IncludeInInnerScopePayloadWitness (s : DB) : Prop :=
  ∃ pos depth inStatement allowIncludeInnerScopeWitness,
    s.errorEvidence? =
      some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness))

/-- Payload witness for `.includeInsideStatement` carrying position + scope + in-statement. -/
def IncludeInsideStatementPayloadWitness (s : DB) : Prop :=
  ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
    s.errorEvidence? =
      some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness))

/-- Code-indexed bundle for high-value parser-error shape evidence. -/
def HighValueShapeViolation (s : DB) (code : ParseErrorCode) : Prop :=
  match code with
  | .invalidLabel => s.InvalidLabelViolation
  | .duplicateDisjointVariable => s.DuplicateDisjointVariableViolation
  | .disjointStatementTooShort => s.DisjointStatementTooShortViolation
  | .tokenNotInScope => s.TokenNotInScopeViolation
  | .inactiveMathSymbol => s.InactiveMathSymbolViolation
  | _ => True

/-- All-code evidence witness carried by a concrete parser interrupt. -/
def AllCodePayloadShapeViolation (s : DB) (code : ParseErrorCode) : Prop :=
  ∃ pos msg idx ev,
    s.error? = some ⟨.error pos msg, idx⟩ ∧
    s.errorEvidence? = some ev ∧
    ev.code = code ∧
    ErrorEvidence.allowed ev

/-- All-code semantic witness carried by a concrete parser interrupt.
Currently identical to `AllCodePayloadShapeViolation`; kept as a stable API for future strengthening. -/
def AllCodeSemanticViolation (s : DB) (code : ParseErrorCode) : Prop :=
  s.AllCodePayloadShapeViolation code

/-- Clause-indexed all-code semantic violation predicate. -/
def AllCodeClauseSemanticViolation (s : DB) (clause : SpecClause) : Prop :=
  ∃ code, ParseErrorCode.specClause code = clause ∧ s.AllCodeSemanticViolation code

/-- Concrete parser violations emitted by `done`-mode closure checks at EOF. -/
def DoneModeViolation (s : DB) (code : ParseErrorCode) : Prop :=
  match code with
  | .unclosedBlock => s.AllCodeSemanticViolation code
  | .unclosedComment => s.AllCodeSemanticViolation code
  | .unclosedConst => s.AllCodeSemanticViolation code
  | .unclosedVar => s.AllCodeSemanticViolation code
  | .unclosedDjvars => s.AllCodeSemanticViolation code
  | .unclosedFloat => s.AllCodeSemanticViolation code
  | .unclosedEss => s.AllCodeSemanticViolation code
  | .unclosedAx => s.AllCodeSemanticViolation code
  | .unclosedThm => s.AllCodeSemanticViolation code
  | .unclosedProof => s.AllCodeSemanticViolation code
  | _ => False

/-- Concrete parser violation for internal consistency gate failures. -/
def InternalConsistencyViolation (s : DB) : Prop :=
  ∃ allowDup wf dv,
    s.errorEvidence? = some (.internalGate allowDup wf dv)

/-- Canonical per-code rule-semantic predicate.
This is the stable theorem-facing API for code-indexed parser semantics.
Specific constructors can be strengthened over time without changing callers. -/
def RuleSemanticViolation (s : DB) (code : ParseErrorCode) : Prop :=
  match code with
  | .invalidLabel => s.InvalidLabelViolation
  | .duplicateDisjointVariable => s.DuplicateDisjointVariableViolation
  | .disjointStatementTooShort => s.DisjointStatementTooShortViolation
  | .variableAlreadyActive => s.VariableAlreadyActiveViolation
  | .constantStatementEmpty => s.ConstantStatementEmptyViolation
  | .variableStatementEmpty => s.VariableStatementEmptyViolation
  | .tokenNotInScope => s.TokenNotInScopeViolation
  | .inactiveMathSymbol => s.InactiveMathSymbolViolation
  | .cantSaveEmptyStack => s.CompressedSaveViolation
  | .unclosedBlock => s.DoneModeViolation .unclosedBlock
  | .unclosedComment => s.DoneModeViolation .unclosedComment
  | .unclosedConst => s.DoneModeViolation .unclosedConst
  | .unclosedVar => s.DoneModeViolation .unclosedVar
  | .unclosedDjvars => s.DoneModeViolation .unclosedDjvars
  | .unclosedFloat => s.DoneModeViolation .unclosedFloat
  | .unclosedEss => s.DoneModeViolation .unclosedEss
  | .unclosedAx => s.DoneModeViolation .unclosedAx
  | .unclosedThm => s.DoneModeViolation .unclosedThm
  | .unclosedProof => s.DoneModeViolation .unclosedProof
  | .notACommand => s.TokenFormViolation .notACommand
  | .invalidMathString => s.TokenFormViolation .invalidMathString
  | .unknownStatementType => s.TokenFormViolation .unknownStatementType
  | .nestedCommentDelimiter => s.TokenFormViolation .nestedCommentDelimiter
  | .cantPopGlobalScope => s.ScopeDeclViolation .cantPopGlobalScope
  | .constMustBeOutermost => s.ScopeDeclViolation .constMustBeOutermost
  | .duplicateSymbolOrAssert => s.ScopeDeclViolation .duplicateSymbolOrAssert
  | .firstSymbolNotConstant => s.ScopeDeclViolation .firstSymbolNotConstant
  | .hypothesisSymbolsNotInFrame => s.ScopeDeclViolation .hypothesisSymbolsNotInFrame
  | .outOfOrderHypothesesInFrame => s.ScopeDeclViolation .outOfOrderHypothesesInFrame
  | .expectedConstantAndVariable => s.ScopeDeclViolation .expectedConstantAndVariable
  | .variableAlreadyHasFloatHyp => s.ScopeDeclViolation .variableAlreadyHasFloatHyp
  | .tokenNotVariable => s.ScopeDeclViolation .tokenNotVariable
  | .tokenNotConstantOrVariable => s.ScopeDeclViolation .tokenNotConstantOrVariable
  | .topLevelEssentialNotAllowed => s.ScopeDeclViolation .topLevelEssentialNotAllowed
  | .includeCycleDetected => s.IncludeViolation .includeCycleDetected
  | .includeDepthExceeded => s.IncludeViolation .includeDepthExceeded
  | .includeBudgetExhausted => s.IncludeViolation .includeBudgetExhausted
  | .includeInInnerScope => s.IncludeViolation .includeInInnerScope
  | .includeInsideStatement => s.IncludeViolation .includeInsideStatement
  | .includeExtractedEmptyPath => s.IncludeViolation .includeExtractedEmptyPath
  | .includeEmptyPathBeforeNormalization => s.IncludeViolation .includeEmptyPathBeforeNormalization
  | .includePathEmptyAfterNormalization => s.IncludeViolation .includePathEmptyAfterNormalization
  | .includeReadFailure => s.IncludeReadFailureViolation
  | .stackFormulaNoConstantHead => s.ProofCheckViolation .stackFormulaNoConstantHead
  | .hypothesisNoConstantHead => s.ProofCheckViolation .hypothesisNoConstantHead
  | .typeErrorInSubstitution => s.ProofCheckViolation .typeErrorInSubstitution
  | .badTypecodeInSubstitution => s.ProofCheckViolation .badTypecodeInSubstitution
  | .duplicateFloatVariable => s.ProofCheckViolation .duplicateFloatVariable
  | .disjointVariableViolation => s.ProofCheckViolation .disjointVariableViolation
  | .assertionNoConstantHead => s.ProofCheckViolation .assertionNoConstantHead
  | .assertionVarsNotInFrame => s.ProofCheckViolation .assertionVarsNotInFrame
  | .stackUnderflow => s.ProofCheckViolation .stackUnderflow
  | .proofBackrefIndexOutOfRange => s.ProofCheckViolation .proofBackrefIndexOutOfRange
  | .proofParseError => s.ProofCheckViolation .proofParseError
  | .unknownStepQuestionRejected => s.ProofCheckViolation .unknownStepQuestionRejected
  | .hypothesisNotInDatabaseScope => s.ProofCheckViolation .hypothesisNotInDatabaseScope
  | .statementNotFound => s.ProofCheckViolation .statementNotFound
  | .mandatoryHypothesisNotFoundInDatabase =>
      s.ProofCheckViolation .mandatoryHypothesisNotFoundInDatabase
  | .hypothesisNotFound => s.ProofCheckViolation .hypothesisNotFound
  | .theoremMoreThanOneStackElement => s.TheoremFinalityViolation .theoremMoreThanOneStackElement
  | .theoremClaimMismatch => s.TheoremFinalityViolation .theoremClaimMismatch
  | .internalIllFormedDatabaseAfterParse =>
      s.ScopeDeclViolation .internalIllFormedDatabaseAfterParse ∨
      s.IncludeViolation .internalIllFormedDatabaseAfterParse ∨
      s.InternalConsistencyViolation

/-- Rule semantic predicate paired with the code's mapped spec clause. -/
def RuleClauseSemanticViolation (s : DB) (code : ParseErrorCode) : Prop :=
  s.RuleSemanticViolation code ∧
    s.ParserSpecClauseViolation (ParseErrorCode.specClause code)

/-- Canonical parser semantic violation bundle:
decoded error-code witness + mapped spec-clause witness + rule-level predicate. -/
def ParserSemanticViolation (s : DB) (code : ParseErrorCode) : Prop :=
  s.ParserSpecViolation code ∧
    s.ParserSpecClauseViolation (ParseErrorCode.specClause code) ∧
      s.RuleSemanticViolation code


def pushScope (s : DB) : DB :=
  { s with scopes := s.scopes.push s.frame.size }


def popScope (pos : Pos) (db : DB) : DB :=
  if let some sc := db.scopes.back? then
    -- Closing the block at depth `db.scopes.size` deactivates exactly the
    -- `$v` declarations tagged with that depth or deeper.  Declarations are
    -- appended in non-decreasing depth, so those form a suffix; filtering by
    -- the surviving depth states the intent directly.
    let depth := db.scopes.size - 1
    { db with frame := db.frame.shrink sc, scopes := db.scopes.pop,
              activeVars := db.activeVars.filter (fun e => e.2 ≤ depth) }
  else
    db.mkErrorFromEvidence pos (.scopeDecl .cantPopGlobalScope)


/-- Record an accepted-but-incomplete proof's label ([MM §4.1.4] warning
surface).  Every other database component is untouched. -/
@[inline] def recordIncomplete (db : DB) (incomplete : Bool) (l : String) : DB :=
  if incomplete then { db with incompleteProofs := db.incompleteProofs.push l }
  else db

def find? (db : DB) (l : String) : Option Object := db.objects[l]?

/-- Lookups ignore the activity stack: `find?` reads only `objects`, so any
update confined to `activeVars` (and frame/scope bookkeeping) leaves every
symbol lookup fixed.  This keeps the scoping repair invisible to every
`find?`-based invariant. -/
@[simp] theorem find?_with_activeVars (db : DB) (fr : Frame)
    (sc : Array (Nat × Nat)) (av : Array (String × Nat)) (l : String) :
    ({ db with frame := fr, scopes := sc, activeVars := av } : DB).find? l =
      db.find? l := rfl


def isConst (db : DB) (tk : String) : Bool :=
  if let some (.const _) := db.find? tk then true else false

def isVar (db : DB) (tk : String) : Bool :=
  if let some (.var _) := db.find? tk then true else false

/-- [MM §4.2.2] Is `tk` an active variable, i.e. declared by a `$v` whose
enclosing block has not yet closed?  This is the predicate the book means by
"active variable"; `isVar` only says the name was ever declared as one. -/
def isActiveVar (db : DB) (tk : String) : Bool :=
  db.isVar tk && db.activeVars.any (fun e => e.1 == tk)

/-- [MM §4.2.2] Every surviving `$v` declaration was made at a depth that is
still open.  This is the content of "closing a block deactivates the variables
it declared": without it a depth tag could outlive its block, and activity would
part company with the book's rule.  `Metamath.VariableActivity` proves the
correspondence that this invariant underwrites. -/
def ActiveVarsBounded (db : DB) : Prop :=
  ∀ e ∈ db.activeVars.toList, e.2 ≤ db.scopes.size

/-- Every entry in the activity stack names a registered variable.  Pushes only
happen for a name that the same `insert` registers or that is already a `$v`, and
the registry never shrinks, so no entry can name an unregistered token. -/
def ActiveVarsSound (db : DB) : Prop :=
  ∀ e ∈ db.activeVars.toList, db.isVar e.1 = true

/-- No name appears twice in the activity stack.  A push happens only when the
name is not already active, so a second live entry for one variable cannot arise;
stating it keeps that gate from being weakened by accident. -/
def ActiveVarsNodup (db : DB) : Prop :=
  db.activeVars.toList.Pairwise (fun a b => a.1 ≠ b.1)

/-- Activity refines declaration *by construction*: the conjunct with `isVar`
makes "an active variable is a declared variable" definitional, so no DB-wide
invariant has to be carried to relate the two. -/
theorem isActiveVar_isVar {db : DB} {tk : String}
    (h : db.isActiveVar tk = true) : db.isVar tk = true := by
  simpa using (Bool.and_eq_true _ _ |>.mp h).1

def isSym (db : DB) (tk : String) : Bool :=
  match db.find? tk with
  | some (.const _) => true
  | some (.var _) => true
  | _ => false

/-- [MM §4.2.2] The math-symbol gate.  A symbol occurring in a math string must
be an *active* constant or an *active* variable.  Constants may only be declared
in the outermost block, so a declared constant is always active; variables are
block-scoped, so a declared variable must additionally still be active.

The two rejections are kept distinct because the book governs them by different
clauses: a name that was never declared is a §4.2.2 symbol error, while a name
whose `$v` block has been popped is an activity error at the same clause but a
different fault — and neither is the §4.2.4 `$d` fault. -/
def mathSymbolViolation? (db : DB) (tk : String) : Option ScopeDeclError :=
  match db.find? tk with
  | some (.const _) => none
  | some (.var _) =>
      if db.isActiveVar tk then none else some (.inactiveMathSymbol tk)
  | _ => some (.tokenNotConstantOrVariable tk)



/-- Scope gate for `$d` symbols: variable must exist and be active in current frame. -/
def djvarsScopeViolation? (db : DB) (tk : String) : Option ScopeDeclError :=
  if db.isActiveVar tk then
    none
  else if db.isVar tk then
    -- declared as a variable, but its `$v` block has been popped
    some (.tokenNotInScope tk)
  else
    some (.tokenNotVariable tk)


@[inline] def withFrame (f : Frame → Frame) (db : DB) : DB :=
  { db with frame := f db.frame }


@[inline] def withDJ (f : Array DJ → Array DJ) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨f dj, hyps⟩


@[inline] def withHyps (f : Array String → Array String) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨dj, f hyps⟩


def insert (db : DB) (pos : Pos) (l : String) (obj : String → Object) : DB :=
  -- Spec Section 4.2.8: $c must be in outermost block only
  -- Note: metamath.exe rejects direct $c in inner scope (test47b)
  let db := match obj l with
  | .const _ =>
    if !db.config.allowConstInnerScope && db.scopes.size > 0 then
      db.mkErrorFromEvidence pos (.scopeDecl .constMustBeOutermost)
    else db
  | _ => db
  if db.error then db else
  match obj l with
  | .var _ =>
      -- [MM §4.2.2] "A variable may not be declared a second time while it is
      -- active, but it may be declared again ... after it becomes inactive."
      -- The registry is consulted first: an unregistered name is fresh, so it
      -- cannot be active and needs no activity test.  Only a known name is
      -- gated on activity — which is exactly the book's condition, and keeps
      -- the fresh-insert lemmas free of any DB-wide invariant.
      match db.find? l with
      | none =>
          { db with objects := db.objects.insert l (obj l),
                    activeVars := db.activeVars.push (l, db.scopes.size) }
      | some (.var _) =>
          if db.isActiveVar l then
            db.mkErrorFromEvidence pos (.scopeDecl (.variableAlreadyActive l))
          else
            { db with activeVars := db.activeVars.push (l, db.scopes.size) }
      | some _ =>
          db.mkErrorFromEvidence pos (.scopeDecl (.duplicateSymbolOrAssert l))
  | _ =>
      if db.find? l |>.isSome then
        db.mkErrorFromEvidence pos (.scopeDecl (.duplicateSymbolOrAssert l))
      else
        { db with objects := db.objects.insert l (obj l) }



/-- Check whether a float variable already appears in the current frame. -/
def floatVarOccursInFrame (db : DB) (v : String) : Bool :=
  db.frame.hyps.toList.any fun lbl =>
    match db.find? lbl with
    | some (.hyp false prevF _) =>
        prevF.size >= 2 &&
          (match prevF[1]! with
          | .var v' => v'
          | _ => "") == v
    | _ => false


def hypOK? (db : DB) (label : String) : Bool :=
  match db.find? label with
  | some (.hyp ess f _) => if ess then f.hasConstHead else f.isFloatShape
  | _ => false

def frameHypsOk? (db : DB) (fr : Frame) : Bool :=
  (List.range fr.hyps.size).all fun i => db.hypOK? fr.hyps[i]!

def frameFloatVarsUnique? (db : DB) (fr : Frame) : Bool :=
  let idxs := List.range fr.hyps.size
  idxs.all fun i =>
    idxs.all fun j =>
      if _ : i = j then
        true
      else
        match db.find? fr.hyps[i]!, db.find? fr.hyps[j]! with
        | some (.hyp false fi _), some (.hyp false fj _) => Formula.floatVarsDistinct? fi fj
        | _, _ => true

def wellFormedFrame? (db : DB) (fr : Frame) : Bool :=
  db.frameHypsOk? fr && db.frameFloatVarsUnique? fr

def wellFormedObj? (db : DB) (lbl : String) (obj : Object) : Bool :=
  match obj with
  | .const _ => true
  | .var v => v == lbl
  | .hyp ess f _ => if ess then f.hasConstHead else f.isFloatShape
  | .assert f fr _ => f.hasConstHead && db.wellFormedFrame? fr

def wellFormedObjects? (db : DB) : Bool :=
  db.objects.toList.all fun kv => db.wellFormedObj? kv.1 kv.2

def wellFormed? (db : DB) : Bool :=
  db.wellFormedFrame? db.frame && db.wellFormedObjects?

/-- Extract float variable names from a frame (only well-formed $f hyps contribute). -/
def frameFloatVars (db : DB) (fr : Frame) : List String :=
  fr.hyps.toList.filterMap fun lbl =>
    match db.find? lbl with
    | some (.hyp false f _) =>
        if f.isFloatShape then
          match f[1]! with
          | .var v => some v
          | _ => none
        else
          none
    | _ => none

/-- For a frame attached to an assertion, every DV-pair variable must have an
    active floating hypothesis in that frame. -/
def frameDvVarsInFrame? (db : DB) (fr : Frame) : Bool :=
  let fvars := db.frameFloatVars fr
  fr.dj.toList.all fun p => decide (p.1 ∈ fvars ∧ p.2 ∈ fvars)

/-- Global parser post-check: every stored assertion frame satisfies
    `frameDvVarsInFrame?`. -/
def assertDvVarsInFrame? (db : DB) : Bool :=
  db.objects.toList.all fun kv =>
    match kv.2 with
    | .assert _ fr _ => db.frameDvVarsInFrame? fr
    | _ => true

/-- Check that formula symbols respect the frame's float variables.

For each tail symbol in the formula:
- variables must be declared by some $f in the frame
- constants must not be declared as frame variables
-/
def formulaSymsRespectFrame (db : DB) (f : Formula) (fr : Frame) : Bool :=
  let vars := frameFloatVars db fr
  (f.toList.tail).all fun s =>
    match s with
    | .var v => decide (v ∈ vars)
    | .const c => decide (c ∉ vars)

/-- `isVar` reads only `objects`, so it is blind to the activity stack.
(`isActiveVar` is precisely the predicate that is *not*.) -/
@[simp] theorem isVar_with_activeVars (db : DB) (fr0 : Frame)
    (sc : Array (Nat × Nat)) (av : Array (String × Nat)) (l : String) :
    ({ db with frame := fr0, scopes := sc, activeVars := av } : DB).isVar l =
      db.isVar l := rfl

/-- Symbol-respect reads only `objects`, so it too is blind to the activity
stack (companion to `find?_with_activeVars`). -/
@[simp] theorem formulaSymsRespectFrame_with_activeVars (db : DB) (fr0 : Frame)
    (sc : Array (Nat × Nat)) (av : Array (String × Nat))
    (f : Formula) (fr : Frame) :
    ({ db with frame := fr0, scopes := sc, activeVars := av } :
        DB).formulaSymsRespectFrame f fr =
      db.formulaSymsRespectFrame f fr := rfl

def insertHypChecks (db : DB) (pos : Pos) (ess : Bool) (f : Formula) : DB :=
  -- Validate basic formula shape (used by parser invariants)
  let db := if f.hasConstHead then db else
    db.mkErrorFromEvidence pos (.scopeDecl .firstSymbolNotConstant)
  if db.error then db else
  let db :=
    if ess then
      if formulaSymsRespectFrame db f (Frame.mk #[] db.frame.hyps) then db
      else
        db.mkErrorFromEvidence pos (.scopeDecl .hypothesisSymbolsNotInFrame)
    else if f.isFloatShape then db
    else
      db.mkErrorFromEvidence pos (.scopeDecl .expectedConstantAndVariable)
  if db.error then db else
  -- For $f statements (ess = false), check that no other $f exists for this variable
  -- Exe mode allows duplicate $f (test15, test16)
  if !ess && f.size >= 2 then
    let v := f[1]!.value
    if !db.config.allowDuplicateFloat && db.floatVarOccursInFrame v then
      db.mkErrorFromEvidence pos (.scopeDecl (.variableAlreadyHasFloatHyp v))
    else db
  else db


def insertHyp (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) : DB :=
  let db := db.insertHypChecks pos ess f
  if db.error then db else
  let db := db.insert pos l (.hyp ess f)
  if db.error then db else
    db.withHyps fun hyps => hyps.push l


def trimFrameKeep (db : DB) (vars : HashSet String) (l : String) : Bool :=
  match db.find? l with
  | some (.hyp false f _) =>
      let v := f[1]!.value
      vars.contains v
  | _ => true

def trimFrameHypsPairsList (db : DB) (vars : HashSet String) (i : Nat) (ls : List String) :
    List (Nat × String) :=
  ((List.zipIdx ls i).filter (fun p => trimFrameKeep db vars p.1)).map (fun p => (p.2, p.1))

def trimFrameHypsPairs (db : DB) (vars : HashSet String) (hyps : Array String) : Array (Nat × String) :=
  (trimFrameHypsPairsList db vars 0 hyps.toList).toArray

def trimFrameHyps (db : DB) (vars : HashSet String) (hyps : Array String) : Array String :=
  (trimFrameHypsPairs db vars hyps).map (fun p => p.2)

def trimFrame (db : DB) (fmla : Formula) (fr := db.frame) : Bool × Frame := Id.run do
  let collectVars (fmla : Formula) vars :=
    fmla.foldlVars vars HashSet.insert
  let mut vars : HashSet String := collectVars fmla ∅
  for l in fr.hyps do
    if let some (.hyp true f _) := db.find? l then
      vars := collectVars f vars
  let mut dj := #[]
  for v in fr.dj do
    if vars.contains v.1 && vars.contains v.2 then
      dj := dj.push v
  let hyps := trimFrameHyps db vars fr.hyps
  let mut ok := true
  let mut varsWithF : HashSet String := ∅
  for l in fr.hyps do
    if let some (.hyp false f _) := db.find? l then
      -- Spec §4.2.7: $f and $e can be interleaved (appearance order).
      -- We intentionally do not enforce "$f before $e".
      let v := f[1]!.value
      if vars.contains v then
        varsWithF := varsWithF.insert v
  -- Check that all variables have a $f hypothesis
  for v in vars do
    unless varsWithF.contains v do ok := false
  (ok, ⟨dj, hyps⟩)

def trimFrame' (db : DB) (fmla : Formula) : Except ScopeDeclError Frame :=
  let (ok, fr) := db.trimFrame fmla
  if ok then pure fr
  else throw .outOfOrderHypothesesInFrame

def insertAxiom (db : DB) (pos : Pos) (l : String) (fmla : Formula) : DB :=
  let db := if fmla.hasConstHead then db else
    db.mkErrorFromEvidence pos (.scopeDecl .firstSymbolNotConstant)
  if db.error then db
  else
    match db.trimFrame' fmla with
    | .ok fr =>
      if db.interrupt then { db with error? := some ⟨.ax pos l fmla fr, default⟩ }
      else db.insert pos l (.assert fmla fr)
    | .error err =>
      db.mkErrorFromEvidence pos (.scopeDecl err)


def mkProofState (_db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    ProofState := Id.run do
  ⟨pos, l, fmla, fr, #[], #[], .start, false⟩

def preload (db : DB) (pr : ProofState) (l : String) : Except ProofCheckFail ProofState :=
  match db.find? l with
  | some (.hyp _ f _) =>
      -- Check db.frame (all active hypotheses in scope), NOT pr.frame (trimmed mandatory)
      if l ∈ db.frame.hyps.toList then
        return pr.pushHeap (.fmla f)
      else
        throw (.proofCheck (.hypothesisNotInDatabaseScope l))
  | some (.assert f fr _) => return pr.pushHeap (.assert f fr)
  | _ => throw (.proofCheck (.statementNotFound l))

/-- Pre-populate heap with mandatory hypotheses for compressed proof format.
    Per spec Appendix B: "the order of the mandatory hypotheses of the statement
    being proved must not be changed if the compressed proof format is used"
    Test: metamath-test/tests/unit/test33_compressed_proof_stack_underflow.mm -/
def preloadMandatoryHyps (db : DB) (pr : ProofState) : Except ProofCheckFail ProofState := do
  let mut pr := pr
  for lbl in pr.frame.hyps do
    match db.find? lbl with
    | some (.hyp _ f _) => pr := pr.pushHeap (.fmla f)
    | _ => throw (.proofCheck (.mandatoryHypothesisNotFoundInDatabase lbl))
  return pr

variable (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) in
def checkHyp (i : Nat) (subst : HashMap String Formula) :
    Except ProofCheckFail (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(
      let thm {a b n} : i < a → n + a = b → n + i < b
      | h, rfl => Nat.add_lt_add_left h _
      thm h off.2)
    if !val.hasConstHead then
      .error (.proofCheck .stackFormulaNoConstantHead)
    else if let some (.hyp ess f _) := db.find? hyps[i] then
      if ess then
        if !f.hasConstHead then
          .error (.proofCheck .hypothesisNoConstantHead)
        else if !formulaSymsRespectFrame db f (Frame.mk #[] hyps) then
          .error (.scopeDecl .hypothesisSymbolsNotInFrame)
        else if f[0]! == val[0]! then
          match f.subst subst with
          | .ok s =>
              if s == val then
                checkHyp (i+1) subst
              else
                .error (.proofCheck .typeErrorInSubstitution)
          | .error _ =>
              .error (.proofCheck .typeErrorInSubstitution)
        else .error (.proofCheck (.badTypecodeInSubstitution s!"{hyps[i]}: {f} / {val}"))
      else
        if !f.isFloatShape then
          .error (.scopeDecl .expectedConstantAndVariable)
        else if f[0]! == val[0]! then
          if subst.contains f[1]!.value then
            .error (.proofCheck .duplicateFloatVariable)
          else
            checkHyp (i+1) (subst.insert f[1]!.value val)
        else .error (.proofCheck (.badTypecodeInSubstitution s!"{hyps[i]}: {f} / {val}"))
    else
      .error (.proofCheck (.hypothesisNotFound hyps[i]))
  else pure subst


def dvCheckBool (vars : List String) (djTarget djSource : Array (String × String))
    (subst : HashMap String Formula) : Bool :=
  let djList := djTarget.toList
  let disj s1 s2 := s1 != s2 &&
    decide ((if s1 < s2 then (s1, s2) else (s2, s1)) ∈ djList)
  djSource.toList.all (fun (v1, v2) =>
    match subst[v1]?, subst[v2]? with
    | some e1, some e2 =>
        let vars1 := e1.varsIn vars
        let vars2 := e2.varsIn vars
        vars1.all (fun s1 => vars2.all (fun s2 => disj s1 s2))
    | _, _ => false)

def dvCheck (vars : List String) (djTarget djSource : Array (String × String))
    (subst : HashMap String Formula) : Except ProofCheckFail Unit :=
  if dvCheckBool vars djTarget djSource subst then
    Except.ok ()
  else
    Except.error (.proofCheck .disjointVariableViolation)

def stepAssert (db : DB) (pr : ProofState) (f : Formula) : Frame → Except ProofCheckFail ProofState
  | fr@⟨dj, hyps⟩ => do
    if h : hyps.size ≤ pr.stack.size then
      if !f.hasConstHead then
        throw (.proofCheck .assertionNoConstantHead)
      else if !formulaSymsRespectFrame db f fr then
        throw (.proofCheck .assertionVarsNotInFrame)
      else
        let off : {off // off + hyps.size = pr.stack.size} :=
          ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h⟩
        let subst ← checkHyp db hyps pr.stack off 0 ∅
        let vars := frameFloatVars db db.frame
        dvCheck vars db.frame.dj dj subst
        let concl ←
          match f.subst subst with
          | .ok concl => Except.ok concl
          | .error _ => Except.error (.proofCheck .typeErrorInSubstitution)
        pure { pr with stack := (pr.stack.shrink off).push concl }
    else throw (.proofCheck (.stackUnderflow hyps.size pr.stack.size))

def stepNormal (db : DB) (pr : ProofState) (l : String) : Except ProofCheckFail ProofState :=
  match db.find? l with
  | some (.hyp ess f _) =>
      -- Check db.frame (all active hypotheses in scope), NOT pr.frame (trimmed mandatory)
      if l ∈ db.frame.hyps.toList then
        if ess then
          if !f.hasConstHead then
            throw (.proofCheck .hypothesisNoConstantHead)
          else
            return pr.push f
        else
          if !f.isFloatShape then
            throw (.scopeDecl .expectedConstantAndVariable)
          else
            return pr.push f
      else
        throw (.proofCheck (.hypothesisNotInDatabaseScope l))
  | some (.assert f fr _) => db.stepAssert pr f fr
  | _ => throw (.proofCheck (.statementNotFound l))

def stepProof (db : DB) (pr : ProofState) (i : Nat) : Except ProofCheckFail ProofState :=
  match pr.heap[i]? with
  | none => throw (.proofCheck (.proofBackrefIndexOutOfRange i pr.heap.size))
  | some (.fmla f) => return pr.push f
  | some (.assert f fr) => db.stepAssert pr f fr

end DB





inductive CharParser
  | ws : CharParser
  | token : Nat → ByteSliceT → CharParser
  deriving Inhabited

inductive TokensKind
  | float
  | ess
  | ax
  | thm

instance : ToString TokensKind where
  toString
  | .float => "float"
  | .ess => "ess"
  | .ax => "ax"
  | .thm => "thm"

def TokensKind.delim : TokensKind → ByteArray
  | .thm => "$=".toAscii
  | _ => "$.".toAscii

structure TokensParser where
  k : TokensKind
  pos : Pos
  label : String

instance : ToString TokensParser where
  toString | ⟨k, pos, label⟩ => s!"at {pos}: {k} {label}"

inductive TokenParser
  | start : TokenParser
  | comment : TokenParser → TokenParser
  /-- `$c` accumulation; the flag records whether any symbol has been seen,
  so the terminator can enforce the book's `constant+` arity. -/
  | const : Bool → TokenParser
  /-- `$v` accumulation; the flag records whether any symbol has been seen,
  so the terminator can enforce the book's `variable+` arity. -/
  | var : Bool → TokenParser
  | djvars : Array String → TokenParser
  | math : Array Sym → TokensParser → TokenParser
  | label : Pos → String → TokenParser
  | includePath : TokenParser → Pos → TokenParser
  | includeClose : TokenParser → Pos → String → TokenParser
  | proof : ProofState → TokenParser
  deriving Inhabited

def TokenParser.toString : TokenParser → String
  | .start => "start"
  | .comment p => "comment " ++ toString p
  | .const _ => "const"
  | .var _ => "var"
  | .djvars s => s!"djvars {s}"
  | .math s p => s!"math {s} {p}"
  | .label pos l => s!"at {pos}: ? {l}"
  | .includePath resume pos =>
      s!"at {pos}: include path (resume {toString resume})"
  | .includeClose resume pos path =>
      s!"at {pos}: include close {path} (resume {toString resume})"
  | .proof p => ToString.toString p

instance : ToString TokenParser := ⟨TokenParser.toString⟩

structure ParserState where
  db : DB
  tokp : TokenParser
  charp : CharParser
  line : Nat
  linepos : Nat
  sourceFile : String := ""
  deriving Inhabited

namespace ParserState


@[inline] def withDB (f : DB → DB) (s : ParserState) : ParserState :=
  { s with db := f s.db }


def mkPos (s : ParserState) (pos : Nat) : Pos := ⟨s.line, pos - s.linepos⟩

def mkError (s : ParserState) (pos : Pos) (msg : String) : ParserState :=
  s.withDB fun db => db.mkError pos msg

def mkErrorWithEvidence (s : ParserState) (pos : Pos) (msg : String) (ev : ErrorEvidence) : ParserState :=
  s.withDB fun db => db.mkErrorWithEvidence pos msg ev

def mkErrorFromEvidence (s : ParserState) (pos : Pos) (ev : ErrorEvidence) : ParserState :=
  s.withDB fun db => db.mkErrorFromEvidence pos ev

@[inline] def requestInclude (s : ParserState) (resume : TokenParser)
    (includePath : String) : ParserState :=
  { s with
      tokp := resume
      db := { s.db with error? := some ⟨.includeRequest s.sourceFile includePath, default⟩ } }

def normalizeIncludePath (literalPaths : Bool) (sourceFile : String)
    (rawPath : String) : Except IncludeError String := do
  if rawPath.isEmpty then
    throw (.emptyPathBeforeNormalization sourceFile)
  -- Mirror modes keep the include string exactly as written (the references
  -- key file identity and lookup on the literal spelling, "./x" included);
  -- spec-faithful modes strip a leading "./" before canonicalizing.
  if literalPaths then
    return rawPath
  let normalized :=
    if rawPath.startsWith "./" then
      (rawPath.drop 2).toString
    else
      rawPath
  if normalized.isEmpty then
    throw (.pathEmptyAfterNormalization rawPath sourceFile)
  pure normalized

def includePathFromToken (tk : ByteSlice) : String × Bool :=
  let raw := tk.toString
  if raw.endsWith "$]" then
    ((raw.take (raw.length - 2)).toString, true)
  else
    (raw, false)



def mkErrorAt (s : ParserState) (pos : Pos) (l msg : String) : ParserState :=
  s.mkError pos s!"at {l}: {msg}"

def withAt (l : String) (f : Unit → ParserState) : ParserState :=
  let s := f ()
  if let some ⟨.error pos msg, i⟩ := s.db.error? then
    s.withDB fun db => { db with error? := some ⟨.error pos s!"at {l}: {msg}", i⟩ }
  else s



def label (s : ParserState) (pos : Pos) (tk : ByteSlice) : ParserState :=
  let (ok, tk) := toLabel tk
  if ok then { s with tokp := .label pos tk }
  else s.mkErrorFromEvidence pos (.tokenForm (.invalidLabel tk))



def withMath (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) : ParserState :=
  let (ok, tk) := toMath tk
  if !ok then
    s.mkErrorFromEvidence pos (.tokenForm (.invalidMathString tk))
  else
  f s tk


-- Proof-friendly djvars loop (recursive, avoids forIn elaboration).
def djvars_loop_aux (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) (i : Nat) : ParserState :=
  if h : i < arr.size then
    let tk1 := arr[i]
    if tk1 == tk then
      s.mkErrorFromEvidence pos (.scopeDecl (.duplicateDisjointVariable tk))
    else
      let p := if tk1 < tk then (tk1, tk) else (tk, tk1)
      let s' := s.withDB fun db => db.withDJ fun dj => dj.push p
      djvars_loop_aux arr s' pos tk (i + 1)
  else
    { s with tokp := .djvars (arr.push tk) }
termination_by arr.size - i


def djvars_loop (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) : ParserState :=
  match s.db.djvarsScopeViolation? tk with
  | some err =>
      s.mkErrorFromEvidence pos (.scopeDecl err)
  | none =>
      djvars_loop_aux arr s pos tk 0


def sym (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) : ParserState :=
  if tk.eqArray "$.".toAscii then
    { s with tokp := .start }
  else s.withMath pos tk fun s tk =>
    s.withDB fun db => db.insert pos tk f


def resumeThm (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  let pr := s.db.mkProofState pos l fmla fr
  { s with tokp := .proof pr }


inductive CompressedAction
  | step (n : Nat)
  | save
  | unknown

/-- Decode a compressed proof token into actions and the updated accumulator. -/
def decodeCompressed (tk : ByteSlice) (chr : Nat)
    (invalidBytePolicy : CompressedInvalidBytePolicy := .reject) :
    Except ProofCheckFail (List CompressedAction × Nat) := do
  let mut chr := chr
  let mut acts : List CompressedAction := []
  for c in tk do
    if 'A'.toUInt8 ≤ c && c ≤ 'Z'.toUInt8 then
      if c ≤ 'T'.toUInt8 then
        let n := 20 * chr + (c - 'A'.toUInt8).toNat
        acts := CompressedAction.step n :: acts
        chr := 0
      else if c < 'Z'.toUInt8 then
        chr := 5 * chr + (c - 'T'.toUInt8).toNat
      else
        acts := CompressedAction.save :: acts
        chr := 0
    else if c = '?'.toUInt8 then
      acts := CompressedAction.unknown :: acts
      chr := 0
    else
      match invalidBytePolicy with
      | .reject => throw (.proofCheck .proofParseError)
      | .ignore => pure ()
  return (acts.reverse, chr)

def applyCompressedActions (db : DB) (pr : ProofState) (acts : List CompressedAction) :
    Except ProofCheckFail ProofState :=
  acts.foldlM (fun pr act =>
    match act with
    | .step n =>
        db.stepProof pr n
    | .save =>
        -- Per spec Appendix B: Z saves current stack top to heap for reuse
        -- Test: metamath-test/tests/core/small/out-of-range-saved-step-bad1.mm
        match pr.save with
        | .ok pr' => pure pr'
        | .error err => throw (.compressedSave err)
    | .unknown =>
        -- Per spec §4.1.4: ? marks incomplete proof step, verifier should accept
        -- Test: metamath-test/tests/unit/test30_qmark_in_compressed_proof.mm
        -- Knife mode rejects unknown steps (stricter policy)
        if db.config.rejectUnknownSteps then
          throw (.proofCheck .unknownStepQuestionRejected)
        else
          pure { pr.push pr.fmla with incomplete := true }
    ) pr

/-- Scope/config gate for rejecting top-level $e in strict modes. -/
def topLevelEssViolation? (db : DB) : Option ScopeDeclError :=
  if db.config.rejectToplevelEss && db.scopes.size == 0 then
    some .topLevelEssentialNotAllowed
  else
    none


def feedTokens (s : ParserState) (arr : Array Sym) : TokensParser → ParserState
  | ⟨k, pos, l⟩ => withAt l fun _ => Id.run do
    unless Formula.hasConstHead arr do
      return s.mkErrorFromEvidence pos (.scopeDecl .firstSymbolNotConstant)
    match k with
    | .float =>
      unless Formula.isFloatShape arr do
        return s.mkErrorFromEvidence pos (.scopeDecl .expectedConstantAndVariable)
      let s := s.withDB fun db => db.insertHyp pos l false arr
      pure { s with tokp := .start }
    | .ess =>
      -- Knife mode rejects top-level $e (stricter policy)
      -- Test: metamath-test/tests/unit/test67_toplevel_essential.mm
      match topLevelEssViolation? s.db with
      | some err =>
          return s.mkErrorFromEvidence pos (.scopeDecl err)
      | none =>
          let s := s.withDB fun db => db.insertHyp pos l true arr
          pure { s with tokp := .start }
    | .ax =>
      let s := s.withDB fun db => db.insertAxiom pos l arr
      pure { s with tokp := .start }
    | .thm =>
      match s.db.trimFrame' arr with
      | .ok fr =>
        if s.db.interrupt then
          s.withDB fun db => { db with error? := some ⟨.thm pos l arr fr, default⟩ }
        else s.resumeThm pos l arr fr
      | .error err =>
        s.mkErrorFromEvidence pos (.scopeDecl err)


def feedProof (s : ParserState) (tk : ByteSlice) (pr : ProofState) : ParserState :=
  withAt pr.label fun _ =>
    match go pr with
    | .ok pr => { s with tokp := .proof pr }
    | .error err =>
      s.mkErrorFromEvidence pr.pos (ProofCheckFail.evidence err)
where
  goNormal (pr : ProofState) : Except ProofCheckFail ProofState :=
    -- Per spec §4.1.4: "A proof may contain a ? in place of a label to indicate
    -- an unknown step. A proof verifier may ignore any proof containing ? but
    -- should warn the user that the proof is incomplete."
    -- Test: metamath-test/tests/unit/test20_unknown_step_qmark_(should_accept_with_warning).mm
    -- Knife mode rejects unknown steps (stricter policy)
    if tk.eqArray "?".toAscii then
      if s.db.config.rejectUnknownSteps then
        throw (.proofCheck .unknownStepQuestionRejected)
      else
        pure { pr.push pr.fmla with incomplete := true }
    else
      let (ok, tk) := toLabel tk
      if ok then s.db.stepNormal pr tk
      else throw (.tokenForm (.invalidLabel tk))
  go (pr : ProofState) : Except ProofCheckFail ProofState := do
    match pr.ptp with
    | .start =>
      if tk.eqArray "(".toAscii then
        -- Enter compressed proof mode: pre-populate heap with mandatory hypotheses
        let pr ← s.db.preloadMandatoryHyps pr
        pure { pr with ptp := .preload }
      else goNormal { pr with ptp := .normal }
    | .preload =>
      if tk.eqArray ")".toAscii then
        pure { pr with ptp := .compressed 0 }
      else
        let (ok, tk) := toLabel tk
        if ok then s.db.preload pr tk
        else throw (.tokenForm (.invalidLabel tk))
    | .normal => goNormal pr
    | .compressed chr =>
      let mut pr := pr
      let (acts, chr) ← decodeCompressed tk chr s.db.config.compressedInvalidBytes
      pr ← applyCompressedActions s.db pr acts
      pure { pr with ptp := .compressed chr }


def finishProof (s : ParserState) : ProofState → ParserState
  | ⟨pos, l, fmla, fr, _, stack, ptp, incomplete⟩ => withAt l fun _ => Id.run do
    let s := { s with tokp := .start }
    match ptp with
    | .compressed 0 => ()
    | .normal => ()
    | _ =>
        return s.mkErrorFromEvidence pos (.proofCheck .proofParseError)
    unless stack.size == 1 do
      return s.mkErrorFromEvidence pos (.theoremFinality
        (.theoremMoreThanOneStackElement stack.size))
    unless stack[0]! == fmla do
      return s.mkErrorFromEvidence pos (.theoremFinality
        (.theoremClaimMismatch fmla stack[0]!))
    s.withDB fun db => (db.insert pos l (.assert fmla fr)).recordIncomplete incomplete l


def feedToken (s : ParserState) (pos : Nat) (tk : ByteSlice) : ParserState :=
  let absPos := pos
  let pos := s.mkPos pos
  match s.tokp with
  | .comment p =>
    if tk.eqArray "$)".toAscii then { s with tokp := p }
    else if tk.eqArray "$(".toAscii then
      -- Per spec §4.1.2: "comments may not contain the 2-character sequences $( or $)"
      -- Test: metamath-test/tests/unit/test03_nested_comment_delimiters.mm
      s.mkErrorFromEvidence pos (.tokenForm .nestedCommentDelimiter)
    else s
  | p =>
    if tk.eqArray "$(".toAscii then { s with tokp := p.comment } else
    if tk.eqArray "$[".toAscii then
      let scopeDepth := s.db.scopes.size
      let inStatement :=
        match p with
        | .start => false
        | _ => true
      match includeDirectiveViolation? s.db.config scopeDepth inStatement absPos with
      | some err =>
          s.mkErrorFromEvidence pos (.includeErr err)
      | none =>
          { s with tokp := .includePath p pos }
    else
    match p with
    | .comment _ => unreachable!
    | .start =>
      if tk.len == 2 && tk[0]! == '$'.toUInt8 then
        match Metamath.Verify.uint8ToChar (tk[1]!) with
        | '{' => s.withDB .pushScope
        | '}' => s.withDB (.popScope pos)
        | 'c' => { s with tokp := .const false }
        | 'v' => { s with tokp := .var false }
        | 'd' => { s with tokp := .djvars #[] }
        | _ => s.label pos tk
      else s.label pos tk
    | .const seen =>
        if tk.eqArray "$.".toAscii then
          if seen then { s with tokp := .start }
          else s.mkErrorFromEvidence pos
            (.scopeDecl .constantStatementEmpty)
        else
          let s := s.sym pos tk .const
          { s with tokp := .const true }
    | .var seen =>
        if tk.eqArray "$.".toAscii then
          if seen then { s with tokp := .start }
          else s.mkErrorFromEvidence pos
            (.scopeDecl .variableStatementEmpty)
        else
          let s := s.sym pos tk .var
          { s with tokp := .var true }
    | .djvars arr =>
      if tk.eqArray "$.".toAscii then
        if arr.size < 2 then
          s.mkErrorFromEvidence pos
            (.scopeDecl (.disjointStatementTooShort arr.size))
        else
          { s with tokp := .start }
      else
      s.withMath pos tk fun s tk => djvars_loop arr s pos tk
    | .math arr p =>
      if tk.eqArray p.k.delim then
        s.feedTokens arr p
      else
        s.withMath pos tk fun s tk => Id.run do
          let tk ← match s.db.find? tk with
          | some (.const _) => Sym.const tk
          | some (.var _) =>
            -- A math symbol must be *active*, not merely declared: a variable whose
            -- `$v` block has been popped is rejected by the same gate the spec
            -- mirrors, with its own fault code.
            if s.db.isActiveVar tk then Sym.var tk
            else return s.mkErrorFromEvidence pos (.scopeDecl (.inactiveMathSymbol tk))
          | _ =>
            match s.db.mathSymbolViolation? tk with
            | some err =>
              return s.mkErrorFromEvidence pos (.scopeDecl err)
            | none =>
              -- Unreachable if gate/model invariants hold; classify as internal consistency fault.
              return s.mkErrorFromEvidence pos (.internalGate s.db.config.allowDuplicateFloat s.db.wellFormed? s.db.assertDvVarsInFrame?)
          { s with tokp := .math (arr.push tk) p }
    | .label pos lab =>
      if tk.len == 2 && tk[0]! == '$'.toUInt8 then
        let go (s : ParserState) (k : TokensKind) :=
          { s with tokp := .math #[] ⟨k, pos, lab⟩ }
        match Metamath.Verify.uint8ToChar (tk[1]!) with
        | 'f' => go s .float
        | 'e' => go s .ess
        | 'a' => go s .ax
        | 'p' => go s .thm
        | _ =>
          let ty := (toLabel tk).2
          s.mkErrorFromEvidence pos (.tokenForm (.unknownStatementType ty))
      else
        let ty := (toLabel tk).2
        s.mkErrorFromEvidence pos (.tokenForm (.unknownStatementType ty))
    | .includePath resume includePos =>
      if tk.eqArray "$]".toAscii then
        s.mkErrorFromEvidence includePos (.includeErr (.emptyPathBeforeNormalization s.sourceFile))
      else
        let (rawPath, closesInline) := includePathFromToken tk
        match normalizeIncludePath s.db.config.literalIncludePaths s.sourceFile rawPath with
        | .error err =>
            s.mkErrorFromEvidence includePos (.includeErr err)
        | .ok includePath =>
            if closesInline then
              s.requestInclude resume includePath
            else
              { s with tokp := .includeClose resume includePos includePath }
    | .includeClose resume includePos includePath =>
      if tk.eqArray "$]".toAscii then
        s.requestInclude resume includePath
      else
        s.mkErrorFromEvidence includePos (.tokenForm (.notACommand tk.toString))
    | .proof pr =>
      let s := { s with tokp := default }
      if tk.eqArray "$.".toAscii then s.finishProof pr
      else s.feedProof tk pr


inductive OldToken
  | this (off : Nat)
  | old (base off : Nat) (arr : ByteArray)

inductive FeedState
  | ws : FeedState
  | token : OldToken → FeedState

def updateLine (s : ParserState) (i : Nat) (c : UInt8) : ParserState :=
  if c == '\n'.toUInt8 then { s with line := s.line + 1, linepos := i + 1 } else s


def feed (base : Nat) (arr : ByteArray)
    (i : Nat) (rs : FeedState) (s : ParserState) : ParserState :=
  if h : i < arr.size then
    let c := arr[i]
    if isWhitespace c then
      match rs with
      | .ws =>
        let s := s.updateLine (base + i) c
        feed base arr (i+1) .ws s
      | .token ot =>
        let s := match ot with
        | .this off => s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
        | .old base off arr' => s.feedToken (base + off)
          (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
        let s : ParserState := s.updateLine (base + i) c
        if let some ⟨e, _⟩ := s.db.error? then
          { s with db := { s.db with error? := some ⟨e, i+1⟩ } }
        else feed base arr (i+1) .ws s
    else
      let rs := if let .ws := rs then .token (.this i) else rs
      feed base arr (i+1) rs s
  else
    { s with charp :=
      match rs with
      | .ws => .ws
      | .token ot =>
        match ot with
        | .this off => .token base (ByteSliceT.mk arr off)
        | .old base off arr' => .token base (ByteSliceT.mk (arr' ++ arr) off) }
termination_by arr.size - i


def feedAll (s : ParserState) (base : Nat) (arr : ByteArray) : ParserState :=
  match s.charp with
  | .ws => s.feed base arr 0 .ws
  | .token base' tk =>
    let arr' := tk.byteArray
    let off := tk.start
    let s := { s with charp := default }
    s.feed base arr 0 (.token (.old base' off arr'))


def done (s : ParserState) (base : Nat) : DB := Id.run do
  let mut s := s
  if s.db.error then
    return s.db
  if let .token pos tk := s.charp then
    s := s.feedToken pos tk.toSlice
  if s.db.error then
    return s.db
  let base := s.mkPos base
  let { db := db, tokp := tokp, ..} := s
  match tokp with
  | .start =>
    if db.scopes.size > 0 then
      db.mkParseError base .unclosedBlock
    else db
  | .comment _ => db.mkParseError base .unclosedComment
  | .const _ => db.mkParseError base .unclosedConst
  | .var _ => db.mkParseError base .unclosedVar
  | .djvars _ => db.mkParseError base .unclosedDjvars
  | .math _ p => match p.k with
    | .float => db.mkParseError base .unclosedFloat
    | .ess => db.mkParseError base .unclosedEss
    | .ax => db.mkParseError base .unclosedAx
    | .thm => db.mkParseError base .unclosedThm
  | .label pos lab => db.mkErrorFromEvidence pos (.tokenForm (.notACommand lab))
  | .includePath _ pos => db.mkErrorFromEvidence pos (.tokenForm (.notACommand "$["))
  | .includeClose _ pos _ => db.mkErrorFromEvidence pos (.tokenForm (.notACommand "$["))
  | .proof _ => db.mkParseError base .unclosedProof




end ParserState

/-! ## Pure Parser Entry Point

`checkBytes` is a pure parser entry point for proofs about parser invariants.
It processes the full byte array in one pass. This is simpler to reason about
than chunked IO. The canonical IO entrypoint (`check`) is single-pass include-aware
streaming (`checkSinglePass`), while `checkBytes` remains the pure parser model.
-/
def checkBytesCore (arr : ByteArray) (config : ModeConfig := {}) : DB :=
  let initialDB : DB := { (default : DB) with config := config }
  let initialState : ParserState := { (default : ParserState) with db := initialDB }
  let s := initialState.feedAll 0 arr
  s.done arr.size


def checkBytes (arr : ByteArray) (config : ModeConfig := {}) : DB :=
  let db := checkBytesCore arr config
  if db.error? = none then
    -- When allowDuplicateFloat is true, skip wellFormed? check since duplicate $f
    -- would cause wellFormed? to fail (but is intentionally allowed)
    if (db.config.allowDuplicateFloat || db.wellFormed?) && db.assertDvVarsInFrame? then
      db
    else
      db.mkErrorFromEvidence ⟨0, 0⟩
        (.internalGate db.config.allowDuplicateFloat db.wellFormed? db.assertDvVarsInFrame?)
  else
    db



section AllCodeRuleClauseTheorems

end AllCodeRuleClauseTheorems

-- Preprocessor with include support
-- Processes $[ filename $] directives by recursively loading files
-- Handles self-includes and cycles per spec §4.1.2
-- In strict mode: validates includes are at outermost scope and not inside statements

-- Two sets track include state:
-- - `processing`: Files currently being processed (call stack) - for cycle detection
-- - `seen`: All files ever fully processed - for duplicate ignore
/-- Pure include scanner output:
- `.bytes chunk`: emit parser bytes directly.
- `.needInclude path`: request include expansion of `path` relative to current file. -/
inductive IncludeScanChunk where
  | bytes (chunk : ByteArray)
  | needInclude (path : String)
  deriving Inhabited

/-- [MM §4.1.2] Boundary check for a child include file that has been consumed.

An included file must end between statements, at the block depth it was entered
at, with nothing buffered.  This classifies the failure exactly as `done` does,
except that the depth it compares against is the child's entry depth rather than
zero — a child legitimately entered inside an open block must merely restore it,
not close it.

Returns `none` when the child ended legally. -/
def childFileBoundaryError? (entryScopeDepth : Nat) (s : ParserState) :
    Option ErrorEvidence :=
  match s.charp with
  | .token _ _ => some (.doneMode .unclosedBlock)  -- callers flush first
  | .ws =>
      match s.tokp with
      | .start =>
          if s.db.scopes.size = entryScopeDepth then none
          else some (.doneMode .unclosedBlock)
      | .comment _ => some (.doneMode .unclosedComment)
      | .const _ => some (.doneMode .unclosedConst)
      | .var _ => some (.doneMode .unclosedVar)
      | .djvars _ => some (.doneMode .unclosedDjvars)
      | .math _ p =>
          match p.k with
          | .float => some (.doneMode .unclosedFloat)
          | .ess => some (.doneMode .unclosedEss)
          | .ax => some (.doneMode .unclosedAx)
          | .thm => some (.doneMode .unclosedThm)
      | .label _ lab => some (.tokenForm (.notACommand lab))
      | .includePath _ _ => some (.tokenForm (.notACommand "$["))
      | .includeClose _ _ _ => some (.tokenForm (.notACommand "$["))
      | .proof _ => some (.doneMode .unclosedProof)

/-- Explicit include-driver stack frame for single-pass include processing. -/
structure IncludeDriverFrame where
  fname : String
  canonStr : String
  contents : ByteArray
  offset : Nat := 0
  nextDepth : Nat
  needsSep : Bool := false
  /-- Line state of *this* file, parked while a child include runs, so that
  positions are reported per file rather than cumulatively across the
  traversal.  The column is stored as an offset from the current absolute
  position, not as an absolute `linepos`, because the driver's absolute
  counter keeps advancing while the child is fed.  Restored when the child
  frame is popped. -/
  savedLine : Nat := 0
  savedCol : Nat := 0
  /-- Parser block depth at the moment this file was entered.  [MM §4.1.2] an
  included file may not contain an incomplete statement, so on exhaustion the
  child must have returned to exactly this depth with no statement open.  No
  default: every frame must state the boundary it will be held to. -/
  entryScopeDepth : Nat
  deriving Inhabited

/-- Request emitted by the include-aware parser driver core.
`pushFile` is raised when parser tokenization encounters `$[ ... $]`. -/
inductive IncludeRequest where
  | pushFile (sourceFile : String) (includePath : String)
  deriving Inhabited

/-- Mutable include-driver state carried by the IO driver loop.
This keeps include-tracking (`processing`, `seen`, `stack`) explicit and separate
from parser-core transition logic. -/
structure IncludeDriverState where
  parser : ParserState
  base : Nat
  processing : HashSet String
  seen : HashSet String
  stack : List IncludeDriverFrame
  deriving Inhabited

/-- Result of one pure driver step (no IO performed).
- `fed`: bytes consumed or frame popped; driver state advanced, keep looping
- `done`: include stack is empty; driver should finalize and return
- `push`: parser requested a child include; driver must do IO then resume -/
inductive FrameStep where
  | fed  (st : IncludeDriverState)
  | done (st : IncludeDriverState)
  | push (sourceFile includePath : String)
         (nextDepth : Nat) (st : IncludeDriverState)

def scanIncludes (contents : ByteArray) (fname : String) (config : ModeConfig := {}) :
    Except IncludeError (List IncludeScanChunk) := Id.run do
  let mut chunks : List IncludeScanChunk := []
  let mut buf : ByteArray := ByteArray.empty
  let mut i := 0
  let mut scopeDepth := 0  -- Track ${ $} nesting
  let mut inStatement := false  -- Track if we're inside a statement (after label before $.)
  let mut inComment := false  -- Track if we're inside a comment

  while i < contents.size do
    -- Track comment state (comments take precedence over everything else)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := Metamath.Verify.uint8ToChar (contents[i+1]!)
      if c == '(' then
        inComment := true
        buf := buf.push contents[i]!
        buf := buf.push contents[i+1]!
        i := i + 2
        continue
      else if c == ')' then
        inComment := false
        buf := buf.push contents[i]!
        buf := buf.push contents[i+1]!
        i := i + 2
        continue

    -- Skip everything inside comments
    if inComment then
      buf := buf.push contents[i]!
      i := i + 1
      continue

    -- Track statement boundaries at token starts.  `$c`, `$v`, and `$d`
    -- begin with their keyword; labeled statements begin with the label, so a
    -- four-keyword (`$f`/`$e`/`$a`/`$p`) heuristic is incomplete.  Outside
    -- comments, only `$.`, `${`, and `$}` leave the scanner between
    -- statements; `$[` preserves the current state until its placement gate
    -- below has run.
    let atTokenStart := i == 0 || isWhitespace contents[i - 1]!
    if atTokenStart then
      if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
        let c := Metamath.Verify.uint8ToChar (contents[i+1]!)
        if c == '{' then
          scopeDepth := scopeDepth + 1
          inStatement := false
        else if c == '}' then
          scopeDepth := max 0 (scopeDepth - 1)
          inStatement := false
        else if c == '.' then
          inStatement := false
        else if c != '[' then
          inStatement := true
      else if !isWhitespace contents[i]! then
        inStatement := true

    -- Look for $[ token (only outside comments)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 && contents[i+1]! == '['.toUInt8 then
      -- Validate strict mode constraints (spec §4.1.2) via a pure gate helper.
      match includeDirectiveViolation? config scopeDepth inStatement i with
      | some err =>
          return .error err
      | none =>
          pure ()

      i := i + 2
      -- Skip whitespace after $[
      while i < contents.size && isWhitespace contents[i]! do
        i := i + 1

      -- Extract filename until $]
      let mut includePath := ByteArray.empty
      let startPos := i  -- Debug: save start position
      while i + 1 < contents.size && !(contents[i]! == '$'.toUInt8 && contents[i+1]! == ']'.toUInt8) do
        let c := contents[i]!
        if !isWhitespace c then
          includePath := includePath.push c
        i := i + 1
      -- Debug: check what we extracted
      if includePath.isEmpty && i > startPos then
        return .error (.extractedEmptyPath (toString startPos) (toString i) fname)

      -- Skip $]
      if i + 1 < contents.size then i := i + 2

      -- Convert includePath to String
      let mut includeFile := String.fromUTF8! includePath

      -- Debug: check extracted path before normalization
      if includeFile.isEmpty then
        return .error (.emptyPathBeforeNormalization fname)

      -- Normalize "./" prefix (FilePath doesn't handle it well)
      if includeFile.startsWith "./" then
        includeFile := (includeFile.drop 2).toString

      -- Check for empty path after normalization
      if includeFile.isEmpty then
        return .error (.pathEmptyAfterNormalization (String.fromUTF8! includePath) fname)

      -- Flush buffered bytes before the include
      if !buf.isEmpty then
        chunks := chunks.concat (.bytes buf)
        buf := ByteArray.empty
      chunks := chunks.concat (.needInclude includeFile)
      continue
    else
      buf := buf.push contents[i]!
      i := i + 1

  if !buf.isEmpty then
    chunks := chunks.concat (.bytes buf)
  return .ok chunks

/-- Canonical DB materialization for include-preprocessor errors. -/
def includePreprocessErrorDB (config : ModeConfig) (err : IncludeError) : DB :=
  let initialDB : DB := { (default : DB) with config := config }
  initialDB.mkErrorFromEvidence ⟨1, 1⟩ (.includeErr err)


/-- Feed one contiguous byte chunk into the parser state and advance absolute base offset. -/
@[inline] def flushChunkToParser (s : ParserState) (base : Nat) (chunk : ByteArray) :
    ParserState × Nat :=
  if chunk.isEmpty then
    (s, base)
  else
    let s := s.feedAll base chunk
    (s, base + chunk.size)

/-- Finalize the one token already buffered by `feedAll`, without rereading
source bytes or manufacturing a second input pass.  Resetting `charp` makes the
result safe to resume after an include request. -/
@[inline] def flushPendingToken (s : ParserState) : ParserState :=
  match s.charp with
  | .ws => s
  | .token pos tk =>
      { s.feedToken pos tk.toSlice with charp := .ws }

/-- Extract a driver-level include request from parser error payloads. -/
@[inline] def parserIncludeRequestOfError? (err : Error) :
    Option IncludeRequest :=
  match err with
  | .includeRequest sourceFile includePath =>
      some (.pushFile sourceFile includePath)
  | _ =>
      none

/-- Clear a driver-consumed include request without changing the suspended
token-parser continuation.  This is used only after
`parserIncludeRequestOfError?` has identified the interrupt payload. -/
@[inline] def clearIncludeRequest (s : ParserState) : ParserState :=
  { s with db := { s.db with error? := none } }

/-- Admission verdict for one include candidate. -/
inductive IncludeAdmission where
  /-- New file: admit a frame with updated bookkeeping. -/
  | admit (nextDepth : Nat) (processing seen : Std.HashSet String)
  /-- [MM 4.1.2] a later reference to an already-included file: ignore. -/
  | skipDuplicate
  /-- [MM 4.1.2] a later reference to a file whose first reference is still
  being expanded.  Non-rejecting modes ignore it; canonical-path modes also
  emit a warning, while literal-path mirror modes remain silent. -/
  | skipCycle

/-- Pure include-admission core: depth, cycle and duplicate policy for one
candidate file, shared by the IO driver's root and child preparation so the
two cannot drift. -/
def includeFrameGate (fname canonStr : String) (depth : Nat)
    (rejectCycles : Bool)
    (processing seen : Std.HashSet String) :
    Except IncludeError IncludeAdmission :=
  match depth with
  | 0 => .error (.depthExceeded fname)
  | d + 1 =>
      if processing.contains canonStr then
        if rejectCycles then .error (.cycleDetected canonStr) else .ok .skipCycle
      else if seen.contains canonStr then
        .ok .skipDuplicate
      else
        .ok (.admit (d + 1) (processing.insert canonStr) (seen.insert canonStr))

/-- Compute the path passed to the filesystem for an include request.
Literal-path modes use the include string from the invocation directory;
canonical modes first resolve it relative to the including file. -/
def includeLookupPath (literalPaths : Bool) (sourceFile includePath : String) :
    System.FilePath :=
  if literalPaths then
    System.FilePath.mk includePath
  else
    (System.FilePath.parent sourceFile |>.getD ".") / includePath

/-- Select the key used by include-once suppression after filesystem
canonicalization has been obtained.  Literal modes intentionally ignore the
canonical path; canonical modes intentionally ignore the original spelling. -/
def includeIdentityKey (literalPaths : Bool) (literal canonical : String) : String :=
  if literalPaths then literal else canonical

/-- Build an include stack frame from a file path under depth/cycle/duplicate guards.
Returns:
- `none` when duplicate suppression (`seen`) skips this file
- `some frame` when a new file frame is ready for scanning/feeding
along with updated `processing` and `seen` sets. -/
def prepareIncludeFrameWithIO
    (realPath : String → IO System.FilePath)
    (readFile : String → IO ByteArray)
    (fname : String) (depth : Nat) (entryScopeDepth : Nat)
    (rejectCycles literalPaths : Bool)
    (processing seen : HashSet String) :
    IO (Except IncludeError (Option IncludeDriverFrame × HashSet String × HashSet String)) := do
  match depth with
  | 0 =>
      return .error (.depthExceeded fname)
  | _ + 1 =>
      -- Mirror modes key file identity on the include string as written;
      -- spec-faithful modes canonicalize so every spelling of one file is one
      -- file.
      let canonStr ←
        if literalPaths then
          pure (includeIdentityKey true fname "")
        else do
          pure (includeIdentityKey false fname (← realPath fname).toString)
      match includeFrameGate fname canonStr depth rejectCycles processing seen with
      | .error err =>
          return .error err
      | .ok .skipDuplicate =>
          return .ok (none, processing, seen)
      | .ok .skipCycle =>
          -- Accepted per the spec, but almost always an authoring mistake:
          -- say so without failing.  Mirror modes stay silent — the
          -- references print nothing here.
          unless literalPaths do
            IO.eprintln s!"warning: include cycle ignored: '{fname}' is already being included (treated like white space per section 4.1.2)"
          return .ok (none, processing, seen)
      | .ok (.admit nextDepth processing seen) =>
          let contents ← readFile fname
          return .ok
            (some {
              fname := fname
              canonStr := canonStr
              contents := contents
              nextDepth := nextDepth - 1
              entryScopeDepth := entryScopeDepth
            }, processing, seen)

/-- Restore the line state parked on the frame we are returning to, so a
child's newlines do not leak into its parent's reported positions.  With an
empty stack there is nothing to resume and the state is left untouched. -/
def restoreLineState (s : ParserState) (base : Nat) :
    List IncludeDriverFrame → ParserState
  | [] => s
  | parent :: _ =>
      -- A resuming parent is first fed one injected separator byte, which
      -- advances the absolute counter without being part of its source, so
      -- the reconstructed line start accounts for it.
      let resumeBase := if parent.needsSep then base + 1 else base
      { s with line := parent.savedLine,
               linepos := resumeBase - parent.savedCol }

/-- Pop an exhausted child frame, enforcing the [MM §4.1.2] file boundary first.

Both exhausted-frame branches route through here so they cannot drift.  The
boundary error is raised *before* the parent's line state is restored, so the
reported position is the child's EOF in the child's file rather than a parent
coordinate.  Token-splicing profiles opt out: there the child is explicitly
permitted to hand a partial token to its parent. -/
def popExhaustedFrame (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (rest : List IncludeDriverFrame) : ParserState :=
  match rest with
  | [] =>
      -- Root frame: end of input, not a file boundary.  `done` is the sole owner
      -- of end-of-input finality; checking here too would give it two owners and
      -- could report the root's unfinished state against a child-relative rule.
      s
  | _ :: _ =>
      match s.db.config.childFileBoundary with
      | .spliceAll =>
        restoreLineState s base rest
      | .spliceExceptComments =>
        -- `metamath.exe` scans each physical file for includes before it
        -- concatenates their contents.  That scan diagnoses an unterminated
        -- comment locally, even though other parser state may cross the file
        -- boundary after concatenation.
        match s.charp, s.tokp with
        | .ws, .comment _ =>
            { s with sourceFile := frame.fname }.withDB fun db =>
              db.mkErrorFromEvidence (s.mkPos base) (.doneMode .unclosedComment)
        | _, _ => restoreLineState s base rest
      | .strict =>
        match childFileBoundaryError? frame.entryScopeDepth s with
        | some ev => { s with sourceFile := frame.fname }.withDB
            fun db => db.mkErrorFromEvidence (s.mkPos base) ev
        | none => restoreLineState s base rest

/-- Pure: advance the include-driver by one step without performing any IO.
Returns `fed` when bytes were consumed or a frame was popped (keep looping),
`done` when the stack is empty (finalize), or `push` when the parser
encountered a `$[ ... $]` directive and the driver must read a file. -/
def stepFrame (st : IncludeDriverState) : FrameStep :=
  match st.stack with
  | [] => .done st
  | frame :: rest =>
      if frame.needsSep then
        let sep := ByteArray.empty.push ' '.toUInt8
        let (s1, base1) := flushChunkToParser st.parser st.base sep
        .fed { st with parser := s1, base := base1,
                       stack := { frame with needsSep := false } :: rest }
      else if frame.offset >= frame.contents.size then
        match st.parser.charp with
        | .ws =>
            -- Exhausted with nothing buffered: check the child boundary, then pop.
            .fed { st with parser := popExhaustedFrame st.parser st.base frame rest,
                           processing := st.processing.erase frame.canonStr,
                           stack := rest }
        | .token _ _ =>
            -- `feedAll` deliberately retains the final token until a boundary.
            -- Flush that one buffered token while this file frame is still live,
            -- so a terminal `$]` can request its child before the frame is popped.
            let sInput := { st.parser with sourceFile := frame.fname }
            let s1 := flushPendingToken sInput
            match s1.db.error? with
            | some ⟨err, consumed⟩ =>
                match parserIncludeRequestOfError? err with
                | some (.pushFile sourceFile includeFile) =>
                    let parentFrame :=
                      { frame with needsSep := true, savedLine := s1.line,
                                   savedCol :=
                                     (st.base + consumed) - s1.linepos }
                    let sCleared := clearIncludeRequest s1
                    .push sourceFile includeFile frame.nextDepth
                      { st with parser := sCleared, base := st.base + consumed,
                                stack := parentFrame :: rest }
                | none =>
                    .fed { st with parser := s1, base := st.base + consumed }
            | none =>
                .fed { st with parser := popExhaustedFrame s1 st.base frame rest,
                               processing := st.processing.erase frame.canonStr,
                               stack := rest }
      else
        let chunk := frame.contents.extract frame.offset frame.contents.size
        let sInput := { st.parser with sourceFile := frame.fname }
        let s1 := sInput.feedAll st.base chunk
        match s1.db.error? with
        | some ⟨err, consumed⟩ =>
            match parserIncludeRequestOfError? err with
            | some (.pushFile sourceFile includeFile) =>
                let parentFrame :=
                  { frame with offset := frame.offset + consumed,
                               needsSep := true, savedLine := s1.line,
                               savedCol :=
                                 (st.base + consumed) - s1.linepos }
                let sCleared := clearIncludeRequest s1
                .push sourceFile includeFile frame.nextDepth
                  { st with parser := sCleared, base := st.base + consumed,
                            stack := parentFrame :: rest }
            | none =>
                .fed { st with parser := s1, base := st.base + consumed }
        | none =>
            .fed { st with parser := s1, base := st.base + chunk.size,
                           stack := { frame with offset := frame.contents.size } :: rest }


/-- Result of a pure driver phase (`runPureSteps`): the driver advanced by
`stepFrame` steps until the pass finished, a parser error stopped it, or the
parser requested an include push that needs the IO layer. -/
inductive DriverPhase where
  | done (st : IncludeDriverState)
  | stopped (st : IncludeDriverState)
  | push (sourceFile includePath : String) (nextDepth : Nat) (st : IncludeDriverState)

/-- Pure-phase termination measure of one frame: unfed bytes plus a pending
injected separator. -/
def IncludeDriverFrame.measure (f : IncludeDriverFrame) : Nat :=
  (f.contents.size - f.offset) + (if f.needsSep then 1 else 0)

/-- Pure-phase termination measure: unfed bytes and pending separators across
the stack, plus the stack height. -/
def IncludeDriverState.measure (st : IncludeDriverState) : Nat :=
  (st.stack.map IncludeDriverFrame.measure).sum + st.stack.length

/-- Every looping (`.fed`, error-free) `stepFrame` result strictly decreases
the driver measure: it consumes the injected separator, consumes the frame's
remaining bytes, or pops a frame.  The error-carrying `.fed` results — the only
ones that leave the measure unchanged — are excluded by the error guard, which
is exactly the condition under which the driver loop keeps looping. -/
theorem stepFrame_fed_measure_lt (st st' : IncludeDriverState)
    (h : stepFrame st = .fed st') (h_err : st'.parser.db.error = false) :
    st'.measure < st.measure := by
  unfold stepFrame at h
  cases h_stack : st.stack with
  | nil =>
      rw [h_stack] at h
      exact absurd h (by simp)
  | cons frame rest =>
      rw [h_stack] at h
      dsimp only [] at h
      by_cases h_sep : frame.needsSep = true
      · -- injected separator consumed: needsSep flips off
        rw [if_pos h_sep] at h
        injection h with h
        subst h
        simp only [IncludeDriverState.measure, IncludeDriverFrame.measure,
          h_stack, List.map_cons, List.sum_cons, List.length_cons, h_sep,
          reduceIte, Bool.false_eq_true]
        omega
      · rw [if_neg h_sep] at h
        by_cases h_exh : frame.offset ≥ frame.contents.size
        · -- frame exhausted
          rw [if_pos h_exh] at h
          cases h_charp : st.parser.charp with
          | ws =>
              -- nothing buffered: boundary check, pop
              rw [h_charp] at h
              dsimp only [] at h
              injection h with h
              subst h
              simp only [IncludeDriverState.measure, h_stack, List.map_cons,
                List.sum_cons, List.length_cons]
              omega
          | token pos tk =>
              -- one buffered token: flush it, then dispatch on the outcome
              rw [h_charp] at h
              dsimp only [] at h
              cases h_e : (flushPendingToken
                  { db := st.parser.db, tokp := st.parser.tokp,
                    charp := CharParser.token pos tk, line := st.parser.line,
                    linepos := st.parser.linepos,
                    sourceFile := frame.fname }).db.error? with
              | some intr =>
                  obtain ⟨err, consumed⟩ := intr
                  rw [h_e] at h
                  dsimp only [] at h
                  cases h_req : parserIncludeRequestOfError? err with
                  | some req =>
                      cases req with
                      | pushFile src inc =>
                          rw [h_req] at h
                          exact absurd h (by simp)
                  | none =>
                      -- flush errored without an include request: the loop
                      -- guard excludes this from recursing
                      rw [h_req] at h
                      injection h with h
                      subst h
                      rw [DB.error, h_e] at h_err
                      simp at h_err
              | none =>
                  -- flush succeeded: boundary check, pop
                  rw [h_e] at h
                  dsimp only [] at h
                  injection h with h
                  subst h
                  simp only [IncludeDriverState.measure, h_stack, List.map_cons,
                    List.sum_cons, List.length_cons]
                  omega
        · -- live frame: feed the remaining chunk
          rw [if_neg h_exh] at h
          cases h_e : (ParserState.feedAll
              { db := st.parser.db, tokp := st.parser.tokp,
                charp := st.parser.charp, line := st.parser.line,
                linepos := st.parser.linepos, sourceFile := frame.fname }
              st.base
              (frame.contents.extract frame.offset frame.contents.size)).db.error? with
          | some intr =>
              obtain ⟨err, consumed⟩ := intr
              rw [h_e] at h
              dsimp only [] at h
              cases h_req : parserIncludeRequestOfError? err with
              | some req =>
                  cases req with
                  | pushFile src inc =>
                      rw [h_req] at h
                      exact absurd h (by simp)
              | none =>
                  -- chunk errored without an include request: the loop guard
                  -- excludes this from recursing
                  rw [h_req] at h
                  injection h with h
                  subst h
                  rw [DB.error, h_e] at h_err
                  simp at h_err
          | none =>
              -- full chunk consumed: offset advances to the end
              rw [h_e] at h
              dsimp only [] at h
              injection h with h
              subst h
              have h_lt : frame.offset < frame.contents.size := by omega
              have h_sep_f : frame.needsSep = false := by
                cases h_ns : frame.needsSep with
                | false => rfl
                | true => exact absurd h_ns h_sep
              simp only [IncludeDriverState.measure, IncludeDriverFrame.measure,
                h_stack, List.map_cons, List.sum_cons, List.length_cons, h_sep_f,
                Bool.false_eq_true, reduceIte]
              omega

/-- Run pure `stepFrame` steps until the pass finishes, a parser error stops
it, or an include push needs the IO layer.  Total: every looping step strictly
decreases `IncludeDriverState.measure`. -/
def runPureSteps (st : IncludeDriverState) : DriverPhase :=
  match _h : stepFrame st with
  | .done st' => .done st'
  | .push sourceFile includePath nextDepth st' =>
      .push sourceFile includePath nextDepth st'
  | .fed st' =>
      if _h_err : st'.parser.db.error then .stopped st'
      else runPureSteps st'
termination_by st.measure
decreasing_by exact stepFrame_fed_measure_lt st st' _h (by simpa using _h_err)

/-- Resolve one include push: locate the child relative to its requesting file,
prepare its frame under the depth/cycle/duplicate gate, and splice it onto the
stack.  This is the only IO the driver loop performs. -/
def resolvePushWithIO
    (realPath : String → IO System.FilePath)
    (readFile : String → IO ByteArray)
    (sourceFile includePath : String) (nextDepth : Nat)
    (st : IncludeDriverState) :
    IO (Except IncludeError IncludeDriverState) := do
  -- Mirror modes look the include string up literally from the invocation
  -- directory, exactly as the references do; spec-faithful modes resolve
  -- relative to the including file.
  let fullPath := includeLookupPath st.parser.db.config.literalIncludePaths
    sourceFile includePath
  try
    match ← prepareIncludeFrameWithIO realPath readFile fullPath.toString nextDepth
        st.parser.db.scopes.size st.parser.db.config.rejectIncludeCycles
        st.parser.db.config.literalIncludePaths
        st.processing st.seen with
    | .error incErr =>
        return .error incErr
    | .ok (none, processing', seen') =>
        return .ok { st with processing := processing', seen := seen' }
    | .ok (some childFrame, processing', seen') =>
        -- A child file starts its own per-file line numbering at line 0; the
        -- parent's state is parked on the parent frame and restored when this
        -- child is popped.
        let childParser := { st.parser with line := 0, linepos := st.base }
        return .ok { st with processing := processing', seen := seen',
                             parser := childParser,
                             stack := childFrame :: st.stack }
  catch e =>
    return .error (.readFailure includePath fullPath.toString e.toString)

/-- The include-driver loop: alternate pure phases (`runPureSteps`) with
include resolutions (`resolvePushWithIO`).  `fuel` bounds only the number of
include resolutions — pure work is fuel-free and terminates by the measure —
and comes from `ModeConfig.maxIncludeResolutions`.  Exhausting it is a loud
`IncludeError`, never a silent truncation. -/
def runDriverLoop
    (realPath : String → IO System.FilePath)
    (readFile : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) :
    IO (Except IncludeError IncludeDriverState) :=
  match runPureSteps st with
  | .done st' => return .ok st'
  | .stopped st' => return .ok st'
  | .push sourceFile includePath nextDepth st' =>
      match fuel with
      | 0 => return .error (.budgetExhausted includePath)
      | fuel' + 1 => do
          match ← resolvePushWithIO realPath readFile
              sourceFile includePath nextDepth st' with
          | .error incErr => return .error incErr
          | .ok st'' => runDriverLoop realPath readFile fuel' st''

/-- Single-pass include-aware parser driver parameterized by filesystem hooks.
Reads each file once, scans `$[ ... $]` directives on the fly, and streams non-include
bytes directly into `ParserState.feedAll`. Recursive include traversal is bounded by
`depth` (from `ModeConfig.maxIncludeDepth`). -/
def processFileSinglePassWithIO
    (realPath : String → IO System.FilePath)
    (readFile : String → IO ByteArray)
    (fname : String) (config : ModeConfig) (depth : Nat)
    (st0 : IncludeDriverState) :
    IO (Except IncludeError IncludeDriverState) := do
  match ← prepareIncludeFrameWithIO realPath readFile fname depth
      st0.parser.db.scopes.size config.rejectIncludeCycles
      config.literalIncludePaths
      st0.processing st0.seen with
  | .error err =>
      return .error err
  | .ok (none, _, seen) =>
      return .ok { st0 with seen := seen }
  | .ok (some rootFrame, processing, seen) =>
      -- The loop is the proof-friendly recursion itself: pure `stepFrame`
      -- phases with IO only at include resolutions.
      -- `finalizeSinglePassResult` stays the sole owner of EOF finality: the
      -- loop returns the streaming state without evaluating a pending final
      -- token twice.
      runDriverLoop realPath readFile config.maxIncludeResolutions
        { st0 with processing := processing, seen := seen, stack := [rootFrame] }

/-- Default single-pass include-aware parser driver using filesystem reads. -/
def processFileSinglePass (fname : String) (processing seen : HashSet String)
    (config : ModeConfig) (depth : Nat)
    (s0 : ParserState) (base0 : Nat) :
    IO (Except IncludeError (ParserState × Nat × HashSet String)) :=
  do
    let st0 : IncludeDriverState := {
      parser := s0
      base := base0
      processing := processing
      seen := seen
      stack := []
    }
    match (← processFileSinglePassWithIO
      (fun path => IO.FS.realPath path)
      (fun path => IO.FS.readBinFile path)
      fname config depth st0) with
    | .error err => return .error err
    | .ok st => return .ok (st.parser, st.base, st.seen)

/-- Pure post-processing for single-pass include results. -/
def finalizeSinglePassResult (config : ModeConfig)
    (result : Except IncludeError (ParserState × Nat × HashSet String)) : DB :=
  match result with
  | .error err =>
      includePreprocessErrorDB config err
  | .ok (s, base, _) =>
      let db := s.done base
      if db.error? = none then
        if (db.config.allowDuplicateFloat || db.wellFormed?) && db.assertDvVarsInFrame? then
          db
        else
          db.mkErrorFromEvidence ⟨0, 0⟩
            (.internalGate db.config.allowDuplicateFloat db.wellFormed? db.assertDvVarsInFrame?)
      else
        db

/-- Canonical initial DB used by single-pass IO entrypoints. -/
@[inline] def singlePassInitialDB (config : ModeConfig) : DB :=
  { (default : DB) with config := config }

/-- Canonical initial parser state used by single-pass IO entrypoints. -/
@[inline] def singlePassInitialState (config : ModeConfig) : ParserState :=
  { (default : ParserState) with db := singlePassInitialDB config }

/-- Canonical initial single-pass include-processing invocation. -/
@[inline] def singlePassInitialResult (fname : String) (config : ModeConfig) :
    IO (Except IncludeError (ParserState × Nat × HashSet String)) :=
  processFileSinglePass
    fname
    (HashSet.emptyWithCapacity 16)
    (HashSet.emptyWithCapacity 16)
    config
    config.maxIncludeDepth
    (singlePassInitialState config)
    0

/-- IO entrypoint using single-pass include scanning + parser streaming.
This keeps include recursion bounded and avoids materializing a fully expanded
byte array before parsing. -/
def checkSinglePass (fname : String) (config : ModeConfig := {}) : IO DB := do
  let result ← singlePassInitialResult fname config
  return finalizeSinglePassResult config result

/-- Default IO entrypoint (single-pass include handling). -/
def check (fname : String) (config : ModeConfig := {}) : IO DB :=
  checkSinglePass fname config

/-! ## Include child-file boundary: preservation theorems

The runtime boundary check of [MM §4.1.2] is gated here so it cannot be weakened
silently.  `stepFrame`'s two exhausted-frame branches both route through
`popExhaustedFrame`; the theorems below pin what that operation does. -/

namespace ParserState

/-- Boundary success under `.ws` is exactly "between statements, at entry depth". -/
theorem childFileBoundaryError?_none_iff (d : Nat) (s : ParserState)
    (h_ws : s.charp = .ws) :
    childFileBoundaryError? d s = none
      ↔ (s.tokp = .start ∧ s.db.scopes.size = d) := by
  unfold childFileBoundaryError?
  rw [h_ws]
  cases h_tokp : s.tokp <;>
    simp_all [h_tokp] <;>
    split <;> simp_all

/-- Every unfinished token-parser mode is rejected: only `.start` can pass. -/
theorem childFileBoundaryError?_isSome_of_ne_start (d : Nat) (s : ParserState)
    (h_ws : s.charp = .ws) (h_ne : s.tokp ≠ .start) :
    (childFileBoundaryError? d s).isSome = true := by
  unfold childFileBoundaryError?
  rw [h_ws]
  cases h_tokp : s.tokp <;> simp_all [h_tokp] <;> split <;> simp

/-- A buffered token is never a legal child boundary; callers must flush first. -/
theorem childFileBoundaryError?_isSome_of_token (d : Nat) (s : ParserState)
    (pos : Nat) (tk : ByteArray) (h : s.charp = .token pos tk) :
    (childFileBoundaryError? d s).isSome = true := by
  unfold childFileBoundaryError?
  rw [h]
  rfl

/-- Root pop is the identity: `done` remains the sole owner of end-of-input. -/
@[simp] theorem popExhaustedFrame_root (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) :
    popExhaustedFrame s base frame [] = s := rfl

/-- A fully splicing profile bypasses the boundary entirely. -/
theorem popExhaustedFrame_spliceAll (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (f : IncludeDriverFrame)
    (rest : List IncludeDriverFrame)
    (h : s.db.config.childFileBoundary = .spliceAll) :
    popExhaustedFrame s base frame (f :: rest) = restoreLineState s base (f :: rest) := by
  unfold popExhaustedFrame
  simp [h]

/-- The `metamath.exe` boundary policy permits statement splicing but rejects
an unterminated child comment before returning to the parent. -/
theorem popExhaustedFrame_spliceExceptComments_rejects_comment
    (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (f : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) (resume : TokenParser)
    (h_policy : s.db.config.childFileBoundary = .spliceExceptComments)
    (h_charp : s.charp = .ws) (h_tokp : s.tokp = .comment resume) :
    (popExhaustedFrame s base frame (f :: rest)).db.error? =
      ({ s with sourceFile := frame.fname }.withDB fun db =>
        db.mkErrorFromEvidence (s.mkPos base) (.doneMode .unclosedComment)).db.error? := by
  unfold popExhaustedFrame
  simp [h_policy, h_charp, h_tokp]

/-- A strict child pop that raises no error leaves the parser between statements
at the depth the child was entered at — the parent resumes exactly where it was. -/
theorem popExhaustedFrame_child_success (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (f : IncludeDriverFrame)
    (rest : List IncludeDriverFrame)
    (h_strict : s.db.config.childFileBoundary = .strict)
    (h_ws : s.charp = .ws)
    (h_no_err : (popExhaustedFrame s base frame (f :: rest)).db.error? = none) :
    s.tokp = .start ∧ s.db.scopes.size = frame.entryScopeDepth := by
  rw [← childFileBoundaryError?_none_iff frame.entryScopeDepth s h_ws]
  cases h_b : childFileBoundaryError? frame.entryScopeDepth s with
  | none => rfl
  | some ev =>
      exfalso
      rw [show popExhaustedFrame s base frame (f :: rest)
            = ({ s with sourceFile := frame.fname }).withDB
                (fun db => db.mkErrorFromEvidence (s.mkPos base) ev) from by
          unfold popExhaustedFrame; simp [h_strict, h_b]] at h_no_err
      simp [ParserState.withDB, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.mkError] at h_no_err

/-- A strict child that is not between statements at entry depth cannot pop
cleanly: the boundary error is raised. -/
theorem popExhaustedFrame_child_rejects (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (f : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) (ev : ErrorEvidence)
    (h_strict : s.db.config.childFileBoundary = .strict)
    (h_bad : childFileBoundaryError? frame.entryScopeDepth s = some ev) :
    (popExhaustedFrame s base frame (f :: rest)).db.error?
      = ({ s with sourceFile := frame.fname }.withDB
          fun db => db.mkErrorFromEvidence (s.mkPos base) ev).db.error? := by
  unfold popExhaustedFrame
  simp [h_strict, h_bad]

end ParserState

/-! ### `stepFrame` call-site gates

The two theorems below have `stepFrame st` on the left, so they bind the runtime
to `popExhaustedFrame` at both exhausted-frame branches.  If either branch stops
calling the shared helper — or reconstructs the popped state by hand — these stop
being true and the build fails. -/

/-- Exhausted frame, no separator pending, nothing buffered: `stepFrame` pops
through `popExhaustedFrame` and yields exactly this driver state. -/
theorem stepFrame_exhausted_ws
    (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame)
    (h_stack : st.stack = frame :: rest)
    (h_sep : frame.needsSep = false)
    (h_exhausted : frame.offset ≥ frame.contents.size)
    (h_ws : st.parser.charp = .ws) :
    stepFrame st =
      .fed { st with parser := popExhaustedFrame st.parser st.base frame rest,
                     processing := st.processing.erase frame.canonStr,
                     stack := rest } := by
  unfold stepFrame
  rw [h_stack]
  simp [h_sep, h_exhausted, h_ws]

/-- Exhausted frame with a final buffered token: `stepFrame` flushes that token,
and when the flush raises no error it pops through the same `popExhaustedFrame`
applied to the *flushed* parser. -/
theorem stepFrame_exhausted_flushed
    (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) (pos : Nat) (tk : ByteArray)
    (h_stack : st.stack = frame :: rest)
    (h_sep : frame.needsSep = false)
    (h_exhausted : frame.offset ≥ frame.contents.size)
    (h_tok : st.parser.charp = .token pos tk)
    (h_flush_ok :
      (flushPendingToken
        { st.parser with charp := .token pos tk, sourceFile := frame.fname }).db.error?
        = none) :
    stepFrame st =
      .fed { st with
              parser := popExhaustedFrame
                (flushPendingToken
                  { st.parser with charp := .token pos tk, sourceFile := frame.fname })
                st.base frame rest,
              processing := st.processing.erase frame.canonStr,
              stack := rest } := by
  unfold stepFrame
  rw [h_stack]
  simp [h_sep, h_exhausted, h_tok, h_flush_ok]

end Verify
end Metamath
