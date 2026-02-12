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

namespace Array

/-- Total index equals partial index when in-bounds (Nat version). -/
@[simp] theorem getBang_eq_get_nat (a : Array α) (i : Nat) (h : i < a.size) [Inhabited α] :
  a[i]! = a[i]'h := by
  simp only [getElem!_pos, h]

/-- (A) Length bridge: arrays and their lists have the same length. -/
@[simp] theorem toList_length (a : Array α) : a.toList.length = a.size := by
  rfl

/-- (B) Characterize `get? = some` without `Inhabited`: unfold `get?`. -/
@[simp] theorem get?_eq_some_iff {a : Array α} {i : Nat} {x : α} :
    a[i]? = some x ↔ ∃ h : i < a.size, a[i]'h = x := by
  simp only [getElem?_def]
  by_cases h : i < a.size
  · -- in-bounds branch
    simp [h]
  · -- out-of-bounds branch
    simp [h]

/-- (C) Bridge `Array.get!` to `List.get!` under a bound. -/
@[simp] theorem get!_toList' {α} [Inhabited α]
    (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a.toList[i]! := by
  simp [getElem_toList, h]

end Array

def UInt8.toChar (n : UInt8) : Char := ⟨n.toUInt32, by
  have := n.toFin.2
  simp [size, UInt32.isValidChar, Nat.isValidChar] at *; omega⟩

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

open IO.FS (Handle)
open Std (HashMap HashSet)

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
  deriving DecidableEq, Repr, Inhabited

namespace ModeConfig

/-- Zar mode: Strict spec compliance (138/138 tests) -/
def zar : ModeConfig := {}

/-- Knife mode: Stricter - rejects incomplete proofs, top-level $e -/
def knife : ModeConfig := {
  rejectUnknownSteps := true
  rejectToplevelEss := true
}

/-- Exe mode: More permissive - matches metamath.exe behavior exactly (132/138)
    NOTE: allowConstInnerScope = false because metamath.exe rejects direct $c in inner scope -/
def exe : ModeConfig := {
  allowDuplicateFloat := true
  allowIncludeInnerScope := true
  allowTokenSplicing := true
}

/-- Fully permissive: Accept everything syntactically valid (EBNF minimal spec) -/
def permissive : ModeConfig := {
  allowDuplicateFloat := true
  allowConstInnerScope := true
  allowIncludeInnerScope := true
  allowTokenSplicing := true
}

end ModeConfig

/-- Legacy enum for CLI convenience -/
inductive VerifierMode where
  | zar
  | knife
  | exe
  | permissive
  deriving DecidableEq, Repr, Inhabited

namespace VerifierMode

def toConfig : VerifierMode → ModeConfig
  | .zar => ModeConfig.zar
  | .knife => ModeConfig.knife
  | .exe => ModeConfig.exe
  | .permissive => ModeConfig.permissive

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

@[simp] theorem isSpecWhitespace_formFeed : isSpecWhitespace (0x0c : UInt8) = true := by
  simp [isSpecWhitespace]

/-- Parser tokenization whitespace now matches the Metamath spec set (§4.1.1). -/
theorem checkBytes_tokenization_whitespace_matches_spec (c : UInt8) :
    isWhitespace c = isSpecWhitespace c := by
  rfl

def isPrintable (c : UInt8) : Bool := c >= 32 && c <= 126

def isMathChar (c : UInt8) : Bool := c ≠ '$'.toUInt8 && isPrintable c

def toLabel (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
    unless isLabelChar c do ok := false
  (ok, s)

def toMath (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
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
  | tokenNotInScope
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
  | sec4_4_5_compressedProof
  | sec4_4_6_unknownProof
  | impl_internalConsistency
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
  | .tokenNotInScope => "symbol '<sym>' not in scope"
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

/-- Codes that are permitted to be emitted with `codeOnly` evidence. -/
def codeOnlyAllowed : ParseErrorCode → Bool
  | .unclosedBlock => true
  | .unclosedComment => true
  | .unclosedConst => true
  | .unclosedVar => true
  | .unclosedDjvars => true
  | .unclosedFloat => true
  | .unclosedEss => true
  | .unclosedAx => true
  | .unclosedThm => true
  | .unclosedProof => true
  | _ => false

theorem codeOnlyAllowed_cases (code : ParseErrorCode) :
    ParseErrorCode.codeOnlyAllowed code = true →
    code = .unclosedBlock ∨ code = .unclosedComment ∨ code = .unclosedConst ∨
    code = .unclosedVar ∨ code = .unclosedDjvars ∨ code = .unclosedFloat ∨
    code = .unclosedEss ∨ code = .unclosedAx ∨ code = .unclosedThm ∨
    code = .unclosedProof := by
  cases code <;> simp [ParseErrorCode.codeOnlyAllowed]

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
  | .typeErrorInSubstitution => .sec4_3_proofVerification
  | .badTypecodeInSubstitution => .sec4_3_proofVerification
  | .duplicateFloatVariable => .sec4_2_5_f_e_hypotheses
  | .disjointVariableViolation => .sec4_2_4_djvars
  | .assertionNoConstantHead => .sec4_2_6_assertions
  | .assertionVarsNotInFrame => .sec4_2_7_frames
  | .stackUnderflow => .sec4_3_proofVerification
  | .proofBackrefIndexOutOfRange => .sec4_4_5_compressedProof
  | .invalidLabel => .sec4_2_1_labels
  | .invalidMathString => .sec4_1_1_whitespace
  | .duplicateDisjointVariable => .sec4_2_4_djvars
  | .tokenNotInScope => .sec4_2_4_djvars
  | .tokenNotVariable => .sec4_2_4_djvars
  | .unknownStepQuestionRejected => .sec4_4_6_unknownProof
  | .topLevelEssentialNotAllowed => .sec4_2_8_scoping
  | .proofParseError => .sec4_3_proofVerification
  | .theoremMoreThanOneStackElement => .sec4_3_proofVerification
  | .theoremClaimMismatch => .sec4_3_proofVerification
  | .nestedCommentDelimiter => .sec4_1_2_comments
  | .tokenNotConstantOrVariable => .sec4_2_2_constantsVariables
  | .unknownStatementType => .sec4_1_3_basicSyntax
  | .internalIllFormedDatabaseAfterParse => .impl_internalConsistency
  | .includeCycleDetected => .sec4_1_2_includes
  | .includeInInnerScope => .sec4_1_2_includes
  | .includeInsideStatement => .sec4_1_2_includes
  | .includeExtractedEmptyPath => .sec4_1_2_includes
  | .includeEmptyPathBeforeNormalization => .sec4_1_2_includes
  | .includePathEmptyAfterNormalization => .sec4_1_2_includes
  | .includeReadFailure => .sec4_1_2_includes
  | .hypothesisNotInDatabaseScope => .sec4_2_8_scoping
  | .statementNotFound => .sec4_3_proofVerification
  | .mandatoryHypothesisNotFoundInDatabase => .sec4_2_7_frames
  | .hypothesisNotFound => .sec4_3_proofVerification
  | .outOfOrderHypothesesInFrame => .sec4_2_7_frames

/-- Option-valued compatibility wrapper (kept for existing callsites/tests). -/
def specClause? (code : ParseErrorCode) : Option SpecClause :=
  some (specClause code)

@[simp] theorem specClause?_unclosedDjvars :
    specClause? .unclosedDjvars = some .sec4_2_4_djvars := rfl

end ParseErrorCode



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
  | tokenNotInScope (sym : String)
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
  | .tokenNotInScope _ => .tokenNotInScope
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
  | .tokenNotInScope sym => "symbol '" ++ sym ++ "' not in scope"
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
  | inInnerScope (pos : Nat) (scopeDepth : Nat)
  | insideStatement (pos : Nat)
  | extractedEmptyPath (startPos endPos file : String)
  | emptyPathBeforeNormalization (file : String)
  | pathEmptyAfterNormalization (origPath file : String)
  | readFailure (name path err : String)
  deriving DecidableEq, Repr, Inhabited

namespace IncludeError

def code : IncludeError → ParseErrorCode
  | .cycleDetected _ => .includeCycleDetected
  | .inInnerScope _ _ => .includeInInnerScope
  | .insideStatement _ => .includeInsideStatement
  | .extractedEmptyPath _ _ _ => .includeExtractedEmptyPath
  | .emptyPathBeforeNormalization _ => .includeEmptyPathBeforeNormalization
  | .pathEmptyAfterNormalization _ _ => .includePathEmptyAfterNormalization
  | .readFailure _ _ _ => .includeReadFailure

def message : IncludeError → String
  | .cycleDetected path =>
      "include cycle detected: '" ++ path ++ "' is already being processed"
  | .inInnerScope _ _ =>
      "include in inner scope (config requires outermost scope only, spec §4.1.2)"
  | .insideStatement _ =>
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

structure Interrupt where
  e : Error
  idx : Nat

/-- Structured evidence for parser errors (used for semantic inversion). -/
inductive ErrorEvidence where
  | codeOnly (code : ParseErrorCode)
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
  | codeOnly code => code
  | tokenForm err => TokenFormError.code err
  | scopeDecl err => ScopeDeclError.code err
  | .includeErr err => IncludeError.code err
  | proofCheck err => ProofCheckError.code err
  | theoremFinality err => TheoremFinalityError.code err
  | compressedSave err => CompressedSaveError.code err
  | internalGate _ _ _ => .internalIllFormedDatabaseAfterParse

def message : ErrorEvidence → String
  | codeOnly code => ParseErrorCode.message code
  | tokenForm err => TokenFormError.message err
  | scopeDecl err => ScopeDeclError.message err
  | .includeErr err => IncludeError.message err
  | proofCheck err => ProofCheckError.message err
  | theoremFinality err => TheoremFinalityError.message err
  | compressedSave err => CompressedSaveError.message err
  | internalGate _ _ _ => ParseErrorCode.message .internalIllFormedDatabaseAfterParse

def allowed : ErrorEvidence → Prop
  | codeOnly code => ParseErrorCode.codeOnlyAllowed code = true
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
  objects : HashMap String Object
  interrupt : Bool
  error? : Option Interrupt
  errorEvidence? : Option ErrorEvidence := none
  config : ModeConfig := {}
  deriving Inhabited

namespace DB

@[inline] def error (s : DB) : Bool := s.error?.isSome

/-- Default config is zar (all defaults) -/
@[simp] theorem default_config : (default : DB).config = {} := rfl

def mkError (s : DB) (pos : Pos) (msg : String) : DB :=
  { s with error? := some ⟨.error pos msg, default⟩, errorEvidence? := none }

/-- Error constructor that records structured evidence alongside the message. -/
def mkErrorWithEvidence (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) : DB :=
  { s with error? := some ⟨.error pos msg, default⟩, errorEvidence? := some ev }

/-- Error constructor that derives the message from evidence. -/
def mkErrorFromEvidence (s : DB) (pos : Pos) (ev : ErrorEvidence) : DB :=
  s.mkErrorWithEvidence pos (ErrorEvidence.message ev) ev

/-- Parser-specific error constructor with stable code-to-message mapping. -/
def mkParseError (s : DB) (pos : Pos) (code : ParseErrorCode) : DB :=
  s.mkErrorFromEvidence pos (.codeOnly code)

@[simp] theorem mkError_config (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).config = s.config := rfl

@[simp] theorem mkError_error (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).error = true := rfl

@[simp] theorem mkError_error?_isSome (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).error?.isSome = true := rfl

@[simp] theorem mkParseError_config (s : DB) (pos : Pos) (code : ParseErrorCode) :
    (s.mkParseError pos code).config = s.config := by
  simp [mkParseError, mkErrorFromEvidence, mkErrorWithEvidence]

@[simp] theorem mkParseError_error?_isSome (s : DB) (pos : Pos) (code : ParseErrorCode) :
    (s.mkParseError pos code).error?.isSome = true := by
  simp [mkParseError, mkErrorFromEvidence, mkErrorWithEvidence]

@[simp] theorem mkErrorWithEvidence_config (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).config = s.config := rfl

@[simp] theorem mkErrorWithEvidence_error?_isSome (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).error?.isSome = true := rfl

@[simp] theorem mkErrorWithEvidence_error (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).error = true := by
  rfl

@[simp] theorem mkErrorWithEvidence_frame (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).frame = s.frame := rfl

@[simp] theorem mkErrorWithEvidence_scopes (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).scopes = s.scopes := rfl

@[simp] theorem mkErrorWithEvidence_objects (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).objects = s.objects := rfl

@[simp] theorem mkErrorWithEvidence_interrupt (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).interrupt = s.interrupt := rfl

@[simp] theorem mkErrorWithEvidence_error? (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).error? ≠ none := by
  simp [mkErrorWithEvidence]

@[simp] theorem mkErrorFromEvidence_frame (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).frame = s.frame := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_scopes (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).scopes = s.scopes := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_objects (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).objects = s.objects := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_interrupt (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).interrupt = s.interrupt := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_error? (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).error? ≠ none := by
  simp [mkErrorFromEvidence, mkErrorWithEvidence]


@[simp] theorem mkErrorFromEvidence_config (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).config = s.config := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_error?_isSome (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).error?.isSome = true := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_error (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).error = true := by
  simp [mkErrorFromEvidence, DB.error, mkErrorWithEvidence]

@[simp] theorem mkParseError_errorEvidence? (s : DB) (pos : Pos) (code : ParseErrorCode) :
    (s.mkParseError pos code).errorEvidence? = some (.codeOnly code) := by
  simp [mkParseError, mkErrorFromEvidence, mkErrorWithEvidence]

/-- Decode parser error code (when present) from the DB interrupt payload. -/
def parseErrorCode? (s : DB) : Option ParseErrorCode :=
  match s.error? with
  | some ⟨.error _ _, _⟩ =>
      match s.errorEvidence? with
      | some (.codeOnly code) =>
          if ParseErrorCode.codeOnlyAllowed code then some code else none
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

/-- Concrete parser violation for out-of-scope `$d` symbol use. -/
def TokenNotInScopeViolation (s : DB) : Prop :=
  s.ScopeDeclViolation .tokenNotInScope

/-- Metamath book §4.2.1 predicate for label-token syntax violations. -/
def Sec4_2_1_LabelSyntaxViolation (s : DB) : Prop :=
  s.InvalidLabelViolation

/-- Metamath book §4.2.4 predicate for duplicate `$d` variable entries. -/
def Sec4_2_4_DjvarsDuplicateViolation (s : DB) : Prop :=
  s.DuplicateDisjointVariableViolation

/-- Metamath book §4.2.4 predicate for `$d` variable scope violations. -/
def Sec4_2_4_DjvarsScopeViolation (s : DB) : Prop :=
  s.TokenNotInScopeViolation

/-- Code-indexed bundle for high-value parser-error shape evidence. -/
def HighValueShapeViolation (s : DB) (code : ParseErrorCode) : Prop :=
  match code with
  | .invalidLabel => s.InvalidLabelViolation
  | .duplicateDisjointVariable => s.DuplicateDisjointVariableViolation
  | .tokenNotInScope => s.TokenNotInScopeViolation
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
  | .tokenNotInScope => s.TokenNotInScopeViolation
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
  | .internalIllFormedDatabaseAfterParse => s.InternalConsistencyViolation

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

/-- Parser-level soundness: every decoded parse error code has a concrete error witness. -/

theorem parseErrorCode?_sound (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code → s.ParserSpecViolation code := by
  intro h_code
  unfold DB.parseErrorCode? at h_code
  cases h_err : s.error? with
  | none =>
      simp [h_err] at h_code
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e with
          | error pos msg =>
              cases h_ev : s.errorEvidence? with
              | none =>
                  simp [h_err, h_ev] at h_code
              | some ev =>
                  cases ev with
                  | codeOnly code' =>
                      -- parseErrorCode? only returns for allowed code-only entries
                      have h_code' : code' = code := by
                        cases h_allowed : ParseErrorCode.codeOnlyAllowed code' with
                        | false =>
                            have : (none : Option ParseErrorCode) = some code := by
                              simpa [h_err, h_ev, h_allowed] using h_code
                            cases this
                        | true =>
                            simpa [h_err, h_ev, h_allowed] using h_code
                      refine ⟨pos, msg, idx, .codeOnly code', ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [ErrorEvidence.code] using h_code'
                  | tokenForm err =>
                      refine ⟨pos, msg, idx, .tokenForm err, ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | scopeDecl err =>
                      refine ⟨pos, msg, idx, .scopeDecl err, ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | includeErr err =>
                      refine ⟨pos, msg, idx, .includeErr err, ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | proofCheck err =>
                      refine ⟨pos, msg, idx, .proofCheck err, ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | theoremFinality err =>
                      refine ⟨pos, msg, idx, .theoremFinality err, ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | compressedSave err =>
                      refine ⟨pos, msg, idx, .compressedSave err, ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | internalGate allowDup wf dv =>
                      refine ⟨pos, msg, idx, .internalGate allowDup wf dv, ?_, ?_, ?_⟩
                      · simpa [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
          | ax pos l f fr =>
              simp [h_err] at h_code
          | thm pos l f fr =>
              simp [h_err] at h_code


/-- Parser-level clause soundness from decoded code + code-to-clause map. -/
theorem parseErrorCode?_clause_sound
    (s : DB) (code : ParseErrorCode) (clause : SpecClause) :
    s.parseErrorCode? = some code →
    ParseErrorCode.specClause code = clause →
    s.ParserSpecClauseViolation clause := by
  intro h_code h_clause
  exact ⟨code, h_code, h_clause⟩

/-- Parser-level clause soundness with the canonical clause chosen by the code. -/
theorem parseErrorCode?_specClause_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact ⟨code, h_code, rfl⟩

/-- All-code evidence soundness:
decoded parser code carries a concrete evidence witness for that code. -/
theorem parseErrorCode?_allCodePayloadShape_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.AllCodePayloadShapeViolation code := by
  intro h_code
  obtain ⟨pos, msg, idx, ev, h_err, h_ev, h_code'⟩ := parseErrorCode?_sound s code h_code
  have h_code_ev : s.parseErrorCode? = some ev.code := by
    simpa [h_code'] using h_code
  have h_allowed : ErrorEvidence.allowed ev := by
    cases ev with
    | codeOnly code' =>
        -- `parseErrorCode?` only returns code-only entries when the code is allowed.
        unfold DB.parseErrorCode? at h_code_ev
        simp [h_err, h_ev] at h_code_ev
        -- h_code_ev : (if codeOnlyAllowed code' then some code' else none) = some code'
        cases h : ParseErrorCode.codeOnlyAllowed code' with
        | false =>
            have : (none : Option ParseErrorCode) = some code' := by
              simpa [h] using h_code_ev
            cases this
        | true =>
            simpa [ErrorEvidence.allowed] using h
    | tokenForm _ => simp [ErrorEvidence.allowed]
    | scopeDecl _ => simp [ErrorEvidence.allowed]
    | includeErr _ => simp [ErrorEvidence.allowed]
    | proofCheck _ => simp [ErrorEvidence.allowed]
    | theoremFinality _ => simp [ErrorEvidence.allowed]
    | compressedSave _ => simp [ErrorEvidence.allowed]
    | internalGate _ _ _ => simp [ErrorEvidence.allowed]
  exact ⟨pos, msg, idx, ev, h_err, h_ev, h_code', h_allowed⟩

/-- Clause witness derivable directly from all-code payload-shape witness. -/
theorem allCodePayloadShape_implies_specClauseViolation
    (s : DB) (code : ParseErrorCode) :
    s.AllCodePayloadShapeViolation code →
    s.ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_shape
  rcases h_shape with ⟨pos, msg, idx, ev, h_err, h_ev, h_code, h_allowed⟩
  refine ⟨code, ?_, rfl⟩
  unfold DB.parseErrorCode?
  cases ev with
  | codeOnly code' =>
      have h_allowed' : ParseErrorCode.codeOnlyAllowed code' = true := by
        simpa [ErrorEvidence.allowed] using h_allowed
      have h_code' : code' = code := by
        simpa [ErrorEvidence.code] using h_code
      clear h_code
      subst code
      simp [h_err, h_ev, h_allowed']
  | tokenForm _ => simp [h_err, h_ev, h_code, h_allowed]
  | scopeDecl _ => simp [h_err, h_ev, h_code, h_allowed]
  | includeErr _ => simp [h_err, h_ev, h_code, h_allowed]
  | proofCheck _ => simp [h_err, h_ev, h_code, h_allowed]
  | theoremFinality _ => simp [h_err, h_ev, h_code, h_allowed]
  | compressedSave _ => simp [h_err, h_ev, h_code, h_allowed]
  | internalGate _ _ _ => simp [h_err, h_ev, h_code, h_allowed]

/-- All-code semantic soundness:
decoded parser code carries a semantic witness for that code. -/
theorem parseErrorCode?_allCodeSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.AllCodeSemanticViolation code := by
  intro h_code
  -- Under code-first evidence, semantic soundness is the same as evidence soundness.
  exact parseErrorCode?_allCodePayloadShape_sound s code h_code

/-- Lift any code-indexed semantic witness to the corresponding clause-indexed one. -/
theorem allCodeSemantic_implies_clauseSemantic
    (s : DB) (code : ParseErrorCode) :
    s.AllCodeSemanticViolation code →
    s.AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) := by
  intro h_sem
  exact ⟨code, rfl, h_sem⟩

/-- Clause-indexed semantic soundness for any decoded parser code. -/
theorem parseErrorCode?_allCodeClauseSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact allCodeSemantic_implies_clauseSemantic s code
    (parseErrorCode?_allCodeSemantic_sound s code h_code)

/-- Concrete parser-spec predicate:
decoded-code clause witness paired with all-code payload-shape evidence. -/
def ConcreteSpecPredicate (s : DB) (code : ParseErrorCode) : Prop :=
  s.ParserSpecClauseViolation (ParseErrorCode.specClause code) ∧
    s.AllCodePayloadShapeViolation code

/-- Canonical all-code semantic clause predicate:
decoded-code clause witness paired with semantic payload-shape evidence. -/
def ConcreteSemanticClausePredicate (s : DB) (code : ParseErrorCode) : Prop :=
  s.AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) ∧
    s.AllCodeSemanticViolation code

/-- Canonical all-code packaging theorem from decoded parser code
to concrete spec predicate (clause + payload-shape). -/
theorem parseErrorCode?_concrete_spec_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ConcreteSpecPredicate code := by
  intro h_code
  have h_shape : s.AllCodePayloadShapeViolation code :=
    parseErrorCode?_allCodePayloadShape_sound s code h_code
  exact ⟨allCodePayloadShape_implies_specClauseViolation s code h_shape, h_shape⟩

/-- Canonical all-code semantic packaging theorem from decoded parser code
to semantic clause predicate (clause + semantic payload-shape). -/
theorem parseErrorCode?_concrete_semantic_clause_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ConcreteSemanticClausePredicate code := by
  intro h_code
  have h_sem : s.AllCodeSemanticViolation code :=
    parseErrorCode?_allCodeSemantic_sound s code h_code
  exact ⟨allCodeSemantic_implies_clauseSemantic s code h_sem, h_sem⟩


/-- Canonical parser rule-semantic soundness for any decoded code. -/
theorem parseErrorCode?_ruleSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.RuleSemanticViolation code := by
  intro h_code
  obtain ⟨pos, msg, idx, ev, h_err, h_ev, h_code'⟩ := parseErrorCode?_sound s code h_code
  have h_code_ev : s.parseErrorCode? = some ev.code := by
    simpa [h_code'] using h_code
  cases ev with
  | codeOnly code' =>
      -- In the code-only case, the reported code is exactly `code'`.
      have h_code_eq : code = code' := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code

      -- parseErrorCode? only returns codeOnly if the code is allowed
      have h_allowed : ParseErrorCode.codeOnlyAllowed code' = true := by
        cases h : ParseErrorCode.codeOnlyAllowed code' with
        | false =>
            have h_contra := h_code_ev
            unfold DB.parseErrorCode? at h_contra
            simp [h_err, h_ev, h] at h_contra
        | true =>
            simpa using h

      -- For allowed codes, RuleSemanticViolation reduces to DoneModeViolation.
      rcases ParseErrorCode.codeOnlyAllowed_cases code' h_allowed with
        h_block
        | h_comment
        | h_const
        | h_var
        | h_dj
        | h_float
        | h_ess
        | h_ax
        | h_thm
        | h_proof
      · subst h_block
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedBlock h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_comment
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedComment h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_const
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedConst h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_var
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedVar h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_dj
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedDjvars h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_float
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedFloat h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_ess
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedEss h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_ax
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedAx h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_thm
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedThm h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
      · subst h_proof
        have h_sem := parseErrorCode?_allCodeSemantic_sound s .unclosedProof h_code_ev
        simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_sem
  | tokenForm err =>
      have h_code_eq : code = TokenFormError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_tf : s.TokenFormViolation (TokenFormError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (TokenFormError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_tf
      exact h_rule
  | scopeDecl err =>
      have h_code_eq : code = ScopeDeclError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_sc : s.ScopeDeclViolation (ScopeDeclError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (ScopeDeclError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_sc
      exact h_rule
  | includeErr err =>
      have h_code_eq : code = IncludeError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_inc : s.IncludeViolation (IncludeError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (IncludeError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_inc
      exact h_rule
  | proofCheck err =>
      have h_code_eq : code = ProofCheckError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_pc : s.ProofCheckViolation (ProofCheckError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (ProofCheckError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_pc
      exact h_rule
  | theoremFinality err =>
      have h_code_eq : code = TheoremFinalityError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_tf : s.TheoremFinalityViolation (TheoremFinalityError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (TheoremFinalityError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_tf
      exact h_rule
  | compressedSave err =>
      have h_code_eq : code = CompressedSaveError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_cs : s.CompressedSaveViolation := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (CompressedSaveError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_cs
      exact h_rule
  | internalGate allowDup wf dv =>
      have h_code_eq : code = ParseErrorCode.internalIllFormedDatabaseAfterParse := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_ic : s.InternalConsistencyViolation := ⟨allowDup, wf, dv, h_ev⟩
      simpa [DB.RuleSemanticViolation] using h_ic

/-- Canonical parser rule+clause semantic soundness for any decoded code. -/
theorem parseErrorCode?_ruleClauseSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.RuleClauseSemanticViolation code := by
  intro h_code
  exact ⟨
    parseErrorCode?_ruleSemantic_sound s code h_code,
    parseErrorCode?_specClause_sound s code h_code
  ⟩

/-- Canonical parser-level semantic soundness:
decoded code implies both concrete code witness and clause witness. -/
theorem parseErrorCode?_semantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ParserSemanticViolation code := by
  intro h_code
  exact ⟨
    parseErrorCode?_sound s code h_code,
    parseErrorCode?_specClause_sound s code h_code,
    parseErrorCode?_ruleSemantic_sound s code h_code
  ⟩

def pushScope (s : DB) : DB :=
  { s with scopes := s.scopes.push s.frame.size }

@[simp] theorem pushScope_config (s : DB) : (s.pushScope).config = s.config := rfl

def popScope (pos : Pos) (db : DB) : DB :=
  if let some sc := db.scopes.back? then
    { db with frame := db.frame.shrink sc, scopes := db.scopes.pop }
  else
    db.mkErrorFromEvidence pos (.scopeDecl .cantPopGlobalScope)

@[simp] theorem popScope_config (pos : Pos) (s : DB) : (s.popScope pos).config = s.config := by
  unfold popScope
  cases h : s.scopes.back? <;> simp [DB.mkErrorFromEvidence_config]

def find? (db : DB) (l : String) : Option Object := db.objects[l]?

def isConst (db : DB) (tk : String) : Bool :=
  if let some (.const _) := db.find? tk then true else false

def isVar (db : DB) (tk : String) : Bool :=
  if let some (.var _) := db.find? tk then true else false

/-- `$d` activity predicate: variable must already be active in current frame. -/
def activeVarInScope (db : DB) (tk : String) : Bool :=
  db.frame.hyps.toList.any fun lbl =>
    match db.find? lbl with
    | some (.hyp false prevF _) =>
        prevF.size >= 2 &&
          (match prevF[1]! with
          | .var v' => v'
          | _ => "") == tk
    | _ => false

def isSym (db : DB) (tk : String) : Bool :=
  match db.find? tk with
  | some (.const _) => true
  | some (.var _) => true
  | _ => false

@[inline] def withFrame (f : Frame → Frame) (db : DB) : DB :=
  { db with frame := f db.frame }

@[simp] theorem withFrame_config (f : Frame → Frame) (s : DB) : (s.withFrame f).config = s.config := rfl

@[inline] def withDJ (f : Array DJ → Array DJ) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨f dj, hyps⟩

@[simp] theorem withDJ_config (f : Array DJ → Array DJ) (s : DB) : (s.withDJ f).config = s.config := rfl

@[inline] def withHyps (f : Array String → Array String) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨dj, f hyps⟩

@[simp] theorem withHyps_config (f : Array String → Array String) (s : DB) : (s.withHyps f).config = s.config := rfl

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
  if let some o := db.find? l then
    let ok : Bool := match o with
    | .var _ => if let .var _ := obj l then true else false
    | _ => false
    if ok then db
    else
      db.mkErrorFromEvidence pos (.scopeDecl (.duplicateSymbolOrAssert l))
  else
    { db with objects := db.objects.insert l (obj l) }

/-- `insert` preserves `config`. -/
@[simp] theorem insert_config (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).config = db.config := by
  unfold insert
  -- All branches either return db with config intact, or mkError which preserves config,
  -- or construct a new DB with explicit config := db.config
  repeat (first | split | simp [DB.mkErrorFromEvidence_config, DB.mkError_error] | rfl)

/-- Equation lemma: When db has no error and db.find? l = none and insert doesn't error,
    it adds to objects. -/
theorem insert_no_dup_objects
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_prior_err : db.error = false)
    (h_no_dup : db.find? l = none)
    (h_no_err : (db.insert pos l obj).error = false) :
    (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  unfold insert
  -- Case split on obj l to handle const check
  cases h_obj : obj l with
  | const s =>
    simp only
    -- First split: const check
    split
    · -- Const check failed, creates error - contradiction with h_no_err
      exfalso
      simp only [h_obj, insert, error, mkError] at h_no_err
      split at h_no_err
      · simp only [Option.isSome] at h_no_err
        contradiction
      · -- The isFalse case is impossible because outer split is isTrue
        simp_all
    · -- Const check passed - db.error = false reduces if to else branch
      simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | var s =>
    simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | hyp ess f s =>
    simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | assert f frame s =>
    simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]

/-- Equation lemma: insert find? self when no duplicate and no error. -/
theorem insert_find?_self
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_prior_err : db.error = false)
    (h_no_dup : db.find? l = none)
    (h_no_err : (db.insert pos l obj).error = false) :
    (db.insert pos l obj).find? l = some (obj l) := by
  simp only [find?, insert_no_dup_objects db pos l obj h_no_prior_err h_no_dup h_no_err]
  exact Std.HashMap.getElem?_insert_self

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

@[simp] theorem activeVarInScope_eq_floatVarOccursInFrame (db : DB) (tk : String) :
    db.activeVarInScope tk = db.floatVarOccursInFrame tk := rfl

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

@[simp] theorem insertHypChecks_config (db : DB) (pos : Pos) (ess : Bool) (f : Formula) :
    (db.insertHypChecks pos ess f).config = db.config := by
  unfold insertHypChecks
  by_cases h_head : f.hasConstHead
  · simp [h_head]
    cases h_err : db.error with
    | true =>
        simp
    | false =>
        simp
        cases h_ess : ess with
        | true =>
            simp
            by_cases h_syms : formulaSymsRespectFrame db f (Frame.mk #[] db.frame.hyps)
            · simp [h_syms]
            · simp [h_syms, DB.mkErrorFromEvidence_config]
        | false =>
            simp
            by_cases h_shape : f.isFloatShape
            · simp [h_shape]
              by_cases h_size : f.size >= 2
              · simp [h_size]
                by_cases h_dup :
                  db.config.allowDuplicateFloat = false ∧
                    db.floatVarOccursInFrame f[1]!.value = true
                · simp [h_err, h_dup, DB.mkErrorFromEvidence_config]
                · simp [h_err, h_dup]
              · simp [h_size]
            · simp [h_shape, DB.error, DB.mkErrorFromEvidence_config]
  · simp [h_head, DB.error, DB.mkErrorFromEvidence_config]

def insertHyp (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) : DB :=
  let db := db.insertHypChecks pos ess f
  if db.error then db else
  let db := db.insert pos l (.hyp ess f)
  if db.error then db else
    db.withHyps fun hyps => hyps.push l

@[simp] theorem insertHyp_config (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) :
    (db.insertHyp pos l ess f).config = db.config := by
  unfold insertHyp
  -- Each step preserves config: insertHypChecks, insert, withHyps
  simp only [DB.error]
  split <;> try simp [DB.insertHypChecks_config]
  split <;> simp [DB.insertHypChecks_config, DB.insert_config, DB.withHyps_config]

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
      -- Spec §4.2.4: $f and $e can be interleaved (appearance order)
      -- No need to enforce "$f before $e" - that's a legacy restriction
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

@[simp] theorem insertAxiom_config (db : DB) (pos : Pos) (l : String) (fmla : Formula) :
    (db.insertAxiom pos l fmla).config = db.config := by
  unfold insertAxiom
  by_cases h_head : fmla.hasConstHead
  · simp only [h_head, ↓reduceIte, DB.error]
    split  -- split on db.error?.isSome
    · simp  -- error case: return db unchanged
    · -- no error, split on trimFrame' result
      cases h_trim : db.trimFrame' fmla with
      | error msg => simp [DB.mkErrorFromEvidence_config]
      | ok fr =>
        simp only []
        split  -- split on db.interrupt
        · simp  -- interrupt: set error? with same config
        · simp [DB.insert_config]  -- normal: insert preserves config
  · -- hasConstHead = false: mkError sets error, so returns the errored db
    simp only [h_head, Bool.false_eq_true, ↓reduceIte, DB.error, DB.mkErrorFromEvidence_config,
      DB.mkErrorFromEvidence_error?_isSome]

def mkProofState (_db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    ProofState := Id.run do
  ⟨pos, l, fmla, fr, #[], #[], .start⟩

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

/-- Equation lemma: base case when `i ≥ hyps.size`. -/
@[simp] theorem checkHyp_base
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (h : ¬ i < hyps.size) :
  checkHyp db hyps stack off i σ = .ok σ := by
  unfold checkHyp
  simp [h]
  rfl

/-- Equation lemma when lookup at `hyps[i]` finds an **essential** hypothesis. -/
@[simp] theorem checkHyp_step_hyp_true
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (f : Formula) (lbl : String)
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp true f lbl)) :
  checkHyp db hyps stack off i σ
    =
  if !stack[off.1 + i]!.hasConstHead then
    .error (.proofCheck .stackFormulaNoConstantHead)
  else if !f.hasConstHead then
    .error (.proofCheck .hypothesisNoConstantHead)
  else if !formulaSymsRespectFrame db f (Frame.mk #[] hyps) then
    .error (.scopeDecl .hypothesisSymbolsNotInFrame)
  else if f[0]! == stack[off.1 + i]![0]! then
    match f.subst σ with
    | .ok s =>
        if s == stack[off.1 + i]! then
          checkHyp db hyps stack off (i+1) σ
        else
          .error (.proofCheck .typeErrorInSubstitution)
    | .error _ => .error (.proofCheck .typeErrorInSubstitution)
  else
    .error (.proofCheck
      (.badTypecodeInSubstitution
        s!"{hyps[i]}: {f} / {stack[off.1 + i]!}")) := by
  -- Use rw to unfold only the LHS
  rw [checkHyp]
  simp [h_i, h_find, -beq_iff_eq]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx, bind, Except.bind, -beq_iff_eq]

/-- Equation lemma when lookup at `hyps[i]` finds a **float** hypothesis. -/
@[simp] theorem checkHyp_step_hyp_false
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (f : Formula) (lbl : String)
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp false f lbl)) :
  checkHyp db hyps stack off i σ
    =
  if !stack[off.1 + i]!.hasConstHead then
    .error (.proofCheck .stackFormulaNoConstantHead)
  else if !f.isFloatShape then
    .error (.scopeDecl .expectedConstantAndVariable)
  else if f[0]! == stack[off.1 + i]![0]! then
    if σ.contains f[1]!.value then
      .error (.proofCheck .duplicateFloatVariable)
    else
      checkHyp db hyps stack off (i+1) (σ.insert f[1]!.value (stack[off.1 + i]!))
  else
    .error (.proofCheck
      (.badTypecodeInSubstitution
        s!"{hyps[i]}: {f} / {stack[off.1 + i]!}")) := by
  rw [checkHyp]  -- KEY: Use rw not unfold to avoid expanding RHS recursive calls
  simp [h_i, h_find, -beq_iff_eq]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx, -beq_iff_eq]

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
        let vars := frameFloatVars db pr.frame
        dvCheck vars pr.frame.dj dj subst
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
  | const : TokenParser
  | var : TokenParser
  | djvars : Array String → TokenParser
  | math : Array Sym → TokensParser → TokenParser
  | label : Pos → String → TokenParser
  | proof : ProofState → TokenParser
  deriving Inhabited

def TokenParser.toString : TokenParser → String
  | .start => "start"
  | .comment p => "comment " ++ toString p
  | .const => "const"
  | .var => "var"
  | .djvars s => s!"djvars {s}"
  | .math s p => s!"math {s} {p}"
  | .label pos l => s!"at {pos}: ? {l}"
  | .proof p => ToString.toString p

instance : ToString TokenParser := ⟨TokenParser.toString⟩

structure ParserState where
  db : DB
  tokp : TokenParser
  charp : CharParser
  line : Nat
  linepos : Nat
  deriving Inhabited

namespace ParserState

-- Helper lemmas for Id monad proofs
@[simp] theorem pure_db_config (s : ParserState) : (pure s : Id ParserState).db.config = s.db.config := rfl
@[simp] theorem Id_run_db_config (m : Id ParserState) : (Id.run m).db.config = m.db.config := rfl

@[inline] def withDB (f : DB → DB) (s : ParserState) : ParserState :=
  { s with db := f s.db }

@[simp] theorem withDB_db_config (f : DB → DB) (s : ParserState) :
    (s.withDB f).db.config = (f s.db).config := rfl

def mkPos (s : ParserState) (pos : Nat) : Pos := ⟨s.line, pos - s.linepos⟩

def mkError (s : ParserState) (pos : Pos) (msg : String) : ParserState :=
  s.withDB fun db => db.mkError pos msg

def mkErrorWithEvidence (s : ParserState) (pos : Pos) (msg : String) (ev : ErrorEvidence) : ParserState :=
  s.withDB fun db => db.mkErrorWithEvidence pos msg ev

def mkErrorFromEvidence (s : ParserState) (pos : Pos) (ev : ErrorEvidence) : ParserState :=
  s.withDB fun db => db.mkErrorFromEvidence pos ev

@[simp] theorem mkError_db_config (s : ParserState) (pos : Pos) (msg : String) :
    (s.mkError pos msg).db.config = s.db.config := by
  simp [ParserState.mkError, ParserState.withDB]

@[simp] theorem mkErrorWithEvidence_db_config (s : ParserState) (pos : Pos) (msg : String)
    (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).db.config = s.db.config := by
  simp [ParserState.mkErrorWithEvidence, ParserState.withDB]

@[simp] theorem mkErrorFromEvidence_db_config (s : ParserState) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).db.config = s.db.config := by
  simp [ParserState.mkErrorFromEvidence, ParserState.withDB]

def mkErrorAt (s : ParserState) (pos : Pos) (l msg : String) : ParserState :=
  s.mkError pos s!"at {l}: {msg}"

@[simp] theorem mkErrorAt_db_config (s : ParserState) (pos : Pos) (l msg : String) :
    (s.mkErrorAt pos l msg).db.config = s.db.config := by
  simp [ParserState.mkErrorAt]

def withAt (l : String) (f : Unit → ParserState) : ParserState :=
  let s := f ()
  if let some ⟨.error pos msg, i⟩ := s.db.error? then
    s.withDB fun db => { db with error? := some ⟨.error pos s!"at {l}: {msg}", i⟩ }
  else s

@[simp] theorem withAt_db_config (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).db.config = (f ()).db.config := by
  unfold ParserState.withAt
  -- `withAt` only rewrites the error message (if the interrupt is an `.error`), and does not touch `config`.
  generalize hs : f () = s0
  cases h_err : s0.db.error? with
  | none =>
      simp [h_err]
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e <;> simp [h_err, ParserState.withDB]

@[simp] theorem withAt_tokp (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).tokp = (f ()).tokp := by
  unfold ParserState.withAt
  generalize hs : f () = s0
  cases h_err : s0.db.error? with
  | none =>
      simp [h_err]
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e <;> simp [h_err, ParserState.withDB]

def label (s : ParserState) (pos : Pos) (tk : ByteSlice) : ParserState :=
  let (ok, tk) := toLabel tk
  if ok then { s with tokp := .label pos tk }
  else s.mkErrorFromEvidence pos (.tokenForm (.invalidLabel tk))

@[simp] theorem label_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    (s.label pos tk).db.config = s.db.config := by
  unfold ParserState.label
  -- Split on the if condition (ok = true)
  split <;> split <;> simp [ParserState.mkErrorFromEvidence_db_config]

def withMath (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) : ParserState :=
  let (ok, tk) := toMath tk
  if !ok then
    s.mkErrorFromEvidence pos (.tokenForm (.invalidMathString tk))
  else
  f s tk

@[simp] theorem withMath_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState)
    (hf : ∀ tk', (f s tk').db.config = s.db.config) :
    (s.withMath pos tk f).db.config = s.db.config := by
  unfold ParserState.withMath
  split
  · -- Let binding for (ok, tk)
    split
    · simp [ParserState.mkErrorFromEvidence_db_config]  -- !ok case
    · exact hf _  -- ok case

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

@[simp] theorem djvars_loop_aux_db_config (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String) (i : Nat) :
    (djvars_loop_aux arr s pos tk i).db.config = s.db.config := by
  -- Induction on the remainder `arr.size - i`.
  refine Nat.rec (motive := fun m => ∀ i (s : ParserState), arr.size - i = m →
      (djvars_loop_aux arr s pos tk i).db.config = s.db.config) ?base ?step (arr.size - i) i s rfl
  · intro i s hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simpa [hs] using hpos
    simp [djvars_loop_aux, hi]
  · intro m ih i s hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      ·
        have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        have : False := by
          -- `hs` says `arr.size - i = Nat.succ m`, contradicting `hz`.
          have hs' := hs
          simpa [hz] using hs'
        exact False.elim this
    -- Split on duplicate variable.
    have hs' : arr.size - (i + 1) = m := by
      -- `arr.size - (i+1) = pred (arr.size - i)` and `pred (succ m) = m`.
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    -- Unfold one step and discharge each branch.
    unfold djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    split  -- split on arr[i] == tk
    · -- duplicate case: mkErrorFromEvidence preserves config
      simp [ParserState.mkErrorFromEvidence_db_config]
    · -- non-duplicate: recurse, and `withDB`/`withDJ` preserve config
      have h_cfg : (s.withDB (fun db => db.withDJ fun dj => dj.push (if arr[i] < tk then (arr[i], tk) else (tk, arr[i])))).db.config = s.db.config := by
        simp [ParserState.withDB, DB.withDJ_config]
      -- Apply IH on the recursive call and rewrite the state's config back to `s`.
      simpa [h_cfg] using ih (i + 1) _ hs'

def djvars_loop (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) : ParserState :=
  if s.db.isVar tk then
    djvars_loop_aux arr s pos tk 0
  else
    s.mkErrorFromEvidence pos (.scopeDecl (.tokenNotVariable tk))

@[simp] theorem djvars_loop_db_config (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String) :
    (djvars_loop arr s pos tk).db.config = s.db.config := by
  unfold djvars_loop
  by_cases h_var : s.db.isVar tk
  · simp [h_var, djvars_loop_aux_db_config]
  · simp [h_var, ParserState.mkErrorFromEvidence_db_config]

def sym (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) : ParserState :=
  if tk.eqArray "$.".toAscii then
    { s with tokp := .start }
  else s.withMath pos tk fun s tk =>
    s.withDB fun db => db.insert pos tk f

@[simp] theorem sym_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) :
    (s.sym pos tk f).db.config = s.db.config := by
  unfold ParserState.sym ParserState.withMath
  by_cases h_end : tk.eqArray "$.".toAscii
  · simp [h_end]
  · simp only [h_end, Bool.false_eq_true, ↓reduceIte]
    by_cases h_ok : (toMath tk).fst = false
    · simp [h_ok, ParserState.mkErrorFromEvidence_db_config]
    · simp [h_ok, ParserState.withDB, DB.insert_config]

def resumeAxiom (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  s.withDB fun db => db.insert pos l (.assert fmla fr)

@[simp] theorem resumeAxiom_db_config (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    (s.resumeAxiom pos l fmla fr).db.config = s.db.config := by
  simp [ParserState.resumeAxiom, ParserState.withDB, DB.insert_config]

def resumeThm (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  let pr := s.db.mkProofState pos l fmla fr
  { s with tokp := .proof pr }

@[simp] theorem resumeThm_db_config (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    (s.resumeThm pos l fmla fr).db.config = s.db.config := by
  simp [ParserState.resumeThm]

inductive CompressedAction
  | step (n : Nat)
  | save
  | unknown

/-- Decode a compressed proof token into actions and the updated accumulator. -/
def decodeCompressed (tk : ByteSlice) (chr : Nat) :
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
      throw (.proofCheck .proofParseError)
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
        -- Per spec §4.4.6: ? marks incomplete proof step, verifier should accept
        -- Test: metamath-test/tests/unit/test30_qmark_in_compressed_proof.mm
        -- Knife mode rejects unknown steps (stricter policy)
        if db.config.rejectUnknownSteps then
          throw (.proofCheck .unknownStepQuestionRejected)
        else
          pure (pr.push pr.fmla)
    ) pr

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
      if s.db.config.rejectToplevelEss && s.db.scopes.size == 0 then
        return s.mkErrorFromEvidence pos (.scopeDecl .topLevelEssentialNotAllowed)
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

@[simp] theorem feedTokens_db_config (s : ParserState) (arr : Array Sym) (p : TokensParser) :
    (s.feedTokens arr p).db.config = s.db.config := by
  cases p with
  | mk k pos l =>
      -- `withAt` only rewrites error messages; it doesn't touch the DB config.
      unfold ParserState.feedTokens
      simp only [ParserState.withAt_db_config, ParserState.Id_run_db_config]
      -- Split on all conditions and handle each case
      repeat (first | split | simp [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB,
        DB.insertHyp_config, DB.insertAxiom_config, ParserState.resumeThm_db_config,
        ParserState.pure_db_config] | rfl)

def feedProof (s : ParserState) (tk : ByteSlice) (pr : ProofState) : ParserState :=
  withAt pr.label fun _ =>
    match go pr with
    | .ok pr => { s with tokp := .proof pr }
    | .error err =>
      s.mkErrorFromEvidence pr.pos (ProofCheckFail.evidence err)
where
  goNormal (pr : ProofState) : Except ProofCheckFail ProofState :=
    -- Per spec §4.4.6: "A proof may contain a ? in place of a label to indicate
    -- an unknown step. A proof verifier may ignore any proof containing ? but
    -- should warn the user that the proof is incomplete."
    -- Test: metamath-test/tests/unit/test20_unknown_step_qmark_(should_accept_with_warning).mm
    -- Knife mode rejects unknown steps (stricter policy)
    if tk.eqArray "?".toAscii then
      if s.db.config.rejectUnknownSteps then
        throw (.proofCheck .unknownStepQuestionRejected)
      else
        pure (pr.push pr.fmla)
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
      let (acts, chr) ← decodeCompressed tk chr
      pr ← applyCompressedActions s.db pr acts
      pure { pr with ptp := .compressed chr }

@[simp] theorem feedProof_db_config (s : ParserState) (tk : ByteSlice) (pr : ProofState) :
    (s.feedProof tk pr).db.config = s.db.config := by
  -- `go` only manipulates the proof state; the DB is changed only via `mkError` on failure.
  unfold ParserState.feedProof
  simp only [ParserState.withAt_db_config]
  -- Split on match result: ok returns unchanged db, error uses mkError
  split <;> simp [ParserState.mkErrorFromEvidence_db_config]

def finishProof (s : ParserState) : ProofState → ParserState
  | ⟨pos, l, fmla, fr, _, stack, ptp⟩ => withAt l fun _ => Id.run do
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
    s.withDB fun db => db.insert pos l (.assert fmla fr)

@[simp] theorem finishProof_db_config (s : ParserState) (pr : ProofState) :
    (s.finishProof pr).db.config = s.db.config := by
  cases pr with
  | mk pos l fmla fr heap stack ptp =>
      unfold ParserState.finishProof
      simp only [ParserState.withAt_db_config, Id.run]
      -- The function returns either mkError or insert via withDB; all preserve config
      cases ptp with
      | start => simp [ParserState.mkErrorFromEvidence_db_config]
      | preload => simp [ParserState.mkErrorFromEvidence_db_config]
      | normal =>
          simp only [Pure.pure, Bind.bind]
          split
          · split <;> simp [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB, DB.insert_config]
          · simp [ParserState.mkErrorFromEvidence_db_config]
      | compressed chr =>
          simp only [Pure.pure, Bind.bind]
          split
          · -- Case h_1: compressed 0
            split
            · split <;> simp [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB, DB.insert_config]
            · simp [ParserState.mkErrorFromEvidence_db_config]
          · -- Case h_2: normal (impossible - just use simp)
            split
            · split <;> simp [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB, DB.insert_config]
            · simp [ParserState.mkErrorFromEvidence_db_config]
          · -- Case h_3: other (chr ≠ 0) - returns mkError
            simp [ParserState.mkErrorFromEvidence_db_config]

def feedToken (s : ParserState) (pos : Nat) (tk : ByteSlice) : ParserState :=
  let pos := s.mkPos pos
  match s.tokp with
  | .comment p =>
    if tk.eqArray "$)".toAscii then { s with tokp := p }
    else if tk.eqArray "$(".toAscii then
      -- Per spec §4.1.1: "comments may not contain the 2-character sequences $( or $)"
      -- Test: metamath-test/tests/unit/test03_nested_comment_delimiters.mm
      s.mkErrorFromEvidence pos (.tokenForm .nestedCommentDelimiter)
    else s
  | p =>
    if tk.eqArray "$(".toAscii then { s with tokp := p.comment } else
    match p with
    | .comment _ => unreachable!
    | .start =>
      if tk.len == 2 && tk[0]! == '$'.toUInt8 then
        match tk[1]!.toChar with
        | '{' => s.withDB .pushScope
        | '}' => s.withDB (.popScope pos)
        | 'c' => { s with tokp := .const }
        | 'v' => { s with tokp := .var }
        | 'd' => { s with tokp := .djvars #[] }
        | _ => s.label pos tk
      else s.label pos tk
    | .const => s.sym pos tk .const
    | .var => s.sym pos tk .var
    | .djvars arr =>
      if tk.eqArray "$.".toAscii then { s with tokp := .start } else
      s.withMath pos tk fun s tk => djvars_loop arr s pos tk
    | .math arr p =>
      if tk.eqArray p.k.delim then
        s.feedTokens arr p
      else
        s.withMath pos tk fun s tk => Id.run do
          let tk ← match s.db.find? tk with
          | some (.const _) => Sym.const tk
          | some (.var _) => Sym.var tk
          | _ =>
            return s.mkErrorFromEvidence pos (.scopeDecl (.tokenNotConstantOrVariable tk))
          { s with tokp := .math (arr.push tk) p }
    | .label pos lab =>
      if tk.len == 2 && tk[0]! == '$'.toUInt8 then
        let go (s : ParserState) (k : TokensKind) :=
          { s with tokp := .math #[] ⟨k, pos, lab⟩ }
        match tk[1]!.toChar with
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
    | .proof pr =>
      let s := { s with tokp := default }
      if tk.eqArray "$.".toAscii then s.finishProof pr
      else s.feedProof tk pr

@[simp] theorem feedToken_db_config (s : ParserState) (pos : Nat) (tk : ByteSlice) :
    (s.feedToken pos tk).db.config = s.db.config := by
  unfold ParserState.feedToken
  -- Case split on the token parser state; each branch either keeps `db` unchanged, or applies
  -- an operation proven to preserve `config`.
  cases s.tokp with
  | comment p =>
      -- comment mode: either exit comment, error on nested $( or stay in comment
      simp only []
      split
      · rfl  -- $) exits comment
      · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
  | start =>
      -- start mode: check for special tokens or treat as label
      simp only []
      split
      · rfl  -- $( opens comment
      · split
        · -- $X commands
          split <;> simp [ParserState.withDB, DB.pushScope_config, DB.popScope_config, ParserState.label_db_config]
        · -- other: label
          simp [ParserState.label_db_config]
  | const =>
      simp only []
      split
      · rfl  -- $( opens comment
      · simp [ParserState.sym_db_config]
  | var =>
      simp only []
      split
      · rfl  -- $( opens comment
      · simp [ParserState.sym_db_config]
  | djvars arr =>
      simp only []
      split
      · rfl  -- $( opens comment
      · split
        · rfl  -- $. ends djvars
        · simp [ParserState.djvars_loop_db_config]
  | math arr' p =>
      simp only []
      split
      · rfl  -- $( opens comment
      · -- Inner match enters .math case
        split
        · simp [ParserState.feedTokens_db_config]  -- delimiter ends math
        · -- Continue math: withMath + Id.run do
          apply ParserState.withMath_db_config
          intro tk'
          simp only [Id.run, Pure.pure, Bind.bind]
          split
          · rfl  -- h_1: const case
          · rfl  -- h_2: var case
          · simp [ParserState.mkErrorFromEvidence_db_config]  -- h_3: error case
  | label pos' lab =>
      simp only []
      split
      · rfl  -- $( opens comment
      · -- Statement type or error
        split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]  -- f/e/a/p or unknown
        · simp [ParserState.mkErrorFromEvidence_db_config]  -- invalid
  | proof pr =>
      simp only []
      split
      · rfl  -- $( opens comment
      · -- Inner match enters .proof case
        split <;> simp [ParserState.finishProof_db_config, ParserState.feedProof_db_config]

inductive OldToken
  | this (off : Nat)
  | old (base off : Nat) (arr : ByteArray)

inductive FeedState
  | ws : FeedState
  | token : OldToken → FeedState

def updateLine (s : ParserState) (i : Nat) (c : UInt8) : ParserState :=
  if c == '\n'.toUInt8 then { s with line := s.line + 1, linepos := i + 1 } else s

@[simp] theorem updateLine_db (s : ParserState) (i : Nat) (c : UInt8) :
    (s.updateLine i c).db = s.db := by
  unfold ParserState.updateLine
  split <;> rfl

@[simp] theorem updateLine_db_config (s : ParserState) (i : Nat) (c : UInt8) :
    (s.updateLine i c).db.config = s.db.config := by
  simp [updateLine_db]

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

@[simp] theorem feed_db_config (base : Nat) (arr : ByteArray) (i : Nat) (rs : FeedState) (s : ParserState) :
    (s.feed base arr i rs).db.config = s.db.config := by
  -- Induction on the remainder `arr.size - i` (same termination measure as `feed`).
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState), arr.size - i = m →
      (s.feed base arr i rs).db.config = s.db.config) ?base ?step (arr.size - i) i rs s rfl
  · intro i rs s hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simpa [hs] using hpos
    unfold ParserState.feed
    simp only [hi, ↓reduceDIte]
  · intro m ih i rs s hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      ·
        have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        have : False := by
          -- `hs` says `arr.size - i = Nat.succ m`, contradicting `hz`.
          have hs' := hs
          simpa [hz] using hs'
        exact False.elim this
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    let c := arr[i]
    by_cases h_ws : isWhitespace c
    · -- Whitespace branch.
      cases rs with
      | ws =>
          -- updateLine does not touch `db`.
          have hrec := ih (i + 1) FeedState.ws (s.updateLine (base + i) c) hs'
          -- c := arr[i], so hrec applies to (s.updateLine (base + i) arr[i])
          -- Transform hrec's RHS from (s.updateLine ...).db.config to s.db.config
          simp only [ParserState.updateLine_db_config] at hrec
          unfold ParserState.feed
          have h_ws' : isWhitespace arr[i] = true := h_ws
          simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte]
          exact hrec
      | token ot =>
          -- Flush token with `feedToken` (preserves config), then either set interrupt or recurse.
          have hs0 :
              (match ot with
              | .this off => (s.feedToken (base + off) (ByteSlice.mk arr off (i - off))).db.config
              | .old base' off arr' =>
                  (s.feedToken (base + off)
                    (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))).db.config)
                = s.db.config := by
            cases ot <;> simp [ParserState.feedToken_db_config]
          -- After `feedToken`, `updateLine` still does not touch `db`.
          -- Split on whether parsing produced an interrupt.
          cases ot with
          | this off =>
              let s0 := s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
              -- Use arr[i] directly instead of c to match goal structure after unfold
              let s1 : ParserState := s0.updateLine (base + i) arr[i]
              have hs1 : s1.db.config = s.db.config := by
                simp only [s1, ParserState.updateLine_db_config, s0, ParserState.feedToken_db_config]
              have h_ws' : isWhitespace arr[i] = true := h_ws
              cases h_err : s1.db.error? with
              | some intr =>
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err, hs1]
              | none =>
                  have hrec := ih (i + 1) FeedState.ws s1 hs'
                  -- hrec : (feed ... s1).db.config = s1.db.config
                  -- Chain with hs1 : s1.db.config = s.db.config
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err]
                  exact hrec.trans hs1
          | old base' off arr' =>
              -- Note: in the feed function, | .old base off arr' => uses the pattern's base
              -- Here base' is the pattern's base, so we use base' + off
              let s0 := s.feedToken (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
              -- Use arr[i] directly instead of c to match goal structure after unfold
              let s1 : ParserState := s0.updateLine (base + i) arr[i]
              have hs1 : s1.db.config = s.db.config := by
                simp only [s1, ParserState.updateLine_db_config, s0, ParserState.feedToken_db_config]
              have h_ws' : isWhitespace arr[i] = true := h_ws
              cases h_err : s1.db.error? with
              | some intr =>
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err, hs1]
              | none =>
                  have hrec := ih (i + 1) FeedState.ws s1 hs'
                  -- hrec : (feed ... s1).db.config = s1.db.config
                  -- Chain with hs1 : s1.db.config = s.db.config
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err]
                  exact hrec.trans hs1
    · -- Non-whitespace: recurse without changing `db`.
      -- Unfold one step of `feed` without relying on equational theorems for the recursive definition.
      -- In the non-whitespace branch, the recursion state updates only `charp`, not `db`.
      -- h_ws : ¬ isWhitespace c where c := arr[i]
      have h_ws' : ¬ isWhitespace arr[i] = true := h_ws
      cases rs with
      | ws =>
          have hrec := ih (i + 1) (FeedState.token (OldToken.this i)) s hs'
          unfold ParserState.feed
          simp only [hi, h_ws', ↓reduceDIte]
          exact hrec
      | token ot =>
          have hrec := ih (i + 1) (FeedState.token ot) s hs'
          unfold ParserState.feed
          simp only [hi, h_ws', ↓reduceDIte]
          exact hrec

def feedAll (s : ParserState) (base : Nat) (arr : ByteArray) : ParserState :=
  match s.charp with
  | .ws => s.feed base arr 0 .ws
  | .token base' tk =>
    let arr' := tk.byteArray
    let off := tk.start
    let s := { s with charp := default }
    s.feed base arr 0 (.token (.old base' off arr'))

@[simp] theorem feedAll_db_config (s : ParserState) (base : Nat) (arr : ByteArray) :
    (s.feedAll base arr).db.config = s.db.config := by
  cases h : s.charp with
  | ws =>
      simp [ParserState.feedAll, h, ParserState.feed_db_config]
  | token base' tk =>
      simp [ParserState.feedAll, h, ParserState.feed_db_config]

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
  | .const => db.mkParseError base .unclosedConst
  | .var => db.mkParseError base .unclosedVar
  | .djvars _ => db.mkParseError base .unclosedDjvars
  | .math _ p => match p.k with
    | .float => db.mkParseError base .unclosedFloat
    | .ess => db.mkParseError base .unclosedEss
    | .ax => db.mkParseError base .unclosedAx
    | .thm => db.mkParseError base .unclosedThm
  | .label pos lab => db.mkErrorFromEvidence pos (.tokenForm (.notACommand lab))
  | .proof _ => db.mkParseError base .unclosedProof

/-- If parsing ends in `$d` mode at whitespace boundary, `done` reports unclosed `$d`. -/
theorem done_error_if_djvars_ws
    (s : ParserState) (base : Nat) (vars : Array String)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none)
    (h_tokp : s.tokp = .djvars vars) :
    (s.done base).error? ≠ none := by
  simp [ParserState.done, h_charp, h_no_err, h_tokp, DB.mkParseError, DB.mkErrorFromEvidence,
    DB.mkErrorWithEvidence, DB.error, Id.run]

/-- If parsing ends in `$d` mode after flushing a pending token, `done` reports unclosed `$d`. -/
theorem done_error_if_djvars_token
    (s : ParserState) (base : Nat) (pos : Nat) (tk : ByteSliceT) (vars : Array String)
    (h_charp : s.charp = .token pos tk)
    (h_no_err : s.db.error? = none)
    (h_feed_no_err : (s.feedToken pos tk.toSlice).db.error? = none)
    (h_tokp : (s.feedToken pos tk.toSlice).tokp = .djvars vars) :
    (s.done base).error? ≠ none := by
  simp [ParserState.done, h_charp, h_no_err, h_feed_no_err, h_tokp, DB.mkParseError,
    DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.error, Id.run]

/-- If parsing ends in `$d` mode at whitespace boundary, `done` reports code `unclosedDjvars`. -/
theorem done_errorCode_if_djvars_ws
    (s : ParserState) (base : Nat) (vars : Array String)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none)
    (h_tokp : s.tokp = .djvars vars) :
    (s.done base).parseErrorCode? = some .unclosedDjvars := by
  simp [ParserState.done, h_charp, h_no_err, h_tokp, DB.parseErrorCode?, DB.mkParseError,
    DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.error, Id.run, ParseErrorCode.codeOnlyAllowed]

/-- If parsing ends in `$d` mode after flushing a pending token, code is `unclosedDjvars`. -/
theorem done_errorCode_if_djvars_token
    (s : ParserState) (base : Nat) (pos : Nat) (tk : ByteSliceT) (vars : Array String)
    (h_charp : s.charp = .token pos tk)
    (h_no_err : s.db.error? = none)
    (h_feed_no_err : (s.feedToken pos tk.toSlice).db.error? = none)
    (h_tokp : (s.feedToken pos tk.toSlice).tokp = .djvars vars) :
    (s.done base).parseErrorCode? = some .unclosedDjvars := by
  simp [ParserState.done, h_charp, h_no_err, h_feed_no_err, h_tokp, DB.parseErrorCode?,
    DB.mkParseError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.error, Id.run,
    ParseErrorCode.codeOnlyAllowed]

/-- `done` preserves any existing parser error code (first parser error wins). -/
theorem done_preserves_existing_parseErrorCode
    (s : ParserState) (base : Nat) (code : ParseErrorCode)
    (h_prev : s.db.parseErrorCode? = some code) :
    (s.done base).parseErrorCode? = some code := by
  obtain ⟨pos, msg, idx, ev, h_err, _, _⟩ :=
    (DB.parseErrorCode?_semantic_sound (s := s.db) (code := code) h_prev).1
  have h_err_some : s.db.error?.isSome = true := by
    simp [h_err]
  have h_done : s.done base = s.db := by
    unfold ParserState.done
    simp [h_err_some, DB.error, Id.run, Pure.pure]
  simpa [h_done] using h_prev

/-- Parser-level soundness (ws branch): open `$d` at EOF yields `unclosedDjvars`
under the no-prior-error contract. -/
theorem done_unclosedDjvars_sound_ws
    (s : ParserState) (base : Nat)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none)
    (vars : Array String)
    (h_tokp : s.tokp = .djvars vars) :
    (s.done base).parseErrorCode? = some .unclosedDjvars := by
  exact done_errorCode_if_djvars_ws s base vars h_charp h_no_err h_tokp

/-- EOF inversion (whitespace case): `done` returns the code dictated by the current parser mode. -/
theorem done_parseErrorCode?_ws
    (s : ParserState) (base : Nat)
    (h_charp : s.charp = .ws)
    (h_no_err : s.db.error? = none) :
    (s.done base).parseErrorCode? =
      match s.tokp with
      | .start =>
          if s.db.scopes.size > 0 then some .unclosedBlock else none
      | .comment _ => some .unclosedComment
      | .const => some .unclosedConst
      | .var => some .unclosedVar
      | .djvars _ => some .unclosedDjvars
      | .math _ p =>
          match p.k with
          | .float => some .unclosedFloat
          | .ess => some .unclosedEss
          | .ax => some .unclosedAx
          | .thm => some .unclosedThm
      | .label _ _ => some .notACommand
      | .proof _ => some .unclosedProof := by
  unfold ParserState.done
  simp [h_charp, h_no_err, DB.error, DB.parseErrorCode?, DB.mkParseError, DB.mkErrorFromEvidence,
    DB.mkErrorWithEvidence, Id.run, ParseErrorCode.codeOnlyAllowed]
  cases h_tokp : s.tokp <;>
    simp [h_tokp, DB.parseErrorCode?, DB.mkParseError, DB.mkErrorFromEvidence,
      DB.mkErrorWithEvidence, ParseErrorCode.codeOnlyAllowed]
  case start =>
    by_cases h_scope : 0 < s.db.scopes.size
    · simp [h_scope, ParseErrorCode.codeOnlyAllowed]
    · simp [h_scope, h_no_err]
  case math a p =>
    cases h_k : p.k <;>
      simp [h_k, ParseErrorCode.codeOnlyAllowed]
  case label pos lab =>
    simp [ErrorEvidence.code, TokenFormError.code]

/-- EOF inversion (token case): `done` returns the code dictated by the parser mode after
flushing the pending token, assuming no error was raised during the flush. -/
theorem done_parseErrorCode?_token
    (s : ParserState) (base : Nat) (pos : Nat) (tk : ByteSliceT)
    (h_charp : s.charp = .token pos tk)
    (h_no_err : s.db.error? = none)
    (h_feed_no_err : (s.feedToken pos tk.toSlice).db.error? = none) :
    (s.done base).parseErrorCode? =
      match (s.feedToken pos tk.toSlice).tokp with
      | TokenParser.start =>
          if (s.feedToken pos tk.toSlice).db.scopes.size > 0 then some .unclosedBlock else none
      | TokenParser.comment _ => some .unclosedComment
      | TokenParser.const => some .unclosedConst
      | TokenParser.var => some .unclosedVar
      | TokenParser.djvars _ => some .unclosedDjvars
      | TokenParser.math _ p =>
          match p.k with
          | .float => some .unclosedFloat
          | .ess => some .unclosedEss
          | .ax => some .unclosedAx
          | .thm => some .unclosedThm
      | TokenParser.label _ _ => some .notACommand
      | TokenParser.proof _ => some .unclosedProof := by
  unfold ParserState.done
  simp [h_charp, h_no_err, h_feed_no_err, DB.error, DB.parseErrorCode?, DB.mkParseError,
    DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, Id.run, ParseErrorCode.codeOnlyAllowed]
  cases h_tokp : (s.feedToken pos tk.toSlice).tokp <;>
    simp [h_tokp, DB.parseErrorCode?, DB.mkParseError, DB.mkErrorFromEvidence,
      DB.mkErrorWithEvidence, ParseErrorCode.codeOnlyAllowed]
  case start =>
    by_cases h_scope : 0 < (s.feedToken pos tk.toSlice).db.scopes.size
    · simp [h_scope, ParseErrorCode.codeOnlyAllowed]
    · simp [h_scope, h_feed_no_err]
  case math a p =>
    cases h_k : p.k <;>
      simp [h_k, ParseErrorCode.codeOnlyAllowed]
  case label pos lab =>
    simp [ErrorEvidence.code, TokenFormError.code]

@[simp] theorem done_config (s : ParserState) (base : Nat) :
    (s.done base).config = s.db.config := by
  by_cases h_err0 : s.db.error?.isSome = true
  · unfold ParserState.done
    simp [h_err0, DB.error, Bind.bind, Id.run, Pure.pure]
  · cases h_charp : s.charp with
    | ws =>
        unfold ParserState.done
        simp [h_err0, h_charp, DB.error, Bind.bind, Id.run, Pure.pure]
        cases h_tokp : s.tokp with
        | start =>
            by_cases h_scope : 0 < s.db.scopes.size
            · simp [h_tokp, h_scope, DB.mkErrorFromEvidence_config]
            · simp [h_tokp, h_scope]
        | comment _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | const =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | var =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | djvars _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | math _ p =>
            cases h_k : p.k <;> simp [h_tokp, h_k, DB.mkErrorFromEvidence_config]
        | label _ _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | proof _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
    | token pos tk =>
        by_cases h_err1 : (s.feedToken pos tk.toSlice).db.error?.isSome = true
        · unfold ParserState.done
          simp [h_err0, h_charp, h_err1, DB.error, Bind.bind, Id.run, Pure.pure,
            ParserState.feedToken_db_config]
        · unfold ParserState.done
          simp [h_err0, h_charp, h_err1, DB.error, Bind.bind, Id.run, Pure.pure,
            ParserState.feedToken_db_config]
          cases h_tokp : (s.feedToken pos tk.toSlice).tokp with
          | start =>
              by_cases h_scope : 0 < (s.feedToken pos tk.toSlice).db.scopes.size
              · simp [h_tokp, h_scope, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
              · simp [h_tokp, h_scope, ParserState.feedToken_db_config]
          | comment _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | const =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | var =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | djvars _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | math _ p =>
              cases h_k : p.k <;>
                simp [h_tokp, h_k, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | label _ _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | proof _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]

end ParserState

/-! ## Pure Parser Entry Point

`checkBytes` is a pure parser entry point for proofs about parser invariants.
It processes the full byte array in one pass. This is simpler to reason about
than chunked IO, and the IO entry point (`check`) delegates to it after
include-expansion.
-/
def checkBytesCore (arr : ByteArray) (config : ModeConfig := {}) : DB :=
  let initialDB : DB := { (default : DB) with config := config }
  let initialState : ParserState := { (default : ParserState) with db := initialDB }
  let s := initialState.feedAll 0 arr
  s.done arr.size

-- Config is preserved through parsing (no operation modifies it)
-- This is observable: config is set once at init and never changed
@[simp] theorem checkBytesCore_config (arr : ByteArray) (config : ModeConfig) :
    (checkBytesCore arr config).config = config := by
  -- `config` is set once at initialization; `feedAll` and `done` preserve it.
  simp [checkBytesCore, ParserState.feedAll_db_config, ParserState.done_config]

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

/-- Internal gate violation semantics for `checkBytes`:
if the internal "well-formed + DV" gate fails, we record the dedicated code
and can recover the precise failed condition. -/
theorem checkBytes_internalGate_violation
    (arr : ByteArray) (config : ModeConfig)
    (h_none : (checkBytesCore arr config).error? = none)
    (h_code : (checkBytes arr config).parseErrorCode? = some .internalIllFormedDatabaseAfterParse) :
      ( (¬ (checkBytesCore arr config).config.allowDuplicateFloat ∧
          (checkBytesCore arr config).wellFormed? = false)
        ∨ (checkBytesCore arr config).assertDvVarsInFrame? = false ) := by
  -- Unfold the post-check gate and analyze the failure branch.
  unfold checkBytes at h_code
  let db := checkBytesCore arr config
  have h_none' : db.error? = none := by
    simpa [db] using h_none
  have h_code' :
      (if (db.config.allowDuplicateFloat || db.wellFormed?) && db.assertDvVarsInFrame?
        then db
        else db.mkErrorFromEvidence ⟨0, 0⟩
          (.internalGate db.config.allowDuplicateFloat db.wellFormed? db.assertDvVarsInFrame?)).parseErrorCode? =
        some .internalIllFormedDatabaseAfterParse := by
    simpa [db, h_none'] using h_code
  let A := db.config.allowDuplicateFloat
  let WF := db.wellFormed?
  let B := db.assertDvVarsInFrame?
  have h_code'' :
      (if (A || WF) && B
        then db
        else db.mkErrorFromEvidence ⟨0, 0⟩ (.internalGate A WF B)).parseErrorCode? =
        some .internalIllFormedDatabaseAfterParse := by
    simpa [A, WF, B] using h_code'
  by_cases h_gate : (A || WF) && B
  · -- Gate succeeded: contradicts that we emitted the internal error.
    have h_db_code : db.parseErrorCode? = some .internalIllFormedDatabaseAfterParse := by
      simpa [h_gate] using h_code''
    have h_db_none : db.parseErrorCode? = none := by
      simp [DB.parseErrorCode?, h_none']
    simpa [h_db_none] using h_db_code
  · -- Gate failed: either the DV check failed, or both allowDuplicateFloat and wellFormed? were false.
    cases hAorWF : (A || WF) <;> cases hB : B
    · -- A || WF = false, B = false
      exact Or.inr (by simpa [B, db] using hB)
    · -- A || WF = false, B = true
      cases hA : A <;> cases hWF : WF
      · have hAne : ¬ A = true := by
          simp [hA]
        exact Or.inl ⟨by simpa [A, db] using hAne, by simpa [WF, db] using hWF⟩
      · simp [hA, hWF] at hAorWF
      · simp [hA, hWF] at hAorWF
      · simp [hA, hWF] at hAorWF
    · -- A || WF = true, B = false
      exact Or.inr (by simpa [B, db] using hB)
    · -- A || WF = true, B = true (impossible under gate-false)
      have h_true : ((A || WF) && B) = true := by
        simp [hAorWF, hB]
      exact (h_gate h_true).elim
  -- (no `h_none` false branch; it is a hypothesis)

/-- Non-overwrite bridge inside `checkBytesCore`:
if `feedAll` has already produced a decoded parse error code, `done` preserves it. -/
theorem checkBytesCore_preserves_feedAll_parseErrorCode
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code :
      (({ (default : ParserState) with db := { (default : DB) with config := config } }).feedAll 0 arr).db.parseErrorCode? = some code) :
    (checkBytesCore arr config).parseErrorCode? = some code := by
  unfold checkBytesCore
  let initialDB : DB := { (default : DB) with config := config }
  let initialState : ParserState := { (default : ParserState) with db := initialDB }
  have h_done :
      ((initialState.feedAll 0 arr).done arr.size).parseErrorCode? = some code := by
    exact ParserState.done_preserves_existing_parseErrorCode
      (s := initialState.feedAll 0 arr) (base := arr.size) (code := code)
      (by simpa [initialState, initialDB] using h_code)
  simpa [initialState, initialDB] using h_done

/-- Non-overwrite bridge from parser core to final `checkBytes` result:
if core parser already has a decoded parse error code, the post-check gate keeps it. -/
theorem checkBytes_preserves_checkBytesCore_parseErrorCode
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code : (checkBytesCore arr config).parseErrorCode? = some code) :
    (checkBytes arr config).parseErrorCode? = some code := by
  unfold checkBytes
  by_cases h_none : (checkBytesCore arr config).error? = none
  · exfalso
    rcases (DB.parseErrorCode?_semantic_sound (s := checkBytesCore arr config) code h_code).1 with
      ⟨pos, msg, idx, ev, h_err, _, _⟩
    simp [h_err] at h_none
  · simp [h_none, h_code]

/-- End-to-end non-overwrite theorem:
if the feed stage has already produced a decoded parse error code, the full
`checkBytes` pipeline preserves exactly that code. -/
theorem checkBytes_preserves_feedAll_parseErrorCode
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code :
      (({ (default : ParserState) with db := { (default : DB) with config := config } }).feedAll 0 arr).db.parseErrorCode? = some code) :
    (checkBytes arr config).parseErrorCode? = some code := by
  exact checkBytes_preserves_checkBytesCore_parseErrorCode arr config code
    (checkBytesCore_preserves_feedAll_parseErrorCode arr config code h_code)

theorem checkBytes_no_error_wellFormed?
    (arr : ByteArray) (config : ModeConfig := {}) :
    config.allowDuplicateFloat = false →  -- Only when duplicate $f not allowed
    (checkBytes arr config).error? = none →
    (checkBytes arr config).wellFormed? = true := by
  intro h_no_dup h_ok
  -- The logic: if error? = none when allowDuplicateFloat = false, then either:
  -- 1. wellFormed? was true (and db returned as-is), or
  -- 2. wellFormed? was false, so error was set (contradicts error? = none)
  simp only [checkBytes] at h_ok ⊢
  -- db0 = checkBytesCore arr config has config preserved
  have h_dup : (checkBytesCore arr config).config.allowDuplicateFloat = false := by
    simp only [checkBytesCore_config, h_no_dup]
  by_cases h_err : (checkBytesCore arr config).error? = none
  · simp only [h_err, ↓reduceIte] at h_ok ⊢
    by_cases h_wf : (checkBytesCore arr config).wellFormed? = true
    · -- When wellFormed? = true, the condition is true and we return db unchanged
      have h_assert : (checkBytesCore arr config).assertDvVarsInFrame? = true := by
        by_cases h_a : (checkBytesCore arr config).assertDvVarsInFrame? = true
        · exact h_a
        ·
          simp [h_wf, h_a, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at h_ok
      simp only [h_wf, Bool.or_true, h_assert, Bool.true_and, ↓reduceIte]
    · -- wellFormed? = false when not allowing dup sets error, contradicting h_ok
      have h_cond :
          (((checkBytesCore arr config).config.allowDuplicateFloat ||
              (checkBytesCore arr config).wellFormed?) &&
            (checkBytesCore arr config).assertDvVarsInFrame?) = false := by
        cases h : (checkBytesCore arr config).wellFormed? with
        | true => exact (h_wf h).elim
        | false => simp only [h_dup, Bool.false_or, Bool.false_and]
      simp only [h_cond, Bool.false_eq_true, ↓reduceIte, DB.mkErrorFromEvidence] at h_ok
      -- h_ok : some _ = none, which is a contradiction
      cases h_ok
  · simp [h_err] at h_ok

theorem checkBytes_no_error_assertDvVarsInFrame?
    (arr : ByteArray) (config : ModeConfig := {}) :
    (checkBytes arr config).error? = none →
    (checkBytes arr config).assertDvVarsInFrame? = true := by
  intro h_ok
  by_cases h_err : (checkBytesCore arr config).error? = none
  · simp [checkBytes, h_err] at h_ok ⊢
    by_cases h_assert : (checkBytesCore arr config).assertDvVarsInFrame? = true
    · by_cases h_gate : config.allowDuplicateFloat = true ∨ (checkBytesCore arr config).wellFormed? = true
      · simp [h_gate, h_assert]
      · have h_mk :
            ((checkBytesCore arr config).mkErrorFromEvidence ⟨0, 0⟩
              (.internalGate (checkBytesCore arr config).config.allowDuplicateFloat
                (checkBytesCore arr config).wellFormed?
                (checkBytesCore arr config).assertDvVarsInFrame?)).assertDvVarsInFrame? =
              (checkBytesCore arr config).assertDvVarsInFrame? := by
            rfl
        have h_cond_false :
            ((config.allowDuplicateFloat = true ∨ (checkBytesCore arr config).wellFormed? = true) ∧
              (checkBytesCore arr config).assertDvVarsInFrame? = true) = false := by
          simp [h_gate, h_assert]
        have h_mk_true :
            ((checkBytesCore arr config).mkErrorFromEvidence ⟨0, 0⟩
              (.internalGate (checkBytesCore arr config).config.allowDuplicateFloat
                (checkBytesCore arr config).wellFormed?
                (checkBytesCore arr config).assertDvVarsInFrame?)).assertDvVarsInFrame? = true := by
            simpa [h_mk] using h_assert
        simpa [h_cond_false] using h_mk_true
    ·
      simp [h_assert, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at h_ok
  · simp [checkBytes, h_err] at h_ok

/-- Canonical parser-entry semantic soundness:
`checkBytes` decoded code implies bundled semantic violation witness. -/
theorem checkBytes_parseErrorCode?_semantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ParserSemanticViolation code := by
  intro h_code
  exact DB.parseErrorCode?_semantic_sound (s := checkBytes arr config) code h_code

/-- Parser-level soundness at the byte-stream entrypoint. -/
theorem checkBytes_parseErrorCode?_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ParserSpecViolation code := by
  intro h_code
  exact (checkBytes_parseErrorCode?_semantic_sound arr config code h_code).1

/-- `checkBytes` clause-level soundness from decoded code + code-to-clause mapping. -/
theorem checkBytes_parseErrorCode?_clause_sound
    (arr : ByteArray) (config : ModeConfig)
    (code : ParseErrorCode) (clause : SpecClause) :
    (checkBytes arr config).parseErrorCode? = some code →
    ParseErrorCode.specClause code = clause →
    (checkBytes arr config).ParserSpecClauseViolation clause := by
  intro h_code h_clause
  rcases (checkBytes_parseErrorCode?_semantic_sound arr config code h_code).2.1 with ⟨code', h_code', h_clause'⟩
  exact ⟨code', h_code', h_clause'.trans h_clause⟩

/-- `checkBytes` clause soundness using the canonical clause attached to the code. -/
theorem checkBytes_parseErrorCode?_specClause_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact (checkBytes_parseErrorCode?_semantic_sound arr config code h_code).2.1

/-- `checkBytes` all-code payload-shape soundness:
decoded parser code carries normalized payload-shape evidence for every constructor. -/
theorem checkBytes_parseErrorCode?_allCodePayloadShape_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).AllCodePayloadShapeViolation code := by
  intro h_code
  exact DB.parseErrorCode?_allCodePayloadShape_sound (s := checkBytes arr config) code h_code

/-- `checkBytes` all-code semantic payload-shape soundness:
decoded parser code carries semantic message-shape evidence for every constructor. -/
theorem checkBytes_parseErrorCode?_allCodeSemantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).AllCodeSemanticViolation code := by
  intro h_code
  exact DB.parseErrorCode?_allCodeSemantic_sound (s := checkBytes arr config) code h_code

theorem checkBytes_allCodePayloadShape_implies_specClauseViolation
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).AllCodePayloadShapeViolation code →
    (checkBytes arr config).ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_shape
  exact DB.allCodePayloadShape_implies_specClauseViolation (s := checkBytes arr config) code h_shape

/-- `checkBytes` all-code clause-semantic soundness:
decoded parser code yields semantic witness for the code's mapped clause. -/
theorem checkBytes_parseErrorCode?_allCodeClauseSemantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact DB.parseErrorCode?_allCodeClauseSemantic_sound (s := checkBytes arr config) code h_code

/-- Canonical all-code parser-entry packaging theorem:
decoded code yields concrete spec predicate (clause + payload-shape) for all constructors. -/
theorem checkBytes_parseErrorCode?_concrete_spec_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ConcreteSpecPredicate code := by
  intro h_code
  exact DB.parseErrorCode?_concrete_spec_sound (s := checkBytes arr config) code h_code

/-- Canonical all-code parser-entry semantic packaging theorem:
decoded code yields concrete semantic clause predicate for all constructors. -/
theorem checkBytes_parseErrorCode?_concrete_semantic_clause_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ConcreteSemanticClausePredicate code := by
  intro h_code
  exact DB.parseErrorCode?_concrete_semantic_clause_sound
    (s := checkBytes arr config) code h_code

/-- Canonical parser-entry rule-semantic soundness for any decoded code. -/
theorem checkBytes_parseErrorCode?_ruleSemantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).RuleSemanticViolation code := by
  intro h_code
  exact DB.parseErrorCode?_ruleSemantic_sound (s := checkBytes arr config) code h_code

/-- Canonical parser-entry rule+clause semantic soundness for any decoded code. -/
theorem checkBytes_parseErrorCode?_ruleClauseSemantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).RuleClauseSemanticViolation code := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) code h_code

theorem checkBytes_parseErrorCode?_invalidLabel_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).InvalidLabelViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .invalidLabel h_code
  simpa [DB.RuleSemanticViolation, DB.InvalidLabelViolation] using h_rule

theorem checkBytes_parseErrorCode?_duplicateDisjointVariable_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).DuplicateDisjointVariableViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .duplicateDisjointVariable h_code
  simpa [DB.RuleSemanticViolation, DB.DuplicateDisjointVariableViolation] using h_rule

theorem checkBytes_parseErrorCode?_tokenNotInScope_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).TokenNotInScopeViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .tokenNotInScope h_code
  simpa [DB.RuleSemanticViolation, DB.TokenNotInScopeViolation] using h_rule

theorem checkBytes_parseErrorCode?_cantSaveEmptyStack_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .cantSaveEmptyStack →
    (checkBytes arr config).CompressedSaveViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .cantSaveEmptyStack h_code
  simpa [DB.RuleSemanticViolation, DB.CompressedSaveViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedBlock_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedBlock →
    (checkBytes arr config).DoneModeViolation .unclosedBlock := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedBlock h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedComment_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedComment →
    (checkBytes arr config).DoneModeViolation .unclosedComment := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedComment h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedConst_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedConst →
    (checkBytes arr config).DoneModeViolation .unclosedConst := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedConst h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedVar_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedVar →
    (checkBytes arr config).DoneModeViolation .unclosedVar := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedVar h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedDjvars_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedDjvars →
    (checkBytes arr config).DoneModeViolation .unclosedDjvars := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedDjvars h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedFloat_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedFloat →
    (checkBytes arr config).DoneModeViolation .unclosedFloat := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedFloat h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedEss_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedEss →
    (checkBytes arr config).DoneModeViolation .unclosedEss := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedEss h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedAx_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedAx →
    (checkBytes arr config).DoneModeViolation .unclosedAx := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedAx h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedThm_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedThm →
    (checkBytes arr config).DoneModeViolation .unclosedThm := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedThm h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedProof_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedProof →
    (checkBytes arr config).DoneModeViolation .unclosedProof := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedProof h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

section AllCodeRuleClauseTheorems

theorem checkBytes_parseErrorCode?_cantSaveEmptyStack_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .cantSaveEmptyStack →
    (checkBytes arr config).RuleClauseSemanticViolation .cantSaveEmptyStack := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .cantSaveEmptyStack h_code

theorem checkBytes_parseErrorCode?_unclosedBlock_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedBlock →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedBlock := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedBlock h_code

theorem checkBytes_parseErrorCode?_unclosedComment_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedComment →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedComment := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedComment h_code

theorem checkBytes_parseErrorCode?_unclosedConst_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedConst →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedConst := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedConst h_code

theorem checkBytes_parseErrorCode?_unclosedVar_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedVar →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedVar := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedVar h_code

theorem checkBytes_parseErrorCode?_unclosedDjvars_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedDjvars →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedDjvars := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedDjvars h_code

theorem checkBytes_parseErrorCode?_unclosedFloat_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedFloat →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedFloat := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedFloat h_code

theorem checkBytes_parseErrorCode?_unclosedEss_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedEss →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedEss := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedEss h_code

theorem checkBytes_parseErrorCode?_unclosedAx_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedAx →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedAx := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedAx h_code

theorem checkBytes_parseErrorCode?_unclosedThm_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedThm →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedThm := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedThm h_code

theorem checkBytes_parseErrorCode?_notACommand_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .notACommand →
    (checkBytes arr config).RuleClauseSemanticViolation .notACommand := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .notACommand h_code

theorem checkBytes_parseErrorCode?_unclosedProof_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedProof →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedProof := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedProof h_code

theorem checkBytes_parseErrorCode?_cantPopGlobalScope_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .cantPopGlobalScope →
    (checkBytes arr config).RuleClauseSemanticViolation .cantPopGlobalScope := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .cantPopGlobalScope h_code

theorem checkBytes_parseErrorCode?_constMustBeOutermost_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .constMustBeOutermost →
    (checkBytes arr config).RuleClauseSemanticViolation .constMustBeOutermost := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .constMustBeOutermost h_code

theorem checkBytes_parseErrorCode?_duplicateSymbolOrAssert_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateSymbolOrAssert →
    (checkBytes arr config).RuleClauseSemanticViolation .duplicateSymbolOrAssert := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .duplicateSymbolOrAssert h_code

theorem checkBytes_parseErrorCode?_firstSymbolNotConstant_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .firstSymbolNotConstant →
    (checkBytes arr config).RuleClauseSemanticViolation .firstSymbolNotConstant := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .firstSymbolNotConstant h_code

theorem checkBytes_parseErrorCode?_hypothesisSymbolsNotInFrame_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .hypothesisSymbolsNotInFrame →
    (checkBytes arr config).RuleClauseSemanticViolation .hypothesisSymbolsNotInFrame := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .hypothesisSymbolsNotInFrame h_code

theorem checkBytes_parseErrorCode?_expectedConstantAndVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .expectedConstantAndVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .expectedConstantAndVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .expectedConstantAndVariable h_code

theorem checkBytes_parseErrorCode?_variableAlreadyHasFloatHyp_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .variableAlreadyHasFloatHyp →
    (checkBytes arr config).RuleClauseSemanticViolation .variableAlreadyHasFloatHyp := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .variableAlreadyHasFloatHyp h_code

theorem checkBytes_parseErrorCode?_stackFormulaNoConstantHead_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .stackFormulaNoConstantHead →
    (checkBytes arr config).RuleClauseSemanticViolation .stackFormulaNoConstantHead := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .stackFormulaNoConstantHead h_code

theorem checkBytes_parseErrorCode?_hypothesisNoConstantHead_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .hypothesisNoConstantHead →
    (checkBytes arr config).RuleClauseSemanticViolation .hypothesisNoConstantHead := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .hypothesisNoConstantHead h_code

theorem checkBytes_parseErrorCode?_typeErrorInSubstitution_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .typeErrorInSubstitution →
    (checkBytes arr config).RuleClauseSemanticViolation .typeErrorInSubstitution := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .typeErrorInSubstitution h_code

theorem checkBytes_parseErrorCode?_badTypecodeInSubstitution_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .badTypecodeInSubstitution →
    (checkBytes arr config).RuleClauseSemanticViolation .badTypecodeInSubstitution := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .badTypecodeInSubstitution h_code

theorem checkBytes_parseErrorCode?_duplicateFloatVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateFloatVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .duplicateFloatVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .duplicateFloatVariable h_code

theorem checkBytes_parseErrorCode?_disjointVariableViolation_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .disjointVariableViolation →
    (checkBytes arr config).RuleClauseSemanticViolation .disjointVariableViolation := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .disjointVariableViolation h_code

theorem checkBytes_parseErrorCode?_assertionNoConstantHead_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .assertionNoConstantHead →
    (checkBytes arr config).RuleClauseSemanticViolation .assertionNoConstantHead := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .assertionNoConstantHead h_code

theorem checkBytes_parseErrorCode?_assertionVarsNotInFrame_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .assertionVarsNotInFrame →
    (checkBytes arr config).RuleClauseSemanticViolation .assertionVarsNotInFrame := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .assertionVarsNotInFrame h_code

theorem checkBytes_parseErrorCode?_stackUnderflow_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .stackUnderflow →
    (checkBytes arr config).RuleClauseSemanticViolation .stackUnderflow := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .stackUnderflow h_code

theorem checkBytes_parseErrorCode?_proofBackrefIndexOutOfRange_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .proofBackrefIndexOutOfRange →
    (checkBytes arr config).RuleClauseSemanticViolation .proofBackrefIndexOutOfRange := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .proofBackrefIndexOutOfRange h_code

theorem checkBytes_parseErrorCode?_invalidLabel_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).RuleClauseSemanticViolation .invalidLabel := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .invalidLabel h_code

theorem checkBytes_parseErrorCode?_invalidMathString_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidMathString →
    (checkBytes arr config).RuleClauseSemanticViolation .invalidMathString := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .invalidMathString h_code

theorem checkBytes_parseErrorCode?_duplicateDisjointVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .duplicateDisjointVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .duplicateDisjointVariable h_code

theorem checkBytes_parseErrorCode?_tokenNotInScope_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).RuleClauseSemanticViolation .tokenNotInScope := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .tokenNotInScope h_code

theorem checkBytes_parseErrorCode?_tokenNotVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .tokenNotVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .tokenNotVariable h_code

theorem checkBytes_parseErrorCode?_unknownStepQuestionRejected_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unknownStepQuestionRejected →
    (checkBytes arr config).RuleClauseSemanticViolation .unknownStepQuestionRejected := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unknownStepQuestionRejected h_code

theorem checkBytes_parseErrorCode?_topLevelEssentialNotAllowed_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
    (checkBytes arr config).RuleClauseSemanticViolation .topLevelEssentialNotAllowed := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .topLevelEssentialNotAllowed h_code

theorem checkBytes_parseErrorCode?_proofParseError_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .proofParseError →
    (checkBytes arr config).RuleClauseSemanticViolation .proofParseError := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .proofParseError h_code

theorem checkBytes_parseErrorCode?_theoremMoreThanOneStackElement_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .theoremMoreThanOneStackElement →
    (checkBytes arr config).RuleClauseSemanticViolation .theoremMoreThanOneStackElement := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .theoremMoreThanOneStackElement h_code

theorem checkBytes_parseErrorCode?_theoremClaimMismatch_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .theoremClaimMismatch →
    (checkBytes arr config).RuleClauseSemanticViolation .theoremClaimMismatch := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .theoremClaimMismatch h_code

theorem checkBytes_parseErrorCode?_nestedCommentDelimiter_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .nestedCommentDelimiter →
    (checkBytes arr config).RuleClauseSemanticViolation .nestedCommentDelimiter := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .nestedCommentDelimiter h_code

theorem checkBytes_parseErrorCode?_tokenNotConstantOrVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .tokenNotConstantOrVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .tokenNotConstantOrVariable h_code

theorem checkBytes_parseErrorCode?_unknownStatementType_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unknownStatementType →
    (checkBytes arr config).RuleClauseSemanticViolation .unknownStatementType := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unknownStatementType h_code

theorem checkBytes_parseErrorCode?_internalIllFormedDatabaseAfterParse_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .internalIllFormedDatabaseAfterParse →
    (checkBytes arr config).RuleClauseSemanticViolation .internalIllFormedDatabaseAfterParse := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .internalIllFormedDatabaseAfterParse h_code

theorem checkBytes_parseErrorCode?_includeCycleDetected_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeCycleDetected →
    (checkBytes arr config).RuleClauseSemanticViolation .includeCycleDetected := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .includeCycleDetected h_code

theorem checkBytes_parseErrorCode?_includeInInnerScope_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
    (checkBytes arr config).RuleClauseSemanticViolation .includeInInnerScope := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .includeInInnerScope h_code

theorem checkBytes_parseErrorCode?_includeInsideStatement_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
    (checkBytes arr config).RuleClauseSemanticViolation .includeInsideStatement := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .includeInsideStatement h_code

theorem checkBytes_parseErrorCode?_includeExtractedEmptyPath_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeExtractedEmptyPath →
    (checkBytes arr config).RuleClauseSemanticViolation .includeExtractedEmptyPath := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .includeExtractedEmptyPath h_code

theorem checkBytes_parseErrorCode?_includeEmptyPathBeforeNormalization_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeEmptyPathBeforeNormalization →
    (checkBytes arr config).RuleClauseSemanticViolation .includeEmptyPathBeforeNormalization := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .includeEmptyPathBeforeNormalization h_code

theorem checkBytes_parseErrorCode?_includePathEmptyAfterNormalization_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includePathEmptyAfterNormalization →
    (checkBytes arr config).RuleClauseSemanticViolation .includePathEmptyAfterNormalization := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .includePathEmptyAfterNormalization h_code

theorem checkBytes_parseErrorCode?_includeReadFailure_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeReadFailure →
    (checkBytes arr config).RuleClauseSemanticViolation .includeReadFailure := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .includeReadFailure h_code

end AllCodeRuleClauseTheorems

section HighValueParseErrorClauseLinks

theorem parseErrorCode_specClause_invalidLabel :
    ParseErrorCode.specClause .invalidLabel = .sec4_2_1_labels := rfl

theorem parseErrorCode_specClause_duplicateDisjointVariable :
    ParseErrorCode.specClause .duplicateDisjointVariable = .sec4_2_4_djvars := rfl

theorem parseErrorCode_specClause_tokenNotInScope :
    ParseErrorCode.specClause .tokenNotInScope = .sec4_2_4_djvars := rfl

end HighValueParseErrorClauseLinks

section HighValueClausePredicates

theorem invalidLabel_violation_implies_sec4_2_1
    (s : DB) :
    s.InvalidLabelViolation →
    s.Sec4_2_1_LabelSyntaxViolation := by
  intro h
  simpa [DB.Sec4_2_1_LabelSyntaxViolation] using h

theorem duplicateDisjointVariable_violation_implies_sec4_2_4_duplicate
    (s : DB) :
    s.DuplicateDisjointVariableViolation →
    s.Sec4_2_4_DjvarsDuplicateViolation := by
  intro h
  simpa [DB.Sec4_2_4_DjvarsDuplicateViolation] using h

theorem tokenNotInScope_violation_implies_sec4_2_4_scope
    (s : DB) :
    s.TokenNotInScopeViolation →
    s.Sec4_2_4_DjvarsScopeViolation := by
  intro h
  simpa [DB.Sec4_2_4_DjvarsScopeViolation] using h

theorem checkBytes_invalidLabel_implies_sec4_2_1
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).Sec4_2_1_LabelSyntaxViolation := by
  intro h_code
  exact invalidLabel_violation_implies_sec4_2_1 (s := checkBytes arr config)
    (checkBytes_parseErrorCode?_invalidLabel_violation arr config h_code)

theorem checkBytes_duplicateDisjointVariable_implies_sec4_2_4_duplicate
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).Sec4_2_4_DjvarsDuplicateViolation := by
  intro h_code
  exact duplicateDisjointVariable_violation_implies_sec4_2_4_duplicate (s := checkBytes arr config)
    (checkBytes_parseErrorCode?_duplicateDisjointVariable_violation arr config h_code)

theorem checkBytes_tokenNotInScope_implies_sec4_2_4_scope
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).Sec4_2_4_DjvarsScopeViolation := by
  intro h_code
  exact tokenNotInScope_violation_implies_sec4_2_4_scope (s := checkBytes arr config)
    (checkBytes_parseErrorCode?_tokenNotInScope_violation arr config h_code)

end HighValueClausePredicates

/-- Concrete clause theorem for the `$d`-at-EOF parser error. -/
theorem checkBytes_unclosedDjvars_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedDjvars →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_4_djvars := by
  intro h_code
  exact ⟨.unclosedDjvars, h_code, rfl⟩

theorem checkBytes_invalidLabel_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_1_labels := by
  intro h_code
  exact ⟨.invalidLabel, h_code, rfl⟩

theorem checkBytes_duplicateDisjointVariable_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_4_djvars := by
  intro h_code
  exact ⟨.duplicateDisjointVariable, h_code, rfl⟩

theorem checkBytes_tokenNotInScope_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_4_djvars := by
  intro h_code
  exact ⟨.tokenNotInScope, h_code, rfl⟩

-- Preprocessor with include support
-- Processes $[ filename $] directives by recursively loading files
-- Handles self-includes and cycles per spec §4.1.2
-- In strict mode: validates includes are at outermost scope and not inside statements

-- Two sets track include state:
-- - `processing`: Files currently being processed (call stack) - for cycle detection
-- - `seen`: All files ever fully processed - for duplicate ignore
partial def scanIncludes (contents : ByteArray) (fname : String) (config : ModeConfig := {}) :
    Except IncludeError (List (Sum ByteArray String)) := Id.run do
  let mut chunks : List (Sum ByteArray String) := []
  let mut buf : ByteArray := ByteArray.empty
  let mut i := 0
  let mut scopeDepth := 0  -- Track ${ $} nesting
  let mut inStatement := false  -- Track if we're inside a statement (after label before $.)
  let mut inComment := false  -- Track if we're inside a comment

  while i < contents.size do
    -- Track comment state (comments take precedence over everything else)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
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

    -- Track scope depth for strict mode validation
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == '{' then
        scopeDepth := scopeDepth + 1
      else if c == '}' then
        scopeDepth := max 0 (scopeDepth - 1)
      else if c == '.' then
        inStatement := false  -- Statement terminator

    -- Track if we're entering a statement (simplified: after $f, $e, $a, $p)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == 'f' || c == 'e' || c == 'a' || c == 'p' then
        inStatement := true

    -- Look for $[ token (only outside comments)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 && contents[i+1]! == '['.toUInt8 then
      -- Validate strict mode constraints (spec §4.1.2)
      -- Check: not in inner scope (unless config allows)
      if !config.allowIncludeInnerScope && scopeDepth > 0 then
        return .error (.inInnerScope i scopeDepth)
      -- Check: not inside a statement (unless config allows token splicing)
      if !config.allowTokenSplicing && inStatement then
        return .error (.insideStatement i)

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
        chunks := chunks.concat (.inl buf)
        buf := ByteArray.empty
      chunks := chunks.concat (.inr includeFile)
      continue
    else
      buf := buf.push contents[i]!
      i := i + 1

  if !buf.isEmpty then
    chunks := chunks.concat (.inl buf)
  return .ok chunks

partial def expandIncludes (fname : String) (processing seen : HashSet String)
    (config : ModeConfig := {}) :
    IO (Except IncludeError (ByteArray × HashSet String)) := do
  -- Canonicalize path (resolve ./ and ../)
  let canonPath ← IO.FS.realPath fname
  let canonStr := canonPath.toString

  -- Check for cycles (file is currently being processed)
  -- Per spec §4.1.2 + metamath.exe: reject self-includes and cycles
  -- Tests: metamath-test/tests/unit/test28_self_include.mm
  --        metamath-test/tests/unit/test44_include_cycle_main.mm
  if processing.contains canonStr then
    return .error (.cycleDetected canonStr)

  -- Check for duplicates (file was already fully processed)
  -- Per spec §4.1.2: duplicate includes are silently ignored
  -- Tests: metamath-test/tests/unit/test42_include_duplicate_main.mm
  --        metamath-test/tests/unit/test46_duplicate_include_main.mm
  if seen.contains canonStr then
    return .ok (ByteArray.empty, seen)

  let seen := seen.insert canonStr

  -- Read file
  let h ← Handle.mk fname IO.FS.Mode.read
  let rec readAll (acc : ByteArray) : IO ByteArray := do
    let buf ← h.read 4096
    if buf.isEmpty then return acc
    else readAll (acc ++ buf)
  let contents ← readAll ByteArray.empty

  match scanIncludes contents fname config with
  | .error err => return .error err
  | .ok chunks =>
      let mut result := ByteArray.empty
      let mut seen := seen  -- Make seen mutable to thread through
      for chunk in chunks do
        match chunk with
        | .inl bytes =>
            result := result ++ bytes
        | .inr includeFile =>
            -- Resolve relative path (relative to current file's directory)
            let baseDir := System.FilePath.parent fname |>.getD "."
            let fullPath := baseDir / includeFile

            -- Recursively expand the included file
            -- Pass `processing.insert canonStr` so the child knows we're currently processing this file
            try
              match ← expandIncludes fullPath.toString (processing.insert canonStr) seen config with
              | .ok (expanded, seen') =>
                seen := seen'  -- Thread the updated seen set through
                result := result ++ expanded
                -- Add whitespace to separate from next token
                result := result.push ' '.toUInt8
              | .error e => return .error e
            catch e =>
              return .error (.readFailure includeFile fullPath.toString e.toString)

      return .ok (result, seen)

partial def check (fname : String) (config : ModeConfig := {}) : IO DB := do
  -- Expand all includes recursively with config awareness
  -- processing = {} (call stack for cycle detection)
  -- seen = {} (all files ever processed for duplicate detection)
  match ← expandIncludes fname (HashSet.emptyWithCapacity 16) (HashSet.emptyWithCapacity 16) config with
  | .error err =>
    -- Return DB with error for include validation failures
    let initialDB : DB := { (default : DB) with config := config }
    return initialDB.mkErrorFromEvidence ⟨1, 1⟩ (.includeErr err)
  | .ok (processed, _) =>
    return checkBytes processed config

end Verify
end Metamath
