import Std.Data.HashMap
import Std.Data.HashSet
import Metamath.ByteSliceCompat

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
  c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\r'.toUInt8 || c == '\t'.toUInt8

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
  deriving Inhabited

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

namespace ProofState

def push (pr : ProofState) (f : Formula) : ProofState :=
  { pr with stack := pr.stack.push f }

def pushHeap (pr : ProofState) (el : HeapEl) : ProofState :=
  { pr with heap := pr.heap.push el }

def save (pr : ProofState) : Except String ProofState :=
  if let some f := pr.stack.back? then
    pure <| pr.pushHeap (.fmla f)
  else
    throw "can't save empty stack"

end ProofState

inductive Error
  | error (pos : Pos) (msg : String)
  | ax (pos : Pos) (l : String) (f : Formula) (fr : Frame)
  | thm (pos : Pos) (l : String) (f : Formula) (fr : Frame)

structure Interrupt where
  e : Error
  idx : Nat

structure DB where
  frame : Frame
  scopes : Array (Nat × Nat)
  objects : HashMap String Object
  interrupt : Bool
  error? : Option Interrupt
  config : ModeConfig := {}
  deriving Inhabited

namespace DB

@[inline] def error (s : DB) : Bool := s.error?.isSome

/-- Default config is zar (all defaults) -/
@[simp] theorem default_config : (default : DB).config = {} := rfl

def mkError (s : DB) (pos : Pos) (msg : String) : DB :=
  { s with error? := some ⟨.error pos msg, default⟩ }

@[simp] theorem mkError_config (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).config = s.config := rfl

@[simp] theorem mkError_error (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).error = true := rfl

@[simp] theorem mkError_error?_isSome (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).error?.isSome = true := rfl

def pushScope (s : DB) : DB :=
  { s with scopes := s.scopes.push s.frame.size }

@[simp] theorem pushScope_config (s : DB) : (s.pushScope).config = s.config := rfl

def popScope (pos : Pos) (db : DB) : DB :=
  if let some sc := db.scopes.back? then
    { db with frame := db.frame.shrink sc, scopes := db.scopes.pop }
  else
    db.mkError pos "can't pop global scope"

@[simp] theorem popScope_config (pos : Pos) (s : DB) : (s.popScope pos).config = s.config := by
  unfold popScope
  cases h : s.scopes.back? <;> simp [DB.mkError_config]

def find? (db : DB) (l : String) : Option Object := db.objects[l]?

def isConst (db : DB) (tk : String) : Bool :=
  if let some (.const _) := db.find? tk then true else false

def isVar (db : DB) (tk : String) : Bool :=
  if let some (.var _) := db.find? tk then true else false

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
      db.mkError pos s!"$c must be in outermost block (spec Section 4.2.8)"
    else db
  | _ => db
  if db.error then db else
  if let some o := db.find? l then
    let ok : Bool := match o with
    | .var _ => if let .var _ := obj l then true else false
    | _ => false
    if ok then db else db.mkError pos s!"duplicate symbol/assert {l}"
  else
    { db with objects := db.objects.insert l (obj l) }

/-- `insert` preserves `config`. -/
@[simp] theorem insert_config (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).config = db.config := by
  unfold insert
  -- All branches either return db with config intact, or mkError which preserves config,
  -- or construct a new DB with explicit config := db.config
  repeat (first | split | simp [DB.mkError_config, DB.mkError_error] | rfl)

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

def insertHypChecks (db : DB) (pos : Pos) (ess : Bool) (f : Formula) : DB :=
  -- Validate basic formula shape (used by parser invariants)
  let db := if f.hasConstHead then db else db.mkError pos "first symbol is not a constant"
  if db.error then db else
  let db :=
    if ess then db
    else if f.isFloatShape then db
    else db.mkError pos "expected a constant and a variable"
  if db.error then db else
  -- For $f statements (ess = false), check that no other $f exists for this variable
  -- Exe mode allows duplicate $f (test15, test16)
  if !ess && f.size >= 2 then
    let v := f[1]!.value
    if !db.config.allowDuplicateFloat && db.floatVarOccursInFrame v then
      db.mkError pos s!"variable {v} already has $f hypothesis"
    else db
  else db

@[simp] theorem insertHypChecks_config (db : DB) (pos : Pos) (ess : Bool) (f : Formula) :
    (db.insertHypChecks pos ess f).config = db.config := by
  unfold insertHypChecks
  -- `mkError` preserves config, and no branch assigns to `config`.
  repeat (first | split | simp [DB.error, DB.mkError_config, DB.mkError_error] | rfl)

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

def trimFrame' (db : DB) (fmla : Formula) : Except String Frame :=
  let (ok, fr) := db.trimFrame fmla
  if ok then pure fr
  else throw s!"out of order hypotheses in frame"

def insertAxiom (db : DB) (pos : Pos) (l : String) (fmla : Formula) : DB :=
  let db := if fmla.hasConstHead then db else db.mkError pos "first symbol is not a constant"
  if db.error then db
  else
    match db.trimFrame' fmla with
    | .ok fr =>
      if db.interrupt then { db with error? := some ⟨.ax pos l fmla fr, default⟩ }
      else db.insert pos l (.assert fmla fr)
    | .error msg => db.mkError pos msg

@[simp] theorem insertAxiom_config (db : DB) (pos : Pos) (l : String) (fmla : Formula) :
    (db.insertAxiom pos l fmla).config = db.config := by
  unfold insertAxiom
  by_cases h_head : fmla.hasConstHead
  · simp only [h_head, ↓reduceIte, DB.error]
    split  -- split on db.error?.isSome
    · simp  -- error case: return db unchanged
    · -- no error, split on trimFrame' result
      cases h_trim : db.trimFrame' fmla with
      | error msg => simp [DB.mkError_config]
      | ok fr =>
        simp only []
        split  -- split on db.interrupt
        · simp  -- interrupt: set error? with same config
        · simp [DB.insert_config]  -- normal: insert preserves config
  · -- hasConstHead = false: mkError sets error, so returns the errored db
    simp only [h_head, Bool.false_eq_true, ↓reduceIte, DB.mkError_error, DB.mkError_config]

def mkProofState (_db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    ProofState := Id.run do
  ⟨pos, l, fmla, fr, #[], #[], .start⟩

def preload (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (.hyp _ f _) =>
      -- Check db.frame (all active hypotheses in scope), NOT pr.frame (trimmed mandatory)
      if l ∈ db.frame.hyps.toList then
        return pr.pushHeap (.fmla f)
      else
        throw s!"hypothesis {l} not in database scope"
  | some (.assert f fr _) => return pr.pushHeap (.assert f fr)
  | _ => throw s!"statement {l} not found"

/-- Pre-populate heap with mandatory hypotheses for compressed proof format.
    Per spec Appendix B: "the order of the mandatory hypotheses of the statement
    being proved must not be changed if the compressed proof format is used"
    Test: metamath-test/tests/unit/test33_compressed_proof_stack_underflow.mm -/
def preloadMandatoryHyps (db : DB) (pr : ProofState) : Except String ProofState := do
  let mut pr := pr
  for lbl in pr.frame.hyps do
    match db.find? lbl with
    | some (.hyp _ f _) => pr := pr.pushHeap (.fmla f)
    | _ => throw s!"mandatory hypothesis {lbl} not found in database"
  return pr

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

variable (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) in
def checkHyp (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(
      let thm {a b n} : i < a → n + a = b → n + i < b
      | h, rfl => Nat.add_lt_add_left h _
      thm h off.2)
    if !val.hasConstHead then
      throw "stack formula has no constant head"
    else if let some (.hyp ess f _) := db.find? hyps[i] then
      if ess then
        if !f.hasConstHead then
          throw "hypothesis has no constant head"
        else if !formulaSymsRespectFrame db f (Verify.Frame.mk #[] hyps) then
          throw "hypothesis symbols not in frame"
        else if f[0]! == val[0]! then
          if (← f.subst subst) == val then
            checkHyp (i+1) subst
          else throw "type error in substitution"
        else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
      else
        if !f.isFloatShape then
          throw "expected a constant and a variable"
        else if f[0]! == val[0]! then
          if subst.contains f[1]!.value then
            throw "duplicate float variable"
          else
            checkHyp (i+1) (subst.insert f[1]!.value val)
        else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
    else
      throw s!"hypothesis {hyps[i]} not found"
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
    .error "stack formula has no constant head"
  else if !f.hasConstHead then
    .error "hypothesis has no constant head"
  else if !formulaSymsRespectFrame db f (Verify.Frame.mk #[] hyps) then
    .error "hypothesis symbols not in frame"
  else if f[0]! == stack[off.1 + i]![0]! then
    match f.subst σ with
    | .ok s =>
        if s == stack[off.1 + i]! then
          checkHyp db hyps stack off (i+1) σ
        else
          .error "type error in substitution"
    | .error e => .error e
  else
    .error (s!"bad typecode in substitution {hyps[i]}: {f} / {stack[off.1 + i]!}") := by
  -- Use rw to unfold only the LHS
  rw [checkHyp]
  simp [h_i, h_find, -beq_iff_eq]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx, bind, Except.bind, -beq_iff_eq]
  -- After all simplifications, LHS and RHS are structurally identical
  -- Just need to handle the nested if-then-else and match cases
  split
  · -- Case: stack formula has no constant head
    rfl
  · -- Case: stack formula has constant head
    split
    · -- Case: hypothesis has no constant head
      rfl
    · -- Case: hypothesis has constant head
      split
      · -- Case: hypothesis symbols not in frame
        rfl
      · -- Case: hypothesis symbols in frame
        split
        · -- Case: typecode check passes
          split
          · -- Case: subst returns error
            rename_i err heq
            simp [heq]
          · -- Case: subst returns ok
            rename_i val heq
            simp [heq]
            split <;> rfl
        · -- Case: typecode check fails
          rfl

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
    .error "stack formula has no constant head"
  else if !f.isFloatShape then
    .error "expected a constant and a variable"
  else if f[0]! == stack[off.1 + i]![0]! then
    if σ.contains f[1]!.value then
      .error "duplicate float variable"
    else
      checkHyp db hyps stack off (i+1) (σ.insert f[1]!.value (stack[off.1 + i]!))
  else
    .error (s!"bad typecode in substitution {hyps[i]}: {f} / {stack[off.1 + i]!}") := by
  rw [checkHyp]  -- KEY: Use rw not unfold to avoid expanding RHS recursive calls
  simp [h_i, h_find, -beq_iff_eq]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx, -beq_iff_eq]
  -- Float case: simpler than essential case, no do-notation to reduce
  split
  · -- Case: stack formula has no constant head
    rfl
  · -- Case: stack formula has constant head
    split
    · -- Case: bad float shape
      rfl
    · -- Case: float shape ok
      split
      · -- Case: typecode check passes
        split <;> rfl
      · -- Case: typecode check fails
        rfl

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
    (subst : HashMap String Formula) : Except String Unit :=
  if dvCheckBool vars djTarget djSource subst then
    Except.ok ()
  else
    Except.error "disjoint variable violation"

def stepAssert (db : DB) (pr : ProofState) (f : Formula) : Frame → Except String ProofState
  | fr@⟨dj, hyps⟩ => do
    if h : hyps.size ≤ pr.stack.size then
      if !f.hasConstHead then
        throw "assertion has no constant head"
      else if !formulaSymsRespectFrame db f fr then
        throw "assertion variables not in frame"
      else
        let off : {off // off + hyps.size = pr.stack.size} :=
          ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h⟩
        let subst ← checkHyp db hyps pr.stack off 0 ∅
        let vars := frameFloatVars db pr.frame
        dvCheck vars pr.frame.dj dj subst
        let concl ← f.subst subst
        pure { pr with stack := (pr.stack.shrink off).push concl }
    else throw "stack underflow"

def stepNormal (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (.hyp ess f _) =>
      -- Check db.frame (all active hypotheses in scope), NOT pr.frame (trimmed mandatory)
      if l ∈ db.frame.hyps.toList then
        if ess then
          if !f.hasConstHead then
            throw "hypothesis has no constant head"
          else
            return pr.push f
        else
          if !f.isFloatShape then
            throw "expected a constant and a variable"
          else
            return pr.push f
      else
        throw s!"hypothesis {l} not in database scope"
  | some (.assert f fr _) => db.stepAssert pr f fr
  | _ => throw s!"statement {l} not found"

def stepProof (db : DB) (pr : ProofState) (i : Nat) : Except String ProofState :=
  match pr.heap[i]? with
  | none => throw "proof backref index out of range"
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

@[simp] theorem mkError_db_config (s : ParserState) (pos : Pos) (msg : String) :
    (s.mkError pos msg).db.config = s.db.config := by
  simp [ParserState.mkError, ParserState.withDB]

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
      simp [hs, h_err]
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e <;> simp [hs, h_err, ParserState.withDB]

def label (s : ParserState) (pos : Pos) (tk : ByteSlice) : ParserState :=
  let (ok, tk) := toLabel tk
  if ok then { s with tokp := .label pos tk }
  else s.mkError pos s!"invalid label '{tk}'"

@[simp] theorem label_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    (s.label pos tk).db.config = s.db.config := by
  unfold ParserState.label
  -- Split on the if condition (ok = true)
  split <;> split <;> simp [ParserState.mkError_db_config]

def withMath (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) : ParserState :=
  let (ok, tk) := toMath tk
  if !ok then s.mkError pos s!"invalid math string '{tk}'" else
  f s tk

@[simp] theorem withMath_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState)
    (hf : ∀ tk', (f s tk').db.config = s.db.config) :
    (s.withMath pos tk f).db.config = s.db.config := by
  unfold ParserState.withMath
  split
  · -- Let binding for (ok, tk)
    split
    · simp [ParserState.mkError_db_config]  -- !ok case
    · exact hf _  -- ok case

-- Proof-friendly djvars loop (recursive, avoids forIn elaboration).
def djvars_loop_aux (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) (i : Nat) : ParserState :=
  if h : i < arr.size then
    let tk1 := arr[i]
    if tk1 == tk then
      s.mkError pos s!"duplicate disjoint variable {tk}"
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
      have : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simpa [hs] using this
    simp [djvars_loop_aux, hi]
  · intro m ih i s hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      ·
        have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        have : False := by
          -- `hs` says `arr.size - i = Nat.succ m`, contradicting `hz`.
          simpa [hz] using hs
        exact False.elim this
    -- Split on duplicate variable.
    have hs' : arr.size - (i + 1) = m := by
      -- `arr.size - (i+1) = pred (arr.size - i)` and `pred (succ m) = m`.
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    -- Unfold one step and discharge each branch.
    unfold djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    split  -- split on arr[i] == tk
    · -- duplicate case: mkError preserves config
      simp [ParserState.mkError_db_config]
    · -- non-duplicate: recurse, and `withDB`/`withDJ` preserve config
      have h_cfg : (s.withDB (fun db => db.withDJ fun dj => dj.push (if arr[i] < tk then (arr[i], tk) else (tk, arr[i])))).db.config = s.db.config := by
        simp [ParserState.withDB, DB.withDJ_config]
      -- Apply IH on the recursive call and rewrite the state's config back to `s`.
      simpa [h_cfg] using ih (i + 1) _ hs'

def djvars_loop (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) : ParserState :=
  if s.db.isVar tk then
    djvars_loop_aux arr s pos tk 0
  else
    s.mkError pos s!"{tk} is not a variable"

@[simp] theorem djvars_loop_db_config (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String) :
    (djvars_loop arr s pos tk).db.config = s.db.config := by
  unfold djvars_loop
  by_cases h : s.db.isVar tk <;> simp [h, ParserState.mkError_db_config, djvars_loop_aux_db_config]

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
    · simp [h_ok, ParserState.mkError_db_config]
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
    Except String (List CompressedAction × Nat) := do
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
      throw "proof parse error"
  return (acts.reverse, chr)

def applyCompressedActions (db : DB) (pr : ProofState) (acts : List CompressedAction) :
    Except String ProofState :=
  acts.foldlM (fun pr act =>
    match act with
    | .step n =>
        db.stepProof pr n
    | .save =>
        -- Per spec Appendix B: Z saves current stack top to heap for reuse
        -- Test: metamath-test/tests/core/small/out-of-range-saved-step-bad1.mm
        pr.save
    | .unknown =>
        -- Per spec §4.4.6: ? marks incomplete proof step, verifier should accept
        -- Test: metamath-test/tests/unit/test30_qmark_in_compressed_proof.mm
        -- Knife mode rejects unknown steps (stricter policy)
        if db.config.rejectUnknownSteps then
          throw "unknown step '?' not allowed (config rejects incomplete proofs)"
        else
          pure (pr.push pr.fmla)
    ) pr

def feedTokens (s : ParserState) (arr : Array Sym) : TokensParser → ParserState
  | ⟨k, pos, l⟩ => withAt l fun _ => Id.run do
    unless Formula.hasConstHead arr do
      return s.mkError pos "first symbol is not a constant"
    match k with
    | .float =>
      unless Formula.isFloatShape arr do
        return s.mkError pos "expected a constant and a variable"
      let s := s.withDB fun db => db.insertHyp pos l false arr
      pure { s with tokp := .start }
    | .ess =>
      -- Knife mode rejects top-level $e (stricter policy)
      -- Test: metamath-test/tests/unit/test67_toplevel_essential.mm
      if s.db.config.rejectToplevelEss && s.db.scopes.size == 0 then
        return s.mkError pos "top-level $e not allowed (config requires $e inside blocks)"
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
      | .error msg => s.mkError pos msg

@[simp] theorem feedTokens_db_config (s : ParserState) (arr : Array Sym) (p : TokensParser) :
    (s.feedTokens arr p).db.config = s.db.config := by
  cases p with
  | mk k pos l =>
      -- `withAt` only rewrites error messages; it doesn't touch the DB config.
      unfold ParserState.feedTokens
      simp only [ParserState.withAt_db_config, ParserState.Id_run_db_config]
      -- Split on all conditions and handle each case
      repeat (first | split | simp [ParserState.mkError_db_config, ParserState.withDB, DB.insertHyp_config,
        DB.insertAxiom_config, ParserState.resumeThm_db_config, ParserState.pure_db_config] | rfl)

def feedProof (s : ParserState) (tk : ByteSlice) (pr : ProofState) : ParserState :=
  withAt pr.label fun _ =>
    match go pr with
    | .ok pr => { s with tokp := .proof pr }
    | .error msg => s.mkError pr.pos msg
where
  goNormal (pr : ProofState) :=
    -- Per spec §4.4.6: "A proof may contain a ? in place of a label to indicate
    -- an unknown step. A proof verifier may ignore any proof containing ? but
    -- should warn the user that the proof is incomplete."
    -- Test: metamath-test/tests/unit/test20_unknown_step_qmark_(should_accept_with_warning).mm
    -- Knife mode rejects unknown steps (stricter policy)
    if tk.eqArray "?".toAscii then
      if s.db.config.rejectUnknownSteps then
        throw "unknown step '?' not allowed (config rejects incomplete proofs)"
      else
        pure (pr.push pr.fmla)
    else
      let (ok, tk) := toLabel tk
      if ok then s.db.stepNormal pr tk
      else throw s!"invalid label '{tk}'"
  go (pr : ProofState) : Except String ProofState := do
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
        else throw s!"invalid label '{tk}'"
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
  split <;> simp [ParserState.mkError_db_config]

def finishProof (s : ParserState) : ProofState → ParserState
  | ⟨pos, l, fmla, fr, _, stack, ptp⟩ => withAt l fun _ => Id.run do
    let s := { s with tokp := .start }
    match ptp with
    | .compressed 0 => ()
    | .normal => ()
    | _ => return s.mkError pos "proof parse error"
    unless stack.size == 1 do
      return s.mkError pos "more than one element on stack"
    unless stack[0]! == fmla do
      return s.mkError pos "theorem does not prove what it claims"
    s.withDB fun db => db.insert pos l (.assert fmla fr)

@[simp] theorem finishProof_db_config (s : ParserState) (pr : ProofState) :
    (s.finishProof pr).db.config = s.db.config := by
  cases pr with
  | mk pos l fmla fr heap stack ptp =>
      unfold ParserState.finishProof
      simp only [ParserState.withAt_db_config, Id.run]
      -- The function returns either mkError or insert via withDB; all preserve config
      cases ptp with
      | start => simp [ParserState.mkError_db_config]
      | preload => simp [ParserState.mkError_db_config]
      | normal =>
          simp only [Pure.pure, Bind.bind]
          split
          · split <;> simp [ParserState.mkError_db_config, ParserState.withDB, DB.insert_config]
          · simp [ParserState.mkError_db_config]
      | compressed chr =>
          simp only [↓reduceDIte, Pure.pure, Bind.bind]
          split
          · -- Case h_1: compressed 0
            split
            · split <;> simp [ParserState.mkError_db_config, ParserState.withDB, DB.insert_config]
            · simp [ParserState.mkError_db_config]
          · -- Case h_2: normal (impossible - just use simp)
            split
            · split <;> simp [ParserState.mkError_db_config, ParserState.withDB, DB.insert_config]
            · simp [ParserState.mkError_db_config]
          · -- Case h_3: other (chr ≠ 0) - returns mkError
            simp [ParserState.mkError_db_config]

def feedToken (s : ParserState) (pos : Nat) (tk : ByteSlice) : ParserState :=
  let pos := s.mkPos pos
  match s.tokp with
  | .comment p =>
    if tk.eqArray "$)".toAscii then { s with tokp := p }
    else if tk.eqArray "$(".toAscii then
      -- Per spec §4.1.1: "comments may not contain the 2-character sequences $( or $)"
      -- Test: metamath-test/tests/unit/test03_nested_comment_delimiters.mm
      s.mkError pos "nested comment delimiter '$(' inside comment"
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
          | _ => return s.mkError pos s!"{tk} is not a constant or variable"
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
        | _ => s.mkError pos s!"unknown statement type {(toLabel tk).2}"
      else s.mkError pos s!"unknown statement type {(toLabel tk).2}"
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
      · split <;> simp [ParserState.mkError_db_config]
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
          · simp [ParserState.mkError_db_config]  -- h_3: error case
  | label pos' lab =>
      simp only []
      split
      · rfl  -- $( opens comment
      · -- Statement type or error
        split
        · split <;> simp [ParserState.mkError_db_config]  -- f/e/a/p or unknown
        · simp [ParserState.mkError_db_config]  -- invalid
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
      have : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simpa [hs] using this
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
          simpa [hz] using hs
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
      simpa [ParserState.feedAll, h] using
        (ParserState.feed_db_config (base := base) (arr := arr) (i := 0) (rs := FeedState.ws) (s := s))
  | token base' tk =>
      simpa [ParserState.feedAll, h] using
        (ParserState.feed_db_config (base := base) (arr := arr) (i := 0)
          (rs := FeedState.token (OldToken.old base' tk.start tk.byteArray)) (s := { s with charp := default }))

def done (s : ParserState) (base : Nat) : DB := Id.run do
  let mut s := s
  if let .token pos tk := s.charp then
    s := s.feedToken pos tk.toSlice
  let base := s.mkPos base
  let { db := db, tokp := tokp, ..} := s
  match tokp with
  | .start =>
    if db.scopes.size > 0 then
      db.mkError base "unclosed block (missing $})"
    else db
  | .comment _ => db.mkError base "unclosed comment"
  | .const => db.mkError base "unclosed $c"
  | .var => db.mkError base "unclosed $v"
  | .djvars _ => db.mkError base "unclosed $d"
  | .math _ p => match p.k with
    | .float => db.mkError base "unclosed $f"
    | .ess => db.mkError base "unclosed $e"
    | .ax => db.mkError base "unclosed $a"
    | .thm => db.mkError base "unclosed $p"
  | .label pos _ => db.mkError pos "not a command"
  | .proof _ => db.mkError base "unclosed $p proof"

@[simp] theorem done_config (s : ParserState) (base : Nat) :
    (s.done base).config = s.db.config := by
  cases h_charp : s.charp with
  | ws =>
      cases h_tokp : s.tokp with
      | start =>
          by_cases h_scopes : s.db.scopes.size > 0 <;>
            simp [ParserState.done, h_charp, h_tokp, h_scopes, DB.mkError_config, Id.run]
      | comment p =>
          simp [ParserState.done, h_charp, h_tokp, DB.mkError_config, Id.run]
      | const =>
          simp [ParserState.done, h_charp, h_tokp, DB.mkError_config, Id.run]
      | var =>
          simp [ParserState.done, h_charp, h_tokp, DB.mkError_config, Id.run]
      | djvars arr =>
          simp [ParserState.done, h_charp, h_tokp, DB.mkError_config, Id.run]
      | math a p =>
          cases h_k : p.k <;>
            simp [ParserState.done, h_charp, h_tokp, h_k, DB.mkError_config, Id.run]
      | label pos l =>
          simp [ParserState.done, h_charp, h_tokp, DB.mkError_config, Id.run]
      | proof pr =>
          simp [ParserState.done, h_charp, h_tokp, DB.mkError_config, Id.run]
  | token pos tk =>
      cases h_tokp : (s.feedToken pos tk.toSlice).tokp with
      | start =>
          by_cases h_scopes : (s.feedToken pos tk.toSlice).db.scopes.size > 0 <;>
            simp [ParserState.done, h_charp, h_tokp, h_scopes, ParserState.feedToken_db_config, DB.mkError_config, Id.run]
      | comment p =>
          simp [ParserState.done, h_charp, h_tokp, ParserState.feedToken_db_config, DB.mkError_config, Id.run]
      | const =>
          simp [ParserState.done, h_charp, h_tokp, ParserState.feedToken_db_config, DB.mkError_config, Id.run]
      | var =>
          simp [ParserState.done, h_charp, h_tokp, ParserState.feedToken_db_config, DB.mkError_config, Id.run]
      | djvars arr =>
          simp [ParserState.done, h_charp, h_tokp, ParserState.feedToken_db_config, DB.mkError_config, Id.run]
      | math a p =>
          cases h_k : p.k <;>
            simp [ParserState.done, h_charp, h_tokp, h_k, ParserState.feedToken_db_config, DB.mkError_config, Id.run]
      | label pos l =>
          simp [ParserState.done, h_charp, h_tokp, ParserState.feedToken_db_config, DB.mkError_config, Id.run]
      | proof pr =>
          simp [ParserState.done, h_charp, h_tokp, ParserState.feedToken_db_config, DB.mkError_config, Id.run]

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
    if db.config.allowDuplicateFloat || db.wellFormed? then
      db
    else
      db.mkError ⟨0, 0⟩ "internal error: ill-formed database after parse"
  else
    db

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
      simp only [h_wf, Bool.or_true, ↓reduceIte]
    · -- wellFormed? = false when not allowing dup sets error, contradicting h_ok
      have h_cond : ((checkBytesCore arr config).config.allowDuplicateFloat || (checkBytesCore arr config).wellFormed?) = false := by
        cases h : (checkBytesCore arr config).wellFormed? with
        | true => exact (h_wf h).elim
        | false => simp only [h_dup, Bool.false_or]
      simp only [h_cond, Bool.false_eq_true, ↓reduceIte, DB.mkError] at h_ok
      -- h_ok : some _ = none, which is a contradiction
      cases h_ok
  · simp [h_err] at h_ok

-- Preprocessor with include support
-- Processes $[ filename $] directives by recursively loading files
-- Handles self-includes and cycles per spec §4.1.2
-- In strict mode: validates includes are at outermost scope and not inside statements

-- Two sets track include state:
-- - `processing`: Files currently being processed (call stack) - for cycle detection
-- - `seen`: All files ever fully processed - for duplicate ignore
partial def expandIncludes (fname : String) (processing seen : HashSet String)
    (config : ModeConfig := {}) :
    IO (Except String (ByteArray × HashSet String)) := do
  -- Canonicalize path (resolve ./ and ../)
  let canonPath ← IO.FS.realPath fname
  let canonStr := canonPath.toString

  -- Check for cycles (file is currently being processed)
  -- Per spec §4.1.2 + metamath.exe: reject self-includes and cycles
  -- Tests: metamath-test/tests/unit/test28_self_include.mm
  --        metamath-test/tests/unit/test44_include_cycle_main.mm
  if processing.contains canonStr then
    return .error s!"include cycle detected: '{canonStr}' is already being processed"

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

  -- Process includes: find $[ ... $] and expand recursively
  let mut result := ByteArray.empty
  let mut seen := seen  -- Make seen mutable to thread through
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
        result := result.push contents[i]!
        result := result.push contents[i+1]!
        i := i + 2
        continue
      else if c == ')' then
        inComment := false
        result := result.push contents[i]!
        result := result.push contents[i+1]!
        i := i + 2
        continue

    -- Skip everything inside comments
    if inComment then
      result := result.push contents[i]!
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
        return .error s!"include in inner scope (config requires outermost scope only, spec §4.1.2)"
      -- Check: not inside a statement (unless config allows token splicing)
      if !config.allowTokenSplicing && inStatement then
        return .error s!"include inside statement (config forbids token splicing, spec §4.1.2)"

      i := i + 2
      -- Skip whitespace after $[
      while i < contents.size && (contents[i]! == ' '.toUInt8 || contents[i]! == '\n'.toUInt8 || contents[i]! == '\t'.toUInt8 || contents[i]! == '\r'.toUInt8) do
        i := i + 1

      -- Extract filename until $]
      let mut includePath := ByteArray.empty
      let startPos := i  -- Debug: save start position
      while i + 1 < contents.size && !(contents[i]! == '$'.toUInt8 && contents[i+1]! == ']'.toUInt8) do
        let c := contents[i]!
        if c != ' '.toUInt8 && c != '\n'.toUInt8 && c != '\t'.toUInt8 && c != '\r'.toUInt8 then
          includePath := includePath.push c
        i := i + 1
      -- Debug: check what we extracted
      if includePath.isEmpty && i > startPos then
        return .error s!"extracted empty path from position {startPos} to {i} in {fname}"

      -- Skip $]
      if i + 1 < contents.size then i := i + 2

      -- Convert includePath to String
      let mut includeFile := String.fromUTF8! includePath

      -- Debug: check extracted path before normalization
      if includeFile.isEmpty then
        return .error s!"extracted empty include path before normalization in {fname}"

      -- Normalize "./" prefix (FilePath doesn't handle it well)
      if includeFile.startsWith "./" then
        includeFile := (includeFile.drop 2).toString

      -- Check for empty path after normalization
      if includeFile.isEmpty then
        return .error s!"include path became empty after normalizing './' prefix (original was '{String.fromUTF8! includePath}') in {fname}"

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
        return .error s!"failed to read include file '{includeFile}' (resolved to '{fullPath}'): {e}"
    else
      result := result.push contents[i]!
      i := i + 1

  return .ok (result, seen)

partial def check (fname : String) (config : ModeConfig := {}) : IO DB := do
  -- Expand all includes recursively with config awareness
  -- processing = {} (call stack for cycle detection)
  -- seen = {} (all files ever processed for duplicate detection)
  match ← expandIncludes fname (HashSet.emptyWithCapacity 16) (HashSet.emptyWithCapacity 16) config with
  | .error msg =>
    -- Return DB with error for include validation failures
    let initialDB : DB := { (default : DB) with config := config }
    return initialDB.mkError ⟨1, 1⟩ msg
  | .ok (processed, _) =>
    return checkBytes processed config
