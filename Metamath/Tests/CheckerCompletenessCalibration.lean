import Metamath.CheckerCompleteness.Declare

/-!
# Calibration of dummy declarations and proof acceptance

Executable checks, run when this file is compiled: `#guard` evaluates each check and fails the
build if it is not `true`. They test the definitions of `Metamath.CheckerCompleteness` on concrete
parser states; they are tests, not proofs. `proofAcceptedB_eq_true_iff` proves that the Boolean
check decides `ProofAccepted`.
-/

set_option autoImplicit false

namespace Metamath.CheckerCompletenessCalibration

open Metamath.Verify Metamath.CheckerCompleteness

/-- `ProofAccepted`, computed. -/
def proofAcceptedB (s : ParserState) (pos : Pos) (label : String) (f : Verify.Formula)
    (proof : Array String) : Bool :=
  f.hasConstHead && !s.db.interrupt &&
    match s.db.trimFrame' f with
    | .error _ => false
    | .ok frImpl =>
        match proof.foldlM (fun pr l => s.db.stepNormal pr l)
            { s.db.mkProofState pos label f frImpl with ptp := .normal } with
        | .error _ => false
        | .ok pr => (s.finishProof pr).db.error?.isNone

theorem proofAcceptedB_eq_true_iff (s : ParserState) (pos : Pos) (label : String)
    (f : Verify.Formula) (proof : Array String) :
    proofAcceptedB s pos label f proof = true ↔ ProofAccepted s pos label f proof := by
  unfold proofAcceptedB ProofAccepted
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hhead, hint⟩, hrest⟩ := h
    refine ⟨hhead, hint, ?_⟩
    split at hrest
    · cases hrest
    · rename_i frImpl htrim
      split at hrest
      · cases hrest
      · rename_i pr hfold
        exact ⟨frImpl, pr, htrim, hfold, Option.isNone_iff_eq_none.mp hrest⟩
  · rintro ⟨hhead, hint, frImpl, pr, htrim, hfold, hfin⟩
    simp only [hhead, hint, htrim, hfold, hfin, Bool.and_true, Bool.not_false,
      Option.isNone_none]

/-- The state of a parser that has read `src` from the start. -/
def after (src : String) : ParserState :=
  ({ (default : ParserState) with db := { (default : DB) with config := {} } }).feedAll 0 src.toUTF8

def pos₀ : Pos := ⟨0, 0⟩

def claimC : Verify.Formula := #[.const "|-", .const "c"]

def isStart (s : ParserState) : Bool :=
  match s.tokp with
  | .start => true
  | _ => false

/-! ## A proof that needs a dummy variable

`ax` has the mandatory hypotheses `wx $f wff x` and `hx $e wff x`, and concludes `|- c`. A proof of
`|- c` must substitute a variable for `x`: a dummy variable of the theorem. -/

def axiomBlock : String :=
  "$c wff |- c $.\n${\n  $v x $.\n  wx $f wff x $.\n  hx $e wff x $.\n  ax $a |- c $.\n$}\n"

/-- The state before the `$p` statement of `th`, with `wy` active in the current block. -/
def beforeTh : ParserState := after (axiomBlock ++ "${\n  $v y $.\n  wy $f wff y $.\n")

-- A parser checkpoint before `th`: between statements, no error, `th` is a fresh label.
#guard isStart beforeTh && beforeTh.db.error?.isNone && (beforeTh.db.find? "th").isNone
-- With `wy` active, no dummy needs to be declared: the proof `wy wy ax` is accepted as is.
#guard proofAcceptedB (beforeTh.withDB (·.declareDummies pos₀ [])) pos₀ "th" claimC
  #["wy", "wy", "ax"]

/-- The same point without the block's `$v y` and `$f` statements. -/
def beforeThNoDummy : ParserState := after (axiomBlock ++ "${\n")

#guard isStart beforeThNoDummy && beforeThNoDummy.db.error?.isNone
-- Without a declared dummy the proof fails ...
#guard !proofAcceptedB beforeThNoDummy pos₀ "th" claimC #["wy", "wy", "ax"]
-- ... and after declaring one it is accepted.
#guard proofAcceptedB (beforeThNoDummy.withDB (·.declareDummies pos₀ [⟨"wff", "y", "wy"⟩]))
  pos₀ "th" claimC #["wy", "wy", "ax"]

/-! ## A dummy variable that needs a `$d` statement

`ax2` needs its two variables distinct. In the proof of `th2`, one of them is the frame variable
`z`, the other the dummy `u`: the dummy's `$d` pair with `z` is required. -/

def dvSource : String :=
  "$c wff |- c $.\n${\n  $v x w $.\n  wx $f wff x $.\n  ww $f wff w $.\n  hx $e wff x $.\n" ++
  "  hw $e wff w $.\n  $d x w $.\n  ax2 $a |- c $.\n$}\n" ++
  "${\n  $v z $.\n  wz $f wff z $.\n  hz $e wff z $.\n"

def beforeTh2 : ParserState := after dvSource

#guard isStart beforeTh2 && beforeTh2.db.error?.isNone
-- The dummy `u` with its `$d` pair against `z` (as declared by `declareDummies`): accepted.
#guard proofAcceptedB (beforeTh2.withDB (·.declareDummies pos₀ [⟨"wff", "u", "wu"⟩]))
  pos₀ "th2" claimC #["wz", "wu", "hz", "wu", "ax2"]
-- The dummy `u` declared without its `$d` pairs: rejected.
#guard !proofAcceptedB (beforeTh2.withDB (·.declareDummy pos₀ ⟨"wff", "u", "wu"⟩))
  pos₀ "th2" claimC #["wz", "wu", "hz", "wu", "ax2"]

end Metamath.CheckerCompletenessCalibration
