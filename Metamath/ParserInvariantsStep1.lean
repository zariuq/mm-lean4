import Metamath.Verify
import Metamath.WellFormedness
import Metamath.ParserCorrectness
import Metamath.DBLemmas

namespace Metamath.ParserInvariantsStep1

open Verify
open Metamath.WF
open Metamath.ParserCorrectness

/-- Helper: db.insert for .hyp implies freshness -/
theorem insert_hyp_implies_fresh
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_ok : (db.insert pos l (.hyp ess f)).error? = none) :
    db.find? l = none := by
  by_cases h_find : db.find? l = none
  · exact h_find
  · cases h_find' : db.find? l with
    | none =>
        cases h_find h_find'
    | some o =>
        cases h_err : db.error with
        | true =>
            have h_ok' : db.error? = none := by
              simpa [DB.insert, h_err] using h_ok
            have h_err' : db.error = false :=
              (Metamath.ParserBasics.no_error_iff db).1 h_ok'
            have : False := by
              have h_err'' := h_err'
              simp [h_err] at h_err''
            exact this.elim
        | false =>
            cases o with
            | const _ =>
                simp [DB.insert, h_err, h_find', DB.mkError] at h_ok
            | var _ =>
                simp [DB.insert, h_err, h_find', DB.mkError] at h_ok
            | hyp _ _ _ =>
                simp [DB.insert, h_err, h_find', DB.mkError] at h_ok
            | assert _ _ _ =>
                simp [DB.insert, h_err, h_find', DB.mkError] at h_ok

private theorem insertHypChecks_preserves_objects
    (db : DB) (pos : Pos) (ess : Bool) (f : Formula) :
    (DB.insertHypChecks db pos ess f).objects = db.objects := by
  unfold DB.insertHypChecks
  repeat (first | split | rfl | simp)

/-- Parser check: Verify.lean:feedTokens (lines 561-567)
    The parser enforces that all $f hypotheses have the form #[.const c, .var v]
    BEFORE calling insertHyp. -/
theorem feedTokens_validates_float
    (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String)
    (h_success : (s.feedTokens arr (TokensParser.mk .float pos l)).db.error? = none) :
    WellFormedFloat arr := by
  -- The parser guards the float branch with two checks; success forces both.
  have h_head : Formula.hasConstHead arr = true := by
    cases h_head : Formula.hasConstHead arr with
    | true => rfl
    | false =>
        have : False := by
          have h_success' := h_success
          simp [ParserState.feedTokens, ParserState.withAt, ParserState.mkError, ParserState.withDB,
            DB.mkError, h_head] at h_success'
        exact this.elim
  have h_shape : Formula.isFloatShape arr = true := by
    cases h_shape : Formula.isFloatShape arr with
    | true => rfl
    | false =>
        have : False := by
          have h_success' := h_success
          simp [ParserState.feedTokens, ParserState.withAt, ParserState.mkError, ParserState.withDB,
            DB.mkError, h_head, h_shape] at h_success'
        exact this.elim

  -- Unfold the shape check to extract the concrete float structure.
  have h_size : arr.size = 2 := by
    by_cases h_size : arr.size = 2
    · exact h_size
    · have : False := by
        have h_shape' := h_shape
        simp [Formula.isFloatShape, h_size] at h_shape'
      exact this.elim
  have h_shape' :
      (match arr[0]!, arr[1]! with
        | Sym.const _, Sym.var _ => true
        | _, _ => false) = true := by
    simpa [Formula.isFloatShape, h_size] using h_shape
  cases h0 : arr[0]! with
  | const c =>
      cases h1 : arr[1]! with
      | var v =>
          exact ⟨h_size, c, v, h0, h1⟩
      | const c' =>
          have : False := by
            simp [h0, h1] at h_shape'
          exact this.elim
  | var v =>
      have : False := by
        cases h1 : arr[1]! <;> simp [h0, h1] at h_shape'
      exact this.elim

/-- insertHyp ensures label freshness (if it inserts). -/
theorem insertHyp_ensures_fresh_db
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_success : (db.insertHyp pos l ess f).error? = none) :
    db.find? l = none := by
  let db_after := DB.insertHypChecks db pos ess f
  have h_check_err : db_after.error = false := by
    cases h_err : db_after.error with
    | true =>
        have h_success' := h_success
        simp [DB.insertHyp, db_after, h_err] at h_success'
        have h_err_false : db_after.error = false :=
          (Metamath.ParserBasics.no_error_iff _).1 h_success'
        have : False := by
          have h_err_false' := h_err_false
          simp [h_err] at h_err_false'
        exact this.elim
    | false => rfl
  have h_insert_ok : (db_after.insert pos l (.hyp ess f)).error? = none := by
    cases h_ins_err : (db_after.insert pos l (.hyp ess f)).error with
    | true =>
        have h_success' := h_success
        simp [DB.insertHyp, db_after, h_check_err, h_ins_err] at h_success'
        have h_ins_err_false : (db_after.insert pos l (.hyp ess f)).error = false :=
          (Metamath.ParserBasics.no_error_iff _).1 h_success'
        have : False := by
          have h_ins_err_false' := h_ins_err_false
          simp [h_ins_err] at h_ins_err_false'
        exact this.elim
    | false =>
        exact (Metamath.ParserBasics.no_error_iff _).2 h_ins_err
  have h_fresh_after : db_after.find? l = none :=
    insert_hyp_implies_fresh db_after pos l ess f h_insert_ok
  have h_objects_eq : db_after.objects = db.objects := by
    simpa [db_after] using insertHypChecks_preserves_objects db pos ess f
  have h_find_eq : db_after.find? l = db.find? l := by
    simp [DB.find?, h_objects_eq]
  simpa [h_find_eq] using h_fresh_after

/-- General validation: feedTokens ensures any inserted formula has size > 0 and const head. -/
theorem feedTokens_validates_formula
    (s : ParserState) (arr : Array Sym) (p : TokensParser)
    (h_success : (s.feedTokens arr p).db.error? = none) :
    WellFormedFormula arr := by
  cases p with
  | mk k pos l =>
      -- Head check must pass for any tokens kind.
      have h_head : Formula.hasConstHead arr = true := by
        cases h_head : Formula.hasConstHead arr with
        | true => rfl
        | false =>
            have : False := by
              have h_success' := h_success
              simp [ParserState.feedTokens, ParserState.withAt, ParserState.mkError, ParserState.withDB,
                DB.mkError, h_head] at h_success'
            exact this.elim
      exact wellFormedFormula_of_hasConstHead h_head

/-- Composite theorem: feedTokens validates both essential and float hypotheses. -/
theorem feedTokens_validates_hyp
    (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String) (k : TokensKind)
    (h_success : (s.feedTokens arr (TokensParser.mk k pos l)).db.error? = none) :
    (k = .ess → WellFormedFormula arr) ∧ (k = .float → WellFormedFloat arr) := by
  constructor
  · intro _ -- k = .ess
    exact feedTokens_validates_formula s arr (TokensParser.mk k pos l) h_success
  · intro h_float
    rw [h_float] at h_success
    exact feedTokens_validates_float s arr pos l h_success

end Metamath.ParserInvariantsStep1
