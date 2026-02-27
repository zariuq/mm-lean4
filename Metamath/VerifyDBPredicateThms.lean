import Metamath.Verify

namespace Metamath
namespace Verify
namespace DB

theorem mathSymbolViolation?_tokenNotConstantOrVariable_iff
    (db : DB) (tk : String) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) ↔
      db.isSym tk = false := by
  unfold mathSymbolViolation?
  by_cases h_sym : db.isSym tk
  · simp [h_sym]
  · simp [h_sym]

theorem mathSymbolViolation?_tokenNotConstantOrVariable_implies_isSym_false
    (db : DB) (tk : String) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) →
      db.isSym tk = false := by
  intro h
  exact (mathSymbolViolation?_tokenNotConstantOrVariable_iff db tk).1 h

@[simp] theorem mathSymbolViolation?_of_find_none
    (db : DB) (tk : String)
    (h_find : db.find? tk = none) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) := by
  have h_sym : db.isSym tk = false := by
    unfold DB.isSym
    simp [h_find]
  unfold DB.mathSymbolViolation?
  simp [h_sym]

@[simp] theorem mathSymbolViolation?_of_find_hyp
    (db : DB) (tk : String) (fvar : Bool) (fmla : Formula) (lbl : String)
    (h_find : db.find? tk = some (.hyp fvar fmla lbl)) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) := by
  have h_sym : db.isSym tk = false := by
    unfold DB.isSym
    simp [h_find]
  unfold DB.mathSymbolViolation?
  simp [h_sym]

@[simp] theorem mathSymbolViolation?_of_find_assert
    (db : DB) (tk : String) (fmla : Formula) (fr : Frame) (lbl : String)
    (h_find : db.find? tk = some (.assert fmla fr lbl)) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) := by
  have h_sym : db.isSym tk = false := by
    unfold DB.isSym
    simp [h_find]
  unfold DB.mathSymbolViolation?
  simp [h_sym]

theorem djvarsScopeViolation?_tokenNotVariable_iff
    (db : DB) (tk : String) :
    db.djvarsScopeViolation? tk = some (.tokenNotVariable tk) ↔
      db.isVar tk = false := by
  unfold djvarsScopeViolation?
  by_cases h_var : db.isVar tk
  · simp [h_var]
  · simp [h_var]

theorem djvarsScopeViolation?_none_iff
    (db : DB) (tk : String) :
    db.djvarsScopeViolation? tk = none ↔ db.isVar tk = true := by
  unfold djvarsScopeViolation?
  by_cases h_var : db.isVar tk <;> simp [h_var]

theorem insert_no_dup_objects
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_prior_err : db.error = false)
    (h_no_dup : db.find? l = none)
    (h_no_err : (db.insert pos l obj).error = false) :
    (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  unfold insert
  cases h_obj : obj l with
  | const s =>
    simp only
    split
    · exfalso
      simp only [h_obj, insert, error] at h_no_err
      split at h_no_err
      · simp only [Option.isSome] at h_no_err
        contradiction
      · simp_all
    · simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | var s =>
    simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | hyp ess f s =>
    simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | assert f frame s =>
    simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]

theorem insert_find?_self
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_prior_err : db.error = false)
    (h_no_dup : db.find? l = none)
    (h_no_err : (db.insert pos l obj).error = false) :
    (db.insert pos l obj).find? l = some (obj l) := by
  simp only [find?, insert_no_dup_objects db pos l obj h_no_prior_err h_no_dup h_no_err]
  exact Std.HashMap.getElem?_insert_self

end DB
end Verify
end Metamath
