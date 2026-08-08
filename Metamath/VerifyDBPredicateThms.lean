import Metamath.Verify

namespace Metamath
namespace Verify
namespace DB

/-- `isSym` is exactly the disjunction the math-symbol gate splits on. -/
theorem isSym_eq_false_iff (db : DB) (tk : String) :
    db.isSym tk = false ↔ (db.isConst tk = false ∧ db.isVar tk = false) := by
  unfold isSym isConst isVar
  cases h : db.find? tk with
  | none => simp
  | some obj => cases obj <;> simp

/-- A name that is not a symbol at all is not an *active* variable either. -/
theorem isActiveVar_eq_false_of_isVar_eq_false
    (db : DB) (tk : String) (h : db.isVar tk = false) :
    db.isActiveVar tk = false := by
  unfold isActiveVar
  simp [h]

theorem mathSymbolViolation?_tokenNotConstantOrVariable_iff
    (db : DB) (tk : String) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) ↔
      db.isSym tk = false := by
  unfold mathSymbolViolation?
  cases h : db.find? tk with
  | none => simp [isSym, h]
  | some obj =>
      cases obj with
      | const _ => simp [isSym, h]
      | var _ =>
          by_cases h_a : db.isActiveVar tk <;>
            simp [isSym, isVar, isActiveVar, h] at *
      | hyp _ _ _ => simp [isSym, h]
      | assert _ _ _ => simp [isSym, h]

/-- The other math-string rejection: declared as a variable, but inactive. -/
theorem mathSymbolViolation?_inactiveMathSymbol_iff
    (db : DB) (tk : String) :
    db.mathSymbolViolation? tk = some (.inactiveMathSymbol tk) ↔
      (db.isVar tk = true ∧ db.isActiveVar tk = false) := by
  unfold mathSymbolViolation?
  cases h : db.find? tk with
  | none => simp [isVar, isActiveVar, h]
  | some obj =>
      cases obj with
      | const _ => simp [isVar, isActiveVar, h]
      | var _ =>
          by_cases h_a : db.isActiveVar tk <;>
            simp [isVar, isActiveVar, h] at *
      | hyp _ _ _ => simp [isVar, isActiveVar, h]
      | assert _ _ _ => simp [isVar, isActiveVar, h]

/-- The gate accepts exactly the active constants and active variables. -/
theorem mathSymbolViolation?_none_iff_active
    (db : DB) (tk : String) :
    db.mathSymbolViolation? tk = none ↔
      (db.isConst tk = true ∨ db.isActiveVar tk = true) := by
  unfold mathSymbolViolation?
  cases h : db.find? tk with
  | none => simp [isConst, isActiveVar, isVar, h]
  | some obj =>
      cases obj with
      | const _ => simp [isConst, h]
      | var _ =>
          by_cases h_a : db.isActiveVar tk <;> simp [isConst, h, h_a]
      | hyp _ _ _ => simp [isConst, isActiveVar, isVar, h]
      | assert _ _ _ => simp [isConst, isActiveVar, isVar, h]

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
  unfold DB.mathSymbolViolation?
  simp [h_find]

@[simp] theorem mathSymbolViolation?_of_find_hyp
    (db : DB) (tk : String) (fvar : Bool) (fmla : Formula) (lbl : String)
    (h_find : db.find? tk = some (.hyp fvar fmla lbl)) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) := by
  unfold DB.mathSymbolViolation?
  simp [h_find]

@[simp] theorem mathSymbolViolation?_of_find_assert
    (db : DB) (tk : String) (fmla : Formula) (fr : Frame) (lbl : String)
    (h_find : db.find? tk = some (.assert fmla fr lbl)) :
    db.mathSymbolViolation? tk = some (.tokenNotConstantOrVariable tk) := by
  unfold DB.mathSymbolViolation?
  simp [h_find]

/-- The `$d` gate separates the two ways a symbol can fail [MM §4.2.4]: this
one fires only when the name was never declared as a variable at all. -/
theorem djvarsScopeViolation?_tokenNotVariable_iff
    (db : DB) (tk : String) :
    db.djvarsScopeViolation? tk = some (.tokenNotVariable tk) ↔
      db.isVar tk = false := by
  unfold djvarsScopeViolation? DB.isActiveVar
  by_cases h_decl : db.isVar tk <;> simp [h_decl]

/-- The other `$d` failure: the name *is* a declared variable, but the block
that declared it has been popped, so it is no longer active. -/
theorem djvarsScopeViolation?_tokenNotInScope_iff
    (db : DB) (tk : String) :
    db.djvarsScopeViolation? tk = some (.tokenNotInScope tk) ↔
      (db.isVar tk = true ∧ db.isActiveVar tk = false) := by
  unfold djvarsScopeViolation?
  by_cases h_act : db.isActiveVar tk <;> by_cases h_decl : db.isVar tk <;>
    simp [h_act, h_decl]

/-- Either way, the gate fires exactly when the symbol is not an *active*
variable — declaration alone is not enough. -/
theorem djvarsScopeViolation?_isSome_iff
    (db : DB) (tk : String) :
    (db.djvarsScopeViolation? tk).isSome = true ↔ db.isActiveVar tk = false := by
  unfold djvarsScopeViolation? DB.isActiveVar
  by_cases h_act : db.isActiveVar tk <;> by_cases h_decl : db.isVar tk <;>
    simp_all [DB.isActiveVar]

theorem djvarsScopeViolation?_none_iff
    (db : DB) (tk : String) :
    db.djvarsScopeViolation? tk = none ↔ db.isActiveVar tk = true := by
  unfold djvarsScopeViolation?
  by_cases h_act : db.isActiveVar tk <;> by_cases h_decl : db.isVar tk <;>
    simp [h_act, h_decl]

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
    · simp [h_no_prior_err, h_no_dup]
  | var s =>
    -- The registry is consulted first, so a fresh name takes the insert
    -- branch directly; no activity reasoning is needed here.
    simp [h_no_prior_err, h_no_dup]
  | hyp ess f s =>
    simp [h_no_prior_err, h_no_dup]
  | assert f frame s =>
    simp [h_no_prior_err, h_no_dup]

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
