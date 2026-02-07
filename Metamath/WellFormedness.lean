/-
# Metamath.WellFormedness
Foundational well-formedness predicates that capture parser guarantees.
-/
import Std.Data.HashMap.Lemmas
import Metamath.Verify
import Metamath.ArrayListExt
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false


namespace Metamath
namespace WF
open Verify

/-- A formula is well-formed iff it is nonempty and its head is a constant. -/
def WellFormedFormula (f : Formula) : Prop :=
  0 < f.size ∧ ∃ c : String, f[0]! = Sym.const c

/-- A floating hypothesis formula has *exactly* the Metamath shape `$f C v`. -/
def WellFormedFloat (f : Formula) : Prop :=
  f.size = 2 ∧ ∃ c v : String, f[0]! = Sym.const c ∧ f[1]! = Sym.var v

/-- Extract the variable of a floating hypothesis (partial; used in uniqueness). -/
def floatVar? (f : Formula) : Option String :=
  if h : f.size = 2 then
    match f[1] with
    | .var v   => some v
    | _        => none
  else
    none

/-- Every label in a frame resolves to a hypothesis and its formula is well-formed. -/
def HypOK (db : DB) (label : String) : Prop :=
  ∃ ess f lbl,
    db.find? label = some (.hyp ess f lbl) ∧
    (ess = false → WellFormedFloat f) ∧
    (ess = true  → WellFormedFormula f)

/-- No two distinct $f-binders attach to the same variable in this frame. -/
def UniqueFloatVars (db : DB) (fr : Frame) : Prop :=
  ∀ (i j : Nat) (hi : i < fr.hyps.size) (hj : j < fr.hyps.size),
    i ≠ j →
    ∀ (fi fj : Formula) (lbli lblj : String),
      db.find? fr.hyps[i] = some (.hyp false fi lbli) →
      db.find? fr.hyps[j] = some (.hyp false fj lblj) →
      fi.size ≥ 2 → fj.size ≥ 2 →
      let vi := match fi[1]! with | .var v => v | _ => ""
      let vj := match fj[1]! with | .var v => v | _ => ""
      vi ≠ vj

/-- Frame well-formedness -/
def WellFormedFrame (db : DB) (fr : Frame) : Prop :=
  (∀ i (hi : i < fr.hyps.size), HypOK db fr.hyps[i]) ∧
  UniqueFloatVars db fr

/-- Database well-formedness -/
def WellFormedDB (db : DB) : Prop :=
  WellFormedFrame db db.frame ∧
  (∀ lbl obj, db.find? lbl = some obj →
    match obj with
    | .hyp ess f _   => (if ess then WellFormedFormula f else WellFormedFloat f)
    | .assert f fr _ => WellFormedFormula f ∧ WellFormedFrame db fr
    | .var v         => v = lbl  -- Invariant: var labels = var names
    | _              => True)

/-- A variable `v` is declared by some earlier floating hypothesis in the frame. -/
def FloatDeclaredBefore (db : DB) (fr : Frame) (i : Nat) (v : String) : Prop :=
  ∃ j : Nat, j < i ∧
    ∃ (f : Formula) (lbl : String),
      db.find? fr.hyps[j]! = some (.hyp false f lbl) ∧
      f.isFloatShape = true ∧
      f[1]! = Sym.var v

/-- A frame is well-scoped if:
1. Every essential hypothesis respects the frame's float variables
2. Every variable in an essential hypothesis is declared by an earlier float
3. DV pairs are ordered (v < w) and both variables are in the frame
-/
def WellScopedFrame (db : DB) (fr : Frame) : Prop :=
  (∀ i, i < fr.hyps.size →
    match db.find? fr.hyps[i]! with
    | some (.hyp true f _) =>
        DB.formulaSymsRespectFrame db f (Verify.Frame.mk #[] fr.hyps) = true ∧
        (∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db fr i v)
    | _ => True) ∧
  (∀ v w, (v, w) ∈ fr.dj.toList →
    v < w ∧
    v ∈ DB.frameFloatVars db fr ∧
    w ∈ DB.frameFloatVars db fr)

/-- All symbols in a formula are declared with the correct kind in the DB. -/
def FormulaSymbolsDeclared (db : DB) (f : Formula) : Prop :=
  ∀ s ∈ f.toList,
    match s with
    | .const c => db.isConst c = true
    | .var v => db.isVar v = true

/-- A database is well-scoped if all assertion frames are well-scoped
    and all assertion formulas respect their frames. -/
def WellScopedDB (db : DB) : Prop :=
  WellScopedFrame db db.frame ∧
  (∀ lbl obj, db.find? lbl = some obj →
    match obj with
    | .assert f fr _ =>
        WellScopedFrame db fr ∧
        DB.formulaSymsRespectFrame db f fr = true ∧
        FormulaSymbolsDeclared db f
    | .hyp _ f _ =>
        (lbl ∈ db.frame.hyps.toList → DB.formulaSymsRespectFrame db f db.frame = true) ∧
        FormulaSymbolsDeclared db f
    | _ => True)

/-- Well-scopedness plus scope snapshots: every stored scope prefix is well-scoped. -/
def WellScopedDBWithScopes (db : DB) : Prop :=
  WellScopedDB db ∧
  (∀ sc ∈ db.scopes.toList, WellScopedFrame db (db.frame.shrink sc))

theorem WellScopedDBWithScopes.toWellScopedDB {db : DB} :
    WellScopedDBWithScopes db → WellScopedDB db := by
  intro h
  exact h.1

theorem wellFormedFormula_of_hasConstHead {f : Formula} :
    f.hasConstHead = true → WellFormedFormula f := by
  intro h
  by_cases h_pos : 0 < f.size
  · cases h_head : f[0]! with
    | const c =>
        exact ⟨h_pos, ⟨c, h_head⟩⟩
    | var v =>
        have h_head' : f[0]'h_pos = Sym.var v := by
          have h_eq : f[0]! = f[0]'h_pos := by
            simpa using (Array.getBang_eq_get_nat f 0 h_pos)
          simpa [h_eq] using h_head
        have h' : f.hasConstHead = false := by
          simp [Formula.hasConstHead, h_pos, h_head']
        have : False := by
          have h'' := h'
          simp [h] at h''
        exact this.elim
  · have h' : f.hasConstHead = false := by
      simp [Formula.hasConstHead, h_pos]
    have : False := by
      have h'' := h'
      simp [h] at h''
    exact this.elim

theorem var_label_eq_name_of_db
    {db : DB} {lbl v : String}
    (h_db : WellFormedDB db)
    (h_find : db.find? lbl = some (Object.var v)) :
    v = lbl := by
  have h := h_db.2 lbl (Object.var v) h_find
  exact h

theorem isConst_not_isVar (db : DB) (c : String) :
    db.isConst c = true → db.isVar c = false := by
  intro h_const
  cases h_find : db.find? c with
  | none =>
      simp [DB.isConst, h_find] at h_const
  | some obj =>
      cases obj with
      | const _ =>
          simp [DB.isVar, h_find]
      | var _ =>
          simp [DB.isConst, h_find] at h_const
      | hyp _ _ _ =>
          simp [DB.isConst, h_find] at h_const
      | assert _ _ _ =>
          simp [DB.isConst, h_find] at h_const

-- frameFloatVars only depends on hyps, not dj
theorem frameFloatVars_hyps_only (db : DB) (dj1 dj2 : Array (String × String)) (hyps : Array String) :
    DB.frameFloatVars db (Frame.mk dj1 hyps) = DB.frameFloatVars db (Frame.mk dj2 hyps) := by
  simp only [DB.frameFloatVars]

theorem frameFloatVars_mk_eq (db : DB) (fr : Frame) :
    DB.frameFloatVars db fr = DB.frameFloatVars db (Frame.mk #[] fr.hyps) := by
  simp only [DB.frameFloatVars]

theorem frameFloatVars_mem_iff
    (db : DB) (hyps : Array String) (v : String) :
    v ∈ DB.frameFloatVars db (Frame.mk #[] hyps) ↔
      ∃ lbl f lbl',
        lbl ∈ hyps.toList ∧
        db.find? lbl = some (.hyp false f lbl') ∧
        f.isFloatShape = true ∧
        f[1]! = Sym.var v := by
  unfold DB.frameFloatVars
  constructor
  · intro h_mem
    rcases (List.mem_filterMap).1 h_mem with ⟨lbl, h_lbl_mem, h_some⟩
    cases h_find : db.find? lbl with
    | none =>
        simp [h_find] at h_some
    | some obj =>
        cases obj with
        | hyp ess f lbl' =>
            cases ess with
            | true =>
                simp [h_find] at h_some
            | false =>
                by_cases h_shape : f.isFloatShape
                · cases h_f1 : f[1]! with
                  | const _ =>
                      simp [h_find, h_shape, h_f1] at h_some
                  | var v' =>
                      have h_eq : v' = v := by
                        simpa [h_find, h_shape, h_f1] using h_some
                      subst h_eq
                      exact ⟨lbl, f, lbl', h_lbl_mem, h_find, h_shape, h_f1⟩
                · simp [h_find, h_shape] at h_some
        | _ =>
            simp [h_find] at h_some
  · intro h_ex
    rcases h_ex with ⟨lbl, f, lbl', h_lbl_mem, h_find, h_shape, h_f1⟩
    apply (List.mem_filterMap).2
    refine ⟨lbl, h_lbl_mem, ?_⟩
    simp [h_find, h_shape, h_f1]

-- General version using the above
theorem frameFloatVars_mem_iff' (db : DB) (fr : Frame) (v : String) :
    v ∈ DB.frameFloatVars db fr ↔
      ∃ lbl f lbl',
        lbl ∈ fr.hyps.toList ∧
        db.find? lbl = some (.hyp false f lbl') ∧
        f.isFloatShape = true ∧
        f[1]! = Sym.var v := by
  rw [frameFloatVars_mk_eq db fr]
  exact frameFloatVars_mem_iff db fr.hyps v

theorem frameFloatVars_mem_isVar
    (db : DB) (fr : Frame) (h_scoped_db : WellScopedDB db)
    (v : String) (h_in : v ∈ DB.frameFloatVars db fr) :
    db.isVar v = true := by
  obtain ⟨lbl, f_hyp, lbl', _h_lbl_mem, h_find, h_shape, h_f1⟩ :=
    (frameFloatVars_mem_iff' db fr v).1 h_in
  have h_decl_hyp : FormulaSymbolsDeclared db f_hyp :=
    (h_scoped_db.2 lbl (.hyp false f_hyp lbl') h_find).2
  have h_size : f_hyp.size = 2 := by
    by_cases h_size' : f_hyp.size = 2
    · exact h_size'
    · have : False := by
        simp [Formula.isFloatShape, h_size'] at h_shape
      exact this.elim
  have h_pos1 : 1 < f_hyp.size := by
    simp [h_size]
  have h_mem_var : Sym.var v ∈ f_hyp.toList := by
    have h_mem' := Array.getElem!_mem_toList f_hyp 1 h_pos1
    simpa [h_f1] using h_mem'
  exact h_decl_hyp (Sym.var v) h_mem_var

theorem frameFloatVars_mem_implies_index
    (db : DB) (hyps : Array String) (v : String)
    (h_mem : v ∈ DB.frameFloatVars db (Frame.mk #[] hyps)) :
    ∃ i, i < hyps.size ∧
      ∃ f lbl', db.find? hyps[i]! = some (.hyp false f lbl') ∧
        f.isFloatShape = true ∧
        f[1]! = Sym.var v := by
  rcases (frameFloatVars_mem_iff db hyps v).1 h_mem with
    ⟨lbl, f, lbl', h_lbl_mem, h_find, h_shape, h_f1⟩
  rcases Array.toList_mem_implies_index hyps lbl h_lbl_mem with ⟨i, hi, h_eq⟩
  have h_find_i : db.find? hyps[i]! = some (.hyp false f lbl') := by
    simpa [h_eq] using h_find
  exact ⟨i, hi, f, lbl', h_find_i, h_shape, h_f1⟩

theorem formulaSymsRespectFrame_mem
    (db : DB) (f : Formula) (fr : Frame)
    (h_ok : DB.formulaSymsRespectFrame db f fr = true) :
    ∀ s ∈ f.toList.tail,
      match s with
      | .var v => v ∈ DB.frameFloatVars db fr
      | .const c => c ∉ DB.frameFloatVars db fr := by
  have h_ok' :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars db fr)
          | .const c => decide (c ∉ DB.frameFloatVars db fr)) = true := by
    simpa [DB.formulaSymsRespectFrame] using h_ok
  intro s h_mem
  have h_all := (List.all_eq_true).1 h_ok'
  have h_dec := h_all s h_mem
  cases s with
  | var v =>
      simpa using (decide_eq_true_iff.mp h_dec)
  | const c =>
      simpa using (decide_eq_true_iff.mp h_dec)

theorem formulaSymsRespectFrame_of_declared
    (db : DB) (fr : Frame) (f : Formula)
    (h_scoped_db : WellScopedDB db)
    (h_decl : FormulaSymbolsDeclared db f)
    (h_var_in : ∀ v, Sym.var v ∈ f.toList.tail → v ∈ DB.frameFloatVars db fr) :
    DB.formulaSymsRespectFrame db f fr = true := by
  -- Prove the all predicate for every tail symbol.
  have h_all :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars db fr)
          | .const c => decide (c ∉ DB.frameFloatVars db fr)) = true := by
    apply (List.all_eq_true).2
    intro s h_mem
    cases s with
    | var v =>
        have h_in : v ∈ DB.frameFloatVars db fr := h_var_in v h_mem
        simpa using (decide_eq_true_iff.mpr h_in)
    | const c =>
        have h_mem' : Sym.const c ∈ f.toList := List.mem_of_mem_tail h_mem
        have h_isConst : db.isConst c = true := h_decl (Sym.const c) h_mem'
        have h_not_in : c ∉ DB.frameFloatVars db fr := by
          intro h_in
          have h_isVar : db.isVar c = true :=
            frameFloatVars_mem_isVar db fr h_scoped_db c h_in
          have h_isVar_false : db.isVar c = false := isConst_not_isVar db c h_isConst
          have : False := by
            simpa [h_isVar] using h_isVar_false
          exact this.elim
        simpa using (decide_eq_true_iff.mpr h_not_in)
  simpa [DB.formulaSymsRespectFrame] using h_all

theorem floatDeclaredBefore_of_symsRespectFrame
    (db : DB) (fr : Frame) (f : Formula)
    (h_ok : DB.formulaSymsRespectFrame db f (Frame.mk #[] fr.hyps) = true) :
    ∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db fr fr.hyps.size v := by
  intro v h_mem
  have h_in :
      v ∈ DB.frameFloatVars db (Frame.mk #[] fr.hyps) := by
    have h := formulaSymsRespectFrame_mem db f (Frame.mk #[] fr.hyps) h_ok
    simpa using h (Sym.var v) h_mem
  rcases frameFloatVars_mem_implies_index db fr.hyps v h_in with
    ⟨i, hi, f_hyp, lbl', h_find, h_shape, h_f1⟩
  exact ⟨i, hi, f_hyp, lbl', h_find, h_shape, h_f1⟩

theorem frameFloatVars_mem_of_mem_prefix
    (db : DB) (hyps : Array String) (lbl : String) (v : String)
    (h_mem : v ∈ DB.frameFloatVars db (Frame.mk #[] hyps)) :
    v ∈ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)) := by
  rcases (frameFloatVars_mem_iff db hyps v).1 h_mem with
    ⟨lbl', f, lbl'_name, h_lbl_mem, h_find, h_shape, h_f1⟩
  have h_lbl_mem' : lbl' ∈ (hyps.push lbl).toList := by
    simp [Array.toList_push, h_lbl_mem]
  exact (frameFloatVars_mem_iff db (hyps.push lbl) v).2
    ⟨lbl', f, lbl'_name, h_lbl_mem', h_find, h_shape, h_f1⟩

theorem formulaSymsRespectFrame_push_float
    (db : DB) (f : Formula) (hyps : Array String) (lbl : String)
    (f_float : Formula) (lbl_float : String)
    (h_ok : DB.formulaSymsRespectFrame db f (Frame.mk #[] hyps) = true)
    (h_decl : FormulaSymbolsDeclared db f)
    (h_find_float : db.find? lbl = some (.hyp false f_float lbl_float))
    (h_shape : f_float.isFloatShape = true)
    (h_decl_float : FormulaSymbolsDeclared db f_float) :
    DB.formulaSymsRespectFrame db f (Frame.mk #[] (hyps.push lbl)) = true := by
  -- Reduce to per-symbol property.
  have h_ok' :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars db (Frame.mk #[] hyps))
          | .const c => decide (c ∉ DB.frameFloatVars db (Frame.mk #[] hyps))) = true := by
    simpa [DB.formulaSymsRespectFrame] using h_ok
  have h_all := (List.all_eq_true).1 h_ok'
  -- Show the predicate holds for the pushed frame.
  have h_ok'' :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)))
          | .const c => decide (c ∉ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)))) = true := by
    apply (List.all_eq_true).2
    intro s h_mem
    have h_s := h_all s h_mem
    cases s with
    | var v =>
        have h_in : v ∈ DB.frameFloatVars db (Frame.mk #[] hyps) := by
          simpa using (decide_eq_true_iff.mp h_s)
        have h_in' := frameFloatVars_mem_of_mem_prefix db hyps lbl v h_in
        simpa using (decide_eq_true_iff.mpr h_in')
    | const c =>
        -- If c were in the new frameFloatVars, it would either come from an old float
        -- (contradicts h_s) or from the new float, which would make c a variable.
        have h_not_old : c ∉ DB.frameFloatVars db (Frame.mk #[] hyps) := by
          simpa using (decide_eq_true_iff.mp h_s)
        -- Assume c is in the new frameFloatVars and derive contradiction.
        by_cases h_in_new : c ∈ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl))
        · rcases (frameFloatVars_mem_iff db (hyps.push lbl) c).1 h_in_new with
            ⟨lbl', f', lbl'_name, h_lbl_mem, h_find, h_shape', h_f1⟩
          have h_mem_split : lbl' ∈ hyps.toList ∨ lbl' = lbl := by
            simpa [Array.toList_push] using h_lbl_mem
          cases h_mem_split with
          | inl h_old =>
              -- Then c was already in old frameFloatVars.
              have h_old_mem :
                  c ∈ DB.frameFloatVars db (Frame.mk #[] hyps) := by
                exact (frameFloatVars_mem_iff db hyps c).2
                  ⟨lbl', f', lbl'_name, h_old, h_find, h_shape', h_f1⟩
              exact (h_not_old h_old_mem).elim
          | inr h_eq =>
              subst h_eq
              -- New float hyp gives db.isVar c = true, contradicting const-ness.
              have h_isVar : db.isVar c = true := by
                -- f_float has Sym.var c at index 1, so it's in the toList.
                have h_size : f_float.size = 2 := by
                  unfold Formula.isFloatShape at h_shape
                  by_cases h_size : f_float.size = 2
                  · exact h_size
                  ·
                    have : False := by
                      simpa [h_size] using h_shape
                    exact this.elim
                have h_pos1 : 1 < f_float.size := by
                  simp [h_size]
                have h_eq_opt :
                    some (Object.hyp false f' lbl'_name) =
                      some (Object.hyp false f_float lbl_float) := by
                  exact h_find.symm.trans h_find_float
                have h_eq_obj :
                    Object.hyp false f' lbl'_name = Object.hyp false f_float lbl_float :=
                  Option.some.inj h_eq_opt
                have h_f_eq : f' = f_float := by
                  cases h_eq_obj
                  rfl
                have h_eq'' : f_float[1]! = Sym.var c := by
                  simpa [h_f_eq] using h_f1
                have h_mem_list : Sym.var c ∈ f_float.toList := by
                  have h_mem : f_float[1]! ∈ f_float.toList :=
                    Array.getElem!_mem_toList f_float 1 h_pos1
                  simpa [h_eq''] using h_mem
                exact h_decl_float (Sym.var c) h_mem_list
              have h_mem_list' : Sym.const c ∈ f.toList :=
                List.mem_of_mem_tail h_mem
              have h_isConst : db.isConst c = true := h_decl (Sym.const c) h_mem_list'
              have h_not_var := isConst_not_isVar db c h_isConst
              simp [h_isVar] at h_not_var
        · -- Not in new frameFloatVars, so predicate holds.
          exact decide_eq_true_iff.mpr h_in_new
  -- Conclude formulaSymsRespectFrame for the pushed frame.
  simpa [DB.formulaSymsRespectFrame] using h_ok''

theorem frameFloatVars_mem_push_ess_iff
    (db : DB) (hyps : Array String) (lbl : String)
    (f_ess : Formula) (lbl_ess : String) (v : String)
    (h_find : db.find? lbl = some (.hyp true f_ess lbl_ess)) :
    v ∈ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)) ↔
      v ∈ DB.frameFloatVars db (Frame.mk #[] hyps) := by
  constructor
  · intro h_mem
    rcases (frameFloatVars_mem_iff db (hyps.push lbl) v).1 h_mem with
      ⟨lbl', f, lbl'_name, h_lbl_mem, h_find', h_shape, h_f1⟩
    have h_mem_split : lbl' ∈ hyps.toList ∨ lbl' = lbl := by
      simpa [Array.toList_push] using h_lbl_mem
    cases h_mem_split with
    | inl h_old =>
        exact (frameFloatVars_mem_iff db hyps v).2
          ⟨lbl', f, lbl'_name, h_old, h_find', h_shape, h_f1⟩
    | inr h_eq =>
        have h_find'' : db.find? lbl' = some (.hyp true f_ess lbl_ess) := by
          simpa [h_eq] using h_find
        have h_eq_opt :
            some (Object.hyp false f lbl'_name) =
              some (Object.hyp true f_ess lbl_ess) := by
          exact h_find'.symm.trans h_find''
        have h_eq_obj :
            Object.hyp false f lbl'_name = Object.hyp true f_ess lbl_ess :=
          Option.some.inj h_eq_opt
        cases h_eq_obj
  · intro h_mem
    exact frameFloatVars_mem_of_mem_prefix db hyps lbl v h_mem

theorem formulaSymsRespectFrame_push_ess
    (db : DB) (f : Formula) (hyps : Array String) (lbl : String)
    (f_ess : Formula) (lbl_ess : String)
    (h_ok : DB.formulaSymsRespectFrame db f (Frame.mk #[] hyps) = true)
    (h_find : db.find? lbl = some (.hyp true f_ess lbl_ess)) :
    DB.formulaSymsRespectFrame db f (Frame.mk #[] (hyps.push lbl)) = true := by
  -- Reduce to per-symbol property on the tail.
  have h_ok' :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars db (Frame.mk #[] hyps))
          | .const c => decide (c ∉ DB.frameFloatVars db (Frame.mk #[] hyps))) = true := by
    simpa [DB.formulaSymsRespectFrame] using h_ok
  have h_all := (List.all_eq_true).1 h_ok'
  have h_ok'' :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)))
          | .const c => decide (c ∉ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)))) = true := by
    apply (List.all_eq_true).2
    intro s h_mem
    have h_s := h_all s h_mem
    cases s with
    | var v =>
        have h_in : v ∈ DB.frameFloatVars db (Frame.mk #[] hyps) := by
          simpa using (decide_eq_true_iff.mp h_s)
        have h_in' := (frameFloatVars_mem_push_ess_iff db hyps lbl f_ess lbl_ess v h_find).2 h_in
        simpa using (decide_eq_true_iff.mpr h_in')
    | const c =>
        have h_not_old : c ∉ DB.frameFloatVars db (Frame.mk #[] hyps) := by
          simpa using (decide_eq_true_iff.mp h_s)
        have h_not_new : c ∉ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)) := by
          intro h_in_new
          have h_in_old :=
            (frameFloatVars_mem_push_ess_iff db hyps lbl f_ess lbl_ess c h_find).1 h_in_new
          exact h_not_old h_in_old
        simpa using (decide_eq_true_iff.mpr h_not_new)
  simpa [DB.formulaSymsRespectFrame] using h_ok''

theorem toList_tail_of_size_two {α : Type} [Inhabited α] (arr : Array α)
    (h_size : arr.size = 2) :
    arr.toList.tail = [arr[1]!] := by
  have h_len : arr.toList.length = 2 := by
    simp [Array.length_toList, h_size]
  cases h_list : arr.toList with
  | nil =>
        have h' : False := by
          simpa [h_list] using h_len
        exact h'.elim
  | cons a tl =>
      cases tl with
      | nil =>
          have h' : False := by
            simpa [h_list] using h_len
          exact h'.elim
      | cons b tl' =>
          cases tl' with
          | nil =>
              -- arr.toList = [a,b]
              have h1_lt : 1 < arr.size := by
                simp [h_size]
              have h1_eq : arr[1]! = arr[1]'h1_lt := by
                simpa using (Array.getBang_eq_get_nat (a := arr) (i := 1) (h := h1_lt))
              have h_toList1' : arr.toList[1] = arr[1]'h1_lt := by
                simpa using (Array.getElem_toList (xs := arr) (i := 1) h1_lt)
              have h_toList1 : arr.toList[1] = arr[1]! := by
                simpa [h1_eq] using h_toList1'
              have h_b : b = arr[1]! := by
                have h_b' : arr.toList[1] = b := by
                  simp [h_list]
                exact h_b'.symm.trans h_toList1
              simpa [h_list, h_b]
          | cons c tl'' =>
              have h' : False := by
                simpa [h_list] using h_len
              exact h'.elim

theorem formulaSymsRespectFrame_float_self
    (db : DB) (hyps : Array String) (lbl : String)
    (f_float : Formula) (lbl_float : String)
    (h_find : db.find? lbl = some (.hyp false f_float lbl_float))
    (h_shape : f_float.isFloatShape = true) :
    DB.formulaSymsRespectFrame db f_float (Frame.mk #[] (hyps.push lbl)) = true := by
  -- Extract the float shape details
  have h_size : f_float.size = 2 := by
    unfold Formula.isFloatShape at h_shape
    by_cases h_size : f_float.size = 2
    · exact h_size
    · simp [h_size] at h_shape
  have h_float :
      ∃ c v, f_float[0]! = Sym.const c ∧ f_float[1]! = Sym.var v := by
    cases h0 : f_float[0]! with
    | const c =>
        cases h1 : f_float[1]! with
        | var v =>
            exact ⟨c, v, rfl, rfl⟩
        | const c' =>
            have h_shape' :
                (if f_float.size = 2 then
                  match Sym.const c, Sym.const c' with
                  | Sym.const _, Sym.var _ => true
                  | _, _ => false
                else false) = true := by
              simpa [Formula.isFloatShape, h0, h1] using h_shape
            have h_shape'' :
                (match Sym.const c, Sym.const c' with
                  | Sym.const _, Sym.var _ => true
                  | _, _ => false) = true := by
              simpa [h_size] using h_shape'
            have : False := by
              simpa using h_shape''
            exact this.elim
    | var v0 =>
        cases h1 : f_float[1]! with
        | var v1 =>
            have h_shape' :
                (if f_float.size = 2 then
                  match Sym.var v0, Sym.var v1 with
                  | Sym.const _, Sym.var _ => true
                  | _, _ => false
                else false) = true := by
              simpa [Formula.isFloatShape, h0, h1] using h_shape
            have h_shape'' :
                (match Sym.var v0, Sym.var v1 with
                  | Sym.const _, Sym.var _ => true
                  | _, _ => false) = true := by
              simpa [h_size] using h_shape'
            have : False := by
              simpa using h_shape''
            exact this.elim
        | const c1 =>
            have h_shape' :
                (if f_float.size = 2 then
                  match Sym.var v0, Sym.const c1 with
                  | Sym.const _, Sym.var _ => true
                  | _, _ => false
                else false) = true := by
              simpa [Formula.isFloatShape, h0, h1] using h_shape
            have h_shape'' :
                (match Sym.var v0, Sym.const c1 with
                  | Sym.const _, Sym.var _ => true
                  | _, _ => false) = true := by
              simpa [h_size] using h_shape'
            have : False := by
              simpa using h_shape''
            exact this.elim
  rcases h_float with ⟨c, v, h0, h1⟩
  -- Show v is in the new frameFloatVars
  have h_lbl_mem : lbl ∈ (hyps.push lbl).toList := by
    simp [Array.toList_push]
  have h_mem :
      v ∈ DB.frameFloatVars db (Frame.mk #[] (hyps.push lbl)) := by
    apply (frameFloatVars_mem_iff db (hyps.push lbl) v).2
    exact ⟨lbl, f_float, lbl_float, h_lbl_mem, h_find, h_shape, h1⟩
  -- Now discharge formulaSymsRespectFrame
  have h_tail : f_float.toList.tail = [Sym.var v] := by
    have h_tail' := toList_tail_of_size_two f_float h_size
    simpa [h1] using h_tail'
  unfold DB.formulaSymsRespectFrame
  -- tail is [var v], so all predicate holds if v in frameFloatVars
  simp [h_tail, h_mem]

theorem floatDeclaredBefore_of_prefix
    (db : DB) (fr : Frame) (lbl : String) (i : Nat) (v : String)
    (h_le : i ≤ fr.hyps.size)
    (h_decl : FloatDeclaredBefore db fr i v) :
    FloatDeclaredBefore db { fr with hyps := fr.hyps.push lbl } i v := by
  rcases h_decl with ⟨j, hj, f, lbl', h_find, h_shape, h_f1⟩
  have h_j_lt : j < fr.hyps.size := Nat.lt_of_lt_of_le hj h_le
  have h_find' : db.find? (fr.hyps.push lbl)[j]! = some (.hyp false f lbl') := by
    have h_get : (fr.hyps.push lbl)[j]! = fr.hyps[j]! :=
      Array.getElem!_push_lt h_j_lt
    simpa [h_get] using h_find
  exact ⟨j, hj, f, lbl', h_find', h_shape, h_f1⟩

theorem assert_formula_wf_of_db
    {db : DB} {lbl name : String} {f : Formula} {fr : Frame}
    (h_db : WellFormedDB db)
    (h_find : db.find? lbl = some (Object.assert f fr name)) :
    WellFormedFormula f := by
  have h := h_db.2 lbl (Object.assert f fr name) h_find
  exact h.1

theorem assert_frame_wf_of_db
    {db : DB} {lbl name : String} {f : Formula} {fr : Frame}
    (h_db : WellFormedDB db)
    (h_find : db.find? lbl = some (Object.assert f fr name)) :
    WellFormedFrame db fr := by
  have h := h_db.2 lbl (Object.assert f fr name) h_find
  exact h.2

@[simp] theorem WellFormedFormula.size_pos {f} :
  WellFormedFormula f → 0 < f.size := fun h => h.1

theorem WellFormedFormula.head_const {f} :
  WellFormedFormula f → ∃ c, f[0]! = Sym.const c := fun h => h.2

theorem WellFormedFloat.size_pos {f} :
  WellFormedFloat f → 0 < f.size := by
  intro h
  rw [h.1]
  omega

theorem wellFormedFloat_of_isFloatShape {f : Formula} :
    f.isFloatShape = true → WellFormedFloat f := by
  intro h
  unfold Formula.isFloatShape at h
  by_cases h_size : f.size = 2
  · have h_match :
        (match f[0]!, f[1]! with
          | Sym.const _, Sym.var _ => true
          | _, _ => false) = true := by
        simpa [h_size] using h
    cases h0 : f[0]! with
    | const c =>
        cases h1 : f[1]! with
        | var v =>
            exact ⟨h_size, c, v, h0, h1⟩
        | const c' =>
            have : False := by
              simp [h0, h1] at h_match
            exact this.elim
    | var v =>
        have : False := by
          cases h1 : f[1]! <;> simp [h0, h1] at h_match
        exact this.elim
  · exact (by
      have h' := h
      simp [h_size] at h')

theorem isFloatShape_of_wellFormedFloat {f : Formula} :
    WellFormedFloat f → f.isFloatShape = true := by
  intro h
  rcases h with ⟨h_size, c, v, h0, h1⟩
  have h0_lt : 0 < f.size := by
    simp [h_size]
  have h1_lt : 1 < f.size := by
    simp [h_size]
  have h0' : f[0]'h0_lt = Sym.const c := by
    simpa [Array.getBang_eq_get_nat (a := f) (i := 0) (h := h0_lt)] using h0
  have h1' : f[1]'h1_lt = Sym.var v := by
    simpa [Array.getBang_eq_get_nat (a := f) (i := 1) (h := h1_lt)] using h1
  unfold Formula.isFloatShape
  simp [h_size, h0', h1']

theorem hypOK_of_hypOK? {db : DB} {label : String} :
    db.hypOK? label = true → HypOK db label := by
  intro h
  unfold HypOK
  cases h_find : db.find? label with
  | none =>
      exfalso
      simp [DB.hypOK?, h_find] at h
  | some obj =>
      cases obj with
      | hyp ess f lbl =>
          refine ⟨ess, f, lbl, ?_⟩
          constructor
          · rfl
          · constructor
            · intro h_ess
              have h_float : f.isFloatShape = true := by
                simpa [DB.hypOK?, h_find, h_ess] using h
              exact wellFormedFloat_of_isFloatShape h_float
            · intro h_ess
              have h_head : f.hasConstHead = true := by
                simpa [DB.hypOK?, h_find, h_ess] using h
              exact wellFormedFormula_of_hasConstHead h_head
      | const _ =>
          exfalso
          simp [DB.hypOK?, h_find] at h
      | var _ =>
          exfalso
          simp [DB.hypOK?, h_find] at h
      | assert _ _ _ =>
          exfalso
          simp [DB.hypOK?, h_find] at h

theorem floatVarsDistinct_of_sizes {f g : Formula}
    (h_f : f.size ≥ 2) (h_g : g.size ≥ 2) :
    f.floatVarsDistinct? g = true → f.floatVarName ≠ g.floatVarName := by
  intro h
  by_cases h_eq : f.floatVarName = g.floatVarName
  · have h_false : f.floatVarsDistinct? g = false := by
      simp [Formula.floatVarsDistinct?, h_f, h_g, h_eq]
    have : False := by
      simp [h_false] at h
    exact this.elim
  · exact h_eq

theorem frameFloatVarsUnique_of_frameFloatVarsUnique?
    {db : DB} {fr : Frame} :
    db.frameFloatVarsUnique? fr = true → UniqueFloatVars db fr := by
  intro h
  intro i j hi hj h_neq fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
  have h_outer : ∀ i ∈ List.range fr.hyps.size,
      (List.range fr.hyps.size).all (fun j =>
        if h_ij : i = j then
          true
        else
          match db.find? fr.hyps[i]!, db.find? fr.hyps[j]! with
          | some (.hyp false fi _), some (.hyp false fj _) => Formula.floatVarsDistinct? fi fj
          | _, _ => true) = true := by
    simpa using (List.all_eq_true).1 h
  have h_i : (List.range fr.hyps.size).all (fun j =>
        if h_ij : i = j then
          true
        else
          match db.find? fr.hyps[i]!, db.find? fr.hyps[j]! with
          | some (.hyp false fi _), some (.hyp false fj _) => Formula.floatVarsDistinct? fi fj
          | _, _ => true) = true := by
    apply h_outer i
    simpa using hi
  have h_inner : ∀ j ∈ List.range fr.hyps.size,
      (if h_ij : i = j then
          true
        else
          match db.find? fr.hyps[i]!, db.find? fr.hyps[j]! with
          | some (.hyp false fi _), some (.hyp false fj _) => Formula.floatVarsDistinct? fi fj
          | _, _ => true) = true := by
    simpa using (List.all_eq_true).1 h_i
  have h_pair :
      (if h_ij : i = j then
          true
        else
          match db.find? fr.hyps[i]!, db.find? fr.hyps[j]! with
          | some (.hyp false fi _), some (.hyp false fj _) => Formula.floatVarsDistinct? fi fj
          | _, _ => true) = true := by
    apply h_inner j
    simpa using hj
  have h_pair' :
      (match db.find? fr.hyps[i]!, db.find? fr.hyps[j]! with
        | some (.hyp false fi _), some (.hyp false fj _) => Formula.floatVarsDistinct? fi fj
        | _, _ => true) = true := by
    simpa [h_neq] using h_pair
  have h_find_i : db.find? fr.hyps[i]! = some (.hyp false fi lbli) := by
    have h_eq : fr.hyps[i]! = fr.hyps[i]'hi := Array.getBang_eq_get_nat (a := fr.hyps) (i := i) (h := hi)
    simpa [h_eq] using h_fi
  have h_find_j : db.find? fr.hyps[j]! = some (.hyp false fj lblj) := by
    have h_eq : fr.hyps[j]! = fr.hyps[j]'hj := Array.getBang_eq_get_nat (a := fr.hyps) (i := j) (h := hj)
    simpa [h_eq] using h_fj
  have h_distinct : fi.floatVarsDistinct? fj = true := by
    simpa [h_find_i, h_find_j] using h_pair'
  have h_ne : fi.floatVarName ≠ fj.floatVarName :=
    floatVarsDistinct_of_sizes (f := fi) (g := fj) h_sz_i h_sz_j h_distinct
  simpa [Formula.floatVarName] using h_ne

theorem wellFormedFrame_of_wellFormedFrame?
    {db : DB} {fr : Frame} :
    db.wellFormedFrame? fr = true → WellFormedFrame db fr := by
  intro h
  have h_and : db.frameHypsOk? fr = true ∧ db.frameFloatVarsUnique? fr = true := by
    simpa [DB.wellFormedFrame?] using h
  constructor
  · intro i hi
    have h_all :
        (List.range fr.hyps.size).all (fun i => db.hypOK? fr.hyps[i]!) = true := h_and.1
    have h_i : db.hypOK? fr.hyps[i]! = true := by
      have h_mem : i ∈ List.range fr.hyps.size := by
        simpa using hi
      exact (List.all_eq_true).1 h_all i h_mem
    have h_ok : HypOK db fr.hyps[i]! := hypOK_of_hypOK? h_i
    have h_eq : fr.hyps[i]! = fr.hyps[i]'hi := Array.getBang_eq_get_nat (a := fr.hyps) (i := i) (h := hi)
    simpa [h_eq] using h_ok
  · exact frameFloatVarsUnique_of_frameFloatVarsUnique? h_and.2

theorem wellFormedObj_of_wellFormedObj?
    {db : DB} {lbl : String} {obj : Object} :
    db.wellFormedObj? lbl obj = true →
    match obj with
    | .hyp ess f _   => (if ess then WellFormedFormula f else WellFormedFloat f)
    | .assert f fr _ => WellFormedFormula f ∧ WellFormedFrame db fr
    | .var v         => v = lbl
    | _              => True := by
  intro h
  cases obj with
  | const _ =>
      trivial
  | var v =>
      have h_eq : (v == lbl) = true := by
        simpa [DB.wellFormedObj?] using h
      exact (beq_iff_eq).1 h_eq
  | hyp ess f lbl' =>
      cases ess with
      | false =>
          have h_shape : f.isFloatShape = true := by
            simpa [DB.wellFormedObj?] using h
          simpa using (wellFormedFloat_of_isFloatShape h_shape)
      | true =>
          have h_head : f.hasConstHead = true := by
            simpa [DB.wellFormedObj?] using h
          simpa using (wellFormedFormula_of_hasConstHead h_head)
  | assert f fr proof =>
      have h_and : f.hasConstHead = true ∧ db.wellFormedFrame? fr = true := by
        simpa [DB.wellFormedObj?, Bool.and_eq_true] using h
      exact ⟨wellFormedFormula_of_hasConstHead h_and.1, wellFormedFrame_of_wellFormedFrame? h_and.2⟩

theorem wellFormedDB_of_wellFormed?
    {db : DB} : db.wellFormed? = true → WellFormedDB db := by
  intro h
  have h_and : db.wellFormedFrame? db.frame = true ∧ db.wellFormedObjects? = true := by
    simpa [DB.wellFormed?] using h
  constructor
  · exact wellFormedFrame_of_wellFormedFrame? h_and.1
  · intro lbl obj h_find
    have h_all : db.objects.toList.all (fun kv => db.wellFormedObj? kv.1 kv.2) = true := by
      simpa [DB.wellFormedObjects?] using h_and.2
    have h_find' : db.objects[lbl]? = some obj := by
      simpa [DB.find?] using h_find
    have h_mem : (lbl, obj) ∈ db.objects.toList := by
      exact (Std.HashMap.mem_toList_iff_getElem?_eq_some).2 h_find'
    have h_obj : db.wellFormedObj? lbl obj = true :=
      (List.all_eq_true).1 h_all (lbl, obj) h_mem
    exact wellFormedObj_of_wellFormedObj? h_obj

end WF
end Metamath
