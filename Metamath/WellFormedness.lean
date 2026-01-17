/-
# Metamath.WellFormedness
Foundational well-formedness predicates that capture parser guarantees.
-/
import Std.Data.HashMap.Lemmas
import Metamath.Verify

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
