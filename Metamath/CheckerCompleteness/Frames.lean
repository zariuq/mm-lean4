import Metamath.Spec.Completeness
import Metamath.CheckerCompleteness.Declare
import Metamath.CheckerCompleteness.Trim

/-!
# The frames of a `$p` statement

Facts about the database state before a `$p` statement, relating the frame that frame trimming
stores for the claim to the active frame and to the declarative statement:

- `premiseTypecode_isConst`, `conclusionTypecode_isConst`: the typecodes the stored assertions use
  in premises, and the typecode of a claim, are declared constants.
- `extendedFrame_of_trim`: the active frame is an extended frame (Metamath book §4.2.7) of the
  frame `DB.trimFrame'` stores for a claim; `frameExprsInScope_of_trim`: the stored statement is in
  scope.
- `dvRel_dummyDJs_iff_dummyDV`: the `$d` pairs the parser stores for dummy variables and the spec's
  dummy pairs give the same `$d` relation.
- `dummyDecls_fresh`: declarations of spec dummies with fresh names, with fresh `$f` labels.
-/

set_option autoImplicit false

/-! ## Runtime facts -/

namespace Metamath.CheckerCompleteness

open Metamath.Verify
open Metamath.Kernel
open Metamath.WF
open Metamath.Spec.Equivalence
open Metamath.StoredStatementSoundness.Runtime (trimVars trimFrame_hyps_eq
  trimFrame_dj_toList_eq_filter trimFrameHyps_mem_iff toFrame_hyps_subset_of_subsequence
  trimVars_contains_of_target_var)

/-! ### Typecodes are declared constants -/

/-- The typecode of a formula with head constant `c` is `c`. -/
theorem toExpr_typecode_of_head {f : Verify.Formula} {c : String}
    (h_pos : 0 < f.size) (h_head : f[0]! = .const c) :
    (toExpr f).typecode.c = c := by
  unfold toExpr
  rw [dif_pos h_pos]
  rw [Kernel.getElem!_pos f 0 h_pos] at h_head
  simp [h_head, Verify.Sym.value]

/-- The typecode of a well-formed formula whose symbols are declared is a declared constant. -/
theorem typecode_isConst_of_wellFormed (db : Verify.DB) {f : Verify.Formula}
    (h_wff : WellFormedFormula f) (h_decl : FormulaSymbolsDeclared db f) :
    db.isConst (toExpr f).typecode.c = true := by
  obtain ⟨h_pos, c, h_c⟩ := h_wff
  rw [toExpr_typecode_of_head h_pos h_c]
  have h_mem : Verify.Sym.const c ∈ f.toList := by
    have h_mem' := Array.getElem!_mem_toList f 0 h_pos
    rwa [h_c] at h_mem'
  exact h_decl _ h_mem

/-- The typecode of a claim with a constant head whose symbols are declared is a declared
constant. -/
theorem conclusionTypecode_isConst (db : Verify.DB) (f : Verify.Formula)
    (h_head : f.hasConstHead = true) (h_decl : FormulaSymbolsDeclared db f) :
    db.isConst (toExpr f).typecode.c = true :=
  typecode_isConst_of_wellFormed db (wellFormedFormula_of_hasConstHead h_head) h_decl

/-- A hypothesis object of a well-formed database has a well-formed formula. -/
theorem wellFormedFormula_of_hyp (db : Verify.DB) (h_wf : WellFormedDB db)
    {label : String} {ess : Bool} {g : Verify.Formula} {nm : String}
    (h_find : db.find? label = some (.hyp ess g nm)) : WellFormedFormula g := by
  have h_obj := h_wf.2 label _ h_find
  cases ess with
  | false =>
      obtain ⟨h_size, c, _, h_c, _⟩ := (by simpa using h_obj : WellFormedFloat g)
      exact ⟨by omega, c, h_c⟩
  | true => simpa using h_obj

/-- A spec hypothesis converted from a label comes from a hypothesis object, and has the typecode
of its formula. -/
theorem convertHyp_typecode (db : Verify.DB) {label : String} {h : Spec.Hyp}
    (h_conv : convertHyp db label = some h) :
    ∃ ess g nm, db.find? label = some (.hyp ess g nm) ∧
      (hypExpr h).typecode = (toExpr g).typecode := by
  unfold convertHyp at h_conv
  cases h_find : db.find? label with
  | none => simp [h_find] at h_conv
  | some obj =>
    cases obj with
    | const _ => simp [h_find] at h_conv
    | var _ => simp [h_find] at h_conv
    | assert _ _ _ => simp [h_find] at h_conv
    | hyp ess g nm =>
      refine ⟨ess, g, nm, rfl, ?_⟩
      cases h_e : toExprOpt g with
      | none => cases ess <;> simp [h_find, h_e] at h_conv
      | some e =>
        have h_toExpr : toExpr g = e := ((toExprOpt_some_iff_toExpr g e).mp h_e).2
        cases ess with
        | false =>
          obtain ⟨tc, syms⟩ := e
          rcases syms with _ | ⟨s, _ | ⟨s', rest⟩⟩ <;> simp [h_find, h_e] at h_conv
          subst h_conv
          simp [hypExpr, h_toExpr]
        | true =>
          simp [h_find, h_e] at h_conv
          subst h_conv
          simp [hypExpr, h_toExpr]

/-- Every hypothesis converted from a label of a well-formed, declared database has a declared
constant as typecode. -/
theorem convertHyp_typecode_isConst (db : Verify.DB) (h_wf : WellFormedDB db)
    (h_sf : CompletenessScopedFacts db) {label : String} {h : Spec.Hyp}
    (h_conv : convertHyp db label = some h) :
    db.isConst (hypExpr h).typecode.c = true := by
  obtain ⟨ess, g, nm, h_find, h_tc⟩ := convertHyp_typecode db h_conv
  rw [h_tc]
  exact typecode_isConst_of_wellFormed db (wellFormedFormula_of_hyp db h_wf h_find)
    (h_sf.hyp_declared label ess g nm h_find)

/-- Every hypothesis of a stored assertion has a declared constant as typecode. -/
theorem storedHyp_typecode_isConst (db : Verify.DB) (h_wf : WellFormedDB db)
    (h_sf : CompletenessScopedFacts db) {l : String} {fr : Spec.Frame} {e : Spec.Expr}
    (h_lookup : toDatabaseTotal db l = some (fr, e)) {h : Spec.Hyp} (h_mem : h ∈ fr.hyps) :
    db.isConst (hypExpr h).typecode.c = true := by
  obtain ⟨_, frImpl, _, _, h_frame, _⟩ :=
    toDatabase_lookup db (toDatabaseTotal db) l fr e rfl h_lookup
  obtain ⟨label, _, h_conv⟩ := hyps_mem_has_label db frImpl fr h h_frame h_mem
  exact convertHyp_typecode_isConst db h_wf h_sf h_conv

/-- Every typecode the stored assertions of a well-formed, declared database use in
premises (heads of their hypotheses and typecodes of their variables) is a declared constant. -/
theorem premiseTypecode_isConst (db : Verify.DB) (h_wf : WellFormedDB db)
    (h_sf : CompletenessScopedFacts db) {t : String}
    (h_t : Metamath.PremiseTypecode (dbToAxioms (toDatabaseTotal db)) t) :
    db.isConst t = true := by
  obtain ⟨ax, ⟨l, fr, e, h_lookup, h_ctx, h_fmla⟩, h_cases⟩ := h_t
  have h_hyp_tc : ∀ hyp ∈ fr.hyps, db.isConst (hypExpr hyp).typecode.c = true :=
    fun hyp h_hyp => storedHyp_typecode_isConst db h_wf h_sf h_lookup h_hyp
  obtain ⟨ctx, fmla⟩ := ax
  simp only at h_ctx h_fmla
  subst h_ctx h_fmla
  rcases h_cases with ⟨h, h_mem, h_head⟩ | ⟨v, h_mem, h_type⟩
  · obtain ⟨hyp, h_hyp, rfl⟩ := hyps_correspondence h_mem
    rw [← h_head]
    have h_tc := h_hyp_tc hyp h_hyp
    cases hyp with
    | floating c w => simpa [hypToDeclarativeFormula, hypExpr] using h_tc
    | essential e' => simpa [hypToDeclarativeFormula, exprToFormula, hypExpr] using h_tc
  · obtain ⟨w, h_w⟩ := Spec.DummyExtension.declared_of_mem_vars_statementOfFrame
      (e := e) (fr := fr) h_mem
    obtain ⟨c, h_float, h_vtc⟩ := mem_varMapOfFrame_sound_typed (findVar_mem_of_some h_w)
    rw [← h_type, h_vtc]
    simpa [hypExpr] using h_hyp_tc _ h_float

/-! ### The active frame extends the trimmed frame -/

/-- A frame converted from a well-formed runtime frame is well-formed. -/
theorem frameWellFormed_of_toFrame (db : Verify.DB) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_fr : toFrame db frImpl = some fr) (h_wf : WellFormedFrame db frImpl) :
    FrameWellFormed fr :=
  ⟨floatUnique_of_uniqueFloatVars db frImpl fr h_fr h_wf h_wf.2,
    floatVarNoDup_of_uniqueFloatVars db frImpl fr h_fr h_wf h_wf.2⟩

/-- The active frame of a well-formed database is well-formed. -/
theorem frameWellFormed_active (db : Verify.DB) (frAct : Spec.Frame) (h_wf : WellFormedDB db)
    (h_act : toFrame db db.frame = some frAct) : FrameWellFormed frAct :=
  frameWellFormed_of_toFrame db db.frame frAct h_act h_wf.1

/-- The frame `DB.trimFrame'` stores for a claim is well-formed. -/
theorem frameWellFormed_of_trim (db : Verify.DB) (f : Verify.Formula) (frImpl : Verify.Frame)
    (fr : Spec.Frame) (h_wf : WellFormedDB db) (h_trim : db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame db frImpl = some fr) : FrameWellFormed fr :=
  frameWellFormed_of_toFrame db frImpl fr h_fr
    (ParserOps.trimFrame'_success_implies_wellformed_frame db f frImpl h_wf h_trim)

/-- A floating hypothesis object `$f c v` converts to `Hyp.floating c v`. -/
theorem convertHyp_of_wellFormedFloat (db : Verify.DB) {label : String} {g : Verify.Formula}
    {nm : String} (h_find : db.find? label = some (.hyp false g nm)) (h_g : WellFormedFloat g) :
    convertHyp db label = some (.floating (toExpr g).typecode ⟨g[1]!.value⟩) := by
  have h_size : g.size = 2 := h_g.1
  have h_pos : 0 < g.size := by omega
  have h_tail : g.toList.tail = [g[1]!] := array_size2_tail_is_second_elem h_size
  have h_opt : toExprOpt g = some ⟨(toExpr g).typecode, [g[1]!.value]⟩ := by
    rw [toExprOpt_some_iff_toExpr]
    refine ⟨h_pos, ?_⟩
    unfold toExpr
    rw [dif_pos h_pos]
    simp [h_tail, toSym]
  unfold convertHyp
  simp [h_find, h_opt]

/-- The active frame is an extended frame of the frame `DB.trimFrame'` stores for a claim:
it contains the trimmed hypotheses and `$d` pairs, every other hypothesis is the `$f` of a
variable that is not mandatory, hence neither a variable of the trimmed frame nor a constant, and
every other `$d` pair has a variable that is not mandatory. -/
theorem extendedFrame_of_trim (db : Verify.DB) (f : Verify.Formula) (frImpl : Verify.Frame)
    (fr frAct : Spec.Frame) (h_wf : WellFormedDB db) (h_sf : CompletenessScopedFacts db)
    (h_trim : db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame db frImpl = some fr) (h_act : toFrame db db.frame = some frAct) :
    Spec.Completeness.ExtendedFrame (toConsts db) fr frAct := by
  have h_trim_pair : db.trimFrame f = (true, frImpl) := ParserOps.trimFrame'_ok_iff.mp h_trim
  have h_frImpl_wf : WellFormedFrame db frImpl :=
    ParserOps.trimFrame'_success_implies_wellformed_frame db f frImpl h_wf h_trim
  have h_hyps : frImpl.hyps = DB.trimFrameHyps db (trimVars db f) db.frame.hyps := by
    have h_output : (db.trimFrame f).2.hyps = frImpl.hyps :=
      congrArg (fun p => p.2.hyps) h_trim_pair
    exact h_output.symm.trans (trimFrame_hyps_eq db f)
  have h_dj : frImpl.dj.toList = db.frame.dj.toList.filter
      (fun p => (trimVars db f).contains p.1 && (trimVars db f).contains p.2) := by
    have h_output : (db.trimFrame f).2.dj = frImpl.dj := congrArg (fun p => p.2.dj) h_trim_pair
    rw [← h_output]
    exact trimFrame_dj_toList_eq_filter db f
  have h_var_mand : ∀ v, v ∈ fr.vars → (trimVars db f).contains v.v = true :=
    fun v hv => trimVars_contains_of_target_var db f frImpl fr h_trim h_fr h_frImpl_wf hv
  have h_fr_dv := toFrame_dv_eq db frImpl fr h_fr
  have h_act_dv := toFrame_dv_eq db db.frame frAct h_act
  refine ⟨frameWellFormed_active db frAct h_wf h_act, ?_, ?_, ?_, ?_⟩
  · exact toFrame_hyps_subset_of_subsequence db db.frame frImpl frAct fr
      (ParserOps.trimFrame_produces_subsequence h_trim_pair) h_act h_fr
  · intro h h_mem h_not
    obtain ⟨label, h_label, h_conv⟩ := hyps_mem_has_label db db.frame frAct h h_act h_mem
    obtain ⟨i, hi, h_at⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp h_label)
    obtain ⟨ess, g, nm, h_find, _⟩ := convertHyp_typecode db h_conv
    cases h_keep : DB.trimFrameKeep db (trimVars db f) label with
    | true =>
        have h_label_trim : label ∈ frImpl.hyps.toList := by
          rw [h_hyps]
          exact (trimFrameHyps_mem_iff db (trimVars db f) db.frame.hyps label).mpr
            ⟨i, hi, h_at, by rw [h_at]; exact h_keep⟩
        obtain ⟨h', h_conv', h'_mem⟩ := convertHyp_mem_hyps db frImpl fr label h_fr h_label_trim
        have h_eq : h' = h := Option.some.inj (h_conv'.symm.trans h_conv)
        exact absurd (h_eq ▸ h'_mem) h_not
    | false =>
        cases ess with
        | true => simp [DB.trimFrameKeep, h_find] at h_keep
        | false =>
            have h_notMand : (trimVars db f).contains g[1]!.value = false := by
              simpa [DB.trimFrameKeep, h_find] using h_keep
            have h_g : WellFormedFloat g := by simpa using h_wf.2 label _ h_find
            have h_eq : h = .floating (toExpr g).typecode ⟨g[1]!.value⟩ :=
              Option.some.inj (h_conv.symm.trans (convertHyp_of_wellFormedFloat db h_find h_g))
            refine ⟨(toExpr g).typecode, ⟨g[1]!.value⟩, h_eq, ?_, ?_⟩
            · intro hv
              have h_mand := h_var_mand _ hv
              simp only at h_mand
              rw [h_notMand] at h_mand
              exact Bool.false_ne_true h_mand
            · obtain ⟨h_size, _, x, _, h_x⟩ := h_g
              have h_mem : Verify.Sym.var x ∈ g.toList := by
                have h_mem' := Array.getElem!_mem_toList g 1 (by omega)
                rwa [h_x] at h_mem'
              have h_isVar : db.isVar x = true := h_sf.hyp_declared label false g nm h_find _ h_mem
              intro h_const
              have h_const' : db.isConst x = true := by
                simpa [toConsts, h_x, Verify.Sym.value] using h_const
              have h_notVar := WF.isConst_not_isVar db x h_const'
              rw [h_isVar] at h_notVar
              exact Bool.noConfusion h_notVar
  · intro p hp
    rw [h_fr_dv] at hp
    rw [h_act_dv]
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [h_dj] at hq
    exact List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩
  · intro p hp h_not
    rw [h_act_dv] at hp
    rw [h_fr_dv] at h_not
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have h_not_both :
        ((trimVars db f).contains q.1 && (trimVars db f).contains q.2) = false := by
      cases h_both : ((trimVars db f).contains q.1 && (trimVars db f).contains q.2) with
      | false => rfl
      | true =>
          refine absurd (List.mem_map.mpr ⟨q, ?_, rfl⟩) h_not
          rw [h_dj]
          exact List.mem_filter.mpr ⟨hq, h_both⟩
    obtain ⟨q1, q2⟩ := q
    cases h1 : (trimVars db f).contains q1 with
    | false =>
        left
        intro hv
        have h_mand := h_var_mand _ hv
        simp only [convertDV] at h_mand
        rw [h1] at h_mand
        exact Bool.false_ne_true h_mand
    | true =>
        right
        intro hv
        have h_mand := h_var_mand _ hv
        simp only [convertDV] at h_mand
        simp [h1, h_mand] at h_not_both

end Metamath.CheckerCompleteness

namespace Metamath.CheckerCompleteness

open Metamath.Spec.DummyExtension (dummyDV mem_dummyDV dummyDV_complete)

/-! ## The `$d` relation of the dummy pairs -/

/-- The `$d` relation of the dummy pairs: two distinct variables, one a dummy and the other a
variable before it or a dummy. -/
theorem dvRel_dummyDV {seen ds : List Spec.Variable} {v w : Spec.Variable} :
    Spec.dvRel (dummyDV seen ds) v w ↔
      v ≠ w ∧ ((v ∈ ds ∧ w ∈ seen ++ ds) ∨ (w ∈ ds ∧ v ∈ seen ++ ds)) := by
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl (mem_dummyDV h)⟩
    · exact ⟨hne, Or.inr (mem_dummyDV h)⟩
  · rintro ⟨hne, ⟨hv, hw⟩ | ⟨hw, hv⟩⟩
    · exact ⟨hne, dummyDV_complete hv hw (Ne.symm hne)⟩
    · exact ⟨hne, (dummyDV_complete hw hv hne).symm⟩

theorem canonDJ_mem (d w : String) : canonDJ d w = (d, w) ∨ canonDJ d w = (w, d) := by
  by_cases h : d < w
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

theorem mem_dummyDJs : ∀ {seen ds : List String} {x y : String},
    (x, y) ∈ dummyDJs seen ds →
      (x ∈ ds ∧ y ∈ seen ++ ds) ∨ (y ∈ ds ∧ x ∈ seen ++ ds)
  | _, [], _, _, h => nomatch h
  | seen, d :: ds, x, y, h => by
      rcases List.mem_append.mp h with h | h
      · obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
        rcases canonDJ_mem d w with hc | hc <;> rw [hc] at heq <;>
          simp only [Prod.mk.injEq] at heq <;> obtain ⟨rfl, rfl⟩ := heq
        · exact Or.inl ⟨List.Mem.head _, List.mem_append_left _ hw⟩
        · exact Or.inr ⟨List.Mem.head _, List.mem_append_left _ hw⟩
      · have hsub : ∀ {z : String}, z ∈ (seen ++ [d]) ++ ds → z ∈ seen ++ d :: ds := by
          intro z hz
          simpa using hz
        rcases mem_dummyDJs h with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · exact Or.inl ⟨List.Mem.tail _ hx, hsub hy⟩
        · exact Or.inr ⟨List.Mem.tail _ hy, hsub hx⟩

theorem dummyDJs_complete : ∀ {seen ds : List String} {d w : String},
    d ∈ ds → w ∈ seen ++ ds → w ≠ d →
      (d, w) ∈ dummyDJs seen ds ∨ (w, d) ∈ dummyDJs seen ds
  | _, [], _, _, hd, _, _ => nomatch hd
  | seen, d' :: ds, d, w, hd, hw, hne => by
      change (d, w) ∈ seen.map (canonDJ d') ++ dummyDJs (seen ++ [d']) ds ∨
        (w, d) ∈ seen.map (canonDJ d') ++ dummyDJs (seen ++ [d']) ds
      rcases List.mem_cons.mp hd with rfl | hd
      · rcases List.mem_append.mp hw with hw | hw
        · rcases canonDJ_mem d w with hc | hc
          · exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, hc⟩))
          · exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, hc⟩))
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact absurd rfl hne
          · rcases dummyDJs_complete (seen := seen ++ [d]) hw
              (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
              (Ne.symm hne) with h | h
            · exact Or.inr (List.mem_append_right _ h)
            · exact Or.inl (List.mem_append_right _ h)
      · have hw' : w ∈ (seen ++ [d']) ++ ds := by
          rcases List.mem_append.mp hw with hw | hw
          · exact List.mem_append_left _ (List.mem_append_left _ hw)
          · rcases List.mem_cons.mp hw with rfl | hw
            · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
            · exact List.mem_append_right _ hw
        rcases dummyDJs_complete hd hw' hne with h | h
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr (List.mem_append_right _ h)

/-- The `$d` relation of the dummy pairs the parser stores, read as spec pairs. -/
theorem dvRel_dummyDJs {seen ds : List String} {v w : Spec.Variable} :
    Spec.dvRel ((dummyDJs seen ds).map Kernel.convertDV) v w ↔
      v ≠ w ∧ ((v.v ∈ ds ∧ w.v ∈ seen ++ ds) ∨ (w.v ∈ ds ∧ v.v ∈ seen ++ ds)) := by
  have hconv : ∀ {x y : Spec.Variable},
      (x, y) ∈ (dummyDJs seen ds).map Kernel.convertDV ↔ (x.v, y.v) ∈ dummyDJs seen ds := by
    intro x y
    constructor
    · intro h
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
      obtain ⟨a, b⟩ := p
      simp only [Kernel.convertDV, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hp
    · intro h
      exact List.mem_map.mpr ⟨(x.v, y.v), h, rfl⟩
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, mem_dummyDJs (hconv.mp h)⟩
    · exact ⟨hne, (mem_dummyDJs (hconv.mp h)).symm⟩
  · rintro ⟨hne, ⟨hv, hw⟩ | ⟨hw, hv⟩⟩
    · have hne' : w.v ≠ v.v := fun h => hne (by cases v; cases w; simp_all)
      rcases dummyDJs_complete hv hw hne' with h | h
      · exact ⟨hne, Or.inl (hconv.mpr h)⟩
      · exact ⟨hne, Or.inr (hconv.mpr h)⟩
    · have hne' : v.v ≠ w.v := fun h => hne (by cases v; cases w; simp_all)
      rcases dummyDJs_complete hw hv hne' with h | h
      · exact ⟨hne, Or.inr (hconv.mpr h)⟩
      · exact ⟨hne, Or.inl (hconv.mpr h)⟩

theorem dvRel_append {A B : List (Spec.Variable × Spec.Variable)} {v w : Spec.Variable} :
    Spec.dvRel (A ++ B) v w ↔ Spec.dvRel A v w ∨ Spec.dvRel B v w := by
  unfold Spec.dvRel
  simp only [List.mem_append]
  constructor
  · rintro ⟨hne, (h | h) | (h | h)⟩
    · exact Or.inl ⟨hne, Or.inl h⟩
    · exact Or.inr ⟨hne, Or.inl h⟩
    · exact Or.inl ⟨hne, Or.inr h⟩
    · exact Or.inr ⟨hne, Or.inr h⟩
  · rintro (⟨hne, h | h⟩ | ⟨hne, h | h⟩)
    · exact ⟨hne, Or.inl (Or.inl h)⟩
    · exact ⟨hne, Or.inr (Or.inl h)⟩
    · exact ⟨hne, Or.inl (Or.inr h)⟩
    · exact ⟨hne, Or.inr (Or.inr h)⟩

/-- The parser's dummy pairs and the spec's dummy pairs give the same `$d` relation, when the
names of the spec's variables before the dummies are exactly `seen`. -/
theorem dvRel_dummyDJs_iff_dummyDV {seen : List String} {seenV : List Spec.Variable}
    (hseen : ∀ x : Spec.Variable, x ∈ seenV ↔ x.v ∈ seen) (ds : List Spec.Variable)
    {v w : Spec.Variable} :
    Spec.dvRel ((dummyDJs seen (ds.map (·.v))).map Kernel.convertDV) v w ↔
      Spec.dvRel (dummyDV seenV ds) v w := by
  have hds : ∀ x : Spec.Variable, x.v ∈ ds.map (·.v) ↔ x ∈ ds := by
    intro x
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h
      have : y = x := by cases x; cases y; simp_all
      exact this ▸ hy
    · intro h
      exact List.mem_map.mpr ⟨x, h, rfl⟩
  have hboth : ∀ x : Spec.Variable, x.v ∈ seen ++ ds.map (·.v) ↔ x ∈ seenV ++ ds := by
    intro x
    simp only [List.mem_append, hds, hseen]
  rw [dvRel_dummyDJs, dvRel_dummyDV, hds v, hds w, hboth v, hboth w]

/-! ## Fresh declarations for spec dummies -/

/-- A label longer than `bound`, of a different length for each index `i`. -/
def dummyLabel (bound i : Nat) : String := String.ofList (List.replicate (bound + 1 + i) 'l')

theorem dummyLabel_length (bound i : Nat) : (dummyLabel bound i).length = bound + 1 + i := by
  simp [dummyLabel]

/-- The declarations of the spec dummies `ps`: typecode and name from the spec, and the `$f`
label `dummyLabel bound i` for the `i`-th. -/
def dummyDecls (bound : Nat) : List (Spec.Constant × Spec.Variable) → Nat → List DummyDecl
  | [], _ => []
  | p :: ps, i => ⟨p.1.c, p.2.v, dummyLabel bound i⟩ :: dummyDecls bound ps (i + 1)

theorem dummyDecls_vars (bound : Nat) : ∀ (ps : List (Spec.Constant × Spec.Variable)) (i : Nat),
    (dummyDecls bound ps i).map (·.var) = ps.map (·.2.v)
  | [], _ => rfl
  | _ :: ps, i => congrArg (_ :: ·) (dummyDecls_vars bound ps (i + 1))

theorem dummyDecls_floats (bound : Nat) : ∀ (ps : List (Spec.Constant × Spec.Variable)) (i : Nat),
    (dummyDecls bound ps i).map (fun d => Spec.Hyp.floating ⟨d.tc⟩ ⟨d.var⟩) =
      ps.map (fun p => Spec.Hyp.floating p.1 p.2)
  | [], _ => rfl
  | _ :: ps, i => congrArg (_ :: ·) (dummyDecls_floats bound ps (i + 1))

theorem mem_dummyDecls {bound : Nat} : ∀ {ps : List (Spec.Constant × Spec.Variable)} {i : Nat}
    {d : DummyDecl}, d ∈ dummyDecls bound ps i →
      (∃ p ∈ ps, d.tc = p.1.c ∧ d.var = p.2.v) ∧ ∃ j, i ≤ j ∧ d.lbl = dummyLabel bound j
  | p :: ps, i, d, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨⟨p, List.Mem.head _, rfl, rfl⟩, i, Nat.le_refl _, rfl⟩
      · obtain ⟨⟨q, hq, h1, h2⟩, j, hij, hj⟩ := mem_dummyDecls h
        exact ⟨⟨q, List.Mem.tail _ hq, h1, h2⟩, j, Nat.le_of_succ_le hij, hj⟩

theorem dummyDecls_lbls_nodup (bound : Nat) : ∀ (ps : List (Spec.Constant × Spec.Variable))
    (i : Nat), ((dummyDecls bound ps i).map (·.lbl)).Nodup
  | [], _ => List.nodup_nil
  | _ :: ps, i => by
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, dummyDecls_lbls_nodup bound ps (i + 1)⟩
      obtain ⟨d, hd, hdl⟩ := List.mem_map.mp hmem
      obtain ⟨_, j, hij, hj⟩ := mem_dummyDecls hd
      have hlen := congrArg String.length (hj.symm.trans hdl)
      simp only [dummyLabel_length] at hlen
      omega

theorem find?_eq_none_of_not_mem_keys {db : Verify.DB} {l : String}
    (h : l ∉ db.objects.keys) : db.find? l = none :=
  Std.HashMap.getElem?_eq_none fun hm => h (Std.HashMap.mem_keys.mpr hm)

/-- Declarations for spec dummies with fresh names are fresh: the `$f` labels are longer than every
object name, every dummy name and `label`. -/
theorem dummyDecls_fresh (db : Verify.DB) (label : String) (bound : Nat)
    (ps : List (Spec.Constant × Spec.Variable)) (hnodup : (ps.map Prod.snd).Nodup)
    (hkeys : ∀ p ∈ ps, p.2.v ∉ db.objects.keys) (hlabel : ∀ p ∈ ps, p.2.v ≠ label)
    (hbound : ∀ s ∈ db.objects.keys ++ label :: ps.map (·.2.v), s.length ≤ bound)
    (htc : ∀ p ∈ ps, db.isConst p.1.c = true) :
    DummyDeclsFresh db label (dummyDecls bound ps 0) := by
  have hlbl_long : ∀ d ∈ dummyDecls bound ps 0, bound < d.lbl.length := by
    intro d hd
    obtain ⟨_, j, _, hj⟩ := mem_dummyDecls hd
    rw [hj, dummyLabel_length]
    omega
  have hvars_nodup : (ps.map (·.2.v)).Nodup := by
    have hinj : ∀ a b : Spec.Variable, a.v = b.v → a = b := by
      intro a b h
      cases a
      cases b
      simp_all
    have := hnodup.map (S := fun x y : String => x ≠ y) (fun v : Spec.Variable => v.v)
      (fun a b hab h => hab (hinj a b h))
    rw [List.map_map] at this
    exact this
  refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, fun d hd => ?_⟩
  · obtain ⟨⟨p, hp, _, hv⟩, _⟩ := mem_dummyDecls hd
    rw [hv]
    exact find?_eq_none_of_not_mem_keys (hkeys p hp)
  · refine find?_eq_none_of_not_mem_keys fun hmem => ?_
    have := hbound _ (List.mem_append_left _ hmem)
    have := hlbl_long d hd
    omega
  · rw [dummyDecls_vars, List.nodup_append, List.nodup_append]
    refine ⟨⟨hvars_nodup, dummyDecls_lbls_nodup bound ps 0, ?_⟩, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      have := hbound _ (List.mem_append_right _ (List.Mem.tail _ ha))
      have := hlbl_long d hd
      omega
    · intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      subst hab
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨p, hp, hpv⟩ := List.mem_map.mp ha
        exact hlabel p hp hpv
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
        have := hbound _ (List.mem_append_right _ (List.Mem.head _))
        have := hlbl_long d hd
        omega
  · obtain ⟨⟨p, hp, htcd, _⟩, _⟩ := mem_dummyDecls hd
    rw [htcd]
    exact htc p hp

section Scope

open Metamath.Kernel Metamath.WF

/-! ## The stored statement is in scope -/

/-- The spec frame and expression of a formula with a well-scoped frame that it respects are in
scope for the database's constants (the per-assertion part of `toDatabase_spec_wellFormed`). -/
theorem frameExprsInScope_of_scoped (db : Verify.DB) (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDB db) (fr_impl : Verify.Frame) (fr : Spec.Frame) (f : Verify.Formula)
    (h_fr : toFrame db fr_impl = some fr) (h_frame_wf : WellFormedFrame db fr_impl)
    (h_formula_wf : WellFormedFormula f)
    (h_scoped_assert : WellScopedFrame db fr_impl ∧
      Verify.DB.formulaSymsRespectFrame db f fr_impl = true ∧ FormulaSymbolsDeclared db f) :
    Spec.FrameExprsInScope (toConsts db) fr (toExpr f) := by
  constructor
  · exact exprVarsInScope_of_formula db fr_impl fr f (toExpr f)
      h_fr h_frame_wf h_formula_wf h_scoped_assert.2.1 h_scoped_assert.2.2 rfl
  · intro h h_mem
    cases h with
    | floating c v =>
        simp
    | essential e_hyp =>
        obtain ⟨label, h_lbl_mem, h_conv⟩ :=
          hyps_mem_has_label db fr_impl fr (Spec.Hyp.essential e_hyp) h_fr h_mem
        obtain ⟨i, hi, h_lbl_eq⟩ := toList_mem_implies_index fr_impl.hyps label h_lbl_mem
        have h_find_hyp :
            ∃ f_hyp lbl', db.find? label = some (.hyp true f_hyp lbl') ∧
              toExpr f_hyp = e_hyp := by
          unfold convertHyp at h_conv
          cases h_find' : db.find? label with
          | none =>
              simp [h_find'] at h_conv
          | some obj =>
              cases obj with
              | const _ =>
                  simp [h_find'] at h_conv
              | var _ =>
                  simp [h_find'] at h_conv
              | assert _ _ _ =>
                  simp [h_find'] at h_conv
              | hyp ess f_hyp lbl' =>
                  cases ess with
                  | false =>
                      cases h_e : toExprOpt f_hyp with
                      | none =>
                          have : False := by
                            simp [h_find', h_e] at h_conv
                          exact this.elim
                      | some e' =>
                          simp [h_find', h_e] at h_conv
                          cases e' with
                          | mk tc syms =>
                              cases syms with
                              | nil =>
                                  cases h_conv
                              | cons s rest =>
                                  cases rest with
                                  | nil =>
                                      cases h_conv
                                  | cons s' rest' =>
                                      cases h_conv
                  | true =>
                      cases h_e : toExprOpt f_hyp with
                      | none =>
                          simp [h_find', h_e] at h_conv
                      | some e' =>
                          simp [h_find', h_e] at h_conv
                          have h_e_eq : e' = e_hyp := by
                            simpa using h_conv
                          have h_toExpr' := (toExprOpt_some_iff_toExpr f_hyp e').1 h_e |>.2
                          have h_toExpr : toExpr f_hyp = e_hyp := by
                            simpa [h_e_eq] using h_toExpr'
                          refine ⟨f_hyp, lbl', ?_, h_toExpr⟩
                          rfl
        rcases h_find_hyp with ⟨f_hyp, lbl', h_find_hyp, h_toExpr_hyp⟩
        have h_find_i : db.find? fr_impl.hyps[i]! = some (.hyp true f_hyp lbl') := by
          have h_lbl_eq' : fr_impl.hyps[i]! = label := by
            simpa using h_lbl_eq
          simpa [h_lbl_eq'] using h_find_hyp
        have h_scoped_i := h_scoped_assert.1.1 i hi
        have h_res_hypsOnly :
            Verify.DB.formulaSymsRespectFrame db f_hyp (Verify.Frame.mk #[] fr_impl.hyps) = true := by
          have h_scoped_i' :
              Verify.DB.formulaSymsRespectFrame db f_hyp (Verify.Frame.mk #[] fr_impl.hyps) = true ∧
              (∀ v, Verify.Sym.var v ∈ f_hyp.toList.tail → FloatDeclaredBefore db fr_impl i v) := by
            simpa [h_find_i] using h_scoped_i
          exact h_scoped_i'.1
        have h_res :
            Verify.DB.formulaSymsRespectFrame db f_hyp fr_impl = true := by
          simpa [formulaSymsRespectFrame_hyps_only] using h_res_hypsOnly
        have h_wff_hyp : WellFormedFormula f_hyp :=
          essential_in_db_wellformed db label f_hyp lbl' h_wf h_find_hyp
        have h_decl_hyp : FormulaSymbolsDeclared db f_hyp := by
          have h_scoped_hyp := h_scoped.2 label (.hyp true f_hyp lbl') h_find_hyp
          exact h_scoped_hyp.2
        exact exprVarsInScope_of_formula db fr_impl fr f_hyp e_hyp
          h_fr h_frame_wf h_wff_hyp h_res h_decl_hyp h_toExpr_hyp

/-- The statement a `$p` claim stores, with its trimmed frame, is in scope at the state before
it. -/
theorem frameExprsInScope_of_trim (db : Verify.DB) (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDB db) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_trim : db.trimFrame' f = .ok frImpl) (h_fr : toFrame db frImpl = some fr)
    (h_head : f.hasConstHead = true) (h_decl : FormulaSymbolsDeclared db f) :
    Spec.FrameExprsInScope (toConsts db) fr (toExpr f) :=
  frameExprsInScope_of_scoped db h_wf h_scoped frImpl fr f h_fr
    (ParserOps.trimFrame'_success_implies_wellformed_frame db f frImpl h_wf h_trim)
    (wellFormedFormula_of_hasConstHead h_head)
    ⟨ParserOps.trimFrame'_success_implies_scoped_frame db f frImpl h_scoped h_trim,
      ParserOps.trimFrame'_success_implies_formulaSymsRespectFrame db f frImpl h_wf h_scoped
        h_decl h_trim,
      h_decl⟩

/-- A name that is not an object of the database is not a mandatory variable of a claim whose
symbols are declared. -/
theorem notMandatory_of_fresh (db : Verify.DB) (h_scoped : WellScopedDB db) (f : Verify.Formula)
    (h_decl : FormulaSymbolsDeclared db f) {d : String} (h_fresh : db.find? d = none) :
    NotMandatory db f d := by
  have h_not_var : db.isVar d = false := by
    simp [Verify.DB.isVar, h_fresh]
  have key : ∀ g : Verify.Formula, FormulaSymbolsDeclared db g →
      Verify.Sym.var d ∉ g.toList.tail := by
    intro g hg hmem
    have h := hg (Verify.Sym.var d) (List.mem_of_mem_tail hmem)
    simp only at h
    rw [h_not_var] at h
    cases h
  refine ⟨key f h_decl, fun l _ g nm h_find => key g ?_⟩
  exact (h_scoped.2 l (.hyp true g nm) h_find).2

end Scope

end Metamath.CheckerCompleteness
