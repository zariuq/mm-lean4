/-
Stored-statement soundness for the streaming Metamath verifier.

The operational checker must use the full active frame while checking a proof:
proof-local dummy variables can occur there.  The assertion stored in the
database instead contains the trimmed mandatory frame.  `Metamath.Spec.StoredStatement`
connects those two levels through `Statement.untrim`; this module applies it to
the checker's runs and eliminates earlier derived theorems from the final axiom
set.
-/

import Metamath.PrefixProvability.Checker
import Metamath.Spec.StoredStatement

set_option autoImplicit false

namespace Metamath.StoredStatementSoundness

open Metamath
open Metamath.Verify
open Metamath.Kernel (toDatabase toFrame toExpr)
open Metamath.Spec
open Metamath.Spec.Equivalence
namespace Runtime

open Metamath.Spec.StoredStatement
open PrefixProvability.Checker

private theorem List.mapM_option_congr {α β : Type}
    (f g : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) :
    @List.mapM Option _ α β f xs = @List.mapM Option _ α β g xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.mapM_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Frame conversion is stable under any database extension that preserves
all already-present objects. -/
theorem toFrame_stable_of_find_mono
    (sourceDB targetDB : DB) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_mono : ∀ label obj, sourceDB.find? label = some obj →
      targetDB.find? label = some obj)
    (h_frame : Kernel.toFrame sourceDB frImpl = some fr) :
    Kernel.toFrame targetDB frImpl = some fr := by
  have h_convert : ∀ label ∈ frImpl.hyps.toList,
      Kernel.convertHyp targetDB label = Kernel.convertHyp sourceDB label := by
    intro label h_label
    obtain ⟨hyp, h_conv, _h_mem⟩ :=
      Kernel.convertHyp_mem_hyps sourceDB frImpl fr label h_frame h_label
    cases h_find : sourceDB.find? label with
    | none =>
        unfold Kernel.convertHyp at h_conv
        simp [h_find] at h_conv
    | some obj =>
        have h_find_target := h_mono label obj h_find
        unfold Kernel.convertHyp
        rw [h_find_target, h_find]
  unfold Kernel.toFrame at h_frame ⊢
  have h_map := List.mapM_option_congr
    (Kernel.convertHyp targetDB) (Kernel.convertHyp sourceDB)
    frImpl.hyps.toList h_convert
  rw [h_map]
  exact h_frame

/-- Pointwise object preservation induces inclusion of the projected spec
databases. -/
theorem toDatabase_subset_of_find_mono
    (sourceDB targetDB : DB)
    (h_source_wf : WF.WellFormedDB sourceDB)
    (h_mono : ∀ label obj, sourceDB.find? label = some obj →
      targetDB.find? label = some obj)
    (sourceΓ targetΓ : Spec.Database)
    (h_sourceΓ : Kernel.toDatabase sourceDB = some sourceΓ)
    (h_targetΓ : Kernel.toDatabase targetDB = some targetΓ) :
    Kernel.SpecDBSubset sourceΓ targetΓ := by
  intro label entry h_lookup
  obtain ⟨fmla, frImpl, name, h_find, h_frame, h_expr⟩ :=
    Kernel.toDatabase_lookup sourceDB sourceΓ label entry.1 entry.2
      h_sourceΓ h_lookup
  have h_find_target := h_mono label (.assert fmla frImpl name) h_find
  have h_frame_target := toFrame_stable_of_find_mono sourceDB targetDB
    frImpl entry.1 h_mono h_frame
  have h_formula_wf : WF.WellFormedFormula fmla :=
    WF.assert_formula_wf_of_db h_source_wf h_find
  have h_expr_opt : Kernel.toExprOpt fmla = some entry.2 :=
    (Kernel.toExprOpt_some_iff_toExpr fmla entry.2).2
      ⟨h_formula_wf.1, h_expr⟩
  unfold Kernel.toDatabase at h_targetΓ
  injection h_targetΓ with h_target_eq
  rw [← h_target_eq]
  simp [Kernel.toDatabaseTotal, h_find_target, h_frame_target, h_expr_opt]

/-- Variables active in a prefix frame remain variables in every registry
extension, hence cannot become constants later. -/
theorem frameVarsDisjointConsts_of_find_mono
    (sourceDB targetDB : DB) (sourceImpl : Verify.Frame)
    (source : Spec.Frame)
    (h_source : Kernel.toFrame sourceDB sourceImpl = some source)
    (h_source_wf : WF.WellFormedFrame sourceDB sourceImpl)
    (h_source_scoped : WF.WellScopedDB sourceDB)
    (h_mono : ∀ label obj, sourceDB.find? label = some obj →
      targetDB.find? label = some obj) :
    Spec.FrameVarsDisjointConsts (Kernel.toConsts targetDB) source := by
  intro v h_v h_const
  have h_name : v.v ∈ Kernel.varNames source.vars :=
    (Kernel.varNames_mem_iff source.vars v.v).2 h_v
  have h_float : v.v ∈ DB.frameFloatVars sourceDB sourceImpl :=
    (Kernel.frameFloatVars_mem_iff_vars sourceDB sourceImpl source h_source
      h_source_wf v.v).2 h_name
  have h_is_var : sourceDB.isVar v.v = true :=
    Kernel.frameFloatVars_mem_isVar sourceDB sourceImpl h_source_scoped v.v h_float
  cases h_find : sourceDB.find? v.v with
  | none => simp [DB.isVar, h_find] at h_is_var
  | some obj =>
      cases obj with
      | var name =>
          have h_find_target := h_mono v.v (.var name) h_find
          simp [Kernel.toConsts, DB.isConst, h_find_target] at h_const
      | const name => simp [DB.isVar, h_find] at h_is_var
      | hyp ess f name => simp [DB.isVar, h_find] at h_is_var
      | assert f fr name => simp [DB.isVar, h_find] at h_is_var

/-- The mandatory source-variable names computed by `DB.trimFrame`. -/
def trimVars (db : DB) (fmla : Verify.Formula) : Std.HashSet String :=
  let vars0 : Std.HashSet String := fmla.foldlVars ∅ Std.HashSet.insert
  Id.run
    (forIn db.frame.hyps vars0 (fun l r =>
      match db.find? l with
      | some (.hyp true f _) =>
          pure (ForInStep.yield (f.foldlVars r Std.HashSet.insert))
      | _ => pure (ForInStep.yield r)))

@[simp] theorem trimFrame_hyps_eq (db : DB) (fmla : Verify.Formula) :
    (db.trimFrame fmla).2.hyps =
      DB.trimFrameHyps db (trimVars db fmla) db.frame.hyps := by
  rfl

/-- The operational DV loop is exactly a stable filter by the mandatory
variable set. -/
theorem trimFrame_dj_toList_eq_filter (db : DB) (fmla : Verify.Formula) :
    (db.trimFrame fmla).2.dj.toList =
      db.frame.dj.toList.filter
        (fun p => (trimVars db fmla).contains p.1 &&
          (trimVars db fmla).contains p.2) := by
  have foldl_push_filter :
      ∀ (ls : List Verify.DJ)
        (pred : Verify.DJ → Bool)
        (acc : Array Verify.DJ),
        (ls.foldl (fun acc a => if pred a then acc.push a else acc) acc).toList =
          acc.toList ++ ls.filter pred := by
    intro ls pred acc
    induction ls generalizing acc with
    | nil => simp
    | cons a rest ih =>
        by_cases h_pred : pred a = true
        · simp [List.foldl, List.filter, h_pred, ih, Array.toList_push,
            List.append_assoc]
        · simp [List.foldl, List.filter, h_pred, ih]
  have h_body :
      (fun (v : Verify.DJ) (r : Array Verify.DJ) =>
        if (trimVars db fmla).contains v.1 &&
            (trimVars db fmla).contains v.2 then
          (pure (ForInStep.yield (r.push v)) :
            Id (ForInStep (Array Verify.DJ)))
        else
          (pure (ForInStep.yield r) :
            Id (ForInStep (Array Verify.DJ)))) =
      (fun (v : Verify.DJ) (r : Array Verify.DJ) =>
        (pure
          (ForInStep.yield
            (if (trimVars db fmla).contains v.1 &&
                (trimVars db fmla).contains v.2 then r.push v else r)) :
          Id (ForInStep (Array Verify.DJ)))) := by
    funext v r
    by_cases h : (trimVars db fmla).contains v.1 &&
        (trimVars db fmla).contains v.2 <;> simp [h]
  have h_fold :=
    (_root_.List.ArrayListExt.Array.idRun_forIn_yield_eq_foldl
      (arr := db.frame.dj)
      (init := #[])
      (step := fun (acc : Array Verify.DJ) (a : Verify.DJ) =>
        if (trimVars db fmla).contains a.1 &&
            (trimVars db fmla).contains a.2 then acc.push a else acc))
  have h_loop :
      Id.run
          (forIn db.frame.dj #[] (fun (v : Verify.DJ)
            (r : Array Verify.DJ) =>
            if (trimVars db fmla).contains v.1 &&
                (trimVars db fmla).contains v.2 then
              pure (ForInStep.yield (r.push v))
            else pure (ForInStep.yield r))) =
        db.frame.dj.toList.foldl
          (fun (acc : Array Verify.DJ) (a : Verify.DJ) =>
            if (trimVars db fmla).contains a.1 &&
                (trimVars db fmla).contains a.2 then acc.push a else acc)
          #[] := by
    rw [h_body]
    exact h_fold
  have h_def :
      (db.trimFrame fmla).2.dj =
        Id.run
          (forIn db.frame.dj #[] (fun (v : Verify.DJ)
            (r : Array Verify.DJ) =>
            if (trimVars db fmla).contains v.1 &&
                (trimVars db fmla).contains v.2 then
              pure (ForInStep.yield (r.push v))
            else pure (ForInStep.yield r))) := by
    rfl
  rw [h_def, h_loop]
  simpa using
    (foldl_push_filter db.frame.dj.toList
      (fun p => (trimVars db fmla).contains p.1 &&
        (trimVars db fmla).contains p.2) #[])

/-- Membership in the trimmed operational hypothesis array records both the
source index and the fact that `trimFrameKeep` admitted that source entry. -/
theorem trimFrameHyps_mem_iff
    (db : DB) (vars : Std.HashSet String) (hyps : Array String) (label : String) :
    label ∈ (DB.trimFrameHyps db vars hyps).toList ↔
      ∃ i, ∃ hi : i < hyps.size, hyps[i] = label ∧
        DB.trimFrameKeep db vars hyps[i] = true := by
  constructor
  · intro h_mem
    have h_pairs :
        ∃ p, p ∈ (DB.trimFrameHypsPairs db vars hyps).toList ∧ p.2 = label := by
      simpa [DB.trimFrameHyps, Array.toList_map, List.mem_map] using h_mem
    obtain ⟨p, h_p, h_label⟩ := h_pairs
    have h_p' :
        p ∈ DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
      simpa [DB.trimFrameHypsPairs] using h_p
    rcases List.mem_map.mp h_p' with ⟨q, h_q, h_pq⟩
    rcases List.mem_filter.mp h_q with ⟨h_zip, h_keep⟩
    have h_get : hyps.toList[q.2]? = some q.1 :=
      (List.mem_zipIdx_iff_getElem?).mp h_zip
    rcases (List.getElem?_eq_some_iff).mp h_get with ⟨hi, h_at⟩
    refine ⟨q.2, by simpa [Array.length_toList] using hi, ?_, ?_⟩
    · have h_q_label : q.1 = label := by
        exact (congrArg Prod.snd h_pq).trans h_label
      simpa [Array.getElem_toList] using h_at.trans h_q_label
    · have h_at' : hyps[q.2] = q.1 := by
        simpa using h_at
      simpa [h_at'] using h_keep
  · rintro ⟨i, hi, h_label, h_keep⟩
    subst label
    exact ParserOps.trimFrameHyps_mem_of_keep db vars hyps hi h_keep

/-- Converting an injective operational hypothesis subsequence yields a
semantic hypothesis subset. -/
theorem toFrame_hyps_subset_of_subsequence
    (db : DB) (sourceImpl targetImpl : Verify.Frame)
    (source target : Spec.Frame)
    (h_subseq : ParserOps.IsInjectiveSubsequence
      sourceImpl.hyps targetImpl.hyps)
    (h_source : Kernel.toFrame db sourceImpl = some source)
    (h_target : Kernel.toFrame db targetImpl = some target) :
    ∀ h, h ∈ target.hyps → h ∈ source.hyps := by
  intro h h_mem
  obtain ⟨label, h_label_target, h_convert⟩ :=
    Kernel.hyps_mem_has_label db targetImpl target h h_target h_mem
  obtain ⟨i, hi, h_at⟩ :=
    Array.toList_mem_implies_index targetImpl.hyps label h_label_target
  obtain ⟨indexMap, h_maps, _h_injective⟩ := h_subseq
  let j := (indexMap i hi).val
  have hj : j < sourceImpl.hyps.size := (indexMap i hi).property
  have h_target_source : targetImpl.hyps[i]'hi = sourceImpl.hyps[j]'hj :=
    h_maps i hi
  have h_at' : targetImpl.hyps[i]'hi = label := by
    have h_bang := Array.getBang_eq_get_nat
      (a := targetImpl.hyps) (i := i) (h := hi)
    simpa [h_bang] using h_at
  have h_source_label : sourceImpl.hyps[j]'hj = label := by
    exact h_target_source.symm.trans h_at'
  have h_label_source : label ∈ sourceImpl.hyps.toList := by
    have h_mem_at : sourceImpl.hyps.toList[j] ∈ sourceImpl.hyps.toList :=
      List.getElem_mem (by simpa [Array.length_toList] using hj)
    have h_toList : sourceImpl.hyps.toList[j] = sourceImpl.hyps[j]'hj :=
      Array.getElem_toList (xs := sourceImpl.hyps) (i := j) hj
    simpa [h_toList, h_source_label] using h_mem_at
  obtain ⟨h_source_spec, h_convert_source, h_mem_source⟩ :=
    Kernel.convertHyp_mem_hyps db sourceImpl source label h_source h_label_source
  have h_eq : h_source_spec = h :=
    Option.some.inj (h_convert_source.symm.trans h_convert)
  simpa [h_eq] using h_mem_source

/-- Every target variable was selected by `trimFrame`'s mandatory-variable
set. -/
theorem trimVars_contains_of_target_var
    (db : DB) (fmla : Verify.Formula) (targetImpl : Verify.Frame)
    (target : Spec.Frame)
    (h_trim : db.trimFrame' fmla = .ok targetImpl)
    (h_target : Kernel.toFrame db targetImpl = some target)
    (h_target_wf : WF.WellFormedFrame db targetImpl)
    {v : Spec.Variable} (h_v : v ∈ target.vars) :
    (trimVars db fmla).contains v.v = true := by
  have h_name : v.v ∈ Kernel.varNames target.vars :=
    (Kernel.varNames_mem_iff target.vars v.v).2 h_v
  have h_float : v.v ∈ DB.frameFloatVars db targetImpl :=
    (Kernel.frameFloatVars_mem_iff_vars db targetImpl target h_target
      h_target_wf v.v).2 h_name
  rcases (WF.frameFloatVars_mem_iff db targetImpl.hyps v.v).1 h_float with
    ⟨label, f, lbl, h_label_target, h_find, _h_shape, h_f1⟩
  have h_trim_pair : db.trimFrame fmla = (true, targetImpl) :=
    ParserOps.trimFrame'_ok_iff.mp h_trim
  have h_hyps : targetImpl.hyps =
      DB.trimFrameHyps db (trimVars db fmla) db.frame.hyps := by
    have h_output : (db.trimFrame fmla).2.hyps = targetImpl.hyps :=
      congrArg (fun p => p.2.hyps) h_trim_pair
    exact h_output.symm.trans (trimFrame_hyps_eq db fmla)
  have h_label_trimmed :
      label ∈ (DB.trimFrameHyps db (trimVars db fmla) db.frame.hyps).toList := by
    simpa [h_hyps] using h_label_target
  obtain ⟨i, hi, h_at, h_keep⟩ :=
    (trimFrameHyps_mem_iff db (trimVars db fmla) db.frame.hyps label).mp
      h_label_trimmed
  have h_find_source :
      db.find? db.frame.hyps[i] = some (.hyp false f lbl) := by
    simpa [h_at] using h_find
  have h_f1_value : f[1]!.value = v.v := by
    simp [h_f1, Verify.Sym.value]
  simpa [DB.trimFrameKeep, h_find_source, h_f1_value] using h_keep

/-- A source DV pair whose endpoints are mandatory is retained verbatim by
the operational trimming loop. -/
theorem trimFrame_dj_mem_of_mandatory
    (db : DB) (fmla : Verify.Formula) (targetImpl : Verify.Frame)
    (h_trim : db.trimFrame' fmla = .ok targetImpl)
    {p : Verify.DJ} (h_mem : p ∈ db.frame.dj.toList)
    (h_left : (trimVars db fmla).contains p.1 = true)
    (h_right : (trimVars db fmla).contains p.2 = true) :
    p ∈ targetImpl.dj.toList := by
  have h_trim_pair : db.trimFrame fmla = (true, targetImpl) :=
    ParserOps.trimFrame'_ok_iff.mp h_trim
  have h_output : (db.trimFrame fmla).2.dj = targetImpl.dj :=
    congrArg (fun x => x.2.dj) h_trim_pair
  have h_filter : p ∈
      db.frame.dj.toList.filter
        (fun q => (trimVars db fmla).contains q.1 &&
          (trimVars db fmla).contains q.2) := by
    exact List.mem_filter.mpr ⟨h_mem, by simp [h_left, h_right]⟩
  have h_eq := trimFrame_dj_toList_eq_filter db fmla
  have h_output_mem : p ∈ (db.trimFrame fmla).2.dj.toList := by
    rw [h_eq]
    exact h_filter
  simpa [h_output] using h_output_mem

/-- `trimFrameKeep` never drops an essential hypothesis, so every converted
source essential occurs in the converted target frame. -/
theorem essential_mem_target_of_trim
    (db : DB) (fmla : Verify.Formula) (targetImpl : Verify.Frame)
    (source target : Spec.Frame)
    (h_wf : WF.WellFormedDB db)
    (h_trim : db.trimFrame' fmla = .ok targetImpl)
    (h_source : Kernel.toFrame db db.frame = some source)
    (h_target : Kernel.toFrame db targetImpl = some target)
    {e_hyp : Spec.Expr}
    (h_mem : Spec.Hyp.essential e_hyp ∈ source.hyps) :
    Spec.Hyp.essential e_hyp ∈ target.hyps := by
  obtain ⟨label, h_label_source, h_convert⟩ :=
    Kernel.hyps_mem_has_label db db.frame source
      (Spec.Hyp.essential e_hyp) h_source h_mem
  obtain ⟨f, lbl, h_find, _h_head⟩ :=
    Kernel.convertHyp_essential_implies_hasConstHead db label e_hyp
      h_wf.1 h_label_source h_convert
  obtain ⟨i, hi, h_at⟩ :=
    Array.toList_mem_implies_index db.frame.hyps label h_label_source
  have h_find_at : db.find? db.frame.hyps[i] = some (.hyp true f lbl) := by
    have h_at' : db.frame.hyps[i] = label := by
      have h_bang := Array.getBang_eq_get_nat
        (a := db.frame.hyps) (i := i) (h := hi)
      simpa [h_bang] using h_at
    simpa [h_at'] using h_find
  have h_keep : DB.trimFrameKeep db (trimVars db fmla) db.frame.hyps[i] = true := by
    simp [DB.trimFrameKeep, h_find_at]
  have h_label_trimmed : label ∈
      (DB.trimFrameHyps db (trimVars db fmla) db.frame.hyps).toList := by
    have h_mem_at := ParserOps.trimFrameHyps_mem_of_keep
      db (trimVars db fmla) db.frame.hyps hi h_keep
    have h_at' : db.frame.hyps[i] = label := by
      have h_bang := Array.getBang_eq_get_nat
        (a := db.frame.hyps) (i := i) (h := hi)
      simpa [h_bang] using h_at
    simpa [h_at'] using h_mem_at
  have h_trim_pair : db.trimFrame fmla = (true, targetImpl) :=
    ParserOps.trimFrame'_ok_iff.mp h_trim
  have h_hyps : targetImpl.hyps =
      DB.trimFrameHyps db (trimVars db fmla) db.frame.hyps := by
    have h_output : (db.trimFrame fmla).2.hyps = targetImpl.hyps :=
      congrArg (fun p => p.2.hyps) h_trim_pair
    exact h_output.symm.trans (trimFrame_hyps_eq db fmla)
  have h_label_target : label ∈ targetImpl.hyps.toList := by
    simpa [h_hyps] using h_label_trimmed
  obtain ⟨targetHyp, h_convert_target, h_target_mem⟩ :=
    Kernel.convertHyp_mem_hyps db targetImpl target label h_target h_label_target
  have h_eq : targetHyp = Spec.Hyp.essential e_hyp :=
    Option.some.inj (h_convert_target.symm.trans h_convert)
  simpa [h_eq] using h_target_mem

/-- Concrete `trimFrame'` execution supplies every structural premise of the
active-frame to stored-statement bridge.  `h_target_scope` is the ordinary
well-scoping fact for the stored assertion; no provability assumption occurs
in this theorem. -/
theorem frameReduction_of_trim
    (db : DB) (fmla : Verify.Formula) (targetImpl : Verify.Frame)
    (source target : Spec.Frame) (e : Spec.Expr) (consts : Spec.ConstSet)
    (h_wf : WF.WellFormedDB db)
    (h_trim : db.trimFrame' fmla = .ok targetImpl)
    (h_source : Kernel.toFrame db db.frame = some source)
    (h_target : Kernel.toFrame db targetImpl = some target)
    (h_source_disjoint : Spec.FrameVarsDisjointConsts consts source)
    (h_target_scope : Spec.FrameExprsInScope consts target e) :
    StoredStatement.FrameReduction source target e := by
  have h_target_impl_wf : WF.WellFormedFrame db targetImpl :=
    ParserOps.trimFrame'_success_implies_wellformed_frame
      db fmla targetImpl h_wf h_trim
  have h_trim_pair : db.trimFrame fmla = (true, targetImpl) :=
    ParserOps.trimFrame'_ok_iff.mp h_trim
  have h_subseq : ParserOps.IsInjectiveSubsequence
      db.frame.hyps targetImpl.hyps :=
    ParserOps.trimFrame_produces_subsequence h_trim_pair
  have h_hyp_subset : ∀ h, h ∈ target.hyps → h ∈ source.hyps :=
    toFrame_hyps_subset_of_subsequence db db.frame targetImpl source target
      h_subseq h_source h_target
  have h_source_wf : Spec.Equivalence.FrameWellFormed source := by
    exact ⟨
      Kernel.floatUnique_of_uniqueFloatVars db db.frame source h_source
        h_wf.1 h_wf.1.2,
      Kernel.floatVarNoDup_of_uniqueFloatVars db db.frame source h_source
        h_wf.1 h_wf.1.2⟩
  have h_target_wf : Spec.Equivalence.FrameWellFormed target := by
    exact ⟨
      Kernel.floatUnique_of_uniqueFloatVars db targetImpl target h_target
        h_target_impl_wf h_target_impl_wf.2,
      Kernel.floatVarNoDup_of_uniqueFloatVars db targetImpl target h_target
        h_target_impl_wf h_target_impl_wf.2⟩
  refine {
    sourceWellFormed := h_source_wf
    targetWellFormed := h_target_wf
    typesAgree := StoredStatement.frameMapTypesAgree_of_hyps_subset
      h_source_wf.1 h_hyp_subset
    domainLE := StoredStatement.frameMapDomainLE_of_hyps_subset h_hyp_subset
    conclusionRetained := StoredStatement.exprVarsRetained_of_scopes
      h_source_disjoint h_target_scope.1
    essentialRetained := ?_
    dvRetained := ?_ }
  · intro e_hyp h_essential
    have h_essential_target := essential_mem_target_of_trim db fmla targetImpl
      source target h_wf h_trim h_source h_target h_essential
    refine ⟨h_essential_target, ?_⟩
    exact StoredStatement.exprVarsRetained_of_scopes h_source_disjoint
      (h_target_scope.2 (Spec.Hyp.essential e_hyp)
        h_essential_target)
  · intro v w h_source_rel h_v_target h_w_target
    obtain ⟨targetVRv, h_find_v⟩ := h_v_target
    obtain ⟨targetVRw, h_find_w⟩ := h_w_target
    have h_v_mem : v ∈ target.vars := findVR_in_vars h_find_v
    have h_w_mem : w ∈ target.vars := findVR_in_vars h_find_w
    have h_v_mandatory := trimVars_contains_of_target_var db fmla targetImpl
      target h_trim h_target h_target_impl_wf h_v_mem
    have h_w_mandatory := trimVars_contains_of_target_var db fmla targetImpl
      target h_trim h_target h_target_impl_wf h_w_mem
    have h_source_dv := Kernel.toFrame_dv_eq db db.frame source h_source
    have h_target_dv := Kernel.toFrame_dv_eq db targetImpl target h_target
    rcases h_source_rel with ⟨h_ne, h_pair | h_pair⟩
    · rw [h_source_dv] at h_pair
      obtain ⟨p, h_p_mem, h_p_convert⟩ := List.mem_map.mp h_pair
      have h_canonical : Kernel.convertDV (v.v, w.v) = (v, w) := by
        cases v
        cases w
        rfl
      have h_p_eq : p = (v.v, w.v) :=
        Kernel.convertDV_injective (h_p_convert.trans h_canonical.symm)
      subst p
      have h_target_pair := trimFrame_dj_mem_of_mandatory db fmla targetImpl
        h_trim h_p_mem h_v_mandatory h_w_mandatory
      refine ⟨h_ne, Or.inl ?_⟩
      rw [h_target_dv]
      exact List.mem_map.mpr ⟨(v.v, w.v), h_target_pair, h_canonical⟩
    · rw [h_source_dv] at h_pair
      obtain ⟨p, h_p_mem, h_p_convert⟩ := List.mem_map.mp h_pair
      have h_canonical : Kernel.convertDV (w.v, v.v) = (w, v) := by
        cases v
        cases w
        rfl
      have h_p_eq : p = (w.v, v.v) :=
        Kernel.convertDV_injective (h_p_convert.trans h_canonical.symm)
      subst p
      have h_target_pair := trimFrame_dj_mem_of_mandatory db fmla targetImpl
        h_trim h_p_mem h_w_mandatory h_v_mandatory
      refine ⟨h_ne, Or.inr ?_⟩
      rw [h_target_dv]
      exact List.mem_map.mpr ⟨(w.v, v.v), h_target_pair, h_canonical⟩

theorem dbToAxioms_mono {Γ Γ' : Spec.Database}
    (h : Kernel.SpecDBSubset Γ Γ') :
    ∀ s, dbToAxioms Γ s → dbToAxioms Γ' s := by
  intro s hs
  obtain ⟨l, fr, e, h_lookup, h_ctx, h_fmla⟩ := hs
  exact ⟨l, fr, e, h l (fr, e) h_lookup, h_ctx, h_fmla⟩

/-- Registry facts propagate between two recorded entry states in index order. -/
theorem RunTrace.find?_mono_between_members
    {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (i j : Nat)
    (h_i : i < steps.length) (h_j : j < steps.length) (h_le : i ≤ j)
    (n : String) (o : Object)
    (h_find : (steps[i]!).state.db.find? n = some o) :
    (steps[j]!).state.db.find? n = some o := by
  induction h generalizing i j with
  | nil _ _ _ => simp at h_i
  | cons p r rest q h_head h_rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact h_find
          | succ j =>
              simp only [List.getElem!_cons_succ]
              apply h_rest.find?_mono_to_member j (by simpa using h_j) n o
              apply feedToken_find?_mono r.state r.pos r.tk n o
              simpa using h_find
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              apply ih i j (by simpa using h_i) (by simpa using h_j)
                (by omega)
              simpa using h_find

/-- An entry present before step `i` must have been created strictly earlier. -/
theorem RunTrace.creation_before_member
    {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (i j : Nat)
    (h_i : i < steps.length) (h_j : j < steps.length)
    (n : String) (o : Object)
    (h_present : (steps[i]!).state.db.find? n = some o)
    (h_created : CreatesEntry (steps[j]!) n o) : j < i := by
  by_contra h_not
  have h_forward := find?_mono_between_members h i j h_i h_j
    (Nat.le_of_not_gt h_not) n o h_present
  rw [h_created.1] at h_forward
  cases h_forward

/-- The exact stored statement produced by a successful `$p` event is already
provable from the projected pre-insertion database.  The returned database is
used only to identify and validate the stored mandatory frame. -/
theorem finishProof_storedStatement_prefixProvable
    (prefixDB finalDB : DB) (pr : ProofState) (n : String)
    (prefixΓ finalΓ : Spec.Database) (source : Spec.Frame)
    (h_prefix_wf : WF.WellFormedDB prefixDB)
    (h_prefix_scoped : WF.WellScopedDB prefixDB)
    (h_mono : ∀ label obj, prefixDB.find? label = some obj →
      finalDB.find? label = some obj)
    (h_final_db : Kernel.toDatabase finalDB = some finalΓ)
    (h_strong : Spec.Equivalence.WellFormedDatabaseStrong finalΓ
      (Kernel.toConsts finalDB))
    (h_final_wf : WF.WellFormedDB finalDB)
    (h_find_final : finalDB.find? n = some (.assert pr.fmla pr.frame n))
    (h_trim : prefixDB.trimFrame' pr.fmla = .ok pr.frame)
    (h_prefix_db : Kernel.toDatabase prefixDB = some prefixΓ)
    (h_source : Kernel.toFrame prefixDB prefixDB.frame = some source)
    (h_prefix_provable :
      Spec.Provable prefixΓ source (Kernel.toExpr pr.fmla)) :
    ∃ target : Spec.Frame,
      Kernel.toFrame finalDB pr.frame = some target ∧
      (StoredStatement.statementOfFrame target (Kernel.toExpr pr.fmla)).Provable
        (dbToAxioms prefixΓ) := by
  have h_target_impl_wf : WF.WellFormedFrame prefixDB pr.frame :=
    ParserOps.trimFrame'_success_implies_wellformed_frame prefixDB pr.fmla
      pr.frame h_prefix_wf h_trim
  obtain ⟨target, h_target_prefix⟩ :=
    Kernel.toFrame_some_of_wfFrame_any prefixDB pr.frame h_target_impl_wf
  have h_target_final : Kernel.toFrame finalDB pr.frame = some target :=
    toFrame_stable_of_find_mono prefixDB finalDB pr.frame target h_mono
      h_target_prefix
  have h_formula_wf : WF.WellFormedFormula pr.fmla :=
    WF.assert_formula_wf_of_db h_final_wf h_find_final
  have h_expr_opt : Kernel.toExprOpt pr.fmla = some (Kernel.toExpr pr.fmla) :=
    (Kernel.toExprOpt_some_iff_toExpr pr.fmla (Kernel.toExpr pr.fmla)).2
      ⟨h_formula_wf.1, rfl⟩
  have h_lookup_final :
      finalΓ n = some (target, Kernel.toExpr pr.fmla) := by
    unfold Kernel.toDatabase at h_final_db
    injection h_final_db with h_Γ
    rw [← h_Γ]
    simp [Kernel.toDatabaseTotal, h_find_final, h_target_final, h_expr_opt]
  have h_target_scope :
      Spec.FrameExprsInScope (Kernel.toConsts finalDB) target
        (Kernel.toExpr pr.fmla) :=
    h_strong.1.1 n target (Kernel.toExpr pr.fmla) h_lookup_final
  have h_source_disjoint :
      Spec.FrameVarsDisjointConsts (Kernel.toConsts finalDB) source :=
    frameVarsDisjointConsts_of_find_mono prefixDB finalDB prefixDB.frame source
      h_source h_prefix_wf.1 h_prefix_scoped h_mono
  have h_reduction : StoredStatement.FrameReduction source target
      (Kernel.toExpr pr.fmla) :=
    frameReduction_of_trim prefixDB pr.fmla pr.frame source target
      (Kernel.toExpr pr.fmla) (Kernel.toConsts finalDB) h_prefix_wf h_trim
      h_source h_target_prefix h_source_disjoint h_target_scope
  have h_prefix_subset : Kernel.SpecDBSubset prefixΓ finalΓ :=
    toDatabase_subset_of_find_mono prefixDB finalDB h_prefix_wf h_mono
      prefixΓ finalΓ h_prefix_db h_final_db
  have h_prefix_basic :
      Spec.WellFormedDatabase prefixΓ (Kernel.toConsts finalDB) := by
    constructor
    · intro l fr e h_lookup
      exact h_strong.1.1 l fr e (h_prefix_subset l (fr, e) h_lookup)
    · intro l fr e h_lookup
      exact h_strong.1.2 l fr e (h_prefix_subset l (fr, e) h_lookup)
  have h_active_semantic :
      Metamath.Provable (dbToAxioms prefixΓ) (frameToContext source)
        (exprToFormula (varMapOfFrame source) (Kernel.toExpr pr.fmla)) := by
    obtain ⟨proof, finalStack, h_valid, h_stack⟩ := h_prefix_provable
    rw [h_stack] at h_valid
    exact proofValid_to_declarative h_prefix_basic h_source_disjoint h_valid
  exact ⟨target, h_target_final,
    StoredStatement.statementProvable_of_frameReduction h_reduction h_active_semantic⟩

/-- The axiom-event theory exposed by a registry chronology.  Membership records
both a local `$a` finish event and the exact projected statement it creates.
`RunTrace` does not by itself certify full IO-execution membership. -/
def AxiomEventOfTrace (steps : List RunStep) (Γ : Spec.Database) :
    Metamath.Statement → Prop :=
  fun stmt => ∃ (idx : Nat) (n : String) (f : Verify.Formula)
      (fr : Verify.Frame) (lbl : String) (target : Spec.Frame)
      (arr : Array Verify.Sym) (p : TokensParser),
    idx < steps.length ∧
    CreatesEntry (steps[idx]!) n (.assert f fr lbl) ∧
    AxiomFinishEvent (steps[idx]!).state (steps[idx]!).pos
      (steps[idx]!).tk arr p ∧
    p.label = n ∧ f = arr ∧ lbl = n ∧
    Γ n = some (target, Kernel.toExpr f) ∧
    stmt = StoredStatement.statementOfFrame target (Kernel.toExpr f)

/-- Project an implementation assertion lookup into its exact semantic frame
and expression in the returned database. -/
theorem assertion_projection_of_find
    (db : DB) (Γ : Spec.Database) (n : String)
    (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_db : Kernel.toDatabase db = some Γ)
    (h_wf : WF.WellFormedDB db)
    (h_find : db.find? n = some (.assert f fr lbl)) :
    ∃ target : Spec.Frame,
      Kernel.toFrame db fr = some target ∧
      Γ n = some (target, Kernel.toExpr f) := by
  have h_fr_wf : WF.WellFormedFrame db fr :=
    WF.assert_frame_wf_of_db h_wf h_find
  obtain ⟨target, h_target⟩ := Kernel.toFrame_some_of_wfFrame_any db fr h_fr_wf
  have h_formula_wf : WF.WellFormedFormula f :=
    WF.assert_formula_wf_of_db h_wf h_find
  have h_expr_opt : Kernel.toExprOpt f = some (Kernel.toExpr f) :=
    (Kernel.toExprOpt_some_iff_toExpr f (Kernel.toExpr f)).2
      ⟨h_formula_wf.1, rfl⟩
  refine ⟨target, h_target, ?_⟩
  unfold Kernel.toDatabase at h_db
  injection h_db with h_Γ
  rw [← h_Γ]
  simp [Kernel.toDatabaseTotal, h_find, h_target, h_expr_opt]

/-! ## Accepted-run stored-statement theorem -/

/-- Every assertion in an accepted certified single-pass run is either tied to
a local `$a` finish event, or it was stored by a `$p` finish event at a parser
state that does not yet contain it, and its exact stored declarative statement
is provable from the assertions of that state.  Every object of that state is
in the returned database, so that witness's proof cannot cite the statement
itself. The conclusion does not retain membership of the witnesses in the
actual run; `RunEmission.check_every_theorem_provable_from_run_axiom_events`
retains that membership and the `$a`/`$p` classification. -/
theorem check_storedStatements_writtenProof
    (fname : String) (config : ModeConfig) (h_cfg : config.IsSound)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : check fname config w = .ok db w')
    (h_success : db.error? = none) :
    ∃ Γ : Spec.Database,
      Kernel.toDatabase db = some Γ ∧
      Spec.Equivalence.WellFormedDatabaseStrong Γ (Kernel.toConsts db) ∧
      ∀ n f fr lbl, db.find? n = some (.assert f fr lbl) →
        (∃ (s : ParserState) (i : Nat) (tk : ByteSlice)
            (arr : Array Verify.Sym) (p : TokensParser),
            AxiomFinishEvent s i tk arr p ∧
            p.label = n ∧ f = arr ∧ lbl = n ∧
            f.hasConstHead = true ∧
            s.db.find? n = none ∧
            s.db.trimFrame' arr = .ok fr)
        ∨ (∃ (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState)
            (prefixΓ : Spec.Database) (target : Spec.Frame),
            FinishProofEvent s i tk pr ∧
            pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
            s.db.find? n = none ∧
            (∀ l o, s.db.find? l = some o → db.find? l = some o) ∧
            Kernel.toDatabase s.db = some prefixΓ ∧
            Kernel.toFrame db fr = some target ∧
            (StoredStatement.statementOfFrame target (Kernel.toExpr f)).Provable
              (dbToAxioms prefixΓ)) := by
  have h_final :=
    check_database_wellFormed_strong fname config h_cfg w w' db
      h_run h_success
  let Γ := Classical.choose h_final
  have h_final_tail := Classical.choose_spec h_final
  have h_final_db : Kernel.toDatabase db = some Γ := h_final_tail.1
  have h_strong :
      Spec.Equivalence.WellFormedDatabaseStrong Γ (Kernel.toConsts db) :=
    h_final_tail.2.1
  have h_final_wf : WF.WellFormedDB db := h_final_tail.2.2.1
  obtain ⟨steps, q, h_trace, h_steps_inv, h_pointwise,
      h_member_mono, h_origin, h_payload⟩ :=
    check_registry_insertionHistory_exactly_one fname config h_cfg w w'
      db h_run h_success
  refine ⟨Γ, h_final_db, h_strong, ?_⟩
  intro n f fr lbl h_find_final
  obtain ⟨idx, ⟨h_idx, h_creates⟩, _h_unique⟩ :=
    h_origin n f fr lbl h_find_final
  have h_step_mem : steps[idx]! ∈ steps := by
    rw [getElem!_pos steps idx h_idx]
    exact List.getElem_mem h_idx
  obtain ⟨h_inv, h_ghost, _h_error_free⟩ :=
    h_steps_inv (steps[idx]!) h_step_mem
  have h_mono : ∀ label obj,
      (steps[idx]!).state.db.find? label = some obj →
      db.find? label = some obj :=
    h_member_mono idx h_idx
  rcases h_payload idx n f fr lbl h_idx h_creates with h_axiom | h_theorem
  · obtain ⟨arr, p, h_event, h_label, h_fmla, h_lbl, h_head,
      h_fresh, _h_insert, h_trim⟩ := h_axiom
    have h_head' : f.hasConstHead = true := by
      rw [h_fmla]
      exact h_head
    exact Or.inl ⟨(steps[idx]!).state, (steps[idx]!).pos,
      (steps[idx]!).tk, arr, p, h_event, h_label, h_fmla, h_lbl,
      h_head', h_fresh, h_trim⟩
  · obtain ⟨pr, prefixΓ, source, h_event, h_label, h_fmla, h_frame,
      h_lbl, h_fresh, _h_insert, h_prefix_db, h_source, h_prefix_provable⟩ :=
        h_theorem
    have h_trim : (steps[idx]!).state.db.trimFrame' pr.fmla = .ok pr.frame :=
      finishProofEvent_trimFrame (steps[idx]!).state (steps[idx]!).pos
        (steps[idx]!).tk pr h_ghost h_event
    have h_find_final' : db.find? n = some (.assert pr.fmla pr.frame n) := by
      simpa [h_label, h_fmla, h_frame, h_lbl] using h_find_final
    have h_prefix_provable' :
        Spec.Provable prefixΓ source (Kernel.toExpr pr.fmla) := by
      rw [h_fmla]
      exact h_prefix_provable
    obtain ⟨target, h_target_final, h_exact⟩ :=
      finishProof_storedStatement_prefixProvable (steps[idx]!).state.db db pr n
        prefixΓ Γ source h_inv.1 h_inv.2.1.1 h_mono h_final_db h_strong
        h_final_wf h_find_final' h_trim h_prefix_db h_source h_prefix_provable'
    exact Or.inr ⟨(steps[idx]!).state, (steps[idx]!).pos, (steps[idx]!).tk, pr,
      prefixΓ, target, h_event, h_label, h_fmla, h_frame, h_lbl, h_fresh, h_mono,
      h_prefix_db, by simpa [h_frame] using h_target_final,
      by simpa [h_fmla] using h_exact⟩

/-- **Trace-relative derived-rule elimination.** In an accepted certified run,
every stored `$p` statement is declaratively provable using only `$a`-classified
events in the emitted registry chronology.  Earlier `$p` statements are
eliminated by cut along strict creation order, and the local written proof is
interpreted against its pre-insertion database, so it cannot use self-citation.

The theorem deliberately inherits `RunTrace`'s boundary: registry seams do not
certify that every recorded parser state is a state of the concrete IO run. -/
theorem check_every_theorem_provable_from_trace_axiom_events
    (fname : String) (config : ModeConfig) (h_cfg : config.IsSound)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : check fname config w = .ok db w')
    (h_success : db.error? = none) :
    ∃ (Γ : Spec.Database) (steps : List RunStep) (q : ParserState),
      Kernel.toDatabase db = some Γ ∧
      RunTrace (singlePassInitialState config) steps q ∧
      (∀ n, q.db.find? n = db.find? n) ∧
      ∀ n f fr lbl, db.find? n = some (.assert f fr lbl) →
        ∃ (idx : Nat) (target : Spec.Frame),
          idx < steps.length ∧
          CreatesEntry (steps[idx]!) n (.assert f fr lbl) ∧
          Kernel.toFrame db fr = some target ∧
          Γ n = some (target, Kernel.toExpr f) ∧
          ((∃ (arr : Array Verify.Sym) (p : TokensParser),
              AxiomFinishEvent (steps[idx]!).state (steps[idx]!).pos
                (steps[idx]!).tk arr p ∧
              p.label = n ∧ f = arr ∧ lbl = n ∧
              AxiomEventOfTrace steps Γ
                (StoredStatement.statementOfFrame target (Kernel.toExpr f)))
            ∨ (∃ pr : ProofState,
              FinishProofEvent (steps[idx]!).state (steps[idx]!).pos
                (steps[idx]!).tk pr ∧
              pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
              (StoredStatement.statementOfFrame target (Kernel.toExpr f)).Provable
                (AxiomEventOfTrace steps Γ))) := by
  have h_final :=
    check_database_wellFormed_strong fname config h_cfg w w' db
      h_run h_success
  let Γ := Classical.choose h_final
  have h_final_tail := Classical.choose_spec h_final
  have h_final_db : Kernel.toDatabase db = some Γ := h_final_tail.1
  have h_strong :
      Spec.Equivalence.WellFormedDatabaseStrong Γ (Kernel.toConsts db) :=
    h_final_tail.2.1
  have h_final_wf : WF.WellFormedDB db := h_final_tail.2.2.1
  obtain ⟨steps, q, h_trace, h_steps_inv, h_pointwise,
      h_member_mono, h_origin, h_payload⟩ :=
    check_registry_insertionHistory_exactly_one fname config h_cfg w w'
      db h_run h_success
  let A := AxiomEventOfTrace steps Γ
  have h_created : ∀ idx : Nat, idx < steps.length →
      ∀ n f fr lbl,
        db.find? n = some (.assert f fr lbl) →
        CreatesEntry (steps[idx]!) n (.assert f fr lbl) →
        ∃ target : Spec.Frame,
          Kernel.toFrame db fr = some target ∧
          Γ n = some (target, Kernel.toExpr f) ∧
          (A (StoredStatement.statementOfFrame target (Kernel.toExpr f)) ∨
            (StoredStatement.statementOfFrame target (Kernel.toExpr f)).Provable A) := by
    intro idx
    induction idx using Nat.strongRecOn with
    | ind idx ih =>
      intro h_idx n f fr lbl h_find_final h_creates
      have h_step_mem : steps[idx]! ∈ steps := by
        rw [getElem!_pos steps idx h_idx]
        exact List.getElem_mem h_idx
      obtain ⟨h_inv, h_ghost, _h_error_free⟩ :=
        h_steps_inv (steps[idx]!) h_step_mem
      have h_mono : ∀ label obj,
          (steps[idx]!).state.db.find? label = some obj →
          db.find? label = some obj :=
        h_member_mono idx h_idx
      obtain ⟨target, h_target_final, h_lookup_final⟩ :=
        assertion_projection_of_find db Γ n f fr lbl h_final_db h_final_wf
          h_find_final
      rcases h_payload idx n f fr lbl h_idx h_creates with h_axiom | h_theorem
      · obtain ⟨arr, p, h_event, h_label, h_fmla, h_lbl, _h_head,
          _h_fresh, _h_insert, _h_trim⟩ := h_axiom
        refine ⟨target, h_target_final, h_lookup_final, Or.inl ?_⟩
        change AxiomEventOfTrace steps Γ
          (StoredStatement.statementOfFrame target (Kernel.toExpr f))
        exact ⟨idx, n, f, fr, lbl, target, arr, p, h_idx, h_creates,
          h_event, h_label, h_fmla, h_lbl, h_lookup_final, rfl⟩
      · obtain ⟨pr, prefixΓ, source, h_event, h_label, h_fmla, h_frame,
          h_lbl, _h_fresh, _h_insert, h_prefix_db, h_source,
          h_prefix_provable⟩ := h_theorem
        have h_trim :
            (steps[idx]!).state.db.trimFrame' pr.fmla = .ok pr.frame :=
          finishProofEvent_trimFrame (steps[idx]!).state (steps[idx]!).pos
            (steps[idx]!).tk pr h_ghost h_event
        have h_find_final' :
            db.find? n = some (.assert pr.fmla pr.frame n) := by
          simpa [h_label, h_fmla, h_frame, h_lbl] using h_find_final
        obtain ⟨storedTarget, h_stored_target, h_prefix_exact⟩ :=
          finishProof_storedStatement_prefixProvable
            (steps[idx]!).state.db db pr n prefixΓ Γ source h_inv.1
            h_inv.2.1.1 h_mono h_final_db h_strong h_final_wf h_find_final'
            h_trim h_prefix_db h_source (by
              rw [h_fmla]
              exact h_prefix_provable)
        have h_source_exact :
            (StoredStatement.statementOfFrame storedTarget
              (Kernel.toExpr pr.fmla)).Provable A := by
          apply StoredStatement.replaceDerivedAxioms h_prefix_exact
          intro a ha
          obtain ⟨l, specFr, e, h_lookup_prefix, h_ctx, h_afmla⟩ := ha
          obtain ⟨f₀, fr₀, lbl₀, h_find_prefix, h_toFrame_prefix,
              h_toExpr⟩ :=
            Kernel.toDatabase_lookup (steps[idx]!).state.db prefixΓ l specFr e
              h_prefix_db h_lookup_prefix
          have h_find_final₀ : db.find? l = some (.assert f₀ fr₀ lbl₀) :=
            h_mono l (.assert f₀ fr₀ lbl₀) h_find_prefix
          obtain ⟨j, ⟨h_j, h_create_j⟩, _h_unique_j⟩ :=
            h_origin l f₀ fr₀ lbl₀ h_find_final₀
          have h_j_lt : j < idx :=
            Metamath.StoredStatementSoundness.Runtime.RunTrace.creation_before_member
              h_trace idx j h_idx h_j l
              (.assert f₀ fr₀ lbl₀) h_find_prefix h_create_j
          obtain ⟨target₀, h_target_final₀, _h_lookup_final₀, h_old⟩ :=
            ih j h_j_lt h_j l f₀ fr₀ lbl₀ h_find_final₀ h_create_j
          have h_target_from_prefix : Kernel.toFrame db fr₀ = some specFr :=
            toFrame_stable_of_find_mono (steps[idx]!).state.db db fr₀ specFr
              h_mono h_toFrame_prefix
          have h_target_eq : target₀ = specFr := by
            rw [h_target_final₀] at h_target_from_prefix
            exact Option.some.inj h_target_from_prefix
          have h_stmt_eq :
              a = StoredStatement.statementOfFrame target₀ (Kernel.toExpr f₀) := by
            rw [h_target_eq, h_toExpr]
            cases a with
            | mk actx afmla =>
                dsimp only at h_ctx h_afmla ⊢
                unfold StoredStatement.statementOfFrame
                rw [h_ctx, h_afmla]
          rw [h_stmt_eq]
          rcases h_old with h_ax | h_th
          · exact StoredStatement.sourceAxiom_self_provable h_ax
          · exact h_th
        have h_stored_eq : storedTarget = target := by
          have h_target_final' : Kernel.toFrame db pr.frame = some target := by
            simpa [h_frame] using h_target_final
          rw [h_stored_target] at h_target_final'
          exact Option.some.inj h_target_final'
        refine ⟨target, h_target_final, h_lookup_final, Or.inr ?_⟩
        simpa [h_stored_eq, h_fmla] using h_source_exact
  refine ⟨Γ, steps, q, h_final_db, h_trace, h_pointwise, ?_⟩
  intro n f fr lbl h_find_final
  obtain ⟨idx, ⟨h_idx, h_creates⟩, _h_unique⟩ :=
    h_origin n f fr lbl h_find_final
  obtain ⟨target, h_target, h_lookup, h_result⟩ :=
    h_created idx h_idx n f fr lbl h_find_final h_creates
  refine ⟨idx, target, h_idx, h_creates, h_target, h_lookup, ?_⟩
  rcases h_payload idx n f fr lbl h_idx h_creates with h_axiom | h_theorem
  · obtain ⟨arr, p, h_event, h_label, h_fmla, h_lbl, _h_head,
      _h_fresh, _h_insert, _h_trim⟩ := h_axiom
    apply Or.inl
    refine ⟨arr, p, h_event, h_label, h_fmla, h_lbl, ?_⟩
    change AxiomEventOfTrace steps Γ
      (StoredStatement.statementOfFrame target (Kernel.toExpr f))
    exact ⟨idx, n, f, fr, lbl, target, arr, p, h_idx, h_creates,
      h_event, h_label, h_fmla, h_lbl, h_lookup, rfl⟩
  · obtain ⟨pr, _prefixΓ, _source, h_event, h_label, h_fmla, h_frame,
      h_lbl, _h_fresh, _h_insert, _h_prefix_db, _h_source,
      _h_prefix_provable⟩ := h_theorem
    apply Or.inr
    refine ⟨pr, h_event, h_label, h_fmla, h_frame, h_lbl, ?_⟩
    rcases h_result with h_ax | h_th
    · exact StoredStatement.sourceAxiom_self_provable h_ax
    · exact h_th

end Runtime
end Metamath.StoredStatementSoundness
