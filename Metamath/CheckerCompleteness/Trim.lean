import Metamath.StoredStatementSoundness
import Metamath.ParserInvariantPreservation

/-!
# Frame trimming ignores dummy declarations

`DB.trimFrame` keeps the essential hypotheses of the active frame, the floating hypotheses of the
mandatory variables (those of the claim and of the essential hypotheses), and the `$d` pairs of
mandatory variables. Floating hypotheses and `$d` pairs appended for variables that are not
mandatory leave the trimmed frame unchanged (`trimFrame_eq_of_dummy_floats`), so declaring dummy
variables before a `$p` statement does not change the statement it stores.

The mandatory variables are exactly those of the claim and of the active essential hypotheses
(`trimVars_contains_iff`), and each has an active floating hypothesis when trimming succeeds
(`trimVars_subset_frameFloatVars`).
-/

set_option autoImplicit false

namespace Metamath.CheckerCompleteness

open Metamath.Verify
open Metamath.StoredStatementSoundness.Runtime (trimVars)
open Metamath.ParserOps (collectVarsFromHypsList collectFloatVarsFromHypsList)
open Std (HashSet)

/-! ## Normal form of `DB.trimFrame` -/

/-- The `$f`-coverage loop of `DB.trimFrame`, exactly as the `do` block runs it. -/
def trimVarsWithF (db : DB) (vars : HashSet String) : HashSet String :=
  Id.run
    (forIn db.frame.hyps (∅ : HashSet String) (fun l r =>
      match db.find? l with
      | some (.hyp false f _) =>
          let v := f[1]!.value
          if vars.contains v then
            pure (ForInStep.yield (r.insert v))
          else
            pure (ForInStep.yield r)
      | _ => pure (ForInStep.yield r)))

/-- The final coverage check of `DB.trimFrame`. -/
def trimOk (vars varsWithF : HashSet String) : Bool :=
  Id.run
    (forIn vars true (fun v ok =>
      if varsWithF.contains v then
        pure (ForInStep.yield ok)
      else
        pure (ForInStep.yield false)))

theorem trimFrame_fst_eq (db : DB) (fmla : Verify.Formula) :
    (db.trimFrame fmla).1 =
      trimOk (trimVars db fmla) (trimVarsWithF db (trimVars db fmla)) := by
  rfl

/-- A yield-only `Id` loop whose body agrees pointwise with a step function is
that step function's left fold. -/
theorem idRun_forIn_eq_foldl_of_body {α β : Type} (arr : Array α) (init : β)
    (body : α → β → Id (ForInStep β)) (step : β → α → β)
    (h : ∀ a b, body a b = pure (ForInStep.yield (step b a))) :
    Id.run (forIn arr init body) = arr.toList.foldl step init := by
  have h_eq : body = fun a b => pure (ForInStep.yield (step b a)) :=
    funext fun a => funext fun b => h a b
  subst h_eq
  exact _root_.List.ArrayListExt.Array.idRun_forIn_yield_eq_foldl arr init step

theorem trimVars_eq_collect (db : DB) (fmla : Verify.Formula) :
    trimVars db fmla =
      collectVarsFromHypsList db db.frame.hyps.toList
        (fmla.foldlVars ∅ HashSet.insert) := by
  unfold trimVars collectVarsFromHypsList
  dsimp only
  refine idRun_forIn_eq_foldl_of_body _ _ _ _ ?_
  intro l r
  rcases db.find? l with _ | ⟨_ | _ | ⟨_ | _, f, nm⟩ | _⟩ <;> rfl

theorem trimVarsWithF_eq_collect (db : DB) (vars : HashSet String) :
    trimVarsWithF db vars =
      collectFloatVarsFromHypsList db vars db.frame.hyps.toList := by
  unfold trimVarsWithF collectFloatVarsFromHypsList
  refine idRun_forIn_eq_foldl_of_body _ _ _ _ ?_
  intro l r
  rcases db.find? l with _ | ⟨_ | _ | ⟨_ | _, f, nm⟩ | _⟩
  all_goals try rfl
  dsimp only
  split <;> rfl

theorem trimOk_eq_foldl (vars varsWithF : HashSet String) :
    trimOk vars varsWithF =
      vars.toList.foldl (fun b v => b && varsWithF.contains v) true := by
  have h_body :
      (fun v ok =>
        if varsWithF.contains v then
          (pure (ForInStep.yield ok) : Id (ForInStep Bool))
        else
          (pure (ForInStep.yield false) : Id (ForInStep Bool))) =
      (fun v ok =>
        (pure (ForInStep.yield (ok && varsWithF.contains v)) : Id (ForInStep Bool))) := by
    funext v ok
    cases varsWithF.contains v <;> cases ok <;> rfl
  unfold trimOk
  rw [h_body, Std.HashSet.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl]
  rfl

/-! ## Folds that ignore appended labels -/

theorem foldl_congr_of_mem {α β : Type} (f g : β → α → β) (l : List α) (init : β)
    (h : ∀ x ∈ l, ∀ acc, f acc x = g acc x) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      exact ih _ (fun y hy acc => h y (by simp [hy]) acc)

theorem foldl_eq_init_of_mem {α β : Type} (f : β → α → β) (l : List α) (init : β)
    (h : ∀ x ∈ l, ∀ acc, f acc x = acc) :
    l.foldl f init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      exact ih _ (fun y hy acc => h y (by simp [hy]) acc)

/-- Appending labels that resolve to `$f` hypotheses leaves the essential-variable
collection unchanged, provided the old labels resolve as before. -/
theorem collectVarsFromHypsList_append_floats (db db' : DB) (L E : List String)
    (vars : HashSet String)
    (h_old : ∀ l ∈ L, db'.find? l = db.find? l)
    (h_extra : ∀ l ∈ E, ∃ f nm, db'.find? l = some (.hyp false f nm)) :
    collectVarsFromHypsList db' (L ++ E) vars = collectVarsFromHypsList db L vars := by
  unfold collectVarsFromHypsList
  rw [List.foldl_append]
  rw [foldl_eq_init_of_mem _ E]
  · apply foldl_congr_of_mem
    intro l hl acc
    simp only [h_old l hl]
  · intro l hl acc
    obtain ⟨f, nm, h_find⟩ := h_extra l hl
    simp only [h_find]

/-- Appending `$f` hypotheses whose variable is outside `vars` leaves the
`$f`-coverage set unchanged. -/
theorem collectFloatVarsFromHypsList_append_floats (db db' : DB)
    (vars : HashSet String) (L E : List String)
    (h_old : ∀ l ∈ L, db'.find? l = db.find? l)
    (h_extra : ∀ l ∈ E, ∃ f nm, db'.find? l = some (.hyp false f nm) ∧
      vars.contains f[1]!.value = false) :
    collectFloatVarsFromHypsList db' vars (L ++ E) =
      collectFloatVarsFromHypsList db vars L := by
  unfold collectFloatVarsFromHypsList
  rw [List.foldl_append]
  rw [foldl_eq_init_of_mem _ E]
  · apply foldl_congr_of_mem
    intro l hl acc
    simp only [h_old l hl]
  · intro l hl acc
    obtain ⟨f, nm, h_find, h_not⟩ := h_extra l hl
    simp only [h_find, h_not]
    rfl

/-- Appending labels that `trimFrameKeep` drops does not change the trimmed
hypothesis array. -/
theorem trimFrameHyps_append_dropped (db db' : DB) (vars : HashSet String)
    (hyps extra : Array String)
    (h_old : ∀ l ∈ hyps.toList, db'.find? l = db.find? l)
    (h_extra : ∀ l ∈ extra.toList, DB.trimFrameKeep db' vars l = false) :
    DB.trimFrameHyps db' vars (hyps ++ extra) = DB.trimFrameHyps db vars hyps := by
  have h_list :
      DB.trimFrameHypsPairsList db' vars 0 (hyps ++ extra).toList =
        DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
    unfold DB.trimFrameHypsPairsList
    rw [Array.toList_append, List.zipIdx_append, List.filter_append]
    have h_tail :
        List.filter (fun p => DB.trimFrameKeep db' vars p.1)
          (extra.toList.zipIdx (0 + hyps.toList.length)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      simp [h_extra p.1 (List.fst_mem_of_mem_zipIdx hp)]
    have h_head :
        List.filter (fun p => DB.trimFrameKeep db' vars p.1) (hyps.toList.zipIdx 0) =
          List.filter (fun p => DB.trimFrameKeep db vars p.1) (hyps.toList.zipIdx 0) := by
      apply List.filter_congr
      intro p hp
      unfold DB.trimFrameKeep
      rw [h_old p.1 (List.fst_mem_of_mem_zipIdx hp)]
    rw [h_tail, h_head, List.append_nil]
  unfold DB.trimFrameHyps DB.trimFrameHypsPairs
  rw [h_list]

/-! ## Main invariance theorem -/

theorem frame_ext_of {a b : Verify.Frame} (h1 : a.dj = b.dj) (h2 : a.hyps = b.hyps) : a = b := by
  obtain ⟨dj1, hyps1⟩ := a
  obtain ⟨dj2, hyps2⟩ := b
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- The mandatory-variable set is unchanged by appending `$f` hypotheses. -/
theorem trimVars_append_floats (db db' : DB) (fmla : Verify.Formula)
    (extra : Array String)
    (h_hyps : db'.frame.hyps = db.frame.hyps ++ extra)
    (h_old : ∀ l ∈ db.frame.hyps, db'.find? l = db.find? l)
    (h_extra : ∀ l ∈ extra, ∃ f nm, db'.find? l = some (.hyp false f nm)) :
    trimVars db' fmla = trimVars db fmla := by
  rw [trimVars_eq_collect, trimVars_eq_collect, h_hyps, Array.toList_append]
  exact collectVarsFromHypsList_append_floats db db' _ _ _
    (fun l hl => h_old l (Array.mem_toList_iff.mp hl))
    (fun l hl => h_extra l (Array.mem_toList_iff.mp hl))

/-- Declaring `$f` hypotheses for variables that are not mandatory for `fmla`,
together with `$d` pairs each touching such a variable, leaves the trimmed frame
of `fmla` and its success flag unchanged. -/
theorem trimFrame_eq_of_dummy_extension (db db' : DB) (fmla : Verify.Formula)
    (extra : Array String) (extraDJ : Array Verify.DJ)
    (h_hyps : db'.frame.hyps = db.frame.hyps ++ extra)
    (h_dj : db'.frame.dj = db.frame.dj ++ extraDJ)
    (h_old : ∀ l ∈ db.frame.hyps, db'.find? l = db.find? l)
    (h_extra : ∀ l ∈ extra, ∃ f nm, db'.find? l = some (.hyp false f nm) ∧
      (trimVars db fmla).contains f[1]!.value = false)
    (h_extraDJ : ∀ p ∈ extraDJ, (trimVars db fmla).contains p.1 = false ∨
      (trimVars db fmla).contains p.2 = false) :
    db'.trimFrame fmla = db.trimFrame fmla := by
  have h_vars : trimVars db' fmla = trimVars db fmla :=
    trimVars_append_floats db db' fmla extra h_hyps h_old
      (fun l hl => by
        obtain ⟨f, nm, h_find, _⟩ := h_extra l hl
        exact ⟨f, nm, h_find⟩)
  have h_fst : (db'.trimFrame fmla).1 = (db.trimFrame fmla).1 := by
    rw [trimFrame_fst_eq, trimFrame_fst_eq, h_vars, trimVarsWithF_eq_collect,
      trimVarsWithF_eq_collect, h_hyps, Array.toList_append,
      collectFloatVarsFromHypsList_append_floats db db' _ _ _
        (fun l hl => h_old l (Array.mem_toList_iff.mp hl))
        (fun l hl => h_extra l (Array.mem_toList_iff.mp hl))]
  have h_dj' : (db'.trimFrame fmla).2.dj = (db.trimFrame fmla).2.dj := by
    apply Array.ext'
    rw [StoredStatementSoundness.Runtime.trimFrame_dj_toList_eq_filter,
      StoredStatementSoundness.Runtime.trimFrame_dj_toList_eq_filter, h_vars, h_dj,
      Array.toList_append, List.filter_append]
    have h_nil :
        List.filter
          (fun p => (trimVars db fmla).contains p.1 && (trimVars db fmla).contains p.2)
          extraDJ.toList = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      rcases h_extraDJ p (Array.mem_toList_iff.mp hp) with h | h <;> simp [h]
    rw [h_nil, List.append_nil]
  have h_hyps' : (db'.trimFrame fmla).2.hyps = (db.trimFrame fmla).2.hyps := by
    rw [StoredStatementSoundness.Runtime.trimFrame_hyps_eq,
      StoredStatementSoundness.Runtime.trimFrame_hyps_eq, h_vars, h_hyps]
    apply trimFrameHyps_append_dropped
    · exact fun l hl => h_old l (Array.mem_toList_iff.mp hl)
    · intro l hl
      obtain ⟨f, nm, h_find, h_not⟩ := h_extra l (Array.mem_toList_iff.mp hl)
      unfold DB.trimFrameKeep
      simp only [h_find, h_not]
  exact Prod.ext h_fst (frame_ext_of h_dj' h_hyps')

/-! ## Coverage: every mandatory variable has an active `$f` -/

theorem trimOk_eq_true_iff (vars varsWithF : HashSet String) :
    trimOk vars varsWithF = true ↔
      ∀ v, vars.contains v = true → varsWithF.contains v = true := by
  rw [trimOk_eq_foldl, List.foldl_and_eq_true]
  constructor
  · intro h v hv
    exact h v (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hv))
  · intro h v hv
    exact h v (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hv))

/-- A successful trim covers every mandatory variable by a `$f` of the active
frame. -/
theorem trimVars_subset_frameFloatVars (db : DB) (fmla : Verify.Formula)
    (fr : Verify.Frame) (h_wf : WF.WellFormedDB db)
    (h_trim : db.trimFrame' fmla = .ok fr) {v : String}
    (h_v : (trimVars db fmla).contains v = true) :
    v ∈ db.frameFloatVars db.frame := by
  have h_ok : (db.trimFrame fmla).1 = true :=
    congrArg Prod.fst (ParserOps.trimFrame'_ok_iff.mp h_trim)
  rw [trimFrame_fst_eq, trimOk_eq_true_iff] at h_ok
  have h_cov := h_ok v h_v
  rw [trimVarsWithF_eq_collect] at h_cov
  exact ParserOps.collectFloatVarsFromHypsList_contains_implies_frameFloatVars
    db _ v h_wf h_cov

/-! ## The mandatory-variable set, exactly -/

theorem foldlVars_eq_tail_foldl (f : Verify.Formula) (vars : HashSet String) :
    f.foldlVars vars HashSet.insert =
      f.toList.tail.foldl
        (fun a s => match s with
          | Verify.Sym.var v => HashSet.insert a v
          | _ => a) vars := by
  unfold Verify.Formula.foldlVars
  have h :=
    _root_.List.ArrayListExt.Array.foldl_eq_list_foldl_drop (arr := f) (init := vars)
      (start := 1)
      (f := fun a s => match s with
        | Verify.Sym.var v => HashSet.insert a v
        | _ => a)
  simp only [List.drop_one] at h
  exact h

theorem foldlVars_contains_imp (f : Verify.Formula) (vars : HashSet String) (v : String)
    (h : (f.foldlVars vars HashSet.insert).contains v = true) :
    vars.contains v = true ∨ Verify.Sym.var v ∈ f.toList.tail := by
  rw [foldlVars_eq_tail_foldl] at h
  generalize f.toList.tail = ls at h ⊢
  induction ls generalizing vars with
  | nil => exact Or.inl h
  | cons s ss ih =>
      cases s with
      | const c =>
          rcases ih vars h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons_of_mem _ h')
      | var w =>
          rcases ih (vars.insert w) h with h' | h'
          · rw [Std.HashSet.contains_insert] at h'
            rcases Bool.or_eq_true_iff.mp h' with h'' | h''
            · have h_eq : w = v := by simpa using h''
              subst h_eq
              exact Or.inr (by simp)
            · exact Or.inl h''
          · exact Or.inr (List.mem_cons_of_mem _ h')

theorem collectVarsFromHypsList_contains_imp (db : DB) (ls : List String)
    (vars : HashSet String) (v : String)
    (h : (collectVarsFromHypsList db ls vars).contains v = true) :
    vars.contains v = true ∨
      ∃ l ∈ ls, ∃ f nm, db.find? l = some (.hyp true f nm) ∧
        Verify.Sym.var v ∈ f.toList.tail := by
  induction ls generalizing vars with
  | nil => exact Or.inl h
  | cons l ls ih =>
      have lift :
          (∃ l' ∈ ls, ∃ f nm, db.find? l' = some (.hyp true f nm) ∧
            Verify.Sym.var v ∈ f.toList.tail) →
          ∃ l' ∈ l :: ls, ∃ f nm, db.find? l' = some (.hyp true f nm) ∧
            Verify.Sym.var v ∈ f.toList.tail := by
        rintro ⟨l', hl', f, nm, h_find, h_mem⟩
        exact ⟨l', List.mem_cons_of_mem _ hl', f, nm, h_find, h_mem⟩
      rcases h_find : db.find? l with _ | ⟨_ | _ | ⟨_ | _, f, nm⟩ | _⟩
      all_goals
        simp only [collectVarsFromHypsList, List.foldl_cons, h_find] at h
      case some.hyp.true =>
        rcases ih (f.foldlVars vars HashSet.insert) h with h' | h'
        · rcases foldlVars_contains_imp f vars v h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr ⟨l, by simp, f, nm, h_find, h''⟩
        · exact Or.inr (lift h')
      all_goals
        rcases ih vars h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (lift h')

/-- `trimFrame` retains exactly the variables of the statement and of the
active essential hypotheses. -/
theorem trimVars_contains_iff (db : DB) (fmla : Verify.Formula) (v : String) :
    (trimVars db fmla).contains v = true ↔
      Verify.Sym.var v ∈ fmla.toList.tail ∨
        ∃ l ∈ db.frame.hyps.toList, ∃ f nm,
          db.find? l = some (.hyp true f nm) ∧ Verify.Sym.var v ∈ f.toList.tail := by
  rw [trimVars_eq_collect]
  constructor
  · intro h
    rcases collectVarsFromHypsList_contains_imp db _ _ v h with h0 | h1
    · rcases foldlVars_contains_imp fmla ∅ v h0 with h00 | h01
      · simp at h00
      · exact Or.inl h01
    · exact Or.inr h1
  · rintro (h0 | ⟨l, hl, f, nm, h_find, h_mem⟩)
    · exact ParserOps.collectVarsFromHypsList_preserves_contains db _ _ v
        (ParserOps.foldlVars_contains_of_mem fmla ∅ v h0)
    · exact ParserOps.collectVarsFromHypsList_contains_of_mem db _ _ l f nm hl h_find
        v h_mem

/-- `d` is not a mandatory variable of `fmla` in `db`: it occurs neither in the
statement nor in any active essential hypothesis. -/
def NotMandatory (db : DB) (fmla : Verify.Formula) (d : String) : Prop :=
  Verify.Sym.var d ∉ fmla.toList.tail ∧
    ∀ l ∈ db.frame.hyps.toList, ∀ f nm, db.find? l = some (.hyp true f nm) →
      Verify.Sym.var d ∉ f.toList.tail

theorem notMandatory_iff (db : DB) (fmla : Verify.Formula) (d : String) :
    NotMandatory db fmla d ↔ (trimVars db fmla).contains d = false := by
  constructor
  · rintro ⟨h_fmla, h_ess⟩
    cases h : (trimVars db fmla).contains d with
    | false => rfl
    | true =>
        rcases (trimVars_contains_iff db fmla d).mp h with h0 |
            ⟨l, hl, f, nm, h_find, h_mem⟩
        · exact absurd h0 h_fmla
        · exact absurd h_mem (h_ess l hl f nm h_find)
  · intro h
    refine ⟨fun h0 => ?_, fun l hl f nm h_find h_mem => ?_⟩
    · have := (trimVars_contains_iff db fmla d).mpr (Or.inl h0)
      rw [h] at this
      exact Bool.false_ne_true this
    · have := (trimVars_contains_iff db fmla d).mpr (Or.inr ⟨l, hl, f, nm, h_find, h_mem⟩)
      rw [h] at this
      exact Bool.false_ne_true this

/-! ## Trimming after adding dummy floats -/

/-- Old frame labels resolve as before once every one of them is found in `db`
and `find?` only grows. -/
theorem find?_frame_hyps_eq_of_mono (db db' : DB) (h_wf : WF.WellFormedDB db)
    (h_mono : ∀ l o, db.find? l = some o → db'.find? l = some o) :
    ∀ l ∈ db.frame.hyps, db'.find? l = db.find? l := by
  intro l hl
  obtain ⟨i, hi, h_at⟩ := Array.mem_iff_getElem.mp hl
  obtain ⟨ess, f, nm, h_find, _, _⟩ := h_wf.1.1 i hi
  rw [h_at] at h_find
  rw [h_find]
  exact h_mono l _ h_find

/-- Declaring dummy variables (fresh `$f C d` hypotheses for non-mandatory `d`,
and `$d` pairs each touching a non-mandatory variable) does not change the
trimmed frame of `fmla`. -/
theorem trimFrame_eq_of_dummy_floats (db db' : DB) (fmla : Verify.Formula)
    (extra : Array String) (extraDJ : Array Verify.DJ)
    (h_wf : WF.WellFormedDB db)
    (h_hyps : db'.frame.hyps = db.frame.hyps ++ extra)
    (h_dj : db'.frame.dj = db.frame.dj ++ extraDJ)
    (h_mono : ∀ l o, db.find? l = some o → db'.find? l = some o)
    (h_extra : ∀ l ∈ extra, ∃ c d,
      db'.find? l = some (.hyp false #[.const c, .var d] l) ∧ NotMandatory db fmla d)
    (h_extraDJ : ∀ v w, (v, w) ∈ extraDJ →
      NotMandatory db fmla v ∨ NotMandatory db fmla w) :
    db'.trimFrame fmla = db.trimFrame fmla := by
  apply trimFrame_eq_of_dummy_extension db db' fmla extra extraDJ h_hyps h_dj
    (find?_frame_hyps_eq_of_mono db db' h_wf h_mono)
  · intro l hl
    obtain ⟨c, d, h_find, h_d⟩ := h_extra l hl
    exact ⟨_, l, h_find, (notMandatory_iff db fmla d).mp h_d⟩
  · intro p hp
    rcases h_extraDJ p.1 p.2 hp with h | h
    · exact Or.inl ((notMandatory_iff db fmla _).mp h)
    · exact Or.inr ((notMandatory_iff db fmla _).mp h)

theorem trimFrame'_ok_of_dummy_floats (db db' : DB) (fmla : Verify.Formula)
    (fr : Verify.Frame) (extra : Array String) (extraDJ : Array Verify.DJ)
    (h_wf : WF.WellFormedDB db)
    (h_hyps : db'.frame.hyps = db.frame.hyps ++ extra)
    (h_dj : db'.frame.dj = db.frame.dj ++ extraDJ)
    (h_mono : ∀ l o, db.find? l = some o → db'.find? l = some o)
    (h_extra : ∀ l ∈ extra, ∃ c d,
      db'.find? l = some (.hyp false #[.const c, .var d] l) ∧ NotMandatory db fmla d)
    (h_extraDJ : ∀ v w, (v, w) ∈ extraDJ →
      NotMandatory db fmla v ∨ NotMandatory db fmla w)
    (h_trim : db.trimFrame' fmla = .ok fr) :
    db'.trimFrame' fmla = .ok fr := by
  unfold DB.trimFrame' at h_trim ⊢
  rw [trimFrame_eq_of_dummy_floats db db' fmla extra extraDJ h_wf h_hyps h_dj h_mono
    h_extra h_extraDJ]
  exact h_trim

/-! ## Examples

Kernel-checked instances: one where a genuine dummy extension leaves the trimmed
frame fixed, and two showing that each non-mandatory condition is needed. -/

namespace Examples

/-- The statement `|- x`. -/
def fX : Verify.Formula := #[.const "|-", .var "x"]
/-- The statement `|- x z`. -/
def fXZ : Verify.Formula := #[.const "|-", .var "x", .var "z"]
/-- `wx $f wff x $.` -/
def objX : Object := .hyp false #[.const "wff", .var "x"] "wx"
/-- `wy $f wff y $.` -/
def objY : Object := .hyp false #[.const "wff", .var "y"] "wy"

/-- Active frame: `wx $f wff x $.` only. -/
def db0 : DB :=
  { (default : DB) with
    frame := ⟨#[], #["wx"]⟩
    objects := (∅ : Std.HashMap String Object).insert "wx" objX }

/-- `db0` after declaring the dummy `wy $f wff y $.` and `$d x y $.`. -/
def db1 : DB :=
  { db0 with
    frame := ⟨#[("x", "y")], #["wx", "wy"]⟩
    objects := db0.objects.insert "wy" objY }

theorem db0_find_wx : db0.find? "wx" = some objX := by
  show ((∅ : Std.HashMap String Object).insert "wx" objX)["wx"]? = some objX
  exact Std.HashMap.getElem?_insert_self

theorem db1_find_wy : db1.find? "wy" = some objY := by
  show (db0.objects.insert "wy" objY)["wy"]? = some objY
  exact Std.HashMap.getElem?_insert_self

theorem db1_find_wx : db1.find? "wx" = db0.find? "wx" := by
  show (db0.objects.insert "wy" objY)["wx"]? = db0.objects["wx"]?
  rw [Std.HashMap.getElem?_insert]
  simp

theorem y_notMandatory : NotMandatory db0 fX "y" := by
  refine ⟨by decide, ?_⟩
  intro l hl f nm h_find
  have h_l : l = "wx" := by simpa [db0] using hl
  subst h_l
  rw [db0_find_wx] at h_find
  cases h_find

/-- Positive: the dummy extension of `db0` trims to the same frame. -/
theorem db1_trimFrame_eq : db1.trimFrame fX = db0.trimFrame fX := by
  apply trimFrame_eq_of_dummy_extension db0 db1 fX #["wy"] #[("x", "y")] rfl rfl
  · intro l hl
    have h_l : l = "wx" := by simpa [db0] using hl
    subst h_l
    exact db1_find_wx
  · intro l hl
    have h_l : l = "wy" := by simpa using hl
    subst h_l
    exact ⟨#[.const "wff", .var "y"], "wy", db1_find_wy,
      (notMandatory_iff db0 fX "y").mp y_notMandatory⟩
  · intro p hp
    have h' : p ∈ [(("x", "y") : Verify.DJ)] := Array.mem_def.mp hp
    rcases List.mem_singleton.mp h' with rfl
    exact Or.inr ((notMandatory_iff db0 fX "y").mp y_notMandatory)

/-- The trimmed frame of `db0` keeps `wx` (so the example is not degenerate)
and, by `db1_trimFrame_eq`, `db1`'s drops the dummy `wy`. -/
theorem db1_trimFrame_keeps_wx_drops_wy :
    "wx" ∈ (db1.trimFrame fX).2.hyps.toList ∧
      "wy" ∉ (db1.trimFrame fX).2.hyps.toList := by
  rw [db1_trimFrame_eq, StoredStatementSoundness.Runtime.trimFrame_hyps_eq,
    StoredStatementSoundness.Runtime.trimFrameHyps_mem_iff,
    StoredStatementSoundness.Runtime.trimFrameHyps_mem_iff]
  constructor
  · refine ⟨0, by decide, rfl, ?_⟩
    show DB.trimFrameKeep db0 (trimVars db0 fX) "wx" = true
    unfold DB.trimFrameKeep
    rw [db0_find_wx]
    exact (trimVars_contains_iff db0 fX "x").mpr (Or.inl (by decide))
  · rintro ⟨i, hi, h_at, _⟩
    have h_i : i = 0 := by
      have : i < 1 := hi
      omega
    subst h_i
    have h_wx : db0.frame.hyps[0]'hi = "wx" := rfl
    rw [h_wx] at h_at
    exact absurd h_at (by decide)

/-- Empty active frame. -/
def dbE : DB := default

/-- `dbE` after declaring `wx $f wff x $.` for the *mandatory* `x`. -/
def dbEx : DB :=
  { dbE with
    frame := ⟨#[], #["wx"]⟩
    objects := dbE.objects.insert "wx" objX }

/-- Negative: a `$f` for a mandatory variable changes the trimmed frame. -/
theorem dbEx_trimFrame_ne : dbEx.trimFrame fX ≠ dbE.trimFrame fX := by
  intro h
  have h_mem : "wx" ∈ (dbEx.trimFrame fX).2.hyps.toList := by
    rw [StoredStatementSoundness.Runtime.trimFrame_hyps_eq,
      StoredStatementSoundness.Runtime.trimFrameHyps_mem_iff]
    refine ⟨0, by decide, rfl, ?_⟩
    show DB.trimFrameKeep dbEx (trimVars dbEx fX) "wx" = true
    have h_find : dbEx.find? "wx" = some objX := by
      show (dbE.objects.insert "wx" objX)["wx"]? = some objX
      exact Std.HashMap.getElem?_insert_self
    unfold DB.trimFrameKeep
    rw [h_find]
    exact (trimVars_contains_iff dbEx fX "x").mpr (Or.inl (by decide))
  rw [h, StoredStatementSoundness.Runtime.trimFrame_hyps_eq,
    StoredStatementSoundness.Runtime.trimFrameHyps_mem_iff] at h_mem
  obtain ⟨i, hi, _, _⟩ := h_mem
  have h_size : dbE.frame.hyps.size = 0 := rfl
  omega

/-- `dbE` after declaring `$d x z $.` between two *mandatory* variables. -/
def dbEdj : DB := { dbE with frame := ⟨#[("x", "z")], #[]⟩ }

/-- Negative: a `$d` pair of mandatory variables changes the trimmed frame. -/
theorem dbEdj_trimFrame_ne : dbEdj.trimFrame fXZ ≠ dbE.trimFrame fXZ := by
  intro h
  have h_x : (trimVars dbEdj fXZ).contains "x" = true :=
    (trimVars_contains_iff dbEdj fXZ "x").mpr (Or.inl (by decide))
  have h_z : (trimVars dbEdj fXZ).contains "z" = true :=
    (trimVars_contains_iff dbEdj fXZ "z").mpr (Or.inl (by decide))
  let q : Verify.DJ := ("x", "z")
  have h_mem : q ∈ (dbEdj.trimFrame fXZ).2.dj.toList := by
    rw [StoredStatementSoundness.Runtime.trimFrame_dj_toList_eq_filter]
    refine List.mem_filter.mpr ⟨List.mem_singleton.mpr rfl, ?_⟩
    show ((trimVars dbEdj fXZ).contains "x" && (trimVars dbEdj fXZ).contains "z") = true
    rw [h_x, h_z]
    rfl
  rw [h, StoredStatementSoundness.Runtime.trimFrame_dj_toList_eq_filter] at h_mem
  exact List.not_mem_nil (List.mem_filter.mp h_mem).1

end Examples

end Metamath.CheckerCompleteness
