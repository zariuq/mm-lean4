import Metamath.Spec.StoredStatement

/-!
# Dummy variables for a frame

A Metamath proof may use variables beyond the mandatory ones through optional `$f` and `$d`
statements: the extended frames of the Metamath book (§4.2.7), which are the pre-statements of its
Appendix C (C.4). A provable pre-statement may need such "dummy" variables, and no bound on their
number works for all statements (C.2.4). This module turns a declarative derivation of a stored
statement into a derivation from `$f`-typed variables only (`FrameDerivable`) in an active frame
extended by dummy variables.

- `extendDummies frAct ds`: the frame `frAct` with one `$f` statement per dummy in `ds`, and one
  `$d` pair between each dummy and each variable before it (the variables of `frAct` and the
  earlier dummies).
- `exists_dummies_of_statementProvable`: a declaratively provable stored statement `(fr, e)` is
  derivable in `extendDummies frAct ds`, for an active frame `frAct` containing `fr` and fresh
  dummies `ds`. There is one dummy per distinct variable outside `fr` that some derivation uses,
  typed by the conclusion's typecode or by a typecode the database's assertions use in premises.
-/

namespace Metamath.Spec.DummyExtension

open Metamath.Spec.Equivalence
open Metamath.Spec.StoredStatement
open Metamath.Spec.Bridge (DeclarativeVR DeclarativeFormula DeclarativeExpr)
/-! ## Lists and variable maps -/

theorem find?_append_of_some {α : Type _} {p : α → Bool} {l₁ l₂ : List α} {a : α}
    (h : l₁.find? p = some a) : (l₁ ++ l₂).find? p = some a := by
  induction l₁ with
  | nil => exact nomatch h
  | cons x xs ih =>
      simp only [List.cons_append, List.find?] at h ⊢
      cases hpx : p x with
      | true => rw [hpx] at h; exact h
      | false => rw [hpx] at h; exact ih h

theorem find?_append_of_none {α : Type _} {p : α → Bool} {l₁ l₂ : List α}
    (h : l₁.find? p = none) : (l₁ ++ l₂).find? p = l₂.find? p := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, List.find?] at h ⊢
      cases hpx : p x with
      | true => rw [hpx] at h; exact nomatch h
      | false => rw [hpx] at h; exact ih h

theorem find?_none_of_all {α : Type _} {p : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = false) → l.find? p = none
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.find?]
      rw [h a (List.Mem.head _)]
      exact find?_none_of_all fun b hb => h b (List.Mem.tail _ hb)

theorem findVR_append_of_some {vm tail : VarMap} {w : Variable} {vr : DeclarativeVR}
    (h : findVR vm w = some vr) : findVR (vm ++ tail) w = some vr := by
  unfold findVR at h ⊢
  cases hfind : vm.find? (fun p => p.1 = w) with
  | none => rw [hfind] at h; exact nomatch h
  | some _ => rw [hfind] at h; rw [find?_append_of_some hfind]; exact h

theorem varMapOfFrameAux_append (l₁ l₂ : List (Constant × Variable)) (n : Nat) :
    varMapOfFrameAux n (l₁ ++ l₂) =
      varMapOfFrameAux n l₁ ++ varMapOfFrameAux (n + l₁.length) l₂ := by
  induction l₁ generalizing n with
  | nil => simp [varMapOfFrameAux]
  | cons head rest ih =>
      obtain ⟨c, v⟩ := head
      have harith : n + 1 + rest.length = n + (rest.length + 1) := by omega
      simp [varMapOfFrameAux, ih, harith]

/-- Indices assigned by `varMapOfFrameAux n l` lie in `[n, n + l.length)`. -/
theorem varMapOfFrameAux_index_bound :
    ∀ {l : List (Constant × Variable)} {n : Nat} {entry : Variable × DeclarativeVR},
      entry ∈ varMapOfFrameAux n l → n ≤ entry.2.i ∧ entry.2.i < n + l.length
  | (_, _) :: _, _, _, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · simp
      · obtain ⟨h1, h2⟩ := varMapOfFrameAux_index_bound htail
        simp only [List.length_cons]
        omega

theorem findVR_aux_of_not_mem {n : Nat} {l : List (Constant × Variable)} {v : Variable}
    (h : v ∉ l.map Prod.snd) : findVR (varMapOfFrameAux n l) v = none := by
  cases hfind : findVR (varMapOfFrameAux n l) v with
  | none => rfl
  | some vr => exact absurd (varMapOfFrameAux_vars.mp ⟨vr, findVR_mem_of_some hfind⟩) h

/-! ## Variables of the statement a frame denotes -/

/-- Every variable of a hypothesis of `frameToContext fr` is declared by `fr`. -/
theorem declared_of_mem_hyp {fr : Frame} {f : DeclarativeFormula}
    (hf : f ∈ (frameToContext fr).hyps) {x : DeclarativeVR} (hx : x ∈' f.2) :
    ∃ w, findVar (varMapOfFrame fr) x = some w := by
  obtain ⟨h, hh, rfl⟩ := hyps_correspondence hf
  cases h with
  | floating c v =>
      obtain ⟨vr, hvr⟩ := findVR_of_float hh
      have hxvr : x = vr := by
        simpa [hypToDeclarativeFormula, hvr, Metamath.Expr.mem] using hx
      rw [hxvr]
      exact ⟨v, findVR_findVar_inverse_frame hvr⟩
  | essential e =>
      obtain ⟨s, _, hfind⟩ := exprToDeclarativeExpr_mem_extract hx
      exact ⟨⟨s⟩, findVR_findVar_inverse_frame hfind⟩

/-- Every variable of a converted expression is declared by the frame. -/
theorem declared_of_mem_exprToFormula {fr : Frame} {e : Expr} {x : DeclarativeVR}
    (hx : x ∈' (exprToFormula (varMapOfFrame fr) e).2) :
    ∃ w, findVar (varMapOfFrame fr) x = some w := by
  obtain ⟨s, _, hfind⟩ := exprToDeclarativeExpr_mem_extract hx
  exact ⟨⟨s⟩, findVR_findVar_inverse_frame hfind⟩

/-- The variables of the statement a frame denotes are declared by the frame. -/
theorem declared_of_mem_vars_statementOfFrame {fr : Frame} {e : Expr} {x : DeclarativeVR}
    (hx : x ∈ (statementOfFrame fr e).vars) : ∃ w, findVar (varMapOfFrame fr) x = some w := by
  obtain ⟨f, hf, hxf⟩ := List.mem_flatMap.mp hx
  rcases List.mem_cons.mp hf with rfl | hf
  · exact declared_of_mem_exprToFormula (Metamath.Expr.mem_vars_iff.mp hxf)
  · exact declared_of_mem_hyp hf (Metamath.Expr.mem_vars_iff.mp hxf)

/-- Every variable a frame declares occurs in the statement it denotes. -/
theorem mem_vars_statementOfFrame {fr : Frame} {e : Expr} {x : DeclarativeVR} {w : Variable}
    (hnodup : FloatVarNoDup fr) (h : findVar (varMapOfFrame fr) x = some w) :
    x ∈ (statementOfFrame fr e).vars := by
  have hvr := findVar_findVR_inverse_frame hnodup h
  obtain ⟨c, hfloat, _⟩ := mem_varMapOfFrame_sound_typed (findVR_mem_of_some hvr)
  refine (statementOfFrame fr e).mem_vars_of_hyp (hypToDeclarativeFormula_mem hfloat) ?_
  simp [hypToDeclarativeFormula, hvr, Metamath.Expr.mem]

/-! ## Reindexing into a larger frame -/

theorem vars_subset_of_hyps_subset {source target : Frame}
    (h : ∀ hyp ∈ source.hyps, hyp ∈ target.hyps) {v : Variable} (hv : v ∈ source.vars) :
    v ∈ target.vars := by
  obtain ⟨c, hc⟩ := var_mem_iff_float.mp hv
  exact var_mem_iff_float.mpr ⟨c, h _ hc⟩

/-- A frame and a larger frame with unique floating hypotheses give each common variable the same
typecode. -/
theorem frameMapTypesAgree_of_extension {source target : Frame}
    (h_target_unique : FloatUnique target) (h_subset : ∀ h ∈ source.hyps, h ∈ target.hyps) :
    FrameMapTypesAgree source target := by
  intro v sourceVR targetVR h_source h_target
  obtain ⟨sourceType, h_float_source, h_source_type⟩ :=
    mem_varMapOfFrame_sound_typed (findVR_mem_of_some h_source)
  obtain ⟨targetType, h_float_target, h_target_type⟩ :=
    mem_varMapOfFrame_sound_typed (findVR_mem_of_some h_target)
  have h_type_eq : sourceType = targetType :=
    h_target_unique sourceType targetType v (h_subset _ h_float_source) h_float_target
  rw [h_source_type, h_target_type, h_type_eq]

/-- A variable of `source` is reindexed to its variable in `target`. -/
theorem findVR_reindexVR {source target : Frame} (h_nodup : FloatVarNoDup source)
    (hvars : ∀ v ∈ source.vars, v ∈ target.vars) {x : DeclarativeVR} {w : Variable}
    (hx : findVar (varMapOfFrame source) x = some w) :
    findVR (varMapOfFrame target) w = some (reindexVR source target x) := by
  have hsx := findVar_findVR_inverse_frame h_nodup hx
  obtain ⟨y, hy⟩ := (varMapDomain_ofFrame target w).mp (hvars w (findVR_in_vars hsx))
  rw [reindexVR_of_findVR hsx hy]
  exact hy

/-- Reindexing a hypothesis of `source` into a frame containing its variables. The symbols of an
essential hypothesis that `target` declares as variables must be variables of `source`. -/
theorem hypToDeclarativeFormula_subst_reindex {source target : Frame} {hyp : Hyp}
    (hmem : hyp ∈ source.hyps) (hvars : ∀ v ∈ source.vars, v ∈ target.vars)
    (hback : ∀ eh, hyp = Hyp.essential eh → ∀ s ∈ eh.syms, ∀ y,
      findVR (varMapOfFrame target) ⟨s⟩ = some y →
      ∃ x, findVR (varMapOfFrame source) ⟨s⟩ = some x) :
    (hypToDeclarativeFormula (varMapOfFrame source) hyp).subst
        (Metamath.renameSubst (reindexVR source target)) =
      hypToDeclarativeFormula (varMapOfFrame target) hyp := by
  cases hyp with
  | floating c v =>
      obtain ⟨x, hx⟩ := findVR_of_float hmem
      obtain ⟨y, hy⟩ :=
        (varMapDomain_ofFrame target v).mp (hvars v (var_mem_iff_float.mpr ⟨c, hmem⟩))
      have hxy : reindexVR source target x = y := reindexVR_of_findVR hx hy
      simp only [hypToDeclarativeFormula, hx, hy]
      change (c.c, [Metamath.Sym.var (reindexVR source target x)] ++ []) =
        (c.c, [Metamath.Sym.var y])
      rw [hxy, List.append_nil]
  | essential eh =>
      rw [hypToDeclarativeFormula_essential, hypToDeclarativeFormula_essential]
      exact exprToFormula_subst_reindex_of_syms (hback eh rfl)
        (fun s _ x hx => (varMapDomain_ofFrame target ⟨s⟩).mp (hvars _ (findVR_in_vars hx)))

/-- Reindexing a `$d` pair of `source` into a frame containing its variables and `$d` pairs. -/
theorem frameToContext_dj_reindex {source target : Frame} (h_nodup : FloatVarNoDup source)
    (hvars : ∀ v ∈ source.vars, v ∈ target.vars) (hdv : ∀ p ∈ source.dv, p ∈ target.dv)
    {a b : DeclarativeVR} (hab : (frameToContext source).dj a b) :
    (frameToContext target).dj (reindexVR source target a) (reindexVR source target b) := by
  obtain ⟨v, w, ha, hb⟩ := dvListToDeclarativeDJ_findVars hab
  have hrel : Spec.dvRel source.dv v w := dvListToDeclarativeDJ_to_dvRel hab ha hb
  apply dvRel_to_dvListToDeclarativeDJ fun _ _ _ h1 h2 => findVR_injective_frame h1 h2
  · exact ⟨hrel.1, hrel.2.imp (hdv _) (hdv _)⟩
  · exact findVR_reindexVR h_nodup hvars ha
  · exact findVR_reindexVR h_nodup hvars hb

/-! ## The extended frame -/

/-- `$d` pairs between each of `ds` and every variable before it: those of `seen` and the earlier
members of `ds`. There is one pair per unordered pair. -/
def dummyDV : List Variable → List Variable → List (Variable × Variable)
  | _, [] => []
  | seen, d :: ds => seen.map (fun w => (d, w)) ++ dummyDV (seen ++ [d]) ds

theorem mem_dummyDV : ∀ {seen ds : List Variable} {x y : Variable},
    (x, y) ∈ dummyDV seen ds → x ∈ ds ∧ y ∈ seen ++ ds
  | _, [], _, _, h => nomatch h
  | seen, d :: ds, x, y, h => by
      rcases List.mem_append.mp h with h | h
      · obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨List.Mem.head _, List.mem_append_left _ hw⟩
      · obtain ⟨hx, hy⟩ := mem_dummyDV h
        refine ⟨List.Mem.tail _ hx, ?_⟩
        simpa using hy

theorem ne_of_mem_dummyDV : ∀ {seen ds : List Variable}, (seen ++ ds).Nodup →
    ∀ {x y : Variable}, (x, y) ∈ dummyDV seen ds → x ≠ y
  | _, [], _, _, _, h => nomatch h
  | seen, d :: ds, hnd, x, y, h => by
      rcases List.mem_append.mp h with h | h
      · obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        intro hxw
        subst hxw
        exact (List.nodup_append.mp hnd).2.2 _ hw _ (List.Mem.head _) rfl
      · refine ne_of_mem_dummyDV ?_ h
        simpa using hnd

/-- Every pair of distinct variables with one of them in `ds` has its `$d` pair, in one of the two
orders. -/
theorem dummyDV_complete : ∀ {seen ds : List Variable} {d w : Variable},
    d ∈ ds → w ∈ seen ++ ds → w ≠ d →
      (d, w) ∈ dummyDV seen ds ∨ (w, d) ∈ dummyDV seen ds
  | _, [], _, _, hd, _, _ => nomatch hd
  | seen, d' :: ds, d, w, hd, hw, hne => by
      simp only [dummyDV, List.mem_append]
      rcases List.mem_cons.mp hd with rfl | hd
      · rcases List.mem_append.mp hw with hw | hw
        · exact Or.inl (Or.inl (List.mem_map.mpr ⟨w, hw, rfl⟩))
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact absurd rfl hne
          · rcases dummyDV_complete (seen := seen ++ [d]) hw
              (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
              (Ne.symm hne) with h | h
            · exact Or.inr (Or.inr h)
            · exact Or.inl (Or.inr h)
      · have hw' : w ∈ (seen ++ [d']) ++ ds := by
          rcases List.mem_append.mp hw with hw | hw
          · exact List.mem_append_left _ (List.mem_append_left _ hw)
          · rcases List.mem_cons.mp hw with rfl | hw
            · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
            · exact List.mem_append_right _ hw
        rcases dummyDV_complete hd hw' hne with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

/-- The frame `fr` extended by optional `$f` hypotheses for the dummy variables `ds` (with their
typecodes) and by one `$d` pair between each dummy and each variable before it. -/
def extendDummies (fr : Frame) (ds : List (Constant × Variable)) : Frame where
  hyps := fr.hyps ++ ds.map fun p => Hyp.floating p.1 p.2
  dv := fr.dv ++ dummyDV fr.vars (ds.map Prod.snd)

/-- Dummy variables fresh for a frame: pairwise distinct, not variables of the
frame, and not symbols of its essential hypotheses. -/
structure DummyFresh (fr : Frame) (ds : List (Constant × Variable)) : Prop where
  nodup : (ds.map Prod.snd).Nodup
  not_var : ∀ p ∈ ds, p.2 ∉ fr.vars
  not_essential : ∀ p ∈ ds, ∀ eh, Hyp.essential eh ∈ fr.hyps → p.2.v ∉ eh.syms

theorem floatList_extendDummies (fr : Frame) (ds : List (Constant × Variable)) :
    floatList (extendDummies fr ds) = floatList fr ++ ds := by
  unfold floatList extendDummies
  simp only [List.filterMap_append]
  congr 1
  induction ds with
  | nil => rfl
  | cons p rest ih => simp [ih]

theorem vars_extendDummies (fr : Frame) (ds : List (Constant × Variable)) :
    (extendDummies fr ds).vars = fr.vars ++ ds.map Prod.snd := by
  rw [← floatList_map_snd_eq_vars, floatList_extendDummies, List.map_append,
    floatList_map_snd_eq_vars]

theorem varMapOfFrame_extendDummies (fr : Frame) (ds : List (Constant × Variable)) :
    varMapOfFrame (extendDummies fr ds) =
      varMapOfFrame fr ++ varMapOfFrameAux (floatList fr).length ds := by
  unfold varMapOfFrame
  rw [floatList_extendDummies, varMapOfFrameAux_append, Nat.zero_add]

/-- The extended map agrees with the base map on base variables and on every
variable that is not a dummy. -/
theorem findVR_extendDummies {fr : Frame} {ds : List (Constant × Variable)} {v : Variable}
    (h : v ∈ fr.vars ∨ v ∉ ds.map Prod.snd) :
    findVR (varMapOfFrame (extendDummies fr ds)) v = findVR (varMapOfFrame fr) v := by
  rw [varMapOfFrame_extendDummies]
  cases hfind : findVR (varMapOfFrame fr) v with
  | some _ => exact findVR_append_of_some hfind
  | none =>
      rcases h with hmem | hnot
      · obtain ⟨vr, hvr⟩ := (varMapDomain_ofFrame fr v).mp hmem
        rw [hfind] at hvr
        exact nomatch hvr
      · have hnone : (varMapOfFrame fr).find? (fun p => p.1 = v) = none := by
          unfold findVR at hfind
          cases hf : (varMapOfFrame fr).find? (fun p => p.1 = v) with
          | none => rfl
          | some _ => rw [hf] at hfind; exact nomatch hfind
        have haux := findVR_aux_of_not_mem (n := (floatList fr).length) hnot
        unfold findVR at haux ⊢
        rw [find?_append_of_none hnone]
        exact haux

theorem eq_of_snd_eq_of_nodup {l : List (Constant × Variable)}
    (hnodup : (l.map Prod.snd).Nodup) {p q : Constant × Variable}
    (hp : p ∈ l) (hq : q ∈ l) (h : p.2 = q.2) : p = q := by
  induction l with
  | nil => exact nomatch hp
  | cons a rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      obtain ⟨hnot, hrest⟩ := hnodup
      rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
      · rfl
      · exact absurd (h ▸ List.mem_map_of_mem hq') hnot
      · exact absurd (h.symm ▸ List.mem_map_of_mem hp') hnot
      · exact ih hrest hp' hq'

theorem frameWellFormed_extendDummies {fr : Frame} {ds : List (Constant × Variable)}
    (hfr : FrameWellFormed fr) (hfresh : DummyFresh fr ds) :
    FrameWellFormed (extendDummies fr ds) := by
  constructor
  · intro c c' v hc hc'
    simp only [extendDummies, List.mem_append, List.mem_map] at hc hc'
    rcases hc with hc | ⟨p, hp, hpeq⟩ <;> rcases hc' with hc' | ⟨p', hp', hpeq'⟩
    · exact hfr.1 c c' v hc hc'
    · injection hpeq' with _ hv
      exact absurd (by rw [hv]; exact var_mem_iff_float.mpr ⟨c, hc⟩) (hfresh.not_var p' hp')
    · injection hpeq with _ hv
      exact absurd (by rw [hv]; exact var_mem_iff_float.mpr ⟨c', hc'⟩) (hfresh.not_var p hp)
    · injection hpeq with hc₀ hv
      injection hpeq' with hc₀' hv'
      have hpp : p = p' := eq_of_snd_eq_of_nodup hfresh.nodup hp hp' (hv.trans hv'.symm)
      subst hpp
      exact hc₀.symm.trans hc₀'
  · unfold FloatVarNoDup
    rw [floatList_extendDummies, List.map_append, List.nodup_append]
    refine ⟨hfr.2, hfresh.nodup, ?_⟩
    intro a ha b hb hab
    subst hab
    rw [floatList_map_snd_eq_vars] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact hfresh.not_var p hp ha

/-! ## Dummy slots -/

/-- Position of the first occurrence of `v` in a list (the length if absent). -/
def posOf : List DeclarativeVR → DeclarativeVR → Nat
  | [], _ => 0
  | a :: l, v => if a = v then 0 else posOf l v + 1

theorem posOf_inj : ∀ {l : List DeclarativeVR} {a b : DeclarativeVR},
    a ∈ l → b ∈ l → posOf l a = posOf l b → a = b
  | [], _, _, ha, _, _ => nomatch ha
  | x :: l, a, b, ha, hb, h => by
      by_cases hxa : x = a <;> by_cases hxb : x = b
      · exact hxa.symm.trans hxb
      · subst hxa
        simp [posOf, hxb] at h
      · subst hxb
        simp [posOf, hxa] at h
      · simp only [posOf, if_neg hxa, if_neg hxb, Nat.add_right_cancel_iff] at h
        exact posOf_inj ((List.mem_cons.mp ha).resolve_left (Ne.symm hxa))
          ((List.mem_cons.mp hb).resolve_left (Ne.symm hxb)) h

/-- The largest length of a string in the list. -/
def maxLength (l : List String) : Nat :=
  l.foldr (fun s acc => max s.length acc) 0

theorem length_le_maxLength : ∀ {l : List String} {s : String}, s ∈ l → s.length ≤ maxLength l
  | _ :: _, _, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (length_le_maxLength htail) (Nat.le_max_right _ _)

/-- The name of dummy slot `i`: longer than `bound`, and of a different length
for every slot. -/
def dummyName (bound i : Nat) : String :=
  String.ofList (List.replicate (bound + 1 + i) 'd')

theorem dummyName_length (bound i : Nat) : (dummyName bound i).length = bound + 1 + i := by
  simp [dummyName]

/-- One optional floating hypothesis per support slot: the slot's dummy name,
typed by the typecode of the support variable. -/
def allocate (bound : Nat) : List DeclarativeVR → Nat → List (Constant × Variable)
  | [], _ => []
  | v :: rest, i => (⟨v.type⟩, ⟨dummyName bound i⟩) :: allocate bound rest (i + 1)

theorem allocate_names (bound : Nat) : ∀ {support : List DeclarativeVR} {i : Nat}
    {p : Constant × Variable}, p ∈ allocate bound support i →
      ∃ j, i ≤ j ∧ p.2 = ⟨dummyName bound j⟩
  | _ :: _, i, _, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · exact ⟨i, Nat.le_refl _, rfl⟩
      · obtain ⟨j, hij, hp⟩ := allocate_names bound htail
        exact ⟨j, Nat.le_of_succ_le hij, hp⟩

theorem allocate_types (bound : Nat) : ∀ {support : List DeclarativeVR} {i : Nat}
    {p : Constant × Variable}, p ∈ allocate bound support i →
      ∃ v ∈ support, p.1 = ⟨v.type⟩
  | v :: _, _, _, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · exact ⟨v, List.Mem.head _, rfl⟩
      · obtain ⟨w, hw, hp⟩ := allocate_types bound htail
        exact ⟨w, List.Mem.tail _ hw, hp⟩

theorem allocate_nodup (bound : Nat) : ∀ (support : List DeclarativeVR) (i : Nat),
    ((allocate bound support i).map Prod.snd).Nodup
  | [], _ => List.nodup_nil
  | _ :: rest, i => by
      simp only [allocate, List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, allocate_nodup bound rest (i + 1)⟩
      obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hmem
      obtain ⟨j, hij, hpj⟩ := allocate_names bound hp
      have hlen := congrArg (fun x : Variable => x.v.length) (hpj.symm.trans hpeq)
      simp only [dummyName_length] at hlen
      omega

/-- Allocated names avoid every string no longer than `bound`. -/
theorem allocate_avoids {bound : Nat} {support : List DeclarativeVR} {i : Nat}
    {l : List String} (hl : ∀ s ∈ l, s.length ≤ bound) {p : Constant × Variable}
    (hp : p ∈ allocate bound support i) : p.2.v ∉ l := by
  intro hmem
  obtain ⟨j, _, hpj⟩ := allocate_names bound hp
  have hle := hl _ hmem
  rw [hpj, dummyName_length] at hle
  omega

/-- The dummy variable at the slot of `v`. -/
theorem findVar_allocate (bound : Nat) : ∀ (support : List DeclarativeVR) (v : DeclarativeVR),
    v ∈ support → ∀ (n i : Nat),
      findVar (varMapOfFrameAux n (allocate bound support i)) ⟨v.type, n + posOf support v⟩ =
        some ⟨dummyName bound (i + posOf support v)⟩
  | v₀ :: rest, v, hv, n, i => by
      by_cases hhead : v₀ = v
      · subst hhead
        simp [posOf, findVar, allocate, varMapOfFrameAux]
      · have hvtail : v ∈ rest := (List.mem_cons.mp hv).resolve_left (Ne.symm hhead)
        have ih := findVar_allocate bound rest v hvtail (n + 1) (i + 1)
        unfold findVar at ih ⊢
        simp only [posOf, if_neg hhead, allocate, varMapOfFrameAux, List.find?]
        have hne : (decide ((⟨v₀.type, n⟩ : DeclarativeVR) =
            ⟨v.type, n + (posOf rest v + 1)⟩)) = false := by
          refine decide_eq_false fun heq => ?_
          have := congrArg Metamath.VR.i heq
          simp at this
        rw [hne]
        have harith1 : n + (posOf rest v + 1) = (n + 1) + posOf rest v := by omega
        have harith2 : i + (posOf rest v + 1) = (i + 1) + posOf rest v := by omega
        rw [harith1, harith2]
        exact ih

/-- Strings of a frame that a dummy name must avoid: variable names and symbols
of essential hypotheses. -/
def frameStrings (fr : Frame) : List String :=
  fr.vars.map (·.v) ++
    fr.hyps.flatMap fun h =>
      match h with
      | .essential e => e.syms
      | .floating _ _ => []

theorem allocate_fresh {fr : Frame} {bound : Nat} {support : List DeclarativeVR}
    (hbound : ∀ s ∈ frameStrings fr, s.length ≤ bound) :
    DummyFresh fr (allocate bound support 0) := by
  refine ⟨allocate_nodup bound support 0, fun p hp hvar => ?_, fun p hp eh heh hsym => ?_⟩
  · exact allocate_avoids hbound hp
      (List.mem_append_left _ (List.mem_map.mpr ⟨p.2, hvar, rfl⟩))
  · exact allocate_avoids hbound hp
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, heh, hsym⟩))


/-- The renaming into an extended frame `ext`: a variable that `fr` declares goes to its variable
in `ext`; any other variable goes to the dummy slot after `base` at its position in `ghosts`. -/
def dummyRename (fr ext : Frame) (ghosts : List DeclarativeVR) (base : Nat) (v : DeclarativeVR) :
    DeclarativeVR :=
  if (findVar (varMapOfFrame fr) v).isSome then reindexVR fr ext v
  else ⟨v.type, base + posOf ghosts v⟩

theorem dummyRename_of_declared {fr ext : Frame} {ghosts : List DeclarativeVR} {base : Nat}
    {v : DeclarativeVR} {w : Variable} (h : findVar (varMapOfFrame fr) v = some w) :
    dummyRename fr ext ghosts base v = reindexVR fr ext v := by
  simp [dummyRename, h]

theorem dummyRename_of_undeclared {fr ext : Frame} {ghosts : List DeclarativeVR} {base : Nat}
    {v : DeclarativeVR} (h : findVar (varMapOfFrame fr) v = none) :
    dummyRename fr ext ghosts base v = ⟨v.type, base + posOf ghosts v⟩ := by
  simp [dummyRename, h]


/-! ## Dummy variables for a derivation -/

/-- **Dummy variables.** A declaratively provable stored statement `(fr, e)` is derivable, from
`$f`-typed variables only, in an active frame `frAct` containing `fr` extended by fresh dummy
variables `ds`: one for each distinct variable outside `fr` that a derivation uses. The dummies
avoid `avoid` and the symbols of `e`, and each is typed by the conclusion's typecode or by a
typecode the database's assertions use in premises. The symbols of `e` and of the essential
hypotheses of `fr` that `frAct` declares as variables must be variables of `fr`. -/
theorem exists_dummies_of_statementProvable {Γ : Database} {fr frAct : Frame} {e : Expr}
    (hfr : FrameWellFormed fr) (hact : FrameWellFormed frAct)
    (hhyps : ∀ h ∈ fr.hyps, h ∈ frAct.hyps) (hdv : ∀ p ∈ fr.dv, p ∈ frAct.dv)
    (hsyms : ∀ s ∈ e.syms, (⟨s⟩ : Variable) ∈ frAct.vars → (⟨s⟩ : Variable) ∈ fr.vars)
    (hesyms : ∀ eh, Hyp.essential eh ∈ fr.hyps → ∀ s ∈ eh.syms,
      (⟨s⟩ : Variable) ∈ frAct.vars → (⟨s⟩ : Variable) ∈ fr.vars)
    (avoid : List String)
    (h : (statementOfFrame fr e).Provable (dbToAxioms Γ)) :
    ∃ ds : List (Constant × Variable), DummyFresh frAct ds ∧ (∀ p ∈ ds, p.2.v ∉ e.syms) ∧
      (∀ p ∈ ds, p.2.v ∉ avoid) ∧
      (∀ p ∈ ds, p.1.c = e.typecode.c ∨ Metamath.PremiseTypecode (dbToAxioms Γ) p.1.c) ∧
      (∀ p ∈ ds, ∃ b i, p.2.v = dummyName b i) ∧
      FrameDerivable Γ (extendDummies frAct ds)
        (exprToFormula (varMapOfFrame (extendDummies frAct ds)) e) := by
  obtain ⟨V, hVtype, hder⟩ :=
    Metamath.Statement.exists_finite_extension (fun _ hax => dbToAxioms_trimmed hax) h
  -- The distinct variables of `V` that `fr` does not declare.
  obtain ⟨ghosts, hghosts⟩ : ∃ ghosts : List DeclarativeVR,
      ghosts = (V.filter fun v => (findVar (varMapOfFrame fr) v).isNone).eraseDups := ⟨_, rfl⟩
  have ghosts_mem : ∀ v ∈ ghosts, v ∈ V := by
    intro v hv
    rw [hghosts, List.mem_eraseDups] at hv
    exact (List.mem_filter.mp hv).1
  have hghost : ∀ v, v ∈ (statementOfFrame fr e).vars ++ V →
      findVar (varMapOfFrame fr) v = none → v ∈ ghosts := by
    intro v hv hnone
    have hvV : v ∈ V := by
      rcases List.mem_append.mp hv with hs | hV
      · obtain ⟨w, hw⟩ := declared_of_mem_vars_statementOfFrame hs
        rw [hnone] at hw
        cases hw
      · exact hV
    rw [hghosts, List.mem_eraseDups]
    exact List.mem_filter.mpr ⟨hvV, by simp [hnone]⟩
  -- Dummy names longer than every string in play.
  have hbound : ∀ s ∈ frameStrings frAct ++ (e.syms ++ avoid),
      s.length ≤ maxLength (frameStrings frAct ++ (e.syms ++ avoid)) :=
    fun s hs => length_le_maxLength hs
  generalize maxLength (frameStrings frAct ++ (e.syms ++ avoid)) = bound at hbound
  have hfresh : DummyFresh frAct (allocate bound ghosts 0) :=
    allocate_fresh fun s hs => hbound s (List.mem_append_left _ hs)
  have hconcl : ∀ p ∈ allocate bound ghosts 0, p.2.v ∉ e.syms := fun p hp hm =>
    allocate_avoids hbound hp (List.mem_append_right _ (List.mem_append_left _ hm))
  have havoid : ∀ p ∈ allocate bound ghosts 0, p.2.v ∉ avoid := fun p hp hm =>
    allocate_avoids hbound hp (List.mem_append_right _ (List.mem_append_right _ hm))
  refine ⟨allocate bound ghosts 0, hfresh, hconcl, havoid, fun p hp => ?_,
    fun p hp => (allocate_names bound hp).elim fun j hj => ⟨bound, j, by rw [hj.2]⟩, ?_⟩
  · obtain ⟨v, hv, hp1⟩ := allocate_types bound hp
    rw [hp1]
    exact hVtype v (ghosts_mem v hv)
  obtain ⟨ds, hds⟩ : ∃ ds, ds = allocate bound ghosts 0 := ⟨_, rfl⟩
  rw [← hds] at hfresh hconcl ⊢
  obtain ⟨ext, hext⟩ : ∃ ext, ext = extendDummies frAct ds := ⟨_, rfl⟩
  rw [← hext]
  -- Facts about the extended frame.
  have hwf : FrameWellFormed ext := by rw [hext]; exact frameWellFormed_extendDummies hact hfresh
  have hvars_ext : ext.vars = frAct.vars ++ ds.map Prod.snd := by rw [hext, vars_extendDummies]
  have hvm_ext : varMapOfFrame ext =
      varMapOfFrame frAct ++ varMapOfFrameAux (floatList frAct).length ds := by
    rw [hext, varMapOfFrame_extendDummies]
  have hhyps_ext : ∀ h ∈ fr.hyps, h ∈ ext.hyps := fun h hh => by
    rw [hext]
    exact List.mem_append_left _ (hhyps h hh)
  have hdv_ext : ∀ p ∈ fr.dv, p ∈ ext.dv := fun p hp => by
    rw [hext]
    exact List.mem_append_left _ (hdv p hp)
  have hdummydv : ∀ p ∈ dummyDV frAct.vars (ds.map Prod.snd), p ∈ ext.dv := fun p hp => by
    rw [hext]
    exact List.mem_append_right _ hp
  have hvars_fr_ext : ∀ v ∈ fr.vars, v ∈ ext.vars := fun v hv => by
    rw [hvars_ext]
    exact List.mem_append_left _ (vars_subset_of_hyps_subset hhyps hv)
  -- The renaming.
  obtain ⟨ρ, hρ⟩ : ∃ ρ : DeclarativeVR → DeclarativeVR,
      ρ = dummyRename fr ext ghosts (floatList frAct).length := ⟨_, rfl⟩
  have hρd : ∀ {v : DeclarativeVR} {w : Variable}, findVar (varMapOfFrame fr) v = some w →
      ρ v = reindexVR fr ext v := fun hv => by
    rw [hρ]
    exact dummyRename_of_declared hv
  have hρu : ∀ {v : DeclarativeVR}, findVar (varMapOfFrame fr) v = none →
      ρ v = ⟨v.type, (floatList frAct).length + posOf ghosts v⟩ := fun hv => by
    rw [hρ]
    exact dummyRename_of_undeclared hv
  -- A declared variable goes to its variable in `frAct`, below the dummy slots.
  have hdecl : ∀ {v : DeclarativeVR} {w : Variable}, findVar (varMapOfFrame fr) v = some w →
      findVR (varMapOfFrame ext) w = some (ρ v) ∧ (ρ v).i < (floatList frAct).length := by
    intro v w hv
    have hsrc := findVar_findVR_inverse_frame hfr.2 hv
    have hwAct : w ∈ frAct.vars := vars_subset_of_hyps_subset hhyps (findVR_in_vars hsrc)
    obtain ⟨y, hy⟩ := (varMapDomain_ofFrame frAct w).mp hwAct
    have hyext : findVR (varMapOfFrame ext) w = some y := by
      rw [hext, findVR_extendDummies (Or.inl hwAct)]
      exact hy
    rw [hρd hv, reindexVR_of_findVR hsrc hyext]
    exact ⟨hyext, findVR_index_lt_floatList hy⟩
  -- An undeclared variable goes to its dummy slot.
  have hslot : ∀ v ∈ ghosts, findVar (varMapOfFrame ext)
      ⟨v.type, (floatList frAct).length + posOf ghosts v⟩ =
        some ⟨dummyName bound (posOf ghosts v)⟩ := by
    intro v hv
    rw [hvm_ext]
    have hprefix : (varMapOfFrame frAct).find? (fun p => p.2 =
        (⟨v.type, (floatList frAct).length + posOf ghosts v⟩ : DeclarativeVR)) = none := by
      refine find?_none_of_all fun entry hentry => decide_eq_false fun heq => ?_
      have hb := varMapOfFrameAux_index_bound (n := 0) (l := floatList frAct) hentry
      have hi := congrArg Metamath.VR.i heq
      simp only at hi
      omega
    have halloc := findVar_allocate bound ghosts v hv (floatList frAct).length 0
    rw [Nat.zero_add] at halloc
    unfold findVar at halloc ⊢
    rw [find?_append_of_none hprefix, hds]
    exact halloc
  have hslot_name : ∀ v ∈ ghosts,
      (⟨dummyName bound (posOf ghosts v)⟩ : Variable) ∈ ds.map Prod.snd := by
    intro v hv
    have hmem := findVar_mem_of_some (hslot v hv)
    rw [hvm_ext] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · have hb := varMapOfFrameAux_index_bound (n := 0) (l := floatList frAct) hleft
      simp only at hb
      omega
    · exact varMapOfFrameAux_vars.mp ⟨_, hright⟩
  -- Every variable of the derivation has an image in the extended frame.
  have himage : ∀ v, v ∈ (statementOfFrame fr e).vars ++ V →
      ∃ x, findVR (varMapOfFrame ext) x = some (ρ v) := by
    intro v hv
    cases hfv : findVar (varMapOfFrame fr) v with
    | some w => exact ⟨w, (hdecl hfv).1⟩
    | none =>
        rw [hρu hfv]
        exact ⟨_, findVar_findVR_inverse_frame hwf.2 (hslot v (hghost v hv hfv))⟩
  have hinj : ∀ a b, a ∈ (statementOfFrame fr e).vars ++ V →
      b ∈ (statementOfFrame fr e).vars ++ V → ρ a = ρ b → a = b := by
    intro a b ha hb hab
    cases hfa : findVar (varMapOfFrame fr) a with
    | some wa =>
        cases hfb : findVar (varMapOfFrame fr) b with
        | some wb =>
            refine Decidable.byContradiction fun hne => ?_
            apply reindexVR_ne_of_findVar hfr.2 hfa hfb hne
            rw [← hρd hfa, ← hρd hfb]
            exact hab
        | none =>
            have hlt := (hdecl hfa).2
            rw [hab, hρu hfb] at hlt
            simp only at hlt
            omega
    | none =>
        cases hfb : findVar (varMapOfFrame fr) b with
        | some wb =>
            have hlt := (hdecl hfb).2
            rw [← hab, hρu hfa] at hlt
            simp only at hlt
            omega
        | none =>
            rw [hρu hfa, hρu hfb] at hab
            have hi := congrArg Metamath.VR.i hab
            simp only at hi
            exact posOf_inj (hghost a ha hfa) (hghost b hb hfb) (by omega)
  -- A pair with an undeclared variable is a dummy pair.
  have hdummyPair : ∀ a b, a ∈ (statementOfFrame fr e).vars ++ V →
      b ∈ (statementOfFrame fr e).vars ++ V → a ≠ b → findVar (varMapOfFrame fr) a = none →
      (frameToContext ext).dj (ρ a) (ρ b) := by
    intro a b ha hb hab hnone
    have hga := hghost a ha hnone
    have hne : ρ a ≠ ρ b := fun h => hab (hinj a b ha hb h)
    have hxa := findVar_findVR_inverse_frame hwf.2 (hslot a hga)
    rw [← hρu hnone] at hxa
    obtain ⟨xb, hxb⟩ := himage b hb
    have hxne : xb ≠ ⟨dummyName bound (posOf ghosts a)⟩ := by
      intro heq
      rw [heq, hxa] at hxb
      exact hne (Option.some.inj hxb)
    have hxb_var : xb ∈ frAct.vars ++ ds.map Prod.snd := by
      rw [← hvars_ext]
      exact findVR_in_vars hxb
    have hpair := dummyDV_complete (hslot_name a hga) hxb_var hxne
    apply dvRel_to_dvListToDeclarativeDJ fun _ _ _ h1 h2 => findVR_injective_frame h1 h2
    · exact ⟨fun h => hxne h.symm, hpair.imp (hdummydv _) (hdummydv _)⟩
    · exact hxa
    · exact hxb
  have hdj : ∀ a b, a ∈ (statementOfFrame fr e).vars ++ V →
      b ∈ (statementOfFrame fr e).vars ++ V →
      ((statementOfFrame fr e).withDummies V).ctx.dj a b →
      (frameToContext ext).dj (ρ a) (ρ b) := by
    intro a b ha hb hab
    obtain ⟨⟨hne, hmand⟩, _, _⟩ := hab
    cases hfa : findVar (varMapOfFrame fr) a with
    | none => exact hdummyPair a b ha hb hne hfa
    | some wa =>
        cases hfb : findVar (varMapOfFrame fr) b with
        | none => exact (frameToContext ext).dj.symm (hdummyPair b a hb ha (Ne.symm hne) hfb)
        | some wb =>
            rw [hρd hfa, hρd hfb]
            exact frameToContext_dj_reindex hfr.2 hvars_fr_ext hdv_ext
              (hmand (mem_vars_statementOfFrame hfr.2 hfa) (mem_vars_statementOfFrame hfr.2 hfb))
  have htype : ∀ v, (ρ v).type = v.type := by
    intro v
    cases hfv : findVar (varMapOfFrame fr) v with
    | some w =>
        rw [hρd hfv]
        exact reindexVR_type hfr.2 (frameMapTypesAgree_of_extension hwf.1 hhyps_ext) v
    | none => rw [hρu hfv]
  have hT : ∀ v, v ∈ (statementOfFrame fr e).vars ++ V → FrameDeclared ext (ρ v) := by
    intro v hv
    obtain ⟨x, hx⟩ := himage v hv
    exact ⟨x, findVR_findVar_inverse_frame hx⟩
  -- On formulas over declared variables the renaming is the reindexing.
  have hcongr : ∀ {f : DeclarativeFormula},
      (∀ x, x ∈' f.2 → ∃ w, findVar (varMapOfFrame fr) x = some w) →
      f.subst (Metamath.renameSubst ρ) = f.subst (Metamath.renameSubst (reindexVR fr ext)) := by
    intro f hf
    apply Metamath.Formula.subst_congr
    intro x hx
    obtain ⟨w, hw⟩ := hf x hx
    simp only [Metamath.renameSubst, hρd hw]
  have hhyps' : ∀ g ∈ ((statementOfFrame fr e).withDummies V).ctx.hyps,
      g.subst (Metamath.renameSubst ρ) ∈ (frameToContext ext).hyps := by
    intro g hg
    have hg' : g ∈ (frameToContext fr).hyps := hg
    obtain ⟨hyp, hmem, rfl⟩ := hyps_correspondence hg'
    rw [hcongr fun x hx => declared_of_mem_hyp hg' hx]
    rw [hypToDeclarativeFormula_subst_reindex hmem hvars_fr_ext ?_]
    · exact hypToDeclarativeFormula_mem (hhyps_ext hyp hmem)
    · intro eh heq s hs y hy
      subst heq
      have hsv : (⟨s⟩ : Variable) ∈ ext.vars := findVR_in_vars hy
      rw [hvars_ext] at hsv
      rcases List.mem_append.mp hsv with hAct | hdum
      · exact (varMapDomain_ofFrame fr ⟨s⟩).mp (hesyms eh hmem s hs hAct)
      · obtain ⟨p, hp, hps⟩ := List.mem_map.mp hdum
        have hps' : p.2.v = s := by rw [hps]
        exact absurd (hps' ▸ hs) (hfresh.not_essential p hp eh (hhyps _ hmem))
  have hfmla : (exprToFormula (varMapOfFrame fr) e).subst (Metamath.renameSubst ρ) =
      exprToFormula (varMapOfFrame ext) e := by
    rw [hcongr fun x hx => declared_of_mem_exprToFormula hx]
    refine exprToFormula_subst_reindex_of_syms (fun s hs y hy => ?_) (fun s _ x hx => ?_)
    · have hsv : (⟨s⟩ : Variable) ∈ ext.vars := findVR_in_vars hy
      rw [hvars_ext] at hsv
      rcases List.mem_append.mp hsv with hAct | hdum
      · exact (varMapDomain_ofFrame fr ⟨s⟩).mp (hsyms s hs hAct)
      · obtain ⟨p, hp, hps⟩ := List.mem_map.mp hdum
        have hps' : p.2.v = s := by rw [hps]
        exact absurd (hps' ▸ hs) (hconcl p hp)
    · exact (varMapDomain_ofFrame ext ⟨s⟩).mp (hvars_fr_ext _ (findVR_in_vars hx))
  have hren := Metamath.Derivable.rename (axs := dbToAxioms Γ)
    (fun _ hax => dbToAxioms_trimmed hax)
    (Γ := ((statementOfFrame fr e).withDummies V).ctx)
    (T' := FrameDeclared ext) (Γ' := frameToContext ext)
    (fun g hg v hv => List.mem_append_left V ((statementOfFrame fr e).mem_vars_of_hyp hg hv))
    htype hT hhyps' hdj hder
  change Metamath.Derivable _ _ _
    ((exprToFormula (varMapOfFrame fr) e).subst (Metamath.renameSubst ρ)) at hren
  rw [hfmla] at hren
  exact hren


end Metamath.Spec.DummyExtension
