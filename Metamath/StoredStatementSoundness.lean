/-
Stored-statement soundness for the streaming Metamath verifier.

The operational checker must use the full active frame while checking a proof:
proof-local dummy variables can occur there.  The assertion stored in the
database instead contains the trimmed mandatory frame.  This module connects
those two levels through `Statement.untrim`, then eliminates earlier derived
theorems from the final axiom set.
-/

import Metamath.PrefixWitnessCheckBytes
import Metamath.Spec.Equivalence

set_option autoImplicit false

namespace Metamath.StoredStatementSoundness

open Metamath
open Metamath.Verify
open Metamath.Kernel (toDatabase toFrame toExpr)
open Metamath.Spec
open Metamath.Spec.Equivalence
namespace Semantic

/-- The declarative statement denoted by an operational frame and expression. -/
noncomputable def statementOfFrame (fr : Spec.Frame) (e : Spec.Expr) : Metamath.Statement :=
  ⟨frameToContext fr, exprToFormula (varMapOfFrame fr) e⟩

/-- A type-preserving variable renaming, represented as a substitution. -/
def renameSubst (ρ : Metamath.VR → Metamath.VR) : Metamath.VR → Metamath.Expr :=
  fun v => [Metamath.Sym.var (ρ v)]

/-- The generic active-frame to stored-statement bridge.

The hypotheses are precisely the three structural obligations discharged by
Metamath frame trimming: renamed conclusion, renamed hypotheses, and renamed
distinct-variable constraints.  No assertion membership is assumed. -/
theorem statementProvable_of_translation
    {axs : Metamath.Statement → Prop}
    {activeCtx : Metamath.Context} {activeFmla : Metamath.Formula}
    {stored : Metamath.Statement} (ρ : Metamath.VR → Metamath.VR)
    (h_type : ∀ v, (ρ v).type = v.type)
    (h_fmla : activeFmla.subst (renameSubst ρ) = stored.fmla)
    (h_dj : activeCtx.dj.subst (renameSubst ρ) stored.untrim.ctx.dj)
    (h_hyps : ∀ h ∈ activeCtx.hyps,
      Metamath.Provable axs stored.untrim.ctx (h.subst (renameSubst ρ)))
    (h_active : Metamath.Provable axs activeCtx activeFmla) :
    stored.Provable axs := by
  change Metamath.Provable axs stored.untrim.ctx stored.fmla
  rw [← h_fmla]
  exact Metamath.Provable.trans' (renameSubst ρ) h_active h_dj h_hyps
    (fun v => by
      have h := Metamath.Provable.var (axs := axs) (Γ := stored.untrim.ctx) (ρ v)
      change Metamath.Provable axs stored.untrim.ctx
        (v.type, [Metamath.Sym.var (ρ v)])
      rw [← h_type v]
      exact h)

/-! ## Canonical reindexing between frame-local variable maps -/

/-- Every variable index produced by `varMapOfFrameAux` lies below the end of
the enumerated interval. -/
theorem varMapOfFrameAux_index_lt
    {n : Nat} {xs : List (Spec.Constant × Spec.Variable)}
    {v : Spec.Variable} {vr : Metamath.VR}
    (h_mem : (v, vr) ∈ varMapOfFrameAux n xs) :
    vr.i < n + xs.length := by
  induction xs generalizing n with
  | nil => cases h_mem
  | cons cv rest ih =>
      simp only [varMapOfFrameAux, List.mem_cons] at h_mem
      rcases h_mem with h_head | h_tail
      · have h_vr : vr = ⟨cv.1.c, n⟩ := (Prod.mk.inj h_head).2
        simp [h_vr]
      · have h_lt := ih (n := n + 1) h_tail
        simp only [List.length_cons]
        simp only [Nat.add_assoc] at h_lt
        omega

/-- A variable found in a frame's canonical map has an index below the number
of floating hypotheses in that frame. -/
theorem findVR_index_lt_floatList
    {fr : Spec.Frame} {v : Spec.Variable} {vr : Metamath.VR}
    (h_find : findVR (varMapOfFrame fr) v = some vr) :
    vr.i < (floatList fr).length := by
  have h_mem := findVR_mem_of_some h_find
  simpa using (varMapOfFrameAux_index_lt (n := 0) h_mem)

/-- Reindex a variable from `source`'s canonical numbering to `target`'s.
Variables absent from `target` are moved above its canonical index range. -/
def reindexVR (source target : Spec.Frame) (vr : Metamath.VR) : Metamath.VR :=
  match findVar (varMapOfFrame source) vr with
  | some v =>
      match findVR (varMapOfFrame target) v with
      | some vr' => vr'
      | none => ⟨vr.type, (floatList target).length + vr.i⟩
  | none => ⟨vr.type, (floatList target).length + vr.i⟩

theorem reindexVR_of_findVR
    {source target : Spec.Frame} {v : Spec.Variable}
    {sourceVR targetVR : Metamath.VR}
    (h_source : findVR (varMapOfFrame source) v = some sourceVR)
    (h_target : findVR (varMapOfFrame target) v = some targetVR) :
    reindexVR source target sourceVR = targetVR := by
  have h_back := findVR_findVar_inverse_frame h_source
  simp [reindexVR, h_back, h_target]

theorem reindexVR_of_findVR_target_none
    {source target : Spec.Frame} {v : Spec.Variable}
    {sourceVR : Metamath.VR}
    (h_source : findVR (varMapOfFrame source) v = some sourceVR)
    (h_target : findVR (varMapOfFrame target) v = none) :
    reindexVR source target sourceVR =
      ⟨sourceVR.type, (floatList target).length + sourceVR.i⟩ := by
  have h_back := findVR_findVar_inverse_frame h_source
  simp [reindexVR, h_back, h_target]

/-- The only type obligation for reindexing is that a source variable retained
by the target has the same floating typecode there. -/
def FrameMapTypesAgree (source target : Spec.Frame) : Prop :=
  ∀ v sourceVR targetVR,
    findVR (varMapOfFrame source) v = some sourceVR →
    findVR (varMapOfFrame target) v = some targetVR →
    sourceVR.type = targetVR.type

theorem reindexVR_type
    {source target : Spec.Frame}
    (h_source_nodup : FloatVarNoDup source)
    (h_types : FrameMapTypesAgree source target) (vr : Metamath.VR) :
    (reindexVR source target vr).type = vr.type := by
  unfold reindexVR
  split
  next v h_back =>
    split
    next targetVR h_target =>
      have h_source := findVar_findVR_inverse_frame
        (fr := source) (vr := vr) (v := v) h_source_nodup h_back
      exact (h_types v vr targetVR h_source h_target).symm
    next => rfl
  next => rfl

/-- Target variables are also source variables. -/
def FrameMapDomainLE (source target : Spec.Frame) : Prop :=
  ∀ v targetVR,
    findVR (varMapOfFrame target) v = some targetVR →
    ∃ sourceVR, findVR (varMapOfFrame source) v = some sourceVR

/-- Every source variable occurring in an expression is retained by the target. -/
def ExprVarsRetained (source target : Spec.Frame) (e : Spec.Expr) : Prop :=
  ∀ s, s ∈ e.syms → ∀ sourceVR,
    findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR →
    ∃ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR

/-- Scope checking plus the global constant/variable separation proves that
every source variable occurring in an expression is represented in the target
frame.  This is the semantic form of the mandatory-variable calculation used
by frame trimming. -/
theorem exprVarsRetained_of_scopes
    {consts : Spec.ConstSet} {source target : Spec.Frame} {e : Spec.Expr}
    (h_source_disjoint : Spec.FrameVarsDisjointConsts consts source)
    (h_target_scope : Spec.ExprVarsInScope consts target e) :
    ExprVarsRetained source target e := by
  intro s h_s sourceVR h_source
  have h_source_var : Spec.Variable.mk s ∈ source.vars :=
    findVR_in_vars h_source
  have h_not_const : ¬ consts s :=
    h_source_disjoint (Spec.Variable.mk s) h_source_var
  rcases h_target_scope s h_s with h_target_var | h_const
  · exact (varMapDomain_ofFrame target (Spec.Variable.mk s)).mp h_target_var
  · exact (h_not_const h_const).elim

/-- A hypothesis-subset relation makes the target variable-map domain a
subset of the source domain. -/
theorem frameMapDomainLE_of_hyps_subset
    {source target : Spec.Frame}
    (h_subset : ∀ h, h ∈ target.hyps → h ∈ source.hyps) :
    FrameMapDomainLE source target := by
  intro v targetVR h_target
  obtain ⟨c, h_float_target, _h_type⟩ :=
    mem_varMapOfFrame_sound_typed (findVR_mem_of_some h_target)
  exact findVR_of_float (h_subset _ h_float_target)

/-- If target floating hypotheses are source hypotheses, source uniqueness
forces the canonical variable maps to agree on typecodes. -/
theorem frameMapTypesAgree_of_hyps_subset
    {source target : Spec.Frame}
    (h_source_unique : FloatUnique source)
    (h_subset : ∀ h, h ∈ target.hyps → h ∈ source.hyps) :
    FrameMapTypesAgree source target := by
  intro v sourceVR targetVR h_source h_target
  obtain ⟨sourceType, h_float_source, h_source_type⟩ :=
    mem_varMapOfFrame_sound_typed (findVR_mem_of_some h_source)
  obtain ⟨targetType, h_float_target, h_target_type⟩ :=
    mem_varMapOfFrame_sound_typed (findVR_mem_of_some h_target)
  have h_type_eq : sourceType = targetType :=
    h_source_unique sourceType targetType v h_float_source
      (h_subset _ h_float_target)
  exact h_source_type.trans (h_type_eq ▸ h_target_type.symm)

theorem toMarioSym_subst_reindex
    {source target : Spec.Frame} (h_dom : FrameMapDomainLE source target)
    {s : String}
    (h_keep : ∀ sourceVR,
      findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR →
      ∃ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR) :
    (match toMarioSym (varMapOfFrame source) s with
      | Metamath.Sym.const c => [Metamath.Sym.const c]
      | Metamath.Sym.var vr => renameSubst (reindexVR source target) vr) =
      [toMarioSym (varMapOfFrame target) s] := by
  unfold toMarioSym
  cases h_source : findVR (varMapOfFrame source) ⟨s⟩ with
  | none =>
      cases h_target : findVR (varMapOfFrame target) ⟨s⟩ with
      | none => simp [h_source, h_target]
      | some targetVR =>
          obtain ⟨sourceVR, h_source'⟩ := h_dom ⟨s⟩ targetVR h_target
          rw [h_source] at h_source'
          cases h_source'
  | some sourceVR =>
      obtain ⟨targetVR, h_target⟩ := h_keep sourceVR h_source
      simp [h_source, h_target, renameSubst,
        reindexVR_of_findVR h_source h_target]

theorem exprToMarioExpr_subst_reindex
    {source target : Spec.Frame} (h_dom : FrameMapDomainLE source target)
    {e : Spec.Expr} (h_keep : ExprVarsRetained source target e) :
    (exprToMarioExpr (varMapOfFrame source) e).subst
        (renameSubst (reindexVR source target)) =
      exprToMarioExpr (varMapOfFrame target) e := by
  unfold exprToMarioExpr
  have go : ∀ xs : List String,
      (∀ s, s ∈ xs → ∀ sourceVR,
        findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR →
        ∃ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR) →
      Metamath.Expr.subst (renameSubst (reindexVR source target))
          (xs.map (toMarioSym (varMapOfFrame source))) =
        xs.map (toMarioSym (varMapOfFrame target)) := by
    intro xs h_xs
    induction xs with
    | nil => rfl
    | cons s rest ih =>
        have h_head := toMarioSym_subst_reindex (source := source)
          (target := target) h_dom
          (s := s) (fun sourceVR h_source =>
            h_xs s (by simp) sourceVR h_source)
        have h_tail := ih (fun s' h_mem sourceVR h_source =>
          h_xs s' (by simp [h_mem]) sourceVR h_source)
        cases h_sym : toMarioSym (varMapOfFrame source) s with
        | const c =>
            have h_sym_eq :
                Metamath.Sym.const c = toMarioSym (varMapOfFrame target) s := by
              simpa [h_sym] using h_head
            calc
              Metamath.Expr.subst (renameSubst (reindexVR source target))
                    (toMarioSym (varMapOfFrame source) s ::
                      rest.map (toMarioSym (varMapOfFrame source))) =
                  Metamath.Sym.const c ::
                    Metamath.Expr.subst (renameSubst (reindexVR source target))
                      (rest.map (toMarioSym (varMapOfFrame source))) := by
                    rw [h_sym]
                    rfl
              _ = Metamath.Sym.const c ::
                    rest.map (toMarioSym (varMapOfFrame target)) :=
                  congrArg (Metamath.Sym.const c :: ·) h_tail
              _ = toMarioSym (varMapOfFrame target) s ::
                    rest.map (toMarioSym (varMapOfFrame target)) := by
                  rw [h_sym_eq]
        | var vr =>
            have h_sym_eq :
                Metamath.Sym.var (reindexVR source target vr) =
                  toMarioSym (varMapOfFrame target) s := by
              simpa [h_sym, renameSubst] using h_head
            calc
              Metamath.Expr.subst (renameSubst (reindexVR source target))
                    (toMarioSym (varMapOfFrame source) s ::
                      rest.map (toMarioSym (varMapOfFrame source))) =
                  Metamath.Sym.var (reindexVR source target vr) ::
                    Metamath.Expr.subst (renameSubst (reindexVR source target))
                      (rest.map (toMarioSym (varMapOfFrame source))) := by
                    rw [h_sym]
                    rfl
              _ = Metamath.Sym.var (reindexVR source target vr) ::
                    rest.map (toMarioSym (varMapOfFrame target)) := by
                  rw [h_tail]
              _ = toMarioSym (varMapOfFrame target) s ::
                    rest.map (toMarioSym (varMapOfFrame target)) := by
                  rw [h_sym_eq]
  exact go e.syms h_keep

theorem exprToFormula_subst_reindex
    {source target : Spec.Frame} (h_dom : FrameMapDomainLE source target)
    {e : Spec.Expr} (h_keep : ExprVarsRetained source target e) :
    (exprToFormula (varMapOfFrame source) e).subst
        (renameSubst (reindexVR source target)) =
      exprToFormula (varMapOfFrame target) e := by
  exact congrArg (fun xs => (e.typecode.c, xs))
    (exprToMarioExpr_subst_reindex h_dom h_keep)

/-- Every variable occurring in a frame-denoted statement belongs to that
frame's canonical map, hence lies below its floating-hypothesis count. -/
theorem statementOfFrame_var_index_lt
    {fr : Spec.Frame} {e : Spec.Expr} {vr : Metamath.VR}
    (h_mem : vr ∈ (statementOfFrame fr e).vars) :
    vr.i < (floatList fr).length := by
  simp only [statementOfFrame, Metamath.Statement.vars,
    List.mem_flatMap, List.mem_cons] at h_mem
  obtain ⟨f, h_f, h_vr⟩ := h_mem
  rcases h_f with rfl | h_f
  · have h_expr : vr ∈' exprToMarioExpr (varMapOfFrame fr) e :=
      Expr_vars_iff_mem.mp h_vr
    obtain ⟨s, _h_s, h_find⟩ := exprToMarioExpr_mem_extract h_expr
    exact findVR_index_lt_floatList h_find
  · unfold frameToContext at h_f
    obtain ⟨hyp, h_hyp, rfl⟩ := List.mem_map.mp h_f
    cases hyp with
    | essential e_hyp =>
        have h_expr : vr ∈' exprToMarioExpr (varMapOfFrame fr) e_hyp :=
          Expr_vars_iff_mem.mp h_vr
        obtain ⟨s, _h_s, h_find⟩ := exprToMarioExpr_mem_extract h_expr
        exact findVR_index_lt_floatList h_find
    | floating c v =>
        obtain ⟨vr', h_find⟩ := findVR_of_float
          (fr := fr) (c := c) (v := v) h_hyp
        unfold hypToMarioFormula at h_vr
        simp only [h_find, Metamath.Expr.vars, List.mem_singleton] at h_vr
        subst h_vr
        exact findVR_index_lt_floatList h_find

/-- Disjoint variables in a converted context came from two source variables
that the frame map can recover. -/
theorem dvListToMarioDJ_findVars
    {fr : Spec.Frame} {a b : Metamath.VR}
    (h_dj : (dvListToMarioDJ (varMapOfFrame fr) fr.dv) a b) :
    ∃ v w,
      findVar (varMapOfFrame fr) a = some v ∧
      findVar (varMapOfFrame fr) b = some w := by
  unfold dvListToMarioDJ at h_dj
  simp only [Metamath.DJ.mk'] at h_dj
  rcases h_dj.2 with h_pair | h_pair
  · obtain ⟨⟨v, w⟩, _h_mem, h_eq⟩ := List.mem_filterMap.mp h_pair
    cases h_v : findVR (varMapOfFrame fr) v with
    | none => rw [h_v] at h_eq; cases h_eq
    | some a' =>
        cases h_w : findVR (varMapOfFrame fr) w with
        | none => rw [h_v, h_w] at h_eq; cases h_eq
        | some b' =>
            rw [h_v, h_w] at h_eq
            cases Option.some.inj h_eq
            exact ⟨v, w, findVR_findVar_inverse_frame h_v,
              findVR_findVar_inverse_frame h_w⟩
  · obtain ⟨⟨v, w⟩, _h_mem, h_eq⟩ := List.mem_filterMap.mp h_pair
    cases h_v : findVR (varMapOfFrame fr) v with
    | none => rw [h_v] at h_eq; cases h_eq
    | some b' =>
        cases h_w : findVR (varMapOfFrame fr) w with
        | none => rw [h_v, h_w] at h_eq; cases h_eq
        | some a' =>
            rw [h_v, h_w] at h_eq
            cases Option.some.inj h_eq
            exact ⟨w, v, findVR_findVar_inverse_frame h_w,
              findVR_findVar_inverse_frame h_v⟩

/-- Reindexing is injective on variables represented by the source frame. -/
theorem reindexVR_ne_of_findVar
    {source target : Spec.Frame}
    (h_source_nodup : FloatVarNoDup source)
    {a b : Metamath.VR} {v w : Spec.Variable}
    (h_a : findVar (varMapOfFrame source) a = some v)
    (h_b : findVar (varMapOfFrame source) b = some w)
    (h_ne : a ≠ b) :
    reindexVR source target a ≠ reindexVR source target b := by
  have h_source_a := findVar_findVR_inverse_frame h_source_nodup h_a
  have h_source_b := findVar_findVR_inverse_frame h_source_nodup h_b
  intro h_eq
  cases h_target_a : findVR (varMapOfFrame target) v with
  | some targetA =>
      cases h_target_b : findVR (varMapOfFrame target) w with
      | some targetB =>
          have h_ra := reindexVR_of_findVR h_source_a h_target_a
          have h_rb := reindexVR_of_findVR h_source_b h_target_b
          rw [h_ra, h_rb] at h_eq
          have h_vw : v = w := findVR_injective_frame
            h_target_a (h_eq ▸ h_target_b)
          subst h_vw
          exact h_ne (Option.some.inj (h_source_a.symm.trans h_source_b))
      | none =>
          have h_ra := reindexVR_of_findVR h_source_a h_target_a
          have h_rb := reindexVR_of_findVR_target_none h_source_b h_target_b
          rw [h_ra, h_rb] at h_eq
          have h_lt := findVR_index_lt_floatList h_target_a
          have h_i := congrArg Metamath.VR.i h_eq
          change targetA.i = (floatList target).length + b.i at h_i
          omega
  | none =>
      cases h_target_b : findVR (varMapOfFrame target) w with
      | some targetB =>
          have h_ra := reindexVR_of_findVR_target_none h_source_a h_target_a
          have h_rb := reindexVR_of_findVR h_source_b h_target_b
          rw [h_ra, h_rb] at h_eq
          have h_lt := findVR_index_lt_floatList h_target_b
          have h_i := congrArg Metamath.VR.i h_eq
          change (floatList target).length + a.i = targetB.i at h_i
          omega
      | none =>
          have h_ra := reindexVR_of_findVR_target_none h_source_a h_target_a
          have h_rb := reindexVR_of_findVR_target_none h_source_b h_target_b
          rw [h_ra, h_rb] at h_eq
          apply h_ne
          cases a with
          | mk aty ai =>
              cases b with
              | mk bt bi =>
                  simp only [Metamath.VR.mk.injEq] at h_eq ⊢
                  exact ⟨h_eq.1, Nat.add_left_cancel h_eq.2⟩

/-- Structural relation established by Metamath's frame trimming. -/
structure FrameReduction (source target : Spec.Frame) (e : Spec.Expr) : Prop where
  sourceWellFormed : FrameWellFormed source
  targetWellFormed : FrameWellFormed target
  typesAgree : FrameMapTypesAgree source target
  domainLE : FrameMapDomainLE source target
  conclusionRetained : ExprVarsRetained source target e
  essentialRetained : ∀ e_hyp,
    Spec.Hyp.essential e_hyp ∈ source.hyps →
    Spec.Hyp.essential e_hyp ∈ target.hyps ∧
      ExprVarsRetained source target e_hyp
  dvRetained : ∀ v w,
    Spec.dvRel source.dv v w →
    (∃ targetVR, findVR (varMapOfFrame target) v = some targetVR) →
    (∃ targetVR, findVR (varMapOfFrame target) w = some targetVR) →
    Spec.dvRel target.dv v w

theorem frameReduction_dj_subst
    {source target : Spec.Frame} {e : Spec.Expr}
    (h_red : FrameReduction source target e) :
    (frameToContext source).dj.subst
      (renameSubst (reindexVR source target))
      (statementOfFrame target e).untrim.ctx.dj := by
  intro a b h_ab
  obtain ⟨v, w, h_a, h_b⟩ := dvListToMarioDJ_findVars h_ab
  have h_source_rel : Spec.dvRel source.dv v w :=
    dvListToMarioDJ_to_dvRel h_ab h_a h_b
  have h_reindex_ne : reindexVR source target a ≠ reindexVR source target b :=
    reindexVR_ne_of_findVar h_red.sourceWellFormed.2 h_a h_b
      ((frameToContext source).dj.ne h_ab)
  intro x y h_x h_y
  have h_x' : x = reindexVR source target a :=
    Metamath.Sym.var.inj (List.mem_singleton.mp h_x)
  have h_y' : y = reindexVR source target b :=
    Metamath.Sym.var.inj (List.mem_singleton.mp h_y)
  rw [h_x', h_y']
  change ((frameToContext target).dj.untrim
      (fun vr => vr ∈ (statementOfFrame target e).vars))
        (reindexVR source target a) (reindexVR source target b)
  refine ⟨h_reindex_ne, ?_⟩
  intro h_a_mandatory h_b_mandatory
  have h_source_a := findVar_findVR_inverse_frame
    h_red.sourceWellFormed.2 h_a
  have h_source_b := findVar_findVR_inverse_frame
    h_red.sourceWellFormed.2 h_b
  cases h_target_a : findVR (varMapOfFrame target) v with
  | none =>
      have h_ra := reindexVR_of_findVR_target_none h_source_a h_target_a
      have h_lt := statementOfFrame_var_index_lt h_a_mandatory
      rw [h_ra] at h_lt
      change (floatList target).length + a.i < (floatList target).length at h_lt
      omega
  | some targetA =>
      cases h_target_b : findVR (varMapOfFrame target) w with
      | none =>
          have h_rb := reindexVR_of_findVR_target_none h_source_b h_target_b
          have h_lt := statementOfFrame_var_index_lt h_b_mandatory
          rw [h_rb] at h_lt
          change (floatList target).length + b.i < (floatList target).length at h_lt
          omega
      | some targetB =>
          have h_ra := reindexVR_of_findVR h_source_a h_target_a
          have h_rb := reindexVR_of_findVR h_source_b h_target_b
          rw [h_ra, h_rb]
          apply dvRel_to_dvListToMarioDJ
          · intro v' v'' vr' h_v' h_v''
            exact findVR_injective_frame h_v' h_v''
          · exact h_red.dvRetained v w h_source_rel
              ⟨targetA, h_target_a⟩ ⟨targetB, h_target_b⟩
          · exact h_target_a
          · exact h_target_b

theorem frameReduction_hyp_provable
    {axs : Metamath.Statement → Prop}
    {source target : Spec.Frame} {e : Spec.Expr}
    (h_red : FrameReduction source target e)
    (h : Metamath.Formula)
    (h_mem : h ∈ (frameToContext source).hyps) :
    Metamath.Provable axs (statementOfFrame target e).untrim.ctx
      (h.subst (renameSubst (reindexVR source target))) := by
  obtain ⟨hyp, h_hyp_source, h_eq⟩ := hyps_correspondence h_mem
  cases hyp with
  | essential e_hyp =>
      obtain ⟨h_hyp_target, h_keep⟩ :=
        h_red.essentialRetained e_hyp h_hyp_source
      rw [h_eq, hypToMarioFormula_essential]
      rw [exprToFormula_subst_reindex h_red.domainLE h_keep]
      exact Metamath.Provable.hyp _
        (hypToMarioFormula_mem h_hyp_target)
  | floating c v =>
      obtain ⟨sourceVR, h_sourceVR, h_source_type⟩ :=
        findVR_of_float_typed h_red.sourceWellFormed.1 h_hyp_source
      have h_reindex_type := reindexVR_type h_red.sourceWellFormed.2
        h_red.typesAgree sourceVR
      rw [h_eq]
      unfold hypToMarioFormula
      simp only [h_sourceVR, Metamath.Formula.subst, Metamath.Expr.subst,
        renameSubst]
      have h_var := Metamath.Provable.var
        (axs := axs) (Γ := (statementOfFrame target e).untrim.ctx)
        (reindexVR source target sourceVR)
      change Metamath.Provable axs (statementOfFrame target e).untrim.ctx
        (c.c, [Metamath.Sym.var (reindexVR source target sourceVR)])
      rw [← h_source_type, ← h_reindex_type]
      exact h_var

/-- A semantic derivation under the full active frame certifies the exact
statement formed from the trimmed mandatory frame. -/
theorem statementProvable_of_frameReduction
    {axs : Metamath.Statement → Prop}
    {source target : Spec.Frame} {e : Spec.Expr}
    (h_red : FrameReduction source target e)
    (h_active : Metamath.Provable axs (frameToContext source)
      (exprToFormula (varMapOfFrame source) e)) :
    (statementOfFrame target e).Provable axs := by
  apply statementProvable_of_translation
    (ρ := reindexVR source target)
  · exact reindexVR_type h_red.sourceWellFormed.2 h_red.typesAgree
  · exact exprToFormula_subst_reindex h_red.domainLE h_red.conclusionRetained
  · exact frameReduction_dj_subst h_red
  · exact frameReduction_hyp_provable h_red
  · exact h_active

/-- Operational proof validity plus the standard database invariants certifies
the exact stored declarative statement. -/
theorem statementProvable_of_operational_frameReduction
    {Γ : Spec.Database} {consts : Spec.ConstSet}
    {source target : Spec.Frame} {e : Spec.Expr}
    (h_strong : Spec.Equivalence.WellFormedDatabaseStrong Γ consts)
    (h_source_disjoint : Spec.FrameVarsDisjointConsts consts source)
    (h_red : FrameReduction source target e)
    (h_active : Spec.Provable Γ source e) :
    (statementOfFrame target e).Provable (dbToAxioms Γ) := by
  apply statementProvable_of_frameReduction h_red
  exact operational_to_semantic h_strong h_source_disjoint h_active

/-! ## Derived-statement elimination

`Statement.Provable` checks a stored statement in its `untrim` context.  When
a proved statement is used as a rule, proof-local variables absent from the
stored statement must be renamed away from the ambient statement and the
actual substitution images.  The following construction performs that fresh
renaming explicitly; it is the cut theorem needed to remove earlier `$p`
statements from an axiom predicate. -/

/-- One more than every variable index in a finite forbidden set. -/
def freshBase (xs : List Metamath.VR) : Nat :=
  xs.foldr (fun v n => max (v.i + 1) n) 0

theorem index_lt_freshBase_of_mem {xs : List Metamath.VR} {v : Metamath.VR}
    (h : v ∈ xs) : v.i < freshBase xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst x
        change v.i < max (v.i + 1) (freshBase xs)
        have h₁ := Nat.lt_succ_self v.i
        have h₂ := Nat.le_max_left (v.i + 1) (freshBase xs)
        omega
      · change v.i < max (x.i + 1) (freshBase xs)
        have h₁ := ih h
        have h₂ := Nat.le_max_right (x.i + 1) (freshBase xs)
        omega

/-- A type-preserving injection whose image avoids a finite set. -/
def freshVR (xs : List Metamath.VR) (v : Metamath.VR) : Metamath.VR :=
  ⟨v.type, freshBase xs + v.i⟩

@[simp] theorem freshVR_type (xs : List Metamath.VR) (v : Metamath.VR) :
    (freshVR xs v).type = v.type := rfl

theorem freshVR_injective (xs : List Metamath.VR) :
    Function.Injective (freshVR xs) := by
  intro v w h
  cases v with
  | mk vt vi =>
    cases w with
    | mk wt wi =>
      simp only [freshVR, Metamath.VR.mk.injEq] at h ⊢
      exact ⟨h.1, Nat.add_left_cancel h.2⟩

theorem freshVR_not_mem (xs : List Metamath.VR) (v : Metamath.VR) :
    freshVR xs v ∉ xs := by
  intro h
  have h_lt := index_lt_freshBase_of_mem h
  change freshBase xs + v.i < freshBase xs at h_lt
  omega

theorem expr_mem_iff_mem_vars {e : Metamath.Expr} {v : Metamath.VR} :
    v ∈ e.vars ↔ v ∈' e := by
  change v ∈ e.vars ↔ Metamath.Sym.var v ∈ e
  induction e with
  | nil =>
      change v ∈ ([] : List Metamath.VR) ↔
        Metamath.Sym.var v ∈ ([] : List Metamath.Sym)
      simp
  | cons s e ih =>
      cases s with
      | const c =>
          simp only [Metamath.Expr.vars]
          constructor
          · intro h
            exact List.Mem.tail _ (ih.mp h)
          · intro h
            cases h with
            | tail _ h => exact ih.mpr h
      | var w =>
          simp only [Metamath.Expr.vars, List.mem_cons]
          constructor
          · intro h
            rcases h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr (ih.mp h)
          · intro h
            rcases h with h | h
            · cases h
              exact Or.inl rfl
            · exact Or.inr (ih.mpr h)

theorem expr_subst_congr_on_vars {σ τ : Metamath.VR → Metamath.Expr}
    (e : Metamath.Expr) (h : ∀ v, v ∈ e.vars → σ v = τ v) :
    e.subst σ = e.subst τ := by
  induction e with
  | nil => rfl
  | cons s e ih =>
      cases s with
      | const c =>
          simp only [Metamath.Expr.subst]
          congr 1
          exact ih (fun v hv => h v (by simpa [Metamath.Expr.vars] using hv))
      | var w =>
          simp only [Metamath.Expr.subst]
          rw [h w (by simp [Metamath.Expr.vars])]
          congr 1
          exact ih (fun v hv => h v (by simp [Metamath.Expr.vars, hv]))

theorem formula_subst_congr_on_vars {σ τ : Metamath.VR → Metamath.Expr}
    (f : Metamath.Formula) (h : ∀ v, v ∈ f.2.vars → σ v = τ v) :
    f.subst σ = f.subst τ := by
  cases f
  exact congrArg _ (expr_subst_congr_on_vars _ h)

theorem fmla_vars_mem_statement (s : Metamath.Statement) {v : Metamath.VR}
    (h : v ∈ s.fmla.2.vars) : v ∈ s.vars := by
  simp only [Metamath.Statement.vars, List.mem_flatMap, List.mem_cons]
  exact ⟨s.fmla, Or.inl rfl, h⟩

theorem hyp_vars_mem_statement (s : Metamath.Statement)
    {f : Metamath.Formula} (hf : f ∈ s.ctx.hyps) {v : Metamath.VR}
    (h : v ∈ f.2.vars) : v ∈ s.vars := by
  simp only [Metamath.Statement.vars, List.mem_flatMap, List.mem_cons]
  exact ⟨f, Or.inr hf, h⟩

/-- Variables that a fresh proof-local renaming must avoid. -/
def applicationForbidden (outer ax : Metamath.Statement)
    (σ : Metamath.VR → Metamath.Expr) : List Metamath.VR :=
  outer.vars ++ ax.vars.flatMap fun v => (σ v).vars

theorem outer_var_mem_applicationForbidden (outer ax : Metamath.Statement)
    (σ : Metamath.VR → Metamath.Expr) {v : Metamath.VR}
    (h : v ∈ outer.vars) : v ∈ applicationForbidden outer ax σ := by
  exact List.mem_append_left _ h

theorem image_var_mem_applicationForbidden (outer ax : Metamath.Statement)
    (σ : Metamath.VR → Metamath.Expr) {v w : Metamath.VR}
    (hv : v ∈ ax.vars) (hw : w ∈' σ v) :
    w ∈ applicationForbidden outer ax σ := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨v, hv, expr_mem_iff_mem_vars.mpr hw⟩

/-- Complete a substitution on the proof-local variables of a proved rule by
fresh singleton variables.  It agrees with the supplied substitution on every
variable visible in the stored rule. -/
def completionSubst (outer ax : Metamath.Statement)
    (σ : Metamath.VR → Metamath.Expr) (v : Metamath.VR) : Metamath.Expr :=
  if v ∈ ax.vars then σ v else
    [Metamath.Sym.var (freshVR (applicationForbidden outer ax σ) v)]

theorem completionSubst_of_mem (outer ax : Metamath.Statement)
    (σ : Metamath.VR → Metamath.Expr) {v : Metamath.VR}
    (h : v ∈ ax.vars) : completionSubst outer ax σ v = σ v := by
  simp [completionSubst, h]

theorem completionSubst_of_not_mem (outer ax : Metamath.Statement)
    (σ : Metamath.VR → Metamath.Expr) {v : Metamath.VR}
    (h : v ∉ ax.vars) : completionSubst outer ax σ v =
      [Metamath.Sym.var (freshVR (applicationForbidden outer ax σ) v)] := by
  simp [completionSubst, h]

/-- A previously proved stored statement can be used as a rule inside the
untrimmed context of another stored statement. -/
theorem useProvedStatement
    {A : Metamath.Statement → Prop} {outer ax : Metamath.Statement}
    (hs : ax.Provable A) (σ : Metamath.VR → Metamath.Expr)
    (hdj : ax.ctx.dj.subst σ outer.untrim.ctx.dj)
    (hhyps : ∀ h ∈ ax.ctx.hyps,
      Metamath.Provable A outer.untrim.ctx (h.subst σ))
    (hvars : ∀ v ∈ ax.vars,
      Metamath.Provable A outer.untrim.ctx (v.type, σ v)) :
    Metamath.Provable A outer.untrim.ctx (ax.fmla.subst σ) := by
  let forbidden := applicationForbidden outer ax σ
  let τ := completionSubst outer ax σ
  have hτ_dj : ax.untrim.ctx.dj.subst τ outer.untrim.ctx.dj := by
    intro x y hxy a b ha hb
    by_cases hx : x ∈ ax.vars
    · simp only [τ, completionSubst, hx, if_pos] at ha
      by_cases hy : y ∈ ax.vars
      · simp only [τ, completionSubst, hy, if_pos] at hb
        exact hdj x y (hxy.2 hx hy) a b ha hb
      · simp only [τ, completionSubst, hy] at hb
        change Metamath.Sym.var b ∈
          [Metamath.Sym.var (freshVR forbidden y)] at hb
        simp only [List.mem_singleton, Metamath.Sym.var.injEq] at hb
        subst b
        have ha_forbidden : a ∈ forbidden :=
          image_var_mem_applicationForbidden outer ax σ hx ha
        have h_ne : a ≠ freshVR forbidden y := by
          intro h_eq
          rw [h_eq] at ha_forbidden
          exact freshVR_not_mem forbidden y ha_forbidden
        refine ⟨h_ne, ?_⟩
        intro _ha_outer hb_outer
        exact (freshVR_not_mem forbidden y
          (outer_var_mem_applicationForbidden outer ax σ hb_outer)).elim
    · simp only [τ, completionSubst, hx] at ha
      change Metamath.Sym.var a ∈
        [Metamath.Sym.var (freshVR forbidden x)] at ha
      simp only [List.mem_singleton, Metamath.Sym.var.injEq] at ha
      subst a
      by_cases hy : y ∈ ax.vars
      · simp only [τ, completionSubst, hy, if_pos] at hb
        have hb_forbidden : b ∈ forbidden :=
          image_var_mem_applicationForbidden outer ax σ hy hb
        have h_ne : freshVR forbidden x ≠ b := by
          intro h_eq
          rw [← h_eq] at hb_forbidden
          exact freshVR_not_mem forbidden x hb_forbidden
        refine ⟨h_ne, ?_⟩
        intro ha_outer _hb_outer
        exact (freshVR_not_mem forbidden x
          (outer_var_mem_applicationForbidden outer ax σ ha_outer)).elim
      · simp only [τ, completionSubst, hy] at hb
        change Metamath.Sym.var b ∈
          [Metamath.Sym.var (freshVR forbidden y)] at hb
        simp only [List.mem_singleton, Metamath.Sym.var.injEq] at hb
        subst b
        have h_ne : freshVR forbidden x ≠ freshVR forbidden y := by
          intro h_eq
          exact hxy.1 (freshVR_injective forbidden h_eq)
        refine ⟨h_ne, ?_⟩
        intro ha_outer _hb_outer
        exact (freshVR_not_mem forbidden x
          (outer_var_mem_applicationForbidden outer ax σ ha_outer)).elim
  have hτ_hyps : ∀ h ∈ ax.untrim.ctx.hyps,
      Metamath.Provable A outer.untrim.ctx (h.subst τ) := by
    intro h hh
    have h_eq : h.subst τ = h.subst σ :=
      formula_subst_congr_on_vars h (fun v hv =>
        completionSubst_of_mem outer ax σ
          (hyp_vars_mem_statement ax hh hv))
    rw [h_eq]
    exact hhyps h hh
  have hτ_vars : ∀ v,
      Metamath.Provable A outer.untrim.ctx (v.type, τ v) := by
    intro v
    dsimp only [τ]
    by_cases hv : v ∈ ax.vars
    · rw [completionSubst_of_mem outer ax σ hv]
      exact hvars v hv
    · rw [completionSubst_of_not_mem outer ax σ hv]
      change Metamath.Provable A outer.untrim.ctx
        (freshVR (applicationForbidden outer ax σ) v).vhyp
      simpa [forbidden] using
        (Metamath.Provable.var (axs := A) (Γ := outer.untrim.ctx)
          (freshVR forbidden v))
  have h_use := Metamath.Provable.trans' τ hs hτ_dj hτ_hyps hτ_vars
  change Metamath.Provable A outer.untrim.ctx (ax.fmla.subst τ) at h_use
  have h_eq : ax.fmla.subst τ = ax.fmla.subst σ :=
    formula_subst_congr_on_vars ax.fmla (fun v hv =>
      completionSubst_of_mem outer ax σ (fmla_vars_mem_statement ax hv))
  rw [h_eq] at h_use
  exact h_use

/-- Derived-rule elimination inside an untrimmed ambient statement context. -/
theorem replaceDerivedAxioms_in_untrim
    {A B : Metamath.Statement → Prop} {outer : Metamath.Statement}
    {f : Metamath.Formula}
    (h : Metamath.Provable B outer.untrim.ctx f)
    (hB : ∀ a, B a → a.Provable A) :
    Metamath.Provable A outer.untrim.ctx f := by
  induction h with
  | hyp f hf => exact .hyp f hf
  | var v => exact .var v
  | @ax σ ax hax hdj hhyps hvars ihyps ivars =>
      exact useProvedStatement (outer := outer) (hB ax hax) σ hdj
        (fun f hf => ihyps f hf) (fun v hv => ivars v hv)

/-- Cut for stored Metamath statements: if every rule of `B` has already been
proved from `A`, every stored statement proved from `B` is proved from `A`. -/
theorem replaceDerivedAxioms
    {A B : Metamath.Statement → Prop} {s : Metamath.Statement}
    (h : s.Provable B) (hB : ∀ a, B a → a.Provable A) :
    s.Provable A :=
  replaceDerivedAxioms_in_untrim h hB

theorem statementProvable_mono_axioms
    {A B : Metamath.Statement → Prop} {s : Metamath.Statement}
    (hAB : ∀ a, A a → B a) (h : s.Provable A) : s.Provable B :=
  Metamath.Provable.mono hAB (Metamath.Context.refl _) h

/-- A member of an axiom predicate proves itself as a stored statement.
The variable leaves are supplied by `Provable.var`; no well-formedness
assumption is needed for this declarative direction. -/
theorem sourceAxiom_self_provable
    {A : Metamath.Statement → Prop} {a : Metamath.Statement} (ha : A a) :
    a.Provable A := by
  apply Metamath.Statement.Provable'.of
  have h := Metamath.Provable.ax (Γ := a.ctx) Metamath.VR.expr ha
    ?disj ?hyp ?var
  rw [Metamath.Formula.subst_id] at h
  exact h
  case disj =>
    intro x y hxy x' y' hx hy
    match x', y', hx, hy with
    | _, _, .head _, .head _ => exact hxy
  case hyp =>
    intro f hf
    rw [Metamath.Formula.subst_id]
    exact .hyp f hf
  case var =>
    intro v _
    show Metamath.Provable A a.ctx (v.type, Metamath.VR.expr v)
    exact .var v

end Semantic

namespace Runtime

open Semantic
open PrefixWitnessCheckBytes

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
    Semantic.FrameReduction source target e := by
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
    typesAgree := Semantic.frameMapTypesAgree_of_hyps_subset
      h_source_wf.1 h_hyp_subset
    domainLE := Semantic.frameMapDomainLE_of_hyps_subset h_hyp_subset
    conclusionRetained := Semantic.exprVarsRetained_of_scopes
      h_source_disjoint h_target_scope.1
    essentialRetained := ?_
    dvRetained := ?_ }
  · intro e_hyp h_essential
    have h_essential_target := essential_mem_target_of_trim db fmla targetImpl
      source target h_wf h_trim h_source h_target h_essential
    refine ⟨h_essential_target, ?_⟩
    exact Semantic.exprVarsRetained_of_scopes h_source_disjoint
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
      (Semantic.statementOfFrame target (Kernel.toExpr pr.fmla)).Provable
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
  have h_reduction : Semantic.FrameReduction source target
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
    exact proofValid_to_mario h_prefix_basic h_source_disjoint h_valid
  exact ⟨target, h_target_final,
    Semantic.statementProvable_of_frameReduction h_reduction h_active_semantic⟩

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
    stmt = Semantic.statementOfFrame target (Kernel.toExpr f)

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
a local `$a` finish event or its exact stored declarative statement is
proved by the written `$p` proof.  The theorem proof is transported from the
pre-insertion database into the returned database; it is not obtained by
self-citation. -/
theorem checkSinglePass_storedStatements_writtenProof
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
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
        ∨ (∃ target : Spec.Frame,
            Kernel.toFrame db fr = some target ∧
            (Semantic.statementOfFrame target (Kernel.toExpr f)).Provable
              (dbToAxioms Γ)) := by
  have h_final :=
    checkSinglePass_database_wellFormed_strong fname config h_cfg w w' db
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
    checkSinglePass_registry_chronology_exactly_one fname config h_cfg w w'
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
      h_lbl, _h_fresh, _h_insert, h_prefix_db, h_source, h_prefix_provable⟩ :=
        h_theorem
    have h_trim : (steps[idx]!).state.db.trimFrame' pr.fmla = .ok pr.frame :=
      finishProofEvent_trimFrame (steps[idx]!).state (steps[idx]!).pos
        (steps[idx]!).tk pr h_ghost h_event
    have h_target_impl_wf :
        WF.WellFormedFrame (steps[idx]!).state.db pr.frame :=
      ParserOps.trimFrame'_success_implies_wellformed_frame
        (steps[idx]!).state.db pr.fmla pr.frame h_inv.1 h_trim
    obtain ⟨target, h_target_prefix⟩ :=
      Kernel.toFrame_some_of_wfFrame_any (steps[idx]!).state.db pr.frame
        h_target_impl_wf
    have h_target_final : Kernel.toFrame db pr.frame = some target :=
      toFrame_stable_of_find_mono (steps[idx]!).state.db db pr.frame target
        h_mono h_target_prefix
    have h_find_final' : db.find? n = some (.assert pr.fmla pr.frame n) := by
      simpa [h_label, h_fmla, h_frame, h_lbl] using h_find_final
    have h_formula_wf : WF.WellFormedFormula pr.fmla :=
      WF.assert_formula_wf_of_db h_final_wf h_find_final'
    have h_expr_opt : Kernel.toExprOpt pr.fmla = some (Kernel.toExpr pr.fmla) :=
      (Kernel.toExprOpt_some_iff_toExpr pr.fmla (Kernel.toExpr pr.fmla)).2
        ⟨h_formula_wf.1, rfl⟩
    have h_lookup_final :
        Γ n = some (target, Kernel.toExpr pr.fmla) := by
      unfold Kernel.toDatabase at h_final_db
      injection h_final_db with h_Γ
      rw [← h_Γ]
      simp [Kernel.toDatabaseTotal, h_find_final', h_target_final, h_expr_opt]
    have h_target_scope :
        Spec.FrameExprsInScope (Kernel.toConsts db) target
          (Kernel.toExpr pr.fmla) :=
      h_strong.1.1 n target (Kernel.toExpr pr.fmla) h_lookup_final
    have h_source_disjoint :
        Spec.FrameVarsDisjointConsts (Kernel.toConsts db) source :=
      frameVarsDisjointConsts_of_find_mono (steps[idx]!).state.db db
        (steps[idx]!).state.db.frame source h_source h_inv.1.1
        h_inv.2.1.1 h_mono
    have h_reduction : Semantic.FrameReduction source target
        (Kernel.toExpr pr.fmla) :=
      frameReduction_of_trim (steps[idx]!).state.db pr.fmla pr.frame
        source target (Kernel.toExpr pr.fmla) (Kernel.toConsts db)
        h_inv.1 h_trim h_source h_target_prefix h_source_disjoint h_target_scope
    have h_prefix_subset : Kernel.SpecDBSubset prefixΓ Γ :=
      toDatabase_subset_of_find_mono (steps[idx]!).state.db db h_inv.1
        h_mono prefixΓ Γ h_prefix_db h_final_db
    have h_prefix_provable' :
        Spec.Provable prefixΓ source (Kernel.toExpr pr.fmla) := by
      rw [h_fmla]
      exact h_prefix_provable
    have h_final_provable : Spec.Provable Γ source (Kernel.toExpr pr.fmla) :=
      Spec.Provable.mono_db h_prefix_subset h_prefix_provable'
    have h_exact := Semantic.statementProvable_of_operational_frameReduction
      h_strong h_source_disjoint h_reduction h_final_provable
    exact Or.inr ⟨target, by simpa [h_frame] using h_target_final,
      by simpa [h_fmla] using h_exact⟩

/-- **Trace-relative derived-rule elimination.** In an accepted certified run,
every stored `$p` statement is declaratively provable using only `$a`-classified
events in the emitted registry chronology.  Earlier `$p` statements are
eliminated by cut along strict creation order, and the local written proof is
interpreted against its pre-insertion database, so it cannot use self-citation.

The theorem deliberately inherits `RunTrace`'s boundary: registry seams do not
certify that every recorded parser state is a state of the concrete IO run. -/
theorem checkSinglePass_every_theorem_provable_from_trace_axiom_events
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
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
                (Semantic.statementOfFrame target (Kernel.toExpr f)))
            ∨ (∃ pr : ProofState,
              FinishProofEvent (steps[idx]!).state (steps[idx]!).pos
                (steps[idx]!).tk pr ∧
              pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
              (Semantic.statementOfFrame target (Kernel.toExpr f)).Provable
                (AxiomEventOfTrace steps Γ))) := by
  have h_final :=
    checkSinglePass_database_wellFormed_strong fname config h_cfg w w' db
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
    checkSinglePass_registry_chronology_exactly_one fname config h_cfg w w'
      db h_run h_success
  let A := AxiomEventOfTrace steps Γ
  have h_created : ∀ idx : Nat, idx < steps.length →
      ∀ n f fr lbl,
        db.find? n = some (.assert f fr lbl) →
        CreatesEntry (steps[idx]!) n (.assert f fr lbl) →
        ∃ target : Spec.Frame,
          Kernel.toFrame db fr = some target ∧
          Γ n = some (target, Kernel.toExpr f) ∧
          (A (Semantic.statementOfFrame target (Kernel.toExpr f)) ∨
            (Semantic.statementOfFrame target (Kernel.toExpr f)).Provable A) := by
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
          (Semantic.statementOfFrame target (Kernel.toExpr f))
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
            (Semantic.statementOfFrame storedTarget
              (Kernel.toExpr pr.fmla)).Provable A := by
          apply Semantic.replaceDerivedAxioms h_prefix_exact
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
              a = Semantic.statementOfFrame target₀ (Kernel.toExpr f₀) := by
            rw [h_target_eq, h_toExpr]
            cases a with
            | mk actx afmla =>
                dsimp only at h_ctx h_afmla ⊢
                unfold Semantic.statementOfFrame
                rw [h_ctx, h_afmla]
          rw [h_stmt_eq]
          rcases h_old with h_ax | h_th
          · exact Semantic.sourceAxiom_self_provable h_ax
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
      (Semantic.statementOfFrame target (Kernel.toExpr f))
    exact ⟨idx, n, f, fr, lbl, target, arr, p, h_idx, h_creates,
      h_event, h_label, h_fmla, h_lbl, h_lookup, rfl⟩
  · obtain ⟨pr, _prefixΓ, _source, h_event, h_label, h_fmla, h_frame,
      h_lbl, _h_fresh, _h_insert, _h_prefix_db, _h_source,
      _h_prefix_provable⟩ := h_theorem
    apply Or.inr
    refine ⟨pr, h_event, h_label, h_fmla, h_frame, h_lbl, ?_⟩
    rcases h_result with h_ax | h_th
    · exact Semantic.sourceAxiom_self_provable h_ax
    · exact h_th

end Runtime
end Metamath.StoredStatementSoundness
