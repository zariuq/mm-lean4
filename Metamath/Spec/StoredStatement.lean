import Metamath.Spec.Equivalence

/-!
# Stored statements

A database stores each assertion with its trimmed mandatory frame, while a
proof is checked in the full active frame, where proof-local dummy variables
can occur. This module relates the two levels through Mario Carneiro's
`Statement.untrim`:

- `statementOfFrame fr e` is the declarative statement denoted by a frame and
  an expression;
- `FrameReduction source target e` is the relation that frame trimming
  establishes between an active frame and its trimmed frame;
- `statementProvable_of_frameReduction` turns a derivation in the active frame
  into provability of the stored statement;
- `replaceDerivedAxioms` eliminates earlier derived statements from an axiom
  set.
-/


set_option autoImplicit false

namespace Metamath.Spec.StoredStatement

open Metamath.Spec.Equivalence


/-- The declarative statement denoted by an operational frame and expression. -/
noncomputable def statementOfFrame (fr : Spec.Frame) (e : Spec.Expr) : Metamath.Statement :=
  ⟨frameToContext fr, exprToFormula (varMapOfFrame fr) e⟩

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

theorem toDeclarativeSym_subst_reindex
    {source target : Spec.Frame} {s : String}
    (h_back : ∀ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR →
      ∃ sourceVR, findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR)
    (h_keep : ∀ sourceVR,
      findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR →
      ∃ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR) :
    (match toDeclarativeSym (varMapOfFrame source) s with
      | Metamath.Sym.const c => [Metamath.Sym.const c]
      | Metamath.Sym.var vr => renameSubst (reindexVR source target) vr) =
      [toDeclarativeSym (varMapOfFrame target) s] := by
  unfold toDeclarativeSym
  cases h_source : findVR (varMapOfFrame source) ⟨s⟩ with
  | none =>
      cases h_target : findVR (varMapOfFrame target) ⟨s⟩ with
      | none => simp [h_source, h_target]
      | some targetVR =>
          obtain ⟨sourceVR, h_source'⟩ := h_back targetVR h_target
          rw [h_source] at h_source'
          cases h_source'
  | some sourceVR =>
      obtain ⟨targetVR, h_target⟩ := h_keep sourceVR h_source
      simp [h_source, h_target, renameSubst,
        reindexVR_of_findVR h_source h_target]

/-- Reindexing an expression: its source variables are target variables (`h_keep`), and its
symbols that are target variables are source variables (`h_back`). -/
theorem exprToDeclarativeExpr_subst_reindex_of_syms
    {source target : Spec.Frame} {e : Spec.Expr}
    (h_back : ∀ s ∈ e.syms, ∀ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR →
      ∃ sourceVR, findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR)
    (h_keep : ExprVarsRetained source target e) :
    (exprToDeclarativeExpr (varMapOfFrame source) e).subst
        (renameSubst (reindexVR source target)) =
      exprToDeclarativeExpr (varMapOfFrame target) e := by
  unfold exprToDeclarativeExpr
  have go : ∀ xs : List String,
      (∀ s, s ∈ xs → ∀ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR →
        ∃ sourceVR, findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR) →
      (∀ s, s ∈ xs → ∀ sourceVR,
        findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR →
        ∃ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR) →
      Metamath.Expr.subst (renameSubst (reindexVR source target))
          (xs.map (toDeclarativeSym (varMapOfFrame source))) =
        xs.map (toDeclarativeSym (varMapOfFrame target)) := by
    intro xs h_bs h_xs
    induction xs with
    | nil => rfl
    | cons s rest ih =>
        have h_head := toDeclarativeSym_subst_reindex (source := source)
          (target := target) (s := s)
          (fun targetVR h_target => h_bs s (by simp) targetVR h_target)
          (fun sourceVR h_source => h_xs s (by simp) sourceVR h_source)
        have h_tail := ih (fun s' h_mem targetVR h_target =>
          h_bs s' (by simp [h_mem]) targetVR h_target)
          (fun s' h_mem sourceVR h_source =>
          h_xs s' (by simp [h_mem]) sourceVR h_source)
        cases h_sym : toDeclarativeSym (varMapOfFrame source) s with
        | const c =>
            have h_sym_eq :
                Metamath.Sym.const c = toDeclarativeSym (varMapOfFrame target) s := by
              simpa [h_sym] using h_head
            calc
              Metamath.Expr.subst (renameSubst (reindexVR source target))
                    (toDeclarativeSym (varMapOfFrame source) s ::
                      rest.map (toDeclarativeSym (varMapOfFrame source))) =
                  Metamath.Sym.const c ::
                    Metamath.Expr.subst (renameSubst (reindexVR source target))
                      (rest.map (toDeclarativeSym (varMapOfFrame source))) := by
                    rw [h_sym]
                    rfl
              _ = Metamath.Sym.const c ::
                    rest.map (toDeclarativeSym (varMapOfFrame target)) :=
                  congrArg (Metamath.Sym.const c :: ·) h_tail
              _ = toDeclarativeSym (varMapOfFrame target) s ::
                    rest.map (toDeclarativeSym (varMapOfFrame target)) := by
                  rw [h_sym_eq]
        | var vr =>
            have h_sym_eq :
                Metamath.Sym.var (reindexVR source target vr) =
                  toDeclarativeSym (varMapOfFrame target) s := by
              simpa [h_sym, renameSubst] using h_head
            calc
              Metamath.Expr.subst (renameSubst (reindexVR source target))
                    (toDeclarativeSym (varMapOfFrame source) s ::
                      rest.map (toDeclarativeSym (varMapOfFrame source))) =
                  Metamath.Sym.var (reindexVR source target vr) ::
                    Metamath.Expr.subst (renameSubst (reindexVR source target))
                      (rest.map (toDeclarativeSym (varMapOfFrame source))) := by
                    rw [h_sym]
                    rfl
              _ = Metamath.Sym.var (reindexVR source target vr) ::
                    rest.map (toDeclarativeSym (varMapOfFrame target)) := by
                  rw [h_tail]
              _ = toDeclarativeSym (varMapOfFrame target) s ::
                    rest.map (toDeclarativeSym (varMapOfFrame target)) := by
                  rw [h_sym_eq]
  exact go e.syms h_back h_keep

theorem exprToDeclarativeExpr_subst_reindex
    {source target : Spec.Frame} (h_dom : FrameMapDomainLE source target)
    {e : Spec.Expr} (h_keep : ExprVarsRetained source target e) :
    (exprToDeclarativeExpr (varMapOfFrame source) e).subst
        (renameSubst (reindexVR source target)) =
      exprToDeclarativeExpr (varMapOfFrame target) e :=
  exprToDeclarativeExpr_subst_reindex_of_syms (fun s _ => h_dom ⟨s⟩) h_keep

theorem exprToFormula_subst_reindex_of_syms
    {source target : Spec.Frame} {e : Spec.Expr}
    (h_back : ∀ s ∈ e.syms, ∀ targetVR, findVR (varMapOfFrame target) ⟨s⟩ = some targetVR →
      ∃ sourceVR, findVR (varMapOfFrame source) ⟨s⟩ = some sourceVR)
    (h_keep : ExprVarsRetained source target e) :
    (exprToFormula (varMapOfFrame source) e).subst
        (renameSubst (reindexVR source target)) =
      exprToFormula (varMapOfFrame target) e :=
  congrArg (fun xs => (e.typecode.c, xs)) (exprToDeclarativeExpr_subst_reindex_of_syms h_back h_keep)

theorem exprToFormula_subst_reindex
    {source target : Spec.Frame} (h_dom : FrameMapDomainLE source target)
    {e : Spec.Expr} (h_keep : ExprVarsRetained source target e) :
    (exprToFormula (varMapOfFrame source) e).subst
        (renameSubst (reindexVR source target)) =
      exprToFormula (varMapOfFrame target) e := by
  exact congrArg (fun xs => (e.typecode.c, xs))
    (exprToDeclarativeExpr_subst_reindex h_dom h_keep)

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
  · have h_expr : vr ∈' exprToDeclarativeExpr (varMapOfFrame fr) e :=
      Metamath.Expr.mem_vars_iff.mp h_vr
    obtain ⟨s, _h_s, h_find⟩ := exprToDeclarativeExpr_mem_extract h_expr
    exact findVR_index_lt_floatList h_find
  · unfold frameToContext at h_f
    obtain ⟨hyp, h_hyp, rfl⟩ := List.mem_map.mp h_f
    cases hyp with
    | essential e_hyp =>
        have h_expr : vr ∈' exprToDeclarativeExpr (varMapOfFrame fr) e_hyp :=
          Metamath.Expr.mem_vars_iff.mp h_vr
        obtain ⟨s, _h_s, h_find⟩ := exprToDeclarativeExpr_mem_extract h_expr
        exact findVR_index_lt_floatList h_find
    | floating c v =>
        obtain ⟨vr', h_find⟩ := findVR_of_float
          (fr := fr) (c := c) (v := v) h_hyp
        unfold hypToDeclarativeFormula at h_vr
        simp only [h_find, Metamath.Expr.vars, List.mem_singleton] at h_vr
        subst h_vr
        exact findVR_index_lt_floatList h_find

/-- Disjoint variables in a converted context came from two source variables
that the frame map can recover. -/
theorem dvListToDeclarativeDJ_findVars
    {fr : Spec.Frame} {a b : Metamath.VR}
    (h_dj : (dvListToDeclarativeDJ (varMapOfFrame fr) fr.dv) a b) :
    ∃ v w,
      findVar (varMapOfFrame fr) a = some v ∧
      findVar (varMapOfFrame fr) b = some w := by
  unfold dvListToDeclarativeDJ at h_dj
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
  obtain ⟨v, w, h_a, h_b⟩ := dvListToDeclarativeDJ_findVars h_ab
  have h_source_rel : Spec.dvRel source.dv v w :=
    dvListToDeclarativeDJ_to_dvRel h_ab h_a h_b
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
          apply dvRel_to_dvListToDeclarativeDJ
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
      rw [h_eq, hypToDeclarativeFormula_essential]
      rw [exprToFormula_subst_reindex h_red.domainLE h_keep]
      exact Metamath.Provable.hyp _
        (hypToDeclarativeFormula_mem h_hyp_target)
  | floating c v =>
      obtain ⟨sourceVR, h_sourceVR, h_source_type⟩ :=
        findVR_of_float_typed h_red.sourceWellFormed.1 h_hyp_source
      have h_reindex_type := reindexVR_type h_red.sourceWellFormed.2
        h_red.typesAgree sourceVR
      rw [h_eq]
      unfold hypToDeclarativeFormula
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
  exact operational_to_declarative h_strong h_source_disjoint h_active

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
  exact List.mem_flatMap.mpr ⟨v, hv, Metamath.Expr.mem_vars_iff.mpr hw⟩

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
      Metamath.Formula.subst_congr (fun v hv =>
        completionSubst_of_mem outer ax σ (ax.mem_vars_of_hyp hh hv))
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
    Metamath.Formula.subst_congr (fun v hv =>
      completionSubst_of_mem outer ax σ (ax.mem_vars_of_fmla hv))
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

end Metamath.Spec.StoredStatement
