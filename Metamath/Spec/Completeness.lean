import Metamath.Spec.DummyExtension
import Metamath.Spec.DeclarativeOriginal

/-!
# Completeness of Metamath proofs for the declarative semantics

Mario Carneiro's declarative semantics judges a stored statement in its
`untrim` context: the variables of the statement keep the frame's `$d`
restrictions, and every other variable is available, typed, and disjoint from
all others. A Metamath proof may only use variables with an active `$f`
hypothesis. The two agree once the frame is extended by dummy variables, as the
extended frames of the Metamath book (§4.2.7) allow:

- `statementProvable_iff_exists_extendDummies`: a stored statement is
  declaratively provable iff its conclusion is derivable from `$f`-typed
  variables only in the frame extended by fresh dummy variables, each disjoint
  from every other variable.
- `statementProvable_iff_exists_extendedFrame`: a stored statement is
  declaratively provable iff some extended frame has a Metamath proof of it.
- `exists_extendDummies_of_statementProvable`: the dummy variables can extend
  any given extended frame, such as the active frame of a proof.
- `originalStatementProvable_iff_exists_extendedFrame`: the same for Mario
  Carneiro's original `ax` rule (`Metamath.Spec.DeclarativeOriginal`).

At one fixed frame the two notions differ: a proof may need more dummy
variables than the frame declares (`Metamath.Spec.FixedFrameCounterexample`).
-/

namespace Metamath.Spec.Completeness

open Metamath.Spec.Equivalence
open Metamath.Spec.DummyExtension
open Metamath.Spec.StoredStatement

/-! ## Dummy extensions -/

/-- Trimming the dummies of `extendDummies fr ds` gives back `fr`. -/
theorem frameReduction_extendDummies {fr : Frame} {ds : List (Constant × Variable)} {e : Expr}
    (hfr : FrameWellFormed fr) (hfresh : DummyFresh fr ds)
    (hconcl : ∀ p ∈ ds, p.2.v ∉ e.syms) :
    FrameReduction (extendDummies fr ds) fr e where
  sourceWellFormed := frameWellFormed_extendDummies hfr hfresh
  targetWellFormed := hfr
  typesAgree := frameMapTypesAgree_of_hyps_subset (frameWellFormed_extendDummies hfr hfresh).1
    fun _ hh => List.mem_append_left _ hh
  domainLE := frameMapDomainLE_of_hyps_subset fun _ hh => List.mem_append_left _ hh
  conclusionRetained := by
    intro s hs sourceVR hsource
    have hnot : (⟨s⟩ : Variable) ∉ ds.map Prod.snd := by
      intro hd
      obtain ⟨p, hp, hps⟩ := List.mem_map.mp hd
      exact hconcl p hp (by rw [hps]; exact hs)
    rw [findVR_extendDummies (Or.inr hnot)] at hsource
    exact ⟨sourceVR, hsource⟩
  essentialRetained := by
    intro eh heh
    have heh' : Hyp.essential eh ∈ fr.hyps := by
      rcases List.mem_append.mp heh with h | h
      · exact h
      · obtain ⟨_, _, hp⟩ := List.mem_map.mp h
        cases hp
    refine ⟨heh', ?_⟩
    intro s hs sourceVR hsource
    have hnot : (⟨s⟩ : Variable) ∉ ds.map Prod.snd := by
      intro hd
      obtain ⟨p, hp, hps⟩ := List.mem_map.mp hd
      exact hfresh.not_essential p hp eh heh' (by rw [hps]; exact hs)
    rw [findVR_extendDummies (Or.inr hnot)] at hsource
    exact ⟨sourceVR, hsource⟩
  dvRetained := by
    intro v w hvw hv hw
    obtain ⟨hne, hmem⟩ := hvw
    have hvd : v ∈ fr.vars := (varMapDomain_ofFrame fr v).mpr hv
    have hwd : w ∈ fr.vars := (varMapDomain_ofFrame fr w).mpr hw
    refine ⟨hne, ?_⟩
    rcases hmem with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · obtain ⟨hd, _⟩ := mem_dummyDV h
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
        exact absurd hvd (hfresh.not_var p hp)
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr h
      · obtain ⟨hd, _⟩ := mem_dummyDV h
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
        exact absurd hwd (hfresh.not_var p hp)

/-- **Completeness at the frame level.** A declaratively provable stored
statement is derivable, from `$f`-typed variables only, in its frame extended
by fresh dummy variables. The dummies avoid `avoid`, and each has the
conclusion's typecode or a premise typecode of the database. -/
theorem statementProvable_to_extendDummies {Γ : Database} {fr : Frame} {e : Expr}
    (avoid : List String) (hfr : FrameWellFormed fr)
    (h : (statementOfFrame fr e).Provable (dbToAxioms Γ)) :
    ∃ ds, DummyFresh fr ds ∧ (∀ p ∈ ds, p.2.v ∉ e.syms) ∧ (∀ p ∈ ds, p.2.v ∉ avoid) ∧
      (∀ p ∈ ds, p.1.c = e.typecode.c ∨ Metamath.PremiseTypecode (dbToAxioms Γ) p.1.c) ∧
      FrameDerivable Γ (extendDummies fr ds)
        (exprToFormula (varMapOfFrame (extendDummies fr ds)) e) :=
  let ⟨ds, h1, h2, h3, h4, _, h5⟩ := exists_dummies_of_statementProvable hfr hfr (fun _ h => h)
    (fun _ h => h) (fun _ _ h => h) (fun _ _ _ _ h => h) avoid h
  ⟨ds, h1, h2, h3, h4, h5⟩

/-- **Soundness at the frame level.** A derivation in the frame extended by
fresh dummy variables proves the stored statement declaratively. -/
theorem extendDummies_to_statementProvable {Γ : Database} {fr : Frame} {e : Expr}
    {ds : List (Constant × Variable)} (hfr : FrameWellFormed fr) (hfresh : DummyFresh fr ds)
    (hconcl : ∀ p ∈ ds, p.2.v ∉ e.syms)
    (h : FrameDerivable Γ (extendDummies fr ds)
      (exprToFormula (varMapOfFrame (extendDummies fr ds)) e)) :
    (statementOfFrame fr e).Provable (dbToAxioms Γ) :=
  statementProvable_of_frameReduction (frameReduction_extendDummies hfr hfresh hconcl)
    h.toDeclarative

/-- A stored statement is declaratively provable iff its conclusion is
derivable from `$f`-typed variables only in the frame extended by fresh dummy
variables. -/
theorem statementProvable_iff_exists_extendDummies {Γ : Database} {fr : Frame} {e : Expr}
    (hfr : FrameWellFormed fr) :
    (statementOfFrame fr e).Provable (dbToAxioms Γ) ↔
      ∃ ds, DummyFresh fr ds ∧ (∀ p ∈ ds, p.2.v ∉ e.syms) ∧
        FrameDerivable Γ (extendDummies fr ds)
          (exprToFormula (varMapOfFrame (extendDummies fr ds)) e) := by
  constructor
  · intro h
    obtain ⟨ds, hfresh, hconcl, _, _, hderiv⟩ := statementProvable_to_extendDummies [] hfr h
    exact ⟨ds, hfresh, hconcl, hderiv⟩
  · rintro ⟨ds, hfresh, hconcl, hderiv⟩
    exact extendDummies_to_statementProvable hfr hfresh hconcl hderiv

/-! ## Extended frames -/

/-- `fr'` is an extended frame of `fr` (Metamath book §4.2.7), as a relation
on frames: `fr'` contains the hypotheses and `$d` pairs of `fr`, every other
hypothesis of `fr'` is a `$f` hypothesis for an optional variable (one that is
not a variable of `fr` and not a constant), every other `$d` pair of `fr'` has
an optional variable, and no variable has two `$f` hypotheses. The optional
`$f` hypotheses may use any typecode and their order is not recorded: declared
typecodes and the book's source order (§4.2.7, property 3) are conditions on
source text, not on the declarative statement. -/
structure ExtendedFrame (consts : ConstSet) (fr fr' : Frame) : Prop where
  wellFormed : FrameWellFormed fr'
  hyps_mem : ∀ h ∈ fr.hyps, h ∈ fr'.hyps
  optional_hyp : ∀ h ∈ fr'.hyps, h ∉ fr.hyps →
    ∃ c v, h = Hyp.floating c v ∧ v ∉ fr.vars ∧ ¬ consts v.v
  dv_mem : ∀ p ∈ fr.dv, p ∈ fr'.dv
  optional_dv : ∀ p ∈ fr'.dv, p ∉ fr.dv → p.1 ∉ fr.vars ∨ p.2 ∉ fr.vars

theorem ExtendedFrame.varsDisjointConsts {consts : ConstSet} {fr fr' : Frame}
    (hext : ExtendedFrame consts fr fr') (hdc : FrameVarsDisjointConsts consts fr) :
    FrameVarsDisjointConsts consts fr' := by
  intro v hv
  obtain ⟨c, hc⟩ := var_mem_iff_float.mp hv
  by_cases hin : Hyp.floating c v ∈ fr.hyps
  · exact hdc v (var_mem_iff_float.mpr ⟨c, hin⟩)
  · obtain ⟨_, _, heq, _, hnc⟩ := hext.optional_hyp _ hc hin
    injection heq with _ hv'
    rw [hv']
    exact hnc

/-- Removing the optional statements of an extended frame is the trimming of
`FrameReduction`. -/
theorem ExtendedFrame.frameReduction {consts : ConstSet} {fr fr' : Frame} {e : Expr}
    (hext : ExtendedFrame consts fr fr') (hfr : FrameWellFormed fr)
    (hdc : FrameVarsDisjointConsts consts fr) (hscope : FrameExprsInScope consts fr e) :
    FrameReduction fr' fr e where
  sourceWellFormed := hext.wellFormed
  targetWellFormed := hfr
  typesAgree := frameMapTypesAgree_of_hyps_subset hext.wellFormed.1 hext.hyps_mem
  domainLE := frameMapDomainLE_of_hyps_subset hext.hyps_mem
  conclusionRetained := exprVarsRetained_of_scopes (hext.varsDisjointConsts hdc) hscope.1
  essentialRetained := by
    intro eh heh
    have heh' : Hyp.essential eh ∈ fr.hyps := by
      by_cases hin : Hyp.essential eh ∈ fr.hyps
      · exact hin
      · obtain ⟨_, _, heq, _, _⟩ := hext.optional_hyp _ heh hin
        cases heq
    exact ⟨heh', exprVarsRetained_of_scopes (hext.varsDisjointConsts hdc)
      (hscope.2 (Hyp.essential eh) heh')⟩
  dvRetained := by
    intro v w hvw hv hw
    obtain ⟨hne, hmem⟩ := hvw
    have hvd : v ∈ fr.vars := (varMapDomain_ofFrame fr v).mpr hv
    have hwd : w ∈ fr.vars := (varMapDomain_ofFrame fr w).mpr hw
    refine ⟨hne, ?_⟩
    rcases hmem with h | h
    · by_cases hin : (v, w) ∈ fr.dv
      · exact Or.inl hin
      · rcases hext.optional_dv _ h hin with h1 | h1
        · exact absurd hvd h1
        · exact absurd hwd h1
    · by_cases hin : (w, v) ∈ fr.dv
      · exact Or.inr hin
      · rcases hext.optional_dv _ h hin with h1 | h1
        · exact absurd hwd h1
        · exact absurd hvd h1

theorem ExtendedFrame.refl {consts : ConstSet} {fr : Frame} (hfr : FrameWellFormed fr) :
    ExtendedFrame consts fr fr where
  wellFormed := hfr
  hyps_mem := fun _ h => h
  optional_hyp := fun _ h hn => absurd h hn
  dv_mem := fun _ h => h
  optional_dv := fun _ h hn => absurd h hn

/-- Fresh dummy variables that are not constants extend an extended frame to an
extended frame. -/
theorem ExtendedFrame.extendDummies {consts : ConstSet} {fr frAct : Frame}
    {ds : List (Constant × Variable)} (hext : ExtendedFrame consts fr frAct)
    (hfresh : DummyFresh frAct ds) (hnc : ∀ p ∈ ds, ¬ consts p.2.v) :
    ExtendedFrame consts fr (extendDummies frAct ds) where
  wellFormed := frameWellFormed_extendDummies hext.wellFormed hfresh
  hyps_mem := fun _ hh => List.mem_append_left _ (hext.hyps_mem _ hh)
  optional_hyp := by
    intro h hh hnot
    rcases List.mem_append.mp hh with h' | h'
    · exact hext.optional_hyp h h' hnot
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h'
      exact ⟨p.1, p.2, rfl,
        fun hv => hfresh.not_var p hp (vars_subset_of_hyps_subset hext.hyps_mem hv), hnc p hp⟩
  dv_mem := fun _ hp => List.mem_append_left _ (hext.dv_mem _ hp)
  optional_dv := by
    intro p hp hnot
    rcases List.mem_append.mp hp with h' | h'
    · exact hext.optional_dv p h' hnot
    · rcases p with ⟨d, w⟩
      obtain ⟨hd, _⟩ := mem_dummyDV h'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact Or.inl fun hv =>
        hfresh.not_var q hq (vars_subset_of_hyps_subset hext.hyps_mem hv)

/-- **Soundness for the declarative semantics.** A Metamath proof of `e` in an
extended frame of `fr` proves the stored statement `(fr, e)` declaratively. -/
theorem statementProvable_of_extendedFrame
    {Γ : Database} {consts : ConstSet} {fr fr' : Frame} {e : Expr}
    (hdb : WellFormedDatabaseStrong Γ consts)
    (hfr : FrameWellFormed fr) (hdc : FrameVarsDisjointConsts consts fr)
    (hscope : FrameExprsInScope consts fr e)
    (hext : ExtendedFrame consts fr fr') (hprov : Spec.Provable Γ fr' e) :
    (statementOfFrame fr e).Provable (dbToAxioms Γ) :=
  statementProvable_of_operational_frameReduction hdb (hext.varsDisjointConsts hdc)
    (hext.frameReduction hfr hdc hscope) hprov

/-- **Completeness for the declarative semantics.** Over a database with
finitely many constants, a declaratively provable stored statement `(fr, e)`
has a Metamath proof of `e` in some extended frame of `fr`. -/
theorem exists_extendedFrame_of_statementProvable
    {Γ : Database} {consts : ConstSet} {fr : Frame} {e : Expr}
    (hdb : WellFormedDatabaseStrong Γ consts)
    (hfin : ∃ L : List String, ∀ s, consts s → s ∈ L)
    (hfr : FrameWellFormed fr) (hdc : FrameVarsDisjointConsts consts fr)
    (h : (statementOfFrame fr e).Provable (dbToAxioms Γ)) :
    ∃ fr', ExtendedFrame consts fr fr' ∧ Spec.Provable Γ fr' e := by
  obtain ⟨L, hL⟩ := hfin
  obtain ⟨ds, hfresh, _, havoid, _, hderiv⟩ := statementProvable_to_extendDummies L hfr h
  have hext := (ExtendedFrame.refl (consts := consts) hfr).extendDummies hfresh
    fun p hp hc => havoid p hp (hL _ hc)
  exact ⟨_, hext,
    frameDerivable_to_proofValid hdb hext.wellFormed.2 (hext.varsDisjointConsts hdc) hderiv⟩

/-- **Completeness into a given extended frame.** Over a database with finitely
many constants, a declaratively provable stored statement `(fr, e)` has a
Metamath proof in any extended frame `frAct` of `fr` extended by fresh dummy
variables `ds`. The dummies avoid `avoid`, and each is typed by the conclusion's
typecode or by a typecode the database's assertions use in premises. -/
theorem exists_extendDummies_of_statementProvable
    {Γ : Database} {consts : ConstSet} {fr frAct : Frame} {e : Expr}
    (hdb : WellFormedDatabaseStrong Γ consts)
    (hfin : ∃ L : List String, ∀ s, consts s → s ∈ L)
    (hfr : FrameWellFormed fr) (hdc : FrameVarsDisjointConsts consts fr)
    (hscope : FrameExprsInScope consts fr e) (hext : ExtendedFrame consts fr frAct)
    (avoid : List String)
    (h : (statementOfFrame fr e).Provable (dbToAxioms Γ)) :
    ∃ ds, DummyFresh frAct ds ∧ (∀ p ∈ ds, p.2.v ∉ avoid) ∧
      (∀ p ∈ ds, p.1.c = e.typecode.c ∨ Metamath.PremiseTypecode (dbToAxioms Γ) p.1.c) ∧
      (∀ p ∈ ds, ∃ b i, p.2.v = dummyName b i) ∧
      ExtendedFrame consts fr (extendDummies frAct ds) ∧
      Spec.Provable Γ (extendDummies frAct ds) e := by
  obtain ⟨L, hL⟩ := hfin
  have hdcAct := hext.varsDisjointConsts hdc
  have hback : ∀ {e' : Expr}, ExprVarsInScope consts fr e' → ∀ s ∈ e'.syms,
      (⟨s⟩ : Variable) ∈ frAct.vars → (⟨s⟩ : Variable) ∈ fr.vars := by
    intro e' hsc s hs hAct
    rcases hsc s hs with h | h
    · exact h
    · exact absurd h (hdcAct _ hAct)
  obtain ⟨ds, hfresh, _, havoid, htypes, hnames, hderiv⟩ :=
    exists_dummies_of_statementProvable hfr hext.wellFormed hext.hyps_mem hext.dv_mem
      (hback hscope.1) (fun eh heh => hback (hscope.2 _ heh)) (L ++ avoid) h
  have hext' := hext.extendDummies hfresh
    fun p hp hc => havoid p hp (List.mem_append_left _ (hL _ hc))
  exact ⟨ds, hfresh, fun p hp hm => havoid p hp (List.mem_append_right _ hm), htypes, hnames, hext',
    frameDerivable_to_proofValid hdb hext'.wellFormed.2 (hext'.varsDisjointConsts hdc) hderiv⟩

/-- **Metamath proofs are complete for the declarative semantics.** Over a
well-formed database with finitely many constants, a stored statement is
declaratively provable iff some extended frame of it has a Metamath proof of
its conclusion. -/
theorem statementProvable_iff_exists_extendedFrame
    {Γ : Database} {consts : ConstSet} {fr : Frame} {e : Expr}
    (hdb : WellFormedDatabaseStrong Γ consts)
    (hfin : ∃ L : List String, ∀ s, consts s → s ∈ L)
    (hfr : FrameWellFormed fr) (hdc : FrameVarsDisjointConsts consts fr)
    (hscope : FrameExprsInScope consts fr e) :
    (statementOfFrame fr e).Provable (dbToAxioms Γ) ↔
      ∃ fr', ExtendedFrame consts fr fr' ∧ Spec.Provable Γ fr' e :=
  ⟨exists_extendedFrame_of_statementProvable hdb hfin hfr hdc,
    fun ⟨_, hext, hprov⟩ => statementProvable_of_extendedFrame hdb hfr hdc hscope hext hprov⟩

/-- `statementProvable_iff_exists_extendedFrame` for Mario Carneiro's original
`ax` rule. -/
theorem originalStatementProvable_iff_exists_extendedFrame
    {Γ : Database} {consts : ConstSet} {fr : Frame} {e : Expr}
    (hdb : WellFormedDatabaseStrong Γ consts)
    (hfin : ∃ L : List String, ∀ s, consts s → s ∈ L)
    (hfr : FrameWellFormed fr) (hdc : FrameVarsDisjointConsts consts fr)
    (hscope : FrameExprsInScope consts fr e) :
    DeclarativeOriginal.StatementProvable (dbToAxioms Γ) (statementOfFrame fr e) ↔
      ∃ fr', ExtendedFrame consts fr fr' ∧ Spec.Provable Γ fr' e :=
  (DeclarativeOriginal.statementProvable_iff fun _ hax => dbToAxioms_trimmed hax).trans
    (statementProvable_iff_exists_extendedFrame hdb hfin hfr hdc hscope)

end Metamath.Spec.Completeness
