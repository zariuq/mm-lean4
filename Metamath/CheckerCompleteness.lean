import Metamath.CheckerCompleteness.Frames
import Metamath.CheckerCompleteness.Exact
import Metamath.AssertDvInvariant

/-!
# Checker acceptance and Mario Carneiro's declarative semantics

At a parser state between statements, a `$p` statement with claim `f` stores the statement
`statementOfFrame fr (toExpr f)`, where `fr` is the frame that trimming computes for `f`.

`acceptedWithDummies_iff_statementProvable`: that stored statement is provable in Mario
Carneiro's semantics from the assertions stored so far iff, after declaring finitely many fresh
dummy variables in the current scope (`Verify.DB.declareDummies`: `$v`, `$f` and `$d` statements,
applied as database actions), the parser accepts a normal-mode proof of it (`ProofAccepted`: frame
trimming at `$=`, the proof steps, and `finishProof` at `$.`).
`SourceCompleteness.acceptedWithDummies_iff_statementProvable_afterSource` states it at the end of
an error-free read of source text that stops between statements.

- Soundness (`statementProvable_of_acceptedWithDummies`): an accepted proof in any extended frame
  proves the stored statement (`Spec.Completeness.statementProvable_of_extendedFrame`); no dummy
  variable is needed for this direction.
- Completeness (`acceptedWithDummies_of_statementProvable`): Mario's semantics types every
  variable, a Metamath proof only those with an active `$f` statement. A derivation uses finitely
  many variables; each distinct one outside the stored frame becomes a fresh dummy variable
  (`Spec.Completeness.exists_extendDummies_of_statementProvable`), and a derivation within the
  stored frame declares none. `acceptedWithGeneratedDummies_of_statementProvable` also names the
  dummies: `dummyName b i` for the variables, `dummyLabel b i` for their floating hypotheses.

The dummy declarations here are database actions. `Metamath.SourceCompleteness` realizes them,
and the proof, as source text the parser reads.
-/

set_option autoImplicit false

namespace Metamath.CheckerCompleteness

open Metamath.Verify Metamath.Kernel Metamath.WF Metamath.Spec.Equivalence
open Metamath.Spec.StoredStatement (statementOfFrame)
open Metamath.Spec.Completeness (ExtendedFrame exists_extendDummies_of_statementProvable
  statementProvable_of_extendedFrame)
open Metamath.Spec.DummyExtension (extendDummies DummyFresh maxLength length_le_maxLength)
open Metamath.StoredStatementSoundness.Runtime (toFrame_stable_of_find_mono
  frameVarsDisjointConsts_of_find_mono trimVars)
open Metamath.ParserOps (ParserStateInv)
open Metamath.AssertDv (AssertDvVarsInFrame)
open Metamath.ParserEquivalence (AnyFormatFoldSucceeds)
open Metamath.ParserAnyFormatEquivalence (finishProof_success_stack_conditions)
open Metamath.PrefixProvenance (NormalProofReachable)
open Metamath.PrefixTraceCompressed (NormalProofReachable_same_db_provable)

/-- The constants of a database state are finitely many: each is a key of its object map. -/
theorem toConsts_finite (db : Verify.DB) :
    ∃ L : List String, ∀ s, toConsts db s → s ∈ L := by
  refine ⟨db.objects.keys, fun s hs => ?_⟩
  simp only [toConsts, Verify.DB.isConst, Verify.DB.find?] at hs
  rw [Std.HashMap.mem_keys]
  cases h : db.objects[s]? with
  | none => simp [h] at hs
  | some _ => exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])

/-- A claim whose frame trims respects the active frame: its variables are float variables of the
active frame, and its constants are not. -/
theorem formulaSymsRespectFrame_active_of_trim (db : DB) (f : Verify.Formula)
    (frImpl : Verify.Frame) (h_wf : WellFormedDB db) (h_scoped : WellScopedDB db)
    (h_decl : FormulaSymbolsDeclared db f) (h_trim : db.trimFrame' f = .ok frImpl) :
    db.formulaSymsRespectFrame f db.frame = true := by
  unfold Verify.DB.formulaSymsRespectFrame
  rw [List.all_eq_true]
  intro s hs
  cases s with
  | var v =>
      have hv : (trimVars db f).contains v = true :=
        (trimVars_contains_iff db f v).mpr (Or.inl hs)
      simp [trimVars_subset_frameFloatVars db f frImpl h_wf h_trim hv]
  | const c =>
      simp [const_not_in_frameFloatVars_of_declared db db.frame f h_scoped h_decl c hs]

/-- Symbol declarations survive adding objects. -/
theorem formulaSymbolsDeclared_mono {db db' : DB}
    (h_mono : ∀ l o, db.find? l = some o → db'.find? l = some o) {f : Verify.Formula}
    (h : FormulaSymbolsDeclared db f) : FormulaSymbolsDeclared db' f := by
  intro s hs
  have h1 := h s hs
  cases s with
  | const c => exact isConst_of_find?_mono h_mono h1
  | var v => exact isVar_of_find?_mono h_mono h1

/-- What declaring fresh dummy variables does to the database state (from the `declareDummies_*`
lemmas). -/
structure DummiesDeclared (s : ParserState) (pos : Pos) (label : String) (ds : List DummyDecl)
    (frAct : Spec.Frame) : Prop where
  inv : ParserStateInv (s.withDB (·.declareDummies pos ds))
  error : (s.db.declareDummies pos ds).error? = none
  mono : ∀ l o, s.db.find? l = some o → (s.db.declareDummies pos ds).find? l = some o
  label : (s.db.declareDummies pos ds).find? label = none
  interrupt : (s.db.declareDummies pos ds).interrupt = s.db.interrupt
  hyps : (s.db.declareDummies pos ds).frame.hyps = s.db.frame.hyps ++ (ds.map (·.lbl)).toArray
  dj : (s.db.declareDummies pos ds).frame.dj =
    s.db.frame.dj ++ (dummyDJs (s.db.frameFloatVars s.db.frame) (ds.map (·.var))).toArray
  lbl_find : ∀ d ∈ ds, (s.db.declareDummies pos ds).find? d.lbl =
    some (.hyp false #[.const d.tc, .var d.var] d.lbl)
  toDB : toDatabaseTotal (s.db.declareDummies pos ds) = toDatabaseTotal s.db
  toFrame : toFrame (s.db.declareDummies pos ds) (s.db.declareDummies pos ds).frame =
    some ⟨frAct.hyps ++ ds.map (fun d => Spec.Hyp.floating ⟨d.tc⟩ ⟨d.var⟩),
      frAct.dv ++ (dummyDJs (s.db.frameFloatVars s.db.frame) (ds.map (·.var))).map convertDV⟩
  consts : ∀ c, (s.db.declareDummies pos ds).isConst c = s.db.isConst c

theorem toConsts_eq {db db' : DB} (h : ∀ c, db'.isConst c = db.isConst c) :
    toConsts db' = toConsts db := by
  funext c
  simp only [toConsts, h c]

/-- Declaring fresh dummy variables at a parser state between statements. -/
theorem dummiesDeclared_of_fresh (s : ParserState) (pos : Pos) (label : String)
    (ds : List DummyDecl) (frAct : Spec.Frame) (h_inv : ParserStateInv s)
    (h_start : s.tokp = .start) (h_err : s.db.error? = none) (h_label : s.db.find? label = none)
    (h_fresh : DummyDeclsFresh s.db label ds) (h_act : toFrame s.db s.db.frame = some frAct) :
    DummiesDeclared s pos label ds frAct := by
  have h_wf : WellFormedDB s.db := h_inv.1
  have h_sc : WellScopedDB s.db := h_inv.2.1.1
  have h_not_var : label ∉ ds.map (·.var) := fun h =>
    (List.nodup_append.mp h_fresh.nodup).2.2 label (List.mem_append_left _ h) label
      (List.mem_singleton_self _) rfl
  have h_not_lbl : label ∉ ds.map (·.lbl) := fun h =>
    (List.nodup_append.mp h_fresh.nodup).2.2 label (List.mem_append_right _ h) label
      (List.mem_singleton_self _) rfl
  have h_frame := declareDummies_frame s.db pos label ds h_err h_wf h_sc h_fresh
  refine
    { inv := declareDummies_stateInv s pos label ds h_inv h_start h_err h_fresh
      error := declareDummies_error s.db pos label ds h_err h_wf h_sc h_fresh
      mono := declareDummies_find?_mono s.db pos label ds h_err h_wf h_sc h_fresh
      label := (declareDummies_find?_of_not_mem s.db pos label ds h_err h_wf h_sc h_fresh label
        h_not_var h_not_lbl).trans h_label
      interrupt := (declareDummies_fields s.db pos label ds h_err h_wf h_sc h_fresh).1
      hyps := by rw [h_frame]
      dj := by rw [h_frame]
      lbl_find := declareDummies_find?_lbl s.db pos label ds h_err h_wf h_sc h_fresh
      toDB := declareDummies_toDatabaseTotal s.db pos label ds h_err h_wf h_sc h_fresh
      toFrame := declareDummies_toFrame s.db pos label ds h_err h_wf h_sc h_fresh frAct h_act
      consts := fun c => ?_ }
  by_cases h_var : c ∈ ds.map (·.var)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h_var
    simp [Verify.DB.isConst, declareDummies_find?_var s.db pos label ds h_err h_wf h_sc h_fresh d hd,
      h_fresh.var_fresh d hd]
  · by_cases h_lbl : c ∈ ds.map (·.lbl)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h_lbl
      simp [Verify.DB.isConst, declareDummies_find?_lbl s.db pos label ds h_err h_wf h_sc h_fresh d hd,
        h_fresh.lbl_fresh d hd]
    · simp only [Verify.DB.isConst,
        declareDummies_find?_of_not_mem s.db pos label ds h_err h_wf h_sc h_fresh c h_var h_lbl]

/-- The trimmed frame does not change when fresh dummies are declared. -/
theorem trimFrame'_declareDummies (s : ParserState) (pos : Pos) (label : String)
    (ds : List DummyDecl) (frAct : Spec.Frame) (f : Verify.Formula) (frImpl : Verify.Frame)
    (h_wf : WellFormedDB s.db) (h_scoped : WellScopedDB s.db)
    (h_decl : FormulaSymbolsDeclared s.db f) (h_fresh : DummyDeclsFresh s.db label ds)
    (hD : DummiesDeclared s pos label ds frAct) (h_trim : s.db.trimFrame' f = .ok frImpl) :
    (s.db.declareDummies pos ds).trimFrame' f = .ok frImpl := by
  have h_nm : ∀ d ∈ ds, NotMandatory s.db f d.var := fun d hd =>
    notMandatory_of_fresh s.db h_scoped f h_decl (h_fresh.var_fresh d hd)
  refine trimFrame'_ok_of_dummy_floats s.db _ f frImpl (ds.map (·.lbl)).toArray
    (dummyDJs (s.db.frameFloatVars s.db.frame) (ds.map (·.var))).toArray h_wf hD.hyps hD.dj
    hD.mono ?_ ?_ h_trim
  · intro l hl
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hl)
    exact ⟨d.tc, d.var, hD.lbl_find d hd, h_nm d hd⟩
  · intro v w hvw
    have hvw' : (v, w) ∈ dummyDJs (s.db.frameFloatVars s.db.frame) (ds.map (·.var)) :=
      List.mem_toArray.mp hvw
    rcases mem_dummyDJs hvw' with ⟨hv, _⟩ | ⟨hw, _⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (h_nm d hd)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
      exact Or.inr (h_nm d hd)

/-- The runtime frame after declaring the dummies proves what the spec's extended frame proves. -/
theorem specProvable_runtime_of_extendDummies {Γ : Spec.Database} {frAct : Spec.Frame}
    (seen : List String) (hseen : ∀ x : Spec.Variable, x ∈ frAct.vars ↔ x.v ∈ seen)
    (bound : Nat) (ps : List (Spec.Constant × Spec.Variable)) {e : Spec.Expr}
    (h : Spec.Provable Γ (extendDummies frAct ps) e) :
    Spec.Provable Γ
      ⟨frAct.hyps ++ (dummyDecls bound ps 0).map (fun d => Spec.Hyp.floating ⟨d.tc⟩ ⟨d.var⟩),
        frAct.dv ++ (dummyDJs seen ((dummyDecls bound ps 0).map (·.var))).map convertDV⟩ e := by
  refine (Spec.Provable.dv_congr ?_ ?_).mp h
  · change frAct.hyps ++ ps.map (fun p => Spec.Hyp.floating p.1 p.2) = _
    rw [dummyDecls_floats]
  · intro v w
    change Spec.dvRel (frAct.dv ++ Metamath.Spec.DummyExtension.dummyDV frAct.vars
      (ps.map Prod.snd)) v w ↔ _
    rw [dvRel_append, dvRel_append, dummyDecls_vars]
    have hvars : ps.map (·.2.v) = (ps.map Prod.snd).map (·.v) := by
      rw [List.map_map]
      rfl
    rw [hvars, dvRel_dummyDJs_iff_dummyDV hseen (ps.map Prod.snd)]

/-- **Completeness at a database state, with the declarations.** A `$p` claim whose stored
statement is provable in Mario Carneiro's semantics is accepted after declaring finitely many fresh
dummy variables, each named `dummyName b i` with its floating hypothesis labelled
`dummyLabel b i`. -/
theorem acceptedWithGeneratedDummies_of_statementProvable (s : ParserState) (pos : Pos)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_inv : ParserStateInv s) (h_start : s.tokp = .start) (h_err : s.db.error? = none)
    (h_int : s.db.interrupt = false)
    (h_label : s.db.find? label = none) (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared s.db f)
    (h_trim : s.db.trimFrame' f = .ok frImpl) (h_fr : toFrame s.db frImpl = some fr)
    (h_dv : AssertDvVarsInFrame s.db)
    (h_prov : (statementOfFrame fr (toExpr f)).Provable (dbToAxioms (toDatabaseTotal s.db))) :
    ∃ ds, DummyDeclsFresh s.db label ds ∧
      (∀ d ∈ ds, (∃ b i, d.var = Spec.DummyExtension.dummyName b i) ∧
        ∃ b i, d.lbl = dummyLabel b i) ∧
      ∃ proof, ProofAccepted (s.withDB (·.declareDummies pos ds)) pos label f proof := by
  have h_wf : WellFormedDB s.db := h_inv.1
  have h_scoped : WellScopedDB s.db := h_inv.2.1.1
  have h_sf := completenessScopedFacts_of_wellScopedDB s.db h_scoped
  have h_strong : WellFormedDatabaseStrong (toDatabaseTotal s.db) (toConsts s.db) :=
    toDatabase_wellFormed_strong s.db h_wf h_scoped h_dv _ rfl
  obtain ⟨frAct, h_act⟩ := toFrame_some_of_wfFrame s.db h_wf.1
  have h_ext := extendedFrame_of_trim s.db f frImpl fr frAct h_wf h_sf h_trim h_fr h_act
  have h_fr_wf := frameWellFormed_of_trim s.db f frImpl fr h_wf h_trim h_fr
  have h_frImpl_wf := ParserOps.trimFrame'_success_implies_wellformed_frame s.db f frImpl h_wf
    h_trim
  have h_dc : Spec.FrameVarsDisjointConsts (toConsts s.db) fr :=
    frameVarsDisjointConsts_of_find_mono s.db s.db frImpl fr h_fr h_frImpl_wf h_scoped
      (fun _ _ h => h)
  have h_scope :=
    frameExprsInScope_of_trim s.db h_wf h_scoped f frImpl fr h_trim h_fr h_head h_decl
  obtain ⟨ps, hfresh, havoid, htypes, hnames, _, hprov⟩ :=
    exists_extendDummies_of_statementProvable h_strong (toConsts_finite s.db) h_fr_wf h_dc h_scope
      h_ext (s.db.objects.keys ++ [label]) h_prov
  obtain ⟨bound, hbound⟩ : ∃ bound, bound = maxLength (s.db.objects.keys ++ label :: ps.map (·.2.v)) :=
    ⟨_, rfl⟩
  have h_dfresh : DummyDeclsFresh s.db label (dummyDecls bound ps 0) :=
    dummyDecls_fresh s.db label bound ps hfresh.nodup
      (fun p hp hk => havoid p hp (List.mem_append_left _ hk))
      (fun p hp heq => havoid p hp (List.mem_append_right _ (by rw [heq]; exact List.mem_singleton_self _)))
      (fun x hx => hbound ▸ length_le_maxLength hx)
      (fun p hp => (htypes p hp).elim
        (fun h => h ▸ conclusionTypecode_isConst s.db f h_head h_decl)
        (fun h => premiseTypecode_isConst s.db h_wf h_sf h))
  refine ⟨dummyDecls bound ps 0, h_dfresh, fun d hd => ?_, ?_⟩
  · obtain ⟨⟨p, hp, _, h_var⟩, j, _, h_lbl⟩ := mem_dummyDecls hd
    obtain ⟨b, i, h_name⟩ := hnames p hp
    exact ⟨⟨b, i, h_var.trans h_name⟩, bound, j, h_lbl⟩
  have hD := dummiesDeclared_of_fresh s pos label _ frAct h_inv h_start h_err h_label h_dfresh
    h_act
  obtain ⟨h_wf', h_scopedW', _, _⟩ := hD.inv
  have h_scoped' : WellScopedDB (s.db.declareDummies pos (dummyDecls bound ps 0)) := h_scopedW'.1
  have h_sf' := completenessScopedFacts_of_wellScopedDB _ h_scoped'
  have h_trim' := trimFrame'_declareDummies s pos label _ frAct f frImpl h_wf h_scoped h_decl
    h_dfresh hD h_trim
  have h_decl' := formulaSymbolsDeclared_mono hD.mono h_decl
  have h_resp' := formulaSymsRespectFrame_active_of_trim _ f frImpl h_wf' h_scoped' h_decl' h_trim'
  have hseen : ∀ x : Spec.Variable, x ∈ frAct.vars ↔ x.v ∈ s.db.frameFloatVars s.db.frame := by
    intro x
    rw [frameFloatVars_mem_iff_vars s.db s.db.frame frAct h_act h_wf.1, varNames_mem_iff]
  have h_prov_run := specProvable_runtime_of_extendDummies _ hseen bound ps hprov
  rw [← hD.toDB] at h_prov_run
  obtain ⟨proof, pr, h_fold, _, h_fin⟩ :=
    normal_proof_finishes_exact (s.withDB (·.declareDummies pos (dummyDecls bound ps 0))) label f
      pos frImpl h_wf' h_sf' _ _ rfl hD.toFrame
      (fun l fr₀ e h => by
        have h' : toDatabaseTotal s.db l = some (fr₀, e) := by
          rw [← hD.toDB]
          exact h
        exact (h_strong.2 l fr₀ e h').2)
      h_head h_resp' h_prov_run hD.label hD.error
  exact ⟨proof, h_head, hD.interrupt.trans h_int, frImpl, pr, h_trim', h_fold, h_fin⟩

/-- **Completeness at a database state.** A `$p` claim whose stored statement is provable in
Mario Carneiro's semantics is accepted after declaring finitely many fresh dummy variables. -/
theorem acceptedWithDummies_of_statementProvable (s : ParserState) (pos : Pos)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_inv : ParserStateInv s) (h_start : s.tokp = .start) (h_err : s.db.error? = none)
    (h_int : s.db.interrupt = false)
    (h_label : s.db.find? label = none) (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared s.db f)
    (h_trim : s.db.trimFrame' f = .ok frImpl) (h_fr : toFrame s.db frImpl = some fr)
    (h_dv : AssertDvVarsInFrame s.db)
    (h_prov : (statementOfFrame fr (toExpr f)).Provable (dbToAxioms (toDatabaseTotal s.db))) :
    AcceptedWithDummies s pos label f :=
  let ⟨ds, h_fresh, _, h_acc⟩ := acceptedWithGeneratedDummies_of_statementProvable s pos label f
    frImpl fr h_inv h_start h_err h_int h_label h_head h_decl h_trim h_fr h_dv h_prov
  ⟨ds, h_fresh, h_acc⟩

/-- **Soundness at a database state.** A `$p` claim accepted after declaring dummy variables has
a stored statement that is provable in Mario Carneiro's semantics. -/
theorem statementProvable_of_acceptedWithDummies (s : ParserState) (pos : Pos)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_inv : ParserStateInv s) (h_start : s.tokp = .start) (h_err : s.db.error? = none)
    (h_label : s.db.find? label = none) (h_decl : FormulaSymbolsDeclared s.db f)
    (h_trim : s.db.trimFrame' f = .ok frImpl) (h_fr : toFrame s.db frImpl = some fr)
    (h_dv : AssertDvVarsInFrame s.db)
    (h_acc : AcceptedWithDummies s pos label f) :
    (statementOfFrame fr (toExpr f)).Provable (dbToAxioms (toDatabaseTotal s.db)) := by
  obtain ⟨ds, h_dfresh, proof, h_head, _, frImpl', pr, h_trim'', h_fold, h_fin⟩ := h_acc
  have h_wf : WellFormedDB s.db := h_inv.1
  have h_scoped : WellScopedDB s.db := h_inv.2.1.1
  have h_strong : WellFormedDatabaseStrong (toDatabaseTotal s.db) (toConsts s.db) :=
    toDatabase_wellFormed_strong s.db h_wf h_scoped h_dv _ rfl
  obtain ⟨frAct, h_act⟩ := toFrame_some_of_wfFrame s.db h_wf.1
  have hD := dummiesDeclared_of_fresh s pos label ds frAct h_inv h_start h_err h_label h_dfresh
    h_act
  obtain ⟨h_wf', h_scopedW', _, _⟩ := hD.inv
  have h_scoped' : WellScopedDB (s.db.declareDummies pos ds) := h_scopedW'.1
  have h_sf' := completenessScopedFacts_of_wellScopedDB _ h_scoped'
  have h_trim' := trimFrame'_declareDummies s pos label ds frAct f frImpl h_wf h_scoped h_decl
    h_dfresh hD h_trim
  have h_eq : frImpl' = frImpl := by
    change (s.db.declareDummies pos ds).trimFrame' f = .ok frImpl' at h_trim''
    rw [h_trim'] at h_trim''
    exact (Except.ok.inj h_trim'').symm
  change Array.foldlM (fun pr l => (s.db.declareDummies pos ds).stepNormal pr l)
    { (s.db.declareDummies pos ds).mkProofState pos label f frImpl' with ptp := .normal } proof =
      .ok pr at h_fold
  rw [h_eq] at h_fold
  have h_fmla : pr.fmla = f :=
    (foldlM_stepNormal_preserves_fields (s.db.declareDummies pos ds) proof _ pr h_fold).2.2.1
  obtain ⟨h_size, h_top, _⟩ := finishProof_success_stack_conditions _ pr h_fin
  have h_reach : NormalProofReachable (s.db.declareDummies pos ds) label f pr.stack := by
    obtain ⟨r, h_r, h_rs⟩ :=
      (foldlM_stepNormal_transfer_iff (s.db.declareDummies pos ds) proof label f pos frImpl
        pr.stack).mpr ⟨pr, h_fold, rfl⟩
    exact ⟨proof, r, h_r, h_rs⟩
  obtain ⟨Γ', frRun, h_db', h_act', h_prov⟩ :=
    NormalProofReachable_same_db_provable (s.db.declareDummies pos ds) label f pr.stack h_reach
      hD.error h_wf' h_size
      (h_fmla ▸ h_top)
  have hΓ : Γ' = toDatabaseTotal s.db := by
    unfold toDatabase at h_db'
    rw [← hD.toDB]
    exact (Option.some.inj h_db').symm
  subst hΓ
  have h_fr' : toFrame (s.db.declareDummies pos ds) frImpl = some fr :=
    toFrame_stable_of_find_mono s.db _ frImpl fr hD.mono h_fr
  have h_ext := extendedFrame_of_trim (s.db.declareDummies pos ds) f frImpl fr frRun h_wf' h_sf'
    h_trim' h_fr' h_act'
  rw [toConsts_eq hD.consts] at h_ext
  have h_frImpl_wf := ParserOps.trimFrame'_success_implies_wellformed_frame s.db f frImpl h_wf
    h_trim
  exact statementProvable_of_extendedFrame h_strong
    (frameWellFormed_of_trim s.db f frImpl fr h_wf h_trim h_fr)
    (frameVarsDisjointConsts_of_find_mono s.db s.db frImpl fr h_fr h_frImpl_wf h_scoped
      (fun _ _ h => h))
    (frameExprsInScope_of_trim s.db h_wf h_scoped f frImpl fr h_trim h_fr h_head h_decl)
    h_ext h_prov

/-- **Soundness for the declarative semantics.** If the checker accepts a proof
of `f` at a database state whose active frame is an extended frame of `fr`, the
statement `(fr, f)` is declaratively provable from the database's assertions. -/
theorem statementProvable_of_anyFormatFoldSucceeds
    (db : Verify.DB) (label : String) (f : Verify.Formula)
    (Γ : Spec.Database) (consts : Spec.ConstSet) (fr fr' : Spec.Frame)
    (h_success : db.error? = none) (h_wf : WellFormedDB db)
    (h_db : toDatabase db = some Γ) (h_frame : toFrame db db.frame = some fr')
    (h_strong : WellFormedDatabaseStrong Γ consts) (h_ext : ExtendedFrame consts fr fr')
    (h_fr : FrameWellFormed fr) (h_dc : Spec.FrameVarsDisjointConsts consts fr)
    (h_scope : Spec.FrameExprsInScope consts fr (toExpr f))
    (h_accept : AnyFormatFoldSucceeds db label f) :
    (statementOfFrame fr (toExpr f)).Provable (dbToAxioms Γ) :=
  Spec.Completeness.statementProvable_of_extendedFrame h_strong h_fr h_dc h_scope h_ext
    (ParserEquivalence.specProvable_of_anyFormatFoldSucceeds db label f Γ fr' h_success h_wf
      h_db h_frame h_accept)

/-- **Checker acceptance and Mario Carneiro's semantics.** At a parser state between statements,
the statement that a `$p` claim `f` stores (with the frame `fr` that trimming gives) is provable in
Mario Carneiro's declarative semantics from the assertions stored so far iff, after declaring
finitely many fresh dummy variables, the parser accepts a normal-mode proof of `f`. -/
theorem acceptedWithDummies_iff_statementProvable (s : ParserState) (pos : Pos) (label : String)
    (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_inv : ParserStateInv s) (h_start : s.tokp = .start) (h_err : s.db.error? = none)
    (h_int : s.db.interrupt = false) (h_label : s.db.find? label = none)
    (h_head : f.hasConstHead = true) (h_decl : FormulaSymbolsDeclared s.db f)
    (h_trim : s.db.trimFrame' f = .ok frImpl) (h_fr : toFrame s.db frImpl = some fr)
    (h_dv : AssertDvVarsInFrame s.db) :
    AcceptedWithDummies s pos label f ↔
      (statementOfFrame fr (toExpr f)).Provable (dbToAxioms (toDatabaseTotal s.db)) :=
  ⟨statementProvable_of_acceptedWithDummies s pos label f frImpl fr h_inv h_start h_err h_label
      h_decl h_trim h_fr h_dv,
    acceptedWithDummies_of_statementProvable s pos label f frImpl fr h_inv h_start h_err h_int
      h_label h_head h_decl h_trim h_fr h_dv⟩

end Metamath.CheckerCompleteness
