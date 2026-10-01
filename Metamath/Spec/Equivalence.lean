/-
Bridge between the operational verifier (Verify.lean) and Mario's declarative
specification (DeclarativeSpec.lean), at one fixed frame.

**Soundness** (`operational_to_declarative`): every proof accepted by the verifier
is valid under Mario's semantics.

**Frame derivability** (`FrameDerivable`): Mario's `Provable` in which every
variable leaf must be a variable of the frame, i.e. derivability by Metamath's
rules in that frame. It is exactly operational provability
(`operational_to_frameDerivable`, `frameDerivable_to_proofValid`).

Mario's `Provable` allows any variable, so at one fixed frame it can prove more
than the verifier (`Metamath.Spec.FixedFrameCounterexample`). The two agree up to
extending the frame by dummy variables (`Metamath.Spec.Completeness`).
-/

import Metamath.Spec.Core
import Metamath.Spec.Operational
import Metamath.Spec.Declarative
import Metamath.Spec.Bridge
import Metamath.Spec.Derivable
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


namespace Metamath.Spec.Equivalence

open Spec (Database Frame Expr Hyp Variable Constant Label Subst ProofValid Provable)
open Declarative (Provable)
open Bridge

/-! ## Helper Conversions

We convert our operational types to Mario's semantic types using a **typed**
variable map derived from floating hypotheses.

Key idea: Mario's `VR.type` encodes the *typecode*, while the `i` index
distinguishes variables of the same type. We therefore build a map
`Variable → DeclarativeVR` from floating hypotheses, preserving typecodes.
-/

abbrev VarMap := List (Variable × DeclarativeVR)

/-- Enumerate floats with a running index (auxiliary). -/
def varMapOfFrameAux (n : Nat) : List (Constant × Variable) → VarMap
  | [] => []
  | (c, v) :: rest => (v, ⟨c.c, n⟩) :: varMapOfFrameAux (n + 1) rest

/-- Extract floating hypotheses (typecode, variable) in order. -/
def floatList (fr : Frame) : List (Constant × Variable) :=
  fr.hyps.filterMap fun h =>
    match h with
    | Hyp.floating c v => some (c, v)
    | Hyp.essential _ => none

/-- Build a typed variable map from floating hypotheses. -/
def varMapOfFrame (fr : Frame) : VarMap :=
  varMapOfFrameAux 0 (floatList fr)

/-- Find the DeclarativeVR corresponding to a variable. -/
def findVR (vm : VarMap) (v : Variable) : Option DeclarativeVR :=
  (vm.find? fun p => p.1 = v).map Prod.snd

/-- Find the Variable corresponding to a DeclarativeVR. -/
def findVar (vm : VarMap) (vr : DeclarativeVR) : Option Variable :=
  (vm.find? fun p => p.2 = vr).map Prod.fst

/-- Frame has unique floating hypotheses: each variable has at most one typecode.
    Per Metamath spec, the parser enforces this. -/
def FloatUnique (fr : Frame) : Prop :=
  ∀ c c' v, Hyp.floating c v ∈ fr.hyps → Hyp.floating c' v ∈ fr.hyps → c = c'

/-- Frame has no duplicate variables in floating hypotheses.
    This means each variable appears at most once in floatList.
    The Metamath parser enforces this by not allowing multiple float statements for the same variable. -/
def FloatVarNoDup (fr : Frame) : Prop :=
  List.Nodup ((floatList fr).map Prod.snd)

/-- A frame is well-formed if it has unique floating hypotheses and no duplicate variables. -/
def FrameWellFormed (fr : Frame) : Prop :=
  FloatUnique fr ∧ FloatVarNoDup fr

/-- DV constraints are well-formed: all variables have floating hypotheses
    and there are no self-pairs (v, v).

    The Metamath verifier enforces this:
    - trimFrame filters DV pairs to only include variables in the formula
    - Variables in formulas must have floating hypotheses
    - Pairs are stored in canonical order (v1 < v2), preventing self-pairs -/
def DVWellFormed (fr : Frame) : Prop :=
  -- All DV variables have floating hypotheses
  (∀ v w, (v, w) ∈ fr.dv → v ∈ fr.vars ∧ w ∈ fr.vars) ∧
  -- No self-pairs
  (∀ v, (v, v) ∉ fr.dv)

/-- A database is strongly well-formed if all frames satisfy FrameWellFormed
    and DVWellFormed, in addition to the basic WellFormedDatabase properties. -/
def WellFormedDatabaseStrong (Γ : Database) (consts : ConstSet) : Prop :=
  Spec.WellFormedDatabase Γ consts ∧
  ∀ l fr e, Γ l = some (fr, e) → FrameWellFormed fr ∧ DVWellFormed fr

/-- Convert a symbol string using a typed variable map. -/
def toDeclarativeSym (vm : VarMap) (s : String) : DeclarativeSym :=
  let v := Variable.mk s
  match findVR vm v with
  | some vr => .var vr
  | none => .const s

/-- Convert our Expr (typecode + symbols) to Mario's expression (symbols only). -/
def exprToDeclarativeExpr (vm : VarMap) (e : Expr) : DeclarativeExpr :=
  e.syms.map (fun s => toDeclarativeSym vm s)

-- Note: toDeclarativeSym injectivity and exprToDeclarativeExpr injectivity lemmas
-- are defined later after the infrastructure lemmas they depend on.

/-! ## Inverse Conversions (Mario → Spec)

These convert Mario's representation back to ours. Used in the completeness proof.
-/

/-- Convert a Mario symbol back to a string symbol.
    Variables become the string name of the variable found via findVar.
    Constants stay as themselves. -/
def fromDeclarativeSym (vm : VarMap) (sym : DeclarativeSym) : Sym :=
  match sym with
  | .const s => s
  | .var vr =>
      match findVar vm vr with
      | some v => v.v
      | none => "" -- shouldn't happen for well-formed inputs

/-- Convert a Mario expression back to a list of symbols. -/
def fromDeclarativeExpr (vm : VarMap) (me : DeclarativeExpr) : List Sym :=
  me.map (fromDeclarativeSym vm)

/-- Convert a Mario formula back to an Expr. -/
def fromDeclarativeFormula (vm : VarMap) (fmla : Declarative.Formula) : Expr :=
  ⟨⟨fmla.1⟩, fromDeclarativeExpr vm fmla.2⟩

/-- Convert Expr to Mario's Formula (typecode + symbols). -/
def exprToFormula (vm : VarMap) (e : Expr) : Declarative.Formula :=
  (e.typecode.c, exprToDeclarativeExpr vm e)

-- Note: Roundtrip lemmas (fromDeclarativeSym_toDeclarativeSym_frame, etc.) are defined
-- after findVR_findVar_inverse_frame which they depend on.

/-- Convert a hypothesis to Mario's Formula.

Floating hypotheses become variable formulas; essential hypotheses become expressions. -/
def hypToDeclarativeFormula (vm : VarMap) (h : Hyp) : Declarative.Formula :=
  match h with
  | Hyp.floating c v =>
      let vr :=
        match findVR vm v with
        | some vr => vr
        | none => ⟨c.c, 0⟩
      (c.c, [Metamath.Sym.var vr])
  | Hyp.essential e => exprToFormula vm e

/-- Convert a DV list to Mario's DJ using a typed variable map. -/
def dvListToDeclarativeDJ (vm : VarMap) (dv : List (Variable × Variable)) : DeclarativeDJ :=
  let vrPairs := dv.filterMap fun (v, w) =>
    match findVR vm v, findVR vm w with
    | some vr1, some vr2 => some (vr1, vr2)
    | _, _ => none
  Metamath.DJ.mk' vrPairs

/-- Convert a substitution to Mario's form, using axiom vars for the domain
    and caller vars for the codomain. -/
def toDeclarativeSubst (vmAx vm : VarMap) (σ : Subst) : DeclarativeVR → DeclarativeExpr :=
  fun vr =>
    match findVar vmAx vr with
    | some v => exprToDeclarativeExpr vm (σ v)
    | none => [Metamath.Sym.var vr]

/-- Convert Frame to Context using its typed variable map. -/
noncomputable def frameToContext (fr : Frame) : Declarative.Context :=
  let vm := varMapOfFrame fr
  { hyps := fr.hyps.map (fun h => hypToDeclarativeFormula vm h)
    dj := dvListToDeclarativeDJ vm fr.dv }

/-- Convert our Database to Mario's axiom set. -/
noncomputable def dbToAxioms (Γ : Database) : Declarative.Statement → Prop :=
  fun stmt => ∃ (l : Label) (fr : Frame) (e : Expr),
    Γ l = some (fr, e) ∧
    stmt.ctx = frameToContext fr ∧
    stmt.fmla = exprToFormula (varMapOfFrame fr) e

/-! ## Completeness Infrastructure

These lemmas support the `frameDerivable_to_proofValid` completeness proof.
-/

/-- Inverse of dbToAxioms: extract the concrete label, frame, and expression.
    This is trivial since dbToAxioms is defined as an existential. -/
theorem dbToAxioms_inverse {Γ : Database} {ax : Declarative.Statement} :
    dbToAxioms Γ ax → ∃ l fr e, Γ l = some (fr, e) ∧
                       ax.ctx = frameToContext fr ∧
                       ax.fmla = exprToFormula (varMapOfFrame fr) e := by
  intro h
  exact h

/-- Hypothesis membership in frameToContext comes from frame's hyps. -/
theorem hyps_correspondence {fr : Frame} {h : Declarative.Formula} :
    h ∈ (frameToContext fr).hyps →
    ∃ hyp ∈ fr.hyps, h = hypToDeclarativeFormula (varMapOfFrame fr) hyp := by
  intro h_mem
  unfold frameToContext at h_mem
  simp only [] at h_mem
  obtain ⟨hyp, h_in, h_eq⟩ := List.mem_map.mp h_mem
  exact ⟨hyp, h_in, h_eq.symm⟩

/-- Convert a Mario substitution back to a Spec substitution.
    For variables in the axiom's frame, use fromDeclarativeExpr to convert back.
    For other variables, use identity. -/
def declarativeSubstToSpec (vmAx vm : VarMap) (σ : DeclarativeVR → DeclarativeExpr) : Subst :=
  fun v =>
    match findVR vmAx v with
    | some vr => ⟨⟨vr.type⟩, fromDeclarativeExpr vm (σ vr)⟩
    | none => ⟨⟨""⟩, [v.v]⟩  -- identity for non-axiom vars

/-- declarativeSubstToSpec simplifies when findVR succeeds. -/
theorem declarativeSubstToSpec_findVR {vmAx vm : VarMap} {σ : DeclarativeVR → DeclarativeExpr}
    {v : Variable} {vr : DeclarativeVR}
    (h_find : findVR vmAx v = some vr) :
    declarativeSubstToSpec vmAx vm σ v = ⟨⟨vr.type⟩, fromDeclarativeExpr vm (σ vr)⟩ := by
  unfold declarativeSubstToSpec
  simp [h_find]

/-- Typecode of declarativeSubstToSpec matches the VR type for axiom variables. -/
theorem declarativeSubstToSpec_typecode {vmAx vm : VarMap} {σ : DeclarativeVR → DeclarativeExpr}
    {v : Variable} {vr : DeclarativeVR}
    (h_find : findVR vmAx v = some vr) :
    (declarativeSubstToSpec vmAx vm σ v).typecode.c = vr.type := by
  rw [declarativeSubstToSpec_findVR h_find]

-- Note: declarativeSubstToSpec_float_typecode is defined later, after findVR_of_float_typed

/-! ## Helper Lemmas

These lemmas show that our conversions preserve structure correctly.
-/

/-- Essential hypothesis conversion matches exprToFormula. -/
theorem hypToDeclarativeFormula_essential (vm : VarMap) (e : Expr) :
    hypToDeclarativeFormula vm (Hyp.essential e) = exprToFormula vm e := by
  rfl

/-- If a variable is found in the map, toDeclarativeSym returns .var. -/
theorem toDeclarativeSym_var {vm : VarMap} {v : Variable} {vr : DeclarativeVR}
    (h_find : findVR vm v = some vr) :
    toDeclarativeSym vm v.v = .var vr := by
  unfold toDeclarativeSym
  simp [h_find]

/-- Floating hypothesis for single-variable expression matches exprToFormula. -/
theorem hypToDeclarativeFormula_floating_expr (vm : VarMap) (c : Constant) (v : Variable)
    {vr : DeclarativeVR} (h_find : findVR vm v = some vr) :
    hypToDeclarativeFormula vm (Hyp.floating c v) = exprToFormula vm ⟨c, [v.v]⟩ := by
  unfold hypToDeclarativeFormula exprToFormula exprToDeclarativeExpr
  simp [h_find, toDeclarativeSym_var h_find]
  rfl

/-- Hypothesis conversion always yields a member of the frame context. -/
theorem hypToDeclarativeFormula_mem {fr : Frame} {h : Hyp} :
    h ∈ fr.hyps →
    hypToDeclarativeFormula (varMapOfFrame fr) h ∈ (frameToContext fr).hyps := by
  intro h_in
  unfold frameToContext
  exact (List.mem_map).2 ⟨h, h_in, rfl⟩

/-- Floating hypotheses appear in the floatList. -/
theorem floatList_mem_of_float {fr : Frame} {c : Constant} {v : Variable} :
    Hyp.floating c v ∈ fr.hyps → (c, v) ∈ floatList fr := by
  intro h_in
  unfold floatList
  refine (List.mem_filterMap).2 ?_
  exact ⟨Hyp.floating c v, h_in, rfl⟩

/-- Soundness: members of floatList come from floating hypotheses. -/
theorem floatList_sound {fr : Frame} {c : Constant} {v : Variable} :
    (c, v) ∈ floatList fr → Hyp.floating c v ∈ fr.hyps := by
  intro h_mem
  unfold floatList at h_mem
  simp [List.mem_filterMap] at h_mem
  obtain ⟨h, h_in, h_eq⟩ := h_mem
  cases h with
  | floating c' v' =>
      simp at h_eq
      obtain ⟨h_c, h_v⟩ := h_eq
      cases h_c
      cases h_v
      exact h_in
  | essential e =>
      simp at h_eq

/-- Variables in a frame come from floating hypotheses. -/
theorem var_mem_iff_float {fr : Frame} {v : Variable} :
    v ∈ fr.vars ↔ ∃ c, Hyp.floating c v ∈ fr.hyps := by
  unfold Frame.vars
  constructor
  · intro h_mem
    -- Use mem_filterMap to extract the floating hyp.
    rcases (List.mem_filterMap).1 h_mem with ⟨h, h_in, h_eq⟩
    cases h with
    | floating c v' =>
        cases h_eq
        exact ⟨c, h_in⟩
    | essential e =>
        simp at h_eq
  · rintro ⟨c, h_in⟩
    -- Build membership in filterMap from floating hyp.
    refine (List.mem_filterMap).2 ?_
    exact ⟨Hyp.floating c v, h_in, rfl⟩

/-- If a variable occurs in the var map, findVR returns some value. -/
theorem findVR_some_of_mem {vm : VarMap} {v : Variable} {vr : DeclarativeVR} :
    (v, vr) ∈ vm → ∃ vr', findVR vm v = some vr' := by
  intro h_mem
  classical
  cases h_find : vm.find? (fun p => p.1 = v) with
  | some p =>
      refine ⟨p.2, ?_⟩
      simp [findVR, h_find]
  | none =>
      have h_none' : ∀ x ∈ vm, ¬ decide (x.1 = v) = true :=
        (List.find?_eq_none (l := vm) (p := fun p => p.1 = v)).1 h_find
      have h_none : ∀ x ∈ vm, x.1 ≠ v := by
        intro x hx h_eq
        have h_dec : decide (x.1 = v) = true := decide_eq_true_eq.mpr h_eq
        exact h_none' x hx h_dec
      have : False := h_none (v, vr) h_mem rfl
      exact this.elim

/-- If findVR succeeds, the pair is in the varmap. -/
theorem findVR_mem_of_some {vm : VarMap} {v : Variable} {vr : DeclarativeVR}
    (h_find : findVR vm v = some vr) :
    (v, vr) ∈ vm := by
  unfold findVR at h_find
  match h_f : vm.find? (fun p => p.1 = v) with
  | none =>
      simp only [h_f, Option.map] at h_find
      cases h_find  -- Contradiction: none = some vr
  | some p =>
      simp only [h_f, Option.map, Option.some.injEq] at h_find
      have h_p_mem : p ∈ vm := List.mem_of_find?_eq_some h_f
      have h_p_eq : p.1 = v := by
        have := List.find?_some h_f
        exact decide_eq_true_eq.mp this
      have h_p_is : p = (v, vr) := Prod.ext h_p_eq h_find
      rw [h_p_is] at h_p_mem
      exact h_p_mem

/-- Floating hypotheses induce entries in the typed variable map. -/
theorem mem_varMapAux_of_mem {n : Nat} {c : Constant} {v : Variable}
    {xs : List (Constant × Variable)} :
    (c, v) ∈ xs → ∃ vr, (v, vr) ∈ varMapOfFrameAux n xs := by
  intro h_mem
  induction xs generalizing n with
  | nil =>
      cases h_mem
  | cons cv rest ih =>
      cases cv with
      | mk c0 v0 =>
          cases h_mem with
          | head =>
              refine ⟨⟨c.c, n⟩, ?_⟩
              simp [varMapOfFrameAux]
          | tail _ h_tail =>
              obtain ⟨vr, h_mem'⟩ := ih (n := n + 1) h_tail
              refine ⟨vr, ?_⟩
              simp [varMapOfFrameAux, h_mem']

/-- Typed completeness: floating hyp gives entry with matching type. -/
theorem mem_varMapAux_of_mem_typed {n : Nat} {c : Constant} {v : Variable}
    {xs : List (Constant × Variable)} :
    (c, v) ∈ xs → ∃ vr, (v, vr) ∈ varMapOfFrameAux n xs ∧ vr.type = c.c := by
  intro h_mem
  induction xs generalizing n with
  | nil =>
      cases h_mem
  | cons cv rest ih =>
      cases cv with
      | mk c0 v0 =>
          cases h_mem with
          | head =>
              refine ⟨⟨c.c, n⟩, ?_, rfl⟩
              simp [varMapOfFrameAux]
          | tail _ h_tail =>
              obtain ⟨vr, h_mem', h_type⟩ := ih (n := n + 1) h_tail
              refine ⟨vr, ?_, h_type⟩
              simp [varMapOfFrameAux, h_mem']

/-- Soundness for varMapOfFrameAux: membership implies a float in the list. -/
theorem mem_varMapAux_sound {n : Nat} {v : Variable} {vr : DeclarativeVR}
    {xs : List (Constant × Variable)} :
    (v, vr) ∈ varMapOfFrameAux n xs → ∃ c, (c, v) ∈ xs := by
  intro h_mem
  induction xs generalizing n with
  | nil =>
      cases h_mem
  | cons cv rest ih =>
      cases cv with
      | mk c0 v0 =>
          -- Unfold the head of varMapOfFrameAux and split membership.
          cases h_mem with
          | head =>
              -- (v, vr) is the head pair
              refine ⟨c0, ?_⟩
              simp
          | tail _ h_tail =>
              obtain ⟨c, h_mem'⟩ := ih (n := n + 1) h_tail
              exact ⟨c, List.mem_cons_of_mem _ h_mem'⟩

/-- Stronger soundness: membership implies float AND vr.type matches the typecode. -/
theorem mem_varMapAux_sound_typed {n : Nat} {v : Variable} {vr : DeclarativeVR}
    {xs : List (Constant × Variable)} :
    (v, vr) ∈ varMapOfFrameAux n xs → ∃ c, (c, v) ∈ xs ∧ vr.type = c.c := by
  intro h_mem
  induction xs generalizing n with
  | nil =>
      simp only [varMapOfFrameAux, List.not_mem_nil] at h_mem
  | cons cv rest ih =>
      cases cv with
      | mk c0 v0 =>
          simp only [varMapOfFrameAux, List.mem_cons] at h_mem
          cases h_mem with
          | inl h_eq =>
              -- (v, vr) = (v0, ⟨c0.c, n⟩)
              have h_v : v = v0 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
              have h_vr : vr = ⟨c0.c, n⟩ := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
              refine ⟨c0, ?_, ?_⟩
              · simp [h_v]
              · simp [h_vr]
          | inr h_tail =>
              obtain ⟨c, h_mem', h_type⟩ := ih (n := n + 1) h_tail
              exact ⟨c, List.mem_cons_of_mem _ h_mem', h_type⟩

/-- Index bound: VRs in varMapOfFrameAux have index ≥ n. -/
theorem varMapOfFrameAux_idx_bound {n : Nat} {v : Variable} {vr : DeclarativeVR}
    {xs : List (Constant × Variable)} :
    (v, vr) ∈ varMapOfFrameAux n xs → vr.i ≥ n := by
  intro h_mem
  induction xs generalizing n with
  | nil => cases h_mem
  | cons cv rest ih =>
      simp only [varMapOfFrameAux, List.mem_cons] at h_mem
      cases h_mem with
      | inl h_eq =>
          -- vr = ⟨cv.1.c, n⟩
          have h_vr : vr = ⟨cv.1.c, n⟩ := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
          simp [h_vr]
      | inr h_tail =>
          have h_bound := ih (n := n + 1) h_tail
          omega

/-- Variables in varMapOfFrameAux have unique VRs when input has NoDup variables. -/
theorem varMapOfFrameAux_var_unique_nodup {n : Nat} {xs : List (Constant × Variable)}
    {v : Variable} {vr vr' : DeclarativeVR}
    (h_nodup : List.Nodup (xs.map Prod.snd))
    (h1 : (v, vr) ∈ varMapOfFrameAux n xs)
    (h2 : (v, vr') ∈ varMapOfFrameAux n xs) :
    vr = vr' := by
  induction xs generalizing n with
  | nil => cases h1
  | cons cv rest ih =>
      simp only [varMapOfFrameAux, List.mem_cons] at h1 h2
      simp only [List.map_cons, List.nodup_cons] at h_nodup
      obtain ⟨h_not_in, h_nodup_rest⟩ := h_nodup
      rcases h1 with h1_head | h1_tail
      · -- vr from head
        have h_vr := Prod.mk.inj h1_head
        rcases h2 with h2_head | h2_tail
        · -- Both from head
          have h_vr' := Prod.mk.inj h2_head
          rw [h_vr.2, h_vr'.2]
        · -- vr from head, vr' from tail
          -- But h_vr.1 says v = cv.2, and h_not_in says cv.2 ∉ rest.map Prod.snd
          -- h2_tail says (v, vr') ∈ varMapOfFrameAux (n+1) rest
          -- From soundness, v must be in rest.map Prod.snd
          exfalso
          have h_v_in_rest := mem_varMapAux_sound (n := n + 1) h2_tail
          obtain ⟨c', h_mem⟩ := h_v_in_rest
          have h_v_in_map : v ∈ rest.map Prod.snd := by
            simp only [List.mem_map]
            exact ⟨(c', v), h_mem, rfl⟩
          rw [h_vr.1] at h_v_in_map
          exact h_not_in h_v_in_map
      · -- vr from tail
        rcases h2 with h2_head | h2_tail
        · -- vr from tail, vr' from head
          exfalso
          have h_vr' := Prod.mk.inj h2_head
          have h_v_in_rest := mem_varMapAux_sound (n := n + 1) h1_tail
          obtain ⟨c', h_mem⟩ := h_v_in_rest
          have h_v_in_map : v ∈ rest.map Prod.snd := by
            simp only [List.mem_map]
            exact ⟨(c', v), h_mem, rfl⟩
          rw [h_vr'.1] at h_v_in_map
          exact h_not_in h_v_in_map
        · -- Both from tail
          exact ih h_nodup_rest h1_tail h2_tail

/-- Typed soundness for varMapOfFrame: membership gives floating hyp AND type match. -/
theorem mem_varMapOfFrame_sound_typed {fr : Frame} {v : Variable} {vr : DeclarativeVR} :
    (v, vr) ∈ varMapOfFrame fr → ∃ c, Hyp.floating c v ∈ fr.hyps ∧ vr.type = c.c := by
  intro h_mem
  unfold varMapOfFrame at h_mem
  obtain ⟨c, h_float, h_type⟩ := mem_varMapAux_sound_typed (n := 0) h_mem
  exact ⟨c, floatList_sound h_float, h_type⟩

theorem mem_varMapOfFrame_of_float {fr : Frame} {c : Constant} {v : Variable} :
    Hyp.floating c v ∈ fr.hyps → ∃ vr, (v, vr) ∈ varMapOfFrame fr := by
  intro h_in
  have h_float : (c, v) ∈ floatList fr := floatList_mem_of_float h_in
  exact mem_varMapAux_of_mem (n := 0) h_float

/-- Typed version: floating hypothesis gives entry with matching VR type. -/
theorem mem_varMapOfFrame_of_float_typed {fr : Frame} {c : Constant} {v : Variable} :
    Hyp.floating c v ∈ fr.hyps → ∃ vr, (v, vr) ∈ varMapOfFrame fr ∧ vr.type = c.c := by
  intro h_in
  have h_float : (c, v) ∈ floatList fr := floatList_mem_of_float h_in
  unfold varMapOfFrame
  exact mem_varMapAux_of_mem_typed (n := 0) h_float

/-- Floating hypotheses are always found in the typed variable map. -/
theorem findVR_of_float {fr : Frame} {c : Constant} {v : Variable} :
    Hyp.floating c v ∈ fr.hyps →
    ∃ vr, findVR (varMapOfFrame fr) v = some vr := by
  intro h_in
  obtain ⟨vr, h_mem⟩ := mem_varMapOfFrame_of_float (fr := fr) (c := c) (v := v) h_in
  exact findVR_some_of_mem h_mem

/-- Typed version: floating hypothesis gives findVR result with matching type.
    Requires FloatUnique to ensure the VR has the expected typecode. -/
theorem findVR_of_float_typed {fr : Frame} {c : Constant} {v : Variable}
    (h_unique : FloatUnique fr) :
    Hyp.floating c v ∈ fr.hyps →
    ∃ vr, findVR (varMapOfFrame fr) v = some vr ∧ vr.type = c.c := by
  intro h_in
  -- Get that some VR exists in the map for v
  obtain ⟨_, h_mem, _⟩ := mem_varMapOfFrame_of_float_typed h_in
  -- findVR returns some VR (possibly different from the one we have)
  obtain ⟨vr', h_findVR⟩ := findVR_some_of_mem h_mem
  -- From h_findVR, extract that (v, vr') ∈ varMapOfFrame fr
  have h_mem' : (v, vr') ∈ varMapOfFrame fr := findVR_mem_of_some h_findVR
  -- From membership, get the type info
  obtain ⟨c', h_float', h_type'⟩ := mem_varMapOfFrame_sound_typed h_mem'
  -- Use float uniqueness: c' = c since both are floats for variable v
  have h_c_eq : c' = c := h_unique c' c v h_float' h_in
  refine ⟨vr', h_findVR, ?_⟩
  rw [h_type', h_c_eq]

/-- For floating hypotheses with FloatUnique, declarativeSubstToSpec preserves the typecode. -/
theorem declarativeSubstToSpec_float_typecode {frAx : Frame} {vm : VarMap}
    {σ : DeclarativeVR → DeclarativeExpr} {c : Constant} {v : Variable}
    (h_unique : FloatUnique frAx)
    (h_float : Hyp.floating c v ∈ frAx.hyps) :
    (declarativeSubstToSpec (varMapOfFrame frAx) vm σ v).typecode = c := by
  let vmAx := varMapOfFrame frAx
  obtain ⟨vr, h_findVR, h_type_eq⟩ := findVR_of_float_typed h_unique h_float
  have h_tc := declarativeSubstToSpec_typecode (vm := vm) (σ := σ) h_findVR
  -- h_tc : (declarativeSubstToSpec vmAx vm σ v).typecode.c = vr.type
  -- h_type_eq : vr.type = c.c
  -- Goal: (declarativeSubstToSpec vmAx vm σ v).typecode = c
  -- Use Constant structure
  rcases hdef : (declarativeSubstToSpec (varMapOfFrame frAx) vm σ v).typecode with ⟨tc⟩
  rcases c with ⟨c_str⟩
  simp only [Spec.Constant.mk.injEq]
  -- Goal: tc = c_str
  -- hdef : (declarativeSubstToSpec ...).typecode = ⟨tc⟩
  -- So (declarativeSubstToSpec ...).typecode.c = tc
  have h_tc' : tc = vr.type := by
    have := congrArg Spec.Constant.c hdef
    simp only at this
    rw [← this, h_tc]
  rw [h_tc', h_type_eq]

/-- If a pair appears in varMapOfFrame, it came from a floating hypothesis. -/
theorem mem_varMapOfFrame_sound {fr : Frame} {v : Variable} {vr : DeclarativeVR} :
    (v, vr) ∈ varMapOfFrame fr → ∃ c, Hyp.floating c v ∈ fr.hyps := by
  intro h_mem
  -- Invert the map/enum structure.
  unfold varMapOfFrame at h_mem
  obtain ⟨c, h_float⟩ := mem_varMapAux_sound (n := 0) h_mem
  exact ⟨c, floatList_sound h_float⟩

/-- Variable-map domain matches the frame variable list. -/
def VarMapDomain (vm : VarMap) (vars : List Variable) : Prop :=
  ∀ v, v ∈ vars ↔ ∃ vr, findVR vm v = some vr

/-- varMapOfFrame has the expected domain (frame variables). -/
theorem varMapDomain_ofFrame (fr : Frame) :
    VarMapDomain (varMapOfFrame fr) fr.vars := by
  intro v
  constructor
  · intro h_mem
    obtain ⟨c, h_float⟩ := (var_mem_iff_float (fr := fr) (v := v)).1 h_mem
    exact findVR_of_float (fr := fr) (c := c) (v := v) h_float
  · intro h_find
    obtain ⟨vr, h_find'⟩ := h_find
    -- findVR success implies the variable occurs in the map
    have h_mem' : (v, vr) ∈ varMapOfFrame fr := by
      -- From findVR, extract a pair from the map
      classical
      unfold findVR at h_find'
      cases h_f : (varMapOfFrame fr).find? (fun p => p.1 = v) with
      | none =>
          simp [h_f] at h_find'
      | some p =>
          -- find? returned p with p.1 = v
          have h_p_mem : p ∈ varMapOfFrame fr := List.mem_of_find?_eq_some h_f
          have h_p_eq : p.1 = v := by
            have h_dec := List.find?_some (l := varMapOfFrame fr) (p := fun p => p.1 = v) h_f
            exact decide_eq_true_eq.mp h_dec
          -- Extract the second component from h_find'
          have h_p2 : p.2 = vr := by
            simp [h_f] at h_find'
            exact h_find'
          -- Rewrite p to (v, vr)
          cases p with
          | mk v' vr' =>
              simp at h_p_eq
              cases h_p_eq
              -- Now p = (v, vr')
              cases h_p2
              simpa using h_p_mem
    -- Now use soundness to get a floating hyp
    obtain ⟨c, h_float⟩ := mem_varMapOfFrame_sound (fr := fr) (v := v) (vr := vr) h_mem'
    exact (var_mem_iff_float (fr := fr) (v := v)).2 ⟨c, h_float⟩

/-- toDeclarativeSubst simplifies when findVar succeeds. -/
theorem toDeclarativeSubst_findVar {vmAx vm : VarMap} {σ : Subst} {vr : DeclarativeVR} {v : Variable}
    (h_find : findVar vmAx vr = some v) :
    toDeclarativeSubst vmAx vm σ vr = exprToDeclarativeExpr vm (σ v) := by
  unfold toDeclarativeSubst
  simp [h_find]

/-- toDeclarativeSubst is identity when findVar fails. -/
theorem toDeclarativeSubst_findVar_none {vmAx vm : VarMap} {σ : Subst} {vr : DeclarativeVR}
    (h_find : findVar vmAx vr = none) :
    toDeclarativeSubst vmAx vm σ vr = [Metamath.Sym.var vr] := by
  unfold toDeclarativeSubst
  simp [h_find]

/-- VRs in varMapOfFrameAux have indices starting from n and incrementing.
    This ensures uniqueness: no two entries have the same VR. -/
theorem varMapOfFrameAux_vr_index_ge {n : Nat} {xs : List (Constant × Variable)}
    {v : Variable} {vr : DeclarativeVR} :
    (v, vr) ∈ varMapOfFrameAux n xs → vr.i ≥ n := by
  intro h_mem
  induction xs generalizing n with
  | nil => cases h_mem
  | cons cv rest ih =>
      simp only [varMapOfFrameAux] at h_mem
      cases h_mem with
      | head =>
          -- vr = ⟨cv.fst.c, n⟩, so vr.i = n
          exact Nat.le_refl n
      | tail _ h_tail =>
          have h_ge := ih (n := n + 1) h_tail
          omega

/-- VRs in varMapOfFrameAux are unique: if (v, vr) ∈ aux and (v', vr) ∈ aux, then v = v'. -/
theorem varMapOfFrameAux_vr_unique {n : Nat} {xs : List (Constant × Variable)}
    {v v' : Variable} {vr : DeclarativeVR} :
    (v, vr) ∈ varMapOfFrameAux n xs → (v', vr) ∈ varMapOfFrameAux n xs → v = v' := by
  intro h_mem1 h_mem2
  induction xs generalizing n v v' vr with
  | nil => cases h_mem1
  | cons cv rest ih =>
      simp only [varMapOfFrameAux, List.mem_cons] at h_mem1 h_mem2
      cases h_mem1 with
      | inl h_eq1 =>
          -- (v, vr) = (cv.snd, ⟨cv.fst.c, n⟩)
          cases h_mem2 with
          | inl h_eq2 =>
              -- Both equal to head, so v = v'
              have := Prod.mk.inj h_eq1
              have := Prod.mk.inj h_eq2
              simp_all
          | inr h_tail2 =>
              -- From h_eq1: vr = ⟨cv.fst.c, n⟩, so vr.i = n
              -- From h_tail2: vr.i ≥ n + 1 (contradiction)
              have h_vr : vr = ⟨cv.fst.c, n⟩ := (Prod.mk.inj h_eq1).2
              have h_ge := varMapOfFrameAux_vr_index_ge (n := n + 1) h_tail2
              simp only [h_vr] at h_ge
              omega
      | inr h_tail1 =>
          cases h_mem2 with
          | inl h_eq2 =>
              -- From h_eq2: vr = ⟨cv.fst.c, n⟩, so vr.i = n
              -- From h_tail1: vr.i ≥ n + 1 (contradiction)
              have h_vr : vr = ⟨cv.fst.c, n⟩ := (Prod.mk.inj h_eq2).2
              have h_ge := varMapOfFrameAux_vr_index_ge (n := n + 1) h_tail1
              simp only [h_vr] at h_ge
              omega
          | inr h_tail2 =>
              exact ih h_tail1 h_tail2

/-- VRs in varMapOfFrame are unique. -/
theorem varMapOfFrame_vr_unique {fr : Frame} {v v' : Variable} {vr : DeclarativeVR} :
    (v, vr) ∈ varMapOfFrame fr → (v', vr) ∈ varMapOfFrame fr → v = v' := by
  unfold varMapOfFrame
  exact varMapOfFrameAux_vr_unique (n := 0)

/-- Key inverse lemma: if findVR vm v = some vr, then findVar vm vr = some v.
    This follows from uniqueness of VRs in the VarMap. -/
theorem findVR_findVar_inverse {vm : VarMap} {v : Variable} {vr : DeclarativeVR}
    (h_unique : ∀ v' v'' vr', (v', vr') ∈ vm → (v'', vr') ∈ vm → v' = v'')
    (h_findVR : findVR vm v = some vr) :
    findVar vm vr = some v := by
  unfold findVR at h_findVR
  unfold findVar
  -- From h_findVR, extract the pair p with p.1 = v and p.2 = vr
  match h_find : vm.find? (fun p => p.1 = v) with
  | none =>
      -- Contradiction: findVR returns none but h_findVR says some
      simp only [h_find, Option.map] at h_findVR
      cases h_findVR
  | some p =>
      simp only [h_find, Option.map, Option.some.injEq] at h_findVR
      -- h_findVR : p.2 = vr
      have h_p_mem : p ∈ vm := List.mem_of_find?_eq_some h_find
      have h_p_eq : p.1 = v := by
        have := List.find?_some h_find
        exact decide_eq_true_eq.mp this
      -- Get (v, vr) ∈ vm from p by showing p = (v, vr)
      have h_p_is : p = (v, vr) := Prod.ext h_p_eq h_findVR
      -- Find q with q.2 = vr
      match h_find' : vm.find? (fun q => q.2 = vr) with
      | none =>
          -- Contradiction: (v, vr) ∈ vm but find? says none
          have h_none := List.find?_eq_none.mp h_find'
          rw [h_p_is] at h_p_mem
          have h_false := h_none (v, vr) h_p_mem
          simp at h_false
      | some q =>
          -- Goal is Option.map Prod.fst (some q) = some v
          simp only [h_find', Option.map, Option.some.injEq]
          -- q.2 = vr
          have h_q_mem : q ∈ vm := List.mem_of_find?_eq_some h_find'
          have h_q_eq : q.2 = vr := by
            have := List.find?_some h_find'
            exact decide_eq_true_eq.mp this
          -- Now (q.1, vr) ∈ vm and (v, vr) ∈ vm
          have h_q_is : q = (q.1, vr) := Prod.ext rfl h_q_eq
          rw [h_q_is] at h_q_mem
          rw [h_p_is] at h_p_mem
          -- By uniqueness: q.1 = v
          exact h_unique q.1 v vr h_q_mem h_p_mem

/-- Specialized inverse lemma for varMapOfFrame. -/
theorem findVR_findVar_inverse_frame {fr : Frame} {v : Variable} {vr : DeclarativeVR}
    (h_findVR : findVR (varMapOfFrame fr) v = some vr) :
    findVar (varMapOfFrame fr) vr = some v := by
  apply findVR_findVar_inverse
  · -- Uniqueness from varMapOfFrame_vr_unique
    intro v' v'' vr' h1 h2
    exact varMapOfFrame_vr_unique h1 h2
  · exact h_findVR

/-! ## Roundtrip Lemmas

These show the forward and inverse conversions are consistent.
-/

/-- Roundtrip for symbols: fromDeclarativeSym inverts toDeclarativeSym for frame-based maps. -/
theorem fromDeclarativeSym_toDeclarativeSym_frame {fr : Frame} {s : Sym} :
    fromDeclarativeSym (varMapOfFrame fr) (toDeclarativeSym (varMapOfFrame fr) s) = s := by
  let vm := varMapOfFrame fr
  simp only [fromDeclarativeSym, toDeclarativeSym]
  match h_find : findVR vm ⟨s⟩ with
  | none =>
      -- s is a constant, toDeclarativeSym returns .const s
      rfl
  | some vr =>
      -- s is a variable, toDeclarativeSym returns .var vr
      -- findVar vm vr should return ⟨s⟩
      have h_inv := findVR_findVar_inverse_frame h_find
      simp only [h_inv]

/-- Roundtrip for expressions: fromDeclarativeExpr inverts exprToDeclarativeExpr. -/
theorem fromDeclarativeExpr_exprToDeclarativeExpr_frame {fr : Frame} {syms : List Sym} :
    fromDeclarativeExpr (varMapOfFrame fr) (syms.map (toDeclarativeSym (varMapOfFrame fr))) = syms := by
  unfold fromDeclarativeExpr
  rw [List.map_map]
  -- Goal: (fromDeclarativeSym vm ∘ toDeclarativeSym vm) applied to each = id
  have h : fromDeclarativeSym (varMapOfFrame fr) ∘ toDeclarativeSym (varMapOfFrame fr) = id := by
    funext s
    exact fromDeclarativeSym_toDeclarativeSym_frame
  rw [h, List.map_id]

/-- Roundtrip for formulas: fromDeclarativeFormula inverts exprToFormula. -/
theorem fromDeclarativeFormula_exprToFormula_frame {fr : Frame} {e : Expr} :
    fromDeclarativeFormula (varMapOfFrame fr) (exprToFormula (varMapOfFrame fr) e) = e := by
  rcases e with ⟨⟨tc⟩, syms⟩
  simp only [fromDeclarativeFormula, exprToFormula, exprToDeclarativeExpr,
             fromDeclarativeExpr_exprToDeclarativeExpr_frame]

/-- Inverse of findVR_findVar_inverse: if findVar succeeds, findVR succeeds.
    This requires that VRs map to unique variables. -/
theorem findVar_findVR_inverse {vm : VarMap} {v : Variable} {vr : DeclarativeVR}
    (h_var_unique : ∀ v' vr' vr'', (v', vr') ∈ vm → (v', vr'') ∈ vm → vr' = vr'')
    (h_findVar : findVar vm vr = some v) :
    findVR vm v = some vr := by
  unfold findVar at h_findVar
  match h_f : vm.find? (fun p => p.2 = vr) with
  | none =>
      simp only [h_f, Option.map] at h_findVar
      cases h_findVar
  | some p =>
      simp only [h_f, Option.map, Option.some.injEq] at h_findVar
      -- h_findVar : p.1 = v
      have h_p_mem : p ∈ vm := List.mem_of_find?_eq_some h_f
      have h_p_vr : p.2 = vr := by
        have := List.find?_some h_f
        exact decide_eq_true_eq.mp this
      -- p = (v, vr)
      have h_p_is : p = (v, vr) := Prod.ext h_findVar h_p_vr
      rw [h_p_is] at h_p_mem
      -- (v, vr) ∈ vm, so findVR should find it
      unfold findVR
      match h_f' : vm.find? (fun q => q.1 = v) with
      | none =>
          exfalso
          have h_none := List.find?_eq_none.mp h_f'
          have := h_none (v, vr) h_p_mem
          simp at this
      | some q =>
          simp only [Option.map, h_f']
          have h_q_mem : q ∈ vm := List.mem_of_find?_eq_some h_f'
          have h_q_v : q.1 = v := by
            have := List.find?_some h_f'
            exact decide_eq_true_eq.mp this
          -- q = (v, q.2) and (v, vr) ∈ vm
          -- By variable uniqueness, q.2 = vr
          have h_q_is : q = (v, q.2) := Prod.ext h_q_v rfl
          rw [h_q_is] at h_q_mem
          have h_vr_eq := h_var_unique v q.2 vr h_q_mem h_p_mem
          simp [h_vr_eq]

/-- Specialized inverse for varMapOfFrame: each variable maps to exactly one VR.
    Requires FloatVarNoDup to ensure each variable appears at most once in the varmap. -/
theorem findVar_findVR_inverse_frame {fr : Frame} {v : Variable} {vr : DeclarativeVR}
    (h_nodup : FloatVarNoDup fr)
    (h_findVar : findVar (varMapOfFrame fr) vr = some v) :
    findVR (varMapOfFrame fr) v = some vr := by
  apply findVar_findVR_inverse
  · -- VR uniqueness: each variable maps to at most one VR in varMapOfFrame
    intro v' vr' vr'' h1 h2
    unfold varMapOfFrame at h1 h2
    exact varMapOfFrameAux_var_unique_nodup h_nodup h1 h2
  · exact h_findVar

/-- Reverse roundtrip for symbols: toDeclarativeSym inverts fromDeclarativeSym for VRs in the map.
    If findVar vm vr = some v, then toDeclarativeSym vm (fromDeclarativeSym vm (.var vr)) = .var vr. -/
theorem toDeclarativeSym_fromDeclarativeSym_var {fr : Frame} {vr : DeclarativeVR} {v : Variable}
    (h_nodup : FloatVarNoDup fr)
    (h_find : findVar (varMapOfFrame fr) vr = some v) :
    toDeclarativeSym (varMapOfFrame fr) (fromDeclarativeSym (varMapOfFrame fr) (.var vr)) =
    Metamath.Sym.var vr := by
  simp only [fromDeclarativeSym, h_find, toDeclarativeSym]
  have h_inv := findVar_findVR_inverse_frame h_nodup h_find
  simp only [h_inv]

/-- Reverse roundtrip: exprToDeclarativeExpr inverts fromDeclarativeExpr for well-formed expressions.
    A Mario expression is well-formed w.r.t. a frame if all its VRs are in the VarMap. -/
def DeclarativeExprWellFormed (fr : Frame) (me : DeclarativeExpr) : Prop :=
  ∀ vr, vr ∈' me → ∃ v, findVar (varMapOfFrame fr) vr = some v

/-- Constants in a Mario expression don't clash with variable names in the frame.
    This is guaranteed by Metamath's global separation of constants and variables. -/
def DeclarativeExprConstSeparated (fr : Frame) (me : DeclarativeExpr) : Prop :=
  ∀ s, Metamath.Sym.const s ∈ me → findVR (varMapOfFrame fr) ⟨s⟩ = none

theorem exprToDeclarativeExpr_fromDeclarativeExpr_wellFormed {fr : Frame} {me : DeclarativeExpr}
    (h_nodup : FloatVarNoDup fr)
    (h_wf : DeclarativeExprWellFormed fr me)
    (h_sep : DeclarativeExprConstSeparated fr me) :
    (fromDeclarativeExpr (varMapOfFrame fr) me).map (toDeclarativeSym (varMapOfFrame fr)) = me := by
  let vm := varMapOfFrame fr
  unfold fromDeclarativeExpr
  rw [List.map_map]
  induction me with
  | nil => rfl
  | cons sym rest ih =>
      simp only [List.map_cons]
      congr 1
      · -- Head: toDeclarativeSym vm (fromDeclarativeSym vm sym) = sym
        cases sym with
        | const c =>
            -- Constants: use separation to show findVR returns none
            simp only [Function.comp_apply, fromDeclarativeSym, toDeclarativeSym]
            have h_const_mem : Metamath.Sym.const c ∈ (Metamath.Sym.const c :: rest) :=
              List.Mem.head rest
            have h_none := h_sep c h_const_mem
            simp only [h_none]
        | var vr' =>
            -- Variables: use the helper lemma
            simp only [Function.comp_apply]
            have h_mem : vr' ∈' (Metamath.Sym.var vr' :: rest) := by
              unfold Metamath.Expr.mem
              exact .head ..
            obtain ⟨v', h_findVar⟩ := h_wf vr' h_mem
            exact toDeclarativeSym_fromDeclarativeSym_var h_nodup h_findVar
      · -- Tail: apply IH
        have h_wf_tail : DeclarativeExprWellFormed fr rest := fun vr' h_mem =>
          h_wf vr' (by unfold Metamath.Expr.mem at h_mem ⊢; exact List.mem_cons_of_mem _ h_mem)
        have h_sep_tail : DeclarativeExprConstSeparated fr rest := fun s h_mem =>
          h_sep s (List.mem_cons_of_mem _ h_mem)
        exact ih h_wf_tail h_sep_tail

/-- Substitution roundtrip: toDeclarativeSubst inverts declarativeSubstToSpec on VRs in the axiom frame.
    When σ is a Mario substitution, and vr is a VR from vmAx with findVar vmAx vr = some v,
    then toDeclarativeSubst vmAx vm (declarativeSubstToSpec vmAx vm σ) vr = σ vr
    provided σ vr is well-formed with respect to vm. -/
theorem toDeclarativeSubst_declarativeSubstToSpec_roundtrip {frAx fr : Frame} {σ : DeclarativeVR → DeclarativeExpr}
    {vr : DeclarativeVR} {v : Variable}
    (h_nodup_ax : FloatVarNoDup frAx)
    (h_nodup : FloatVarNoDup fr)
    (h_findVar : findVar (varMapOfFrame frAx) vr = some v)
    (h_wf : DeclarativeExprWellFormed fr (σ vr))
    (h_sep : DeclarativeExprConstSeparated fr (σ vr)) :
    toDeclarativeSubst (varMapOfFrame frAx) (varMapOfFrame fr)
                 (declarativeSubstToSpec (varMapOfFrame frAx) (varMapOfFrame fr) σ) vr = σ vr := by
  let vmAx := varMapOfFrame frAx
  let vm := varMapOfFrame fr
  let σ' := declarativeSubstToSpec vmAx vm σ
  -- toDeclarativeSubst vmAx vm σ' vr = exprToDeclarativeExpr vm (σ' v) when findVar succeeds
  simp only [toDeclarativeSubst, h_findVar]
  -- σ' v = declarativeSubstToSpec vmAx vm σ v
  -- Since findVar vmAx vr = some v, by inverse lemma findVR vmAx v = some vr
  have h_findVR := findVar_findVR_inverse_frame h_nodup_ax h_findVar
  -- declarativeSubstToSpec vmAx vm σ v = ⟨vr.type, fromDeclarativeExpr vm (σ vr)⟩
  simp only [declarativeSubstToSpec, h_findVR]
  -- exprToDeclarativeExpr vm ⟨⟨vr.type⟩, fromDeclarativeExpr vm (σ vr)⟩
  -- = (fromDeclarativeExpr vm (σ vr)).map (toDeclarativeSym vm)
  simp only [exprToDeclarativeExpr]
  -- Apply the reverse roundtrip
  exact exprToDeclarativeExpr_fromDeclarativeExpr_wellFormed h_nodup h_wf h_sep

/-- Substitution extensionality: if two substitutions agree on all VRs in an expression,
    they produce the same result. -/
theorem Expr_subst_ext {σ₁ σ₂ : DeclarativeVR → DeclarativeExpr} :
    {e : DeclarativeExpr} →
    (∀ vr, vr ∈' e → σ₁ vr = σ₂ vr) →
    e.subst σ₁ = e.subst σ₂
  | [], _ => rfl
  | Metamath.Sym.const c :: rest, h_ext => by
      simp only [Metamath.Expr.subst]
      congr 1
      exact Expr_subst_ext fun vr h_mem =>
        h_ext vr (List.Mem.tail _ h_mem)
  | Metamath.Sym.var vr :: rest, h_ext => by
      simp only [Metamath.Expr.subst]
      have h_head := h_ext vr (List.Mem.head _)
      have h_tail := Expr_subst_ext fun vr' h_mem =>
        h_ext vr' (List.Mem.tail _ h_mem)
      rw [h_head, h_tail]

/-- If findVar succeeds, the pair is in the map. -/
theorem findVar_mem_of_some {vm : VarMap} {vr : DeclarativeVR} {v : Variable}
    (h_find : findVar vm vr = some v) :
    (v, vr) ∈ vm := by
  unfold findVar at h_find
  -- h_find : (vm.find? fun p => p.2 = vr).map Prod.fst = some v
  match h_f : vm.find? (fun p => p.2 = vr) with
  | none =>
      simp only [h_f, Option.map] at h_find
      cases h_find
  | some p =>
      simp only [h_f, Option.map, Option.some.injEq] at h_find
      -- h_find : p.1 = v
      have h_p_mem : p ∈ vm := List.mem_of_find?_eq_some h_f
      have h_p_eq : p.2 = vr := by
        have := List.find?_some h_f
        exact decide_eq_true_eq.mp this
      -- p = (v, vr)
      have h_p_is : p = (v, vr) := Prod.ext h_find h_p_eq
      rw [h_p_is] at h_p_mem
      exact h_p_mem

/-- Variables in floatList are exactly Frame.vars. -/
theorem floatList_map_snd_eq_vars (fr : Frame) :
    (floatList fr).map Prod.snd = fr.vars := by
  unfold floatList Frame.vars
  induction fr.hyps with
  | nil => rfl
  | cons h rest ih =>
      match h with
      | Hyp.floating c v =>
          simp only [List.filterMap_cons, List.map_cons]
          exact congrArg (v :: ·) ih
      | Hyp.essential _ =>
          simp only [List.filterMap_cons]
          exact ih

/-- Variables in varMapOfFrameAux are from the second component of the input list. -/
theorem varMapOfFrameAux_vars {n : Nat} {xs : List (Constant × Variable)} {v : Variable} :
    (∃ vr, (v, vr) ∈ varMapOfFrameAux n xs) ↔ v ∈ xs.map Prod.snd := by
  induction xs generalizing n with
  | nil =>
      simp only [varMapOfFrameAux, List.map_nil, List.mem_nil_iff]
      constructor
      · intro ⟨_, h⟩; cases h
      · intro h; cases h
  | cons cv rest ih =>
      simp only [varMapOfFrameAux, List.map_cons, List.mem_cons]
      constructor
      · intro ⟨vr, h_mem⟩
        cases h_mem with
        | inl h_eq =>
            left
            exact (Prod.mk.inj h_eq).1
        | inr h_tail =>
            right
            exact ih.mp ⟨vr, h_tail⟩
      · intro h_or
        cases h_or with
        | inl h_eq =>
            subst h_eq
            exact ⟨⟨cv.fst.c, n⟩, Or.inl rfl⟩
        | inr h_mem =>
            obtain ⟨vr, h_vr_mem⟩ := ih.mpr h_mem
            exact ⟨vr, Or.inr h_vr_mem⟩

/-- If findVR succeeds for varMapOfFrame, the variable is in Frame.vars. -/
theorem findVR_in_vars {fr : Frame} {v : Variable} {vr : DeclarativeVR}
    (h : findVR (varMapOfFrame fr) v = some vr) :
    v ∈ fr.vars := by
  unfold findVR at h
  match h_find : (varMapOfFrame fr).find? (fun p => p.1 = v) with
  | none =>
      simp only [h_find, Option.map] at h
      cases h
  | some p =>
      simp only [h_find, Option.map, Option.some.injEq] at h
      have h_p_mem : p ∈ varMapOfFrame fr := List.mem_of_find?_eq_some h_find
      have h_p_eq : p.1 = v := by
        have := List.find?_some h_find
        exact decide_eq_true_eq.mp this
      -- (p.1, p.2) ∈ varMapOfFrame fr, and p.1 = v
      have h_v_in_aux : v ∈ (floatList fr).map Prod.snd := by
        have h_mem' : ∃ vr', (v, vr') ∈ varMapOfFrame fr := by
          refine ⟨p.2, ?_⟩
          have h_p_is : p = (v, p.2) := Prod.ext h_p_eq rfl
          rw [h_p_is] at h_p_mem
          exact h_p_mem
        unfold varMapOfFrame at h_mem'
        rwa [varMapOfFrameAux_vars] at h_mem'
      rw [floatList_map_snd_eq_vars] at h_v_in_aux
      exact h_v_in_aux

/-- Extract the source symbol from membership in exprToDeclarativeExpr.
    If vr ∈' exprToDeclarativeExpr vm e, then there exists a symbol s in e.syms
    such that findVR vm (Variable.mk s) = some vr. -/
theorem exprToDeclarativeExpr_mem_extract {vm : VarMap} {e : Expr} {vr : DeclarativeVR}
    (h_mem : vr ∈' exprToDeclarativeExpr vm e) :
    ∃ s, s ∈ e.syms ∧ findVR vm (Variable.mk s) = some vr := by
  -- h_mem : Metamath.Expr.mem (exprToDeclarativeExpr vm e) vr
  -- = Metamath.Sym.var vr ∈ e.syms.map (fun s => toDeclarativeSym vm s)
  unfold exprToDeclarativeExpr at h_mem
  unfold Metamath.Expr.mem at h_mem
  -- h_mem : Metamath.Sym.var vr ∈ List.map (toDeclarativeSym vm) e.syms
  obtain ⟨s, h_s_in, h_s_eq⟩ := List.mem_map.mp h_mem
  -- h_s_eq : toDeclarativeSym vm s = Metamath.Sym.var vr
  unfold toDeclarativeSym at h_s_eq
  match h_find : findVR vm (Variable.mk s) with
  | some vr' =>
      simp only [h_find] at h_s_eq
      have h_vr_eq := Metamath.Sym.var.inj h_s_eq
      subst h_vr_eq
      exact ⟨s, h_s_in, h_find⟩
  | none =>
      simp only [h_find] at h_s_eq
      -- h_s_eq : Metamath.Sym.const s = Metamath.Sym.var vr, contradiction
      cases h_s_eq

/-- findVR is injective for VarMaps with unique VRs: if two variables map to the same VR,
    they must be the same variable. -/
theorem findVR_injective {vm : VarMap}
    (h_unique : ∀ v' v'' vr', (v', vr') ∈ vm → (v'', vr') ∈ vm → v' = v'')
    {v1 v2 : Variable} {vr : DeclarativeVR}
    (h_v1 : findVR vm v1 = some vr)
    (h_v2 : findVR vm v2 = some vr) :
    v1 = v2 := by
  unfold findVR at h_v1 h_v2
  -- Extract the pairs from the find? results
  match h_find1 : vm.find? (fun p => p.1 = v1) with
  | none =>
      simp only [h_find1, Option.map] at h_v1
      cases h_v1
  | some p1 =>
      simp only [h_find1, Option.map, Option.some.injEq] at h_v1
      match h_find2 : vm.find? (fun p => p.1 = v2) with
      | none =>
          simp only [h_find2, Option.map] at h_v2
          cases h_v2
      | some p2 =>
          simp only [h_find2, Option.map, Option.some.injEq] at h_v2
          -- h_v1 : p1.2 = vr, h_v2 : p2.2 = vr
          have h_p1_mem : p1 ∈ vm := List.mem_of_find?_eq_some h_find1
          have h_p2_mem : p2 ∈ vm := List.mem_of_find?_eq_some h_find2
          have h_p1_eq : p1.1 = v1 := by
            have := List.find?_some h_find1
            exact decide_eq_true_eq.mp this
          have h_p2_eq : p2.1 = v2 := by
            have := List.find?_some h_find2
            exact decide_eq_true_eq.mp this
          -- p1 = (v1, vr), p2 = (v2, vr)
          have h_p1_is : p1 = (v1, vr) := Prod.ext h_p1_eq h_v1
          have h_p2_is : p2 = (v2, vr) := Prod.ext h_p2_eq h_v2
          rw [h_p1_is] at h_p1_mem
          rw [h_p2_is] at h_p2_mem
          exact h_unique v1 v2 vr h_p1_mem h_p2_mem

/-- findVR is injective for varMapOfFrame. -/
theorem findVR_injective_frame {fr : Frame} {v1 v2 : Variable} {vr : DeclarativeVR}
    (h_v1 : findVR (varMapOfFrame fr) v1 = some vr)
    (h_v2 : findVR (varMapOfFrame fr) v2 = some vr) :
    v1 = v2 :=
  findVR_injective (fun _ _ _ h1 h2 => varMapOfFrame_vr_unique h1 h2) h_v1 h_v2

/-- toDeclarativeSym is injective for varMapOfFrame.
    Key cases:
    - Both const: trivially equal
    - Both var: by findVR_injective_frame
    - Mixed: impossible since .const ≠ .var -/
theorem toDeclarativeSym_inj_frame {fr : Frame} {s1 s2 : String}
    (h_eq : toDeclarativeSym (varMapOfFrame fr) s1 = toDeclarativeSym (varMapOfFrame fr) s2) :
    s1 = s2 := by
  let vm := varMapOfFrame fr
  let v1 : Variable := ⟨s1⟩
  let v2 : Variable := ⟨s2⟩
  -- Unfold toDeclarativeSym to see the match structure
  simp only [toDeclarativeSym] at h_eq
  -- Split on findVR results
  generalize h_find1 : findVR vm v1 = r1 at h_eq
  generalize h_find2 : findVR vm v2 = r2 at h_eq
  match r1, r2 with
  | none, none =>
      -- Both const: .const s1 = .const s2
      exact Metamath.Sym.const.inj h_eq
  | none, some vr2 =>
      -- .const s1 = .var vr2, contradiction
      cases h_eq
  | some vr1, none =>
      -- .var vr1 = .const s2, contradiction
      cases h_eq
  | some vr1, some vr2 =>
      -- .var vr1 = .var vr2
      have h_vr_eq := Metamath.Sym.var.inj h_eq
      rw [h_vr_eq] at h_find1
      have h_v_eq := findVR_injective_frame h_find1 h_find2
      exact congrArg Variable.v h_v_eq

/-- If two symbol lists have equal Mario expressions, the original lists are equal. -/
theorem exprToDeclarativeExpr_syms_inj_frame {fr : Frame} {syms1 syms2 : List String}
    (h_eq : syms1.map (toDeclarativeSym (varMapOfFrame fr)) = syms2.map (toDeclarativeSym (varMapOfFrame fr))) :
    syms1 = syms2 := by
  -- Induct on syms1 with generalized syms2
  induction syms1 generalizing syms2 with
  | nil =>
      -- syms1 = [], so syms2.map ... = [] means syms2 = []
      simp only [List.map_nil] at h_eq
      exact (List.map_eq_nil_iff.mp h_eq.symm).symm
  | cons s1 rest1 ih =>
      -- syms1 = s1 :: rest1
      cases syms2 with
      | nil =>
          -- syms2 = [] but syms1 ≠ [], contradiction
          simp only [List.map_nil, List.map_cons] at h_eq
          cases h_eq
      | cons s2 rest2 =>
          -- Both have heads: (s1 :: rest1).map = (s2 :: rest2).map
          simp only [List.map_cons, List.cons.injEq] at h_eq
          have h_head := toDeclarativeSym_inj_frame h_eq.1
          have h_tail := ih h_eq.2
          simp only [h_head, h_tail]

/-- Full expression equality from formula equality (for varMapOfFrame). -/
theorem exprToFormula_eq_of_eq_frame {fr : Frame} {e e' : Expr}
    (h_eq : exprToFormula (varMapOfFrame fr) e = exprToFormula (varMapOfFrame fr) e') :
    e = e' := by
  -- Unpack formula equality
  unfold exprToFormula at h_eq
  have h := Prod.mk.inj h_eq
  -- h.1 : e.typecode.c = e'.typecode.c
  -- h.2 : exprToDeclarativeExpr vm e = exprToDeclarativeExpr vm e'
  unfold exprToDeclarativeExpr at h
  have h_syms := exprToDeclarativeExpr_syms_inj_frame h.2
  -- h_syms : e.syms = e'.syms
  have h_tc : e.typecode = e'.typecode := by
    cases he : e.typecode
    cases he' : e'.typecode
    simp only [he, he'] at h
    simp only [h.1]
  -- Construct expression equality
  cases e
  cases e'
  simp only at h_tc h_syms
  simp only [h_tc, h_syms]

/-- Lift dvRel to dvListToDeclarativeDJ: if v and w are disjoint via dvRel, and both
    map to VRs via findVR, then the VRs are disjoint in dvListToDeclarativeDJ.
    Requires variable-to-VR uniqueness: different variables map to different VRs. -/
theorem dvRel_to_dvListToDeclarativeDJ {vm : VarMap} {dv : List (Variable × Variable)}
    {v w : Variable} {vr1 vr2 : DeclarativeVR}
    (h_unique : ∀ v' v'' vr', findVR vm v' = some vr' → findVR vm v'' = some vr' → v' = v'')
    (h_dvRel : Spec.dvRel dv v w)
    (h_v : findVR vm v = some vr1)
    (h_w : findVR vm w = some vr2) :
    (dvListToDeclarativeDJ vm dv).disj vr1 vr2 := by
  unfold Spec.dvRel at h_dvRel
  obtain ⟨h_neq, h_mem_or⟩ := h_dvRel
  unfold dvListToDeclarativeDJ
  simp only [Metamath.DJ.mk']
  constructor
  · -- vr1 ≠ vr2 follows from v ≠ w and injectivity via h_unique
    intro h_vr_eq
    rw [h_vr_eq] at h_v
    -- Now h_v : findVR vm v = some vr2, h_w : findVR vm w = some vr2
    have h_eq := h_unique v w vr2 h_v h_w
    exact h_neq h_eq
  · cases h_mem_or with
    | inl h_fwd =>
        -- (v, w) ∈ dv
        left
        apply List.mem_filterMap.mpr
        exact ⟨(v, w), h_fwd, by simp only [h_v, h_w]⟩
    | inr h_rev =>
        -- (w, v) ∈ dv
        right
        apply List.mem_filterMap.mpr
        exact ⟨(w, v), h_rev, by simp only [h_w, h_v]⟩

/-- Inverse of dvRel_to_dvListToDeclarativeDJ: extract dvRel from dvListToDeclarativeDJ membership.
    If two VRs are disjoint in dvListToDeclarativeDJ (constructed from a frame) and both map
    back to variables via findVar, then those variables satisfy dvRel.

    This is parametrized by a Frame (not generic VarMap) to enable use of
    findVR_findVar_inverse_frame which provides the required uniqueness properties. -/
theorem dvListToDeclarativeDJ_to_dvRel {fr : Frame} {dv : List (Variable × Variable)}
    {vr1 vr2 : DeclarativeVR} {v1 v2 : Variable}
    (h_disj : (dvListToDeclarativeDJ (varMapOfFrame fr) dv).disj vr1 vr2)
    (h_v1 : findVar (varMapOfFrame fr) vr1 = some v1)
    (h_v2 : findVar (varMapOfFrame fr) vr2 = some v2) :
    Spec.dvRel dv v1 v2 := by
  let vm := varMapOfFrame fr
  unfold dvListToDeclarativeDJ at h_disj
  simp only [Metamath.DJ.mk'] at h_disj
  obtain ⟨h_vr_neq, h_mem_or⟩ := h_disj
  -- h_vr_neq : vr1 ≠ vr2
  -- h_mem_or : (vr1, vr2) or (vr2, vr1) is in the filterMap result
  unfold Spec.dvRel
  constructor
  · -- v1 ≠ v2 follows from vr1 ≠ vr2 and findVar giving different results
    intro h_v_eq
    cases h_v_eq
    -- Now v1 = v2, so both findVar vm vr1 = some v1 and findVar vm vr2 = some v1
    -- If (vr1, vr2) came from filterMap, there's a (v, w) in dv that produced them
    cases h_mem_or with
    | inl h_fwd =>
        obtain ⟨⟨v, w⟩, h_vw_in, h_eq⟩ := List.mem_filterMap.mp h_fwd
        simp only [] at h_eq
        match h_fv : findVR vm v, h_fw : findVR vm w with
        | some vr_v, some vr_w =>
            rw [h_fv, h_fw] at h_eq
            have h_eq' := Option.some.inj h_eq
            -- h_eq' : (vr_v, vr_w) = (vr1, vr2)
            -- Extract component equalities
            have h_vr1 : vr_v = vr1 := congrArg Prod.fst h_eq'
            have h_vr2 : vr_w = vr2 := congrArg Prod.snd h_eq'
            -- By inverse, findVar vm vr_v = some v and findVar vm vr_w = some w
            have h_findVar_v := findVR_findVar_inverse_frame h_fv
            have h_findVar_w := findVR_findVar_inverse_frame h_fw
            -- Rewrite h_v1, h_v2 to use vr_v, vr_w
            rw [← h_vr1] at h_v1
            rw [← h_vr2] at h_v2
            -- Now: h_v1 : findVar vm vr_v = some v1, h_findVar_v : findVar vm vr_v = some v
            -- Also: h_v2 : findVar vm vr_w = some v1 (note: v2 was substituted to v1 by cases h_v_eq)
            -- h_findVar_w : findVar vm vr_w = some w
            -- So v = v1 and w = v1 (since v2 is now v1), meaning v = w
            have h_v_eq_v1 := Option.some.inj (h_findVar_v.symm.trans h_v1)
            have h_w_eq_v1 := Option.some.inj (h_findVar_w.symm.trans h_v2)
            have h_vw_eq : v = w := h_v_eq_v1.trans h_w_eq_v1.symm
            -- From h_fv : findVR vm v = some vr_v and h_fw : findVR vm w = some vr_w
            -- With v = w: findVR vm v = some vr_v = findVR vm v = some vr_w, so vr_v = vr_w
            have h_vr_vw_eq : vr_v = vr_w := Option.some.inj (h_fv.symm.trans (h_vw_eq ▸ h_fw))
            exact h_vr_neq (h_vr1.symm.trans (h_vr_vw_eq.trans h_vr2))
        | some _, none =>
            rw [h_fv, h_fw] at h_eq
            cases h_eq
        | none, _ =>
            rw [h_fv] at h_eq
            cases h_eq
    | inr h_rev =>
        obtain ⟨⟨v, w⟩, h_vw_in, h_eq⟩ := List.mem_filterMap.mp h_rev
        simp only [] at h_eq
        match h_fv : findVR vm v, h_fw : findVR vm w with
        | some vr_v, some vr_w =>
            rw [h_fv, h_fw] at h_eq
            have h_eq' := Option.some.inj h_eq
            -- h_eq' : (vr_v, vr_w) = (vr2, vr1) (membership is from reversed pair list)
            -- So vr_v = vr2 and vr_w = vr1
            have h_vr2 : vr_v = vr2 := congrArg Prod.fst h_eq'
            have h_vr1 : vr_w = vr1 := congrArg Prod.snd h_eq'
            -- By inverse, findVar vm vr_v = some v and findVar vm vr_w = some w
            have h_findVar_v := findVR_findVar_inverse_frame h_fv
            have h_findVar_w := findVR_findVar_inverse_frame h_fw
            -- Rewrite h_v1, h_v2 to use vr_w, vr_v
            rw [← h_vr1] at h_v1
            rw [← h_vr2] at h_v2
            -- Now: h_v1 : findVar vm vr_w = some v1, h_findVar_w : findVar vm vr_w = some w
            -- Also: h_v2 : findVar vm vr_v = some v1 (v2 was substituted to v1)
            -- h_findVar_v : findVar vm vr_v = some v
            have h_w_eq_v1 := Option.some.inj (h_findVar_w.symm.trans h_v1)
            have h_v_eq_v1 := Option.some.inj (h_findVar_v.symm.trans h_v2)
            have h_vw_eq : v = w := h_v_eq_v1.trans h_w_eq_v1.symm
            -- From h_fv and h_fw with v = w: vr_v = vr_w
            have h_vr_vw_eq : vr_v = vr_w := Option.some.inj (h_fv.symm.trans (h_vw_eq ▸ h_fw))
            -- vr1 = vr_w = vr_v = vr2
            exact h_vr_neq (h_vr1.symm.trans (h_vr_vw_eq.symm.trans h_vr2))
        | some _, none =>
            rw [h_fv, h_fw] at h_eq
            cases h_eq
        | none, _ =>
            rw [h_fv] at h_eq
            cases h_eq
  · -- (v1, v2) ∈ dv ∨ (v2, v1) ∈ dv
    cases h_mem_or with
    | inl h_fwd =>
        obtain ⟨⟨v, w⟩, h_vw_in, h_eq⟩ := List.mem_filterMap.mp h_fwd
        simp only [] at h_eq
        match h_fv : findVR vm v, h_fw : findVR vm w with
        | some vr_v, some vr_w =>
            rw [h_fv, h_fw] at h_eq
            have h_eq' := Option.some.inj h_eq
            cases h_eq'
            have h_v1_eq := findVR_findVar_inverse_frame h_fv
            rw [h_v1_eq] at h_v1
            cases h_v1
            have h_v2_eq := findVR_findVar_inverse_frame h_fw
            rw [h_v2_eq] at h_v2
            cases h_v2
            -- v1 = v, v2 = w, so (v1, v2) = (v, w) ∈ dv
            left
            exact h_vw_in
        | some _, none =>
            rw [h_fv, h_fw] at h_eq
            cases h_eq
        | none, _ =>
            rw [h_fv] at h_eq
            cases h_eq
    | inr h_rev =>
        obtain ⟨⟨v, w⟩, h_vw_in, h_eq⟩ := List.mem_filterMap.mp h_rev
        simp only [] at h_eq
        match h_fv : findVR vm v, h_fw : findVR vm w with
        | some vr_v, some vr_w =>
            rw [h_fv, h_fw] at h_eq
            have h_eq' := Option.some.inj h_eq
            cases h_eq'
            have h_v2_eq := findVR_findVar_inverse_frame h_fv
            rw [h_v2_eq] at h_v2
            cases h_v2
            have h_v1_eq := findVR_findVar_inverse_frame h_fw
            rw [h_v1_eq] at h_v1
            cases h_v1
            -- v2 = v, v1 = w, so (v, w) ∈ dv means (v2, v1) ∈ dv
            right
            exact h_vw_in
        | some _, none =>
            rw [h_fv, h_fw] at h_eq
            cases h_eq
        | none, _ =>
            rw [h_fv] at h_eq
            cases h_eq

/-- Helper for fromDeclarativeExpr membership: if a symbol x_s appears in fromDeclarativeExpr vm me,
    then there exists some DeclarativeSym in me that maps to x_s via fromDeclarativeSym. -/
theorem fromDeclarativeExpr_mem_exists_sym {vm : VarMap} {me : DeclarativeExpr} {x_s : Sym}
    (h_mem : x_s ∈ fromDeclarativeExpr vm me) :
    ∃ sym : DeclarativeSym, sym ∈ me ∧ fromDeclarativeSym vm sym = x_s := by
  unfold fromDeclarativeExpr at h_mem
  obtain ⟨sym, h_sym_in, h_eq⟩ := List.mem_map.mp h_mem
  exact ⟨sym, h_sym_in, h_eq⟩

/-- Key lemma: if a variable v in varsInExpr (from a well-formed Mario expression)
    has a VR in the varMap, then .var vr appears in the expression.

    **Hypothesis**: We work with exprToDeclarativeExpr vm e, which ensures variables
    are represented as .var, not .const.

    This is used in the dvOK inverse bridge where substitution results
    come from exprToDeclarativeExpr applied to database expressions. -/
theorem exprToDeclarativeExpr_varsInExpr_to_vr {fr : Frame} {e : Expr} {v : Variable} {vr : DeclarativeVR}
    (h_mem : v ∈ Spec.varsInExpr fr.vars e)
    (h_findVR : findVR (varMapOfFrame fr) v = some vr) :
    vr ∈' exprToDeclarativeExpr (varMapOfFrame fr) e := by
  let vm := varMapOfFrame fr
  unfold Spec.varsInExpr at h_mem
  simp only [List.mem_filterMap] at h_mem
  obtain ⟨s, h_s_in_syms, h_v_eq⟩ := h_mem
  -- h_s_in_syms : s ∈ e.syms
  -- h_v_eq : (if Variable.mk s ∈ fr.vars then some (Variable.mk s) else none) = some v
  by_cases h_cond : Variable.mk s ∈ fr.vars
  · -- Variable.mk s ∈ fr.vars, so h_v_eq gives Variable.mk s = v
    rw [if_pos h_cond] at h_v_eq
    have h_v_is_s : Variable.mk s = v := Option.some.inj h_v_eq
    -- Goal: vr ∈' exprToDeclarativeExpr vm e, which unfolds to Sym.var vr ∈ exprToDeclarativeExpr vm e
    -- Need to show: Sym.var vr ∈ e.syms.map (toDeclarativeSym vm)
    -- We have s ∈ e.syms and will show toDeclarativeSym vm s = Sym.var vr
    have h_toDeclarative : toDeclarativeSym (varMapOfFrame fr) s = Metamath.Sym.var vr := by
      unfold toDeclarativeSym
      -- Goal: match findVR vm (Variable.mk s) with | some vr => .var vr | none => .const s = .var vr
      -- We have h_v_is_s : Variable.mk s = v, so findVR vm (Variable.mk s) = findVR vm v = some vr
      conv => lhs; rw [h_v_is_s]
      simp only [h_findVR]
    rw [Metamath.Expr.mem, exprToDeclarativeExpr]
    -- Goal: Sym.var vr ∈ List.map (fun s => toDeclarativeSym vm s) e.syms
    -- We have s ∈ e.syms (h_s_in_syms) and toDeclarativeSym vm s = .var vr (h_toDeclarative)
    exact List.mem_map.mpr ⟨s, h_s_in_syms, h_toDeclarative⟩
  · -- ¬(Variable.mk s ∈ fr.vars), so h_v_eq : none = some v (contradiction)
    rw [if_neg h_cond] at h_v_eq
    cases h_v_eq

/-- If a variable v appears in varsInExpr from fromDeclarativeFormula, and v is in fr.vars,
    then there exists a VR in the Mario expression that maps back to v.

    This is the key bridge for the dvOK inverse: we need to extract VRs from
    variables that appear in substitution results.

    Assumption: me contains no .const symbols whose names equal variable names in fr.vars.
    This is a well-formedness assumption satisfied by expressions from toDeclarativeSubst. -/
theorem fromDeclarativeFormula_varsInExpr_to_vr {fr : Frame} {me : DeclarativeExpr} {v : Variable}
    (h_mem : v ∈ Spec.varsInExpr fr.vars ⟨⟨""⟩, fromDeclarativeExpr (varMapOfFrame fr) me⟩)
    -- Well-formedness: constants in me don't have names in fr.vars
    (h_wf : ∀ c, Metamath.Sym.const c ∈ me → Variable.mk c ∉ fr.vars)
    -- Well-formedness: VRs in me are in the varmap (from well-formed provable expressions)
    (h_vr_wf : ∀ vr, vr ∈' me → ∃ v', findVar (varMapOfFrame fr) vr = some v') :
    ∃ vr, vr ∈' me ∧ findVar (varMapOfFrame fr) vr = some v := by
  let vm := varMapOfFrame fr
  unfold Spec.varsInExpr at h_mem
  simp only [List.mem_filterMap] at h_mem
  obtain ⟨s, h_s_in_syms, h_v_eq⟩ := h_mem
  -- h_s_in_syms : s ∈ fromDeclarativeExpr vm me
  -- h_v_eq : (if Variable.mk s ∈ fr.vars then some (Variable.mk s) else none) = some v
  by_cases h_cond : Variable.mk s ∈ fr.vars
  · rw [if_pos h_cond] at h_v_eq
    have h_v_is_s : Variable.mk s = v := Option.some.inj h_v_eq
    -- s ∈ fromDeclarativeExpr vm me
    obtain ⟨sym, h_sym_in, h_sym_eq⟩ := fromDeclarativeExpr_mem_exists_sym h_s_in_syms
    -- sym ∈ me and fromDeclarativeSym vm sym = s
    cases sym with
    | const c =>
        -- fromDeclarativeSym vm (.const c) = c, so c = s
        simp only [fromDeclarativeSym] at h_sym_eq
        -- h_sym_eq : c = s, so Variable.mk s = Variable.mk c
        -- h_cond : Variable.mk s ∈ fr.vars
        -- Rewrite s to c in h_cond
        rw [← h_sym_eq] at h_cond
        -- Now h_cond : Variable.mk c ∈ fr.vars
        -- But h_wf says .const c ∈ me → Variable.mk c ∉ fr.vars
        exact absurd h_cond (h_wf c h_sym_in)
    | var vr' =>
        simp only [fromDeclarativeSym] at h_sym_eq
        -- h_sym_eq : (match findVar vm vr' with some v' => v'.v | none => "") = s
        refine ⟨vr', h_sym_in, ?_⟩
        -- findVar vm vr' = some v
        match h_findVar : findVar vm vr' with
        | some v_found =>
            -- The match in h_sym_eq reduces with h_findVar
            have h_reduce : (match findVar vm vr' with | some v' => v'.v | none => "") = v_found.v := by
              rw [h_findVar]
            rw [h_reduce] at h_sym_eq
            -- Now h_sym_eq : v_found.v = s, and h_v_is_s : Variable.mk s = v
            have h_v_found_eq_v : v_found = v := by
              rw [← h_v_is_s]
              exact Variable.ext v_found (Variable.mk s) h_sym_eq
            rw [h_v_found_eq_v]
        | none =>
            -- h_vr_wf says all VRs in me have findVar = some _
            -- But h_findVar says findVar vm vr' = none
            -- This is a contradiction since vr' ∈' me (from h_sym_in)
            obtain ⟨v_wf, h_wf_some⟩ := h_vr_wf vr' h_sym_in
            -- h_wf_some : findVar vm vr' = some v_wf contradicts h_findVar = none
            rw [h_findVar] at h_wf_some
            cases h_wf_some
  · rw [if_neg h_cond] at h_v_eq
    cases h_v_eq

/-- Mario's Expr.subst equals flatMap with the substitution function.
    This bridges the recursive definition to list operations. -/
theorem declarativeExpr_subst_eq_flatMap (σ : DeclarativeVR → DeclarativeExpr) (e : DeclarativeExpr) :
    Metamath.Expr.subst σ e = e.flatMap (fun sym =>
      match sym with
      | .var vr => σ vr
      | .const c => [.const c]) := by
  induction e with
  | nil => simp only [Metamath.Expr.subst, List.flatMap_nil]
  | cons hd tl ih =>
      cases hd with
      | const c =>
          simp only [Metamath.Expr.subst, List.flatMap_cons, List.singleton_append, ih]
      | var v =>
          rw [Metamath.Expr.subst, List.flatMap_cons, ih]

/-- Auxiliary lemma for substitution correspondence on symbol lists.
    Works on a general list with the const-preservation hypothesis. -/
theorem exprToDeclarativeExpr_applySubst_eq_subst_aux
    {frAx fr : Frame} {σ : Subst} (syms : List Sym)
    (h_const : ∀ s ∈ syms, Variable.mk s ∉ frAx.vars → Variable.mk s ∉ fr.vars) :
    let vmAx := varMapOfFrame frAx
    let vm := varMapOfFrame fr
    let σ_declarative := toDeclarativeSubst vmAx vm σ
    (syms.flatMap fun s => if Variable.mk s ∈ frAx.vars then (σ (Variable.mk s)).syms else [s]).map (toDeclarativeSym vm) =
    (syms.map (toDeclarativeSym vmAx)).flatMap (fun sym =>
      match sym with
      | .var vr => σ_declarative vr
      | .const c => [.const c]) := by
  -- Define local abbreviations for clarity
  let vmAx := varMapOfFrame frAx
  let vm := varMapOfFrame fr
  let σ_declarative := toDeclarativeSubst vmAx vm σ

  induction syms with
  | nil =>
      simp only [List.flatMap_nil, List.map_nil]
  | cons s rest ih =>
      simp only [List.flatMap_cons, List.map_cons, List.map_append]
      let v := Variable.mk s
      -- IH applies to rest with restricted hypothesis
      have h_const_rest : ∀ s' ∈ rest, Variable.mk s' ∉ frAx.vars → Variable.mk s' ∉ fr.vars := by
        intro s' h_in h_not
        exact h_const s' (List.mem_cons_of_mem s h_in) h_not
      -- Show the head symbol correspondence, then use IH for rest
      by_cases h_var : v ∈ frAx.vars
      · -- Case: s is a variable in frAx.vars
        -- Get the VR for this variable from vmAx
        have ⟨vr, h_findVR⟩ := (varMapDomain_ofFrame frAx v).mp h_var
        -- toDeclarativeSym vmAx s = .var vr
        have h_toDeclarative : toDeclarativeSym vmAx s = .var vr := by
          unfold toDeclarativeSym
          simp only [vmAx]
          split
          · rename_i vr' h_eq
            simp only [v] at h_findVR
            rw [h_findVR] at h_eq
            cases h_eq
            rfl
          · rename_i h_eq
            simp only [v] at h_findVR
            rw [h_findVR] at h_eq
            cases h_eq

        -- σ_declarative vr = exprToDeclarativeExpr vm (σ v)
        have h_sigma : σ_declarative vr = exprToDeclarativeExpr vm (σ v) := by
          simp only [σ_declarative, toDeclarativeSubst]
          have h_findVar := findVR_findVar_inverse_frame h_findVR
          split
          · rename_i v' h_eq
            simp only [v] at h_findVR
            have h_findVar' := findVR_findVar_inverse_frame h_findVR
            rw [h_findVar'] at h_eq
            cases h_eq
            rfl
          · rename_i h_eq
            simp only [v] at h_findVR
            have h_findVar' := findVR_findVar_inverse_frame h_findVR
            rw [h_findVar'] at h_eq
            cases h_eq

        simp only [v, h_var, ↓reduceIte]
        rw [h_toDeclarative]
        -- Simplify the match on .var vr
        simp only []
        simp only [σ_declarative, vmAx, vm] at h_sigma
        rw [h_sigma]
        simp only [exprToDeclarativeExpr, v]
        congr 1
        exact ih h_const_rest

      · -- Case: s is not a variable in frAx.vars (constant)
        have h_none : findVR vmAx v = none := by
          simp only [vmAx]
          match h_find : findVR (varMapOfFrame frAx) v with
          | some vr =>
              have h_in := (varMapDomain_ofFrame frAx v).mpr ⟨vr, h_find⟩
              exact absurd h_in h_var
          | none => rfl

        have h_toDeclarative : toDeclarativeSym vmAx s = .const s := by
          unfold toDeclarativeSym
          simp only [vmAx]
          split
          · rename_i vr h_eq
            simp only [v, vmAx] at h_none
            rw [h_none] at h_eq
            cases h_eq
          · rfl

        simp only [v, h_var, ↓reduceIte, List.map]
        rw [h_toDeclarative]

        -- Now we need toDeclarativeSym vm s = .const s (constant in axiom is constant in caller)
        -- Use h_const to show s is also not a variable in fr
        have h_s_in_syms : s ∈ s :: rest := by simp
        have h_var_fr : Variable.mk s ∉ fr.vars := h_const s h_s_in_syms h_var

        have h_none' : findVR vm (Variable.mk s) = none := by
          simp only [vm]
          match h_find : findVR (varMapOfFrame fr) (Variable.mk s) with
          | some vr =>
              have h_in := (varMapDomain_ofFrame fr (Variable.mk s)).mpr ⟨vr, h_find⟩
              exact absurd h_in h_var_fr
          | none => rfl

        have h_toDeclarative' : toDeclarativeSym vm s = .const s := by
          unfold toDeclarativeSym
          simp only [vm]
          split
          · rename_i vr h_eq
            simp only [vm] at h_none'
            rw [h_none'] at h_eq
            cases h_eq
          · rfl

        rw [h_toDeclarative']
        simp only [List.singleton_append]
        congr 1
        exact ih h_const_rest

/-- Main substitution correspondence theorem.
    Maps symbol-by-symbol between our applySubst and Mario's Expr.subst.

    Requires database well-formedness, which ensures that constants are global:
    if a symbol appears in an expression and has no floating hypothesis in that
    frame, then it's a constant and cannot be a variable in any other frame. -/
theorem exprToDeclarativeExpr_applySubst_eq_subst
    {Γ : Database} {consts : ConstSet} {l : Label} {frAx fr : Frame} {σ : Subst} {eAx : Expr}
    (h_wf : Spec.WellFormedDatabase Γ consts)
    (h_lookup : Γ l = some (frAx, eAx))
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr) :
    exprToDeclarativeExpr (varMapOfFrame fr) (Spec.applySubst frAx.vars σ eAx) =
    Metamath.Expr.subst (toDeclarativeSubst (varMapOfFrame frAx) (varMapOfFrame fr) σ)
                        (exprToDeclarativeExpr (varMapOfFrame frAx) eAx) := by
  -- Strategy:
  -- 1. Unfold LHS to get flatMap form
  -- 2. Rewrite RHS using declarativeExpr_subst_eq_flatMap to get flatMap form
  -- 3. Apply aux lemma (with h_const from well-formedness)

  let vmAx := varMapOfFrame frAx
  let vm := varMapOfFrame fr
  let σ_declarative := toDeclarativeSubst vmAx vm σ

  -- LHS unfolds to: (eAx.syms.flatMap ...).map (toDeclarativeSym vm)
  unfold exprToDeclarativeExpr Spec.applySubst
  simp only []

  -- RHS is Expr.subst σ_declarative (eAx.syms.map (toDeclarativeSym vmAx))
  -- Rewrite using declarativeExpr_subst_eq_flatMap
  rw [declarativeExpr_subst_eq_flatMap]

  -- Now apply aux lemma
  have h_const : ∀ s ∈ eAx.syms, Variable.mk s ∉ frAx.vars → Variable.mk s ∉ fr.vars := by
    intro s h_s_in h_not_var h_in_fr
    have h_const : consts s :=
      Spec.const_global_of_wellFormed h_wf h_lookup s h_s_in h_not_var
    have h_disj := h_fr_disjoint (Variable.mk s) h_in_fr
    exact (h_disj h_const).elim
  exact exprToDeclarativeExpr_applySubst_eq_subst_aux eAx.syms h_const

/-- Substitution correspondence for essential hypothesis expressions. -/
theorem exprToDeclarativeExpr_applySubst_eq_subst_hyp
    {Γ : Database} {consts : ConstSet} {l : Label} {frAx fr : Frame} {σ : Subst} {eAx e_hyp : Expr}
    (h_wf : Spec.WellFormedDatabase Γ consts)
    (h_lookup : Γ l = some (frAx, eAx))
    (h_hyp_in : Hyp.essential e_hyp ∈ frAx.hyps)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr) :
    exprToDeclarativeExpr (varMapOfFrame fr) (Spec.applySubst frAx.vars σ e_hyp) =
    Metamath.Expr.subst (toDeclarativeSubst (varMapOfFrame frAx) (varMapOfFrame fr) σ)
                        (exprToDeclarativeExpr (varMapOfFrame frAx) e_hyp) := by
  let vmAx := varMapOfFrame frAx
  let vm := varMapOfFrame fr
  let σ_declarative := toDeclarativeSubst vmAx vm σ
  unfold exprToDeclarativeExpr Spec.applySubst
  simp only []
  rw [declarativeExpr_subst_eq_flatMap]
  have h_const : ∀ s ∈ e_hyp.syms, Variable.mk s ∉ frAx.vars → Variable.mk s ∉ fr.vars := by
    intro s h_s_in h_not_var h_in_fr
    have h_const : consts s :=
      Spec.const_global_of_wellFormed_hyp h_wf h_lookup h_hyp_in s h_s_in h_not_var
    have h_disj := h_fr_disjoint (Variable.mk s) h_in_fr
    exact (h_disj h_const).elim
  exact exprToDeclarativeExpr_applySubst_eq_subst_aux e_hyp.syms h_const

/-! ## Assertions of a database are reducts -/

/-- Variables occurring in the hypotheses of a context. -/
def hypVars (context : Metamath.Context) : List DeclarativeVR :=
  context.hyps.flatMap fun h => h.2.vars

/-- A variable the frame map assigns to a floating hypothesis occurs in that
hypothesis. -/
theorem mem_hypVars_of_findVR {fr : Frame} {v : Variable} {x : DeclarativeVR}
    (h : findVR (varMapOfFrame fr) v = some x) :
    x ∈ hypVars (frameToContext fr) := by
  obtain ⟨c, hfloat, _⟩ := mem_varMapOfFrame_sound_typed (findVR_mem_of_some h)
  refine List.mem_flatMap.mpr ⟨_, hypToDeclarativeFormula_mem hfloat, ?_⟩
  simp [hypToDeclarativeFormula, h, Metamath.Expr.vars]

/-- Both variables of a converted `$d` pair occur in the frame's hypotheses. -/
theorem dj_mem_hypVars {fr : Frame} {a b : DeclarativeVR}
    (hab : (frameToContext fr).dj a b) :
    a ∈ hypVars (frameToContext fr) ∧ b ∈ hypVars (frameToContext fr) := by
  have key : ∀ {x y : DeclarativeVR},
      (x, y) ∈ (fr.dv.filterMap fun p =>
        match findVR (varMapOfFrame fr) p.1, findVR (varMapOfFrame fr) p.2 with
        | some a, some b => some (a, b)
        | _, _ => none) →
      x ∈ hypVars (frameToContext fr) ∧ y ∈ hypVars (frameToContext fr) := by
    intro x y hxy
    obtain ⟨p, _hp, hmatch⟩ := List.mem_filterMap.mp hxy
    cases h1 : findVR (varMapOfFrame fr) p.1 with
    | none => rw [h1] at hmatch; exact nomatch hmatch
    | some a' =>
        cases h2 : findVR (varMapOfFrame fr) p.2 with
        | none => rw [h1, h2] at hmatch; exact nomatch hmatch
        | some b' =>
            rw [h1, h2] at hmatch
            simp only [Option.some.injEq, Prod.mk.injEq] at hmatch
            obtain ⟨rfl, rfl⟩ := hmatch
            exact ⟨mem_hypVars_of_findVR h1, mem_hypVars_of_findVR h2⟩
  obtain ⟨_, hor⟩ := hab
  rcases hor with h | h
  · exact key h
  · exact (key h).symm

/-- Every assertion of `dbToAxioms Γ` is trimmed (a reduct, in the Metamath
book's Appendix C): a variable in its disjointness relation occurs in the
assertion, through its floating hypothesis. -/
theorem dbToAxioms_trimmed {Γ : Database} {ax : Metamath.Statement}
    (hax : dbToAxioms Γ ax) : ax.trimmed := by
  obtain ⟨_l, fr, _e, _hlookup, hctx, _hfmla⟩ := hax
  intro a b hab
  have hab' : (frameToContext fr).dj a b := by rw [← hctx]; exact hab
  have hmem : ∀ x, x ∈ hypVars (frameToContext fr) → x ∈ ax.vars := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := List.mem_flatMap.mp hx
    have hf' : f ∈ ax.ctx.hyps := by rw [hctx]; exact hf
    exact List.mem_flatMap.mpr ⟨f, List.Mem.tail _ hf', hxf⟩
  obtain ⟨ha, hb⟩ := dj_mem_hypVars hab'
  exact ⟨hmem a ha, hmem b hb⟩

/-! ## Frame derivability

`FrameDerivable` is Mario's `Provable` restricted at `var` leaves: every
variable used in the derivation must be a variable of the frame, found in its
floating-hypothesis map. This is Metamath's own rule — the operational verifier
requires every variable to be typed by an active `$f` hypothesis. -/

/-- The variables of the frame `fr`: those its floating-hypothesis map assigns. -/
def FrameDeclared (fr : Frame) (v : DeclarativeVR) : Prop :=
  ∃ w : Variable, findVar (varMapOfFrame fr) v = some w

/-- Derivability by Mario's rules in the frame `fr`: the closure (Metamath book C.2.5) of the
pre-statement whose variable-type hypotheses are the frame's variables. -/
abbrev FrameDerivable (Γ : Database) (fr : Frame) : DeclarativeFormula → Prop :=
  Derivable (dbToAxioms Γ) (FrameDeclared fr) (frameToContext fr)

/-- Forget the frame condition on `var` leaves: frame derivability implies Mario's
declarative provability. -/
theorem FrameDerivable.toDeclarative {Γ : Database} {fr : Frame} {fmla : DeclarativeFormula}
    (h : FrameDerivable Γ fr fmla) :
    Declarative.Provable (dbToAxioms Γ) (frameToContext fr) fmla :=
  provable_iff_derivable.mpr (h.mono (fun _ h => h) (fun _ _ => trivial) (Metamath.Context.refl _))

/-- Every variable of a frame-derivable formula is a variable of the frame. -/
theorem frameDerivable_wellFormed {Γ : Database} {fr : Frame} {fmla : DeclarativeFormula}
    (h_provable : FrameDerivable Γ fr fmla) :
    DeclarativeExprWellFormed fr fmla.2 := by
  induction h_provable with
  | hyp h h_in =>
      intro vr h_vr_mem
      obtain ⟨hyp, hyp_in, hyp_eq⟩ := hyps_correspondence h_in
      cases hyp with
      | essential e_hyp =>
          simp only [hypToDeclarativeFormula_essential] at hyp_eq
          have h_snd_eq : h.2 = exprToDeclarativeExpr (varMapOfFrame fr) e_hyp := by
            rw [hyp_eq]; rfl
          rw [h_snd_eq] at h_vr_mem
          obtain ⟨s, _, h_find⟩ := exprToDeclarativeExpr_mem_extract h_vr_mem
          exact ⟨⟨s⟩, findVR_findVar_inverse_frame h_find⟩
      | floating c v =>
          obtain ⟨vr', h_findVR⟩ := findVR_of_float (fr := fr) (c := c) (v := v) hyp_in
          have h_float_eq := hypToDeclarativeFormula_floating_expr (varMapOfFrame fr) c v h_findVR
          rw [h_float_eq] at hyp_eq
          have h_snd_eq : h.2 = [Metamath.Sym.var vr'] := by
            rw [hyp_eq]
            unfold exprToFormula exprToDeclarativeExpr
            simp only [List.map_cons, List.map_nil]
            unfold toDeclarativeSym
            simp only [h_findVR]
          rw [h_snd_eq] at h_vr_mem
          unfold Metamath.Expr.mem at h_vr_mem
          have h_vr_eq := List.mem_singleton.mp h_vr_mem
          have h_vr_eq' := Metamath.Sym.var.inj h_vr_eq
          subst h_vr_eq'
          exact ⟨v, findVR_findVar_inverse_frame h_findVR⟩
  | var vr h_find =>
      intro vr' h_vr_mem
      unfold Metamath.Expr.mem at h_vr_mem
      have h_vr_eq := List.mem_singleton.mp h_vr_mem
      have h_vr_eq' := Metamath.Sym.var.inj h_vr_eq
      subst h_vr_eq'
      exact h_find
  | ax σ h_axs _ _ _ _ ih_var =>
      intro vr h_vr_mem
      obtain ⟨l, frAx, eAx, h_lookup, _h_ctx_eq, h_fmla_eq⟩ := dbToAxioms_inverse h_axs
      let vmAx := varMapOfFrame frAx
      have h_subst_snd : (Metamath.Formula.subst σ (exprToFormula vmAx eAx)).snd =
                         (exprToDeclarativeExpr vmAx eAx).subst σ := rfl
      rw [h_fmla_eq, h_subst_snd] at h_vr_mem
      obtain ⟨vr', h_vr'_mem, h_vr_in_sigma⟩ := Metamath.Expr.mem_subst h_vr_mem
      have h_vr'_in_fmla_expr : vr' ∈ (exprToDeclarativeExpr vmAx eAx).vars := Metamath.Expr.mem_vars_iff.mpr h_vr'_mem
      have h_fmla_snd_eq : (exprToFormula vmAx eAx).snd = exprToDeclarativeExpr vmAx eAx := rfl
      have h_vr'_in_ax_fmla_vars : vr' ∈ (exprToFormula vmAx eAx).snd.vars := h_fmla_snd_eq ▸ h_vr'_in_fmla_expr
      have h_wf_sigma_vr' : DeclarativeExprWellFormed fr (σ vr') := ih_var vr' (by
        simp only [Metamath.Statement.vars, List.flatMap_cons, List.mem_append]
        left
        rw [h_fmla_eq]
        exact h_vr'_in_ax_fmla_vars)
      exact h_wf_sigma_vr' vr h_vr_in_sigma

/-! ## Forward Direction: ProofValid → Mario.Provable

We first show that every element on a valid proof stack is Mario-provable,
then derive the singleton-stack case as a corollary.
-/

/-- Every element of a valid proof stack is frame derivable. Requires database
well-formedness for substitution correspondence. -/
theorem proofValid_stack_frameDerivable {Γ : Database} {consts : ConstSet} {fr : Frame}
    {stack : List Expr} {steps : List ProofStep}
    (h_wf : Spec.WellFormedDatabase Γ consts)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr) :
    ProofValid Γ fr stack steps →
    ∀ e ∈ stack,
      FrameDerivable Γ fr
        (exprToFormula (varMapOfFrame fr) e) := by
  intro h
  induction h with
  | nil =>
      intro e h_mem
      cases h_mem
  | useEssential stack steps e h_in h_prev ih =>
      intro e' h_mem
      cases h_mem with
      | head =>
          apply Derivable.hyp
          have h_mem' : hypToDeclarativeFormula (varMapOfFrame fr) (Hyp.essential e) ∈
              (frameToContext fr).hyps := hypToDeclarativeFormula_mem (fr := fr) (h := Hyp.essential e) h_in
          simpa [hypToDeclarativeFormula_essential] using h_mem'
      | tail _ h_tail =>
          exact ih e' h_tail
  | useFloating stack steps c v h_in h_prev ih =>
      intro e' h_mem
      cases h_mem with
      | head =>
          apply Derivable.hyp
          have h_mem' : hypToDeclarativeFormula (varMapOfFrame fr) (Hyp.floating c v) ∈
              (frameToContext fr).hyps := hypToDeclarativeFormula_mem (fr := fr) (h := Hyp.floating c v) h_in
          obtain ⟨vr, h_find⟩ := findVR_of_float (fr := fr) (c := c) (v := v) h_in
          have h_eq := hypToDeclarativeFormula_floating_expr (vm := varMapOfFrame fr) (c := c)
            (v := v) (vr := vr) h_find
          simpa [h_eq] using h_mem'
      | tail _ h_tail =>
          exact ih e' h_tail
  | useAxiom stack steps l frAx eAx σ h_ax h_dv h_typed h_prev needed h_needed remaining h_stack_eq ih =>
      intro e' h_mem
      cases h_mem with
      | head =>
          -- The axiom-result case is the main bridge obligation.
          -- e' = applySubst frAx.vars σ eAx (the result of applying the axiom)
          --
          -- We need to prove:
          --   Declarative.Provable (dbToAxioms Γ) (frameToContext fr)
          --     (exprToFormula (varMapOfFrame fr) (applySubst frAx.vars σ eAx))
          --
          -- Strategy: Apply Declarative.Provable.ax with:
          -- 1. The statement from (frAx, eAx)
          -- 2. A Mario substitution built from σ
          -- 3. DV constraint satisfaction via dvOK_implies_DJ_subst
          -- 4. Hypothesis provability via IH

          -- Step 1: Construct the axiom Statement
          let vmAx := varMapOfFrame frAx
          let ax : Declarative.Statement := ⟨frameToContext frAx, exprToFormula vmAx eAx⟩

          -- Step 2: Show ax is in dbToAxioms
          have h_ax_in : dbToAxioms Γ ax := ⟨l, frAx, eAx, h_ax, rfl, rfl⟩

          -- Step 3: Build Mario substitution
          let vm := varMapOfFrame fr
          let σ_declarative : DeclarativeVR → DeclarativeExpr := toDeclarativeSubst vmAx vm σ

          -- At this point we need:
          -- a) ax.ctx.dj.subst σ_declarative (frameToContext fr).dj
          -- b) All hypotheses provable after substitution
          -- c) Show the result formula matches

          -- Apply Provable.ax with substitution σ_declarative
          -- Goal: Provable (dbToAxioms Γ) (frameToContext fr)
          --         (exprToFormula vm (applySubst frAx.vars σ eAx))

          -- The result formula needs to match ax.fmla.subst σ_declarative
          -- We'll prove this via a rewrite at the end

          -- Sub-goal 1: DV constraint satisfaction
          -- ax.ctx.dj.subst σ_declarative (frameToContext fr).dj
          have h_dv_declarative : ax.ctx.dj.subst σ_declarative (frameToContext fr).dj := by
            -- ax.ctx = frameToContext frAx, so ax.ctx.dj = (frameToContext frAx).dj
            -- = dvListToDeclarativeDJ (varMapOfFrame frAx) frAx.dv = dvListToDeclarativeDJ vmAx frAx.dv
            -- Similarly (frameToContext fr).dj = dvListToDeclarativeDJ vm fr.dv
            show (dvListToDeclarativeDJ vmAx frAx.dv).subst σ_declarative (dvListToDeclarativeDJ vm fr.dv)

            -- h_dv : Spec.dvOK fr.vars frAx.dv fr.dv σ
            unfold Metamath.DJ.subst
            intro vr1 vr2 h_dj
            -- h_dj : (dvListToDeclarativeDJ vmAx frAx.dv).disj vr1 vr2
            unfold Metamath.Expr.disjoint
            intro x y h_x_in h_y_in
            -- Need: (dvListToDeclarativeDJ vm fr.dv).disj x y

            -- Step 1: Get the source variable pair from h_dj
            unfold dvListToDeclarativeDJ at h_dj
            simp only [Metamath.DJ.mk'] at h_dj
            obtain ⟨h_neq, h_mem_or⟩ := h_dj
            -- h_mem_or : (vr1, vr2) or (vr2, vr1) is in the filterMap result

            -- Step 2: Extract the original variable pair from filterMap membership
            -- The filterMap keeps (v, w) only when both findVR succeed
            cases h_mem_or with
            | inl h_fwd =>
                -- (vr1, vr2) ∈ frAx.dv.filterMap (...)
                -- Use helper to extract source variables and findVR relations
                obtain ⟨⟨v, w⟩, h_vw_in, h_find⟩ := List.mem_filterMap.mp h_fwd
                -- Case split on the Option results to extract the equations
                simp only [] at h_find
                -- The only way to get `some (vr1, vr2)` is if both findVR succeed
                match h_v : findVR vmAx v, h_w : findVR vmAx w with
                | some vr1', some vr2' =>
                  simp only [h_v, h_w] at h_find
                  -- h_find : some (vr1', vr2') = some (vr1, vr2)
                  have h_eq := Option.some.inj h_find
                  cases h_eq
                  -- Now h_v : findVR vmAx v = some vr1, h_w : findVR vmAx w = some vr2

                  -- Step 3: Connect findVR to findVar (they are inverses)
                  -- This follows from uniqueness of VRs in varMapOfFrame
                  -- (each variable gets a unique index in varMapOfFrameAux)
                  have h_findVar_v : findVar vmAx vr1 = some v :=
                    findVR_findVar_inverse_frame h_v

                  have h_findVar_w : findVar vmAx vr2 = some w :=
                    findVR_findVar_inverse_frame h_w

                  -- Step 4: x ∈' σ_declarative vr1 = x ∈' toDeclarativeSubst vmAx vm σ vr1
                  --       = x ∈' exprToDeclarativeExpr vm (σ v) (by h_findVar_v)
                  change x ∈' (toDeclarativeSubst vmAx vm σ vr1) at h_x_in
                  change y ∈' (toDeclarativeSubst vmAx vm σ vr2) at h_y_in
                  simp only [toDeclarativeSubst, h_findVar_v] at h_x_in
                  simp only [toDeclarativeSubst, h_findVar_w] at h_y_in
                  -- Now h_x_in : x ∈' exprToDeclarativeExpr vm (σ v)
                  -- and h_y_in : y ∈' exprToDeclarativeExpr vm (σ w)

                  -- Step 5: Extract source variables from x and y membership
                  -- Use exprToDeclarativeExpr_mem_extract to get the source symbols
                  obtain ⟨x_s, h_x_s_in, h_x_findVR⟩ := exprToDeclarativeExpr_mem_extract h_x_in
                  obtain ⟨y_s, h_y_s_in, h_y_findVR⟩ := exprToDeclarativeExpr_mem_extract h_y_in
                  let x_var := Variable.mk x_s
                  let y_var := Variable.mk y_s
                  -- x_var ∈ fr.vars (by findVR_in_vars)
                  have h_x_in_vars : x_var ∈ fr.vars := findVR_in_vars h_x_findVR
                  have h_y_in_vars : y_var ∈ fr.vars := findVR_in_vars h_y_findVR
                  -- x_var ∈ varsInExpr fr.vars (σ v) (by definition)
                  have h_x_varsInExpr : x_var ∈ Spec.varsInExpr fr.vars (σ v) := by
                    unfold Spec.varsInExpr
                    apply List.mem_filterMap.mpr
                    refine ⟨x_s, h_x_s_in, ?_⟩
                    simp only [x_var, h_x_in_vars, ite_true]
                  have h_y_varsInExpr : y_var ∈ Spec.varsInExpr fr.vars (σ w) := by
                    unfold Spec.varsInExpr
                    apply List.mem_filterMap.mpr
                    refine ⟨y_s, h_y_s_in, ?_⟩
                    simp only [y_var, h_y_in_vars, ite_true]
                  -- Use dvOK to get dvRel fr.dv x_var y_var
                  have h_dvRel : Spec.dvRel fr.dv x_var y_var := by
                    unfold Spec.dvOK at h_dv
                    exact h_dv v w h_vw_in x_var h_x_varsInExpr y_var h_y_varsInExpr
                  -- Lift dvRel to dvListToDeclarativeDJ
                  have h_unique : ∀ v' v'' vr', findVR vm v' = some vr' → findVR vm v'' = some vr' → v' = v'' :=
                    fun _ _ _ h1 h2 => findVR_injective_frame h1 h2
                  exact dvRel_to_dvListToDeclarativeDJ h_unique h_dvRel h_x_findVR h_y_findVR
                | some _, none =>
                  simp only [h_v, h_w] at h_find
                  -- h_find : none = some (vr1, vr2), contradiction
                  cases h_find
                | none, _ =>
                  simp only [h_v] at h_find
                  -- h_find : none = some (vr1, vr2), contradiction
                  cases h_find

            | inr h_rev =>
                -- Symmetric case: (vr2, vr1) ∈ filterMap result from (v, w) in frAx.dv
                -- So vr2 = findVR vmAx v, vr1 = findVR vmAx w
                obtain ⟨⟨v, w⟩, h_vw_in, h_find⟩ := List.mem_filterMap.mp h_rev
                simp only [] at h_find
                match h_v : findVR vmAx v, h_w : findVR vmAx w with
                | some vr2', some vr1' =>
                    simp only [h_v, h_w] at h_find
                    have h_eq := Option.some.inj h_find
                    -- h_eq : (vr2', vr1') = (vr2, vr1), so vr2' = vr2, vr1' = vr1
                    cases h_eq
                    -- vr2 came from v, vr1 came from w
                    have h_findVar_v : findVar vmAx vr2 = some v := findVR_findVar_inverse_frame h_v
                    have h_findVar_w : findVar vmAx vr1 = some w := findVR_findVar_inverse_frame h_w
                    -- Get the membership in exprToDeclarativeExpr
                    change x ∈' (toDeclarativeSubst vmAx vm σ vr1) at h_x_in
                    change y ∈' (toDeclarativeSubst vmAx vm σ vr2) at h_y_in
                    simp only [toDeclarativeSubst, h_findVar_w] at h_x_in  -- x from σ w
                    simp only [toDeclarativeSubst, h_findVar_v] at h_y_in  -- y from σ v
                    -- Now h_x_in : x ∈' exprToDeclarativeExpr vm (σ w)
                    -- and h_y_in : y ∈' exprToDeclarativeExpr vm (σ v)
                    -- Extract source variables
                    obtain ⟨x_s, h_x_s_in, h_x_findVR⟩ := exprToDeclarativeExpr_mem_extract h_x_in
                    obtain ⟨y_s, h_y_s_in, h_y_findVR⟩ := exprToDeclarativeExpr_mem_extract h_y_in
                    let x_var := Variable.mk x_s
                    let y_var := Variable.mk y_s
                    have h_x_in_vars : x_var ∈ fr.vars := findVR_in_vars h_x_findVR
                    have h_y_in_vars : y_var ∈ fr.vars := findVR_in_vars h_y_findVR
                    -- x_var ∈ varsInExpr fr.vars (σ w), y_var ∈ varsInExpr fr.vars (σ v)
                    have h_x_varsInExpr : x_var ∈ Spec.varsInExpr fr.vars (σ w) := by
                      unfold Spec.varsInExpr
                      apply List.mem_filterMap.mpr
                      refine ⟨x_s, h_x_s_in, ?_⟩
                      simp only [x_var, h_x_in_vars, ite_true]
                    have h_y_varsInExpr : y_var ∈ Spec.varsInExpr fr.vars (σ v) := by
                      unfold Spec.varsInExpr
                      apply List.mem_filterMap.mpr
                      refine ⟨y_s, h_y_s_in, ?_⟩
                      simp only [y_var, h_y_in_vars, ite_true]
                    -- Use dvOK with (v, w) to get dvRel fr.dv y_var x_var
                    -- (note: y is from σ v, x is from σ w)
                    have h_dvRel : Spec.dvRel fr.dv y_var x_var := by
                      unfold Spec.dvOK at h_dv
                      exact h_dv v w h_vw_in y_var h_y_varsInExpr x_var h_x_varsInExpr
                    -- dvRel is symmetric, so we also have dvRel fr.dv x_var y_var
                    have h_dvRel_sym : Spec.dvRel fr.dv x_var y_var := by
                      unfold Spec.dvRel at h_dvRel ⊢
                      constructor
                      · exact fun h => h_dvRel.1 h.symm
                      · cases h_dvRel.2 with
                        | inl h => right; exact h
                        | inr h => left; exact h
                    -- Lift to dvListToDeclarativeDJ
                    have h_unique : ∀ v' v'' vr', findVR vm v' = some vr' → findVR vm v'' = some vr' → v' = v'' :=
                      fun _ _ _ h1 h2 => findVR_injective_frame h1 h2
                    exact dvRel_to_dvListToDeclarativeDJ h_unique h_dvRel_sym h_x_findVR h_y_findVR
                | some _, none =>
                    simp only [h_v, h_w] at h_find
                    cases h_find
                | none, _ =>
                    simp only [h_v] at h_find
                    cases h_find

          -- Sub-goal 2a: Essential hypotheses are provable after substitution
          have h_hyps_ess : ∀ h ∈ ax.ctx.hyps,
              FrameDerivable Γ fr (h.subst σ_declarative) := by
            intro h h_in_hyps
            -- h is a hypothesis from the axiom's frame (essential or floating)
            -- ax.ctx.hyps = frAx.hyps.map (hypToDeclarativeFormula vmAx)
            -- So there exists hyp ∈ frAx.hyps with h = hypToDeclarativeFormula vmAx hyp
            have h_ax_ctx : ax.ctx = frameToContext frAx := rfl
            rw [h_ax_ctx] at h_in_hyps
            unfold frameToContext at h_in_hyps
            simp only [] at h_in_hyps
            -- h_in_hyps : h ∈ frAx.hyps.map (hypToDeclarativeFormula vmAx)
            obtain ⟨hyp, h_hyp_in, h_hyp_eq⟩ := List.mem_map.mp h_in_hyps
            -- hyp ∈ frAx.hyps and h = hypToDeclarativeFormula vmAx hyp
            cases hyp with
            | essential e_hyp =>
                -- h = exprToFormula vmAx e_hyp
                -- h.subst σ_declarative should equal exprToFormula vm (applySubst frAx.vars σ e_hyp)
                -- And applySubst frAx.vars σ e_hyp is in needed (hence on stack)
                rw [← h_hyp_eq, hypToDeclarativeFormula_essential]
                -- Goal: Provable ... ((exprToFormula vmAx e_hyp).subst σ_declarative)
                -- Rewrite using our substitution correspondence
                have h_subst_eq : (exprToFormula vmAx e_hyp).subst σ_declarative =
                    exprToFormula vm (Spec.applySubst frAx.vars σ e_hyp) := by
                  unfold exprToFormula Metamath.Formula.subst
                  simp only []
                  -- Goal: (e_hyp.typecode.c, Expr.subst σ_declarative (exprToDeclarativeExpr vmAx e_hyp)) =
                  --       ((applySubst frAx.vars σ e_hyp).typecode.c, exprToDeclarativeExpr vm (applySubst frAx.vars σ e_hyp))
                  -- applySubst preserves typecode
                  have h_tc : (Spec.applySubst frAx.vars σ e_hyp).typecode = e_hyp.typecode := by
                    unfold Spec.applySubst; rfl
                  rw [h_tc]
                  congr 1
                  -- Now just need the expression part (need to swap sides)
                  exact (exprToDeclarativeExpr_applySubst_eq_subst_hyp h_wf h_ax h_hyp_in h_fr_disjoint).symm
                rw [h_subst_eq]
                -- Now need to show applySubst frAx.vars σ e_hyp is on stack
                have h_in_needed : Spec.applySubst frAx.vars σ e_hyp ∈ needed := by
                  rw [h_needed]
                  apply List.mem_map.mpr
                  refine ⟨Hyp.essential e_hyp, h_hyp_in, ?_⟩
                  rfl
                have h_in_stack : Spec.applySubst frAx.vars σ e_hyp ∈ stack := by
                  rw [h_stack_eq]
                  exact List.mem_append_left _ (List.mem_reverse.mpr h_in_needed)
                exact ih (Spec.applySubst frAx.vars σ e_hyp) h_in_stack
            | floating c_hyp v_hyp =>
                -- h = hypToDeclarativeFormula vmAx (Hyp.floating c_hyp v_hyp) = (c_hyp.c, [.var vr])
                -- h.subst σ_declarative = (c_hyp.c, σ_declarative vr)
                -- σ v_hyp is in needed (hence on stack)
                -- Type preservation: h_typed gives us (σ v_hyp).typecode = c_hyp
                have h_type_pres := h_typed c_hyp v_hyp h_hyp_in
                -- h_type_pres : (σ v_hyp).typecode = c_hyp
                -- Get the VR for v_hyp in vmAx
                have ⟨vr, h_findVR⟩ := findVR_of_float (fr := frAx) (c := c_hyp) (v := v_hyp) h_hyp_in
                -- h = (c_hyp.c, [.var vr])
                rw [← h_hyp_eq]
                have h_float_eq := hypToDeclarativeFormula_floating_expr (vm := vmAx)
                  (c := c_hyp) (v := v_hyp) (vr := vr) h_findVR
                rw [h_float_eq]
                -- Goal: Provable ... ((exprToFormula vmAx ⟨c_hyp, [v_hyp.v]⟩).subst σ_declarative)
                -- exprToFormula vmAx ⟨c_hyp, [v_hyp.v]⟩ = (c_hyp.c, [.var vr])
                unfold exprToFormula exprToDeclarativeExpr
                simp only [List.map_cons, List.map_nil]
                -- Goal: Provable ... ((c_hyp.c, [toDeclarativeSym vmAx v_hyp.v]).subst σ_declarative)
                simp only [Metamath.Formula.subst]
                -- Goal: Provable ... (c_hyp.c, Expr.subst σ_declarative [toDeclarativeSym vmAx v_hyp.v])
                -- toDeclarativeSym vmAx v_hyp.v = .var vr since h_findVR
                have h_sym : toDeclarativeSym vmAx v_hyp.v = .var vr := toDeclarativeSym_var h_findVR
                simp [h_sym, Metamath.Expr.subst]
                -- Goal: Provable ... (c_hyp.c, σ_declarative vr)
                -- σ_declarative vr = exprToDeclarativeExpr vm (σ v_hyp)
                have h_sigma_eq : σ_declarative vr = exprToDeclarativeExpr vm (σ v_hyp) := by
                  have h_findVar := findVR_findVar_inverse_frame h_findVR
                  exact toDeclarativeSubst_findVar h_findVar
                rw [h_sigma_eq]
                -- σ v_hyp is on the stack, so by IH it's provable
                have h_in_needed : σ v_hyp ∈ needed := by
                  rw [h_needed]
                  apply List.mem_map.mpr
                  refine ⟨Hyp.floating c_hyp v_hyp, h_hyp_in, ?_⟩
                  rfl
                have h_in_stack : σ v_hyp ∈ stack := by
                  rw [h_stack_eq]
                  exact List.mem_append_left _ (List.mem_reverse.mpr h_in_needed)
                rw [← (congrArg Constant.c h_type_pres)]
                simpa [vm, exprToFormula, List.append_nil] using
                  ih (σ v_hyp) h_in_stack

          -- Sub-goal 2b: Variable typing - for each VR in axiom, prove (v.type, σ_declarative v)
          -- ax.vars contains DeclarativeVRs from the axiom's formula and hypotheses
          -- Each corresponds to a floating hypothesis in frAx.hyps
          have h_hyps_var : ∀ v ∈ ax.vars,
              FrameDerivable Γ fr (v.type, σ_declarative v) := by
            intro v v_in_vars
            -- v ∈ ax.vars means v appears in the axiom statement
            -- ax.vars is computed from Statement.vars which collects VRs from formulas
            -- Each VR in ax has a corresponding Variable in frAx with a floating hyp
            -- Step 1: v ∈ ax.vars means v is in some expression from ax.fmla or ax.ctx.hyps
            simp only [Metamath.Statement.vars, List.mem_flatMap] at v_in_vars
            obtain ⟨f, h_f_in, h_v_in_f⟩ := v_in_vars
            -- f is a formula containing v, and f ∈ (ax.fmla :: ax.ctx.hyps)
            -- f.2 is the expression part, and v ∈ f.2.vars
            -- By Metamath.Expr.mem_vars_iff, v ∈' f.2
            have h_v_mem : v ∈' f.2 := Metamath.Expr.mem_vars_iff.mp h_v_in_f
            -- Step 2: Find the Variable corresponding to v
            -- The formula f came from exprToFormula vmAx applied to some Metamath expression
            -- Using a helper to extract the variable
            have h_findVar : ∃ var_spec, findVar vmAx v = some var_spec := by
              cases h_f_in with
              | head =>
                  -- f = ax.fmla = exprToFormula vmAx eAx
                  -- h_v_mem : v ∈' f.2 = v ∈' ax.fmla.2 = v ∈' exprToDeclarativeExpr vmAx eAx
                  obtain ⟨s, _, h_findVR⟩ := exprToDeclarativeExpr_mem_extract h_v_mem
                  have h_findVar_eq := findVR_findVar_inverse_frame h_findVR
                  exact ⟨⟨s⟩, h_findVar_eq⟩
              | tail _ h_in_hyps =>
                  have h_ctx_eq : ax.ctx = frameToContext frAx := rfl
                  simp only [h_ctx_eq, frameToContext] at h_in_hyps
                  obtain ⟨hyp, h_hyp_in, h_hyp_eq⟩ := List.mem_map.mp h_in_hyps
                  subst h_hyp_eq
                  cases hyp with
                  | essential e_hyp =>
                      simp only [hypToDeclarativeFormula] at h_v_mem
                      obtain ⟨s, _, h_findVR⟩ := exprToDeclarativeExpr_mem_extract h_v_mem
                      have h_findVar_eq := findVR_findVar_inverse_frame h_findVR
                      exact ⟨⟨s⟩, h_findVar_eq⟩
                  | floating c_hyp v_hyp =>
                      -- hypToDeclarativeFormula for floating directly creates (c.c, [Sym.var vr])
                      -- where vr = findVR vmAx v_hyp (or a default if none)
                      -- v ∈' [Sym.var vr] means Sym.var v ∈ [Sym.var vr], so v = vr
                      unfold hypToDeclarativeFormula at h_v_mem
                      -- h_v_mem : v ∈' [Sym.var (match findVR vmAx v_hyp with ...)]
                      -- v_hyp ∈ frAx.hyps, so findVR vmAx v_hyp should succeed
                      have ⟨vr', h_findVR⟩ := findVR_of_float (fr := frAx) (c := c_hyp)
                        (v := v_hyp) h_hyp_in
                      simp only [h_findVR] at h_v_mem
                      -- h_v_mem : v ∈' [Sym.var vr']
                      -- This means Sym.var v ∈ [Sym.var vr']
                      -- Since it's a singleton, Sym.var v = Sym.var vr'
                      have h_eq_sym : Metamath.Sym.var v = Metamath.Sym.var vr' := by
                        unfold Metamath.Expr.mem at h_v_mem
                        exact List.mem_singleton.mp h_v_mem
                      have h_eq := Metamath.Sym.var.inj h_eq_sym
                      subst h_eq
                      have h_findVar_eq := findVR_findVar_inverse_frame h_findVR
                      exact ⟨v_hyp, h_findVar_eq⟩
            -- Step 3: Continue with the Variable we found
            obtain ⟨var_spec, h_findVar_eq⟩ := h_findVar
            -- var_spec is the Variable in frAx, h_findVar_eq : findVar vmAx v = some var_spec
            -- From findVar success, get map membership
            have h_mem : (var_spec, v) ∈ varMapOfFrame frAx :=
              findVar_mem_of_some h_findVar_eq
            -- From membership, get floating hyp AND type match
            obtain ⟨c_float, h_float_in, h_type_eq⟩ :=
              mem_varMapOfFrame_sound_typed h_mem
            -- h_float_in : Hyp.floating c_float var_spec ∈ frAx.hyps
            -- h_type_eq : v.type = c_float.c
            -- Use h_typed to get substitution type preservation
            have h_sigma_type := h_typed c_float var_spec h_float_in
            -- h_sigma_type : (σ var_spec).typecode = c_float
            -- Connect v.type to (σ var_spec).typecode.c
            have h_type_connect : v.type = (σ var_spec).typecode.c := by
              rw [h_type_eq, h_sigma_type]
            -- Show σ var_spec is on the stack (via needed)
            have h_in_needed : σ var_spec ∈ needed := by
              rw [h_needed]
              apply List.mem_map.mpr
              refine ⟨Hyp.floating c_float var_spec, h_float_in, ?_⟩
              rfl
            have h_in_stack : σ var_spec ∈ stack := by
              rw [h_stack_eq]
              exact List.mem_append_left _ (List.mem_reverse.mpr h_in_needed)
            -- By IH, exprToFormula vm (σ var_spec) is provable
            have h_prov := ih (σ var_spec) h_in_stack
            -- h_prov : Provable axs Γ (exprToFormula vm (σ var_spec))
            -- σ_declarative v = exprToDeclarativeExpr vm (σ var_spec)
            -- toDeclarativeSubst_findVar: when findVar vmAx v = some var_spec,
            -- toDeclarativeSubst vmAx vm σ v = exprToDeclarativeExpr vm (σ var_spec)
            have h_sigma_eq : σ_declarative v = exprToDeclarativeExpr vm (σ var_spec) :=
              toDeclarativeSubst_findVar h_findVar_eq
            rw [h_sigma_eq]
            -- Goal: Provable ... (v.type, exprToDeclarativeExpr vm (σ var_spec))
            -- exprToFormula vm (σ var_spec) = ((σ var_spec).typecode.c, exprToDeclarativeExpr vm (σ var_spec))
            have h_formula_eq : (v.type, exprToDeclarativeExpr vm (σ var_spec)) =
                exprToFormula vm (σ var_spec) := by
              unfold exprToFormula
              rw [h_type_connect]
            rw [h_formula_eq]
            exact h_prov

          -- Sub-goal 3: Show the result formula matches
          -- We need: exprToFormula vm (applySubst frAx.vars σ eAx) = ax.fmla.subst σ_declarative
          -- where ax.fmla = exprToFormula vmAx eAx
          have h_result : exprToFormula vm (Spec.applySubst frAx.vars σ eAx) =
                          (exprToFormula vmAx eAx).subst σ_declarative := by
            -- Typecodes match: applySubst preserves typecode
            -- Expressions match: by exprToDeclarativeExpr_applySubst_eq_subst
            unfold exprToFormula Metamath.Formula.subst
            -- Goal: (typecode, exprToDeclarativeExpr vm (applySubst ...)) =
            --       (typecode, (exprToDeclarativeExpr vmAx eAx).subst σ_declarative)
            congr 1
            -- Now just the expression part
            exact exprToDeclarativeExpr_applySubst_eq_subst h_wf h_ax h_fr_disjoint

          -- Apply Provable.ax and rewrite goal
          rw [h_result]
          exact Derivable.ax σ_declarative h_ax_in h_dv_declarative h_hyps_ess h_hyps_var
      | tail _ h_tail =>
          have h_mem' : e' ∈ needed.reverse ++ remaining :=
            (List.mem_append).2 (Or.inr h_tail)
          have h_mem_stack : e' ∈ stack := by
            simpa [h_stack_eq] using h_mem'
          exact ih e' h_mem_stack

/-- Any element on a valid proof stack is canonically Mario-provable. -/
theorem proofValid_stack_provable {Γ : Database} {consts : ConstSet} {fr : Frame}
    {stack : List Expr} {steps : List ProofStep}
    (h_wf : Spec.WellFormedDatabase Γ consts)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr) :
    ProofValid Γ fr stack steps →
    ∀ e ∈ stack,
      Declarative.Provable (dbToAxioms Γ) (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  intro h e h_mem
  exact (proofValid_stack_frameDerivable h_wf h_fr_disjoint h e h_mem).toDeclarative

/-- Forward direction: If we have a valid operational proof ending with [e],
    then e is provable in Mario's semantic system. -/
theorem proofValid_to_declarative {Γ : Database} {consts : ConstSet} {fr : Frame} {e : Expr}
    {steps : List ProofStep}
    (h_wf : Spec.WellFormedDatabase Γ consts)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr) :
    ProofValid Γ fr [e] steps →
    Declarative.Provable (dbToAxioms Γ) (frameToContext fr)
      (exprToFormula (varMapOfFrame fr) e) := by
  intro h
  have h_all := proofValid_stack_provable h_wf h_fr_disjoint h
  simpa using h_all e (by simp)

/-! ## Backward Direction: Mario.Provable → ProofValid

This direction is trickier because Mario's system doesn't track the proof stack.
We need to show that IF something is provable in Mario's system,
THEN we can construct SOME operational proof (may not be the same steps).

This is the **completeness** direction - showing our verifier is complete with
respect to Mario's semantic specification.

**Status**: COMPLETE. The backward direction (`frameDerivable_to_proofValid`) is fully proven
at line 3498 below. The implementation-level completeness theorem
`verify_impl_complete` in KernelCorrectness.lean establishes the full biconditional.
-/

/-! ### Completeness: Mario → Operational

The structure of the proof:
1. Induct on Mario's `Provable`
2. For each case, extract the formula structure
3. Find corresponding operational proof steps
4. Build `ProofValid` witnesses

Key insight: Mario's `Provable.hyp` and `Provable.var` are base cases that
correspond to our `useEssential`, `useFloating` steps. The `Provable.ax`
case requires recursive proof construction.
-/

/-- Helper: Convert a Mario formula back to our Expr (partial inverse of exprToFormula).
    Returns None if the formula doesn't correspond to a valid Expr structure. -/
noncomputable def declarativeFormulaToExpr (vm : VarMap) (f : Declarative.Formula) : Option Expr :=
  let (tc, syms) := f
  -- Convert Mario symbols back to our symbols
  let spec_syms := syms.filterMap fun s =>
    match s with
    | Metamath.Sym.const c => some c
    | Metamath.Sym.var vr =>
        -- Find the variable in our varmap
        match findVar vm vr with
        | some v => some v.v
        | none => none  -- Variable not in context
  if spec_syms.length = syms.length then
    some ⟨⟨tc⟩, spec_syms⟩
  else
    none

/-- A formula in the context (hypothesis) corresponds to some Expr or variable formula.
    Requires FloatUnique to ensure floating hypothesis formulas have matching types. -/
theorem hyp_formula_is_expr {fr : Frame} {h : Declarative.Formula}
    (h_unique : FloatUnique fr)
    (h_mem : h ∈ (frameToContext fr).hyps) :
    (∃ e : Expr, h = exprToFormula (varMapOfFrame fr) e) ∨
    (∃ v : DeclarativeVR, h = (v.type, [Metamath.Sym.var v])) := by
  obtain ⟨hyp, h_in, h_eq⟩ := hyps_correspondence h_mem
  cases hyp with
  | essential e =>
      left
      rw [h_eq, hypToDeclarativeFormula_essential]
      exact ⟨e, rfl⟩
  | floating c v =>
      right
      rw [h_eq]
      unfold hypToDeclarativeFormula
      -- Get the VR for this variable with type information
      obtain ⟨vr, h_findVR, h_type_eq⟩ := findVR_of_float_typed h_unique h_in
      simp only [h_findVR]
      -- Goal: (c.c, [Sym.var vr]) = (vr.type, [Sym.var vr])
      -- We have h_type_eq : vr.type = c.c, so use its symmetry
      refine ⟨vr, ?_⟩
      apply Prod.ext
      · exact h_type_eq.symm
      · rfl

/-- Helper: If two expressions have equal formulas, their components match. -/
theorem exprToFormula_inj {vm : VarMap} {e e' : Expr}
    (h_eq : exprToFormula vm e = exprToFormula vm e') :
    e.typecode.c = e'.typecode.c ∧ exprToDeclarativeExpr vm e = exprToDeclarativeExpr vm e' := by
  unfold exprToFormula at h_eq
  -- h_eq : (e.typecode.c, exprToDeclarativeExpr vm e) = (e'.typecode.c, exprToDeclarativeExpr vm e')
  have h := Prod.mk.inj h_eq
  exact ⟨h.1, h.2⟩

/-! ### Const/Var Separation for Provable Formulas

Constants in provable formulas are not variable names in the proof context.
This follows from Metamath's global const/var separation:
- Constants are declared with $c, variables with $v
- A symbol can only be declared one way
- Floating hypotheses bind variables, not constants
- Therefore, constants in proofs cannot be variable names
-/

/-- Trace constant membership through substitution.
    If a constant c is in e.subst σ, then either:
    1. c was already in e (as a constant), or
    2. c came from σ vr for some variable vr in e -/
theorem mem_const_subst {σ : Metamath.VR → Metamath.Expr} {c : Metamath.CN} :
    {e : Metamath.Expr} →
    Metamath.Sym.const c ∈ e.subst σ →
    (Metamath.Sym.const c ∈ e) ∨ (∃ vr, vr ∈' e ∧ Metamath.Sym.const c ∈ σ vr)
  | [], h_mem => nomatch h_mem
  | Metamath.Sym.const c' :: rest, h_mem =>
      -- e = const c' :: rest, subst gives const c' :: rest.subst σ
      match h_mem with
      | List.Mem.head _ =>
          -- c = c', so .const c was already in e
          Or.inl (List.Mem.head _)
      | List.Mem.tail _ h_tail =>
          -- c is in rest.subst σ
          match mem_const_subst h_tail with
          | Or.inl h_in_rest => Or.inl (List.Mem.tail _ h_in_rest)
          | Or.inr ⟨vr, h_vr_in, h_c_in⟩ =>
              -- h_vr_in : vr ∈' rest = var vr ∈ rest
              -- Need: vr ∈' (const c' :: rest) = var vr ∈ (const c' :: rest)
              Or.inr ⟨vr, List.Mem.tail _ h_vr_in, h_c_in⟩
  | Metamath.Sym.var vr :: rest, h_mem =>
      -- e = var vr :: rest, subst gives σ vr ++ rest.subst σ
      match List.mem_append.mp h_mem with
      | Or.inl h_in_sigma =>
          -- c is in σ vr
          -- Need: vr ∈' (var vr :: rest) = var vr ∈ (var vr :: rest)
          Or.inr ⟨vr, List.Mem.head _, h_in_sigma⟩
      | Or.inr h_in_rest =>
          -- c is in rest.subst σ
          match mem_const_subst h_in_rest with
          | Or.inl h_in_rest' => Or.inl (List.Mem.tail _ h_in_rest')
          | Or.inr ⟨vr', h_vr_in, h_c_in⟩ =>
              -- h_vr_in : vr' ∈' rest = var vr' ∈ rest
              -- Need: vr' ∈' (var vr :: rest) = var vr' ∈ (var vr :: rest)
              Or.inr ⟨vr', List.Mem.tail _ h_vr_in, h_c_in⟩

/-- Constants in a Mario expression are not variable names in the frame.
    This is the key property needed for the DV constraint proof. -/
def DeclarativeExprConstSep (fr : Frame) (me : DeclarativeExpr) : Prop :=
  ∀ c, Metamath.Sym.const c ∈ me → Variable.mk c ∉ fr.vars

/-- Provable formulas maintain const/var separation.

    The key insight is that constants in provable formulas must have been
    declared as constants (not variables) in the database. Since floating
    hypotheses only bind declared variables, constants cannot be in fr.vars.

    This is proven by induction on Provable:
    - hyp case: hypotheses come from the database and respect const/var separation
    - var case: formula is (v.type, [.var v]) with no constants
    - ax case: axiom formulas come from database, substitution preserves the property
-/
theorem provable_const_separation {Γ : Database} {consts : ConstSet} {fr : Frame} {fmla : DeclarativeFormula}
    (h_wf : WellFormedDatabaseStrong Γ consts)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr)
    (h_provable : Declarative.Provable (dbToAxioms Γ) (frameToContext fr) fmla) :
    DeclarativeExprConstSep fr fmla.2 := by
  induction h_provable with
  | hyp h h_in =>
      -- h ∈ (frameToContext fr).hyps
      -- h comes from fr.hyps via hypToDeclarativeFormula
      -- By construction, constants in h are from the database
      intro c h_c_mem
      -- h is a hypothesis formula from the frame
      -- Get the hyp that produced this formula
      obtain ⟨hyp, hyp_in, hyp_eq⟩ := hyps_correspondence h_in
      cases hyp with
      | essential e_hyp =>
          -- Essential hypothesis formula: exprToFormula vm e_hyp
          simp only [hypToDeclarativeFormula_essential] at hyp_eq
          -- hyp_eq : h = exprToFormula vm e_hyp
          -- h.2 = exprToDeclarativeExpr vm e_hyp = e_hyp.syms.map (toDeclarativeSym vm)
          -- h_c_mem : Metamath.Sym.const c ∈ h.2
          have h_snd_eq : h.2 = exprToDeclarativeExpr (varMapOfFrame fr) e_hyp := by
            rw [hyp_eq]; rfl
          rw [h_snd_eq] at h_c_mem
          unfold exprToDeclarativeExpr at h_c_mem
          -- h_c_mem : .const c ∈ e_hyp.syms.map (toDeclarativeSym vm)
          obtain ⟨s, _, h_s_eq⟩ := List.mem_map.mp h_c_mem
          -- h_s_eq : toDeclarativeSym vm s = .const c
          -- toDeclarativeSym checks findVR and returns either .const or .var
          cases h_find : findVR (varMapOfFrame fr) ⟨s⟩ with
          | none =>
              -- toDeclarativeSym returns .const s when findVR = none
              have h_reduce : toDeclarativeSym (varMapOfFrame fr) s = Metamath.Sym.const s := by
                unfold toDeclarativeSym
                simp only [h_find]
              rw [h_reduce] at h_s_eq
              have h_c_eq_s : s = c := Metamath.Sym.const.inj h_s_eq
              -- Need to show Variable.mk c ∉ fr.vars
              -- Since findVR vm ⟨s⟩ = none and c = s, Variable.mk c ∉ fr.vars
              subst h_c_eq_s
              intro h_in_vars
              -- h_in_vars : Variable.mk s ∈ fr.vars
              -- By varMapDomain_ofFrame, this means findVR vm ⟨s⟩ = some _
              have h_exists := (varMapDomain_ofFrame fr ⟨s⟩).1 h_in_vars
              obtain ⟨vr, h_vr⟩ := h_exists
              rw [h_find] at h_vr
              cases h_vr
          | some vr =>
              -- toDeclarativeSym returns .var vr, contradicts h_s_eq = .const c
              have h_reduce : toDeclarativeSym (varMapOfFrame fr) s = Metamath.Sym.var vr := by
                unfold toDeclarativeSym
                simp only [h_find]
              rw [h_reduce] at h_s_eq
              cases h_s_eq  -- .var vr ≠ .const c
      | floating tc v =>
          -- Floating hypothesis formula: (tc.c, [.var vr])
          -- hypToDeclarativeFormula always produces (tc.c, [.var vr]) for floating
          -- where vr is either found via findVR or a default ⟨tc.c, 0⟩
          -- In either case, h.2 = [.var vr], which contains no constants
          have h_snd_form : ∃ vr', h.2 = [Metamath.Sym.var vr'] := by
            cases h_findVR : findVR (varMapOfFrame fr) v with
            | none =>
                simp only [hypToDeclarativeFormula, h_findVR] at hyp_eq
                exact ⟨⟨tc.c, 0⟩, by rw [hyp_eq]⟩
            | some vr =>
                simp only [hypToDeclarativeFormula, h_findVR] at hyp_eq
                exact ⟨vr, by rw [hyp_eq]⟩
          obtain ⟨vr', h_snd_eq⟩ := h_snd_form
          rw [h_snd_eq] at h_c_mem
          -- h_c_mem : .const c ∈ [.var vr']
          -- The only element is .var vr', but .const c ≠ .var vr'
          cases h_c_mem with
          | tail _ h_tail => nomatch h_tail

  | var v =>
      -- Formula is (v.type, [.var v])
      -- The only symbol is .var v, which is not .const c
      intro c h_c_mem
      -- h_c_mem : .const c ∈ [.var v]
      cases h_c_mem with
      | tail _ h_tail => nomatch h_tail

  | ax σ h_axs h_dj h_hyps h_hyps_var ih_h ih_var =>
      -- (implicit ax).fmla.subst σ - substituted axiom formula
      -- Constants come from: (1) axiom formula constants, (2) σ vr for each VR
      -- By IH on h_hyps_var, each variable's typing respects const/var separation
      intro c h_c_mem
      -- c is in the substituted formula fmla.2 where fmla is the goal formula

      -- Get the axiom info from database
      obtain ⟨l, frAx, eAx, h_lookup, h_ctx_eq, h_fmla_eq⟩ := dbToAxioms_inverse h_axs
      have h_wf_base : Spec.WellFormedDatabase Γ consts := h_wf.1
      let vmAx := varMapOfFrame frAx
      -- The implicit ax satisfies (from dbToAxioms_inverse):
      -- - ax.ctx = frameToContext frAx
      -- - ax.fmla = exprToFormula vmAx eAx
      -- So ax.vars = (ax.fmla :: ax.ctx.hyps).flatMap (·.snd.vars)

      -- h_fmla_eq : ax.fmla = exprToFormula vmAx eAx
      -- The goal is DeclarativeExprConstSep fr fmla.2 where fmla = ax.fmla.subst σ
      -- So fmla.2 = ax.fmla.2.subst σ = (exprToFormula vmAx eAx).2.subst σ = (exprToDeclarativeExpr vmAx eAx).subst σ

      -- h_c_mem : .const c ∈ fmla.2 = (exprToDeclarativeExpr vmAx eAx).subst σ
      have h_c_in_subst : Metamath.Sym.const c ∈ (exprToDeclarativeExpr vmAx eAx).subst σ := by
        simp only [Metamath.Formula.subst] at h_c_mem
        -- Need to rewrite using h_fmla_eq
        have h_fmla_snd : exprToDeclarativeExpr vmAx eAx = (exprToFormula vmAx eAx).2 := rfl
        rw [h_fmla_snd, ← h_fmla_eq]
        exact h_c_mem

      -- Use mem_const_subst to trace where .const c came from
      match mem_const_subst h_c_in_subst with
      | Or.inl h_in_orig =>
          -- Case 1: .const c was in exprToDeclarativeExpr vmAx eAx originally
          -- By WellFormedDatabase, c is a global constant (not in any frame's vars)
          unfold exprToDeclarativeExpr at h_in_orig
          obtain ⟨s, h_s_in, h_s_eq⟩ := List.mem_map.mp h_in_orig
          -- s ∈ eAx.syms, toDeclarativeSym vmAx s = .const c
          match h_find : findVR vmAx ⟨s⟩ with
          | none =>
              -- s is not a variable, so toDeclarativeSym returns .const s
              have h_const : toDeclarativeSym vmAx s = Metamath.Sym.const s := by
                unfold toDeclarativeSym; simp only [h_find]
              rw [h_const] at h_s_eq
              have h_c_eq : s = c := Metamath.Sym.const.inj h_s_eq
              subst h_c_eq
              -- Need: Variable.mk s ∉ fr.vars
              -- By varMapDomain_ofFrame, s ∉ frAx.vars (since findVR = none)
              intro h_in_vars
              -- s is in eAx.syms and not in frAx.vars
              -- By WellFormedDatabase, it must be a global constant
              have h_s_not_in_frAx : Variable.mk s ∉ frAx.vars := by
                intro h_contra
                have h_some := (varMapDomain_ofFrame frAx ⟨s⟩).1 h_contra
                obtain ⟨vr, h_vr⟩ := h_some
                rw [h_find] at h_vr
                cases h_vr
              -- By const_global_of_wellFormed, s is a global constant
              have h_const : consts s :=
                Spec.const_global_of_wellFormed h_wf_base h_lookup s h_s_in h_s_not_in_frAx
              have h_disj := h_fr_disjoint (Variable.mk s) h_in_vars
              exact (h_disj h_const).elim
          | some vr =>
              -- s is a variable, so toDeclarativeSym returns .var vr
              -- But h_s_eq says it equals .const c - contradiction
              have h_var : toDeclarativeSym vmAx s = Metamath.Sym.var vr := by
                unfold toDeclarativeSym; simp only [h_find]
              rw [h_var] at h_s_eq
              cases h_s_eq  -- .var vr ≠ .const c
      | Or.inr ⟨vr, h_vr_in, h_c_in_sigma⟩ =>
          -- Case 2: .const c came from σ vr for some variable vr in the axiom formula
          -- h_vr_in : vr ∈' (exprToDeclarativeExpr vmAx eAx)
          -- Need to show vr ∈ ax.vars to use ih_var
          -- ax.vars = (ax.fmla :: ax.ctx.hyps).flatMap Formula.vars
          -- Since ax.fmla = exprToFormula vmAx eAx, we have ax.fmla.snd = exprToDeclarativeExpr vmAx eAx
          -- vr ∈' ax.fmla.snd implies vr ∈ ax.fmla.snd.vars implies vr ∈ ax.vars
          have h_vr_in_fmla_expr : vr ∈ (exprToDeclarativeExpr vmAx eAx).vars := Metamath.Expr.mem_vars_iff.mpr h_vr_in
          have h_fmla_snd_eq : (exprToFormula vmAx eAx).snd = exprToDeclarativeExpr vmAx eAx := rfl
          have h_vr_in_ax_fmla_vars : vr ∈ (exprToFormula vmAx eAx).snd.vars := h_fmla_snd_eq ▸ h_vr_in_fmla_expr
          -- The implicit ax has ax.vars, and ih_var expects vr ∈ ax.vars
          -- We pass the membership proof directly to ih_var (Lean infers the target set)
          have h_ih : DeclarativeExprConstSep fr (σ vr) := ih_var vr (by
            simp only [Metamath.Statement.vars, List.flatMap_cons, List.mem_append]
            left
            rw [h_fmla_eq]
            exact h_vr_in_ax_fmla_vars)
          -- h_ih says: ∀ c', .const c' ∈ σ vr → Variable.mk c' ∉ fr.vars
          exact h_ih c h_c_in_sigma

/-- Frame-derivable formulas satisfy const/var separation. -/
theorem frameDerivable_const_separation {Γ : Database} {consts : ConstSet} {fr : Frame} {fmla : DeclarativeFormula}
    (h_wf : WellFormedDatabaseStrong Γ consts)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr)
    (h_provable : FrameDerivable Γ fr fmla) :
    DeclarativeExprConstSep fr fmla.2 :=
  provable_const_separation h_wf h_fr_disjoint h_provable.toDeclarative

/-- Generalized completeness: any provable formula can be operationally proved.

This is the general form needed for induction. We show that if a formula fmla
is Mario-provable and fmla = exprToFormula vm e for some e, then Provable Γ fr e.

Requires WellFormedDatabaseStrong to ensure:
- FloatUnique: each variable has at most one typecode (for typecode preservation)
- FloatVarNoDup: no duplicate variables in floating hypotheses (for VR uniqueness)

Also requires FloatVarNoDup fr for the target frame (needed for substitution roundtrip).
-/
theorem frameDerivable_to_proofValid_aux {Γ : Database} {consts : ConstSet} {fr : Frame}
    (h_wf_strong : WellFormedDatabaseStrong Γ consts)
    (h_fr_nodup : FloatVarNoDup fr)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr)
    {fmla : Declarative.Formula}
    (h_declarative : FrameDerivable Γ fr fmla)
    {e : Expr}
    (h_eq : fmla = exprToFormula (varMapOfFrame fr) e) :
    Provable Γ fr e := by
  -- Extract the basic well-formedness
  have h_wf : Spec.WellFormedDatabase Γ consts := h_wf_strong.1
  -- Induct on the Mario proof structure
  induction h_declarative generalizing e with
  | hyp h h_in =>
      -- Case 1: The formula h is a hypothesis in the context
      -- h_in : h ∈ (frameToContext fr).hyps
      -- h_eq : h = exprToFormula vm e
      rw [h_eq] at h_in
      -- Now h_in : exprToFormula vm e ∈ (frameToContext fr).hyps
      -- By hyps_correspondence, get the Hyp that produced this formula
      obtain ⟨hyp, hyp_in, hyp_eq⟩ := hyps_correspondence h_in
      -- hyp_eq : exprToFormula vm e = hypToDeclarativeFormula vm hyp
      cases hyp with
      | essential e' =>
          -- hypToDeclarativeFormula vm (Hyp.essential e') = exprToFormula vm e'
          -- So exprToFormula vm e = exprToFormula vm e'
          simp only [hypToDeclarativeFormula_essential] at hyp_eq
          -- hyp_eq : exprToFormula vm e = exprToFormula vm e'
          -- By injectivity, e' = e
          have h_eq_expr := exprToFormula_eq_of_eq_frame hyp_eq.symm
          -- h_eq_expr : e' = e
          -- Rewrite goal to prove Provable Γ fr e'
          rw [← h_eq_expr]
          -- Now goal is: Provable Γ fr e'
          -- Build proof: one step, push e' to stack
          exact ⟨[ProofStep.useHyp (Hyp.essential e')], [e'],
                 ProofValid.useEssential fr [] [] e' hyp_in (ProofValid.nil fr), rfl⟩
      | floating c v =>
          -- hypToDeclarativeFormula vm (Hyp.floating c v) = (c.c, [.var vr])
          -- Use hypToDeclarativeFormula_floating_expr to relate to exprToFormula
          let vm := varMapOfFrame fr
          obtain ⟨vr, h_findVR⟩ := findVR_of_float (fr := fr) (c := c) (v := v) hyp_in
          have h_float_eq := hypToDeclarativeFormula_floating_expr vm c v h_findVR
          -- h_float_eq : hypToDeclarativeFormula vm (Hyp.floating c v) = exprToFormula vm ⟨c, [v.v]⟩
          rw [h_float_eq] at hyp_eq
          -- hyp_eq : exprToFormula vm e = exprToFormula vm ⟨c, [v.v]⟩
          have h_eq_expr := exprToFormula_eq_of_eq_frame hyp_eq.symm
          -- h_eq_expr : ⟨c, [v.v]⟩ = e
          rw [← h_eq_expr]
          -- Goal: Provable Γ fr ⟨c, [v.v]⟩
          -- ProofValid.useFloating pushes ⟨c, [v.v]⟩
          exact ⟨[ProofStep.useHyp (Hyp.floating c v)], [⟨c, [v.v]⟩],
                 ProofValid.useFloating fr [] [] c v hyp_in (ProofValid.nil fr), rfl⟩
  | var v =>
      -- Case 2: The formula is (v.type, [.var v])
      -- h_eq : (v.type, [.var v]) = exprToFormula vm e
      -- Unpack the formula equality
      let vm := varMapOfFrame fr
      have h_eq' : exprToFormula vm e = (v.type, [Metamath.Sym.var v]) := h_eq.symm
      unfold exprToFormula exprToDeclarativeExpr at h_eq'
      have h_parts := Prod.mk.inj h_eq'
      -- h_parts.1 : e.typecode.c = v.type
      -- h_parts.2 : e.syms.map toDeclarativeSym = [.var v]
      -- From h_parts.2, e.syms is a singleton [s] with toDeclarativeSym vm s = .var v
      match h_syms : e.syms with
      | [] =>
          -- Contradiction: [].map toDeclarativeSym = [] ≠ [.var v]
          simp only [h_syms, List.map_nil] at h_parts
          cases h_parts.2
      | [s] =>
          -- e.syms = [s] and [toDeclarativeSym vm s] = [.var v]
          simp only [h_syms, List.map_cons, List.map_nil] at h_parts
          -- h_parts.1 : e.typecode.c = v.type
          -- h_parts.2 : [toDeclarativeSym vm s] = [.var v]
          -- Extract the element equality
          have h_toDeclarative : toDeclarativeSym vm s = Metamath.Sym.var v := by
            have := List.cons.inj h_parts.2
            exact this.1
          have h_findVR : findVR vm ⟨s⟩ = some v := by
            unfold toDeclarativeSym at h_toDeclarative
            match h_find : findVR vm ⟨s⟩ with
            | none =>
                simp only [h_find] at h_toDeclarative
                cases h_toDeclarative  -- .const s ≠ .var v
            | some vr =>
                simp only [h_find] at h_toDeclarative
                have h_vr_eq := Metamath.Sym.var.inj h_toDeclarative
                rw [h_vr_eq]
          -- Get the floating hypothesis for this variable
          have h_mem := findVR_mem_of_some h_findVR
          obtain ⟨c, h_float, h_type_eq⟩ := mem_varMapOfFrame_sound_typed h_mem
          -- h_float : Hyp.floating c ⟨s⟩ ∈ fr.hyps
          -- h_type_eq : v.type = c.c
          -- Show e = ⟨c, [s]⟩
          have h_expr_eq : e = ⟨c, [s]⟩ := by
            -- e.typecode.c = v.type (from h_parts.1)
            -- v.type = c.c (from h_type_eq)
            -- e.syms = [s] (from h_syms)
            have h_tc_c : e.typecode.c = c.c := by rw [h_parts.1, h_type_eq]
            -- Expr equality is typecode + syms
            cases e with | mk tc syms_e =>
            simp only at h_syms h_tc_c
            simp only [Expr.mk.injEq]
            constructor
            · -- tc = c
              cases tc with | mk tc_str =>
              cases c with | mk c_str =>
              simp only [Constant.mk.injEq] at h_tc_c ⊢
              exact h_tc_c
            · exact h_syms
          rw [h_expr_eq]
          -- Goal: Provable Γ fr ⟨c, [s]⟩ = Provable Γ fr ⟨c, [⟨s⟩.v]⟩
          exact ⟨[ProofStep.useHyp (Hyp.floating c ⟨s⟩)], [⟨c, [s]⟩],
                 ProofValid.useFloating fr [] [] c ⟨s⟩ h_float (ProofValid.nil fr), rfl⟩
      | s :: s' :: rest =>
          -- Contradiction: list length mismatch
          simp only [h_syms, List.map_cons] at h_parts
          -- h_parts.2 : [toDeclarativeSym s, ...] = [.var v], length mismatch
          have := List.cons.inj h_parts.2
          cases this.2
  | ax σ h_axs h_dj h_hyps h_hyps_var ih_h ih_var =>
      -- Case 3: The formula comes from applying an axiom with substitution
      -- The implicit ax is a Statement such that dbToAxioms Γ ax
      -- σ : DeclarativeVR → DeclarativeExpr
      -- h_dj : DJ.subst σ ax.ctx.dj (frameToContext fr).dj
      -- h_hyps : ∀ h ∈ ax.ctx.hyps, Provable (dbToAxioms Γ) (frameToContext fr) (h.subst σ)
      -- h_hyps_var : ∀ v ∈ ax.vars, Provable (dbToAxioms Γ) (frameToContext fr) (v.type, σ v)
      -- ih : IH for essential hypotheses
      -- ih_var : IH for variable typing
      -- h_eq : ax.fmla.subst σ = exprToFormula (varMapOfFrame fr) e

      -- Step 1: Extract the axiom info from database
      let vm := varMapOfFrame fr
      obtain ⟨l, frAx, eAx, h_lookup, h_ctx_eq, h_fmla_eq⟩ := dbToAxioms_inverse h_axs
      -- h_lookup : Γ l = some (frAx, eAx)
      -- h_ctx_eq : ax.ctx = frameToContext frAx (where ax is implicit)
      -- h_fmla_eq : ax.fmla = exprToFormula (varMapOfFrame frAx) eAx

      let vmAx := varMapOfFrame frAx

      -- Step 2: Define our substitution σ'
      let σ' := declarativeSubstToSpec vmAx vm σ

      -- Step 3: Build Provable for the goal expression
      -- The key is that:
      -- - h_eq : ax.fmla.subst σ = exprToFormula vm e
      -- - h_fmla_eq : ax.fmla = exprToFormula vmAx eAx
      -- We need to connect these via the substitution correspondence

      -- For now, use the direct structure from fromDeclarativeFormula
      -- The goal e is given by h_eq, so we just need to prove Provable Γ fr e

      -- The structure for ProofValid.useAxiom:
      -- 1. We have h_lookup : Γ l = some (frAx, eAx) ✓
      -- 2. Need: dvOK fr.vars frAx.dv fr.dv σ'
      -- 3. Need: ∀ c v, Hyp.floating c v ∈ frAx.hyps → (σ' v).typecode = c
      -- 4. Need: ProofValid building up the hypothesis stack
      -- 5. Need: stack structure matching needed.reverse ++ remaining

      -- PART A: FloatUnique and DVWellFormed from strong well-formedness
      have h_wf_frame := h_wf_strong.2 l frAx eAx h_lookup
      have h_frameWf : FrameWellFormed frAx := h_wf_frame.1
      have h_dvWf : DVWellFormed frAx := h_wf_frame.2
      have h_floatUnique : FloatUnique frAx := h_frameWf.1
      have h_floatVarNoDup : FloatVarNoDup frAx := h_frameWf.2

      -- PART B: Typecode preservation for floating hypotheses
      have h_typecode : ∀ c v, Hyp.floating c v ∈ frAx.hyps → (σ' v).typecode = c := by
        intro c v h_float
        exact declarativeSubstToSpec_float_typecode h_floatUnique h_float

      -- PART C: DV constraint preservation (DJ.subst → dvOK)
      -- h_dj ensures variables in substituted expressions from disjoint axiom
      -- variables are disjoint in the theorem's context.
      have h_dvOK : Spec.dvOK fr.vars frAx.dv fr.dv σ' := by
        -- Rewrite h_dj using h_ctx_eq to work with dvListToDeclarativeDJ
        have h_ctx_dj : (frameToContext frAx).dj = dvListToDeclarativeDJ vmAx frAx.dv := rfl
        have h_fr_dj : (frameToContext fr).dj = dvListToDeclarativeDJ vm fr.dv := rfl
        rw [h_ctx_eq, h_ctx_dj, h_fr_dj] at h_dj
        -- Now h_dj : DJ.subst σ (dvListToDeclarativeDJ vmAx frAx.dv) (dvListToDeclarativeDJ vm fr.dv)

        -- Unfold dvOK goal and introduce variables
        unfold Spec.dvOK
        intro v' w' h_vw_mem
        -- Now goal has let bindings for vs and ws, then ∀ x ∈ vs, ∀ y ∈ ws, dvRel ...
        simp only []
        intro x' h_x'_mem y' h_y'_mem
        -- Goal: dvRel fr.dv x' y'

        -- Case split on findVR for v' and w'
        cases h_findVR_v' : findVR vmAx v' with
        | none =>
            -- v' is not a variable in vmAx - but this contradicts DVWellFormed!
            -- By DVWellFormed, (v', w') ∈ frAx.dv implies v' ∈ frAx.vars
            have h_v'_in_frAx_vars : v' ∈ frAx.vars := (h_dvWf.1 v' w' h_vw_mem).1
            -- By varMapDomain_ofFrame, v' ∈ frAx.vars means findVR vmAx v' = some _
            have h_exists_vr : ∃ vr, findVR vmAx v' = some vr :=
              (varMapDomain_ofFrame frAx v').1 h_v'_in_frAx_vars
            -- This contradicts h_findVR_v' = none
            obtain ⟨vr_v', h_vr_v'⟩ := h_exists_vr
            rw [h_findVR_v'] at h_vr_v'
            cases h_vr_v'

        | some vr_v' =>
            -- v' maps to vr_v' in vmAx
            cases h_findVR_w' : findVR vmAx w' with
            | none =>
                -- w' is not a variable in vmAx - but this contradicts DVWellFormed!
                -- By DVWellFormed, (v', w') ∈ frAx.dv implies w' ∈ frAx.vars
                have h_w'_in_frAx_vars : w' ∈ frAx.vars := (h_dvWf.1 v' w' h_vw_mem).2
                -- By varMapDomain_ofFrame, w' ∈ frAx.vars means findVR vmAx w' = some _
                have h_exists_vr : ∃ vr, findVR vmAx w' = some vr :=
                  (varMapDomain_ofFrame frAx w').1 h_w'_in_frAx_vars
                -- This contradicts h_findVR_w' = none
                obtain ⟨vr_w', h_vr_w'⟩ := h_exists_vr
                rw [h_findVR_w'] at h_vr_w'
                cases h_vr_w'

            | some vr_w' =>
                -- MAIN CASE: Both v' and w' have VRs
                -- Step 1: Prove vr_v' ≠ vr_w' (needed for DJ.mk'.disj which requires a ≠ b)
                have h_vr_neq : vr_v' ≠ vr_w' := by
                  intro h_eq
                  -- With vr_v' = vr_w', we have v' = w' by findVR injectivity
                  have h_v'_eq_w' : v' = w' := findVR_injective_frame h_findVR_v' (h_eq ▸ h_findVR_w')
                  subst h_v'_eq_w'
                  -- Now h_vw_mem : (v', v') ∈ frAx.dv
                  -- But DVWellFormed says no self-pairs: h_dvWf.2 v' : (v', v') ∉ frAx.dv
                  exact h_dvWf.2 v' h_vw_mem

                -- Step 2: Construct DJ.disj using vr_v' ≠ vr_w'
                have h_dj_vr : (dvListToDeclarativeDJ vmAx frAx.dv).disj vr_v' vr_w' := by
                  simp only [dvListToDeclarativeDJ, Metamath.DJ.mk']
                  constructor
                  · exact h_vr_neq
                  · left
                    simp only [List.mem_filterMap]
                    exact ⟨(v', w'), h_vw_mem, by simp only [h_findVR_v', h_findVR_w']⟩

                -- Step 3: Apply h_dj to get Expr.disjoint
                have h_expr_disj := h_dj vr_v' vr_w' h_dj_vr
                -- h_expr_disj : (σ vr_v').disjoint (dvListToDeclarativeDJ vm fr.dv) (σ vr_w')
                unfold Metamath.Expr.disjoint at h_expr_disj

                -- Step 3: Connect σ' to σ via declarativeSubstToSpec
                have h_sigma_v' : σ' v' = ⟨⟨vr_v'.type⟩, fromDeclarativeExpr vm (σ vr_v')⟩ :=
                  declarativeSubstToSpec_findVR h_findVR_v'
                have h_sigma_w' : σ' w' = ⟨⟨vr_w'.type⟩, fromDeclarativeExpr vm (σ vr_w')⟩ :=
                  declarativeSubstToSpec_findVR h_findVR_w'

                -- Step 4: Show vr_v' ∈ ax.vars via floating hypothesis membership,
                -- then use h_hyps_var to get Provable for the substituted expression.
                have h_vr_v'_prov := h_hyps_var vr_v' (by
                  -- Show vr_v' ∈ ax.vars via floating hypothesis membership
                  -- 1. findVR success implies v' ∈ frAx.vars
                  have h_v'_in_vars : v' ∈ frAx.vars := findVR_in_vars h_findVR_v'
                  -- 2. By var_mem_iff_float, there's a floating hypothesis for v'
                  obtain ⟨c_float, h_float_in⟩ := var_mem_iff_float.mp h_v'_in_vars
                  -- 3. This hypothesis maps into (frameToContext frAx).hyps
                  have h_hyp_in_ctx : hypToDeclarativeFormula vmAx (Hyp.floating c_float v') ∈
                      (frameToContext frAx).hyps := hypToDeclarativeFormula_mem h_float_in
                  -- 4. The floating formula's .2 is [Sym.var vr_v']
                  have h_float_eq := hypToDeclarativeFormula_floating_expr vmAx c_float v' h_findVR_v'
                  have h_snd_eq : (hypToDeclarativeFormula vmAx (Hyp.floating c_float v')).2 =
                      [Metamath.Sym.var vr_v'] := by
                    rw [h_float_eq]
                    unfold exprToFormula exprToDeclarativeExpr
                    simp only [List.map_cons, List.map_nil]
                    exact congrArg (fun x => [x]) (toDeclarativeSym_var h_findVR_v')
                  -- 5. vr_v' ∈ [Sym.var vr_v'].vars
                  have h_vr_in_snd : vr_v' ∈ Metamath.Expr.vars [Metamath.Sym.var vr_v'] := by
                    simp only [Metamath.Expr.vars, List.filterMap_cons, List.filterMap_nil]
                    exact List.mem_singleton_self _
                  -- 6. Therefore vr_v' ∈ ax.vars (via h_ctx_eq rewriting ax.ctx)
                  simp only [Metamath.Statement.vars, List.mem_flatMap, h_ctx_eq]
                  refine ⟨hypToDeclarativeFormula vmAx (Hyp.floating c_float v'), ?_, ?_⟩
                  · right; exact h_hyp_in_ctx
                  · rw [h_snd_eq]; exact h_vr_in_snd)
                have h_sep_v := frameDerivable_const_separation h_wf_strong h_fr_disjoint h_vr_v'_prov
                have h_wf_v : ∀ c, Metamath.Sym.const c ∈ (σ vr_v') → Variable.mk c ∉ fr.vars := h_sep_v

                have h_vr_w'_prov := h_hyps_var vr_w' (by
                  -- Show vr_w' ∈ ax.vars via floating hypothesis membership
                  -- 1. findVR success implies w' ∈ frAx.vars
                  have h_w'_in_vars : w' ∈ frAx.vars := findVR_in_vars h_findVR_w'
                  -- 2. By var_mem_iff_float, there's a floating hypothesis for w'
                  obtain ⟨c_float, h_float_in⟩ := var_mem_iff_float.mp h_w'_in_vars
                  -- 3. This hypothesis maps into (frameToContext frAx).hyps
                  have h_hyp_in_ctx : hypToDeclarativeFormula vmAx (Hyp.floating c_float w') ∈
                      (frameToContext frAx).hyps := hypToDeclarativeFormula_mem h_float_in
                  -- 4. The floating formula's .2 is [Sym.var vr_w']
                  have h_float_eq := hypToDeclarativeFormula_floating_expr vmAx c_float w' h_findVR_w'
                  have h_snd_eq : (hypToDeclarativeFormula vmAx (Hyp.floating c_float w')).2 =
                      [Metamath.Sym.var vr_w'] := by
                    rw [h_float_eq]
                    unfold exprToFormula exprToDeclarativeExpr
                    simp only [List.map_cons, List.map_nil]
                    exact congrArg (fun x => [x]) (toDeclarativeSym_var h_findVR_w')
                  -- 5. vr_w' ∈ [Sym.var vr_w'].vars
                  have h_vr_in_snd : vr_w' ∈ Metamath.Expr.vars [Metamath.Sym.var vr_w'] := by
                    simp only [Metamath.Expr.vars, List.filterMap_cons, List.filterMap_nil]
                    exact List.mem_singleton_self _
                  -- 6. Therefore vr_w' ∈ ax.vars (via h_ctx_eq rewriting ax.ctx)
                  simp only [Metamath.Statement.vars, List.mem_flatMap, h_ctx_eq]
                  refine ⟨hypToDeclarativeFormula vmAx (Hyp.floating c_float w'), ?_, ?_⟩
                  · right; exact h_hyp_in_ctx
                  · rw [h_snd_eq]; exact h_vr_in_snd)
                have h_sep_w := frameDerivable_const_separation h_wf_strong h_fr_disjoint h_vr_w'_prov
                have h_wf_w : ∀ c, Metamath.Sym.const c ∈ (σ vr_w') → Variable.mk c ∉ fr.vars := h_sep_w

                -- Step 5: Extract VRs from memberships
                simp only [h_sigma_v', Spec.varsInExpr] at h_x'_mem
                simp only [h_sigma_w', Spec.varsInExpr] at h_y'_mem

                -- VR well-formedness from provable_wellformed
                have h_vr_wf_v' : DeclarativeExprWellFormed fr (σ vr_v') :=
                  frameDerivable_wellFormed h_vr_v'_prov
                have h_vr_wf_w' : DeclarativeExprWellFormed fr (σ vr_w') :=
                  frameDerivable_wellFormed h_vr_w'_prov

                obtain ⟨x_vr, h_x_vr_in, h_x_vr_findVar⟩ := fromDeclarativeFormula_varsInExpr_to_vr h_x'_mem h_wf_v h_vr_wf_v'
                obtain ⟨y_vr, h_y_vr_in, h_y_vr_findVar⟩ := fromDeclarativeFormula_varsInExpr_to_vr h_y'_mem h_wf_w h_vr_wf_w'

                -- Step 6: Apply disjointness and convert back
                have h_xy_dj := h_expr_disj x_vr y_vr h_x_vr_in h_y_vr_in
                exact dvListToDeclarativeDJ_to_dvRel h_xy_dj h_x_vr_findVar h_y_vr_findVar

      -- PART D: The result expression
      -- From h_eq : ax.fmla.subst σ = exprToFormula vm e
      -- and h_fmla_eq : ax.fmla = exprToFormula vmAx eAx
      -- We get: (exprToFormula vmAx eAx).subst σ = exprToFormula vm e
      -- We need: applySubst frAx.vars σ' eAx = e
      -- This requires the inverse substitution correspondence

      -- Define the result we'll produce
      let resultExpr := Spec.applySubst frAx.vars σ' eAx

      -- Show resultExpr = e using the roundtrip
      have h_result_eq : resultExpr = e := by
        -- First, combine h_eq and h_fmla_eq
        have h_subst_eq : (exprToFormula vmAx eAx).subst σ = exprToFormula vm e := by
          rw [← h_fmla_eq]
          exact h_eq

        -- Extract components from h_subst_eq
        -- Formula.subst σ (c, me) = (c, me.subst σ)
        -- So h_subst_eq : (eAx.typecode.c, (exprToDeclarativeExpr vmAx eAx).subst σ) = (e.typecode.c, exprToDeclarativeExpr vm e)
        unfold exprToFormula at h_subst_eq
        have h_pair := Prod.mk.inj h_subst_eq
        -- h_pair.1 : eAx.typecode.c = e.typecode.c
        -- h_pair.2 : (exprToDeclarativeExpr vmAx eAx).subst σ = exprToDeclarativeExpr vm e

        -- Goal: applySubst frAx.vars σ' eAx = e
        -- Show via Expr.ext (typecode match + syms match)

        -- Typecode: applySubst preserves typecode
        have h_tc_apply : (Spec.applySubst frAx.vars σ' eAx).typecode = eAx.typecode := by
          unfold Spec.applySubst; rfl
        -- Combined: (applySubst ...).typecode.c = e.typecode.c
        have h_tc_eq : (Spec.applySubst frAx.vars σ' eAx).typecode.c = e.typecode.c := by
          rw [h_tc_apply]
          exact h_pair.1

        -- Symbols: use exprToDeclarativeExpr_applySubst_eq_subst
        have h_apply_subst : exprToDeclarativeExpr vm (Spec.applySubst frAx.vars σ' eAx) =
            (exprToDeclarativeExpr vmAx eAx).subst (toDeclarativeSubst vmAx vm σ') :=
          exprToDeclarativeExpr_applySubst_eq_subst h_wf h_lookup h_fr_disjoint

        -- Need to show: toDeclarativeSubst vmAx vm σ' = σ on VRs in exprToDeclarativeExpr vmAx eAx
        -- This requires the roundtrip theorem with well-formedness
        have h_subst_ext : (exprToDeclarativeExpr vmAx eAx).subst (toDeclarativeSubst vmAx vm σ') =
                           (exprToDeclarativeExpr vmAx eAx).subst σ := by
          -- Use Expr_subst_ext to reduce to pointwise equality on VRs
          apply Expr_subst_ext
          intro vr h_vr_mem
          -- vr ∈' exprToDeclarativeExpr vmAx eAx
          -- VRs in exprToDeclarativeExpr come from variables in eAx that are in frAx.vars
          -- For such VRs, findVar vmAx vr = some v for some v

          -- Get findVar for vr from membership in axiom expression
          have h_vr_in_varmap : ∃ v, findVar vmAx vr = some v := by
            obtain ⟨s, _, h_find⟩ := exprToDeclarativeExpr_mem_extract h_vr_mem
            exact ⟨⟨s⟩, findVR_findVar_inverse_frame h_find⟩

          obtain ⟨v, h_findVar⟩ := h_vr_in_varmap

          -- Get well-formedness for σ vr from IH
          -- vr is in ax.vars (implicit) because it appears in exprToDeclarativeExpr vmAx eAx = ax.fmla.snd
          -- Pass membership proof directly to h_hyps_var (Lean infers the target set)
          have h_vr_prov := h_hyps_var vr (by
            simp only [Metamath.Statement.vars, List.flatMap_cons, List.mem_append]
            left
            -- vr ∈' ax.fmla.snd where ax.fmla = exprToFormula vmAx eAx (from h_fmla_eq)
            have h_fmla_snd_eq : (exprToFormula vmAx eAx).snd = exprToDeclarativeExpr vmAx eAx := rfl
            rw [h_fmla_eq, h_fmla_snd_eq]
            exact Metamath.Expr.mem_vars_iff.mpr h_vr_mem)

          -- DeclarativeExprWellFormed: VRs in σ vr are in target frame
          have h_wf_vr : DeclarativeExprWellFormed fr (σ vr) :=
            frameDerivable_wellFormed h_vr_prov

          -- DeclarativeExprConstSeparated: constants in σ vr aren't variable names
          -- Convert DeclarativeExprConstSep to DeclarativeExprConstSeparated via varMapDomain_ofFrame
          have h_sep_vr : DeclarativeExprConstSeparated fr (σ vr) := by
            have h_constSep : DeclarativeExprConstSep fr (σ vr) :=
              frameDerivable_const_separation h_wf_strong h_fr_disjoint h_vr_prov
            -- DeclarativeExprConstSep says: Variable.mk c ∉ fr.vars
            -- DeclarativeExprConstSeparated says: findVR vm ⟨c⟩ = none
            -- These are equivalent by varMapDomain_ofFrame
            intro c h_c_mem
            have h_not_in_vars := h_constSep c h_c_mem
            -- By varMapDomain, v ∈ fr.vars ↔ ∃ vr, findVR vm v = some vr
            -- So v ∉ fr.vars ↔ findVR vm v = none
            cases h_find : findVR (varMapOfFrame fr) ⟨c⟩ with
            | none => rfl
            | some vr' =>
                -- findVR vm ⟨c⟩ = some vr' means ⟨c⟩ ∈ fr.vars
                have h_in_vars := (varMapDomain_ofFrame fr ⟨c⟩).2 ⟨vr', h_find⟩
                exact absurd h_in_vars h_not_in_vars

          -- Apply roundtrip theorem
          exact toDeclarativeSubst_declarativeSubstToSpec_roundtrip
            h_floatVarNoDup h_fr_nodup h_findVar h_wf_vr h_sep_vr

        -- Combine: exprToDeclarativeExpr vm (applySubst ...) = exprToDeclarativeExpr vm e
        have h_expr_eq : exprToDeclarativeExpr vm (Spec.applySubst frAx.vars σ' eAx) = exprToDeclarativeExpr vm e := by
          rw [h_apply_subst, h_subst_ext, h_pair.2]

        -- By injectivity, get symbol equality
        have h_syms_eq : (Spec.applySubst frAx.vars σ' eAx).syms = e.syms :=
          exprToDeclarativeExpr_syms_inj_frame h_expr_eq

        -- Construct the expression equality
        have h_tc_full : (Spec.applySubst frAx.vars σ' eAx).typecode = e.typecode := by
          -- Constant is a structure with one field .c
          -- If .c fields match, the structs match
          have h_c_eq := h_tc_eq
          cases hA : (Spec.applySubst frAx.vars σ' eAx).typecode with | mk cA =>
          cases hE : e.typecode with | mk cE =>
          simp only [hA, hE] at h_c_eq
          simp only [hA, hE, h_c_eq]
        -- Build Expr equality using structure eta
        calc Spec.applySubst frAx.vars σ' eAx
            = ⟨(Spec.applySubst frAx.vars σ' eAx).typecode,
               (Spec.applySubst frAx.vars σ' eAx).syms⟩ := rfl
          _ = ⟨e.typecode, e.syms⟩ := by rw [h_tc_full, h_syms_eq]
          _ = e := rfl

      -- PART E: Build the proof using IH for each hypothesis
      -- Since Provable is a Prop, we use Classical reasoning to extract proof steps.

      -- Use the result equality to transform the goal
      rw [← h_result_eq]
      -- Goal is now: Provable Γ fr resultExpr = Provable Γ fr (applySubst frAx.vars σ' eAx)

      -- Build Provable for result using ProofValid.useAxiom
      -- We need to show there exist steps and a stack [resultExpr] with ProofValid

      -- The key is building the hypothesis stack from frAx.hyps
      -- For now, we construct a simple proof showing the structure exists

      -- Use Classical.choice to extract proof witnesses from IH
      -- Each hypothesis in frAx.hyps has a Provable via ih

      -- Build the needed stack: substituted hypotheses in reverse order
      let neededStack := frAx.hyps.map (fun h => match h with
        | Hyp.essential e_hyp => Spec.applySubst frAx.vars σ' e_hyp
        | Hyp.floating _ v => σ' v)

      -- For each essential hypothesis, ih gives us Provable
      -- For floating hypotheses, we use ProofValid.useFloating directly

      -- This construction is sound but complex; the key pieces are:
      -- 1. h_lookup : Γ l = some (frAx, eAx) - lookup succeeds
      -- 2. h_dvOK : dvOK ... - DV constraints satisfied
      -- 3. h_typecode : typecode preservation
      -- 4. ih : each hypothesis is provable (from Provable.ax premise)

      -- The full proof uses ProofValidFrom to build up the stack,
      -- then ProofValid.useAxiom to produce the result.
      -- Since Provable is a Prop, we construct it by building the stack from hypotheses.

      -- Strategy: For each hypothesis in frAx.hyps, we have a Provable.
      -- We need to compose these proofs to build the hypothesis stack,
      -- then apply ProofValid.useAxiom.

      -- The key insight is that Provable is existential, so we extract
      -- proof witnesses and compose them using ProofValidFrom.trans.

      -- For essential hypotheses: ih gives Provable after conversion
      -- For floating hypotheses: we use ProofValid.useFloating directly

      -- Build the hypothesis stack using induction on frAx.hyps
      -- Each step adds one hypothesis to the stack

      -- This construction is tedious but straightforward - the pieces are:
      -- 1. Each essential hyp h: ih (exprToFormula vmAx h) gives Provable for h.subst σ
      --    which corresponds to applySubst frAx.vars σ' h
      -- 2. Each floating hyp (c, v): ih (↑vr) gives Provable for σ' v
      --    where vr corresponds to v in vmAx
      -- 3. Compose using ProofValidFrom.trans
      -- 4. Apply ProofValidFrom.useAxiom to get the result

      -- The composition requires careful ordering: neededStack.reverse
      -- since ProofValid pops from the top of stack

      -- For now, we use Classical.choice to extract witnesses and build the proof
      -- This is valid since Provable is a Prop (proof-irrelevant)

      -- FINAL STEP: Build the proof using ProofValid.useAxiom
      --
      -- Strategy:
      -- 1. For each h ∈ frAx.hyps, we get Provable Γ fr (substituted h) from ih
      -- 2. Compose these using ProofValidFrom.trans to build the hypothesis stack
      -- 3. Apply ProofValidFrom.useAxiom with all preconditions
      -- 4. Convert to Provable via toProvable
      --
      -- Preconditions already proven:
      -- - h_lookup : Γ l = some (frAx, eAx)
      -- - h_dvOK : dvOK fr.vars frAx.dv fr.dv σ'
      -- - h_typecode : ∀ c v, Hyp.floating c v ∈ frAx.hyps → (σ' v).typecode = c
      --
      -- The IH handles each hypothesis:
      -- - Essential h: ih (exprToFormula vmAx h) gives Provable for (applySubst frAx.vars σ' h)
      -- - Floating (c,v): ih (↑vr) gives Provable for σ' v
      --
      -- The composition is constructive but requires careful formula conversions
      -- similar to h_result_eq reasoning for each hypothesis.
      -- Build hypothesis stack using induction on frAx.hyps
      -- Each hypothesis h ∈ frAx.hyps has Provable Γ fr (substitute h)
      -- Compose to build the needed stack, then apply useAxiom

      -- Define needed stack (matches ProofValid.useAxiom format)
      let needed := frAx.hyps.map (fun h => match h with
        | Hyp.essential e_hyp => Spec.applySubst frAx.vars σ' e_hyp
        | Hyp.floating _ v => σ' v)

      -- Build the hypothesis stack proof by folding over frAx.hyps
      -- This uses the IH to get Provable for each hypothesis
      have h_hyps_provable : ∀ h ∈ frAx.hyps, Provable Γ fr (match h with
          | Hyp.essential e_hyp => Spec.applySubst frAx.vars σ' e_hyp
          | Hyp.floating _ v => σ' v) := by
        intro hyp h_in
        cases hyp with
        | essential e_hyp =>
            -- ih gives Provable after formula conversion
            -- ax.ctx.hyps = (frameToContext frAx).hyps = frAx.hyps.map (hypToDeclarativeFormula vmAx)
            have h_formula_in : hypToDeclarativeFormula vmAx (Hyp.essential e_hyp) ∈
                (frameToContext frAx).hyps := hypToDeclarativeFormula_mem h_in
            rw [← h_ctx_eq] at h_formula_in

            -- Prove formula equality using substitution correspondence
            have h_formula_eq : (hypToDeclarativeFormula vmAx (Hyp.essential e_hyp)).subst σ =
                exprToFormula vm (Spec.applySubst frAx.vars σ' e_hyp) := by
              unfold hypToDeclarativeFormula exprToFormula
              simp only [Metamath.Formula.subst]
              apply Prod.ext
              · -- Typecode equality: applySubst preserves typecode
                simp only [Spec.applySubst]
              · -- Expression equality via roundtrip
                -- Step 1: exprToDeclarativeExpr_applySubst_eq_subst_hyp gives direction with toDeclarativeSubst
                have h_apply_subst : exprToDeclarativeExpr vm (Spec.applySubst frAx.vars σ' e_hyp) =
                    Metamath.Expr.subst (toDeclarativeSubst vmAx vm σ') (exprToDeclarativeExpr vmAx e_hyp) :=
                  exprToDeclarativeExpr_applySubst_eq_subst_hyp h_wf h_lookup h_in h_fr_disjoint

                -- Step 2: Show toDeclarativeSubst vmAx vm σ' = σ extensionally on vars in e_hyp
                have h_subst_ext : Metamath.Expr.subst (toDeclarativeSubst vmAx vm σ') (exprToDeclarativeExpr vmAx e_hyp) =
                    Metamath.Expr.subst σ (exprToDeclarativeExpr vmAx e_hyp) := by
                  apply Expr_subst_ext
                  intro vr h_vr_mem
                  -- vr appears in exprToDeclarativeExpr vmAx e_hyp
                  -- Need: findVar vmAx vr = some v, WF, and constSep for roundtrip

                  -- Get findVar for vr from membership in hypothesis expression
                  have h_vr_in_varmap : ∃ v, findVar vmAx vr = some v := by
                    obtain ⟨s, _, h_find⟩ := exprToDeclarativeExpr_mem_extract h_vr_mem
                    exact ⟨⟨s⟩, findVR_findVar_inverse_frame h_find⟩
                  obtain ⟨v, h_findVar⟩ := h_vr_in_varmap

                  -- Show vr is in Statement.vars (via hypothesis membership)
                  -- Use h_hyps_var directly with an inline membership proof
                  have h_vr_prov := h_hyps_var vr (by
                    simp only [Metamath.Statement.vars, List.mem_flatMap, h_ctx_eq, h_fmla_eq]
                    have h_hyp_in_ctx : hypToDeclarativeFormula vmAx (Hyp.essential e_hyp) ∈
                        (frameToContext frAx).hyps := hypToDeclarativeFormula_mem h_in
                    have h_snd_eq : (hypToDeclarativeFormula vmAx (Hyp.essential e_hyp)).snd =
                        exprToDeclarativeExpr vmAx e_hyp := rfl
                    refine ⟨hypToDeclarativeFormula vmAx (Hyp.essential e_hyp), List.mem_cons_of_mem _ h_hyp_in_ctx, ?_⟩
                    rw [h_snd_eq]
                    exact Metamath.Expr.mem_vars_iff.mpr h_vr_mem)

                  -- Get well-formedness and const-separation from h_vr_prov
                  have h_wf_vr : DeclarativeExprWellFormed fr (σ vr) :=
                    frameDerivable_wellFormed h_vr_prov
                  have h_sep_vr : DeclarativeExprConstSeparated fr (σ vr) := by
                    have h_constSep : DeclarativeExprConstSep fr (σ vr) :=
                      frameDerivable_const_separation h_wf_strong h_fr_disjoint h_vr_prov
                    intro c h_c_mem
                    have h_not_in_vars := h_constSep c h_c_mem
                    cases h_find : findVR vm ⟨c⟩ with
                    | none => rfl
                    | some vr' =>
                        have h_in_vars := (varMapDomain_ofFrame fr ⟨c⟩).2 ⟨vr', h_find⟩
                        exact absurd h_in_vars h_not_in_vars

                  -- Apply roundtrip (goal is toDeclarativeSubst vmAx vm σ' vr = σ vr)
                  exact toDeclarativeSubst_declarativeSubstToSpec_roundtrip
                    h_floatVarNoDup h_fr_nodup h_findVar h_wf_vr h_sep_vr

                -- Combine: LHS = RHS (Prod.snd reduces to the second component)
                show Metamath.Expr.subst σ (exprToDeclarativeExpr vmAx e_hyp) =
                     exprToDeclarativeExpr vm (Spec.applySubst frAx.vars σ' e_hyp)
                exact (h_apply_subst.trans h_subst_ext).symm

            exact ih_h (hypToDeclarativeFormula vmAx (Hyp.essential e_hyp)) h_formula_in h_formula_eq
        | floating c v =>
            -- ih_var gives Provable for σ' v
            -- Get the VR for v
            obtain ⟨vr, h_findVR⟩ := findVR_of_float (fr := frAx) (c := c) (v := v) h_in

            -- Build membership proof inline (Lean infers the Statement type)
            have h_vr_mem_proof : vr ∈ (List.flatMap
                (fun f => Metamath.Expr.vars f.2)
                ((exprToFormula vmAx eAx) :: (frameToContext frAx).hyps)) := by
              simp only [List.mem_flatMap]
              have h_hyp_in_ctx : hypToDeclarativeFormula vmAx (Hyp.floating c v) ∈
                  (frameToContext frAx).hyps := hypToDeclarativeFormula_mem h_in
              have h_float_eq := hypToDeclarativeFormula_floating_expr vmAx c v h_findVR
              have h_snd_eq : (hypToDeclarativeFormula vmAx (Hyp.floating c v)).2 =
                  [Metamath.Sym.var vr] := by
                rw [h_float_eq]
                unfold exprToFormula exprToDeclarativeExpr
                simp only [List.map_cons, List.map_nil]
                exact congrArg (fun x => [x]) (toDeclarativeSym_var h_findVR)
              have h_vr_in_snd : vr ∈ Metamath.Expr.vars [Metamath.Sym.var vr] := by
                simp only [Metamath.Expr.vars, List.filterMap_cons, List.filterMap_nil]
                exact List.mem_singleton_self _
              exact ⟨hypToDeclarativeFormula vmAx (Hyp.floating c v), List.mem_cons_of_mem _ h_hyp_in_ctx, h_snd_eq ▸ h_vr_in_snd⟩

            -- Use rewriting to match h_hyps_var and ih_var expected type
            have h_vr_in_ax_vars : vr ∈ ((exprToFormula vmAx eAx) :: (frameToContext frAx).hyps).flatMap (·.2.vars) :=
              h_vr_mem_proof

            -- Get Mario provability
            have h_prov_declarative := h_hyps_var vr (by
              simp only [Metamath.Statement.vars, h_fmla_eq, h_ctx_eq]
              exact h_vr_in_ax_vars)

            -- Build formula equality: (vr.type, σ vr) = exprToFormula vm (σ' v)
            have h_sigma_eq := declarativeSubstToSpec_findVR (vm := vm) (σ := σ) h_findVR
            have h_formula_eq : (vr.type, σ vr) = exprToFormula vm (σ' v) := by
              -- Unfold σ' to match h_sigma_eq
              show (vr.type, σ vr) = exprToFormula vm (declarativeSubstToSpec vmAx vm σ v)
              rw [h_sigma_eq]
              unfold exprToFormula
              apply Prod.ext
              · rfl
              · -- fromDeclarativeExpr/exprToDeclarativeExpr roundtrip
                simp only [exprToDeclarativeExpr]
                have h_wf_sigma := frameDerivable_wellFormed h_prov_declarative
                have h_constSep := frameDerivable_const_separation h_wf_strong h_fr_disjoint h_prov_declarative
                -- Convert DeclarativeExprConstSep to DeclarativeExprConstSeparated
                have h_sep_sigma : DeclarativeExprConstSeparated fr (σ vr) := by
                  intro s h_s_mem
                  have h_not_in_vars := h_constSep s h_s_mem
                  cases h_find : findVR vm ⟨s⟩ with
                  | none => rfl
                  | some vr' =>
                      have h_in_vars := (varMapDomain_ofFrame fr ⟨s⟩).2 ⟨vr', h_find⟩
                      exact absurd h_in_vars h_not_in_vars
                exact (exprToDeclarativeExpr_fromDeclarativeExpr_wellFormed h_fr_nodup h_wf_sigma h_sep_sigma).symm

            -- Use ih_var to get operational provability
            exact ih_var vr (by simp only [Metamath.Statement.vars, h_fmla_eq, h_ctx_eq]; exact h_vr_in_ax_vars) h_formula_eq

      -- Use build_hyps_proof to construct the needed stack
      -- This is a fold over frAx.hyps that composes Provable proofs
      have h_needed_stack : ∃ steps, ProofValid Γ fr (needed.reverse) steps := by
        -- First, show each element of needed has a Provable proof
        have h_each : ∀ e ∈ needed, Provable Γ fr e := by
          intro e h_mem
          obtain ⟨hyp, h_in, rfl⟩ := List.mem_map.mp h_mem
          exact h_hyps_provable hyp h_in
        -- Suffices to show ProofValidFrom Γ fr [] needed.reverse steps
        suffices ∃ steps, ProofValidFrom Γ fr [] needed.reverse steps by
          obtain ⟨steps, h⟩ := this
          exact ⟨steps, h.toProofValid⟩
        -- Use a helper that includes the hypothesis in the goal
        suffices ∀ (es : List Expr), (∀ e ∈ es, Provable Γ fr e) →
                   ∃ steps, ProofValidFrom Γ fr [] es.reverse steps by
          exact this needed h_each
        -- Induction on the list with hypothesis included
        intro es h_es
        induction es with
        | nil => exact ⟨[], ProofValidFrom.nil fr []⟩
        | cons e rest ih =>
            -- IH gives proof for rest.reverse
            have h_rest_each : ∀ e' ∈ rest, Provable Γ fr e' :=
              fun e' h => h_es e' (List.mem_cons_of_mem e h)
            obtain ⟨steps_rest, h_valid_rest⟩ := ih h_rest_each
            -- Get proof for e
            have h_e : Provable Γ fr e := h_es e List.mem_cons_self
            obtain ⟨steps_e, finalStack_e, h_valid_e, h_stack_e⟩ := h_e
            rw [h_stack_e] at h_valid_e
            -- Convert to ProofValidFrom
            have h_from_e := h_valid_e.toFrom
            -- Key insight: e should end up at BOTTOM of stack, not top
            -- So we push e first, then build rest.reverse on top
            -- Use append_suffix on IH with suffix [e] to build rest.reverse on top of [e]
            have h_rest_on_e := h_valid_rest.append_suffix [e]
            -- h_rest_on_e : ProofValidFrom Γ fr [e] (rest.reverse ++ [e]) steps_rest
            -- Compose: [] → [e] → (rest.reverse ++ [e])
            have h_composed := ProofValidFrom.trans h_from_e h_rest_on_e
            -- Goal: (e :: rest).reverse = rest.reverse ++ [e] ✓
            simp only [List.reverse_cons]
            exact ⟨steps_rest ++ steps_e, h_composed⟩

      obtain ⟨hyp_steps, h_hyp_valid⟩ := h_needed_stack

      -- Apply ProofValid.useAxiom
      refine ⟨ProofStep.useAssertion l σ' :: hyp_steps, [Spec.applySubst frAx.vars σ' eAx], ?_, rfl⟩
      exact ProofValid.useAxiom fr (needed.reverse) hyp_steps l frAx eAx σ'
        h_lookup h_dvOK h_typecode h_hyp_valid needed rfl [] (by simp)

theorem frameDerivable_to_proofValid {Γ : Database} {consts : ConstSet} {fr : Frame} {e : Expr}
    (h_wf : WellFormedDatabaseStrong Γ consts)
    (h_fr_nodup : FloatVarNoDup fr)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr)
    (h_declarative : FrameDerivable Γ fr (exprToFormula (varMapOfFrame fr) e)) :
    Provable Γ fr e :=
  frameDerivable_to_proofValid_aux h_wf h_fr_nodup h_fr_disjoint h_declarative rfl

/-- Operational provability implies frame derivability. -/
theorem operational_to_frameDerivable {Γ : Database} {consts : ConstSet} {fr : Frame} {e : Expr}
    (h_wf : WellFormedDatabaseStrong Γ consts)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr) :
    Provable Γ fr e →
    FrameDerivable Γ fr (exprToFormula (varMapOfFrame fr) e) := by
  intro h_prov
  rcases h_prov with ⟨steps, finalStack, h_valid, h_stack⟩
  rw [h_stack] at h_valid
  exact proofValid_stack_frameDerivable h_wf.1 h_fr_disjoint h_valid e (by simp)

/-- Soundness: operational provability implies Mario's declarative provability
in the frame context. -/
theorem operational_to_declarative {Γ : Database} {consts : ConstSet} {fr : Frame} {e : Expr}
    (h_wf : WellFormedDatabaseStrong Γ consts)
    (h_fr_disjoint : Spec.FrameVarsDisjointConsts consts fr) :
    Provable Γ fr e →
    Declarative.Provable (dbToAxioms Γ) (frameToContext fr)
      (exprToFormula (varMapOfFrame fr) e) := by
  intro h_prov
  rcases h_prov with ⟨steps, finalStack, h_valid, h_stack⟩
  rw [h_stack] at h_valid
  exact proofValid_to_declarative h_wf.1 h_fr_disjoint h_valid

/-! ## Design Notes

**Why this is hard**:
1. **Type mismatch**: Mario uses indexed variables (VR), we use strings
2. **Stack vs declarative**: We track proof stack, Mario doesn't
3. **DJ vs dv list**: Different representations of disjoint variables
4. **Substitution**: Need to prove our applySubst matches Mario's Expr.subst

**Strategy**:
1. Use Bridge.lean conversions for type translation
2. Prove conversion lemmas (roundtrip theorems from Bridge)
3. Show each ProofValid constructor corresponds to Mario.Provable
4. For backward direction, reconstruct proof steps from Mario's derivation

**Status** (no sorries): `proofValid_to_declarative` (soundness);
`operational_to_frameDerivable` and `frameDerivable_to_proofValid` (operational
provability is frame derivability).
-/

end Metamath.Spec.Equivalence
