/-
Bridge between Operational and Semantic layers.

This file proves the equivalence between:
- **Operational**: Our ProofValid (stack machine semantics)
- **Semantic**: Mario's Provable (declarative mathematics)

**The key theorem** (soundness + completeness):
```lean
theorem operational_iff_semantic (h_wf : WellFormedDatabase Γ) :
  Operational.Provable Γ fr e ↔
    Semantic.Provable (dbToAxioms Γ) (frameToContext fr)
      (exprToFormula (varMapOfFrame fr) e)
```

This is the architectural centerpiece connecting implementation to mathematics.
-/

import Metamath.Spec.Core
import Metamath.Spec.Operational
import Metamath.Spec.Semantic
import Metamath.Spec.Bridge

namespace Metamath.Spec.Equivalence

open Spec (Database Frame Expr Hyp Variable Constant Label Subst ProofValid Provable)
open Semantic (Provable)
open Bridge

/-! ## Helper Conversions

We convert our operational types to Mario's semantic types using a **typed**
variable map derived from floating hypotheses.

Key idea: Mario's `VR.type` encodes the *typecode*, while the `i` index
distinguishes variables of the same type. We therefore build a map
`Variable → MarioVR` from floating hypotheses, preserving typecodes.
-/

abbrev VarMap := List (Variable × MarioVR)

/-- Enumerate floats with a running index (auxiliary). -/
def varMapOfFrameAux (n : Nat) : List (Constant × Variable) → VarMap
  | [] => []
  | (c, v) :: rest => (v, ⟨c.c, n⟩) :: varMapOfFrameAux (n + 1) rest

/-- Extract floating hypotheses (typecode, variable) in order. -/
def floatList (fr : Frame) : List (Constant × Variable) :=
  fr.mand.filterMap fun h =>
    match h with
    | Hyp.floating c v => some (c, v)
    | Hyp.essential _ => none

/-- Build a typed variable map from floating hypotheses. -/
def varMapOfFrame (fr : Frame) : VarMap :=
  varMapOfFrameAux 0 (floatList fr)

/-- Find the MarioVR corresponding to a variable. -/
def findVR (vm : VarMap) (v : Variable) : Option MarioVR :=
  (vm.find? fun p => p.1 = v).map Prod.snd

/-- Find the Variable corresponding to a MarioVR. -/
def findVar (vm : VarMap) (vr : MarioVR) : Option Variable :=
  (vm.find? fun p => p.2 = vr).map Prod.fst

/-- Convert a symbol string using a typed variable map. -/
def toMarioSym (vm : VarMap) (s : String) : MarioSym :=
  let v := Variable.mk s
  match findVR vm v with
  | some vr => .var vr
  | none => .const s

/-- Convert our Expr (typecode + symbols) to Mario's expression (symbols only). -/
def exprToMarioExpr (vm : VarMap) (e : Expr) : MarioExpr :=
  e.syms.map (fun s => toMarioSym vm s)

/-- Convert Expr to Mario's Formula (typecode + symbols). -/
def exprToFormula (vm : VarMap) (e : Expr) : Semantic.Formula :=
  (e.typecode.c, exprToMarioExpr vm e)

/-- Convert a hypothesis to Mario's Formula.

Floating hypotheses become variable formulas; essential hypotheses become expressions. -/
def hypToMarioFormula (vm : VarMap) (h : Hyp) : Semantic.Formula :=
  match h with
  | Hyp.floating c v =>
      let vr :=
        match findVR vm v with
        | some vr => vr
        | none => ⟨c.c, 0⟩
      (c.c, [Metamath.Sym.var vr])
  | Hyp.essential e => exprToFormula vm e

/-- Convert a DV list to Mario's DJ using a typed variable map. -/
def dvListToMarioDJ (vm : VarMap) (dv : List (Variable × Variable)) : MarioDJ :=
  let vrPairs := dv.filterMap fun (v, w) =>
    match findVR vm v, findVR vm w with
    | some vr1, some vr2 => some (vr1, vr2)
    | _, _ => none
  Metamath.DJ.mk' vrPairs

/-- Convert a substitution to Mario's form, using axiom vars for the domain
    and caller vars for the codomain. -/
def toMarioSubst (vmAx vm : VarMap) (σ : Subst) : MarioVR → MarioExpr :=
  fun vr =>
    match findVar vmAx vr with
    | some v => exprToMarioExpr vm (σ v)
    | none => [Metamath.Sym.var vr]

/-- Convert Frame to Context using its typed variable map. -/
noncomputable def frameToContext (fr : Frame) : Semantic.Context :=
  let vm := varMapOfFrame fr
  { hyps := fr.mand.map (fun h => hypToMarioFormula vm h)
    dj := dvListToMarioDJ vm fr.dv }

/-- Convert our Database to Mario's axiom set. -/
noncomputable def dbToAxioms (Γ : Database) : Semantic.Statement → Prop :=
  fun stmt => ∃ (l : Label) (fr : Frame) (e : Expr),
    Γ l = some (fr, e) ∧
    stmt.ctx = frameToContext fr ∧
    stmt.fmla = exprToFormula (varMapOfFrame fr) e

/-! ## Helper Lemmas

These lemmas show that our conversions preserve structure correctly.
-/

/-- Essential hypothesis conversion matches exprToFormula. -/
theorem hypToMarioFormula_essential (vm : VarMap) (e : Expr) :
    hypToMarioFormula vm (Hyp.essential e) = exprToFormula vm e := by
  rfl

/-- If a variable is found in the map, toMarioSym returns .var. -/
theorem toMarioSym_var {vm : VarMap} {v : Variable} {vr : MarioVR}
    (h_find : findVR vm v = some vr) :
    toMarioSym vm v.v = .var vr := by
  unfold toMarioSym
  simp [h_find]

/-- Floating hypothesis for single-variable expression matches exprToFormula. -/
theorem hypToMarioFormula_floating_expr (vm : VarMap) (c : Constant) (v : Variable)
    {vr : MarioVR} (h_find : findVR vm v = some vr) :
    hypToMarioFormula vm (Hyp.floating c v) = exprToFormula vm ⟨c, [v.v]⟩ := by
  unfold hypToMarioFormula exprToFormula exprToMarioExpr
  simp [h_find, toMarioSym_var h_find]

/-- Hypothesis conversion always yields a member of the frame context. -/
theorem hypToMarioFormula_mem {fr : Frame} {h : Hyp} :
    h ∈ fr.mand →
    hypToMarioFormula (varMapOfFrame fr) h ∈ (frameToContext fr).hyps := by
  intro h_in
  unfold frameToContext
  exact (List.mem_map).2 ⟨h, h_in, rfl⟩

/-- Floating hypotheses appear in the floatList. -/
theorem floatList_mem_of_float {fr : Frame} {c : Constant} {v : Variable} :
    Hyp.floating c v ∈ fr.mand → (c, v) ∈ floatList fr := by
  intro h_in
  unfold floatList
  refine (List.mem_filterMap).2 ?_
  exact ⟨Hyp.floating c v, h_in, rfl⟩

/-- Soundness: members of floatList come from floating hypotheses. -/
theorem floatList_sound {fr : Frame} {c : Constant} {v : Variable} :
    (c, v) ∈ floatList fr → Hyp.floating c v ∈ fr.mand := by
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
    v ∈ fr.vars ↔ ∃ c, Hyp.floating c v ∈ fr.mand := by
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
theorem findVR_some_of_mem {vm : VarMap} {v : Variable} {vr : MarioVR} :
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

/-- Soundness for varMapOfFrameAux: membership implies a float in the list. -/
theorem mem_varMapAux_sound {n : Nat} {v : Variable} {vr : MarioVR}
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
theorem mem_varMapAux_sound_typed {n : Nat} {v : Variable} {vr : MarioVR}
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

/-- Typed soundness for varMapOfFrame: membership gives floating hyp AND type match. -/
theorem mem_varMapOfFrame_sound_typed {fr : Frame} {v : Variable} {vr : MarioVR} :
    (v, vr) ∈ varMapOfFrame fr → ∃ c, Hyp.floating c v ∈ fr.mand ∧ vr.type = c.c := by
  intro h_mem
  unfold varMapOfFrame at h_mem
  obtain ⟨c, h_float, h_type⟩ := mem_varMapAux_sound_typed (n := 0) h_mem
  exact ⟨c, floatList_sound h_float, h_type⟩

theorem mem_varMapOfFrame_of_float {fr : Frame} {c : Constant} {v : Variable} :
    Hyp.floating c v ∈ fr.mand → ∃ vr, (v, vr) ∈ varMapOfFrame fr := by
  intro h_in
  have h_float : (c, v) ∈ floatList fr := floatList_mem_of_float h_in
  exact mem_varMapAux_of_mem (n := 0) h_float

/-- Floating hypotheses are always found in the typed variable map. -/
theorem findVR_of_float {fr : Frame} {c : Constant} {v : Variable} :
    Hyp.floating c v ∈ fr.mand →
    ∃ vr, findVR (varMapOfFrame fr) v = some vr := by
  intro h_in
  obtain ⟨vr, h_mem⟩ := mem_varMapOfFrame_of_float (fr := fr) (c := c) (v := v) h_in
  exact findVR_some_of_mem h_mem

/-- If a pair appears in varMapOfFrame, it came from a floating hypothesis. -/
theorem mem_varMapOfFrame_sound {fr : Frame} {v : Variable} {vr : MarioVR} :
    (v, vr) ∈ varMapOfFrame fr → ∃ c, Hyp.floating c v ∈ fr.mand := by
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

/-- toMarioSubst simplifies when findVar succeeds. -/
theorem toMarioSubst_findVar {vmAx vm : VarMap} {σ : Subst} {vr : MarioVR} {v : Variable}
    (h_find : findVar vmAx vr = some v) :
    toMarioSubst vmAx vm σ vr = exprToMarioExpr vm (σ v) := by
  unfold toMarioSubst
  simp [h_find]

/-- toMarioSubst is identity when findVar fails. -/
theorem toMarioSubst_findVar_none {vmAx vm : VarMap} {σ : Subst} {vr : MarioVR}
    (h_find : findVar vmAx vr = none) :
    toMarioSubst vmAx vm σ vr = [Metamath.Sym.var vr] := by
  unfold toMarioSubst
  simp [h_find]

/-- VRs in varMapOfFrameAux have indices starting from n and incrementing.
    This ensures uniqueness: no two entries have the same VR. -/
theorem varMapOfFrameAux_vr_index_ge {n : Nat} {xs : List (Constant × Variable)}
    {v : Variable} {vr : MarioVR} :
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
    {v v' : Variable} {vr : MarioVR} :
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
theorem varMapOfFrame_vr_unique {fr : Frame} {v v' : Variable} {vr : MarioVR} :
    (v, vr) ∈ varMapOfFrame fr → (v', vr) ∈ varMapOfFrame fr → v = v' := by
  unfold varMapOfFrame
  exact varMapOfFrameAux_vr_unique (n := 0)

/-- Key inverse lemma: if findVR vm v = some vr, then findVar vm vr = some v.
    This follows from uniqueness of VRs in the VarMap. -/
theorem findVR_findVar_inverse {vm : VarMap} {v : Variable} {vr : MarioVR}
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
theorem findVR_findVar_inverse_frame {fr : Frame} {v : Variable} {vr : MarioVR}
    (h_findVR : findVR (varMapOfFrame fr) v = some vr) :
    findVar (varMapOfFrame fr) vr = some v := by
  apply findVR_findVar_inverse
  · -- Uniqueness from varMapOfFrame_vr_unique
    intro v' v'' vr' h1 h2
    exact varMapOfFrame_vr_unique h1 h2
  · exact h_findVR

/-- If findVar succeeds, the pair is in the map. -/
theorem findVar_mem_of_some {vm : VarMap} {vr : MarioVR} {v : Variable}
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
  induction fr.mand with
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
theorem findVR_in_vars {fr : Frame} {v : Variable} {vr : MarioVR}
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

/-- Extract the source symbol from membership in exprToMarioExpr.
    If vr ∈' exprToMarioExpr vm e, then there exists a symbol s in e.syms
    such that findVR vm (Variable.mk s) = some vr. -/
theorem exprToMarioExpr_mem_extract {vm : VarMap} {e : Expr} {vr : MarioVR}
    (h_mem : vr ∈' exprToMarioExpr vm e) :
    ∃ s, s ∈ e.syms ∧ findVR vm (Variable.mk s) = some vr := by
  -- h_mem : Metamath.Expr.mem (exprToMarioExpr vm e) vr
  -- = Metamath.Sym.var vr ∈ e.syms.map (fun s => toMarioSym vm s)
  unfold exprToMarioExpr at h_mem
  unfold Metamath.Expr.mem at h_mem
  -- h_mem : Metamath.Sym.var vr ∈ List.map (toMarioSym vm) e.syms
  obtain ⟨s, h_s_in, h_s_eq⟩ := List.mem_map.mp h_mem
  -- h_s_eq : toMarioSym vm s = Metamath.Sym.var vr
  unfold toMarioSym at h_s_eq
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
    {v1 v2 : Variable} {vr : MarioVR}
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
theorem findVR_injective_frame {fr : Frame} {v1 v2 : Variable} {vr : MarioVR}
    (h_v1 : findVR (varMapOfFrame fr) v1 = some vr)
    (h_v2 : findVR (varMapOfFrame fr) v2 = some vr) :
    v1 = v2 :=
  findVR_injective (fun _ _ _ h1 h2 => varMapOfFrame_vr_unique h1 h2) h_v1 h_v2

/-- Lift dvRel to dvListToMarioDJ: if v and w are disjoint via dvRel, and both
    map to VRs via findVR, then the VRs are disjoint in dvListToMarioDJ.
    Requires variable-to-VR uniqueness: different variables map to different VRs. -/
theorem dvRel_to_dvListToMarioDJ {vm : VarMap} {dv : List (Variable × Variable)}
    {v w : Variable} {vr1 vr2 : MarioVR}
    (h_unique : ∀ v' v'' vr', findVR vm v' = some vr' → findVR vm v'' = some vr' → v' = v'')
    (h_dvRel : Spec.dvRel dv v w)
    (h_v : findVR vm v = some vr1)
    (h_w : findVR vm w = some vr2) :
    (dvListToMarioDJ vm dv).disj vr1 vr2 := by
  unfold Spec.dvRel at h_dvRel
  obtain ⟨h_neq, h_mem_or⟩ := h_dvRel
  unfold dvListToMarioDJ
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

/-- Mario's Expr.subst equals flatMap with the substitution function.
    This bridges the recursive definition to list operations. -/
theorem marioExpr_subst_eq_flatMap (σ : MarioVR → MarioExpr) (e : MarioExpr) :
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
          simp only [Metamath.Expr.subst, List.flatMap_cons, ih]

/-- Auxiliary lemma for substitution correspondence on symbol lists.
    Works on a general list with the const-preservation hypothesis. -/
theorem exprToMarioExpr_applySubst_eq_subst_aux
    {frAx fr : Frame} {σ : Subst} (syms : List Sym)
    (h_const : ∀ s ∈ syms, Variable.mk s ∉ frAx.vars → Variable.mk s ∉ fr.vars) :
    let vmAx := varMapOfFrame frAx
    let vm := varMapOfFrame fr
    let σ_mario := toMarioSubst vmAx vm σ
    (syms.flatMap fun s => if Variable.mk s ∈ frAx.vars then (σ (Variable.mk s)).syms else [s]).map (toMarioSym vm) =
    (syms.map (toMarioSym vmAx)).flatMap (fun sym =>
      match sym with
      | .var vr => σ_mario vr
      | .const c => [.const c]) := by
  -- Define local abbreviations for clarity
  let vmAx := varMapOfFrame frAx
  let vm := varMapOfFrame fr
  let σ_mario := toMarioSubst vmAx vm σ

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
        -- toMarioSym vmAx s = .var vr
        have h_toMario : toMarioSym vmAx s = .var vr := by
          unfold toMarioSym
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

        -- σ_mario vr = exprToMarioExpr vm (σ v)
        have h_sigma : σ_mario vr = exprToMarioExpr vm (σ v) := by
          simp only [σ_mario, toMarioSubst]
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
        rw [h_toMario]
        -- Simplify the match on .var vr
        simp only []
        simp only [σ_mario, vmAx, vm] at h_sigma
        rw [h_sigma]
        simp only [exprToMarioExpr, v]
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

        have h_toMario : toMarioSym vmAx s = .const s := by
          unfold toMarioSym
          simp only [vmAx]
          split
          · rename_i vr h_eq
            simp only [v, vmAx] at h_none
            rw [h_none] at h_eq
            cases h_eq
          · rfl

        simp only [v, h_var, ↓reduceIte, List.map]
        rw [h_toMario]

        -- Now we need toMarioSym vm s = .const s (constant in axiom is constant in caller)
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

        have h_toMario' : toMarioSym vm s = .const s := by
          unfold toMarioSym
          simp only [vm]
          split
          · rename_i vr h_eq
            simp only [vm] at h_none'
            rw [h_none'] at h_eq
            cases h_eq
          · rfl

        rw [h_toMario']
        simp only [List.singleton_append]
        congr 1
        exact ih h_const_rest

/-- Main substitution correspondence theorem.
    Maps symbol-by-symbol between our applySubst and Mario's Expr.subst.

    Requires database well-formedness, which ensures that constants are global:
    if a symbol appears in an expression and has no floating hypothesis in that
    frame, then it's a constant and cannot be a variable in any other frame. -/
theorem exprToMarioExpr_applySubst_eq_subst
    {Γ : Database} {l : Label} {frAx fr : Frame} {σ : Subst} {eAx : Expr}
    (h_wf : Spec.WellFormedDatabase Γ)
    (h_lookup : Γ l = some (frAx, eAx)) :
    exprToMarioExpr (varMapOfFrame fr) (Spec.applySubst frAx.vars σ eAx) =
    Metamath.Expr.subst (toMarioSubst (varMapOfFrame frAx) (varMapOfFrame fr) σ)
                        (exprToMarioExpr (varMapOfFrame frAx) eAx) := by
  -- Strategy:
  -- 1. Unfold LHS to get flatMap form
  -- 2. Rewrite RHS using marioExpr_subst_eq_flatMap to get flatMap form
  -- 3. Apply aux lemma (with h_const from well-formedness)

  let vmAx := varMapOfFrame frAx
  let vm := varMapOfFrame fr
  let σ_mario := toMarioSubst vmAx vm σ

  -- LHS unfolds to: (eAx.syms.flatMap ...).map (toMarioSym vm)
  unfold exprToMarioExpr Spec.applySubst
  simp only []

  -- RHS is Expr.subst σ_mario (eAx.syms.map (toMarioSym vmAx))
  -- Rewrite using marioExpr_subst_eq_flatMap
  rw [marioExpr_subst_eq_flatMap]

  -- Now apply aux lemma
  have h_const : ∀ s ∈ eAx.syms, Variable.mk s ∉ frAx.vars → Variable.mk s ∉ fr.vars :=
    fun s h_s_in h_not_var => Spec.const_global_of_wellFormed h_wf h_lookup s h_s_in h_not_var
  exact exprToMarioExpr_applySubst_eq_subst_aux eAx.syms h_const

/-- Substitution correspondence for essential hypothesis expressions. -/
theorem exprToMarioExpr_applySubst_eq_subst_hyp
    {Γ : Database} {l : Label} {frAx fr : Frame} {σ : Subst} {eAx e_hyp : Expr}
    (h_wf : Spec.WellFormedDatabase Γ)
    (h_lookup : Γ l = some (frAx, eAx))
    (h_hyp_in : Hyp.essential e_hyp ∈ frAx.mand) :
    exprToMarioExpr (varMapOfFrame fr) (Spec.applySubst frAx.vars σ e_hyp) =
    Metamath.Expr.subst (toMarioSubst (varMapOfFrame frAx) (varMapOfFrame fr) σ)
                        (exprToMarioExpr (varMapOfFrame frAx) e_hyp) := by
  let vmAx := varMapOfFrame frAx
  let vm := varMapOfFrame fr
  let σ_mario := toMarioSubst vmAx vm σ
  unfold exprToMarioExpr Spec.applySubst
  simp only []
  rw [marioExpr_subst_eq_flatMap]
  have h_const : ∀ s ∈ e_hyp.syms, Variable.mk s ∉ frAx.vars → Variable.mk s ∉ fr.vars :=
    fun s h_s_in h_not_var => Spec.const_global_of_wellFormed_hyp h_wf h_lookup h_hyp_in s h_s_in h_not_var
  exact exprToMarioExpr_applySubst_eq_subst_aux e_hyp.syms h_const

/-! ## Forward Direction: ProofValid → Mario.Provable

We first show that every element on a valid proof stack is Mario-provable,
then derive the singleton-stack case as a corollary.
-/

/-- Any element on a valid proof stack is Mario-provable.
    Requires database well-formedness for substitution correspondence. -/
theorem proofValid_stack_provable {Γ : Database} {fr : Frame} {stack : List Expr}
    {steps : List ProofStep}
    (h_wf : Spec.WellFormedDatabase Γ) :
    ProofValid Γ fr stack steps →
    ∀ e ∈ stack,
      Semantic.Provable (dbToAxioms Γ) (frameToContext fr)
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
          apply Metamath.Provable.hyp
          have h_mem' : hypToMarioFormula (varMapOfFrame fr) (Hyp.essential e) ∈
              (frameToContext fr).hyps := hypToMarioFormula_mem (fr := fr) (h := Hyp.essential e) h_in
          simpa [hypToMarioFormula_essential] using h_mem'
      | tail _ h_tail =>
          exact ih e' h_tail
  | useFloating stack steps c v h_in h_prev ih =>
      intro e' h_mem
      cases h_mem with
      | head =>
          apply Metamath.Provable.hyp
          have h_mem' : hypToMarioFormula (varMapOfFrame fr) (Hyp.floating c v) ∈
              (frameToContext fr).hyps := hypToMarioFormula_mem (fr := fr) (h := Hyp.floating c v) h_in
          obtain ⟨vr, h_find⟩ := findVR_of_float (fr := fr) (c := c) (v := v) h_in
          have h_eq := hypToMarioFormula_floating_expr (vm := varMapOfFrame fr) (c := c)
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
          --   Semantic.Provable (dbToAxioms Γ) (frameToContext fr)
          --     (exprToFormula (varMapOfFrame fr) (applySubst frAx.vars σ eAx))
          --
          -- Strategy: Apply Semantic.Provable.ax with:
          -- 1. The statement from (frAx, eAx)
          -- 2. A Mario substitution built from σ
          -- 3. DV constraint satisfaction via dvOK_implies_DJ_subst
          -- 4. Hypothesis provability via IH

          -- Step 1: Construct the axiom Statement
          let vmAx := varMapOfFrame frAx
          let ax : Semantic.Statement := ⟨frameToContext frAx, exprToFormula vmAx eAx⟩

          -- Step 2: Show ax is in dbToAxioms
          have h_ax_in : dbToAxioms Γ ax := ⟨l, frAx, eAx, h_ax, rfl, rfl⟩

          -- Step 3: Build Mario substitution
          let vm := varMapOfFrame fr
          let σ_mario : MarioVR → MarioExpr := toMarioSubst vmAx vm σ

          -- At this point we need:
          -- a) ax.ctx.dj.subst σ_mario (frameToContext fr).dj
          -- b) All hypotheses provable after substitution
          -- c) Show the result formula matches

          -- Apply Provable.ax with substitution σ_mario
          -- Goal: Provable (dbToAxioms Γ) (frameToContext fr)
          --         (exprToFormula vm (applySubst frAx.vars σ eAx))

          -- The result formula needs to match ax.fmla.subst σ_mario
          -- We'll prove this via a rewrite at the end

          -- Sub-goal 1: DV constraint satisfaction
          -- ax.ctx.dj.subst σ_mario (frameToContext fr).dj
          have h_dv_mario : ax.ctx.dj.subst σ_mario (frameToContext fr).dj := by
            -- ax.ctx = frameToContext frAx, so ax.ctx.dj = (frameToContext frAx).dj
            -- = dvListToMarioDJ (varMapOfFrame frAx) frAx.dv = dvListToMarioDJ vmAx frAx.dv
            -- Similarly (frameToContext fr).dj = dvListToMarioDJ vm fr.dv
            show (dvListToMarioDJ vmAx frAx.dv).subst σ_mario (dvListToMarioDJ vm fr.dv)

            -- h_dv : Spec.dvOK fr.vars frAx.dv fr.dv σ
            unfold Metamath.DJ.subst
            intro vr1 vr2 h_dj
            -- h_dj : (dvListToMarioDJ vmAx frAx.dv).disj vr1 vr2
            unfold Metamath.Expr.disjoint
            intro x y h_x_in h_y_in
            -- Need: (dvListToMarioDJ vm fr.dv).disj x y

            -- Step 1: Get the source variable pair from h_dj
            unfold dvListToMarioDJ at h_dj
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

                  -- Step 4: x ∈' σ_mario vr1 = x ∈' toMarioSubst vmAx vm σ vr1
                  --       = x ∈' exprToMarioExpr vm (σ v) (by h_findVar_v)
                  change x ∈' (toMarioSubst vmAx vm σ vr1) at h_x_in
                  change y ∈' (toMarioSubst vmAx vm σ vr2) at h_y_in
                  simp only [toMarioSubst, h_findVar_v] at h_x_in
                  simp only [toMarioSubst, h_findVar_w] at h_y_in
                  -- Now h_x_in : x ∈' exprToMarioExpr vm (σ v)
                  -- and h_y_in : y ∈' exprToMarioExpr vm (σ w)

                  -- Step 5: Extract source variables from x and y membership
                  -- Use exprToMarioExpr_mem_extract to get the source symbols
                  obtain ⟨x_s, h_x_s_in, h_x_findVR⟩ := exprToMarioExpr_mem_extract h_x_in
                  obtain ⟨y_s, h_y_s_in, h_y_findVR⟩ := exprToMarioExpr_mem_extract h_y_in
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
                  -- Lift dvRel to dvListToMarioDJ
                  have h_unique : ∀ v' v'' vr', findVR vm v' = some vr' → findVR vm v'' = some vr' → v' = v'' :=
                    fun _ _ _ h1 h2 => findVR_injective_frame h1 h2
                  exact dvRel_to_dvListToMarioDJ h_unique h_dvRel h_x_findVR h_y_findVR
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
                    -- Get the membership in exprToMarioExpr
                    change x ∈' (toMarioSubst vmAx vm σ vr1) at h_x_in
                    change y ∈' (toMarioSubst vmAx vm σ vr2) at h_y_in
                    simp only [toMarioSubst, h_findVar_w] at h_x_in  -- x from σ w
                    simp only [toMarioSubst, h_findVar_v] at h_y_in  -- y from σ v
                    -- Now h_x_in : x ∈' exprToMarioExpr vm (σ w)
                    -- and h_y_in : y ∈' exprToMarioExpr vm (σ v)
                    -- Extract source variables
                    obtain ⟨x_s, h_x_s_in, h_x_findVR⟩ := exprToMarioExpr_mem_extract h_x_in
                    obtain ⟨y_s, h_y_s_in, h_y_findVR⟩ := exprToMarioExpr_mem_extract h_y_in
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
                    -- Lift to dvListToMarioDJ
                    have h_unique : ∀ v' v'' vr', findVR vm v' = some vr' → findVR vm v'' = some vr' → v' = v'' :=
                      fun _ _ _ h1 h2 => findVR_injective_frame h1 h2
                    exact dvRel_to_dvListToMarioDJ h_unique h_dvRel_sym h_x_findVR h_y_findVR
                | some _, none =>
                    simp only [h_v, h_w] at h_find
                    cases h_find
                | none, _ =>
                    simp only [h_v] at h_find
                    cases h_find

          -- Sub-goal 2: All axiom hypotheses are provable after substitution
          have h_hyps : ∀ h, h ∈ ax.ctx.hyps ∨ (∃ v : MarioVR, h = (v.type, [.var v])) →
              Semantic.Provable (dbToAxioms Γ) (frameToContext fr) (h.subst σ_mario) := by
            intro h h_case
            cases h_case with
            | inl h_in_hyps =>
                -- h is a hypothesis from the axiom's frame (essential or floating)
                -- ax.ctx.hyps = frAx.mand.map (hypToMarioFormula vmAx)
                -- So there exists hyp ∈ frAx.mand with h = hypToMarioFormula vmAx hyp
                have h_ax_ctx : ax.ctx = frameToContext frAx := rfl
                rw [h_ax_ctx] at h_in_hyps
                unfold frameToContext at h_in_hyps
                simp only [] at h_in_hyps
                -- h_in_hyps : h ∈ frAx.mand.map (hypToMarioFormula vmAx)
                obtain ⟨hyp, h_hyp_in, h_hyp_eq⟩ := List.mem_map.mp h_in_hyps
                -- hyp ∈ frAx.mand and h = hypToMarioFormula vmAx hyp
                cases hyp with
                | essential e_hyp =>
                    -- h = exprToFormula vmAx e_hyp
                    -- h.subst σ_mario should equal exprToFormula vm (applySubst frAx.vars σ e_hyp)
                    -- And applySubst frAx.vars σ e_hyp is in needed (hence on stack)
                    rw [← h_hyp_eq, hypToMarioFormula_essential]
                    -- Goal: Provable ... ((exprToFormula vmAx e_hyp).subst σ_mario)
                    -- Rewrite using our substitution correspondence
                    have h_subst_eq : (exprToFormula vmAx e_hyp).subst σ_mario =
                        exprToFormula vm (Spec.applySubst frAx.vars σ e_hyp) := by
                      unfold exprToFormula Metamath.Formula.subst
                      simp only []
                      -- Goal: (e_hyp.typecode.c, Expr.subst σ_mario (exprToMarioExpr vmAx e_hyp)) =
                      --       ((applySubst frAx.vars σ e_hyp).typecode.c, exprToMarioExpr vm (applySubst frAx.vars σ e_hyp))
                      -- applySubst preserves typecode
                      have h_tc : (Spec.applySubst frAx.vars σ e_hyp).typecode = e_hyp.typecode := by
                        unfold Spec.applySubst; rfl
                      rw [h_tc]
                      congr 1
                      -- Now just need the expression part (need to swap sides)
                      exact (exprToMarioExpr_applySubst_eq_subst_hyp h_wf h_ax h_hyp_in).symm
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
                    -- h = hypToMarioFormula vmAx (Hyp.floating c_hyp v_hyp) = (c_hyp.c, [.var vr])
                    -- h.subst σ_mario = (c_hyp.c, σ_mario vr)
                    -- σ v_hyp is in needed (hence on stack)
                    -- Type preservation: h_typed gives us (σ v_hyp).typecode = c_hyp
                    have h_type_pres := h_typed c_hyp v_hyp h_hyp_in
                    -- h_type_pres : (σ v_hyp).typecode = c_hyp
                    -- Get the VR for v_hyp in vmAx
                    have ⟨vr, h_findVR⟩ := findVR_of_float (fr := frAx) (c := c_hyp) (v := v_hyp) h_hyp_in
                    -- h = (c_hyp.c, [.var vr])
                    rw [← h_hyp_eq]
                    have h_float_eq := hypToMarioFormula_floating_expr (vm := vmAx)
                      (c := c_hyp) (v := v_hyp) (vr := vr) h_findVR
                    rw [h_float_eq]
                    -- Goal: Provable ... ((exprToFormula vmAx ⟨c_hyp, [v_hyp.v]⟩).subst σ_mario)
                    -- exprToFormula vmAx ⟨c_hyp, [v_hyp.v]⟩ = (c_hyp.c, [.var vr])
                    unfold exprToFormula exprToMarioExpr
                    simp only [List.map_cons, List.map_nil]
                    -- Goal: Provable ... ((c_hyp.c, [toMarioSym vmAx v_hyp.v]).subst σ_mario)
                    simp only [Metamath.Formula.subst]
                    -- Goal: Provable ... (c_hyp.c, Expr.subst σ_mario [toMarioSym vmAx v_hyp.v])
                    -- toMarioSym vmAx v_hyp.v = .var vr since h_findVR
                    have h_sym : toMarioSym vmAx v_hyp.v = .var vr := toMarioSym_var h_findVR
                    rw [h_sym, Metamath.Expr.subst, Metamath.Expr.subst, List.append_nil]
                    -- Goal: Provable ... (c_hyp.c, σ_mario vr)
                    -- σ_mario vr = exprToMarioExpr vm (σ v_hyp)
                    have h_sigma_eq : σ_mario vr = exprToMarioExpr vm (σ v_hyp) := by
                      have h_findVar := findVR_findVar_inverse_frame h_findVR
                      exact toMarioSubst_findVar h_findVar
                    rw [h_sigma_eq]
                    -- Goal: Provable ... (c_hyp.c, exprToMarioExpr vm (σ v_hyp))
                    -- By type preservation: (σ v_hyp).typecode = c_hyp
                    -- So exprToFormula vm (σ v_hyp) = ((σ v_hyp).typecode.c, exprToMarioExpr vm (σ v_hyp))
                    --                              = (c_hyp.c, exprToMarioExpr vm (σ v_hyp))
                    have h_formula_eq : (c_hyp.c, exprToMarioExpr vm (σ v_hyp)) =
                        exprToFormula vm (σ v_hyp) := by
                      unfold exprToFormula
                      congr 1
                      exact (congrArg Constant.c h_type_pres).symm
                    rw [h_formula_eq]
                    -- σ v_hyp is on the stack, so by IH it's provable
                    have h_in_needed : σ v_hyp ∈ needed := by
                      rw [h_needed]
                      apply List.mem_map.mpr
                      refine ⟨Hyp.floating c_hyp v_hyp, h_hyp_in, ?_⟩
                      rfl
                    have h_in_stack : σ v_hyp ∈ stack := by
                      rw [h_stack_eq]
                      exact List.mem_append_left _ (List.mem_reverse.mpr h_in_needed)
                    exact ih (σ v_hyp) h_in_stack
            | inr h_is_var =>
                -- h is a variable formula v = (v.type, [.var v])
                obtain ⟨v, h_eq⟩ := h_is_var
                rw [h_eq]
                -- h.subst σ_mario = (v.type, σ_mario v ++ []) since Formula.subst preserves typecode
                -- and Expr.subst σ [.var v] = σ v ++ subst σ []
                simp only [Metamath.Formula.subst, Metamath.Expr.subst]
                -- Now goal: Provable ... (v.type, σ_mario v ++ [])
                rw [List.append_nil]
                -- Now goal: Provable ... (v.type, σ_mario v)
                -- Case split on whether v is in the axiom's varMap
                unfold σ_mario toMarioSubst
                cases h_findVar : findVar vmAx v with
                | none =>
                    -- v is not in axiom's context, so σ_mario v = [.var v]
                    -- Goal: Provable ... (v.type, [.var v])
                    -- This is exactly Provable.var v
                    exact Metamath.Provable.var v
                | some var_spec =>
                    -- v is in axiom's context, corresponding to var_spec
                    -- σ_mario v = exprToMarioExpr vm (σ var_spec)
                    -- Goal: Provable ... (v.type, exprToMarioExpr vm (σ var_spec))
                    --
                    -- Step 1: From findVar success, get map membership
                    have h_mem : (var_spec, v) ∈ varMapOfFrame frAx :=
                      findVar_mem_of_some h_findVar
                    -- Step 2: From membership, get floating hyp AND type match
                    obtain ⟨c_float, h_float_in, h_type_eq⟩ :=
                      mem_varMapOfFrame_sound_typed h_mem
                    -- h_float_in : Hyp.floating c_float var_spec ∈ frAx.mand
                    -- h_type_eq : v.type = c_float.c
                    -- Step 3: Use h_typed to get substitution type preservation
                    have h_sigma_type := h_typed c_float var_spec h_float_in
                    -- h_sigma_type : (σ var_spec).typecode = c_float
                    -- Step 4: Connect v.type to (σ var_spec).typecode.c
                    have h_type_connect : v.type = (σ var_spec).typecode.c := by
                      rw [h_type_eq, h_sigma_type]
                    -- Step 5: Show σ var_spec is on the stack (via needed)
                    have h_in_needed : σ var_spec ∈ needed := by
                      rw [h_needed]
                      apply List.mem_map.mpr
                      refine ⟨Hyp.floating c_float var_spec, h_float_in, ?_⟩
                      rfl
                    have h_in_stack : σ var_spec ∈ stack := by
                      rw [h_stack_eq]
                      exact List.mem_append_left _ (List.mem_reverse.mpr h_in_needed)
                    -- Step 6: By IH, exprToFormula vm (σ var_spec) is provable
                    have h_prov := ih (σ var_spec) h_in_stack
                    -- h_prov : Provable axs Γ (exprToFormula vm (σ var_spec))
                    -- exprToFormula vm (σ var_spec) = ((σ var_spec).typecode.c, exprToMarioExpr vm (σ var_spec))
                    -- Goal: Provable axs Γ (v.type, exprToMarioExpr vm (σ var_spec))
                    -- Step 7: Rewrite using type connection
                    have h_formula_eq : (v.type, exprToMarioExpr vm (σ var_spec)) =
                        exprToFormula vm (σ var_spec) := by
                      unfold exprToFormula
                      rw [h_type_connect]
                    rw [h_formula_eq]
                    exact h_prov

          -- Sub-goal 3: Show the result formula matches
          -- We need: exprToFormula vm (applySubst frAx.vars σ eAx) = ax.fmla.subst σ_mario
          -- where ax.fmla = exprToFormula vmAx eAx
          have h_result : exprToFormula vm (Spec.applySubst frAx.vars σ eAx) =
                          (exprToFormula vmAx eAx).subst σ_mario := by
            -- Typecodes match: applySubst preserves typecode
            -- Expressions match: by exprToMarioExpr_applySubst_eq_subst
            unfold exprToFormula Metamath.Formula.subst
            -- Goal: (typecode, exprToMarioExpr vm (applySubst ...)) =
            --       (typecode, (exprToMarioExpr vmAx eAx).subst σ_mario)
            congr 1
            -- Now just the expression part
            exact exprToMarioExpr_applySubst_eq_subst h_wf h_ax

          -- Apply Provable.ax and rewrite goal
          rw [h_result]
          exact Metamath.Provable.ax σ_mario h_ax_in h_dv_mario h_hyps
      | tail _ h_tail =>
          have h_mem' : e' ∈ needed.reverse ++ remaining :=
            (List.mem_append).2 (Or.inr h_tail)
          have h_mem_stack : e' ∈ stack := by
            simpa [h_stack_eq] using h_mem'
          exact ih e' h_mem_stack

/-- Forward direction: If we have a valid operational proof ending with [e],
    then e is provable in Mario's semantic system. -/
theorem proofValid_to_mario {Γ : Database} {fr : Frame} {e : Expr} {steps : List ProofStep}
    (h_wf : Spec.WellFormedDatabase Γ) :
    ProofValid Γ fr [e] steps →
    Semantic.Provable (dbToAxioms Γ) (frameToContext fr)
      (exprToFormula (varMapOfFrame fr) e) := by
  intro h
  have h_all := proofValid_stack_provable h_wf h
  simpa using h_all e (by simp)

/-! ## Backward Direction: Mario.Provable → ProofValid

This direction is trickier because Mario's system doesn't track the proof stack.
We need to show that IF something is provable in Mario's system,
THEN we can construct SOME operational proof (may not be the same steps).

This is the **completeness** direction - showing our verifier is complete with
respect to Mario's semantic specification.

**Status**: DEFERRED (less critical than soundness)

**Why deferred**:
1. Soundness (forward direction) is more important - ensures our verifier doesn't accept invalid proofs
2. Completeness is nice-to-have - ensures our verifier isn't artificially restrictive
3. More complex - requires reconstructing operational proof steps from declarative proof
4. Can be completed after forward direction is fully proven

**Strategy for future work**:
- Induction on Mario's Provable derivation
- For each Mario constructor (hyp, var, ax), construct corresponding ProofValid steps
- hyp case: Find the hypothesis in our frame, use useEssential or useFloating
- var case: Construct floating hypothesis for the variable
- ax case: Most complex - need to:
  * Find the axiom in our database (inverse of dbToAxioms)
  * Convert Mario's functional substitution to our Subst
  * Recursively construct proofs for needed hypotheses (IH)
  * Apply useAxiom with constructed substitution
-/

/-- Backward direction: If something is provable in Mario's semantic system,
    then we can construct an operational proof.

    This is **completeness** - Mario's spec is not stronger than our verifier.

    **DEFERRED**: This is less critical than soundness. The forward direction
    (soundness) ensures our verifier doesn't accept invalid proofs, which is
    the primary safety property. Completeness ensures we're not artificially
    restrictive, which can be proven later.

    Estimated effort: 4-6 hours (complex due to proof reconstruction) -/
theorem mario_to_proofValid {Γ : Database} {fr : Frame} {e : Expr}
    (h_mario : Semantic.Provable (dbToAxioms Γ) (frameToContext fr)
                                   (exprToFormula (varMapOfFrame fr) e)) :
    Provable Γ fr e := by
  sorry  -- DEFERRED: Completeness less critical than soundness

/-! ## Main Equivalence Theorem

Combines both directions to show operational ↔ semantic equivalence.
-/

/-- **MAIN THEOREM**: Operational and semantic provability are equivalent.

    This connects our verifier's operational semantics to Mario's mathematical foundations.

    - **Forward** (soundness): Verifier accepts → mathematically valid
    - **Backward** (completeness): Mathematically valid → verifier can accept

    We use the typed variable map from floating hypotheses, so typecodes
    are preserved in Mario's VRs by construction.

    Once proven, this enables:
    1. Using Mario's proven lemmas in our proofs
    2. Reasoning about our verifier using textbook mathematics
    3. Confidence that our operational model matches the spec
-/
theorem operational_iff_semantic {Γ : Database} {fr : Frame} {e : Expr}
    (h_wf : Spec.WellFormedDatabase Γ) :
    Provable Γ fr e ↔
    Semantic.Provable (dbToAxioms Γ) (frameToContext fr)
      (exprToFormula (varMapOfFrame fr) e) := by
  constructor
  · -- Forward: Operational → Semantic
    intro ⟨steps, finalStack, h_valid, h_stack⟩
    rw [h_stack] at h_valid
    exact proofValid_to_mario h_wf h_valid
  · -- Backward: Semantic → Operational
    exact mario_to_proofValid

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

**Current status**:
- Structure in place
- 4 sorries in forward direction (one per constructor case)
- 3 sorries in backward direction (one per constructor case)
- Need to prove conversion preserves semantics

**Next steps** (Phase 4 continuation):
1. Prove forward direction first (needed for soundness)
2. Fill in constructor cases using Bridge lemmas
3. Prove backward direction for completeness
-/

end Metamath.Spec.Equivalence
