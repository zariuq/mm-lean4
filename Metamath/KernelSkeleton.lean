/-
SKELETON: Minimal axiomatic kernel for Metamath soundness.

This file contains:
1. Working definitions (toExpr, toSym, etc.)
2. Key proven lemmas (vars_apply_subset, dv_weakening, etc.)
3. AXIOMS for everything broken (marked with TODO)

The goal: get this to compile, then work bottom-up proving each axiom.
-/

import Metamath.Spec
import Metamath.Verify
import Metamath.KernelExtras

namespace Metamath.Kernel

open Metamath.Spec
open Metamath.Verify

/-! ## Working Conversions -/

/-- Convert implementation Sym to spec Sym -/
def toSym (s : Metamath.Verify.Sym) : Metamath.Spec.Sym := s.value

/-- Convert implementation Formula to spec Expr -/
def toExpr (f : Metamath.Verify.Formula) : Metamath.Spec.Expr :=
  if h : f.size > 0 then
    { typecode := ⟨f[0].value⟩
      syms := f.toList.tail.map toSym }
  else
    { typecode := ⟨"ERROR"⟩, syms := [] }

/-! ## Working Spec Lemmas -/

/-- Empty frame satisfies dvOK for any substitution -/
theorem no_dv_always_ok (vars : List Metamath.Spec.Variable) (σ : Metamath.Spec.Subst) :
  Metamath.Spec.dvOK vars [] σ := by
  unfold Metamath.Spec.dvOK
  intro v w hvw
  simp at hvw

/-- Substitution preserves typecode -/
theorem subst_preserves_typecode (vars : List Metamath.Spec.Variable) (σ : Metamath.Spec.Subst) (e : Metamath.Spec.Expr) :
  (Metamath.Spec.applySubst vars σ e).typecode = e.typecode := by
  rfl

/-- Helper: mem_flatMap inversion -/
lemma mem_flatMap_iff {α β : Type _} (xs : List α) (f : α → List β) (b : β) :
  b ∈ xs.flatMap f ↔ ∃ a ∈ xs, b ∈ f a := by
  simp [List.mem_flatMap]

/-- Variables in σ(e) are subset of original vars union vars introduced by σ (PROVEN ✓) -/
theorem vars_apply_subset (vars : List Metamath.Spec.Variable) (σ : Metamath.Spec.Subst) (e : Metamath.Spec.Expr) :
  ∀ v ∈ Metamath.Spec.varsInExpr vars (Metamath.Spec.applySubst vars σ e),
    v ∈ Metamath.Spec.varsInExpr vars e ∨
    ∃ w ∈ Metamath.Spec.varsInExpr vars e, v ∈ Metamath.Spec.varsInExpr vars (σ w) := by
  intro v hv
  unfold Metamath.Spec.varsInExpr at hv
  unfold Metamath.Spec.applySubst at hv
  rcases (by simpa [List.filterMap] using hv) with ⟨s, hs_flat, hv_ok⟩
  have h_vs : Metamath.Spec.Variable.mk s ∈ vars ∧ v = Metamath.Spec.Variable.mk s := by
    by_cases hmem : Metamath.Spec.Variable.mk s ∈ vars
    · simp [hmem] at hv_ok
      exact ⟨hmem, by cases hv_ok; rfl⟩
    · simp [hmem] at hv_ok
  rcases h_vs with ⟨h_var_s, rfl⟩
  have : ∃ s' ∈ e.syms,
           s ∈ (let v := Metamath.Spec.Variable.mk s'
                if v ∈ vars then (σ v).syms else [s']) := by
    simpa [List.mem_flatMap] using hs_flat
  rcases this with ⟨s', hs'_mem, hs_in⟩
  by_cases h_var_s' : Metamath.Spec.Variable.mk s' ∈ vars
  · right
    refine ⟨Metamath.Spec.Variable.mk s', ?_, ?_⟩
    · unfold Metamath.Spec.varsInExpr
      simp [List.filterMap, hs'_mem, h_var_s']
    · unfold Metamath.Spec.varsInExpr
      have : s ∈ (σ (Metamath.Spec.Variable.mk s')).syms := by
        simpa [h_var_s'] using hs_in
      simp [List.filterMap, this, h_var_s]
  · have : s = s' := by simpa [h_var_s'] using hs_in
    have : Metamath.Spec.Variable.mk s' ∈ vars := by simpa [this] using h_var_s
    exact absurd this h_var_s'

/-- DV weakening -/
theorem dv_weakening (vars : List Metamath.Spec.Variable) (dv₁ dv₂ : List (Variable × Variable)) (σ : Metamath.Spec.Subst) :
  dv₁ ⊆ dv₂ →
  Metamath.Spec.dvOK vars dv₂ σ →
  Metamath.Spec.dvOK vars dv₁ σ := by
  intro hsub hok
  unfold Metamath.Spec.dvOK at *
  intro v w hvw
  exact hok v w (hsub hvw)

/-- DV append -/
theorem dv_append (vars : List Metamath.Spec.Variable) (dv₁ dv₂ : List (Variable × Variable)) (σ : Metamath.Spec.Subst) :
  Metamath.Spec.dvOK vars dv₁ σ →
  Metamath.Spec.dvOK vars dv₂ σ →
  Metamath.Spec.dvOK vars (dv₁ ++ dv₂) σ := by
  intro h1 h2
  unfold Metamath.Spec.dvOK at *
  intro v w hvw
  simp [List.mem_append] at hvw
  match hvw with
  | Or.inl hl => exact h1 v w hl
  | Or.inr hr => exact h2 v w hr

/-! ## AXIOMS: Core Bridge Functions (TODO: Prove) -/

/-- TODO: Prove toDatabase conversion is correct -/
axiom toDatabase (db : Metamath.Verify.DB) : Option Metamath.Spec.Database

/-- TODO: Prove toFrame conversion is correct -/
axiom toFrame (db : Metamath.Verify.DB) (fr : Metamath.Verify.Frame) : Option Metamath.Spec.Frame

/-! ## AXIOMS: Matching/Substitution (TODO: Define and prove) -/

/-- TODO: Define and prove matchSyms/matchExpr/matchHyps correspondence -/
axiom matching_sound : True  -- Placeholder for all matching lemmas

/-! ## AXIOMS: checkHyp Soundness (TODO: Prove - Phase 4 statements are type-correct) -/

/-- TODO: Prove checkHyp for floats matches spec -/
axiom checkHyp_floats_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula) :
  True  -- TODO: Simplified - actual checkHyp has complex signature

/-- TODO: Prove checkHyp for essentials matches spec -/
axiom checkHyp_essentials_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula) :
  True  -- TODO: Simplified - actual checkHyp has complex signature

/-! ## AXIOM: stepNormal_sound (CRITICAL - TODO: Prove) -/

/-- TODO: THE BIG ONE - prove one proof step is sound -/
axiom stepNormal_sound (db : Metamath.Verify.DB) (pr : ProofState) (label : String) :
  True  -- TODO: Simplified - actual proof needs full correspondence

/-! ## AXIOM: DV checking (TODO: Prove) -/

axiom dvCheck_sound (db : Metamath.Verify.DB) :
  True  -- TODO: Simplified

/-! ## AXIOM: fold_maintains_inv_and_provable (TODO: Prove) -/

axiom fold_maintains_inv_and_provable (db : Metamath.Verify.DB) :
  True  -- TODO: Simplified

/-! ## Main Soundness Theorem (TODO: Complete proof) -/

theorem verify_impl_sound
    (db : Metamath.Verify.DB)
    (label : String)
    (f : Metamath.Verify.Formula)
    (proof : Array String)
    (WFdb : True) :
  (∃ pr_final : Metamath.Verify.ProofState,
    proof.foldlM (fun pr step => DB.stepNormal db pr step)
      ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], Verify.ProofTokenParser.normal⟩ = Except.ok pr_final ∧
    pr_final.stack.size = 1 ∧
    pr_final.stack[0]? = some f) →
  ∃ (Γ : Metamath.Spec.Database) (fr : Metamath.Spec.Frame),
    toDatabase db = some Γ ∧
    toFrame db db.frame = some fr ∧
    Metamath.Spec.Provable Γ fr (toExpr f) := by
  sorry  -- TODO: Complete using fold lemma

end Metamath.Kernel
