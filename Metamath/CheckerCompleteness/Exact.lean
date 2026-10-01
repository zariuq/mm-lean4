import Metamath.KernelCorrectness
import Metamath.PrefixProvability.Checker

/-!
# The checker accepts exactly

The completeness of the proof checker (`verify_impl_complete`) gives a proof whose final stack
converts to the target expression. For acceptance by `finishProof`, which compares formulas
literally, the final stack must be exactly the claimed formula. It is, because formulas respecting
the active frame are determined by their conversion (`verify_impl_complete_exact`). A normal-mode
run changes only the stack of the proof state, so it transfers to the parser's start state, and
`finishProof` then inserts exactly the claimed assertion (`normal_proof_finishes_exact`).
-/

set_option autoImplicit false

namespace Metamath.CheckerCompleteness

open Metamath.Spec
open Metamath.Spec.Equivalence
open Metamath.Verify
open Metamath.Kernel
open Metamath.WF

/-! ## Exact completeness: the stack ends in `#[f]` -/

/-- Completeness of the normal-mode checker, exactly: a provable claim `f` with a constant head,
respecting the active frame, has a proof whose final stack is `#[f]`. -/
theorem verify_impl_complete_exact (db : Verify.DB) (label : String) (f : Verify.Formula)
    (h_wf : WellFormedDB db) (h_sf : CompletenessScopedFacts db)
    (Γ : Spec.Database) (fr : Spec.Frame)
    (h_db : toDatabase db = some Γ) (h_frame : toFrame db db.frame = some fr)
    (h_dv_wf : ∀ l fr' e, Γ l = some (fr', e) → DVWellFormed fr')
    (h_head : f.hasConstHead = true)
    (h_resp : db.formulaSymsRespectFrame f db.frame = true)
    (h_prov : Spec.Provable Γ fr (toExpr f)) :
    ∃ (proof : Array String) (pr_final : Verify.ProofState),
      proof.foldlM (fun pr step => Verify.DB.stepNormal db pr step)
        ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], Verify.ProofTokenParser.normal, false⟩ =
          Except.ok pr_final ∧
      pr_final.stack = #[f] := by
  obtain ⟨steps, finalStack, h_valid, h_stack⟩ := h_prov
  rw [h_stack] at h_valid
  obtain ⟨pr_final, h_fold, h_view, _h_frame_final, h_head_final, h_respects_final⟩ :=
    foldlM_proofSteps_complete db Γ fr h_db h_frame h_wf h_sf h_dv_wf
      [toExpr f] steps h_valid
      ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], Verify.ProofTokenParser.normal, false⟩
      [] (by simp [viewStack]) rfl stackHasConstHead_empty
      (stackRespectsFrame_empty db db.frame)
  have h_view' : pr_final.stack.toList.map toExpr = [toExpr f] := by
    simpa [viewStack] using h_view
  obtain ⟨f', h_list, h_toExpr⟩ := List.map_eq_singleton_iff.mp h_view'
  have h_arr : pr_final.stack = #[f'] := by
    apply Array.toList_inj.mp
    simpa using h_list
  have h_size : 0 < pr_final.stack.size := by simp [h_arr]
  have h_get : pr_final.stack[0]! = f' := by simp [h_arr]
  have h_head' : f'.hasConstHead = true := by
    have := h_head_final 0 h_size
    rwa [h_get] at this
  have h_resp' : db.formulaSymsRespectFrame f' db.frame = true := by
    have := h_respects_final 0 h_size
    rwa [h_get] at this
  have h_eq : f' = f :=
    formula_eq_of_toExpr_eq_of_respects db db.frame f' f h_head' h_head h_resp' h_resp h_toExpr
  refine ⟨(proofStepsToLabels db db.frame steps.reverse).toArray, pr_final, ?_, ?_⟩
  · rw [← Array.foldlM_toList]
    simpa using h_fold
  · rw [h_arr, h_eq]

/-! ## `stepNormal` changes only the stack -/

/-- A successful `stepAssert` changes only the stack (`shrink` then `push`). -/
theorem stepAssert_ok_shape (db : Verify.DB) (pr r : Verify.ProofState)
    (f : Verify.Formula) (fr : Verify.Frame)
    (h : db.stepAssert pr f fr = .ok r) : r = { pr with stack := r.stack } := by
  obtain ⟨dj, hyps⟩ := fr
  simp only [Verify.DB.stepAssert] at h
  split at h
  · rename_i h_le
    split at h
    · exact absurd h nofun
    · split at h
      · exact absurd h nofun
      · simp only [bind, Except.bind] at h
        cases h_chk : db.checkHyp hyps pr.stack
            ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h_le⟩ 0 ∅ with
        | error e => simp [h_chk] at h
        | ok σ =>
          simp only [h_chk] at h
          cases h_dv : Verify.DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj dj σ with
          | error e => simp [h_dv] at h
          | ok u =>
            simp only [h_dv] at h
            split at h
            · simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              rfl
            · exact absurd h nofun
  · exact absurd h nofun

/-- A successful `stepNormal` changes only the stack: position, label, claimed
formula, frame, heap, token-parser mode and the incompleteness flag are all
untouched. -/
theorem stepNormal_ok_shape (db : Verify.DB) (pr r : Verify.ProofState) (l : String)
    (h : db.stepNormal pr l = .ok r) : r = { pr with stack := r.stack } := by
  unfold Verify.DB.stepNormal at h
  cases h_find : db.find? l with
  | none => simp [h_find] at h
  | some obj =>
    simp only [h_find] at h
    cases obj with
    | const _ => simp at h
    | var _ => simp at h
    | hyp ess f _ =>
      by_cases h_mem : l ∈ db.frame.hyps.toList
      · simp only [h_mem, ↓reduceIte] at h
        cases ess with
        | true =>
          simp only [↓reduceIte] at h
          split at h
          · exact absurd h nofun
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false] at h
          split at h
          · exact absurd h nofun
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            rfl
      · simp [h_mem] at h
    | assert f' fr' _ => exact stepAssert_ok_shape db pr r f' fr' h

/-- Fold lift: a successful `foldlM stepNormal` run changes only the stack. -/
theorem foldlM_stepNormal_ok_shape (db : Verify.DB) (proof : Array String)
    (pr₀ pr : Verify.ProofState)
    (h : proof.foldlM (fun pr l => db.stepNormal pr l) pr₀ = .ok pr) :
    pr = { pr₀ with stack := pr.stack } := by
  have h_ex : ∃ st, pr = { pr₀ with stack := st } :=
    KernelExtras.array_foldlM_preserves
      (fun r : Verify.ProofState => ∃ st, r = { pr₀ with stack := st })
      (fun pr l => db.stepNormal pr l) proof pr₀ pr ⟨pr₀.stack, rfl⟩
      (fun b a b' h_step h_b => by
        obtain ⟨st, rfl⟩ := h_b
        have h1 := stepNormal_ok_shape db _ b' a h_step
        exact ⟨b'.stack, h1⟩)
      h
  obtain ⟨st, h_eq⟩ := h_ex
  subst h_eq
  rfl

/-- Field-wise form of `foldlM_stepNormal_ok_shape`. -/
theorem foldlM_stepNormal_preserves_fields (db : Verify.DB) (proof : Array String)
    (pr₀ pr : Verify.ProofState)
    (h : proof.foldlM (fun pr l => db.stepNormal pr l) pr₀ = .ok pr) :
    pr.pos = pr₀.pos ∧ pr.label = pr₀.label ∧ pr.fmla = pr₀.fmla ∧
      pr.frame = pr₀.frame ∧ pr.heap = pr₀.heap ∧ pr.ptp = pr₀.ptp ∧
      pr.incomplete = pr₀.incomplete := by
  have h_shape := foldlM_stepNormal_ok_shape db proof pr₀ pr h
  generalize pr.stack = S at h_shape
  subst h_shape
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Transfer, exact form: a successful fold from the canonical start state
`⟨⟨0,0⟩, label, f, db.frame, #[], #[], .normal, false⟩` yields a successful fold
from the parser's start state `{ db.mkProofState pos label f frImpl with ptp := .normal }`,
whose result is that start state with the same final stack. -/
theorem foldlM_stepNormal_from_mkProofState (db : Verify.DB) (proof : Array String)
    (label : String) (f : Verify.Formula) (pos : Verify.Pos) (frImpl : Verify.Frame)
    (r₁ : Verify.ProofState)
    (h_fold : proof.foldlM (fun pr step => db.stepNormal pr step)
        ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], .normal, false⟩ = .ok r₁) :
    proof.foldlM (fun pr step => db.stepNormal pr step)
        { db.mkProofState pos label f frImpl with ptp := .normal } =
      .ok { db.mkProofState pos label f frImpl with ptp := .normal, stack := r₁.stack } := by
  obtain ⟨r₂, h_fold₂, h_stack₂⟩ :=
    Metamath.PrefixProvenance.foldlM_stepNormal_transfer_array db proof
      ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], .normal, false⟩
      { db.mkProofState pos label f frImpl with ptp := .normal } r₁ rfl h_fold
  have h_shape := foldlM_stepNormal_ok_shape db proof _ r₂ h_fold₂
  rw [h_fold₂, h_shape, h_stack₂]

/-- Transfer, both directions: the two start states reach exactly the same
final stacks (they agree on the initial stack `#[]`). -/
theorem foldlM_stepNormal_transfer_iff (db : Verify.DB) (proof : Array String)
    (label : String) (f : Verify.Formula) (pos : Verify.Pos) (frImpl : Verify.Frame)
    (S : Array Verify.Formula) :
    (∃ r, proof.foldlM (fun pr step => db.stepNormal pr step)
        ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], .normal, false⟩ = .ok r ∧ r.stack = S) ↔
    (∃ r, proof.foldlM (fun pr step => db.stepNormal pr step)
        { db.mkProofState pos label f frImpl with ptp := .normal } = .ok r ∧ r.stack = S) := by
  constructor
  · rintro ⟨r₁, h_fold, rfl⟩
    obtain ⟨r₂, h_fold₂, h_stack₂⟩ :=
      Metamath.PrefixProvenance.foldlM_stepNormal_transfer_array db proof
        ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], .normal, false⟩
        { db.mkProofState pos label f frImpl with ptp := .normal } r₁ rfl h_fold
    exact ⟨r₂, h_fold₂, h_stack₂⟩
  · rintro ⟨r₂, h_fold, rfl⟩
    obtain ⟨r₁, h_fold₁, h_stack₁⟩ :=
      Metamath.PrefixProvenance.foldlM_stepNormal_transfer_array db proof
        { db.mkProofState pos label f frImpl with ptp := .normal }
        ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], .normal, false⟩ r₂ rfl h_fold
    exact ⟨r₁, h_fold₁, h_stack₁⟩

/-! ## `finishProof` on an exact normal-mode final state -/

/-- On a normal-mode proof state whose stack is exactly `#[fmla]`, with no `?`
step, a fresh label and an error-free database, `finishProof` is exactly the
assertion insert (and resets the token parser). -/
theorem finishProof_of_exact_state (s : Verify.ParserState) (pr : Verify.ProofState)
    (h_ptp : pr.ptp = .normal) (h_stack : pr.stack = #[pr.fmla])
    (h_inc : pr.incomplete = false)
    (h_fresh : s.db.find? pr.label = none) (h_err : s.db.error? = none) :
    s.finishProof pr =
      { s with tokp := .start,
               db := s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame) } := by
  obtain ⟨pos, l, fmla, fr, heap, stack, ptp, inc⟩ := pr
  simp only at h_ptp h_stack h_inc h_fresh ⊢
  subst h_ptp h_stack h_inc
  have h_ins_err : (s.db.insert pos l (.assert fmla fr)).error? = none := by
    unfold Verify.DB.insert
    simp [h_err, h_fresh, Verify.DB.error]
  unfold Verify.ParserState.finishProof Verify.ParserState.withAt
  simp [Id.run, Verify.ParserState.withDB, Verify.DB.recordIncomplete, h_ins_err]

theorem finishProof_of_exact (s : Verify.ParserState) (pr : Verify.ProofState)
    (h_ptp : pr.ptp = .normal) (h_stack : pr.stack = #[pr.fmla])
    (h_inc : pr.incomplete = false)
    (h_fresh : s.db.find? pr.label = none) (h_err : s.db.error? = none) :
    (s.finishProof pr).db = s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame) ∧
    (s.finishProof pr).db.error? = none := by
  rw [finishProof_of_exact_state s pr h_ptp h_stack h_inc h_fresh h_err]
  refine ⟨rfl, ?_⟩
  show (s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame)).error? = none
  unfold Verify.DB.insert
  simp [h_err, h_fresh, Verify.DB.error]

/-- The inserted database, spelled out: only `objects` gains the new assertion. -/
theorem insert_assert_fresh_eq (db : Verify.DB) (pos : Verify.Pos) (l : String)
    (fmla : Verify.Formula) (fr : Verify.Frame)
    (h_fresh : db.find? l = none) (h_err : db.error? = none) :
    db.insert pos l (.assert fmla fr) =
      { db with objects := db.objects.insert l (.assert fmla fr l) } := by
  unfold Verify.DB.insert
  simp [h_err, h_fresh, Verify.DB.error]

/-! ## From provability to the stored assertion -/

/-- A spec-provable claim `f` (constant head, symbols respecting the active
frame) under a fresh label has a normal proof whose run from the parser's start
state ends in a state that `finishProof` turns into exactly the assertion insert. -/
theorem normal_proof_finishes_exact (s : Verify.ParserState) (label : String)
    (f : Verify.Formula) (pos : Verify.Pos) (frImpl : Verify.Frame)
    (h_wf : WellFormedDB s.db) (h_sf : CompletenessScopedFacts s.db)
    (Γ : Spec.Database) (fr : Spec.Frame)
    (h_db : toDatabase s.db = some Γ) (h_frame : toFrame s.db s.db.frame = some fr)
    (h_dv_wf : ∀ l fr' e, Γ l = some (fr', e) → DVWellFormed fr')
    (h_head : f.hasConstHead = true)
    (h_resp : s.db.formulaSymsRespectFrame f s.db.frame = true)
    (h_prov : Spec.Provable Γ fr (toExpr f))
    (h_fresh : s.db.find? label = none) (h_err : s.db.error? = none) :
    ∃ (proof : Array String) (pr : Verify.ProofState),
      proof.foldlM (fun pr step => s.db.stepNormal pr step)
        { s.db.mkProofState pos label f frImpl with ptp := .normal } = .ok pr ∧
      s.finishProof pr =
        { s with tokp := .start, db := s.db.insert pos label (.assert f frImpl) } ∧
      (s.finishProof pr).db.error? = none := by
  obtain ⟨proof, pr₁, h_fold, h_stack⟩ :=
    verify_impl_complete_exact s.db label f h_wf h_sf Γ fr h_db h_frame h_dv_wf
      h_head h_resp h_prov
  have h_fold' := foldlM_stepNormal_from_mkProofState s.db proof label f pos frImpl pr₁ h_fold
  rw [h_stack] at h_fold'
  refine ⟨proof, _, h_fold', ?_, ?_⟩
  · exact finishProof_of_exact_state s _ rfl rfl rfl h_fresh h_err
  · exact (finishProof_of_exact s _ rfl rfl rfl h_fresh h_err).2

end Metamath.CheckerCompleteness
