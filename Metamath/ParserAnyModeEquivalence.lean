/-
ParserAnyModeEquivalence — Phase C8: Any-Mode Biconditional

Integration module connecting compressed and normal proof verification
to the canonical spec-level biconditional. Strengthens the normal-only
`verify_parser_acceptance_iff_spec_provable` to cover both proof modes.

**Theorem chain (each used by the next):**
1. `finishProof_success_stack_conditions` — extract stack properties from finishProof success
2. `compressed_proof_full_provenance_tight` — drop redundant h_stack_one/h_stack_fmla
3. `compressed_acceptance_implies_normal_acceptance` — compressed ⊂ normal at DB level
4. `verify_parser_acceptance_any_mode_iff_spec_provable` — bytes-level biconditional
-/

import Metamath.PrefixTraceCompressed

set_option autoImplicit false

namespace Metamath.ParserAnyModeEquivalence

open Metamath.Verify
open Metamath.WF
open Metamath.PrefixProvenance
open Metamath.PrefixTraceCompressed
open Metamath.ParserOps (withAt_success_eq)
open Metamath.ParserLoopInduction
  (ParserState_mkErrorFromEvidence_sets_error withAt_preserves_error)
open Metamath.Kernel (toDatabase toFrame toExpr
  verify_parser_sound_of_impl_acceptance_equiv
  verify_parser_accepts_of_spec_provable
  parser_construction_wf_scoped)

-- Re-establish Formula to resolve ambiguity with Kernel.Formula
private abbrev Formula := Metamath.Verify.Formula

/-! ## Step 1: finishProof stack extraction

If `finishProof` succeeds (no error), the proof state must have had:
- exactly one element on the stack
- that element equals the claimed formula
- the proof token parser was `.normal` or `.compressed 0`
-/

theorem finishProof_success_stack_conditions
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none) :
    pr.stack.size = 1 ∧
    pr.stack[0]? = some pr.fmla ∧
    (pr.ptp = .normal ∨ pr.ptp = .compressed 0) := by
  cases pr with
  | mk pos l fmla fr heap stack ptp =>
      cases ptp with
      | start =>
          exfalso
          have : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .start⟩).db.error? ≠ none := by
            simp [ParserState.finishProof]
            exact withAt_preserves_error l _ (ParserState_mkErrorFromEvidence_sets_error _ _ _)
          exact this h_success
      | preload =>
          exfalso
          have : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .preload⟩).db.error? ≠ none := by
            simp [ParserState.finishProof]
            exact withAt_preserves_error l _ (ParserState_mkErrorFromEvidence_sets_error _ _ _)
          exact this h_success
      | normal =>
          let inner : Unit → ParserState := fun _ => Id.run do
            let s := { s with tokp := .start }
            unless stack.size == 1 do
              return s.mkErrorFromEvidence pos
                (.theoremFinality (.theoremMoreThanOneStackElement stack.size))
            unless stack[0]! == fmla do
              return s.mkErrorFromEvidence pos
                (.theoremFinality (.theoremClaimMismatch fmla stack[0]!))
            s.withDB fun db => db.insert pos l (.assert fmla fr)
          have h_at : (ParserState.withAt l inner).db.error? = none := by
            simpa [ParserState.finishProof, inner] using h_success
          rcases withAt_success_eq l inner h_at with ⟨h_ok, _⟩
          by_cases h_size : stack.size == 1
          · by_cases h_eq' : stack[0]! == fmla
            · have h_sz : stack.size = 1 := beq_iff_eq.mp h_size
              have h_lt : 0 < stack.size := by omega
              have h_val : stack[0]! = fmla := LawfulBEq.eq_of_beq h_eq'
              simp [getElem!_pos, h_lt] at h_val
              exact ⟨h_sz, by rw [Array.getElem?_eq_getElem h_lt, h_val], Or.inl rfl⟩
            · exact absurd h_ok (by simp [inner, h_size, h_eq',
                ParserState.mkErrorFromEvidence, ParserState.withDB])
          · exact absurd h_ok (by simp [inner, h_size,
              ParserState.mkErrorFromEvidence, ParserState.withDB])
      | compressed chr =>
          by_cases h_chr : chr = 0
          · subst h_chr
            let inner : Unit → ParserState := fun _ => Id.run do
              let s := { s with tokp := .start }
              unless stack.size == 1 do
                return s.mkErrorFromEvidence pos
                  (.theoremFinality (.theoremMoreThanOneStackElement stack.size))
              unless stack[0]! == fmla do
                return s.mkErrorFromEvidence pos
                  (.theoremFinality (.theoremClaimMismatch fmla stack[0]!))
              s.withDB fun db => db.insert pos l (.assert fmla fr)
            have h_at : (ParserState.withAt l inner).db.error? = none := by
              simpa [ParserState.finishProof, inner] using h_success
            rcases withAt_success_eq l inner h_at with ⟨h_ok, _⟩
            by_cases h_size : stack.size == 1
            · by_cases h_eq' : stack[0]! == fmla
              · have h_sz : stack.size = 1 := beq_iff_eq.mp h_size
                have h_lt : 0 < stack.size := by omega
                have h_val : stack[0]! = fmla := LawfulBEq.eq_of_beq h_eq'
                simp [getElem!_pos, h_lt] at h_val
                exact ⟨h_sz, by rw [Array.getElem?_eq_getElem h_lt, h_val], Or.inr rfl⟩
              · exact absurd h_ok (by simp [inner, h_size, h_eq',
                  ParserState.mkErrorFromEvidence, ParserState.withDB])
            · exact absurd h_ok (by simp [inner, h_size,
                ParserState.mkErrorFromEvidence, ParserState.withDB])
          · exfalso
            have : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .compressed chr⟩).db.error? ≠ none := by
              simp [ParserState.finishProof, h_chr]
              exact withAt_preserves_error l _ (ParserState_mkErrorFromEvidence_sets_error _ _ _)
            exact this h_success

/-! ## Step 2: Tightened compressed provenance (no redundant stack hypotheses)

Wrapper around `compressed_proof_full_provenance` that derives the stack
conditions from `h_finish` instead of requiring them as hypotheses. -/

theorem compressed_proof_full_provenance_tight
    (s : ParserState) (label : String) (fmla : Formula)
    (tk_open : ByteSlice) (preload_toks : List ByteSlice)
    (tk_close : ByteSlice) (comp_toks : List ByteSlice)
    (all_acts : List ParserState.CompressedAction)
    (pr₀ pr₁ pr₂ pr₃ pr_final : ProofState)
    (h_init : pr₀ = ⟨⟨0,0⟩, label, fmla, s.db.frame, #[], #[], .start⟩)
    (h_open_ok : (s.feedProof tk_open pr₀).db.error? = none)
    (h_open : tk_open.eqArray "(".toAscii)
    (h_open_tokp : (s.feedProof tk_open pr₀).tokp = .proof pr₁)
    (h_preload : PreloadTokensOK s pr₁ preload_toks pr₂)
    (h_close_ok : (s.feedProof tk_close pr₂).db.error? = none)
    (h_close : tk_close.eqArray ")".toAscii)
    (h_close_tokp : (s.feedProof tk_close pr₂).tokp = .proof pr₃)
    (h_comp : CompressedTokensOK s pr₃ comp_toks pr_final all_acts)
    (h_finish : (s.finishProof pr_final).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db) :
    ∃ (Γ_final : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase (s.finishProof pr_final).db = some Γ_final ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ_final spec_fr (toExpr pr_final.fmla) := by
  obtain ⟨h_stack_one, h_stack_fmla, _⟩ :=
    finishProof_success_stack_conditions s pr_final h_finish
  exact compressed_proof_full_provenance s label fmla
    tk_open preload_toks tk_close comp_toks all_acts
    pr₀ pr₁ pr₂ pr₃ pr_final
    h_init h_open_ok h_open h_open_tokp h_preload
    h_close_ok h_close h_close_tokp h_comp
    h_finish h_s_ok h_wf h_stack_one h_stack_fmla

/-! ## Step 3: Compressed ⊂ Normal at DB level

Any `ProofReachableZ` (compressed execution) implies the existence of an
equivalent `stepNormal` fold with the same stack conditions. Used by the
any-mode biconditional to reduce the compressed forward branch to normal. -/

theorem compressed_acceptance_implies_normal_acceptance
    (db : DB) (label : String) (f' : Formula) (stack : Array Formula)
    (h_reach : ProofReachableZ db label f' stack)
    (h_wf : WellFormedDB db)
    (h_size : stack.size = 1) (h_fmla : stack[0]? = some f') :
    ∃ (proof : Array String) (pr_final : ProofState) (f'' : Formula),
      proof.foldlM (fun pr step => db.stepNormal pr step)
        ⟨⟨0,0⟩, label, f', db.frame, #[], #[], .normal⟩ = .ok pr_final ∧
      pr_final.stack.size = 1 ∧ pr_final.stack[0]? = some f'' ∧
      toExpr f'' = toExpr f' := by
  obtain ⟨labels, pr_final, h_fold, h_stack_eq⟩ :=
    compressed_implies_normal_fold db label f' stack h_reach h_wf h_size h_fmla
  exact ⟨labels, pr_final, f', h_fold, h_stack_eq ▸ h_size, h_stack_eq ▸ h_fmla, rfl⟩

/-! ## Step 4: Any-mode biconditional (bytes level)

Under parse success, implementation acceptance in either normal or compressed
mode (up to expression equivalence) is equivalent to spec provability.

- **Forward (soundness)**: Compressed branch → normal fold (Step 3) → soundness
- **Backward (completeness)**: Spec provable → normal acceptance (Or.inl) -/

theorem verify_parser_acceptance_any_mode_iff_spec_provable
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    -- LHS: normal OR compressed acceptance (with expression equivalence)
    ((∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
         Verify.ProofTokenParser.normal⟩ = Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f)
    ∨
    (∃ (stack : Array Verify.Formula) (f' : Verify.Formula),
      ProofReachableZ (Verify.checkBytes bytes) label f' stack ∧
      stack.size = 1 ∧ stack[0]? = some f' ∧
      toExpr f' = toExpr f))
    ↔
    -- RHS: spec provability
    (∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (Verify.checkBytes bytes) = some Γ ∧
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Provable Γ fr (toExpr f)) := by
  constructor
  · -- Forward: soundness
    intro h_accept
    rcases h_accept with h_normal | ⟨stack, f', h_reach, h_size, h_fmla, h_eqExpr⟩
    · -- Normal mode: direct soundness
      exact verify_parser_sound_of_impl_acceptance_equiv bytes label f h_success h_normal
    · -- Compressed mode: reduce to normal via Step 3, then soundness
      have h_wf : WellFormedDB (Verify.checkBytes bytes) :=
        (parser_construction_wf_scoped bytes h_success).1
      obtain ⟨proof, pr_final, f'', h_fold, h_pr_size, h_pr_fmla, h_eq''⟩ :=
        compressed_acceptance_implies_normal_acceptance
          (Verify.checkBytes bytes) label f' stack h_reach h_wf h_size h_fmla
      obtain ⟨Γ, fr, h_db, h_frame, h_prov⟩ :=
        verify_parser_sound_of_impl_acceptance_equiv bytes label f' h_success
          ⟨proof, pr_final, f'', h_fold, h_pr_size, h_pr_fmla, h_eq''⟩
      exact ⟨Γ, fr, h_db, h_frame, h_eqExpr ▸ h_prov⟩
  · -- Backward: completeness (always produces normal acceptance)
    intro h_spec
    exact Or.inl (verify_parser_accepts_of_spec_provable bytes label f h_success h_spec)

end Metamath.ParserAnyModeEquivalence
