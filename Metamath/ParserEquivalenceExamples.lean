import Metamath.ParserEquivalence
import Metamath.PrefixWitnessCheckBytes
import Metamath.VerifyConformanceThms

set_option autoImplicit false

namespace Metamath.ParserEquivalenceExamples

open Metamath.ParserEquivalence
open Metamath.Spec.Equivalence

/-- Small usage example: importing `Metamath.ParserEquivalence` gives direct access
    to the strict formula-equality upgrade theorem. -/
theorem parserEquivalence_usage_example
    (db : Verify.DB) (f : Verify.Formula)
    (h_wf : WF.WellFormedFormula f)
    (h_resp : Verify.DB.formulaSymsRespectFrame db f db.frame = true) :
    f = f := by
  exact toExpr_eq_implies_formula_eq db f f h_wf h_wf h_resp h_resp rfl

/-- Minimal usage example for supported-local completeness (total DB). -/
theorem parserEquivalence_supported_total_example
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_supported_sem :
      SupportedProvable (toDatabaseTotal (Verify.checkBytes bytes)) fr
        (exprToFormula (varMapOfFrame fr) e)) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e := by
  simpa using
    parser_supported_semantic_to_operational_total
      bytes h_success fr e h_frame h_supported_sem

/-! ## Recommended usage templates (supported-first)

These lemmas are compact call-order templates for downstream users:
1. acceptance -> supported semantic witness
2. acceptance -> canonical semantic witness
3. supported semantic witness -> acceptance -/

/-! ## Theorem map (recommended call order)

For downstream integrations, call the API in this order:

1. **Parser acceptance -> supported-local witness (preferred first step)**:
   `recommended_usage_soundness_supported_total`.
2. **Supported-local witness -> parser acceptance (completeness path)**:
   `recommended_usage_completeness_supported_total`.
3. **Parser acceptance -> canonical semantic witness**:
   `recommended_usage_soundness_semantic_total`.

This keeps the canonical split explicit:
- unconditional soundness to `Spec.Semantic.Provable`;
- completeness through `SupportedProvable` (derivation-local support). -/

/-- Recommended soundness-first template: acceptance witness implies a
derivation-local supported witness (no global support premise). -/
theorem recommended_usage_soundness_supported_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (h_accept :
      ∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
        proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
          ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
           Verify.ProofTokenParser.normal⟩ = Except.ok pr_final ∧
        pr_final.stack.size = 1 ∧
        pr_final.stack[0]? = some f' ∧
        toExpr f' = toExpr f) :
    ∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      SupportedProvable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f)) := by
  exact (verify_parser_acceptance_iff_supported_semantic_provable_total
    bytes label f h_success).1 h_accept

/-- Recommended soundness-first template to canonical semantics:
acceptance witness implies semantic witness (no global support premise). -/
theorem recommended_usage_soundness_semantic_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (h_accept :
      ∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
        proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
          ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
           Verify.ProofTokenParser.normal⟩ = Except.ok pr_final ∧
        pr_final.stack.size = 1 ∧
        pr_final.stack[0]? = some f' ∧
        toExpr f' = toExpr f) :
    ∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f)) := by
  exact verify_parser_acceptance_implies_semantic_provable_total
    bytes label f h_success h_accept

/-- Recommended completeness-first template: a supported semantic witness
implies parser acceptance (normal mode). -/
theorem recommended_usage_completeness_supported_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_supported :
      SupportedProvable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :
    ∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
         Verify.ProofTokenParser.normal⟩ = Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f := by
  exact (verify_parser_acceptance_iff_supported_semantic_provable_total
    bytes label f h_success).2 ⟨fr, h_frame, h_supported⟩

/-- Usage example: `soundDefault` is prefix-certified, so the certified API applies. -/
theorem parserEquivalence_soundDefault_example
    (arr : ByteArray)
    (h_success : (Verify.checkBytes arr .soundDefault).error? = none)
    (pos : Nat) (tk : ByteSlice) (pr : Verify.ProofState)
    (h_evt : Metamath.PrefixWitnessCheckBytes.FinishProofEvent
      (({ (default : Verify.ParserState) with
          db := { (default : Verify.DB) with config := .soundDefault } }).feedAll 0 arr)
      pos tk pr) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (({ (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .soundDefault } }).feedAll 0 arr).db = some Γ ∧
      toFrame (({ (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .soundDefault } }).feedAll 0 arr).db
        (({ (default : Verify.ParserState) with
          db := { (default : Verify.DB) with config := .soundDefault } }).feedAll 0 arr).db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr.fmla) := by
  exact Metamath.PrefixWitnessCheckBytes.checkBytes_done_finishProofEvent_certified
    arr .soundDefault Verify.ModeConfig.soundDefault_prefixCertified h_success pos tk pr h_evt

/-- Usage example: `knife` is also prefix-certified. -/
theorem parserEquivalence_knife_example
    (arr : ByteArray)
    (h_success : (Verify.checkBytes arr .knife).error? = none)
    (pos : Nat) (tk : ByteSlice) (pr : Verify.ProofState)
    (h_evt : Metamath.PrefixWitnessCheckBytes.FinishProofEvent
      (({ (default : Verify.ParserState) with
          db := { (default : Verify.DB) with config := .knife } }).feedAll 0 arr)
      pos tk pr) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (({ (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .knife } }).feedAll 0 arr).db = some Γ ∧
      toFrame (({ (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .knife } }).feedAll 0 arr).db
        (({ (default : Verify.ParserState) with
          db := { (default : Verify.DB) with config := .knife } }).feedAll 0 arr).db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr.fmla) := by
  exact Metamath.PrefixWitnessCheckBytes.checkBytes_done_finishProofEvent_certified
    arr .knife Verify.ModeConfig.knife_prefixCertified h_success pos tk pr h_evt

/-- Semantic canary (canonical `Provable.var` behavior):
with empty context and no axioms, a variable's own floating-hypothesis formula
is derivable via the unconditional `var` constructor. -/
theorem declarative_var_seed_canary_canonical :
    Metamath.Provable (fun _ : Metamath.Statement => False)
      (Metamath.Context.mk' [] [])
      ((⟨"wff", 0⟩ : Metamath.VR).vhyp) := by
  exact Metamath.Provable.var ⟨"wff", 0⟩

end Metamath.ParserEquivalenceExamples
