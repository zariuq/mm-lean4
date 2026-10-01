import Metamath.ParserEquivalence
import Metamath.PrefixProvability.Checker
import Metamath.Verify.Conformance

set_option autoImplicit false

namespace Metamath.ParserEquivalenceExamples

open Metamath.ParserEquivalence
open Metamath.Spec.Equivalence

/-! These examples use only single-pass API surfaces from
`Metamath.ParserEquivalence`; they do not reference two-pass compatibility
theorem names. -/

/-- Small usage example: importing `Metamath.ParserEquivalence` gives direct access
    to the strict formula-equality upgrade theorem. -/
theorem parserEquivalence_usage_example
    (db : Verify.DB) (f f' : Verify.Formula)
    (h_wf_f : WF.WellFormedFormula f)
    (h_wf_f' : WF.WellFormedFormula f')
    (h_resp_f : Verify.DB.formulaSymsRespectFrame db f db.frame = true)
    (h_resp_f' : Verify.DB.formulaSymsRespectFrame db f' db.frame = true)
    (h_eq : toExpr f' = toExpr f) :
    f' = f := by
  exact toExpr_eq_implies_formula_eq db f f' h_wf_f h_wf_f' h_resp_f h_resp_f' h_eq

/-- Minimal usage example: a frame-derivable formula is provable (total DB). -/
theorem parserEquivalence_frameDerivable_total_example
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_derivable :
      FrameDerivable (toDatabaseTotal (Verify.checkBytes bytes)) fr
        (exprToFormula (varMapOfFrame fr) e)) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e := by
  simpa using
    parser_frameDerivable_to_operational_total
      bytes h_success fr e h_frame h_derivable

/-! ## Recommended usage templates

These lemmas are compact call-order templates for downstream users. Here acceptance means a
successful run of the proof steps, not `finishProof`; for acceptance of source text see
`Metamath.SourceCompleteness`.
1. acceptance -> frame derivability
2. acceptance -> Mario's declarative provability
3. frame derivability -> acceptance -/

/-! ## Theorem map (recommended call order)

For downstream integrations, call the API in this order:

1. **Parser acceptance -> frame derivability (preferred first step)**:
   `recommended_usage_soundness_frameDerivable_total`.
2. **Frame derivability -> parser acceptance (completeness path)**:
   `recommended_usage_completeness_frameDerivable_total`.
3. **Parser acceptance -> Mario's declarative provability**:
   `recommended_usage_soundness_declarative_total`.

Frame derivability is exactly acceptance; Mario's declarative provability in
the frame context is implied by it. For stored statements and dummy variables,
see `Metamath.Spec.Completeness`. -/

/-- Recommended soundness-first template: acceptance implies frame
derivability. -/
theorem recommended_usage_soundness_frameDerivable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (h_accept :
      ∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
        proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
          ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
           Verify.ProofTokenParser.normal, false⟩ = Except.ok pr_final ∧
        pr_final.stack.size = 1 ∧
        pr_final.stack[0]? = some f' ∧
        toExpr f' = toExpr f) :
    ∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      FrameDerivable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f)) := by
  exact (proofChecker_normal_iff_frameDerivable_in_parsedDB
    bytes label f h_success).1 h_accept

/-- Recommended soundness template to Mario's semantics: acceptance implies
declarative provability in the frame context. -/
theorem recommended_usage_soundness_declarative_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (h_accept :
      ∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
        proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
          ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
           Verify.ProofTokenParser.normal, false⟩ = Except.ok pr_final ∧
        pr_final.stack.size = 1 ∧
        pr_final.stack[0]? = some f' ∧
        toExpr f' = toExpr f) :
    ∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Declarative.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f)) := by
  exact proofChecker_normal_implies_declarative_provable_in_parsedDB
    bytes label f h_success h_accept

/-- Recommended completeness template: frame derivability implies parser
acceptance (normal mode). -/
theorem recommended_usage_completeness_frameDerivable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_derivable :
      FrameDerivable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :
    ∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
         Verify.ProofTokenParser.normal, false⟩ = Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f := by
  exact (proofChecker_normal_iff_frameDerivable_in_parsedDB
    bytes label f h_success).2 ⟨fr, h_frame, h_derivable⟩

/-- Usage example: `sound` is prefix-certified, so the certified API applies. -/
theorem parserEquivalence_sound_example
    (arr : ByteArray)
    (h_success : (Verify.checkBytes arr .sound).error? = none)
    (pos : Nat) (tk : ByteSlice) (pr : Verify.ProofState)
    (h_evt : Metamath.PrefixProvability.Checker.FinishProofEvent
      (({ (default : Verify.ParserState) with
          db := { (default : Verify.DB) with config := .sound } }).feedAll 0 arr)
      pos tk pr) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (({ (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .sound } }).feedAll 0 arr).db = some Γ ∧
      toFrame (({ (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .sound } }).feedAll 0 arr).db
        (({ (default : Verify.ParserState) with
          db := { (default : Verify.DB) with config := .sound } }).feedAll 0 arr).db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr.fmla) := by
  exact Metamath.PrefixProvability.Checker.checkBytes_finalState_finishProofEvent_certified
    arr .sound Verify.ModeConfig.isSound_sound h_success pos tk pr h_evt

/-- **Headline usage**: an accepted run under a prefix-certified profile gives the
fold-wide guarantee — every finish-proof event in the feed loop was checked
against the database as it stood before that theorem was inserted.

This, not the final-state eliminators below, is what acceptance means. -/
theorem parserEquivalence_sound_headline
    (arr : ByteArray)
    (h_success : (Verify.checkBytes arr .sound).error? = none) :
    Metamath.PrefixProvability.Checker.AllFeedAllEventsProvable 0 arr
      { (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .sound } } :=
  Metamath.PrefixProvability.Checker.checkBytes_feedEvents_prefix_provable_certified
    arr .sound Verify.ModeConfig.isSound_sound h_success

/-- The same headline guarantee under the `knife` profile. -/
theorem parserEquivalence_knife_headline
    (arr : ByteArray)
    (h_success : (Verify.checkBytes arr .knife).error? = none) :
    Metamath.PrefixProvability.Checker.AllFeedAllEventsProvable 0 arr
      { (default : Verify.ParserState) with
        db := { (default : Verify.DB) with config := .knife } } :=
  Metamath.PrefixProvability.Checker.checkBytes_feedEvents_prefix_provable_certified
    arr .knife Verify.ModeConfig.isSound_knife h_success

/-- Narrow example (final-state eliminator only): `knife` is also prefix-certified. -/
theorem parserEquivalence_knife_example
    (arr : ByteArray)
    (h_success : (Verify.checkBytes arr .knife).error? = none)
    (pos : Nat) (tk : ByteSlice) (pr : Verify.ProofState)
    (h_evt : Metamath.PrefixProvability.Checker.FinishProofEvent
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
  exact Metamath.PrefixProvability.Checker.checkBytes_finalState_finishProofEvent_certified
    arr .knife Verify.ModeConfig.isSound_knife h_success pos tk pr h_evt

/-- Declarative canary (canonical `Provable.var` behavior):
with empty context and no axioms, a variable's own floating-hypothesis formula
is derivable via the unconditional `var` constructor. -/
theorem declarative_var_seed_canary_canonical :
    Metamath.Provable (fun _ : Metamath.Statement => False)
      (Metamath.Context.mk' [] [])
      ((⟨"wff", 0⟩ : Metamath.VR).vhyp) := by
  exact Metamath.Provable.var ⟨"wff", 0⟩

end Metamath.ParserEquivalenceExamples
