import Metamath.ParserEquivalence
import Metamath.PrefixWitnessCheckBytes

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

/-- Minimal usage example for the total parser-to-semantic bridge. -/
theorem parserEquivalence_semantic_total_example
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e ↔
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  simpa using parser_operational_iff_semantic_total bytes h_success fr e h_frame

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

end Metamath.ParserEquivalenceExamples
