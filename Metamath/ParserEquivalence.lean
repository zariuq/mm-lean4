/-
ParserEquivalence — Canonical API Surface

This module is the single entry point for the MM-Lean4 verification results.
Import this module to access all top-level theorems.

**Main results (all sorry-free, axiom-free):**

1. `verify_parser_acceptance_iff_spec_provable` — Normal-mode biconditional
2. `verify_parser_acceptance_any_mode_iff_spec_provable` — Any-mode biconditional
3. `ProofReachableZ_iff_NormalProofReachable` — Mode equivalence
4. `compressed_completeness_of_normal_completeness` — Compressed completeness
5. `toExpr_eq_implies_formula_eq` — Strict formula equality upgrade
-/

import Metamath.ParserAnyModeEquivalence

set_option autoImplicit false

namespace Metamath.ParserEquivalence

open Metamath.Kernel (toExpr toExpr_injective_of_wf_respects_frame)

-- Re-export core theorems from KernelClean and ParserAnyModeEquivalence.
-- Users can access these via `open Metamath.ParserEquivalence`.
export Metamath.Kernel
  (toDatabase toFrame toExpr
   verify_parser_acceptance_iff_spec_provable
   verify_parser_sound_of_impl_acceptance_equiv
   verify_parser_accepts_of_spec_provable
   parser_construction_wf_scoped)

export Metamath.ParserAnyModeEquivalence
  (verify_parser_acceptance_any_mode_iff_spec_provable
   ProofReachableZ_iff_NormalProofReachable
   compressed_completeness_of_normal_completeness
   finishProof_success_stack_conditions)

/-! ## Strict formula equality upgrade

The biconditionals above use `toExpr f' = toExpr f` (expression equivalence).
When both formulas are well-formed and respect the frame, this upgrades to
literal formula equality `f' = f` via `toExpr` injectivity. -/

/-- Upgrade `toExpr` equality to literal formula equality.

Requires both formulas to be well-formed (nonempty with constant head)
and to have all symbols respect the given frame. These conditions hold for
any formula stored in a `WellFormedDB` assertion and for stack elements
after a successful proof fold. -/
theorem toExpr_eq_implies_formula_eq
    (db : Verify.DB) (f f' : Verify.Formula)
    (h_wf_f : WF.WellFormedFormula f)
    (h_wf_f' : WF.WellFormedFormula f')
    (h_resp_f : Verify.DB.formulaSymsRespectFrame db f db.frame = true)
    (h_resp_f' : Verify.DB.formulaSymsRespectFrame db f' db.frame = true)
    (h_eq : toExpr f' = toExpr f) :
    f' = f :=
  toExpr_injective_of_wf_respects_frame db db.frame f' f
    h_wf_f' h_wf_f h_resp_f' h_resp_f h_eq

end Metamath.ParserEquivalence
