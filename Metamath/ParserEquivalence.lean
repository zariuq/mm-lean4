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
6. `normal_trace_sound` — Token-trace soundness (normal mode)
7. `compressed_trace_sound` — Token-trace soundness (compressed mode)
-/

import Metamath.ParserAnyModeEquivalence

/-!
## Theorem Map: Trust Chain Layers

### Layer 1 — Bytes-level biconditionals (completeness + soundness)
- `verify_parser_acceptance_iff_spec_provable` (KernelClean.lean:10976)
  Normal-mode `foldlM stepNormal` ↔ `Spec.Provable`. Canonical biconditional.
- `verify_parser_acceptance_any_mode_iff_spec_provable` (ParserAnyModeEquivalence.lean:185)
  (Normal `foldlM` ∨ `ProofReachableZ`) ↔ `Spec.Provable`. Mode-agnostic wrapper.

### Layer 2 — Token-trace soundness (parser execution → Spec.Provable)
- `normal_trace_sound`: `feedProof` token stream in normal mode → `Spec.Provable`
- `compressed_trace_sound`: 4-phase `feedProof` ("(" → preload → ")" → body) → `Spec.Provable`

Both use ParserState-level DB (`finishProof` insertion-time), NOT final `checkBytes` DB.
These prove that actual parser execution implies correctness — no abstract reachability.

### Layer 3 — Mode bridge (token-trace → DB-level reachability)
- `compressed_full_bridge` (PrefixProvenance.lean:2660):
  Parser compressed execution → `ProofReachableZ` (from pure DB operations)
- `ProofReachableZ_iff_NormalProofReachable` (ParserAnyModeEquivalence.lean:236):
  All three modes (normal/compressed/Z-compressed) ↔ `NormalProofReachable` under `WellFormedDB`
- `compressed_acceptance_implies_normal_acceptance` (ParserAnyModeEquivalence.lean:163):
  Any `ProofReachableZ` → ∃ `stepNormal` fold (same form as normal biconditional LHS)

### Layer 4 — Spec equivalence
- `operational_iff_semantic` (Equivalence.lean):
  `Spec.Provable` ↔ `Semantic.Provable` (Mario Carneiro's formulation)

### How the layers connect
- Layer 1 biconditionals are the canonical completeness results (bytes → `Spec.Provable` ↔).
  Normal branch: explicit `foldlM stepNormal`. Compressed branch: `ProofReachableZ`.
- `ProofReachableZ` is NOT assumed — it IS proven from token execution (Layer 3).
- Layer 2 trace theorems are strictly additional: they show the parser's actual
  `feedProof` token-by-token execution implies `Spec.Provable` with zero abstract
  reachability hypotheses.
- Prefix-provenance (each $p provable using only prior assertions) is future work.
  Layer 2 gives `Provable` in `finishProof`-time DB; Layer 1 gives `Provable` in final DB.
-/

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

/-! ## Token-trace acceptance predicates

These structures bundle the hypotheses of the provenance theorems into clean
predicates. They capture: "the parser processed proof tokens one-by-one via
`feedProof`, producing a successful `finishProof`."

**Usage**: Given a `NormalTraceAccepts` or `CompressedTraceAccepts` witness
plus `WellFormedDB` context, apply `normal_trace_sound` or `compressed_trace_sound`
to obtain `Spec.Provable`. -/

open Metamath.Verify
open Metamath.WF (WellFormedDB)
open Metamath.PrefixProvenance (NormalTokensOK normal_proof_full_provenance
  feedProof_start_establishes_reachable NormalTokensOK_preserves_invariant)
open Metamath.PrefixTraceCompressed (PreloadTokensOK CompressedTokensOK
  NormalProofReachable_same_db_provable compressed_proof_prefix_provenance)
open Metamath.ParserAnyModeEquivalence (finishProof_success_stack_conditions
  compressed_proof_full_provenance_tight)

-- Resolve Formula ambiguity (Kernel.Formula vs Verify.Formula)
private abbrev Formula := Metamath.Verify.Formula

/-- Normal-mode trace acceptance: the parser processed proof tokens one-by-one
    via `feedProof` in normal mode, producing a successful `finishProof`.

    The first token `tk₀` transitions from `.start` to `.normal`, then
    `NormalTokensOK` captures the remaining token-by-token fold.

    Stack conditions (`stack.size = 1`, `stack[0]? = some fmla`) are NOT
    included — they are derived from `finish_ok` via
    `finishProof_success_stack_conditions`. -/
structure NormalTraceAccepts (s : ParserState) (tk₀ : ByteSlice) (tokens : List ByteSlice)
    (pr₀ pr₁ pr_final : ProofState) : Prop where
  init_stack : pr₀.stack = #[]
  init_frame : pr₀.frame = s.db.frame
  init_start : pr₀.ptp = ProofTokenParser.start
  first_ok : (s.feedProof tk₀ pr₀).db.error? = none
  first_not_open : ¬ tk₀.eqArray "(".toAscii
  first_not_q : ¬ tk₀.eqArray "?".toAscii
  first_tokp : (s.feedProof tk₀ pr₀).tokp = .proof pr₁
  body : NormalTokensOK s pr₁ tokens pr_final
  finish_ok : (s.finishProof pr_final).db.error? = none

/-- Compressed-mode trace acceptance: the parser processed a compressed proof
    in four phases via `feedProof`, producing a successful `finishProof`.

    Phase A: `tk_open` = "(" → `preloadMandatoryHyps` → `.preload`
    Phase B: `preload_toks` → `db.preload` per label (fill heap)
    Phase C: `tk_close` = ")" → `.compressed 0`
    Phase D: `comp_toks` → `decodeCompressed` → `applyCompressedActions`

    Stack conditions are NOT included — they are derived from `finish_ok`
    via `finishProof_success_stack_conditions`. -/
structure CompressedTraceAccepts (s : ParserState) (label : String) (fmla : Formula)
    (tk_open : ByteSlice) (preload_toks : List ByteSlice)
    (tk_close : ByteSlice) (comp_toks : List ByteSlice)
    (all_acts : List ParserState.CompressedAction)
    (pr₀ pr₁ pr₂ pr₃ pr_final : ProofState) : Prop where
  init : pr₀ = ⟨⟨0,0⟩, label, fmla, s.db.frame, #[], #[], .start⟩
  open_ok : (s.feedProof tk_open pr₀).db.error? = none
  is_open : tk_open.eqArray "(".toAscii
  open_tokp : (s.feedProof tk_open pr₀).tokp = .proof pr₁
  preload : PreloadTokensOK s pr₁ preload_toks pr₂
  close_ok : (s.feedProof tk_close pr₂).db.error? = none
  is_close : tk_close.eqArray ")".toAscii
  close_tokp : (s.feedProof tk_close pr₂).tokp = .proof pr₃
  compressed : CompressedTokensOK s pr₃ comp_toks pr_final all_acts
  finish_ok : (s.finishProof pr_final).db.error? = none

/-! ## Token-trace soundness theorems

These theorems prove that actual parser execution (via `feedProof` token-by-token)
implies `Spec.Provable`. They use NO abstract reachability hypotheses — the
trace structure itself is the witness.

The conclusion gives `Spec.Provable` in the `finishProof`-time database
(`toDatabase (s.finishProof pr_final).db`), which includes the newly-inserted
assertion. -/

/-- Normal-mode trace soundness: if the parser processed tokens in normal mode
    and `finishProof` succeeded, then the proved formula is `Spec.Provable`. -/
theorem normal_trace_sound
    (s : ParserState) (tk₀ : ByteSlice) (tokens : List ByteSlice)
    (pr₀ pr₁ pr_final : ProofState)
    (h_trace : NormalTraceAccepts s tk₀ tokens pr₀ pr₁ pr_final)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (s.finishProof pr_final).db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr_final.fmla) := by
  have ⟨h_stack_one, h_stack_fmla, _⟩ :=
    finishProof_success_stack_conditions s pr_final h_trace.finish_ok
  exact normal_proof_full_provenance s tk₀ tokens pr₀ pr₁ pr_final
    h_trace.init_stack h_trace.init_start
    h_trace.first_ok h_trace.first_not_open h_trace.first_not_q
    h_trace.first_tokp h_trace.body h_trace.finish_ok h_s_ok h_wf
    h_stack_one h_stack_fmla

/-- Compressed-mode trace soundness: if the parser processed a 4-phase compressed
    proof and `finishProof` succeeded, then the proved formula is `Spec.Provable`. -/
theorem compressed_trace_sound
    (s : ParserState) (label : String) (fmla : Formula)
    (tk_open : ByteSlice) (preload_toks : List ByteSlice)
    (tk_close : ByteSlice) (comp_toks : List ByteSlice)
    (all_acts : List ParserState.CompressedAction)
    (pr₀ pr₁ pr₂ pr₃ pr_final : ProofState)
    (h_trace : CompressedTraceAccepts s label fmla tk_open preload_toks
      tk_close comp_toks all_acts pr₀ pr₁ pr₂ pr₃ pr_final)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (s.finishProof pr_final).db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr_final.fmla) :=
  compressed_proof_full_provenance_tight s label fmla
    tk_open preload_toks tk_close comp_toks all_acts
    pr₀ pr₁ pr₂ pr₃ pr_final
    h_trace.init h_trace.open_ok h_trace.is_open h_trace.open_tokp
    h_trace.preload h_trace.close_ok h_trace.is_close h_trace.close_tokp
    h_trace.compressed h_trace.finish_ok h_s_ok h_wf

/-! ## Pre-insert (prefix) trace soundness

These theorems prove that actual parser execution implies `Spec.Provable` in the
**pre-insertion** database (`toDatabase s.db`), not the post-insertion database.
This is strictly stronger than post-insertion provability and captures prefix-provenance:
each theorem is provable using only assertions that existed before it was added. -/

/-- Normal-mode prefix provability: if the parser processed tokens in normal mode
    and `finishProof` succeeded, then the proved formula is `Spec.Provable`
    in the **pre-insertion** database (`toDatabase s.db`). -/
theorem normal_trace_prefix_provable
    (s : ParserState) (tk₀ : ByteSlice) (tokens : List ByteSlice)
    (pr₀ pr₁ pr_final : ProofState)
    (h_trace : NormalTraceAccepts s tk₀ tokens pr₀ pr₁ pr_final)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase s.db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr_final.fmla) := by
  -- Step 1: First token establishes NormalProofReachable
  obtain ⟨pr₁', h_tokp₁, h_label₁, h_fmla₁, h_frame₁, h_ptp₁, h_reach₁⟩ :=
    feedProof_start_establishes_reachable s tk₀ pr₀
      h_trace.first_ok h_trace.init_start h_trace.first_not_open h_trace.first_not_q
      h_trace.init_stack
  have h_eq₁ : pr₁ = pr₁' := by
    rw [h_trace.first_tokp] at h_tokp₁
    exact TokenParser.proof.inj h_tokp₁
  subst h_eq₁
  rw [← h_label₁, ← h_fmla₁] at h_reach₁
  -- Step 2: Multi-step maintains NormalProofReachable
  obtain ⟨h_reach_final, _, _, _, _⟩ :=
    NormalTokensOK_preserves_invariant s tokens pr₁ pr_final h_trace.body
      h_reach₁ h_ptp₁
  -- Step 3: Stack conditions + pre-insert provability
  have ⟨h_stack_one, h_stack_fmla, _⟩ :=
    finishProof_success_stack_conditions s pr_final h_trace.finish_ok
  exact NormalProofReachable_same_db_provable s.db pr_final.label pr_final.fmla pr_final.stack
    h_reach_final h_s_ok h_wf h_stack_one h_stack_fmla

/-- Compressed-mode prefix provability: if the parser processed a 4-phase compressed
    proof and `finishProof` succeeded, then the proved formula is `Spec.Provable`
    in the **pre-insertion** database (`toDatabase s.db`). -/
theorem compressed_trace_prefix_provable
    (s : ParserState) (label : String) (fmla : Formula)
    (tk_open : ByteSlice) (preload_toks : List ByteSlice)
    (tk_close : ByteSlice) (comp_toks : List ByteSlice)
    (all_acts : List ParserState.CompressedAction)
    (pr₀ pr₁ pr₂ pr₃ pr_final : ProofState)
    (h_trace : CompressedTraceAccepts s label fmla tk_open preload_toks
      tk_close comp_toks all_acts pr₀ pr₁ pr₂ pr₃ pr_final)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase s.db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr_final.fmla) := by
  have ⟨h_stack_one, h_stack_fmla, _⟩ :=
    finishProof_success_stack_conditions s pr_final h_trace.finish_ok
  exact compressed_proof_prefix_provenance s label fmla
    tk_open preload_toks tk_close comp_toks all_acts
    pr₀ pr₁ pr₂ pr₃ pr_final
    h_trace.init h_trace.open_ok h_trace.is_open h_trace.open_tokp
    h_trace.preload h_trace.close_ok h_trace.is_close h_trace.close_tokp
    h_trace.compressed h_trace.finish_ok h_s_ok h_wf
    h_stack_one h_stack_fmla

end Metamath.ParserEquivalence
