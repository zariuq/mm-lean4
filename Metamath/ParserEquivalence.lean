/-
ParserEquivalence — Canonical API Surface

This module is the single entry point for the MM-Lean4 verification results.
Import this module to access all top-level theorems.
For compact usage patterns, see `Metamath/ParserEquivalenceExamples.lean`.

**Main results (no project-declared axioms, no sorries):**

1. `verify_parser_acceptance_iff_spec_provable` — Normal-mode biconditional
2. `verify_parser_acceptance_any_mode_iff_spec_provable` — Any-mode biconditional
3. `ProofReachableZ_iff_NormalProofReachable` — Mode equivalence
4. `compressed_completeness_of_normal_completeness` — Compressed completeness
5. `toExpr_eq_implies_formula_eq` — Strict formula equality upgrade
6. `normal_trace_sound` — Token-trace soundness (normal mode)
7. `compressed_trace_sound` — Token-trace soundness (compressed mode)
8. `parser_supported_semantic_to_operational` — Parser-specialized completeness from local support
9. `parser_supported_semantic_to_operational_total` — Same completeness with total DB extraction
10. `parser_operational_to_supported_total` — Parser-specialized operational -> local-support bridge
11. `parser_operational_to_semantic_total` — Parser-specialized unconditional soundness (total DB)
12. `verify_parser_acceptance_iff_supported_semantic_provable_total` — Normal acceptance <-> supported semantic provability (total DB)
13. `verify_parser_acceptance_any_mode_iff_supported_semantic_provable_total` — Any-mode acceptance <-> supported semantic provability (total DB)
14. `verify_parser_acceptance_implies_semantic_provable_total` — Normal acceptance -> canonical semantic provability (total DB)
15. `verify_parser_acceptance_any_mode_implies_semantic_provable_total` — Any-mode acceptance -> canonical semantic provability (total DB)
16. `parser_operational_iff_semantic(_total)` and `verify_parser_acceptance_*_iff_semantic_provable_total` — legacy global-support compatibility wrappers
-/

import Metamath.ParserAnyModeEquivalence

/-!
## Theorem Map: Trust Chain Layers

### Layer 1 — Bytes-level biconditionals (completeness + soundness)
- `verify_parser_acceptance_iff_spec_provable` (KernelClean.lean:10976)
  Normal-mode `foldlM stepNormal` ↔ `Spec.Provable`. Canonical biconditional.
- `verify_parser_acceptance_any_mode_iff_spec_provable` (ParserAnyModeEquivalence.lean:185)
  (Normal `foldlM` ∨ `ProofReachableZ`) ↔ `Spec.Provable`. Mode-agnostic wrapper.
- `verify_parser_acceptance_iff_supported_semantic_provable_total` (this file):
  normal-mode acceptance ↔ supported semantic provability over `toDatabaseTotal`.
- `verify_parser_acceptance_any_mode_iff_supported_semantic_provable_total` (this file):
  any-mode acceptance ↔ supported semantic provability over `toDatabaseTotal`.
- `verify_parser_acceptance_implies_semantic_provable_total` (this file):
  normal-mode acceptance → canonical semantic provability over `toDatabaseTotal`.
- `verify_parser_acceptance_any_mode_implies_semantic_provable_total` (this file):
  any-mode acceptance → canonical semantic provability over `toDatabaseTotal`.

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
- `parser_supported_semantic_to_operational(_total)` (this file):
  completeness from derivation-local support (`SupportedProvable`), no global
  support premise.
- `parser_operational_to_supported_total` (this file):
  operational/spec witness to derivation-local support (`SupportedProvable`),
  no global support premise.
- `parser_operational_to_semantic_total` (this file):
  unconditional soundness to canonical semantics.
- `parser_operational_iff_semantic(_total)` (this file):
  legacy biconditional wrappers that still require global support.

### Layer 5 — checkBytes-level event-lift (PrefixWitnessCheckBytes)
- `checkBytesCore_prefix_provenance` (PrefixWitnessCheckBytes.lean:1996):
  successful `checkBytesCore` run implies all feed/feedAll finishProof events are prefix-provable
- `checkBytes_prefix_provenance` (PrefixWitnessCheckBytes.lean:2033):
  lifts event-lift theorem to `checkBytes`
- `checkBytes_done_finishProofEvent_prefix_provable` (PrefixWitnessCheckBytes.lean:2068):
  direct eliminator for concrete `FinishProofEvent` at final `feedAll` state

### How the layers connect
- Layer 1 biconditionals are the canonical completeness results (bytes → `Spec.Provable` ↔).
  Normal branch: explicit `foldlM stepNormal`. Compressed branch: `ProofReachableZ`.
- `ProofReachableZ` is NOT assumed — it IS proven from token execution (Layer 3).
- Layer 2 trace theorems are strictly additional: they show the parser's actual
  `feedProof` token-by-token execution implies `Spec.Provable` with zero abstract
  reachability hypotheses.
- Layer 5 closes the parser-loop integration for finishProof events on successful
  `checkBytes` runs, giving explicit pre-insert provability at those events.

### Recommended theorem call order (supported-first)
For new integrations, use this sequence:
1. Completeness target:
   build/provide `SupportedProvable ... (exprToFormula ... (toExpr f))`,
   then call `parser_supported_semantic_to_operational_total`, or directly use
   `verify_parser_acceptance_iff_supported_semantic_provable_total`.
2. Soundness target to canonical semantics:
   from acceptance witnesses, call
   `verify_parser_acceptance_implies_semantic_provable_total`
   (or any-mode analogue).
3. Any-mode completeness:
   use `verify_parser_acceptance_any_mode_iff_supported_semantic_provable_total`.
4. Use global-support wrappers only for legacy downstream code that still
   depends on `SemanticFrameSupported`.

Frontend include-policy bridges are intentionally split:
- `Metamath.FrontendBridge` is single-pass-first.
- `Metamath.Legacy.FrontendBridge` hosts two-pass compatibility wrappers.
-/

set_option autoImplicit false

namespace Metamath.ParserEquivalence

open Metamath.Kernel
  (toExpr toExpr_injective_of_wf_respects_frame toConsts toDatabaseTotal
   frameVarsDisjointConsts_of_toFrame floatVarNoDup_of_uniqueFloatVars
   parser_toDatabase_wellFormed_strong)
open Metamath.Spec.Equivalence

-- Re-export core theorems from KernelClean and ParserAnyModeEquivalence.
-- Users can access these via `open Metamath.ParserEquivalence`.
export Metamath.Kernel
  (toDatabase toDatabaseTotal toFrame toExpr
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
open Metamath.WF (WellFormedDB WellScopedDB WellFormedFrame UniqueFloatVars)
open Metamath.PrefixProvenance (NormalTokensOK normal_proof_full_provenance
  feedProof_start_establishes_reachable NormalTokensOK_preserves_invariant
  ProofReachableZ)
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

/-! ## Parser-specialized operational/semantic bridge

`Spec.Equivalence.operational_iff_semantic` is generic by design. This wrapper
specializes it to parser-origin databases and discharges all structural
premises from `checkBytes` success plus `toDatabase`/`toFrame` witnesses. -/

/-- Shared parser-origin structural premises used by all parser bridge theorems.

From `checkBytes` success plus extraction witnesses, we recover exactly the
proof obligations needed by Spec/semantic bridge results:
- strong DB well-formedness at extracted `Γ`
- no duplicate floating variables in extracted `fr`
- frame-vs-constant disjointness for extracted `fr` -/
private theorem parser_structural_premises
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    WellFormedDatabaseStrong Γ (toConsts (Verify.checkBytes bytes)) ∧
    FloatVarNoDup fr ∧
    Spec.FrameVarsDisjointConsts (toConsts (Verify.checkBytes bytes)) fr := by
  let db := Verify.checkBytes bytes
  have h_wf_scoped : WellFormedDB db ∧ WellScopedDB db := by
    simpa [db] using parser_construction_wf_scoped bytes h_success
  have h_frame_wf : WellFormedFrame db db.frame := h_wf_scoped.1.1
  have h_unique : UniqueFloatVars db db.frame := h_frame_wf.2
  have h_fr_nodup : FloatVarNoDup fr :=
    floatVarNoDup_of_uniqueFloatVars db db.frame fr
      (by simpa [db] using h_frame) h_frame_wf h_unique
  have h_fr_disjoint : Spec.FrameVarsDisjointConsts (toConsts db) fr :=
    frameVarsDisjointConsts_of_toFrame db db.frame fr
      (by simpa [db] using h_frame) h_frame_wf h_wf_scoped.2
  rcases parser_toDatabase_wellFormed_strong bytes h_success with
    ⟨Γ', h_db', h_wf_strong'⟩
  have h_Γ : Γ' = Γ := by
    have h_db'_eq : toDatabase db = some Γ' := by
      simpa [db] using h_db'
    have h_db_eq : toDatabase db = some Γ := by
      simpa [db] using h_db
    have h_some_eq : (some Γ' : Option Spec.Database) = some Γ :=
      h_db'_eq.symm.trans h_db_eq
    exact Option.some.inj h_some_eq
  have h_wf_strong : WellFormedDatabaseStrong Γ (toConsts db) := by
    simpa [h_Γ] using h_wf_strong'
  exact ⟨by simpa [db] using h_wf_strong, h_fr_nodup, by simpa [db] using h_fr_disjoint⟩

/-! ## Legacy Compatibility (Global Support Wrappers)

The next wrappers intentionally preserve the old public API shape that
requires a global support premise:
- `parser_operational_iff_semantic(_total)`
- `verify_parser_acceptance_iff_semantic_provable_total`
- `verify_parser_acceptance_any_mode_iff_semantic_provable_total`

New code should prefer the supported-first and unconditional-soundness APIs:
- completeness: `parser_supported_semantic_to_operational(_total)` and
  `verify_parser_acceptance_*_iff_supported_semantic_provable_total`
- soundness: `parser_operational_to_semantic(_total)` and
  `verify_parser_acceptance*_implies_semantic_provable_total`
- operational-to-supported bridge:
  `parser_operational_to_supported(_total)` -/

/-- Legacy parser-specialized operational/semantic equivalence.

For a successful `checkBytes` run, any extracted `(Γ, fr)` witness satisfies the
exact premises required by `operational_iff_semantic`, so users only provide:
- parse success (`h_success`)
- extraction witnesses (`h_db`, `h_frame`)

`WellFormedDatabaseStrong`, `FloatVarNoDup`, and
`FrameVarsDisjointConsts` are discharged from parser success; callers still
provide the global semantic-frame support bridge premise.

Prefer `parser_operational_to_semantic(_total)` for soundness and
`parser_supported_semantic_to_operational(_total)` for completeness. -/
theorem parser_operational_iff_semantic
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_supported : SemanticFrameSupported Γ fr) :
    Spec.Provable Γ fr e ↔
      Spec.Semantic.Provable
        (dbToAxioms Γ)
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  obtain ⟨h_wf_strong, h_fr_nodup, h_fr_disjoint⟩ :=
    parser_structural_premises bytes h_success Γ fr h_db h_frame
  exact
    (operational_iff_semantic
      (Γ := Γ) (consts := toConsts (Verify.checkBytes bytes)) (fr := fr) (e := e)
      h_wf_strong h_fr_nodup h_fr_disjoint h_supported)

/-- Legacy parser-specialized operational/semantic equivalence with total DB extraction.

This removes the obsolete `h_db : toDatabase ... = some Γ` premise from call
sites by fixing `Γ := toDatabaseTotal (checkBytes bytes)`, but it still
requires global support.

Prefer `parser_operational_to_semantic_total` and
`parser_supported_semantic_to_operational_total`. -/
theorem parser_operational_iff_semantic_total
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_supported : SemanticFrameSupported (toDatabaseTotal (Verify.checkBytes bytes)) fr) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e ↔
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  exact parser_operational_iff_semantic bytes h_success
    (toDatabaseTotal (Verify.checkBytes bytes)) fr e
    (by simp [Metamath.Kernel.toDatabase]) h_frame h_supported

/-- Parser-specialized completeness from derivation-local semantic support.

This avoids the global `SemanticFrameSupported` assumption: callers provide a
`SupportedProvable` witness for the target formula instead. -/
theorem parser_supported_semantic_to_operational
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_supported_sem :
      SupportedProvable Γ fr (exprToFormula (varMapOfFrame fr) e)) :
    Spec.Provable Γ fr e := by
  obtain ⟨h_wf_strong, h_fr_nodup, h_fr_disjoint⟩ :=
    parser_structural_premises bytes h_success Γ fr h_db h_frame
  exact
    (mario_to_proofValid
      (Γ := Γ) (consts := toConsts (Verify.checkBytes bytes)) (fr := fr) (e := e)
      h_wf_strong h_fr_nodup h_fr_disjoint h_supported_sem)

/-- Total-DB specialization of
`parser_supported_semantic_to_operational`. -/
theorem parser_supported_semantic_to_operational_total
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_supported_sem :
      SupportedProvable (toDatabaseTotal (Verify.checkBytes bytes)) fr
        (exprToFormula (varMapOfFrame fr) e)) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e := by
  exact parser_supported_semantic_to_operational bytes h_success
    (toDatabaseTotal (Verify.checkBytes bytes)) fr e
    (by simp [Metamath.Kernel.toDatabase]) h_frame h_supported_sem

/-- Parser-specialized unconditional soundness (no global support premise). -/
theorem parser_operational_to_semantic
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable Γ fr e →
      Spec.Semantic.Provable
        (dbToAxioms Γ)
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  have h_struct := parser_structural_premises bytes h_success Γ fr h_db h_frame
  have h_wf_strong : WellFormedDatabaseStrong Γ (toConsts (Verify.checkBytes bytes)) := h_struct.1
  have h_fr_disjoint : Spec.FrameVarsDisjointConsts (toConsts (Verify.checkBytes bytes)) fr := h_struct.2.2
  intro h_prov
  exact operational_to_semantic (Γ := Γ) (consts := toConsts (Verify.checkBytes bytes)) (fr := fr) (e := e)
    h_wf_strong h_fr_disjoint h_prov

/-- Total-DB specialization of `parser_operational_to_semantic`. -/
theorem parser_operational_to_semantic_total
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e →
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  exact parser_operational_to_semantic bytes h_success
    (toDatabaseTotal (Verify.checkBytes bytes)) fr e
    (by simp [Metamath.Kernel.toDatabase]) h_frame

/-- Parser-specialized bridge from operational provability to derivation-local
support (no global support premise). -/
theorem parser_operational_to_supported
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable Γ fr e →
      SupportedProvable Γ fr (exprToFormula (varMapOfFrame fr) e) := by
  have h_struct := parser_structural_premises bytes h_success Γ fr h_db h_frame
  have h_wf_strong : WellFormedDatabaseStrong Γ (toConsts (Verify.checkBytes bytes)) := h_struct.1
  have h_fr_disjoint : Spec.FrameVarsDisjointConsts (toConsts (Verify.checkBytes bytes)) fr := h_struct.2.2
  intro h_prov
  exact operational_to_supported (Γ := Γ) (consts := toConsts (Verify.checkBytes bytes)) (fr := fr) (e := e)
    h_wf_strong h_fr_disjoint h_prov

/-- Total-DB specialization of `parser_operational_to_supported`. -/
theorem parser_operational_to_supported_total
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e →
      SupportedProvable (toDatabaseTotal (Verify.checkBytes bytes)) fr
        (exprToFormula (varMapOfFrame fr) e) := by
  exact parser_operational_to_supported bytes h_success
    (toDatabaseTotal (Verify.checkBytes bytes)) fr e
    (by simp [Metamath.Kernel.toDatabase]) h_frame

/-! ## Acceptance wrappers to semantic provability (total DB extraction) -/

/-- Parser success turns the existing Spec-level existential witness into a
semantic witness over `toDatabaseTotal`, and conversely. -/
private theorem parser_spec_exists_iff_semantic_total_exists
    (bytes : ByteArray)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (h_supported : ∀ fr : Spec.Frame,
      SemanticFrameSupported (toDatabaseTotal (Verify.checkBytes bytes)) fr) :
    (∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (Verify.checkBytes bytes) = some Γ ∧
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Provable Γ fr (toExpr f))
    ↔
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) := by
  constructor
  · intro h
    rcases h with ⟨Γ, fr, h_db, h_frame, h_prov⟩
    have h_db_total : toDatabaseTotal (Verify.checkBytes bytes) = Γ := by
      apply Option.some.inj
      simpa [Metamath.Kernel.toDatabase] using h_db
    have h_Γ_total : Γ = toDatabaseTotal (Verify.checkBytes bytes) := h_db_total.symm
    have h_prov_total :
        Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr (toExpr f) := by
      simpa [h_Γ_total] using h_prov
    have h_sem :
        Spec.Semantic.Provable
      (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
      (frameToContext fr)
      (exprToFormula (varMapOfFrame fr) (toExpr f)) :=
      (parser_operational_iff_semantic_total bytes h_success fr (toExpr f) h_frame
        (h_supported fr)).1 h_prov_total
    exact ⟨fr, h_frame, h_sem⟩
  · intro h
    rcases h with ⟨fr, h_frame, h_sem⟩
    have h_prov_total :
        Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr (toExpr f) :=
      (parser_operational_iff_semantic_total bytes h_success fr (toExpr f) h_frame
        (h_supported fr)).2 h_sem
    exact ⟨toDatabaseTotal (Verify.checkBytes bytes), fr,
      by simp [Metamath.Kernel.toDatabase], h_frame, by simpa using h_prov_total⟩

/-- Legacy compatibility wrapper: normal-mode parser acceptance is equivalent
to canonical semantic provability, using `toDatabaseTotal` as the canonical DB
extraction (requires global support bridge). -/
theorem verify_parser_acceptance_iff_semantic_provable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (h_supported : ∀ fr : Spec.Frame,
      SemanticFrameSupported (toDatabaseTotal (Verify.checkBytes bytes)) fr) :
    (∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[], Verify.ProofTokenParser.normal⟩ =
          Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f)
    ↔
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :=
  (verify_parser_acceptance_iff_spec_provable bytes label f h_success).trans
    (parser_spec_exists_iff_semantic_total_exists bytes f h_success h_supported)

/-- Legacy compatibility wrapper: any-mode parser acceptance (normal ∨ compressed)
is equivalent to canonical semantic provability, using `toDatabaseTotal` as the
canonical DB extraction (requires global support bridge). -/
theorem verify_parser_acceptance_any_mode_iff_semantic_provable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (h_supported : ∀ fr : Spec.Frame,
      SemanticFrameSupported (toDatabaseTotal (Verify.checkBytes bytes)) fr) :
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
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :=
    (verify_parser_acceptance_any_mode_iff_spec_provable bytes label f h_success).trans
    (parser_spec_exists_iff_semantic_total_exists bytes f h_success h_supported)

/-- Parser success turns the Spec-level existential witness into a semantic
witness over `toDatabaseTotal` without any global support premise. -/
private theorem parser_spec_exists_implies_semantic_total_exists
    (bytes : ByteArray)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    (∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (Verify.checkBytes bytes) = some Γ ∧
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Provable Γ fr (toExpr f))
    →
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) := by
  intro h
  rcases h with ⟨Γ, fr, h_db, h_frame, h_prov⟩
  have h_db_total : toDatabaseTotal (Verify.checkBytes bytes) = Γ := by
    apply Option.some.inj
    simpa [Metamath.Kernel.toDatabase] using h_db
  have h_Γ_total : Γ = toDatabaseTotal (Verify.checkBytes bytes) := h_db_total.symm
  have h_prov_total :
      Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr (toExpr f) := by
    simpa [h_Γ_total] using h_prov
  have h_sem :
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f)) :=
    parser_operational_to_semantic_total bytes h_success fr (toExpr f) h_frame h_prov_total
  exact ⟨fr, h_frame, h_sem⟩

/-- Parser success turns the existing Spec-level existential witness into a
supported-semantic witness over `toDatabaseTotal`, and conversely.

This removes manual construction of `SupportedProvable` from parser/spec
witnesses and does not require global support. -/
private theorem parser_spec_exists_iff_supported_total_exists
    (bytes : ByteArray)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    (∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase (Verify.checkBytes bytes) = some Γ ∧
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Provable Γ fr (toExpr f))
    ↔
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      SupportedProvable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f))) := by
  constructor
  · intro h
    rcases h with ⟨Γ, fr, h_db, h_frame, h_prov⟩
    have h_db_total : toDatabaseTotal (Verify.checkBytes bytes) = Γ := by
      apply Option.some.inj
      simpa [Metamath.Kernel.toDatabase] using h_db
    have h_Γ_total : Γ = toDatabaseTotal (Verify.checkBytes bytes) := h_db_total.symm
    have h_prov_total :
        Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr (toExpr f) := by
      simpa [h_Γ_total] using h_prov
    have h_sup :
        SupportedProvable (toDatabaseTotal (Verify.checkBytes bytes)) fr
          (exprToFormula (varMapOfFrame fr) (toExpr f)) :=
      parser_operational_to_supported_total bytes h_success fr (toExpr f) h_frame h_prov_total
    exact ⟨fr, h_frame, h_sup⟩
  · intro h
    rcases h with ⟨fr, h_frame, h_sup⟩
    have h_prov_total :
        Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr (toExpr f) :=
      parser_supported_semantic_to_operational_total bytes h_success fr (toExpr f) h_frame h_sup
    exact ⟨toDatabaseTotal (Verify.checkBytes bytes), fr,
      by simp [Metamath.Kernel.toDatabase], h_frame, by simpa using h_prov_total⟩

/-- Normal-mode parser acceptance implies canonical semantic provability over
`toDatabaseTotal` (unconditional soundness, no global support premise). -/
theorem verify_parser_acceptance_implies_semantic_provable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    (∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[], Verify.ProofTokenParser.normal⟩ =
          Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f)
    →
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) := by
  intro h_accept
  have h_spec :
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase (Verify.checkBytes bytes) = some Γ ∧
        toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
        Spec.Provable Γ fr (toExpr f) :=
    (verify_parser_acceptance_iff_spec_provable bytes label f h_success).1 h_accept
  exact parser_spec_exists_implies_semantic_total_exists bytes f h_success h_spec

/-- Any-mode parser acceptance implies canonical semantic provability over
`toDatabaseTotal` (unconditional soundness, no global support premise). -/
theorem verify_parser_acceptance_any_mode_implies_semantic_provable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
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
    →
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Semantic.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) := by
  intro h_accept
  have h_spec :
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase (Verify.checkBytes bytes) = some Γ ∧
        toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
        Spec.Provable Γ fr (toExpr f) :=
    (verify_parser_acceptance_any_mode_iff_spec_provable bytes label f h_success).1 h_accept
  exact parser_spec_exists_implies_semantic_total_exists bytes f h_success h_spec

/-- Normal-mode parser acceptance is equivalent to derivation-local supported
semantic provability over `toDatabaseTotal` (no global support premise). -/
theorem verify_parser_acceptance_iff_supported_semantic_provable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    (∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[], Verify.ProofTokenParser.normal⟩ =
          Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f)
    ↔
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      SupportedProvable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :=
  (verify_parser_acceptance_iff_spec_provable bytes label f h_success).trans
    (parser_spec_exists_iff_supported_total_exists bytes f h_success)

/-- Any-mode parser acceptance is equivalent to derivation-local supported
semantic provability over `toDatabaseTotal` (no global support premise). -/
theorem verify_parser_acceptance_any_mode_iff_supported_semantic_provable_total
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
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
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      SupportedProvable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :=
    (verify_parser_acceptance_any_mode_iff_spec_provable bytes label f h_success).trans
    (parser_spec_exists_iff_supported_total_exists bytes f h_success)

end Metamath.ParserEquivalence
