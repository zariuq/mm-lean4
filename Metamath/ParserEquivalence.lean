/-
ParserEquivalence — Canonical API Surface

This module collects the results about proof runs in a parsed database and their bridges to
Mario Carneiro's semantics. The acceptance theorems are downstream of it: import
`Metamath.CheckerCompleteness` for acceptance at a parser state and `Metamath.SourceCompleteness`
for source text and complete files.
For compact usage patterns, see `Metamath/ParserEquivalenceExamples.lean`.

**Main results (no project-declared axioms, no sorries):**

Proof runs (expression level):
1. `proofChecker_normal_acceptance_iff_specProvable_in_parsedDB` — a normal-mode run to a one-element stack with the expression `toExpr f` ↔ `Spec.Provable`
2. `proofChecker_anyFormat_acceptance_iff_specProvable_in_parsedDB` — the same for normal or compressed runs
3. `normalFoldSucceeds_iff_specProvable`, `anyFormatFoldSucceeds_iff_specProvable` — the same at any well-formed database state, in its active frame
4. `ProofReachableZ_iff_NormalProofReachable` — reachability in any proof format is normal reachability
5. `proofReachableZ_of_spec_provable` — an any-format witness (a normal proof) from spec provability
6. `toExpr_eq_implies_formula_eq` — strict formula equality upgrade
7. `normal_trace_sound`, `compressed_trace_sound` — token-trace soundness

These are statements about proof runs, not acceptance: `finishProof` compares the final stack
with the claim literally, which the expression `toExpr` cannot see. Acceptance is stated in
`CheckerCompleteness.acceptedWithDummies_iff_statementProvable` (at a parser state between
statements) and in `SourceCompleteness.statementProvable_iff_sourceAccepts` and
`SourceCompleteness.statementProvable_iff_fileAccepts` (for source text and complete files).

Mario Carneiro's declarative semantics:
8. `statementProvable_of_anyFormatFoldSucceeds` (`Metamath/CheckerCompleteness.lean`) — a proof run at a database state whose active frame is an extended frame of `fr` → the stored statement `(fr, f)` is declaratively provable
9. `acceptedWithDummies_iff_statementProvable` (`Metamath/CheckerCompleteness.lean`) — at a parser state between statements, a `$p` claim's stored statement is declaratively provable iff the parser accepts a proof of it after declaring fresh dummy variables
10. `proofChecker_normal_iff_frameDerivable_in_parsedDB`, `proofChecker_anyFormat_iff_frameDerivable_in_parsedDB` — proof runs ↔ derivability by Mario's rules in the frame (`FrameDerivable`)
11. `proofChecker_normal_implies_declarative_provable_in_parsedDB`, `proofChecker_anyFormat_implies_declarative_provable_in_parsedDB` — proof runs → Mario's `Provable` in the frame context
12. `parser_frameDerivable_to_operational(_total)`, `parser_operational_to_frameDerivable(_total)`, `parser_operational_to_declarative(_total)` — parser-specialized bridges
-/

import Metamath.ParserAnyFormatEquivalence

/-!
## Theorem Map: Trust Chain Layers

### Layer 1 — Proof runs
- `proofChecker_normal_acceptance_iff_specProvable_in_parsedDB` (KernelCorrectness.lean):
  normal-mode `foldlM stepNormal` in the parsed database ↔ `Spec.Provable`.
- `proofChecker_anyFormat_acceptance_iff_specProvable_in_parsedDB` (ParserAnyFormatEquivalence.lean):
  (normal `foldlM` ∨ `ProofReachableZ`) ↔ `Spec.Provable`.
- `normalFoldSucceeds_iff_specProvable`, `anyFormatFoldSucceeds_iff_specProvable` (this file):
  the same at any well-formed database state, e.g. the one at a `$p` statement.
- `proofChecker_normal_iff_frameDerivable_in_parsedDB`,
  `proofChecker_anyFormat_iff_frameDerivable_in_parsedDB` (this file):
  proof runs ↔ `FrameDerivable` over `toDatabaseTotal`.
- `proofChecker_normal_implies_declarative_provable_in_parsedDB`,
  `proofChecker_anyFormat_implies_declarative_provable_in_parsedDB` (this file):
  proof runs → Mario's `Provable` in the frame context over `toDatabaseTotal`.

### Layer 2 — Token-trace soundness (parser execution → Spec.Provable)
- `normal_trace_sound`: `feedProof` token stream in normal mode → `Spec.Provable`
- `compressed_trace_sound`: 4-phase `feedProof` ("(" → preload → ")" → body) → `Spec.Provable`

Both use ParserState-level DB (`finishProof` insertion-time), NOT final `checkBytes` DB.
These prove that actual parser execution implies correctness — no abstract reachability.

### Layer 3 — Mode bridge (token-trace → DB-level reachability)
- `compressed_full_bridge` (PrefixProvenance.lean):
  Parser compressed execution → `ProofReachableZ` (from pure DB operations)
- `ProofReachableZ_iff_NormalProofReachable` (ParserAnyFormatEquivalence.lean):
  reachability in any format ↔ `NormalProofReachable`, under `WellFormedDB` and a one-element
  stack holding `fmla`
- `compressed_acceptance_implies_normal_acceptance` (ParserAnyFormatEquivalence.lean):
  Any `ProofReachableZ` → ∃ `stepNormal` fold (same form as normal biconditional LHS)

### Layer 4 — Spec equivalence
- `operational_to_frameDerivable`, `frameDerivable_to_proofValid` (Spec/Equivalence.lean):
  at one frame, `Spec.Provable` ↔ `FrameDerivable`.
- `operational_to_declarative` (Spec/Equivalence.lean):
  `Spec.Provable` → Mario's `Provable` in the frame context.
- `statementProvable_iff_exists_extendedFrame` (Spec/Completeness.lean):
  a stored statement is provable in Mario's statement-level semantics iff some
  extended frame (Metamath book §4.2.7) has a `Spec.Provable` proof.
  `originalStatementProvable_iff_exists_extendedFrame`: the same for Mario's
  original `ax` rule.
- `Spec/FixedFrameCounterexample.lean`: at one fixed frame the two differ, both
  for lack of a dummy variable and for lack of an optional `$d` statement.
- `acceptedWithDummies_iff_statementProvable` (CheckerCompleteness.lean): the
  declarative semantics against the parser's acceptance at a state between statements.
- `statementProvable_iff_sourceAccepts`, `statementProvable_iff_fileAccepts`
  (SourceCompleteness.lean): the same for the source text the parser reads after a prefix,
  and for the complete file `checkBytes` checks.

### Layer 5 — checkBytes-level event-lift (PrefixProvability.Checker)
- `checkBytesCore_prefix_provable` (PrefixProvability/Checker.lean):
  successful `checkBytesCore` run implies all feed/feedAll finishProof events are prefix-provable
- `checkBytes_prefix_provable` (PrefixProvability/Checker.lean):
  lifts event-lift theorem to `checkBytes`
- `checkBytes_feedEvents_prefix_provable` (PrefixProvability/Checker.lean):
  the fold-wide statement — every finish-proof event anywhere in the feed loop is
  provable in the database as it stood at that event (pre-insertion)
- `checkBytes_finalState_finishProofEvent_prefix_provable` (PrefixProvability/Checker.lean):
  narrow eliminator for a `FinishProofEvent` at the final `feedAll` state only

### How the layers connect
- Layer 1 biconditionals relate proof runs in a parsed database to `Spec.Provable` at the
  level of expressions. Normal branch: explicit `foldlM stepNormal`. Compressed branch:
  `ProofReachableZ`. Acceptance of source text is `SourceCompleteness.statementProvable_iff_sourceAccepts`.
- `ProofReachableZ` is NOT assumed — it IS proven from token execution (Layer 3).
- Layer 2 trace theorems are strictly additional: they show the parser's actual
  `feedProof` token-by-token execution implies `Spec.Provable` with zero abstract
  reachability hypotheses.
- Layer 5 closes the parser-loop integration for finishProof events on successful
  `checkBytes` runs, giving explicit pre-insert provability at those events.

### Recommended theorem call order
1. Frame completeness: provide `FrameDerivable ... (exprToFormula ... (toExpr f))`,
   then call `parser_frameDerivable_to_operational_total`, or use
   `proofChecker_normal_iff_frameDerivable_in_parsedDB`.
2. Soundness to Mario's semantics: from proof-run witnesses, call
   `proofChecker_normal_implies_declarative_provable_in_parsedDB`
   (or the any-format analogue); for a stored statement, call
   `CheckerCompleteness.statementProvable_of_anyFormatFoldSucceeds`.
3. Completeness for Mario's semantics:
   `CheckerCompleteness.acceptedWithDummies_iff_statementProvable`, and for source text
   `SourceCompleteness.statementProvable_iff_sourceAccepts`.

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

-- Re-export core theorems from KernelCorrectness and ParserAnyFormatEquivalence.
-- Users can access these via `open Metamath.ParserEquivalence`.
export Metamath.Kernel
  (toDatabase toDatabaseTotal toFrame toExpr
   proofChecker_normal_acceptance_iff_specProvable_in_parsedDB
   verify_parser_sound_of_impl_acceptance_equiv
   verify_parser_accepts_of_spec_provable
   parser_construction_wf_scoped)

export Metamath.ParserAnyFormatEquivalence
  (proofChecker_anyFormat_acceptance_iff_specProvable_in_parsedDB
   ProofReachableZ_iff_NormalProofReachable
   proofReachableZ_of_spec_provable
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
open Metamath.PrefixProvenance (NormalTokensOK normal_proof_provable_from_prefix
  feedProof_start_establishes_reachable NormalTokensOK_preserves_invariant
  ProofReachableZ)
open Metamath.PrefixTraceCompressed (PreloadTokensOK CompressedTokensOK
  NormalProofReachable_same_db_provable compressed_proof_prefix_provable)
open Metamath.ParserAnyFormatEquivalence (finishProof_success_stack_conditions
  compressed_proof_provable_from_prefix_tight)

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
  init : pr₀ = ⟨⟨0,0⟩, label, fmla, s.db.frame, #[], #[], .start, false⟩
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
  exact normal_proof_provable_from_prefix s tk₀ tokens pr₀ pr₁ pr_final
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
  compressed_proof_provable_from_prefix_tight s label fmla
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
  exact compressed_proof_prefix_provable s label fmla
    tk_open preload_toks tk_close comp_toks all_acts
    pr₀ pr₁ pr₂ pr₃ pr_final
    h_trace.init h_trace.open_ok h_trace.is_open h_trace.open_tokp
    h_trace.preload h_trace.close_ok h_trace.is_close h_trace.close_tokp
    h_trace.compressed h_trace.finish_ok h_s_ok h_wf
    h_stack_one h_stack_fmla

/-! ## Parser-specialized operational/declarative bridges

The bridges of `Spec.Equivalence` are generic by design. The wrappers below
specialize them to parser-origin databases and discharge all structural
premises from `checkBytes` success plus `toDatabase`/`toFrame` witnesses. -/

/-- Shared parser-origin structural premises used by all parser bridge theorems.

From `checkBytes` success plus extraction witnesses, we recover exactly the
proof obligations needed by the Spec/declarative bridge results:
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

/-- Parser-specialized completeness: a formula derivable by Mario's rules in
the frame (`FrameDerivable`) is operationally provable. -/
theorem parser_frameDerivable_to_operational
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_derivable :
      FrameDerivable Γ fr (exprToFormula (varMapOfFrame fr) e)) :
    Spec.Provable Γ fr e := by
  obtain ⟨h_wf_strong, h_fr_nodup, h_fr_disjoint⟩ :=
    parser_structural_premises bytes h_success Γ fr h_db h_frame
  exact
    (frameDerivable_to_proofValid
      (Γ := Γ) (consts := toConsts (Verify.checkBytes bytes)) (fr := fr) (e := e)
      h_wf_strong h_fr_nodup h_fr_disjoint h_derivable)

/-- Total-DB specialization of
`parser_frameDerivable_to_operational`. -/
theorem parser_frameDerivable_to_operational_total
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr)
    (h_derivable :
      FrameDerivable (toDatabaseTotal (Verify.checkBytes bytes)) fr
        (exprToFormula (varMapOfFrame fr) e)) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e := by
  exact parser_frameDerivable_to_operational bytes h_success
    (toDatabaseTotal (Verify.checkBytes bytes)) fr e
    (by simp [Metamath.Kernel.toDatabase]) h_frame h_derivable

/-- Parser-specialized soundness for Mario's `Provable` in the frame context. -/
theorem parser_operational_to_declarative
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable Γ fr e →
      Spec.Declarative.Provable
        (dbToAxioms Γ)
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  have h_struct := parser_structural_premises bytes h_success Γ fr h_db h_frame
  have h_wf_strong : WellFormedDatabaseStrong Γ (toConsts (Verify.checkBytes bytes)) := h_struct.1
  have h_fr_disjoint : Spec.FrameVarsDisjointConsts (toConsts (Verify.checkBytes bytes)) fr := h_struct.2.2
  intro h_prov
  exact operational_to_declarative (Γ := Γ) (consts := toConsts (Verify.checkBytes bytes)) (fr := fr) (e := e)
    h_wf_strong h_fr_disjoint h_prov

/-- Total-DB specialization of `parser_operational_to_declarative`. -/
theorem parser_operational_to_declarative_total
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e →
      Spec.Declarative.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) e) := by
  exact parser_operational_to_declarative bytes h_success
    (toDatabaseTotal (Verify.checkBytes bytes)) fr e
    (by simp [Metamath.Kernel.toDatabase]) h_frame

/-- Parser-specialized bridge from operational provability to frame
derivability. -/
theorem parser_operational_to_frameDerivable
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (Γ : Spec.Database)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_db : toDatabase (Verify.checkBytes bytes) = some Γ)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable Γ fr e →
      FrameDerivable Γ fr (exprToFormula (varMapOfFrame fr) e) := by
  have h_struct := parser_structural_premises bytes h_success Γ fr h_db h_frame
  have h_wf_strong : WellFormedDatabaseStrong Γ (toConsts (Verify.checkBytes bytes)) := h_struct.1
  have h_fr_disjoint : Spec.FrameVarsDisjointConsts (toConsts (Verify.checkBytes bytes)) fr := h_struct.2.2
  intro h_prov
  exact operational_to_frameDerivable (Γ := Γ) (consts := toConsts (Verify.checkBytes bytes)) (fr := fr) (e := e)
    h_wf_strong h_fr_disjoint h_prov

/-- Total-DB specialization of `parser_operational_to_frameDerivable`. -/
theorem parser_operational_to_frameDerivable_total
    (bytes : ByteArray)
    (h_success : (Verify.checkBytes bytes).error? = none)
    (fr : Spec.Frame)
    (e : Spec.Expr)
    (h_frame : toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr) :
    Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr e →
      FrameDerivable (toDatabaseTotal (Verify.checkBytes bytes)) fr
        (exprToFormula (varMapOfFrame fr) e) := by
  exact parser_operational_to_frameDerivable bytes h_success
    (toDatabaseTotal (Verify.checkBytes bytes)) fr e
    (by simp [Metamath.Kernel.toDatabase]) h_frame

/-! ## Acceptance wrappers to declarative provability (total DB extraction) -/

/-- Parser success turns the Spec-level existential witness into a declarative
witness over `toDatabaseTotal`. -/
private theorem parser_spec_exists_implies_declarative_total_exists
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
      Spec.Declarative.Provable
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
      Spec.Declarative.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f)) :=
    parser_operational_to_declarative_total bytes h_success fr (toExpr f) h_frame h_prov_total
  exact ⟨fr, h_frame, h_sem⟩

/-- Parser success turns the existing Spec-level existential witness into a
`FrameDerivable` witness over `toDatabaseTotal`, and conversely. -/
private theorem parser_spec_exists_iff_frameDerivable_total_exists
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
      FrameDerivable
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
        FrameDerivable (toDatabaseTotal (Verify.checkBytes bytes)) fr
          (exprToFormula (varMapOfFrame fr) (toExpr f)) :=
      parser_operational_to_frameDerivable_total bytes h_success fr (toExpr f) h_frame h_prov_total
    exact ⟨fr, h_frame, h_sup⟩
  · intro h
    rcases h with ⟨fr, h_frame, h_sup⟩
    have h_prov_total :
        Spec.Provable (toDatabaseTotal (Verify.checkBytes bytes)) fr (toExpr f) :=
      parser_frameDerivable_to_operational_total bytes h_success fr (toExpr f) h_frame h_sup
    exact ⟨toDatabaseTotal (Verify.checkBytes bytes), fr,
      by simp [Metamath.Kernel.toDatabase], h_frame, by simpa using h_prov_total⟩

/-- A normal-mode proof run implies Mario's declarative provability in the frame context over
`toDatabaseTotal`. -/
theorem proofChecker_normal_implies_declarative_provable_in_parsedDB
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    (∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[], Verify.ProofTokenParser.normal, false⟩ =
          Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f)
    →
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      Spec.Declarative.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) := by
  intro h_accept
  have h_spec :
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase (Verify.checkBytes bytes) = some Γ ∧
        toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
        Spec.Provable Γ fr (toExpr f) :=
    (proofChecker_normal_acceptance_iff_specProvable_in_parsedDB bytes label f h_success).1 h_accept
  exact parser_spec_exists_implies_declarative_total_exists bytes f h_success h_spec

/-- A proof run in either mode implies Mario's declarative provability in the frame context over
`toDatabaseTotal`. -/
theorem proofChecker_anyFormat_implies_declarative_provable_in_parsedDB
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    ((∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
         Verify.ProofTokenParser.normal, false⟩ = Except.ok pr_final ∧
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
      Spec.Declarative.Provable
        (dbToAxioms (toDatabaseTotal (Verify.checkBytes bytes)))
        (frameToContext fr)
        (exprToFormula (varMapOfFrame fr) (toExpr f))) := by
  intro h_accept
  have h_spec :
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase (Verify.checkBytes bytes) = some Γ ∧
        toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
        Spec.Provable Γ fr (toExpr f) :=
    (proofChecker_anyFormat_acceptance_iff_specProvable_in_parsedDB bytes label f h_success).1 h_accept
  exact parser_spec_exists_implies_declarative_total_exists bytes f h_success h_spec

/-- A normal-mode proof run exists iff the expression is derivable by Mario's rules in the frame
(`FrameDerivable`) over `toDatabaseTotal`. -/
theorem proofChecker_normal_iff_frameDerivable_in_parsedDB
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    (∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[], Verify.ProofTokenParser.normal, false⟩ =
          Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f' ∧
      toExpr f' = toExpr f)
    ↔
    (∃ (fr : Spec.Frame),
      toFrame (Verify.checkBytes bytes) (Verify.checkBytes bytes).frame = some fr ∧
      FrameDerivable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :=
  (proofChecker_normal_acceptance_iff_specProvable_in_parsedDB bytes label f h_success).trans
    (parser_spec_exists_iff_frameDerivable_total_exists bytes f h_success)

/-- A proof run in either mode exists iff the expression is derivable by Mario's rules in the frame
(`FrameDerivable`) over `toDatabaseTotal`. -/
theorem proofChecker_anyFormat_iff_frameDerivable_in_parsedDB
    (bytes : ByteArray)
    (label : String)
    (f : Verify.Formula)
    (h_success : (Verify.checkBytes bytes).error? = none) :
    ((∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
      proof.foldlM (fun pr step => Verify.DB.stepNormal (Verify.checkBytes bytes) pr step)
        ⟨⟨0, 0⟩, label, f, (Verify.checkBytes bytes).frame, #[], #[],
         Verify.ProofTokenParser.normal, false⟩ = Except.ok pr_final ∧
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
      FrameDerivable
        (toDatabaseTotal (Verify.checkBytes bytes))
        fr
        (exprToFormula (varMapOfFrame fr) (toExpr f))) :=
    (proofChecker_anyFormat_acceptance_iff_specProvable_in_parsedDB bytes label f h_success).trans
    (parser_spec_exists_iff_frameDerivable_total_exists bytes f h_success)

/-! ## Proof runs at a database state

The theorems above run a proof against the database left at the end of
parsing. A `$p` statement is checked in the database state at that statement,
whose active frame may declare dummy variables. The following results hold at
any well-formed database state. They concern the run of the proof steps, whose
final formula has the expression of the claim; acceptance by `finishProof`,
which compares formulas literally, is `CheckerCompleteness.ProofAccepted`. -/

/-- A normal-mode proof run in the active frame of database state `db` ends
with one formula, whose expression is that of `f`. -/
def NormalFoldSucceeds (db : Verify.DB) (label : String) (f : Verify.Formula) : Prop :=
  ∃ (proof : Array String) (pr_final : Verify.ProofState) (f' : Verify.Formula),
    proof.foldlM (fun pr step => Verify.DB.stepNormal db pr step)
      ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], Verify.ProofTokenParser.normal, false⟩ =
        Except.ok pr_final ∧
    pr_final.stack.size = 1 ∧ pr_final.stack[0]? = some f' ∧ toExpr f' = toExpr f

/-- A normal or compressed proof run in the active frame of database state `db`
ends with one formula, whose expression is that of `f`. -/
def AnyFormatFoldSucceeds (db : Verify.DB) (label : String) (f : Verify.Formula) : Prop :=
  NormalFoldSucceeds db label f ∨
    ∃ (stack : Array Verify.Formula) (f' : Verify.Formula),
      ProofReachableZ db label f' stack ∧ stack.size = 1 ∧ stack[0]? = some f' ∧
        toExpr f' = toExpr f

/-- A successful run at a well-formed database state proves the claim in its
active frame. -/
theorem specProvable_of_normalFoldSucceeds
    (db : Verify.DB) (label : String) (f : Verify.Formula)
    (Γ : Spec.Database) (fr : Spec.Frame)
    (h_success : db.error? = none) (h_wf : WellFormedDB db)
    (h_db : toDatabase db = some Γ) (h_frame : toFrame db db.frame = some fr)
    (h_accept : NormalFoldSucceeds db label f) :
    Spec.Provable Γ fr (toExpr f) := by
  obtain ⟨proof, pr_final, f', h_fold, h_size, h_stack, h_eq⟩ := h_accept
  obtain ⟨Γ', fr', h_db', h_frame', h_prov⟩ :=
    Kernel.verify_impl_sound_declarative db label f pr_final f' proof h_success h_wf
      h_fold h_size h_stack
  rw [h_db] at h_db'
  rw [h_frame] at h_frame'
  cases h_db'
  cases h_frame'
  rw [← h_eq]
  exact h_prov

/-- **Proof runs at a database state.** At a well-formed, well-scoped database
state, a normal-mode proof run ends with the expression of `f` iff `f` is
provable in the active frame. -/
theorem normalFoldSucceeds_iff_specProvable
    (db : Verify.DB) (label : String) (f : Verify.Formula)
    (Γ : Spec.Database) (fr : Spec.Frame)
    (h_success : db.error? = none) (h_wf : WellFormedDB db) (h_scoped : WellScopedDB db)
    (h_db : toDatabase db = some Γ) (h_frame : toFrame db db.frame = some fr)
    (h_dv : ∀ l fr' e, Γ l = some (fr', e) → DVWellFormed fr') :
    NormalFoldSucceeds db label f ↔ Spec.Provable Γ fr (toExpr f) :=
  ⟨specProvable_of_normalFoldSucceeds db label f Γ fr h_success h_wf h_db h_frame,
    Kernel.verify_impl_complete db label f h_success h_wf
      (Kernel.completenessScopedFacts_of_wellScopedDB db h_scoped) Γ fr h_db h_frame h_dv⟩

/-- A successful normal or compressed run at a well-formed database state proves
the claim in its active frame. -/
theorem specProvable_of_anyFormatFoldSucceeds
    (db : Verify.DB) (label : String) (f : Verify.Formula)
    (Γ : Spec.Database) (fr : Spec.Frame)
    (h_success : db.error? = none) (h_wf : WellFormedDB db)
    (h_db : toDatabase db = some Γ) (h_frame : toFrame db db.frame = some fr)
    (h_accept : AnyFormatFoldSucceeds db label f) :
    Spec.Provable Γ fr (toExpr f) := by
  rcases h_accept with h_normal | ⟨stack, f', h_reach, h_size, h_fmla, h_eq⟩
  · exact specProvable_of_normalFoldSucceeds db label f Γ fr h_success h_wf h_db h_frame
      h_normal
  · have h_prov := specProvable_of_normalFoldSucceeds db label f' Γ fr h_success h_wf h_db
      h_frame (ParserAnyFormatEquivalence.compressed_acceptance_implies_normal_acceptance
        db label f' stack h_reach h_wf h_size h_fmla)
    rw [← h_eq]
    exact h_prov

/-- Any-format version of `normalFoldSucceeds_iff_specProvable`. -/
theorem anyFormatFoldSucceeds_iff_specProvable
    (db : Verify.DB) (label : String) (f : Verify.Formula)
    (Γ : Spec.Database) (fr : Spec.Frame)
    (h_success : db.error? = none) (h_wf : WellFormedDB db) (h_scoped : WellScopedDB db)
    (h_db : toDatabase db = some Γ) (h_frame : toFrame db db.frame = some fr)
    (h_dv : ∀ l fr' e, Γ l = some (fr', e) → DVWellFormed fr') :
    AnyFormatFoldSucceeds db label f ↔ Spec.Provable Γ fr (toExpr f) :=
  ⟨specProvable_of_anyFormatFoldSucceeds db label f Γ fr h_success h_wf h_db h_frame,
    fun h_prov => Or.inl ((normalFoldSucceeds_iff_specProvable db label f Γ fr h_success h_wf
      h_scoped h_db h_frame h_dv).mpr h_prov)⟩

end Metamath.ParserEquivalence
