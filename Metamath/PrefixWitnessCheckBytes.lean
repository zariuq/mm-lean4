/-
PrefixWitnessCheckBytes — Ghost Invariant for Insertion-Time Prefix Provability

This module establishes a ghost invariant `ProofGhost` that tracks
`NormalProofReachable` during proof execution, and proves that at every
`finishProof` event, the proved formula is `Spec.Provable` in the
**pre-insertion** database (`toDatabase s.db`).

**Main results (all sorry-free):**
- `finishProof_normal_prefix_provable`: Per-event normal-mode prefix provability
- `finishProof_any_mode_prefix_provable`: Per-event any-mode prefix provability
- `feedToken_proof_maintains_ghost`: Ghost propagation through proof-mode feedToken

**Architecture**: `ProofGhost` tracks `NormalProofReachable` within proof mode.
It is maintained through all proof-mode `feedToken` calls (Phase 2b, complete).
The payoff: when `finishProof` succeeds and the ghost holds, the formula is
`Spec.Provable (toDatabase s.db)` — provable in the pre-insert database.

## Operational frame gap and stored-statement boundary

Proof checking uses `db.frame`, the full active scope frame, rather than the
trimmed mandatory frame stored in `pr.frame`. This is required for proof-local
dummy variables and eliminates the former `pr.frame = db.frame` assumption
from the operational chain. It does not by itself certify the exact trimmed
statement stored at `pr.frame`; that is a separate statement-level bridge.

Key changes:
- `stepAssert` (Verify.lean): DV checking uses `db.frame` not `pr.frame`
- `ProofStateInv` (KernelClean.lean): uses `db.frame` for frame_ok/frame_wf
- `stepNormal_transfer` (PrefixProvenance.lean): no longer needs frame equality
- `NormalProofReachable_step`: no longer needs `h_frame : pr.frame = db.frame`
- `ProofGhost`: no longer requires `pr.frame = db.frame`
-/

import Metamath.ParserEquivalence
import Metamath.VerifyParserStateThms
import Metamath.VerifyConformanceThms

set_option autoImplicit false

namespace Metamath.PrefixWitnessCheckBytes

open Metamath.Verify
open Metamath.WF (WellFormedDB)
open Metamath.Kernel (toDatabase toFrame toExpr
  stepProof_preserves_frame_heap stepAssert_preserves_frame_heap)
open Metamath.PrefixProvenance (NormalProofReachable ProofReachableZ
  ZCompressedProofReachable StepSaveAction execStepSave
  feedProof_start_establishes_reachable feedProof_normal_maintains_reachable
  stepNormal_preserves_ptp stepAssert_transfer preload_preserves_stack)
open Metamath.PrefixTraceCompressed (NormalProofReachable_same_db_provable
  ProofReachableZ_same_db_provable
  feedProof_success_go_ok go_start_open_extracts
  go_preload_close_extracts go_preload_label_extracts go_compressed_extracts
  preload_preserves_ptp preload_preserves_label)
open Metamath.ParserOps (ParserStateInv TokpInv feedProof_success_db
  feedProof_success_tokpInv_core finishProof_tokp_start
  updateLine_tokp feedToken_maintains_stateInv withAt_success_eq)
open Metamath.ParserLoopInduction (ParserState_mkErrorFromEvidence_sets_error
  ParserState_requestInclude_sets_error withAt_preserves_error)
open Metamath.ParserAnyModeEquivalence (finishProof_success_stack_conditions)
open Metamath.ParserOps (preloadMandatoryHyps_ok_preserves_core
  preload_ok_preserves_core applyCompressedActions_ok_preserves_core)

/-! ## trimFrame hyps subset

The output of `trimFrame'` filters `db.frame.hyps`, so its hyps are a subset. -/

/-- Elements of `trimFrameHyps` output come from the input array. -/
private theorem trimFrameHyps_mem (db : DB) (vars : Std.HashSet String) (hyps : Array String) :
    ∀ s, s ∈ (DB.trimFrameHyps db vars hyps).toList → s ∈ hyps.toList := by
  intro s h_mem
  simp [DB.trimFrameHyps, DB.trimFrameHypsPairs, DB.trimFrameHypsPairsList] at h_mem
  obtain ⟨⟨idx, h_in⟩, _⟩ := h_mem
  have h_map : s ∈ List.map Prod.fst (hyps.toList.zipIdx) :=
    List.mem_map.mpr ⟨(s, idx), h_in, rfl⟩
  rwa [List.zipIdx_map_fst] at h_map

/-- `trimFrame'` output hyps ⊆ `db.frame.hyps`. -/
private theorem trimFrame'_hyps_subset (db : DB) (fmla : Verify.Formula) (fr : Frame)
    (h_ok : db.trimFrame' fmla = .ok fr) :
    ∀ lbl ∈ fr.hyps.toList, lbl ∈ db.frame.hyps.toList := by
  intro lbl h_mem
  have h_eq : fr = (db.trimFrame fmla).2 := by
    unfold DB.trimFrame' at h_ok
    generalize db.trimFrame fmla = result at h_ok
    obtain ⟨ok, fr'⟩ := result
    simp at h_ok
    split at h_ok
    · exact (Except.ok.inj h_ok).symm
    · exact absurd h_ok (by nofun)
  have ⟨vars, h_hyps⟩ : ∃ vars, (db.trimFrame fmla).2.hyps = DB.trimFrameHyps db vars db.frame.hyps := by
    unfold DB.trimFrame; simp only [Id.run]; exact ⟨_, rfl⟩
  rw [h_eq] at h_mem
  exact trimFrameHyps_mem db vars db.frame.hyps lbl (h_hyps ▸ h_mem)

/-! ## ProofGhost: Ghost invariant for proof-mode execution

Tracks `NormalProofReachable` during normal-mode proof execution and initial
conditions during start mode. For compressed proofs, tracks `PreloadPhaseGhost`
during preload phase and `CompressedFoldGhost` during compressed action phase.
During comment mode (`$( ... $)`), the ghost is preserved through the
`.comment (.proof pr)` wrapper since comments don't modify the database or
proof state.

**Split design**: preload and compressed phases use separate predicates because
the preload extension requires knowledge that no actions have been applied yet
(extending the preload list changes the heap that action folds start from).
The `heap₀` parameter captures the heap state after mandatory preloading,
avoiding the need to bridge `preloadMandatoryHyps` to `DB.preload` folds. -/

/-- Preload phase ghost: tracks mandatory preload + user preloads.
    During preload phase, only the heap grows; stack remains `#[]`.

    Crucially, this stores the mandatory-preload witness explicitly, so it can be
    carried into compressed mode without reconstruction. -/
private def PreloadPhaseGhost (db : DB) (pr : ProofState) : Prop :=
  ∃ (preloads : List String)
    (pr_start pr_mand pr_preload : ProofState),
    pr_start.label = pr.label ∧
    pr_start.fmla = pr.fmla ∧
    pr_start.frame = pr.frame ∧
    pr_start.stack = #[] ∧
    pr_start.heap = #[] ∧
    pr_start.ptp = .start ∧
    (∀ lbl ∈ pr_start.frame.hyps.toList, lbl ∈ db.frame.hyps.toList) ∧
    db.preloadMandatoryHyps pr_start = .ok pr_mand ∧
    preloads.foldlM (DB.preload db) pr_mand = .ok pr_preload ∧
    pr_preload.stack = pr.stack ∧
    pr_preload.heap = pr.heap

/-- Compressed action phase ghost: extends preload phase with step/save actions.
    Tracking heap is essential because `stepProof` reads `heap[n]?` and
    `save` appends stack top to heap — composing fold segments requires both
    stack and heap to match.

    Like `PreloadPhaseGhost`, this retains the mandatory-preload witness. -/
private def CompressedFoldGhost (db : DB) (pr : ProofState) : Prop :=
  ∃ (preloads : List String) (actions : List StepSaveAction)
    (pr_start pr_mand pr_preload pr_fold : ProofState),
    pr_start.label = pr.label ∧
    pr_start.fmla = pr.fmla ∧
    pr_start.frame = pr.frame ∧
    pr_start.stack = #[] ∧
    pr_start.heap = #[] ∧
    pr_start.ptp = .start ∧
    (∀ lbl ∈ pr_start.frame.hyps.toList, lbl ∈ db.frame.hyps.toList) ∧
    db.preloadMandatoryHyps pr_start = .ok pr_mand ∧
    preloads.foldlM (DB.preload db) pr_mand = .ok pr_preload ∧
    actions.foldlM (fun p a => execStepSave db p a) pr_preload = .ok pr_fold ∧
    pr_fold.stack = pr.stack ∧
    pr_fold.heap = pr.heap

/-- Core ghost condition for a proof state against a database.
    Tracks reachability across ALL proof modes:
    - `.start`: stack and heap are empty (proof hasn't begun)
    - `.normal`: `NormalProofReachable` (normal proof fold produces current stack)
    - `.preload`: `PreloadPhaseGhost` (mandatory + individual preloads, no actions)
    - `.compressed n`: `CompressedFoldGhost` (preloads + step/save actions) -/
private def proofGhostCore (db : DB) (pr : ProofState) : Prop :=
  db.trimFrame' pr.fmla = .ok pr.frame ∧
  (pr.ptp = .start → pr.stack = #[] ∧ pr.heap = #[] ∧
    ∀ lbl ∈ pr.frame.hyps.toList, lbl ∈ db.frame.hyps.toList) ∧
  (pr.ptp = .normal →
    NormalProofReachable db pr.label pr.fmla pr.stack) ∧
  (pr.ptp = .preload → PreloadPhaseGhost db pr) ∧
  ((∃ n, pr.ptp = .compressed n) → CompressedFoldGhost db pr)

/-- Ghost invariant for proof-mode execution.
    - `.proof pr`: core ghost conditions for `pr`
    - `.comment inner`: recursively tracks ghost through comment nesting
    - `.includePath resume _` and `.includeClose resume _ _`: recursively
      track the suspended mode through include administration
    - Other modes: trivially `True`

    The recursive clauses make comment and include administration transparent
    to the ghost.

    In strict mode (`rejectUnknownSteps = true`), this ghost is maintained
    through the entire feed loop when combined with `ParserStateInv`. -/
def ProofGhost (db : DB) : TokenParser → Prop
  | .proof pr => proofGhostCore db pr
  | .comment inner => ProofGhost db inner
  | .includePath resume _ => ProofGhost db resume
  | .includeClose resume _ _ => ProofGhost db resume
  | _ => True

/-- Consuming an include request preserves the proof-execution ghost carried
by the restored parser continuation. -/
theorem clearIncludeRequest_requestInclude_maintains_proofGhost
    (s : ParserState) (resume : TokenParser) (includePath : String)
    (h_ghost : ProofGhost s.db resume)
    (h_errorFree : s.db.error? = none) :
    ProofGhost
      (clearIncludeRequest (s.requestInclude resume includePath)).db
      (clearIncludeRequest (s.requestInclude resume includePath)).tokp := by
  have h_state :
      clearIncludeRequest (s.requestInclude resume includePath) =
        { s with tokp := resume } := by
    cases s with
    | mk db tokp charp line linepos sourceFile =>
        simp only [ParserState.requestInclude, clearIncludeRequest]
        congr
        exact h_errorFree.symm
  rw [h_state]
  exact h_ghost

/-! ## Per-event prefix provability

The payoff theorems: when `finishProof` succeeds (triggered by "$." token in
proof mode), and we have `NormalProofReachable` (or `ProofReachableZ`) plus
`WellFormedDB`, the proved formula is `Spec.Provable` in the pre-insert database.

These theorems work at the `finishProof` level. The connection to `feedToken`
(which has an outer "$(" comment check before dispatching to `finishProof`)
is handled in the ghost propagation layer. -/

/-- At a `finishProof` event in **normal mode**, the proved formula is
    `Spec.Provable` in the pre-insertion database (`toDatabase s.db`). -/
theorem finishProof_normal_prefix_provable
    (s : ParserState) (pr : ProofState)
    (_h_normal : pr.ptp = .normal)
    (h_reach : NormalProofReachable s.db pr.label pr.fmla pr.stack)
    (h_wf : WellFormedDB s.db)
    (h_no_err : s.db.error? = none)
    (h_success : (s.finishProof pr).db.error? = none) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase s.db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr.fmla) := by
  have ⟨h_stack_one, h_stack_fmla, _⟩ :=
    finishProof_success_stack_conditions s pr h_success
  exact NormalProofReachable_same_db_provable s.db pr.label pr.fmla pr.stack
    h_reach h_no_err h_wf h_stack_one h_stack_fmla

/-- At a `finishProof` event in **any mode**, the proved formula is
    `Spec.Provable` in the pre-insertion database (`toDatabase s.db`). -/
theorem finishProof_any_mode_prefix_provable
    (s : ParserState) (pr : ProofState)
    (h_reach : ProofReachableZ s.db pr.label pr.fmla pr.stack)
    (h_wf : WellFormedDB s.db)
    (h_no_err : s.db.error? = none)
    (h_success : (s.finishProof pr).db.error? = none) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase s.db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr.fmla) := by
  have ⟨h_stack_one, h_stack_fmla, _⟩ :=
    finishProof_success_stack_conditions s pr h_success
  exact ProofReachableZ_same_db_provable s.db pr.label pr.fmla pr.stack
    h_reach h_no_err h_wf h_stack_one h_stack_fmla

/-! ## Helper lemmas for ghost propagation

Infrastructure for `feedToken_proof_maintains_ghost`: ptp tracking through
feedProof and goNormal, strict-mode "?" rejection. -/

/-- `goNormal` preserves the `ptp` field: output ptp = input ptp.
    This is because `push` (for "?" path) and `stepNormal` (for label path)
    only modify the stack, not ptp. -/
private theorem goNormal_ok_preserves_ptp
    (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState)
    (h_ok : ParserState.feedProof.goNormal s tk pr = .ok pr') :
    pr'.ptp = pr.ptp := by
  unfold ParserState.feedProof.goNormal at h_ok
  by_cases h_q : tk.eqArray "?".toAscii
  · by_cases h_reject : s.db.config.rejectUnknownSteps
    · simp [h_q, h_reject] at h_ok
    · simp [h_q, h_reject, pure, Except.pure] at h_ok
      rw [← h_ok]; rfl
  · by_cases h_lbl : (toLabel tk).fst
    · have h_step : s.db.stepNormal pr (toLabel tk).snd = .ok pr' := by
        simpa [h_q, h_lbl] using h_ok
      exact stepNormal_preserves_ptp s.db pr pr' (toLabel tk).snd h_step
    · simp [h_q, h_lbl] at h_ok

/-- In proof mode, `feedProof` does not produce a `.start` ptp in the output.
    After feedProof, ptp is one of: .normal, .preload, .compressed n.
    This makes the ghost's `.start` clause vacuously true. -/
private theorem feedProof_ptp_not_start
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_success : (s.feedProof tk pr).db.error? = none) :
    ∀ pr_mid, (s.feedProof tk pr).tokp = .proof pr_mid →
      pr_mid.ptp ≠ .start := by
  obtain ⟨pr', h_go, h_tokp⟩ := feedProof_success_go_ok s tk pr h_success
  intro pr_mid h_eq
  rw [h_tokp] at h_eq
  have h_pr_eq := TokenParser.proof.inj h_eq; subst h_pr_eq
  -- Show pr'.ptp ≠ .start from go s tk pr = .ok pr'
  unfold ParserState.feedProof.go at h_go
  cases h_ptp : pr.ptp with
  | start =>
    by_cases h_open : tk.eqArray "(".toAscii
    · -- preloadMandatoryHyps → {mid with ptp := .preload}
      simp [h_ptp, h_open] at h_go
      cases h_pre : s.db.preloadMandatoryHyps pr with
      | error e => simp [h_pre, Functor.map, Except.map] at h_go
      | ok mid =>
        simp [h_pre, Functor.map, Except.map] at h_go
        subst h_go; nofun
    · -- goNormal { pr with ptp := .normal } → ptp = .normal
      simp [h_ptp, h_open] at h_go
      have h_ptp_eq := goNormal_ok_preserves_ptp s tk { pr with ptp := .normal } pr' h_go
      simp at h_ptp_eq
      rw [h_ptp_eq]; nofun
  | preload =>
    by_cases h_close : tk.eqArray ")".toAscii
    · -- → .compressed 0
      simp [h_ptp, h_close, pure, Except.pure] at h_go
      subst h_go; nofun
    · by_cases h_lbl_ok : (toLabel tk).fst
      · cases h_guard : s.db.explicitCompressedHeaderLabelCheck pr
            (toLabel tk).snd with
        | error err =>
            simp [h_ptp, h_close, h_lbl_ok, h_guard,
              bind, Except.bind] at h_go
        | ok value =>
          cases value
          have h_pre : s.db.preload pr (toLabel tk).snd = .ok pr' := by
            simpa [h_ptp, h_close, h_lbl_ok, h_guard,
              bind, Except.bind, pure, Except.pure] using h_go
          have h_ptp_eq := preload_preserves_ptp s.db pr pr' (toLabel tk).snd h_pre
          rw [h_ptp_eq, h_ptp]; nofun
      · simp [h_ptp, h_close, h_lbl_ok] at h_go
  | normal =>
    simp [h_ptp] at h_go
    have h_ptp_eq := goNormal_ok_preserves_ptp s tk pr pr' h_go
    rw [h_ptp_eq, h_ptp]; nofun
  | compressed chr =>
    simp [h_ptp] at h_go
    cases h_dec : ParserState.decodeCompressed tk chr s.db.config.compressedInvalidBytes
        s.db.config.compressedSavePlacement with
    | error e => simp [h_dec, bind, Except.bind] at h_go
    | ok dec =>
      obtain ⟨acts, chr'⟩ := dec
      simp [h_dec, bind, Except.bind] at h_go
      cases h_apply : ParserState.applyCompressedActions s.db pr acts with
      | error e => simp [h_apply, Functor.map, Except.map] at h_go
      | ok mid =>
        simp [h_apply, Functor.map, Except.map] at h_go
        subst h_go; nofun

/-- When the input ptp is `.preload` or `.compressed n`, feedProof output ptp
    is NOT `.normal`. The compressed proof pipeline stays in compressed mode. -/
private theorem feedProof_compressed_pipeline_not_normal
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_success : (s.feedProof tk pr).db.error? = none)
    (h_not_start : pr.ptp ≠ .start) (h_not_normal : pr.ptp ≠ .normal) :
    ∀ pr_mid, (s.feedProof tk pr).tokp = .proof pr_mid →
      pr_mid.ptp ≠ .normal := by
  obtain ⟨pr', h_go, h_tokp⟩ := feedProof_success_go_ok s tk pr h_success
  intro pr_mid h_eq
  rw [h_tokp] at h_eq
  have h_pr_eq := TokenParser.proof.inj h_eq; subst h_pr_eq
  unfold ParserState.feedProof.go at h_go
  cases h_ptp : pr.ptp with
  | start => exact absurd h_ptp h_not_start
  | normal => exact absurd h_ptp h_not_normal
  | preload =>
    by_cases h_close : tk.eqArray ")".toAscii
    · simp [h_ptp, h_close, pure, Except.pure] at h_go
      subst h_go; nofun
    · by_cases h_lbl_ok : (toLabel tk).fst
      · cases h_guard : s.db.explicitCompressedHeaderLabelCheck pr
            (toLabel tk).snd with
        | error err =>
            simp [h_ptp, h_close, h_lbl_ok, h_guard,
              bind, Except.bind] at h_go
        | ok value =>
          cases value
          have h_pre : s.db.preload pr (toLabel tk).snd = .ok pr' := by
            simpa [h_ptp, h_close, h_lbl_ok, h_guard,
              bind, Except.bind, pure, Except.pure] using h_go
          have h_ptp_eq := preload_preserves_ptp s.db pr pr' (toLabel tk).snd h_pre
          rw [h_ptp_eq, h_ptp]; nofun
      · simp [h_ptp, h_close, h_lbl_ok] at h_go
  | compressed chr =>
    simp [h_ptp] at h_go
    cases h_dec : ParserState.decodeCompressed tk chr s.db.config.compressedInvalidBytes
        s.db.config.compressedSavePlacement with
    | error e => simp [h_dec, bind, Except.bind] at h_go
    | ok dec =>
      obtain ⟨acts, chr'⟩ := dec
      simp [h_dec, bind, Except.bind] at h_go
      cases h_apply : ParserState.applyCompressedActions s.db pr acts with
      | error e => simp [h_apply, Functor.map, Except.map] at h_go
      | ok mid =>
        simp [h_apply, Functor.map, Except.map] at h_go
        subst h_go; nofun

/-- In proof mode with `.start` or `.normal` ptp, `feedProof` with `?` token
    errors when `rejectUnknownSteps = true`.
    When ptp = .start, requires that the "(" path is not taken. -/
private theorem feedProof_q_strict_errors
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_q : tk.eqArray "?".toAscii)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_ptp : pr.ptp = .start ∨ pr.ptp = .normal)
    (h_route : pr.ptp = .start → ¬ tk.eqArray "(".toAscii) :
    (s.feedProof tk pr).db.error? ≠ none := by
  -- Proof by contradiction: assume feedProof succeeds → go = .ok → impossible
  intro h_ok
  obtain ⟨pr', h_go, _⟩ := feedProof_success_go_ok s tk pr h_ok
  -- go can't succeed: "?" with strict mode always throws in goNormal
  unfold ParserState.feedProof.go at h_go
  cases h_ptp with
  | inl h_start =>
    simp [h_start, h_route h_start] at h_go
    -- goal: goNormal s tk {pr with ptp := .normal} = .ok pr' → False
    unfold ParserState.feedProof.goNormal at h_go
    simp [h_q, h_strict] at h_go
  | inr h_normal =>
    simp [h_normal] at h_go
    unfold ParserState.feedProof.goNormal at h_go
    simp [h_q, h_strict] at h_go

/-! ## ProofGhost propagation: all token-parser modes

Phase 2c: extend ghost propagation from proof mode (feedToken_proof_maintains_ghost)
to all modes, then compose through feed/feedAll to get checkBytes-level coverage. -/

/-- `proofGhostCore` holds for any `mkProofState` output, because
    `mkProofState` sets `ptp = .start`, `stack = #[]`, `heap = #[]`, making
    all mode-specific conjuncts vacuously true (ptp = .start ≠ .normal/etc.).
    Used when proof mode is entered from `.math .thm` via `resumeThm`. -/
private theorem proofGhostCore_of_mkProofState (db db' : DB) (pos : Pos) (l : String)
    (fmla : Verify.Formula) (fr : Verify.Frame)
    (h_trim : db.trimFrame' fmla = .ok fr)
    (h_scope : ∀ lbl ∈ fr.hyps.toList, lbl ∈ db.frame.hyps.toList) :
    proofGhostCore db (db'.mkProofState pos l fmla fr) := by
  refine ⟨by simpa [DB.mkProofState, Id.run] using h_trim, ?_, ?_, ?_, ?_⟩
  · intro _; exact ⟨by simp [DB.mkProofState, Id.run],
                     by simp [DB.mkProofState, Id.run],
                     by simpa [DB.mkProofState, Id.run] using h_scope⟩
  · simp [DB.mkProofState, Id.run]
  · simp [DB.mkProofState, Id.run]
  · simp [DB.mkProofState, Id.run]

/-! ## PreloadPhaseGhost extension

Infrastructure for extending `PreloadPhaseGhost` when a new `DB.preload` step
succeeds. The key insight: `DB.preload` success depends only on `db` and the
label (not on the proof state), so if it succeeds on one state it succeeds on
any other. The `pushHeap` result depends on the pushed element (determined by
`db` and label) and the starting heap. -/

/-- `DB.preload` success replays on a proof state with matching heap.
    Since `DB.preload` depends only on `db.find?` and `db.frame` (not the proof
    state), success transfers and the output heaps match when inputs match. -/
private theorem DB_preload_replays
    (db : DB) (pr₁ pr₂ pr₁' : ProofState) (lbl : String)
    (h_ok : db.preload pr₁ lbl = .ok pr₁')
    (h_heap : pr₁.heap = pr₂.heap) :
    ∃ pr₂', db.preload pr₂ lbl = .ok pr₂' ∧
      pr₂'.stack = pr₂.stack ∧ pr₂'.heap = pr₁'.heap := by
  unfold DB.preload at h_ok
  cases h_find : db.find? lbl with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok
    cases obj with
    | const _ => exact absurd h_ok (by simp)
    | var _ => exact absurd h_ok (by simp)
    | hyp ess f _ =>
      by_cases h_scope : lbl ∈ db.frame.hyps.toList
      · simp only [h_scope, ↓reduceIte, pure, Except.pure] at h_ok
        have h_eq := Except.ok.inj h_ok; subst h_eq
        exact ⟨pr₂.pushHeap (.fmla f),
          by unfold DB.preload; simp [h_find, h_scope, pure, Except.pure],
          by simp [ProofState.pushHeap],
          by simp [ProofState.pushHeap, h_heap]⟩
      · exact absurd h_ok (by simp [h_scope])
    | assert f fr _ =>
      simp only [pure, Except.pure] at h_ok
      have h_eq := Except.ok.inj h_ok; subst h_eq
      exact ⟨pr₂.pushHeap (.assert f fr),
        by unfold DB.preload; simp [h_find, pure, Except.pure],
        by simp [ProofState.pushHeap],
        by simp [ProofState.pushHeap, h_heap]⟩

/-- `foldlM` over `++` decomposes into sequential folds for `DB.preload`. -/
private theorem foldlM_append_preload
    (db : DB) (pr : ProofState) (xs ys : List String) :
    (xs ++ ys).foldlM (DB.preload db) pr =
    (xs.foldlM (DB.preload db) pr) >>= (fun p =>
      ys.foldlM (DB.preload db) p) := by
  induction xs generalizing pr with
  | nil => simp [List.foldlM, pure, Except.pure, bind, Except.bind]
  | cons x rest ih =>
    simp only [List.foldlM, List.cons_append]
    cases db.preload pr x with
    | error e => simp [bind, Except.bind]
    | ok pr' => simp only [bind, Except.bind]; exact ih pr'

/-- Extend `PreloadPhaseGhost` with a new `DB.preload` step.
    Since `DB.preload` success depends only on `db` and label, the fold
    extends to the ghost's canonical state. Heap transfer uses the fact
    that both the ghost state and actual state have the same heap. -/
private theorem preloadPhaseGhost_extend
    (db : DB) (pr pr' : ProofState) (lbl : String)
    (h_ghost : PreloadPhaseGhost db pr)
    (h_preload : db.preload pr lbl = .ok pr')
    (h_label : pr'.label = pr.label) (h_fmla : pr'.fmla = pr.fmla)
    (h_frame : pr'.frame = pr.frame) :
    PreloadPhaseGhost db pr' := by
  obtain ⟨preloads, pr_start, pr_mand, pr_preload,
    h_start_lbl, h_start_fmla, h_start_frame, h_start_stack, h_start_heap, h_start_ptp,
    h_scope, h_mand, h_fold, h_stack_eq, h_heap_eq⟩ := h_ghost
  -- Replay: DB.preload succeeds on pr_preload too with matching heaps
  obtain ⟨pr_preload', h_ok₂, h_stack₂, h_heap₂⟩ :=
    DB_preload_replays db pr pr_preload pr' lbl h_preload h_heap_eq.symm
  -- Construct extended fold
  refine ⟨preloads ++ [lbl], pr_start, pr_mand, pr_preload', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_start_lbl.trans h_label.symm
  · exact h_start_fmla.trans h_fmla.symm
  · exact h_start_frame.trans h_frame.symm
  · exact h_start_stack
  · exact h_start_heap
  · exact h_start_ptp
  · exact h_scope
  · exact h_mand
  · -- (preloads ++ [lbl]).foldlM ... = .ok pr_preload'
    rw [foldlM_append_preload, h_fold]
    simp only [bind, Except.bind, List.foldlM, h_ok₂, pure, Except.pure]
  · -- pr_preload'.stack = pr'.stack
    -- preload preserves stack on both sides
    rw [h_stack₂, h_stack_eq, preload_preserves_stack db pr pr' lbl h_preload]
  · -- pr_preload'.heap = pr'.heap
    exact h_heap₂

/-! ## Bridge lemmas: CompressedAction ↔ StepSaveAction

The parser uses `applyCompressedActions` (operating on `CompressedAction`) while
`ZCompressedProofReachable` uses `execStepSave` (operating on `StepSaveAction`).
These lemmas bridge the two, enabling us to extend `ZCompressedProofReachable`
witnesses when new compressed actions are applied. -/

/-- Convert a `CompressedAction` (excluding `.unknown`) to `StepSaveAction`. -/
private def toStepSave : ParserState.CompressedAction → StepSaveAction
  | .step n => .step n
  | .save => .save
  | .unknown => .step 0  -- unreachable when unknown is excluded

/-- `applyCompressedActions` with no unknowns equals `foldlM execStepSave`
    after converting actions. -/
private theorem applyCompressedActions_eq_execStepSave_fold
    (db : DB) (pr : ProofState) (acts : List ParserState.CompressedAction)
    (h_no_unknown : ∀ a ∈ acts, a ≠ .unknown) :
    ParserState.applyCompressedActions db pr acts =
    (acts.map toStepSave).foldlM (fun p a => execStepSave db p a) pr := by
  induction acts generalizing pr with
  | nil => rfl
  | cons a rest ih =>
    have h_a : a ≠ .unknown := h_no_unknown a (List.mem_cons_self ..)
    have h_rest : ∀ a ∈ rest, a ≠ .unknown :=
      fun a' h => h_no_unknown a' (List.mem_cons_of_mem _ h)
    -- Unfold both sides one step
    simp only [ParserState.applyCompressedActions, List.foldlM, List.map]
    -- Case split on action type to match first-step results
    cases a with
    | step n =>
      -- Both sides: db.stepProof pr n, then fold rest
      simp only [toStepSave, execStepSave]
      cases db.stepProof pr n with
      | error e => rfl
      | ok pr' => exact ih pr' h_rest
    | save =>
      -- Both sides: match pr.save, then fold rest
      simp only [toStepSave, execStepSave]
      cases pr.save with
      | error e => rfl
      | ok pr' =>
        simp only [pure, Except.pure]
        exact ih pr' h_rest
    | unknown => exact absurd rfl h_a

/-- If strict mode rejects unknown steps, successful compressed action execution
    implies the action list contains no `.unknown`. -/
private theorem applyCompressedActions_ok_no_unknown
    (db : DB) (pr pr' : ProofState) (acts : List ParserState.CompressedAction)
    (h_strict : db.config.rejectUnknownSteps = true)
    (h_ok : ParserState.applyCompressedActions db pr acts = .ok pr') :
    ∀ a ∈ acts, a ≠ ParserState.CompressedAction.unknown := by
  induction acts generalizing pr with
  | nil =>
    intro a h_mem
    cases h_mem
  | cons act rest ih =>
    intro a h_mem
    simp only [ParserState.applyCompressedActions, List.foldlM] at h_ok
    cases act with
    | step n =>
      cases h_step : db.stepProof pr n with
      | error e =>
        simp [h_step, bind, Except.bind] at h_ok
      | ok pr_mid =>
        have h_rest :
            ParserState.applyCompressedActions db pr_mid rest = .ok pr' := by
          simpa [ParserState.applyCompressedActions, List.foldlM, h_step, bind, Except.bind] using h_ok
        have h_mem' : a = ParserState.CompressedAction.step n ∨ a ∈ rest := by
          simpa using h_mem
        cases h_mem' with
        | inl h_eq =>
          subst h_eq
          simp
        | inr h_tail =>
          exact ih pr_mid h_rest a h_tail
    | save =>
      cases h_save : pr.save with
      | error e =>
        simp [h_save, bind, Except.bind] at h_ok
      | ok pr_mid =>
        have h_rest :
            ParserState.applyCompressedActions db pr_mid rest = .ok pr' := by
          simp only [ParserState.applyCompressedActions, h_save, bind,
            Except.bind, pure, Except.pure] at h_ok ⊢
          exact h_ok
        have h_mem' : a = ParserState.CompressedAction.save ∨ a ∈ rest := by
          simpa using h_mem
        cases h_mem' with
        | inl h_eq =>
          subst h_eq
          simp
        | inr h_tail =>
          exact ih pr_mid h_rest a h_tail
    | unknown =>
      simp [h_strict, bind, Except.bind] at h_ok

/-- `foldlM` over `++` decomposes into sequential folds (for Except monad). -/
private theorem foldlM_append_execStepSave
    (db : DB) (pr : ProofState) (xs ys : List StepSaveAction) :
    (xs ++ ys).foldlM (fun p a => execStepSave db p a) pr =
    (xs.foldlM (fun p a => execStepSave db p a) pr) >>= (fun p =>
       ys.foldlM (fun p a => execStepSave db p a) p) := by
  induction xs generalizing pr with
  | nil => simp [List.foldlM, pure, Except.pure, bind, Except.bind]
  | cons x rest ih =>
    simp only [List.foldlM, List.cons_append]
    cases h : execStepSave db pr x with
    | error e => simp [bind, Except.bind]
    | ok pr' =>
      simp only [bind, Except.bind]
      exact ih pr'

/-- Per-step compatibility: if `pr1` and `pr2` agree on `stack` and `heap`,
    and `execStepSave db pr1 a` succeeds, then `execStepSave db pr2 a` also
    succeeds and the results agree on `stack` and `heap`.
    - `.step n` → `stepProof` reads `heap[n]?`, modifies only `stack`
    - `.save`   → `save` reads `stack.back?`, modifies only `heap` -/
private theorem execStepSave_stack_heap_compatible
    (db : DB) (pr1 pr2 pr1' : ProofState) (a : StepSaveAction)
    (h_stack : pr1.stack = pr2.stack) (h_heap : pr1.heap = pr2.heap)
    (h_ok : execStepSave db pr1 a = .ok pr1') :
    ∃ pr2', execStepSave db pr2 a = .ok pr2' ∧
      pr1'.stack = pr2'.stack ∧ pr1'.heap = pr2'.heap := by
  cases a with
  | step n =>
    simp only [execStepSave] at h_ok ⊢
    unfold DB.stepProof at h_ok
    rw [h_heap] at h_ok
    cases h_el : pr2.heap[n]? with
    | none => simp [h_el] at h_ok
    | some el =>
      simp only [h_el] at h_ok
      cases el with
      | fmla f =>
        simp only [pure, Except.pure] at h_ok
        have h_eq := Except.ok.inj h_ok; subst h_eq
        exact ⟨pr2.push f,
          by simp [DB.stepProof, h_el, pure, Except.pure],
          by simp [ProofState.push, h_stack],
          by simp [ProofState.push, h_heap]⟩
      | assert f_a fr_a =>
        obtain ⟨r₂, h_r₂, h_r₂_stack⟩ :=
          stepAssert_transfer db pr1 pr2 pr1' f_a fr_a h_stack h_ok
        exact ⟨r₂,
          by unfold DB.stepProof; simp [h_el]; exact h_r₂,
          h_r₂_stack.symm,
          by rw [(stepAssert_preserves_frame_heap db pr1 pr1' f_a fr_a h_ok).2,
                 (stepAssert_preserves_frame_heap db pr2 r₂ f_a fr_a h_r₂).2, h_heap]⟩
  | save =>
    simp only [execStepSave] at h_ok ⊢
    cases h_save : pr1.save with
    | error e => simp [h_save] at h_ok
    | ok pr1s =>
      simp only [h_save, pure, Except.pure] at h_ok
      have h_eq := Except.ok.inj h_ok; subst h_eq
      unfold ProofState.save at h_save
      cases h_back : pr1.stack.back? with
      | none => simp [h_back] at h_save
      | some f =>
        simp only [h_back, pure, Except.pure] at h_save
        have h_eq := Except.ok.inj h_save; subst h_eq
        have h_back2 : pr2.stack.back? = some f := by rw [← h_stack]; exact h_back
        refine ⟨pr2.pushHeap (.fmla f), ?_, ?_, ?_⟩
        · -- execStepSave db pr2 .save = .ok (pr2.pushHeap (.fmla f))
          simp only [ProofState.save, h_back2, pure, Except.pure]
        · -- Stack: pushHeap preserves stack
          show (pr1.pushHeap (HeapEl.fmla f)).stack = (pr2.pushHeap (HeapEl.fmla f)).stack
          simp only [ProofState.pushHeap]; exact h_stack
        · -- Heap: pushHeap with same input heap
          show (pr1.pushHeap (HeapEl.fmla f)).heap = (pr2.pushHeap (HeapEl.fmla f)).heap
          simp only [ProofState.pushHeap]; exact congrArg (·.push (HeapEl.fmla f)) h_heap

/-- Fold-level compatibility: if `pr1` and `pr2` agree on `stack` and `heap`,
    and folding `acts` from `pr1` succeeds, then folding from `pr2` also
    succeeds and results agree on `stack` and `heap`. -/
private theorem foldlM_execStepSave_compatible
    (db : DB) (pr1 pr2 pr1' : ProofState) (acts : List StepSaveAction)
    (h_stack : pr1.stack = pr2.stack) (h_heap : pr1.heap = pr2.heap)
    (h_ok : acts.foldlM (fun p a => execStepSave db p a) pr1 = .ok pr1') :
    ∃ pr2', acts.foldlM (fun p a => execStepSave db p a) pr2 = .ok pr2' ∧
      pr1'.stack = pr2'.stack ∧ pr1'.heap = pr2'.heap := by
  induction acts generalizing pr1 pr2 with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_ok; subst h_ok
    exact ⟨pr2, rfl, h_stack, h_heap⟩
  | cons a rest ih =>
    simp only [List.foldlM] at h_ok ⊢
    cases h1 : execStepSave db pr1 a with
    | error e => simp [h1, bind, Except.bind] at h_ok
    | ok pr1_mid =>
      simp only [h1, bind, Except.bind] at h_ok
      obtain ⟨pr2_mid, h2, h_s_mid, h_h_mid⟩ :=
        execStepSave_stack_heap_compatible db pr1 pr2 pr1_mid a h_stack h_heap h1
      obtain ⟨pr2_final, h_fold2, h_s_final, h_h_final⟩ :=
        ih pr1_mid pr2_mid h_s_mid h_h_mid h_ok
      exact ⟨pr2_final,
        by simp only [h2, bind, Except.bind]; exact h_fold2,
        h_s_final, h_h_final⟩

/-- Extend `CompressedFoldGhost` with new compressed actions.
    Since the fold state and actual state match on stack+heap,
    applying the same actions produces matching results. -/
private theorem compressedFoldGhost_extend
    (db : DB) (pr pr_mid : ProofState)
    (acts : List ParserState.CompressedAction)
    (h_ghost : CompressedFoldGhost db pr)
    (h_no_unknown : ∀ a ∈ acts, a ≠ .unknown)
    (h_apply : ParserState.applyCompressedActions db pr acts = .ok pr_mid)
    (h_label : pr_mid.label = pr.label) (h_fmla : pr_mid.fmla = pr.fmla) :
    CompressedFoldGhost db pr_mid := by
  -- Unfold goal to expose pr_mid.label/fmla/frame for rewriting
  unfold CompressedFoldGhost
  obtain ⟨preloads, old_actions, pr_start, pr_mand, pr_preload, pr_fold,
    h_start_lbl, h_start_fmla, h_start_frame, h_start_stack, h_start_heap, h_start_ptp,
    h_scope, h_mand, h_pre, h_old_fold, h_stack_eq, h_heap_eq⟩ := h_ghost
  -- Frame is preserved by applyCompressedActions
  have h_core := applyCompressedActions_ok_preserves_core db pr pr_mid acts h_apply
  have h_frame := h_core.2
  -- Convert new CompressedActions to StepSaveActions via bridge
  have h_eq := applyCompressedActions_eq_execStepSave_fold db pr acts h_no_unknown
  rw [h_eq] at h_apply
  let new_sa := acts.map toStepSave
  -- The fold from pr_fold with new_sa succeeds (pr_fold has same stack+heap as pr)
  obtain ⟨pr_fold', h_fold', h_stack', h_heap'⟩ :=
    foldlM_execStepSave_compatible db pr pr_fold pr_mid new_sa
      h_stack_eq.symm h_heap_eq.symm h_apply
  -- The extended fold is old_actions ++ new_sa from pr_preload
  exact ⟨preloads, old_actions ++ new_sa, pr_start, pr_mand, pr_preload, pr_fold',
    h_start_lbl.trans h_label.symm,
    h_start_fmla.trans h_fmla.symm,
    h_start_frame.trans h_frame.symm,
    h_start_stack,
    h_start_heap,
    h_start_ptp,
    h_scope,
    h_mand,
    h_pre,
    by rw [foldlM_append_execStepSave, h_old_fold]; simp only [bind, Except.bind]; exact h_fold',
    h_stack'.symm, h_heap'.symm⟩

/-! ## Compressed Ghost -> Reachability Bridge -/

/-- Replay `preloadMandatoryHyps` from a state with matching frame/heap.
    The loop only reads `db.find?` and `frame.hyps`, and only updates heap. -/
private theorem preloadMandatoryHyps_replays
    (db : DB) (pr₁ pr₂ pr₁' : ProofState)
    (h_ok : db.preloadMandatoryHyps pr₁ = .ok pr₁')
    (h_frame : pr₁.frame = pr₂.frame)
    (h_heap : pr₁.heap = pr₂.heap) :
    ∃ pr₂', db.preloadMandatoryHyps pr₂ = .ok pr₂' ∧
      pr₂'.stack = pr₂.stack ∧ pr₂'.heap = pr₁'.heap := by
  let body : String → ProofState → Except ProofCheckFail (ForInStep ProofState) :=
    fun lbl acc =>
      match db.find? lbl with
      | some (.hyp _ f _) => pure (.yield (acc.pushHeap (.fmla f)))
      | _ => throw (.proofCheck (.mandatoryHypothesisNotFoundInDatabase lbl))
  have h_for₁ : forIn pr₁.frame.hyps pr₁ body = Except.ok pr₁' := by
    unfold DB.preloadMandatoryHyps at h_ok
    simp only [body]
    simp only [bind_pure] at h_ok
    exact h_ok
  have h_for₁_list : forIn pr₁.frame.hyps.toList pr₁ body = Except.ok pr₁' := by
    calc
      forIn pr₁.frame.hyps.toList pr₁ body = forIn pr₁.frame.hyps pr₁ body := by
        exact (Array.forIn_toList (xs := pr₁.frame.hyps) (b := pr₁) (f := body))
      _ = Except.ok pr₁' := h_for₁
  have h_aux :
      ∀ (labels : List String) (acc₁ acc₂ acc₁' : ProofState),
        forIn labels acc₁ body = Except.ok acc₁' →
        acc₁.heap = acc₂.heap →
        ∃ acc₂', forIn labels acc₂ body = Except.ok acc₂' ∧
          acc₂'.stack = acc₂.stack ∧ acc₂'.heap = acc₁'.heap := by
    intro labels
    induction labels with
    | nil =>
      intro acc₁ acc₂ acc₁' h_for h_heap_eq
      simp [List.forIn_nil, pure, Except.pure] at h_for
      subst h_for
      exact ⟨acc₂, by simp [List.forIn_nil, pure, Except.pure], rfl, h_heap_eq.symm⟩
    | cons lbl rest ih =>
      intro acc₁ acc₂ acc₁' h_for h_heap_eq
      simp [List.forIn_cons, body] at h_for ⊢
      cases h_find : db.find? lbl with
      | none =>
        simp [h_find, Bind.bind, Except.bind] at h_for
      | some obj =>
        cases obj with
        | const _ =>
          simp [h_find, Bind.bind, Except.bind] at h_for
        | var _ =>
          simp [h_find, Bind.bind, Except.bind] at h_for
        | assert _ _ _ =>
          simp [h_find, Bind.bind, Except.bind] at h_for
        | hyp ess f origin =>
          have h_tail₁ : forIn rest (acc₁.pushHeap (.fmla f)) body = .ok acc₁' := by
            simp only [h_find, pure, Except.pure, bind, Except.bind, body] at h_for ⊢
            exact h_for
          have h_push_eq : (acc₁.pushHeap (.fmla f)).heap = (acc₂.pushHeap (.fmla f)).heap := by
            simp [ProofState.pushHeap, h_heap_eq]
          obtain ⟨acc₂', h_tail₂, h_stack₂, h_heap₂⟩ :=
            ih (acc₁.pushHeap (.fmla f)) (acc₂.pushHeap (.fmla f)) acc₁' h_tail₁ h_push_eq
          refine ⟨acc₂', ?_, ?_, h_heap₂⟩
          · simp only [pure, Except.pure, bind, Except.bind, body] at h_tail₂ ⊢
            exact h_tail₂
          · rw [h_stack₂]
            simp [ProofState.pushHeap]
  obtain ⟨pr₂', h_for₂_list, h_stack₂, h_heap₂⟩ :=
    h_aux pr₁.frame.hyps.toList pr₁ pr₂ pr₁' h_for₁_list h_heap
  have h_for₂ : forIn pr₂.frame.hyps pr₂ body = Except.ok pr₂' := by
    calc
      forIn pr₂.frame.hyps pr₂ body = forIn pr₂.frame.hyps.toList pr₂ body := by
        exact (Array.forIn_toList (xs := pr₂.frame.hyps) (b := pr₂) (f := body)).symm
      _ = forIn pr₁.frame.hyps.toList pr₂ body := by rw [h_frame]
      _ = Except.ok pr₂' := h_for₂_list
  refine ⟨pr₂', ?_, h_stack₂, h_heap₂⟩
  unfold DB.preloadMandatoryHyps
  simp only [bind_pure]
  simp only [body] at h_for₂
  exact h_for₂

/-- Replay a successful preload fold from a state with matching heap. -/
private theorem foldlM_preload_replays
    (db : DB) (labels : List String) (pr₁ pr₂ pr₁' : ProofState)
    (h_fold : labels.foldlM (DB.preload db) pr₁ = .ok pr₁')
    (h_heap : pr₁.heap = pr₂.heap) :
    ∃ pr₂', labels.foldlM (DB.preload db) pr₂ = .ok pr₂' ∧
      pr₂'.stack = pr₂.stack ∧ pr₂'.heap = pr₁'.heap := by
  induction labels generalizing pr₁ pr₂ with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_fold
    subst h_fold
    exact ⟨pr₂, rfl, rfl, h_heap.symm⟩
  | cons lbl rest ih =>
    simp only [List.foldlM] at h_fold ⊢
    cases h_pre : DB.preload db pr₁ lbl with
    | error e =>
      simp [h_pre, bind, Except.bind] at h_fold
    | ok pr₁mid =>
      simp [h_pre, bind, Except.bind] at h_fold
      obtain ⟨pr₂mid, h_pre₂, h_stack_mid, h_heap_mid⟩ :=
        DB_preload_replays db pr₁ pr₂ pr₁mid lbl h_pre h_heap
      obtain ⟨pr₂', h_fold₂, h_stack₂, h_heap₂⟩ :=
        ih pr₁mid pr₂mid h_fold h_heap_mid.symm
      exact ⟨pr₂', by simp [h_pre₂, bind, Except.bind, h_fold₂], h_stack₂.trans h_stack_mid, h_heap₂⟩

/-- Encode step/save actions as parser compressed actions (no unknowns). -/
private def stepSaveToCompressed : StepSaveAction → ParserState.CompressedAction
  | .step n => .step n
  | .save => .save

/-- Round-trip map: `StepSaveAction -> CompressedAction -> StepSaveAction`. -/
private theorem map_toStepSave_stepSaveToCompressed (acts : List StepSaveAction) :
    (acts.map stepSaveToCompressed).map toStepSave = acts := by
  induction acts with
  | nil => rfl
  | cons a rest ih =>
    cases a <;> simp [stepSaveToCompressed, toStepSave, ih]

/-- Bridge: `preloadMandatoryHyps` success + scope → `DB.preload` fold over same
    labels from a canonical state (with `db.frame`) produces matching heap. -/
private theorem preloadMandatoryHyps_to_preload_fold
    (db : DB) (pr_start pr_mand : ProofState)
    (h_mand : db.preloadMandatoryHyps pr_start = .ok pr_mand)
    (h_heap_empty : pr_start.heap = #[])
    (h_scope : ∀ lbl ∈ pr_start.frame.hyps.toList, lbl ∈ db.frame.hyps.toList)
    (canonical : ProofState)
    (h_can_heap : canonical.heap = #[]) :
    ∃ pr_result,
      pr_start.frame.hyps.toList.foldlM (DB.preload db) canonical = .ok pr_result ∧
      pr_result.heap = pr_mand.heap ∧
      pr_result.stack = canonical.stack := by
  let body : String → ProofState → Except ProofCheckFail (ForInStep ProofState) :=
    fun lbl acc =>
      match db.find? lbl with
      | some (.hyp _ f _) => pure (.yield (acc.pushHeap (.fmla f)))
      | _ => throw (.proofCheck (.mandatoryHypothesisNotFoundInDatabase lbl))
  have h_for_list : forIn pr_start.frame.hyps.toList pr_start body = Except.ok pr_mand := by
    have h_for₁ : forIn pr_start.frame.hyps pr_start body = Except.ok pr_mand := by
      unfold DB.preloadMandatoryHyps at h_mand
      simp only [body]
      simp only [bind_pure] at h_mand
      exact h_mand
    rwa [Array.forIn_toList]
  suffices ∀ (labels : List String) (acc₁ acc₂ acc₁' : ProofState),
      forIn labels acc₁ body = Except.ok acc₁' →
      acc₁.heap = acc₂.heap →
      (∀ lbl ∈ labels, lbl ∈ db.frame.hyps.toList) →
      ∃ acc₂', labels.foldlM (DB.preload db) acc₂ = .ok acc₂' ∧
        acc₂'.heap = acc₁'.heap ∧ acc₂'.stack = acc₂.stack by
    exact this pr_start.frame.hyps.toList pr_start canonical pr_mand
      h_for_list (by rw [h_heap_empty, h_can_heap]) h_scope
  intro labels
  induction labels with
  | nil =>
    intro acc₁ acc₂ acc₁' h_for h_heap h_scope'
    simp [List.forIn_nil, pure, Except.pure] at h_for; subst h_for
    exact ⟨acc₂, rfl, h_heap.symm, rfl⟩
  | cons lbl rest ih =>
    intro acc₁ acc₂ acc₁' h_for h_heap h_scope'
    simp [List.forIn_cons, body] at h_for
    have h_in_scope := h_scope' lbl (.head rest)
    cases h_find : db.find? lbl with
    | none => simp [h_find, Bind.bind, Except.bind] at h_for
    | some obj =>
      cases obj with
      | const _ => simp [h_find, Bind.bind, Except.bind] at h_for
      | var _ => simp [h_find, Bind.bind, Except.bind] at h_for
      | assert _ _ _ => simp [h_find, Bind.bind, Except.bind] at h_for
      | hyp ess f origin =>
        have h_tail : forIn rest (acc₁.pushHeap (.fmla f)) body = .ok acc₁' := by
          simp only [h_find, pure, Except.pure, bind, Except.bind, body] at h_for ⊢
          exact h_for
        have h_push_heap_eq : (acc₁.pushHeap (.fmla f)).heap =
            (acc₂.pushHeap (.fmla f)).heap := by
          simp [ProofState.pushHeap, h_heap]
        obtain ⟨acc₂', h_fold₂, h_heap₂, h_stack₂⟩ :=
          ih (acc₁.pushHeap (.fmla f)) (acc₂.pushHeap (.fmla f)) acc₁'
            h_tail h_push_heap_eq (fun l hl => h_scope' l (.tail lbl hl))
        refine ⟨acc₂', ?_, h_heap₂, ?_⟩
        · simp only [List.foldlM]
          simp [DB.preload, h_find, h_in_scope, pure, Except.pure, bind, Except.bind]
          exact h_fold₂
        · rw [h_stack₂]; simp [ProofState.pushHeap]

/-- Bridge theorem: compressed ghost witness gives `ProofReachableZ`.
    Scope condition extracted from ghost; no external `h_frame` needed. -/
theorem CompressedFoldGhost_to_ProofReachableZ
    (db : DB) (pr : ProofState)
    (h_ghost : CompressedFoldGhost db pr)
    (_h_wf : WellFormedDB db)
    (_h_stack_one : pr.stack.size = 1)
    (_h_stack_fmla : pr.stack[0]? = some pr.fmla) :
    ProofReachableZ db pr.label pr.fmla pr.stack := by
  obtain ⟨preloads, old_actions, pr_start, pr_mand, pr_preload, pr_fold,
    h_start_lbl, h_start_fmla, h_start_frame, h_start_stack, h_start_heap, h_start_ptp,
    h_scope, h_mand, h_pre, h_old_fold, h_stack_eq, h_heap_eq⟩ := h_ghost
  -- Canonical initial state (with db.frame, empty heap/stack)
  let pr_init : ProofState := ⟨⟨0,0⟩, pr.label, pr.fmla, db.frame, #[], #[], .normal, false⟩
  -- Step 1: Convert preloadMandatoryHyps to DB.preload fold from canonical state
  obtain ⟨pr_mand0, h_mand0_fold, h_mand0_heap, h_mand0_stack⟩ :=
    preloadMandatoryHyps_to_preload_fold db pr_start pr_mand
      h_mand h_start_heap h_scope pr_init (by simp [pr_init])
  -- Step 2: Replay user preloads from pr_mand0 (matching heap with pr_mand)
  obtain ⟨pr_preload0, h_pre0, h_pre0_stack, h_pre0_heap⟩ :=
    foldlM_preload_replays db preloads pr_mand pr_mand0 pr_preload h_pre h_mand0_heap.symm
  -- Step 3: Combined preload fold = mandatory labels ++ user preloads
  let all_preloads := pr_start.frame.hyps.toList ++ preloads
  have h_combined : all_preloads.foldlM (DB.preload db) pr_init = .ok pr_preload0 := by
    rw [show all_preloads = pr_start.frame.hyps.toList ++ preloads from rfl,
        foldlM_append_preload, h_mand0_fold]
    simp only [bind, Except.bind]; exact h_pre0
  -- Step 4: Replay action fold from pr_preload to pr_preload0
  have h_mand_stack : pr_mand.stack = pr_start.stack :=
    Metamath.PrefixProvenance.preloadMandatoryHyps_preserves_stack db pr_start pr_mand h_mand
  have h_pre_stack : pr_preload.stack = pr_mand.stack :=
    Metamath.PrefixProvenance.preload_fold_preserves_stack db preloads pr_mand pr_preload h_pre
  have h_preload_stack_eq : pr_preload.stack = pr_preload0.stack := by
    calc
      pr_preload.stack = pr_mand.stack := h_pre_stack
      _ = pr_start.stack := h_mand_stack
      _ = #[] := h_start_stack
      _ = pr_init.stack := by simp [pr_init]
      _ = pr_mand0.stack := h_mand0_stack.symm
      _ = pr_preload0.stack := h_pre0_stack.symm
  have h_preload_heap_eq : pr_preload.heap = pr_preload0.heap := h_pre0_heap.symm
  obtain ⟨pr_fold0, h_old_fold0, h_fold_stack_eq, _h_fold_heap_eq⟩ :=
    foldlM_execStepSave_compatible db pr_preload pr_preload0 pr_fold old_actions
      h_preload_stack_eq h_preload_heap_eq h_old_fold
  -- Step 5: Construct ZCompressedProofReachable directly
  have h_fold0_stack : pr_fold0.stack = pr.stack := by
    calc pr_fold0.stack = pr_fold.stack := h_fold_stack_eq.symm
      _ = pr.stack := h_stack_eq
  apply ProofReachableZ.zcompressed
  exact ⟨all_preloads, old_actions, pr_preload0, pr_fold0,
    h_combined, h_old_fold0, h_fold0_stack⟩

/-! ## Ghost propagation: proof mode

The core ghost propagation theorem for proof mode. When `s.tokp = .proof pr`,
`feedToken` either:
1. Enters comment mode (`$(`): ghost preserved (db unchanged, pr unchanged)
2. Finishes proof (`$.`): ghost becomes `True` (exits proof mode)
3. Runs `feedProof`: ghost maintained via reachability lemmas

Case 3 needs `rejectUnknownSteps = true` to ensure `?` tokens cause errors
(since `?` breaks `NormalProofReachable` by pushing `fmla` directly). -/

/-- Ghost propagation through `feedToken` in proof mode.

    When `s.tokp = .proof pr` and `feedToken` succeeds:
    - `$(`   → comment mode: ghost preserved (db, pr unchanged)
    - `$.`   → finishProof: ghost trivially `True` (exits proof mode)
    - other  → feedProof: ghost maintained via reachability lemmas

    Requires `rejectUnknownSteps = true` to rule out `?` tokens. -/
theorem feedToken_proof_maintains_ghost
    (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState)
    (h_tokp : s.tokp = .proof pr)
    (h_ghost : ProofGhost s.db s.tokp)
    (_h_no_err : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_success : (s.feedToken i tk).db.error? = none) :
    ProofGhost (s.feedToken i tk).db (s.feedToken i tk).tokp := by
  -- Rewrite ghost to use concrete proof state
  rw [h_tokp] at h_ghost
  change proofGhostCore s.db pr at h_ghost
  -- Case split: "$(" (comment), "$." (finishProof), or other (feedProof)
  by_cases h_open : tk.eqArray "$(".toAscii
  · -- Case 1: "$(" → enter comment mode, db unchanged
    have h_db_eq : (s.feedToken i tk).db = s.db := by
      simp [ParserState.feedToken, h_tokp, h_open]
    have h_tokp_eq : (s.feedToken i tk).tokp = .comment (.proof pr) := by
      simp [ParserState.feedToken, h_tokp, h_open]
    rw [h_db_eq, h_tokp_eq]
    exact h_ghost
  · -- Not "$("
    by_cases h_include : tk.eqArray "$[".toAscii
    · have h_gate_none :
        includeDirectiveViolation? s.db.config s.db.scopes.size true i = none := by
        cases h_gate : includeDirectiveViolation? s.db.config s.db.scopes.size true i with
        | none => rfl
        | some err =>
            have h_bad : (s.feedToken i tk).db.error? ≠ none := by
              simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate,
                ParserState.mkErrorFromEvidence, ParserState.withDB]
            exact (h_bad h_success).elim
      have h_tokp_result :
          (s.feedToken i tk).tokp = .includePath (.proof pr) (s.mkPos i) := by
        simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate_none]
      have h_db_result : (s.feedToken i tk).db = s.db := by
        simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate_none]
      rw [h_db_result, h_tokp_result]
      exact h_ghost
    · by_cases h_end : tk.eqArray "$.".toAscii
      · -- Case 2: "$." → finishProof → exits proof mode
        let s0 : ParserState := { s with tokp := default }
        have h_tokp_result : (s.feedToken i tk).tokp = .start := by
          have := finishProof_tokp_start s0 pr
          simpa [ParserState.feedToken, h_tokp, h_open, h_include, h_end, s0] using this
        simp [ProofGhost, h_tokp_result]
      · -- Case 3: feedProof → ghost maintained
        let s0 : ParserState := { s with tokp := default }
        have h_success_feed :
            (s0.feedProof tk pr).db.error? = none := by
          simpa [ParserState.feedToken, h_tokp, h_open, h_include, h_end, s0] using h_success
        have h_db_eq : (s.feedToken i tk).db = s.db := by
          have := feedProof_success_db s0 tk pr h_success_feed
          simpa [ParserState.feedToken, h_tokp, h_open, h_include, h_end, s0] using this
        have ⟨pr_mid, h_tokp_mid_raw, h_fmla_eq, h_frame_eq⟩ :=
          feedProof_success_tokpInv_core s0 tk pr h_success_feed
        have h_tokp_mid : (s.feedToken i tk).tokp = .proof pr_mid := by
          simpa [ParserState.feedToken, h_tokp, h_open, h_include, h_end, s0] using h_tokp_mid_raw
        -- Now show ProofGhost s.db (.proof pr_mid)
        rw [h_db_eq, h_tokp_mid]
        show proofGhostCore s.db pr_mid
        obtain ⟨h_trim_ghost, h_start_ghost, h_normal_ghost, h_preload_ghost,
          h_compressed_ghost⟩ := h_ghost
        refine ⟨?trim_clause, ?start_clause, ?normal_clause, ?preload_clause,
          ?compressed_clause⟩
        case trim_clause =>
          simpa [h_fmla_eq, h_frame_eq] using h_trim_ghost
        case start_clause =>
          -- .start clause: vacuously true (feedProof never produces .start)
          intro h_start_mid
          exfalso
          exact feedProof_ptp_not_start s0 tk pr h_success_feed pr_mid
            h_tokp_mid_raw h_start_mid
        case normal_clause =>
          -- .normal clause: NormalProofReachable maintained
          intro h_normal_mid
          -- Sub-case analysis on pr.ptp
          by_cases h_start : pr.ptp = .start
          · -- pr.ptp = .start → first proof step
            have ⟨h_stack_empty, _h_heap_empty, _h_scope⟩ := h_start_ghost h_start
            by_cases h_open_paren : tk.eqArray "(".toAscii
            · -- "(" starts compressed mode (.preload) → contradiction with .normal
              exfalso
              obtain ⟨pr', h_go, h_tokp_pr'⟩ :=
                feedProof_success_go_ok s0 tk pr h_success_feed
              obtain ⟨mid, _, h_eq⟩ :=
                go_start_open_extracts s0 tk pr pr' h_go h_start h_open_paren
              rw [h_tokp_pr'] at h_tokp_mid_raw
              have h_pr_eq := TokenParser.proof.inj h_tokp_mid_raw; subst h_pr_eq
              rw [h_eq] at h_normal_mid; exact absurd h_normal_mid (by nofun)
            · -- Not "(" → goNormal path
              by_cases h_q : tk.eqArray "?".toAscii
              · exfalso
                exact feedProof_q_strict_errors s0 tk pr h_q
                  (by simpa [s0] using h_strict) (.inl h_start)
                  (fun _ => h_open_paren)
                  h_success_feed
              · -- Normal label token → feedProof_start_establishes_reachable
                have ⟨pr_mid', h_tokp_mid', h_label_mid', h_fmla_mid',
                    _h_frame_mid', _h_ptp_mid', h_reach'⟩ :=
                  feedProof_start_establishes_reachable s0 tk pr
                    h_success_feed h_start h_open_paren h_q h_stack_empty
                have h_eq : pr_mid = pr_mid' := by
                  rw [h_tokp_mid_raw] at h_tokp_mid'
                  exact TokenParser.proof.inj h_tokp_mid'
                subst h_eq
                rw [h_label_mid', h_fmla_mid']
                simpa [s0] using h_reach'
          · -- pr.ptp ≠ .start
            by_cases h_normal : pr.ptp = .normal
            · -- pr.ptp = .normal → feedProof_normal_maintains_reachable
              have h_reach := h_normal_ghost h_normal
              by_cases h_q : tk.eqArray "?".toAscii
              · exfalso
                exact feedProof_q_strict_errors s0 tk pr h_q
                  (by simpa [s0] using h_strict) (.inr h_normal)
                  (fun h_s => absurd h_s h_start)
                  h_success_feed
              · -- Normal label → maintains reachability
                have h_reach_s0 : NormalProofReachable s0.db pr.label pr.fmla pr.stack := by
                  simpa [s0] using h_reach
                have ⟨pr_mid', h_tokp_mid', h_label_mid', h_fmla_mid',
                    _h_frame_mid', _h_ptp_mid', h_reach'⟩ :=
                  feedProof_normal_maintains_reachable s0 tk pr
                    h_success_feed h_normal h_q h_reach_s0
                have h_eq : pr_mid = pr_mid' := by
                  rw [h_tokp_mid_raw] at h_tokp_mid'
                  exact TokenParser.proof.inj h_tokp_mid'
                subst h_eq
                rw [h_label_mid', h_fmla_mid']
                simpa [s0] using h_reach'
            · -- pr.ptp ≠ .start and ≠ .normal → .preload or .compressed
              exfalso
              exact feedProof_compressed_pipeline_not_normal s0 tk pr h_success_feed
                h_start h_normal pr_mid h_tokp_mid_raw h_normal_mid
        case preload_clause =>
          -- .preload clause: PreloadPhaseGhost maintained
          intro h_preload_mid
          obtain ⟨pr', h_go, h_tokp_pr'⟩ :=
            feedProof_success_go_ok s0 tk pr h_success_feed
          rw [h_tokp_pr'] at h_tokp_mid_raw
          have h_pr_eq := TokenParser.proof.inj h_tokp_mid_raw; subst h_pr_eq
          -- Sub-case analysis on pr.ptp
          cases h_ptp : pr.ptp with
          | start =>
            -- .start + "(" → establish PreloadPhaseGhost
            have ⟨h_stack_empty, _h_heap_empty, h_scope⟩ := h_start_ghost h_ptp
            -- "(" must hold (otherwise goNormal → .normal, not .preload)
            have h_open_paren : tk.eqArray "(".toAscii := by
              by_contra h_no_open
              unfold ParserState.feedProof.go at h_go
              simp [h_ptp, h_no_open] at h_go
              have := goNormal_ok_preserves_ptp s0 tk { pr with ptp := .normal } pr' h_go
              simp at this; rw [this] at h_preload_mid; exact absurd h_preload_mid (by nofun)
            obtain ⟨mid, h_pre_ok, h_eq⟩ :=
              go_start_open_extracts s0 tk pr pr' h_go h_ptp h_open_paren
            have h_mand_s : s.db.preloadMandatoryHyps pr = .ok mid := by
              simpa [s0] using h_pre_ok
            have h_mid_core := preloadMandatoryHyps_ok_preserves_core s.db pr mid h_mand_s
            have h_mid_label :=
              Metamath.PrefixTraceCompressed.preloadMandatoryHyps_preserves_label
                s.db pr mid h_mand_s
            -- pr_mid = {mid with ptp := .preload}
            rw [h_eq]; show PreloadPhaseGhost s.db {mid with ptp := .preload}
            unfold PreloadPhaseGhost
            -- Witnesses: start state is original `pr`; mandatory preload gives `mid`.
            refine ⟨[], pr, mid, mid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact h_mid_label.symm
            · exact h_mid_core.1.symm
            · exact h_mid_core.2.symm
            · exact h_stack_empty
            · exact _h_heap_empty
            · exact h_ptp
            · exact h_scope
            · exact h_mand_s
            · simp [List.foldlM, pure, Except.pure]
            · rfl
            · rfl
          | normal =>
            -- .normal → goNormal → output .normal, not .preload
            exfalso
            unfold ParserState.feedProof.go at h_go; simp [h_ptp] at h_go
            have := goNormal_ok_preserves_ptp s0 tk pr pr' h_go
            rw [this, h_ptp] at h_preload_mid; exact absurd h_preload_mid (by nofun)
          | preload =>
            -- .preload → label or ")"
            by_cases h_close : tk.eqArray ")".toAscii
            · -- ")" → .compressed 0, not .preload
              have h_eq := go_preload_close_extracts s0 tk pr pr' h_go h_ptp h_close
              rw [h_eq] at h_preload_mid; exact absurd h_preload_mid (by nofun)
            · -- label → DB.preload extends ghost
              have ⟨_, h_preload_ok⟩ :=
                go_preload_label_extracts s0 tk pr pr' h_go h_ptp h_close
              -- pr' came from db.preload, so ptp preserved
              have h_ptp_eq := preload_preserves_ptp s0.db pr pr' (toLabel tk).snd
                (by simpa [s0] using h_preload_ok)
              -- Extend PreloadPhaseGhost
              have h_pghost := h_preload_ghost h_ptp
              have h_preload_s : s.db.preload pr (toLabel tk).snd = .ok pr' := by
                simpa [s0] using h_preload_ok
              have h_core := preload_ok_preserves_core s.db pr pr' (toLabel tk).snd h_preload_s
              have h_lbl := preload_preserves_label s.db pr pr' (toLabel tk).snd h_preload_s
              exact preloadPhaseGhost_extend s.db pr pr' (toLabel tk).snd
                h_pghost h_preload_s h_lbl h_core.1 h_core.2
          | compressed chr =>
            -- .compressed → output can't be .preload
            unfold ParserState.feedProof.go at h_go; simp [h_ptp] at h_go
            cases h_dec : ParserState.decodeCompressed tk chr s0.db.config.compressedInvalidBytes
                s0.db.config.compressedSavePlacement with
            | error e => simp [h_dec, bind, Except.bind] at h_go
            | ok dec =>
              obtain ⟨acts, chr'⟩ := dec
              simp [h_dec, bind, Except.bind] at h_go
              cases h_apply : ParserState.applyCompressedActions s0.db pr acts with
              | error e => simp [h_apply, Functor.map, Except.map] at h_go
              | ok mid =>
                simp [h_apply, Functor.map, Except.map] at h_go
                subst h_go; exact absurd h_preload_mid (by nofun)
        ·
          -- .compressed n clause: CompressedFoldGhost maintained
          intro ⟨n, h_compressed_mid⟩
          obtain ⟨pr', h_go, h_tokp_pr'⟩ :=
            feedProof_success_go_ok s0 tk pr h_success_feed
          rw [h_tokp_pr'] at h_tokp_mid_raw
          have h_pr_eq := TokenParser.proof.inj h_tokp_mid_raw; subst h_pr_eq
          cases h_ptp : pr.ptp with
          | start =>
            -- .start → output is .normal or .preload, not .compressed
            unfold ParserState.feedProof.go at h_go
            by_cases h_open : tk.eqArray "(".toAscii
            · simp [h_ptp, h_open] at h_go
              cases h_pre : s0.db.preloadMandatoryHyps pr with
              | error e => simp [h_pre, Functor.map, Except.map] at h_go
              | ok mid =>
                simp [h_pre, Functor.map, Except.map] at h_go
                subst h_go; exact absurd h_compressed_mid (by nofun)
            · simp [h_ptp, h_open] at h_go
              have := goNormal_ok_preserves_ptp s0 tk { pr with ptp := .normal } pr' h_go
              simp at this; rw [this] at h_compressed_mid
              exact absurd h_compressed_mid (by nofun)
          | normal =>
            -- .normal → goNormal → output .normal, not .compressed
            exfalso
            unfold ParserState.feedProof.go at h_go; simp [h_ptp] at h_go
            have := goNormal_ok_preserves_ptp s0 tk pr pr' h_go
            rw [this, h_ptp] at h_compressed_mid; exact absurd h_compressed_mid (by nofun)
          | preload =>
            -- .preload → ")" transitions to .compressed 0, label stays .preload
            by_cases h_close : tk.eqArray ")".toAscii
            · -- ")" → .compressed 0: transition PreloadPhaseGhost → CompressedFoldGhost
              have h_eq := go_preload_close_extracts s0 tk pr pr' h_go h_ptp h_close
              rw [h_eq] at h_compressed_mid ⊢
              have h_pghost := h_preload_ghost h_ptp
              show CompressedFoldGhost s.db
                {pr with ptp := .compressed .betweenSteps}
              obtain ⟨preloads, pr_start, pr_mand, pr_preload,
                h_start_lbl, h_start_fmla, h_start_frame, h_start_stack, h_start_heap, h_start_ptp,
                h_scope, h_mand, h_fold, h_stack, h_heap⟩ := h_pghost
              exact ⟨preloads, [], pr_start, pr_mand, pr_preload, pr_preload,
                h_start_lbl, h_start_fmla, h_start_frame, h_start_stack, h_start_heap, h_start_ptp,
                h_scope, h_mand, h_fold,
                by simp [List.foldlM, pure, Except.pure],
                h_stack, h_heap⟩
            · -- label → stays .preload, not .compressed
              have ⟨_, h_preload_ok⟩ :=
                go_preload_label_extracts s0 tk pr pr' h_go h_ptp h_close
              have h_ptp_eq := preload_preserves_ptp s0.db pr pr' (toLabel tk).snd
                (by simpa [s0] using h_preload_ok)
              rw [h_ptp_eq, h_ptp] at h_compressed_mid
              exact absurd h_compressed_mid (by nofun)
          | compressed chr =>
            -- .compressed chr → decode + applyCompressedActions → extend ghost
            obtain ⟨acts, chr', pr_mid_inner, h_dec, h_apply_raw, h_eq⟩ :=
              go_compressed_extracts s0 tk pr pr' chr h_go h_ptp
            rw [h_eq]
            have h_apply : ParserState.applyCompressedActions s.db pr acts = .ok pr_mid_inner := by
              simpa [s0] using h_apply_raw
            have h_cghost := h_compressed_ghost ⟨chr, h_ptp⟩
            have h_core := applyCompressedActions_ok_preserves_core s.db pr pr_mid_inner acts h_apply
            have h_lbl := Metamath.PrefixTraceCompressed.applyCA_preserves_label
              s.db pr acts pr_mid_inner h_apply
            -- Need h_no_unknown: rejectUnknownSteps = true → no unknowns in successful apply
            have h_no_unknown : ∀ a ∈ acts, a ≠ .unknown := by
              exact applyCompressedActions_ok_no_unknown s.db pr pr_mid_inner acts
                (by simpa [s0] using h_strict) h_apply
            show CompressedFoldGhost s.db {pr_mid_inner with ptp := .compressed chr'}
            have h_ext : CompressedFoldGhost s.db pr_mid_inner :=
              compressedFoldGhost_extend s.db pr pr_mid_inner acts
                h_cghost h_no_unknown h_apply h_lbl h_core.1
            simpa [CompressedFoldGhost] using h_ext

private theorem withAt_mkError_ne_none
    (label : String) (s : ParserState) (pos : Pos) (ev : ErrorEvidence) :
    (ParserState.withAt label (fun _ => s.mkErrorFromEvidence pos ev)).db.error? ≠ none :=
  withAt_preserves_error label _
    (ParserState_mkErrorFromEvidence_sets_error s pos ev)

/-- No proof mode occurs beneath the administrative wrappers of a token-parser
mode. -/
private def ProofModeAbsent : TokenParser → Prop
  | .proof _ => False
  | .comment inner => ProofModeAbsent inner
  | .includePath resume _ => ProofModeAbsent resume
  | .includeClose resume _ _ => ProofModeAbsent resume
  | _ => True

private theorem proofGhost_of_proofModeAbsent {db : DB} {tp : TokenParser}
    (h : ProofModeAbsent tp) : ProofGhost db tp := by
  induction tp with
  | proof pr => exact h.elim
  | comment inner ih => exact ih h
  | includePath resume position ih => exact ih h
  | includeClose resume position path ih => exact ih h
  | _ => exact trivial

/-- `djvars_loop_aux` preserves `ProofGhost` when the input tokp is a simple
    (non-proof, non-comment) constructor. Both properties are preserved through
    `mkErrorFromEvidence` (preserves tokp) and `withDB` (preserves tokp).
    Follows the `Nat.rec` pattern from `djvars_loop_aux_db_config` (Verify.lean). -/
private theorem djvars_loop_aux_proofGhost
    (arr_dj : Array String) (s : ParserState) (pos : Pos) (tk : String) (i : Nat)
    (h_absent : ProofModeAbsent s.tokp) :
    ProofGhost (ParserState.djvars_loop_aux arr_dj s pos tk i).db
              (ParserState.djvars_loop_aux arr_dj s pos tk i).tokp := by
  refine Nat.rec
    (motive := fun m => ∀ i (s : ParserState), arr_dj.size - i = m →
      ProofModeAbsent s.tokp →
      ProofGhost (ParserState.djvars_loop_aux arr_dj s pos tk i).db
                (ParserState.djvars_loop_aux arr_dj s pos tk i).tokp)
    ?base ?step (arr_dj.size - i) i s rfl h_absent
  · -- Base: ¬ i < arr_dj.size → result is { s with tokp := .djvars _ }
    intro i s hs h_absent
    have hi : ¬ i < arr_dj.size := by
      intro hi
      have hpos : arr_dj.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    simp [ParserState.djvars_loop_aux, hi, ProofGhost]
  · -- Step: i < arr_dj.size
    intro m ih i s hs h_absent
    have hi : i < arr_dj.size := by
      by_cases hi' : i < arr_dj.size
      · exact hi'
      · have hz : arr_dj.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        simp [hz] at hs
    have hs' : arr_dj.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    unfold ParserState.djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    split  -- on arr_dj[i] == tk
    · -- Duplicate: mkErrorFromEvidence preserves tokp = s.tokp
      exact proofGhost_of_proofModeAbsent h_absent
    · -- Not duplicate: recurse with withDB (preserves tokp)
      exact ih (i + 1) _ hs' h_absent

/-- `feedTokens` always produces an output satisfying ProofGhost.
    For `.float/.ess/.ax`: output tokp is `.start` → True.
    For `.thm`: output tokp is `.proof (mkProofState ...)` → ghost holds.
    All error paths contradict the success hypothesis.

    Proof follows the pattern from `feedToken_maintains_tokpInv` (ParserOperations.lean:8710):
    establish preconditions by contradiction, then compute tokp via simp. -/
private theorem feedTokens_ghost
    (s : ParserState) (arr : Array Verify.Sym) (p : TokensParser)
    (h_success : (s.feedTokens arr p).db.error? = none) :
    ProofGhost (s.feedTokens arr p).db (s.feedTokens arr p).tokp := by
  cases p with
  | mk k pos l =>
    -- Common precondition: hasConstHead must hold on success
    have h_head : Formula.hasConstHead arr = true := by
      by_cases h : Formula.hasConstHead arr
      · exact h
      · exfalso; exact absurd h_success (by
          simpa [ParserState.feedTokens, h] using
            withAt_mkError_ne_none l s pos (.scopeDecl .firstSymbolNotConstant))
    cases k with
    | float =>
      have h_shape : Formula.isFloatShape arr = true := by
        by_cases h : Formula.isFloatShape arr
        · exact h
        · exfalso; exact absurd h_success (by
            simpa [ParserState.feedTokens, h_head, h] using
              withAt_mkError_ne_none l s pos (.scopeDecl .expectedConstantAndVariable))
      have h_tokp : (s.feedTokens arr ⟨.float, pos, l⟩).tokp = .start := by
        simp [ParserState.feedTokens, h_head, h_shape, ParserState.withAt_tokp]
      simp [h_tokp, ProofGhost]
    | ess =>
      have h_gate : ParserState.topLevelEssViolation? s.db = none := by
        cases h : ParserState.topLevelEssViolation? s.db with
        | none => rfl
        | some err => exfalso; exact absurd h_success (by
            simpa [ParserState.feedTokens, h_head, h] using
              withAt_mkError_ne_none l s pos (.scopeDecl err))
      have h_tokp : (s.feedTokens arr ⟨.ess, pos, l⟩).tokp = .start := by
        simp [ParserState.feedTokens, h_head, h_gate, ParserState.withAt_tokp]
      simp [h_tokp, ProofGhost]
    | ax =>
      have h_tokp : (s.feedTokens arr ⟨.ax, pos, l⟩).tokp = .start := by
        simp [ParserState.feedTokens, h_head, ParserState.withAt_tokp]
      simp [h_tokp, ProofGhost]
    | thm =>
      have h_trim : ∃ fr, s.db.trimFrame' arr = .ok fr := by
        cases h : s.db.trimFrame' arr with
        | ok fr => exact ⟨fr, rfl⟩
        | error msg => exfalso; exact absurd h_success (by
            simpa [ParserState.feedTokens, h_head, h] using
              withAt_mkError_ne_none l s pos (.scopeDecl msg))
      obtain ⟨fr, h_trim⟩ := h_trim
      have h_no_int : s.db.interrupt = false := by
        by_cases h : s.db.interrupt
        · exfalso
          have : (s.feedTokens arr ⟨.thm, pos, l⟩).db.error? ≠ none := by
            simp only [ParserState.feedTokens, h_head, h_trim, h]
            unfold ParserState.withAt
            simp [ParserState.withDB]
          exact absurd h_success this
        · simpa using h
      have h_tokp : (s.feedTokens arr ⟨.thm, pos, l⟩).tokp =
          .proof (s.db.mkProofState pos l arr fr) := by
        simp [ParserState.feedTokens, h_head, h_trim, h_no_int,
          ParserState.resumeThm, ParserState.withAt_tokp]
      -- Show the output db equals s.db (resumeThm doesn't modify db)
      have h_feed_eq : s.feedTokens arr ⟨.thm, pos, l⟩ =
          ParserState.withAt l (fun _ => s.resumeThm pos l arr fr) := by
        simp [ParserState.feedTokens, h_head, h_trim, h_no_int]
      rw [h_feed_eq] at h_tokp h_success ⊢
      have ⟨_, h_at_db⟩ := withAt_success_eq l _ h_success
      have h_db_eq : (ParserState.withAt l fun _ => s.resumeThm pos l arr fr).db = s.db := by
        rw [h_at_db]; rfl
      rw [h_tokp, h_db_eq]
      -- proofGhostCore: ptp=.start → all conjuncts vacuously true
      exact proofGhostCore_of_mkProofState s.db s.db pos l arr fr
        h_trim (trimFrame'_hyps_subset s.db arr fr h_trim)

/-- Ghost propagation through `feedToken` for **all** token-parser modes.
    Combines proof-mode handling (`feedToken_proof_maintains_ghost`) with
    comment-mode transparency and non-proof-mode analysis.
    Requires `rejectUnknownSteps = true` (for proof-mode `?` rejection). -/
theorem feedToken_maintains_ghost
    (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_ghost : ProofGhost s.db s.tokp)
    (_h_inv : ParserStateInv s)
    (h_no_err : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_success : (s.feedToken i tk).db.error? = none) :
    ProofGhost (s.feedToken i tk).db (s.feedToken i tk).tokp := by
  cases h_tokp : s.tokp with
  | proof pr =>
    exact feedToken_proof_maintains_ghost s i tk pr h_tokp h_ghost h_no_err h_strict h_success
  | comment inner =>
    -- Comment mode: $) exits, $( errors, else no change
    by_cases h_close : tk.eqArray "$)".toAscii
    · -- $) → exit comment, tokp = inner, db unchanged
      have h_db : (s.feedToken i tk).db = s.db := by
        simp [ParserState.feedToken, h_tokp, h_close]
      have h_tp : (s.feedToken i tk).tokp = inner := by
        simp [ParserState.feedToken, h_tokp, h_close]
      rw [h_db, h_tp]; rw [h_tokp] at h_ghost; exact h_ghost
    · by_cases h_open : tk.eqArray "$(".toAscii
      · -- $( inside comment → error
        have : (s.feedToken i tk).db.error? ≠ none := by
          simp [ParserState.feedToken, h_tokp, h_close, h_open,
            ParserState.mkErrorFromEvidence, ParserState.withDB]
        exact (this h_success).elim
      · -- Other token → no change (result = s)
        have h_db : (s.feedToken i tk).db = s.db := by
          simp [ParserState.feedToken, h_tokp, h_close, h_open]
        have h_tp : (s.feedToken i tk).tokp = .comment inner := by
          simp [ParserState.feedToken, h_tokp, h_close, h_open]
        rw [h_db, h_tp]; rw [h_tokp] at h_ghost; exact h_ghost
  | start =>
    by_cases h_open : tk.eqArray "$(".toAscii
    · simp [ParserState.feedToken, h_tokp, h_open, ProofGhost]
    · -- All .start outputs are non-proof → ProofGhost = True
      simp only [ParserState.feedToken, h_tokp, h_open] at h_success ⊢
      -- Nested matches on $ keywords; all produce non-proof tokp or error
      repeat first
        | split
        | simp_all [ProofGhost, ParserState.withDB, ParserState.label,
            ParserState.mkErrorFromEvidence]
  | const =>
    by_cases h_open : tk.eqArray "$(".toAscii
    · simp [ParserState.feedToken, h_tokp, h_open, ProofGhost]
    · simp only [ParserState.feedToken, h_tokp, h_open] at h_success ⊢
      simp only [ParserState.sym, ParserState.withMath]
      repeat first | split | simp [ProofGhost, h_tokp, ParserState.withDB,
        ParserState.mkErrorFromEvidence]
  | var =>
    by_cases h_open : tk.eqArray "$(".toAscii
    · simp [ParserState.feedToken, h_tokp, h_open, ProofGhost]
    · simp only [ParserState.feedToken, h_tokp, h_open] at h_success ⊢
      simp only [ParserState.sym, ParserState.withMath]
      repeat first | split | simp [ProofGhost, h_tokp, ParserState.withDB,
        ParserState.mkErrorFromEvidence]
  | djvars arr =>
    by_cases h_open : tk.eqArray "$(".toAscii
    · simp [ParserState.feedToken, h_tokp, h_open, ProofGhost]
    · simp only [ParserState.feedToken, h_tokp, h_open] at h_success ⊢
      -- All branches produce non-proof tokp (start, error, or djvars_loop_aux)
      simp only [ParserState.djvars_loop, ParserState.withMath]
      repeat first
        | split
        | simp [ProofGhost, h_tokp, ParserState.mkErrorFromEvidence,
            ParserState.withDB]
        | exact djvars_loop_aux_proofGhost _ s _ _ 0
            (by simp [ProofModeAbsent, h_tokp])
  | math arr' p =>
    by_cases h_open : tk.eqArray "$(".toAscii
    · simp [ParserState.feedToken, h_tokp, h_open, ProofGhost]
    · simp only [ParserState.feedToken, h_tokp, h_open] at h_success ⊢
      by_cases h_include : tk.eqArray "$[".toAscii
      · have h_gate_none :
          includeDirectiveViolation? s.db.config s.db.scopes.size true i = none := by
          have h_success_ft : (s.feedToken i tk).db.error? = none := by
            simpa [ParserState.feedToken, h_tokp, h_open, h_include] using h_success
          cases h_gate : includeDirectiveViolation? s.db.config s.db.scopes.size true i with
          | none => rfl
          | some err =>
              have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate,
                  ParserState.mkErrorFromEvidence, ParserState.withDB]
              exact (h_bad h_success_ft).elim
        have h_tokp_eq :
            (s.feedToken i tk).tokp =
              .includePath (.math arr' p) (s.mkPos i) := by
          simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate_none]
        simp [h_include, h_gate_none, ProofGhost] at h_success ⊢
      · by_cases h_delim : tk.eqArray p.k.delim
        · -- Delimiter → feedTokens
          simp [h_include] at h_success ⊢
          simp only [h_delim, ite_true] at h_success ⊢
          exact feedTokens_ghost s arr' p h_success
        · -- Not delimiter → withMath → stays .math → True
          simp [h_include] at h_success ⊢
          simp only [h_delim] at h_success ⊢
          have h_absent : ProofModeAbsent s.tokp := by
            simp [ProofModeAbsent, h_tokp]
          -- Unfold withMath and eliminate false=true conditions
          simp only [ParserState.withMath, Bool.false_eq_true, ite_false]
          split
          · -- toMath fails → mkErrorFromEvidence → tokp unchanged → non-proof
            exact proofGhost_of_proofModeAbsent h_absent
          · -- toMath succeeds → match on db.find? in Id monad
            try simp [Id.run]
            split
            · exact trivial  -- const → .math → True
            · -- var → active: .math → True; inactive: error state → non-proof
              split
              · exact trivial
              · exact proofGhost_of_proofModeAbsent h_absent
            · split  -- match mathSymbolViolation?
              · exact proofGhost_of_proofModeAbsent h_absent
              · exact proofGhost_of_proofModeAbsent h_absent
  | label pos' lab =>
    by_cases h_open : tk.eqArray "$(".toAscii
    · simp [ParserState.feedToken, h_tokp, h_open, ProofGhost]
    · simp only [ParserState.feedToken, h_tokp, h_open] at h_success ⊢
      repeat first
        | split
        | simp_all [ProofGhost, ParserState.mkErrorFromEvidence,
            ParserState.withDB]

  | includePath resume includePos =>
    have h_resume_ghost : ProofGhost s.db resume := by
      simpa [h_tokp, ProofGhost] using h_ghost
    by_cases h_open : tk.eqArray "$(".toAscii
    · simpa [ParserState.feedToken, h_tokp, h_open, ProofGhost] using
        h_resume_ghost
    · by_cases h_include : tk.eqArray "$[".toAscii
      · have h_gate_none :
          includeDirectiveViolation? s.db.config s.db.scopes.size true i = none := by
          cases h_gate : includeDirectiveViolation? s.db.config s.db.scopes.size true i with
          | none => rfl
          | some err =>
              have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate,
                  ParserState.mkErrorFromEvidence, ParserState.withDB]
              exact (h_bad h_success).elim
        have h_tokp_eq :
            (s.feedToken i tk).tokp =
              .includePath (.includePath resume includePos) (s.mkPos i) := by
          simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate_none]
        have h_db_eq : (s.feedToken i tk).db = s.db := by
          simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate_none]
        rw [h_db_eq, h_tokp_eq]
        exact h_resume_ghost
      · by_cases h_close : tk.eqArray "$]".toAscii
        · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
            simp [ParserState.feedToken, h_tokp, h_open, h_include, h_close,
              ParserState.mkErrorFromEvidence, ParserState.withDB]
          exact (h_bad h_success).elim
        · let rawPath := (ParserState.includePathFromToken tk).1
          let closesInline := (ParserState.includePathFromToken tk).2
          cases h_norm : ParserState.normalizeIncludePath s.db.config.literalIncludePaths s.sourceFile rawPath with
          | error err =>
              have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                simp [ParserState.feedToken, h_tokp, h_open, h_include, h_close,
                  rawPath, h_norm,
                  ParserState.mkErrorFromEvidence, ParserState.withDB]
              exact (h_bad h_success).elim
          | ok includePath =>
              by_cases h_inline : closesInline
              · have h_req : (s.requestInclude resume includePath).db.error? ≠ none :=
                  ParserState_requestInclude_sets_error s resume includePath
                have h_eq : s.feedToken i tk = s.requestInclude resume includePath := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_include, h_close,
                    rawPath, closesInline, h_norm, h_inline]
                exact (h_req (by simpa [h_eq] using h_success)).elim
              · have h_tokp_eq :
                  (s.feedToken i tk).tokp =
                    .includeClose resume includePos includePath := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_include, h_close,
                    rawPath, closesInline, h_norm, h_inline]
                have h_db_eq : (s.feedToken i tk).db = s.db := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_include, h_close,
                    rawPath, closesInline, h_norm, h_inline]
                rw [h_db_eq, h_tokp_eq]
                exact h_resume_ghost
  | includeClose resume includePos includePath =>
    have h_resume_ghost : ProofGhost s.db resume := by
      simpa [h_tokp, ProofGhost] using h_ghost
    by_cases h_open : tk.eqArray "$(".toAscii
    · simpa [ParserState.feedToken, h_tokp, h_open, ProofGhost] using
        h_resume_ghost
    · by_cases h_include : tk.eqArray "$[".toAscii
      · have h_gate_none :
          includeDirectiveViolation? s.db.config s.db.scopes.size true i = none := by
          cases h_gate : includeDirectiveViolation? s.db.config s.db.scopes.size true i with
          | none => rfl
          | some err =>
              have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate,
                  ParserState.mkErrorFromEvidence, ParserState.withDB]
              exact (h_bad h_success).elim
        have h_tokp_eq :
            (s.feedToken i tk).tokp =
              .includePath (.includeClose resume includePos includePath)
                (s.mkPos i) := by
          simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate_none]
        have h_db_eq : (s.feedToken i tk).db = s.db := by
          simp [ParserState.feedToken, h_tokp, h_open, h_include, h_gate_none]
        rw [h_db_eq, h_tokp_eq]
        exact h_resume_ghost
      · by_cases h_close : tk.eqArray "$]".toAscii
        · have h_req : (s.requestInclude resume includePath).db.error? ≠ none :=
            ParserState_requestInclude_sets_error s resume includePath
          have h_eq : s.feedToken i tk = s.requestInclude resume includePath := by
            simp [ParserState.feedToken, h_tokp, h_open, h_include, h_close]
          exact (h_req (by simpa [h_eq] using h_success)).elim
        · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
            simp [ParserState.feedToken, h_tokp, h_open, h_include, h_close,
              ParserState.mkErrorFromEvidence, ParserState.withDB]
          exact (h_bad h_success).elim

/-! ## Local finishProof event theorem -/

/-- A concrete `feedToken` finish-proof event (`$.` on `.proof pr`) that succeeds. -/
def FinishProofEvent (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState) : Prop :=
  s.tokp = .proof pr ∧
  tk.eqArray "$(".toAscii = false ∧
  tk.eqArray "$[".toAscii = false ∧
  tk.eqArray "$.".toAscii = true ∧
  (s.feedToken i tk).db.error? = none

/-- The proof state carried by a concrete finish event contains the exact
mandatory frame computed when the theorem statement was opened. -/
theorem finishProofEvent_trimFrame
    (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_evt : FinishProofEvent s i tk pr) :
    s.db.trimFrame' pr.fmla = .ok pr.frame := by
  rw [h_evt.1] at h_ghost
  exact h_ghost.1

/-- Local event theorem: a successful `feedToken` finishProof event yields
    pre-insert `Spec.Provable` in `s.db`.
    The compressed branch uses `CompressedFoldGhost_to_ProofReachableZ`. -/
theorem feedToken_finishProofEvent_prefixProvable
    (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState)
    (h_inv : ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_no_err : s.db.error? = none)
    (h_evt : FinishProofEvent s i tk pr) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase s.db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr.fmla) := by
  rcases h_evt with ⟨h_tokp, h_open, h_include, h_end, h_success⟩
  rw [h_tokp] at h_ghost
  change proofGhostCore s.db pr at h_ghost
  obtain ⟨_h_trim, _h_start, h_normal, _h_preload, h_compressed⟩ := h_ghost
  let s0 : ParserState := { s with tokp := default }
  have h_finish : (s0.finishProof pr).db.error? = none := by
    simpa [FinishProofEvent, ParserState.feedToken, h_tokp, h_open, h_include, h_end, s0] using h_success
  have h_wf : WellFormedDB s.db := h_inv.1
  have h_no_err0 : s0.db.error? = none := by simpa [s0] using h_no_err
  have ⟨h_stack_one, h_stack_fmla, h_mode⟩ :=
    finishProof_success_stack_conditions s0 pr h_finish
  have h_reach : ProofReachableZ s.db pr.label pr.fmla pr.stack := by
    cases h_mode with
    | inl h_ptp_normal =>
      exact .normal (h_normal h_ptp_normal)
    | inr h_compressed_mode =>
      cases h_compressed_mode with
      | inl h_between =>
        have h_cghost : CompressedFoldGhost s.db pr :=
          h_compressed ⟨.betweenSteps, h_between⟩
        exact CompressedFoldGhost_to_ProofReachableZ s.db pr
          h_cghost h_wf h_stack_one h_stack_fmla
      | inr h_completed =>
        have h_cghost : CompressedFoldGhost s.db pr :=
          h_compressed ⟨.justCompletedStep, h_completed⟩
        exact CompressedFoldGhost_to_ProofReachableZ s.db pr
          h_cghost h_wf h_stack_one h_stack_fmla
  simpa [s0] using
    (finishProof_any_mode_prefix_provable s0 pr h_reach h_wf h_no_err0 h_finish)

/-! ## Event-lift definitions

`EventProvableAt s` says: any feedToken finishProof event at state `s` yields
`Spec.Provable` in the pre-insertion database.

`AllFeedEventsProvable` mirrors `feed`'s recursion, conjoining `EventProvableAt`
at every feedToken call site. -/

/-- A feedToken call at state `s` is prefix-provable for any finishProof event. -/
def EventProvableAt (s : ParserState) : Prop :=
  ∀ (pos : Nat) (tk : ByteSlice) (pr : ProofState),
    FinishProofEvent s pos tk pr →
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase s.db = some Γ ∧
      toFrame s.db s.db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr pr.fmla)

/-- `EventProvableAt` follows from ghost + invariant + no-error. -/
theorem eventProvableAt_of_ghost_inv (s : ParserState)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_inv : ParserStateInv s)
    (h_no_err : s.db.error? = none) :
    EventProvableAt s :=
  fun pos tk pr h_evt =>
    feedToken_finishProofEvent_prefixProvable s pos tk pr h_inv h_ghost h_no_err h_evt

/-- Every feedToken finishProof event during `s.feed base arr i rs` yields
    `Spec.Provable`. Mirrors `feed`'s control flow exactly. -/
private def AllFeedEventsProvable (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState) : Prop :=
  if _ : i < arr.size then
    let c := arr[i]
    if isWhitespace c then
      match rs with
      | .ws =>
          AllFeedEventsProvable base arr (i + 1) .ws (s.updateLine (base + i) c)
      | .token ot =>
          let s0 := match ot with
            | .this off => s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
            | .old base' off arr' => s.feedToken (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
          EventProvableAt s ∧
          let s1 := s0.updateLine (base + i) c
          if s1.db.error? = none then
            AllFeedEventsProvable base arr (i + 1) .ws s1
          else True
    else
      match rs with
      | .ws => AllFeedEventsProvable base arr (i + 1) (.token (.this i)) s
      | .token ot => AllFeedEventsProvable base arr (i + 1) (.token ot) s
  else True
termination_by arr.size - i

/-- All feedToken finishProof events during `s.feedAll base arr`. -/
def AllFeedAllEventsProvable (base : Nat) (arr : ByteArray) (s : ParserState) : Prop :=
  match s.charp with
  | .ws => AllFeedEventsProvable base arr 0 .ws s
  | .token base' tk =>
      AllFeedEventsProvable base arr 0
        (.token (.old base' tk.start tk.byteArray))
        { s with charp := default }

/-! ## Ghost propagation through the feed loop

Parallel structure to `feed_maintains_stateInv` (ParserOperations.lean).
Uses `Nat.rec` induction on `arr.size - i`. -/

/-- `updateLine` preserves the ghost (doesn't change db or tokp). -/
@[simp] private theorem updateLine_db (s : ParserState) (i : Nat) (c : UInt8) :
    (s.updateLine i c).db = s.db := by
  unfold ParserState.updateLine; split <;> rfl

/-- feedToken preserves `rejectUnknownSteps` configuration. -/
private theorem feedToken_strict
    (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (h_strict : s.db.config.rejectUnknownSteps = true) :
    (s.feedToken pos tk).db.config.rejectUnknownSteps = true := by
  simp [h_strict]

/-- Successful `feed` preserves ProofGhost. -/
theorem feed_maintains_ghost
    (base : Nat) (arr : ByteArray) (i : Nat) (rs : ParserState.FeedState) (s : ParserState)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_inv : ParserStateInv s)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_success : (s.feed base arr i rs).db.error? = none) :
    ProofGhost (s.feed base arr i rs).db (s.feed base arr i rs).tokp := by
  refine Nat.rec
    (motive := fun m =>
      ∀ i rs (s : ParserState),
        arr.size - i = m →
        ProofGhost s.db s.tokp →
        ParserStateInv s →
        s.db.error? = none →
        s.db.config.allowDuplicateFloat = false →
        s.db.config.rejectUnknownSteps = true →
        (s.feed base arr i rs).db.error? = none →
        ProofGhost (s.feed base arr i rs).db (s.feed base arr i rs).tokp)
    ?base ?step (arr.size - i) i rs s rfl h_ghost h_inv h_no_err h_no_dup h_strict h_success
  · -- Base case: ¬ i < arr.size → feed does nothing
    intro i rs s hs h_ghost h_inv _h_no_err _h_no_dup _h_strict _h_success
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.feed
    simp [hi]
    exact h_ghost
  · -- Inductive step
    intro m ih i rs s hs h_ghost h_inv h_no_err h_no_dup h_strict h_success
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi'); omega
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    let c := arr[i]
    by_cases h_ws : isWhitespace c
    · cases rs with
      | ws =>
        let s1 : ParserState := s.updateLine (base + i) c
        have h_ghost1 : ProofGhost s1.db s1.tokp := by
          simp [s1, updateLine_tokp]; exact h_ghost
        have h_inv1 : ParserStateInv s1 := by
          simpa [ParserStateInv, s1] using h_inv
        have h_no_err1 : s1.db.error? = none := by
          simpa [s1] using h_no_err
        have h_no_dup1 : s1.db.config.allowDuplicateFloat = false := by
          simpa [s1] using h_no_dup
        have h_strict1 : s1.db.config.rejectUnknownSteps = true := by
          simpa [s1] using h_strict
        have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
          unfold ParserState.feed at h_success
          have h_ws' : isWhitespace arr[i] = true := h_ws
          simpa [hi, h_ws', s1] using h_success
        have h_rec := ih (i + 1) .ws s1 hs' h_ghost1 h_inv1 h_no_err1 h_no_dup1 h_strict1 h_success_rec
        unfold ParserState.feed
        have h_ws' : isWhitespace arr[i] = true := h_ws
        simpa [hi, h_ws', s1] using h_rec
      | token ot =>
        cases ot with
        | this off =>
          let s0 := s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
          let s1 : ParserState := s0.updateLine (base + i) arr[i]
          cases h_err : s1.db.error? with
          | some intr =>
            have h_err0 : s0.db.error? = some intr := by simpa [s1] using h_err
            have h_bad : (s.feed base arr i (.token (.this off))).db.error? ≠ none := by
              unfold ParserState.feed
              have h_ws' : isWhitespace arr[i] = true := h_ws
              simp [hi, h_ws', s0, h_err0]
            exact (h_bad h_success).elim
          | none =>
            have h_tok_ok : s0.db.error? = none := by simpa [s1] using h_err
            have h_ghost0 : ProofGhost s0.db s0.tokp :=
              feedToken_maintains_ghost s (base + off) (ByteSlice.mk arr off (i - off))
                h_ghost h_inv h_no_err h_strict h_tok_ok
            have h_inv0 : ParserStateInv s0 :=
              feedToken_maintains_stateInv s (base + off) (ByteSlice.mk arr off (i - off))
                h_inv h_no_err h_no_dup h_tok_ok
            have h_ghost1 : ProofGhost s1.db s1.tokp := by
              simp [s1, updateLine_tokp]; exact h_ghost0
            have h_inv1 : ParserStateInv s1 := by simpa [ParserStateInv, s1] using h_inv0
            have h_no_err1 : s1.db.error? = none := by simpa [s1] using h_err
            have h_no_dup1 : s1.db.config.allowDuplicateFloat = false := by
              have := ParserState.feedToken_db_config s (base + off) (ByteSlice.mk arr off (i - off))
              simpa [s1, s0, this] using h_no_dup
            have h_strict1 : s1.db.config.rejectUnknownSteps = true := by
              have := ParserState.feedToken_db_config s (base + off) (ByteSlice.mk arr off (i - off))
              simpa [s1, s0, this] using h_strict
            have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
              unfold ParserState.feed at h_success
              have h_ws' : isWhitespace arr[i] = true := h_ws
              have h_err0 : s0.db.error? = none := by simpa [s1] using h_err
              simp [hi, h_ws', s0, h_err0] at h_success; exact h_success
            have h_rec := ih (i + 1) .ws s1 hs' h_ghost1 h_inv1 h_no_err1 h_no_dup1 h_strict1 h_success_rec
            unfold ParserState.feed
            have h_ws' : isWhitespace arr[i] = true := h_ws
            have h_err0 : s0.db.error? = none := by simpa [s1] using h_err
            simpa [hi, h_ws', s0, s1, h_err0] using h_rec
        | old base' off arr' =>
          let s0 := s.feedToken (base' + off)
            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
          let s1 : ParserState := s0.updateLine (base + i) arr[i]
          cases h_err : s1.db.error? with
          | some intr =>
            have h_err0 : s0.db.error? = some intr := by simpa [s1] using h_err
            have h_bad :
                (s.feed base arr i (.token (.old base' off arr'))).db.error? ≠ none := by
              unfold ParserState.feed
              have h_ws' : isWhitespace arr[i] = true := h_ws
              simp [hi, h_ws', s0, h_err0]
            exact (h_bad h_success).elim
          | none =>
            have h_tok_ok : s0.db.error? = none := by simpa [s1] using h_err
            have h_ghost0 : ProofGhost s0.db s0.tokp :=
              feedToken_maintains_ghost s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
                h_ghost h_inv h_no_err h_strict h_tok_ok
            have h_inv0 : ParserStateInv s0 :=
              feedToken_maintains_stateInv s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
                h_inv h_no_err h_no_dup h_tok_ok
            have h_ghost1 : ProofGhost s1.db s1.tokp := by
              simp [s1, updateLine_tokp]; exact h_ghost0
            have h_inv1 : ParserStateInv s1 := by simpa [ParserStateInv, s1] using h_inv0
            have h_no_err1 : s1.db.error? = none := by simpa [s1] using h_err
            have h_no_dup1 : s1.db.config.allowDuplicateFloat = false := by
              have := ParserState.feedToken_db_config s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
              simpa [s1, s0, this] using h_no_dup
            have h_strict1 : s1.db.config.rejectUnknownSteps = true := by
              have := ParserState.feedToken_db_config s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
              simpa [s1, s0, this] using h_strict
            have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
              unfold ParserState.feed at h_success
              have h_ws' : isWhitespace arr[i] = true := h_ws
              have h_err0 : s0.db.error? = none := by simpa [s1] using h_err
              simp [hi, h_ws', s0, h_err0] at h_success; exact h_success
            have h_rec := ih (i + 1) .ws s1 hs' h_ghost1 h_inv1 h_no_err1 h_no_dup1 h_strict1 h_success_rec
            unfold ParserState.feed
            have h_ws' : isWhitespace arr[i] = true := h_ws
            have h_err0 : s0.db.error? = none := by simpa [s1] using h_err
            simpa [hi, h_ws', s0, s1, h_err0] using h_rec
    · -- Non-whitespace: just update FeedState, no db/tokp change
      cases rs with
      | ws =>
        have h_success_rec : (s.feed base arr (i + 1) (.token (.this i))).db.error? = none := by
          unfold ParserState.feed at h_success
          have h_ws' : isWhitespace arr[i] = false := by simpa [c] using h_ws
          simpa [hi, h_ws'] using h_success
        have h_rec := ih (i + 1) (.token (.this i)) s hs' h_ghost h_inv h_no_err h_no_dup h_strict h_success_rec
        unfold ParserState.feed
        have h_ws' : isWhitespace arr[i] = false := by simpa [c] using h_ws
        simpa [hi, h_ws'] using h_rec
      | token ot =>
        have h_success_rec : (s.feed base arr (i + 1) (.token ot)).db.error? = none := by
          unfold ParserState.feed at h_success
          have h_ws' : isWhitespace arr[i] = false := by simpa [c] using h_ws
          simpa [hi, h_ws'] using h_success
        have h_rec := ih (i + 1) (.token ot) s hs' h_ghost h_inv h_no_err h_no_dup h_strict h_success_rec
        unfold ParserState.feed
        have h_ws' : isWhitespace arr[i] = false := by simpa [c] using h_ws
        simpa [hi, h_ws'] using h_rec

/-- Successful `feed` produces prefix-provable events at every feedToken call site.
    Same induction as `feed_maintains_ghost`; at each feedToken call,
    `eventProvableAt_of_ghost_inv` gives `EventProvableAt`. -/
theorem feed_events_provable
    (base : Nat) (arr : ByteArray) (i : Nat) (rs : ParserState.FeedState) (s : ParserState)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_inv : ParserStateInv s)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_success : (s.feed base arr i rs).db.error? = none) :
    AllFeedEventsProvable base arr i rs s := by
  refine Nat.rec
    (motive := fun m =>
      ∀ i rs (s : ParserState),
        arr.size - i = m →
        ProofGhost s.db s.tokp →
        ParserStateInv s →
        s.db.error? = none →
        s.db.config.allowDuplicateFloat = false →
        s.db.config.rejectUnknownSteps = true →
        (s.feed base arr i rs).db.error? = none →
        AllFeedEventsProvable base arr i rs s)
    ?base ?step (arr.size - i) i rs s rfl h_ghost h_inv h_no_err h_no_dup h_strict h_success
  · -- Base case: ¬ i < arr.size → AllFeedEventsProvable = True
    intro i rs s hs _h_ghost _h_inv _h_no_err _h_no_dup _h_strict _h_success
    have hi : ¬ i < arr.size := by
      intro hi; have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi; simp [hs] at hpos
    unfold AllFeedEventsProvable; simp [hi]
  · -- Inductive step
    intro m ih i rs s hs h_ghost h_inv h_no_err h_no_dup h_strict h_success
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi'); omega
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    let c := arr[i]
    by_cases h_ws : isWhitespace c
    · -- Whitespace
      have h_ws' : isWhitespace arr[i] = true := h_ws
      cases rs with
      | ws =>
        let s1 : ParserState := s.updateLine (base + i) c
        have h_ghost1 : ProofGhost s1.db s1.tokp := by
          simp [s1, updateLine_tokp]; exact h_ghost
        have h_inv1 : ParserStateInv s1 := by simpa [ParserStateInv, s1] using h_inv
        have h_no_err1 : s1.db.error? = none := by simpa [s1] using h_no_err
        have h_no_dup1 : s1.db.config.allowDuplicateFloat = false := by simpa [s1] using h_no_dup
        have h_strict1 : s1.db.config.rejectUnknownSteps = true := by simpa [s1] using h_strict
        have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
          unfold ParserState.feed at h_success; simpa [hi, h_ws', s1] using h_success
        have h_rec := ih (i + 1) .ws s1 hs' h_ghost1 h_inv1 h_no_err1 h_no_dup1 h_strict1 h_success_rec
        unfold AllFeedEventsProvable; simp only [hi, ↓reduceDIte, h_ws', ↓reduceIte]
        exact h_rec
      | token ot =>
        cases ot with
        | this off =>
          let s0 := s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
          let s1 : ParserState := s0.updateLine (base + i) arr[i]
          cases h_err : s1.db.error? with
          | some intr =>
            have h_err0 : s0.db.error? = some intr := by simpa [s1] using h_err
            have h_bad : (s.feed base arr i (.token (.this off))).db.error? ≠ none := by
              unfold ParserState.feed; simp [hi, h_ws', s0, h_err0]
            exact (h_bad h_success).elim
          | none =>
            have h_tok_ok : s0.db.error? = none := by simpa [s1] using h_err
            have h_event : EventProvableAt s :=
              eventProvableAt_of_ghost_inv s h_ghost h_inv h_no_err
            have h_ghost0 : ProofGhost s0.db s0.tokp :=
              feedToken_maintains_ghost s (base + off) (ByteSlice.mk arr off (i - off))
                h_ghost h_inv h_no_err h_strict h_tok_ok
            have h_inv0 : ParserStateInv s0 :=
              feedToken_maintains_stateInv s (base + off) (ByteSlice.mk arr off (i - off))
                h_inv h_no_err h_no_dup h_tok_ok
            have h_ghost1 : ProofGhost s1.db s1.tokp := by
              simp [s1, updateLine_tokp]; exact h_ghost0
            have h_inv1 : ParserStateInv s1 := by simpa [ParserStateInv, s1] using h_inv0
            have h_no_err1 : s1.db.error? = none := by simpa [s1] using h_err
            have h_no_dup1 : s1.db.config.allowDuplicateFloat = false := by
              have := ParserState.feedToken_db_config s (base + off) (ByteSlice.mk arr off (i - off))
              simpa [s1, s0, this] using h_no_dup
            have h_strict1 : s1.db.config.rejectUnknownSteps = true := by
              have := ParserState.feedToken_db_config s (base + off) (ByteSlice.mk arr off (i - off))
              simpa [s1, s0, this] using h_strict
            have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
              unfold ParserState.feed at h_success
              have h_err0 : s0.db.error? = none := by simpa [s1] using h_err
              simp [hi, h_ws', s0, h_err0] at h_success; exact h_success
            have h_rec := ih (i + 1) .ws s1 hs' h_ghost1 h_inv1 h_no_err1 h_no_dup1 h_strict1 h_success_rec
            unfold AllFeedEventsProvable; simp only [hi, ↓reduceDIte, h_ws', ↓reduceIte]
            refine ⟨h_event, ?_⟩
            show if s1.db.error? = none then
              AllFeedEventsProvable base arr (i + 1) .ws s1 else True
            rw [if_pos h_err]; exact h_rec
        | old base' off arr' =>
          let s0 := s.feedToken (base' + off)
            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
          let s1 : ParserState := s0.updateLine (base + i) arr[i]
          cases h_err : s1.db.error? with
          | some intr =>
            have h_err0 : s0.db.error? = some intr := by simpa [s1] using h_err
            have h_bad :
                (s.feed base arr i (.token (.old base' off arr'))).db.error? ≠ none := by
              unfold ParserState.feed; simp [hi, h_ws', s0, h_err0]
            exact (h_bad h_success).elim
          | none =>
            have h_tok_ok : s0.db.error? = none := by simpa [s1] using h_err
            have h_event : EventProvableAt s :=
              eventProvableAt_of_ghost_inv s h_ghost h_inv h_no_err
            have h_ghost0 : ProofGhost s0.db s0.tokp :=
              feedToken_maintains_ghost s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
                h_ghost h_inv h_no_err h_strict h_tok_ok
            have h_inv0 : ParserStateInv s0 :=
              feedToken_maintains_stateInv s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
                h_inv h_no_err h_no_dup h_tok_ok
            have h_ghost1 : ProofGhost s1.db s1.tokp := by
              simp [s1, updateLine_tokp]; exact h_ghost0
            have h_inv1 : ParserStateInv s1 := by simpa [ParserStateInv, s1] using h_inv0
            have h_no_err1 : s1.db.error? = none := by simpa [s1] using h_err
            have h_no_dup1 : s1.db.config.allowDuplicateFloat = false := by
              have := ParserState.feedToken_db_config s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
              simpa [s1, s0, this] using h_no_dup
            have h_strict1 : s1.db.config.rejectUnknownSteps = true := by
              have := ParserState.feedToken_db_config s (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
              simpa [s1, s0, this] using h_strict
            have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
              unfold ParserState.feed at h_success
              have h_err0 : s0.db.error? = none := by simpa [s1] using h_err
              simp [hi, h_ws', s0, h_err0] at h_success; exact h_success
            have h_rec := ih (i + 1) .ws s1 hs' h_ghost1 h_inv1 h_no_err1 h_no_dup1 h_strict1 h_success_rec
            unfold AllFeedEventsProvable; simp only [hi, ↓reduceDIte, h_ws', ↓reduceIte]
            refine ⟨h_event, ?_⟩
            show if s1.db.error? = none then
              AllFeedEventsProvable base arr (i + 1) .ws s1 else True
            rw [if_pos h_err]; exact h_rec
    · -- Non-whitespace: no feedToken call, just recurse
      have h_ws' : isWhitespace arr[i] = false := by simpa [c] using h_ws
      cases rs with
      | ws =>
        have h_success_rec : (s.feed base arr (i + 1) (.token (.this i))).db.error? = none := by
          unfold ParserState.feed at h_success; simpa [hi, h_ws'] using h_success
        have h_rec := ih (i + 1) (.token (.this i)) s hs' h_ghost h_inv h_no_err h_no_dup h_strict h_success_rec
        unfold AllFeedEventsProvable; simp only [hi, ↓reduceDIte, h_ws']
        exact h_rec
      | token ot =>
        have h_success_rec : (s.feed base arr (i + 1) (.token ot)).db.error? = none := by
          unfold ParserState.feed at h_success; simpa [hi, h_ws'] using h_success
        have h_rec := ih (i + 1) (.token ot) s hs' h_ghost h_inv h_no_err h_no_dup h_strict h_success_rec
        unfold AllFeedEventsProvable; simp only [hi, ↓reduceDIte, h_ws']
        exact h_rec

/-- Successful `feedAll` preserves ProofGhost. -/
theorem feedAll_maintains_ghost
    (s : ParserState) (base : Nat) (arr : ByteArray)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_inv : ParserStateInv s)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_success : (s.feedAll base arr).db.error? = none) :
    ProofGhost (s.feedAll base arr).db (s.feedAll base arr).tokp := by
  cases h_charp : s.charp with
  | ws =>
    simp [ParserState.feedAll, h_charp] at h_success ⊢
    exact feed_maintains_ghost base arr 0 .ws s h_ghost h_inv h_no_err h_no_dup h_strict h_success
  | token base' tk =>
    let s0 : ParserState := { s with charp := default }
    have h_ghost0 : ProofGhost s0.db s0.tokp := by simpa [s0] using h_ghost
    have h_inv0 : ParserStateInv s0 := by simpa [ParserStateInv, s0] using h_inv
    have h_no_err0 : s0.db.error? = none := by simpa [s0] using h_no_err
    have h_no_dup0 : s0.db.config.allowDuplicateFloat = false := by simpa [s0] using h_no_dup
    have h_strict0 : s0.db.config.rejectUnknownSteps = true := by simpa [s0] using h_strict
    have h_success0 :
        (s0.feed base arr 0 (.token (.old base' tk.start tk.byteArray))).db.error? = none := by
      simpa [ParserState.feedAll, h_charp, s0] using h_success
    have h_ghost_feed := feed_maintains_ghost base arr 0
      (.token (.old base' tk.start tk.byteArray)) s0
      h_ghost0 h_inv0 h_no_err0 h_no_dup0 h_strict0 h_success0
    simpa [ParserState.feedAll, h_charp, s0] using h_ghost_feed

/-! ## Event-lift: feedAll and top-level theorem -/

/-- Successful `feedAll` produces prefix-provable events at every feedToken call site. -/
theorem feedAll_events_provable
    (s : ParserState) (base : Nat) (arr : ByteArray)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_inv : ParserStateInv s)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_success : (s.feedAll base arr).db.error? = none) :
    AllFeedAllEventsProvable base arr s := by
  cases h_charp : s.charp with
  | ws =>
    simp [AllFeedAllEventsProvable, h_charp]
    simp [ParserState.feedAll, h_charp] at h_success
    exact feed_events_provable base arr 0 .ws s h_ghost h_inv h_no_err h_no_dup h_strict h_success
  | token base' tk =>
    simp [AllFeedAllEventsProvable, h_charp]
    let s0 : ParserState := { s with charp := default }
    have h_ghost0 : ProofGhost s0.db s0.tokp := by simpa [s0] using h_ghost
    have h_inv0 : ParserStateInv s0 := by simpa [ParserStateInv, s0] using h_inv
    have h_no_err0 : s0.db.error? = none := by simpa [s0] using h_no_err
    have h_no_dup0 : s0.db.config.allowDuplicateFloat = false := by simpa [s0] using h_no_dup
    have h_strict0 : s0.db.config.rejectUnknownSteps = true := by simpa [s0] using h_strict
    have h_success0 :
        (s0.feed base arr 0 (.token (.old base' tk.start tk.byteArray))).db.error? = none := by
      simpa [ParserState.feedAll, h_charp, s0] using h_success
    have h_events := feed_events_provable base arr 0
      (.token (.old base' tk.start tk.byteArray)) s0
      h_ghost0 h_inv0 h_no_err0 h_no_dup0 h_strict0 h_success0
    simpa [s0] using h_events

open Metamath.ParserOps (done_no_error_implies_db_no_error feedAll_maintains_stateInv) in
/-- **Prefix Provenance Event-Lift**: in a successful `checkBytesCore` run,
    every feedToken finishProof event of the feed loop yields `Spec.Provable`
    in the pre-insertion database, and the same conditional guarantee holds at
    the final `feedAll` state (`EventProvableAt`).

    The second conjunct is *conditional*: nothing here yet constructs the
    concrete event for the trailing token that `done` flushes, so this must not
    be read as proven EOF coverage. -/
theorem checkBytesCore_prefix_provenance (arr : ByteArray) (config : ModeConfig)
    (h_strict : config.rejectUnknownSteps = true)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_success : (checkBytesCore arr config).error? = none) :
    let s₀ : ParserState := { (default : ParserState) with
      db := { (default : DB) with config := config } }
    AllFeedAllEventsProvable 0 arr s₀ ∧
    EventProvableAt (s₀.feedAll 0 arr) := by
  intro s₀
  -- Extract: checkBytesCore success → feedAll output has no error
  have h_feedAll_no_err : (s₀.feedAll 0 arr).db.error? = none := by
    have h_core : (checkBytesCore arr config).error? = none := h_success
    have h_done_ok : ((s₀.feedAll 0 arr).done arr.size).error? = none := by
      show (checkBytesCore arr config).error? = none
      exact h_core
    exact done_no_error_implies_db_no_error (s₀.feedAll 0 arr) arr.size h_done_ok
  -- Initial state properties
  have h_init_ghost : ProofGhost s₀.db s₀.tokp := trivial
  have h_init_inv : ParserStateInv s₀ :=
    Metamath.ParserOps.initState_inv config
  have h_init_no_err : s₀.db.error? = none := rfl
  have h_init_no_dup : s₀.db.config.allowDuplicateFloat = false := h_no_dup
  have h_init_strict : s₀.db.config.rejectUnknownSteps = true := h_strict
  -- Feed events
  have h_feed_events := feedAll_events_provable s₀ 0 arr
    h_init_ghost h_init_inv h_init_no_err h_init_no_dup h_init_strict h_feedAll_no_err
  -- Done flush event
  have h_ghost_out := feedAll_maintains_ghost s₀ 0 arr
    h_init_ghost h_init_inv h_init_no_err h_init_no_dup h_init_strict h_feedAll_no_err
  have h_inv_out := feedAll_maintains_stateInv s₀ 0 arr
    h_init_inv h_init_no_err h_init_no_dup h_feedAll_no_err
  have h_done_event := eventProvableAt_of_ghost_inv (s₀.feedAll 0 arr)
    h_ghost_out h_inv_out h_feedAll_no_err
  exact ⟨h_feed_events, h_done_event⟩

/-- Wrapper: `checkBytes` success implies the same prefix-provenance event-lift
    established for `checkBytesCore`. -/
theorem checkBytes_prefix_provenance (arr : ByteArray) (config : ModeConfig)
    (h_strict : config.rejectUnknownSteps = true)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_success : (checkBytes arr config).error? = none) :
    let s₀ : ParserState := { (default : ParserState) with
      db := { (default : DB) with config := config } }
    AllFeedAllEventsProvable 0 arr s₀ ∧
    EventProvableAt (s₀.feedAll 0 arr) := by
  have h_core_success : (checkBytesCore arr config).error? = none := by
    by_cases h_core : (checkBytesCore arr config).error? = none
    · exact h_core
    · unfold checkBytes at h_success
      simp [h_core] at h_success
  exact checkBytesCore_prefix_provenance arr config h_strict h_no_dup h_core_success

/-- Core eliminator at the **final** `feedAll` state only; see the caveat on
`checkBytes_finalState_finishProofEvent_prefix_provable`. -/
theorem checkBytesCore_finalState_finishProofEvent_prefix_provable
    (arr : ByteArray) (config : ModeConfig)
    (h_strict : config.rejectUnknownSteps = true)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_success : (checkBytesCore arr config).error? = none) :
    let s₀ : ParserState := { (default : ParserState) with
      db := { (default : DB) with config := config } }
    ∀ (pos : Nat) (tk : ByteSlice) (pr : ProofState),
      FinishProofEvent (s₀.feedAll 0 arr) pos tk pr →
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase (s₀.feedAll 0 arr).db = some Γ ∧
        toFrame (s₀.feedAll 0 arr).db (s₀.feedAll 0 arr).db.frame = some fr ∧
        Spec.Provable Γ fr (toExpr pr.fmla) := by
  intro s₀ pos tk pr h_evt
  exact (checkBytesCore_prefix_provenance arr config h_strict h_no_dup h_success).2 pos tk pr h_evt

/-! ## Event to stored entry

The fold-wide result quantifies over finish-proof *events*.  This section links an
event to the database entry it creates, so the guarantee can be read per stored
assertion rather than per event. -/

/-! ## Registry-invariance toolkit

Mirrors the `_db_config` family: each parser operation that cannot create an
assertion is shown to leave `db.objects` untouched, so origin coverage can
dismiss its mode outright. -/

/-- `withAt` never touches the registry: it either passes the state through or
rewrites an error message. -/
theorem withAt_objects (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).db.objects = (f ()).db.objects := by
  unfold ParserState.withAt
  cases h_err : (f ()).db.error? with
  | none => simp [h_err]
  | some it =>
      cases it with
      | mk e idx => cases e <;> simp [h_err, ParserState.withDB]

@[simp] theorem mkErrorFromEvidence_objects (s : ParserState) (pos : Pos)
    (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).db.objects = s.db.objects := by
  simp [ParserState.mkErrorFromEvidence,
    ParserState.withDB]

@[simp] theorem djvars_loop_aux_objects (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String) (i : Nat) :
    (ParserState.djvars_loop_aux arr s pos tk i).db.objects = s.db.objects := by
  refine Nat.rec (motive := fun m => ∀ i (s : ParserState), arr.size - i = m →
      (ParserState.djvars_loop_aux arr s pos tk i).db.objects = s.db.objects)
    ?base ?step (arr.size - i) i s rfl
  · intro i s hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    simp [ParserState.djvars_loop_aux, hi]
  · intro m ih i s hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        have : False := by
          have hs' := hs
          simp [hz] at hs'
        exact this.elim
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    unfold ParserState.djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    split
    · simp
    · rw [ih (i + 1) _ hs']
      simp [ParserState.withDB, DB.withDJ, DB.withFrame]

@[simp] theorem djvars_loop_objects (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String) :
    (ParserState.djvars_loop arr s pos tk).db.objects = s.db.objects := by
  unfold ParserState.djvars_loop
  cases h_gate : s.db.djvarsScopeViolation? tk with
  | none => simp
  | some err => simp

@[simp] theorem resumeThm_objects (s : ParserState) (pos : Pos) (l : String)
    (fmla : Verify.Formula) (fr : Verify.Frame) :
    (s.resumeThm pos l fmla fr).db.objects = s.db.objects := by
  simp [ParserState.resumeThm]

@[simp] theorem feedProof_objects (s : ParserState) (tk : ByteSlice)
    (pr : ProofState) :
    (s.feedProof tk pr).db.objects = s.db.objects := by
  unfold ParserState.feedProof
  rw [withAt_objects]
  split <;> simp

@[simp] theorem DB_mkErrorFromEvidence_objects (db : DB) (pos : Pos)
    (ev : ErrorEvidence) :
    (db.mkErrorFromEvidence pos ev).objects = db.objects := by
  simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]

@[simp] theorem pushScope_objects (db : DB) : db.pushScope.objects = db.objects := rfl

@[simp] theorem popScope_objects (db : DB) (pos : Pos) :
    (DB.popScope pos db).objects = db.objects := by
  unfold DB.popScope
  split
  · rfl
  · rfl

@[simp] theorem requestInclude_objects (s : ParserState) (resume : TokenParser)
    (path : String) :
    (s.requestInclude resume path).db.objects = s.db.objects := rfl

@[simp] theorem label_objects (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    (s.label pos tk).db.objects = s.db.objects := by
  unfold ParserState.label
  repeat' split
  all_goals rfl

/-- The registry decides `find?`, so registry equality transports emptiness. -/
theorem no_new_assert_of_objects_eq (s' s : ParserState) (n : String)
    (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h : s'.db.objects = s.db.objects) (h_old : s.db.find? n = none) :
    s'.db.find? n ≠ some (.assert f fr lbl) := by
  intro h_new
  rw [show s'.db.find? n = s.db.find? n from by simp [DB.find?, h], h_old] at h_new
  cases h_new

theorem withAt_find? (l : String) (g : Unit → ParserState) (n : String) :
    (ParserState.withAt l g).db.find? n = (g ()).db.find? n := by
  simp [DB.find?, withAt_objects]

/-! ### Per-mode registry preservation

One lemma per token-parser mode that cannot create an assertion: each shows
`feedToken` leaves `db.objects` untouched there, prefix branches (`$(`, `$[`)
included. -/

theorem feedToken_start_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_tokp : s.tokp = .start) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  simp only [h_tokp]
  repeat' split
  all_goals first | rfl | simp [ParserState.withDB]

theorem feedToken_label_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (q : Pos) (lab : String) (h_tokp : s.tokp = .label q lab) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  simp only [h_tokp]
  repeat' split
  all_goals rfl

theorem feedToken_includePath_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (resume : TokenParser) (q : Pos) (h_tokp : s.tokp = .includePath resume q) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  simp only [h_tokp]
  repeat' split
  all_goals rfl

theorem feedToken_includeClose_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (resume : TokenParser) (q : Pos) (path : String)
    (h_tokp : s.tokp = .includeClose resume q path) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  simp only [h_tokp]
  repeat' split
  all_goals rfl

theorem feedToken_comment_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (q : TokenParser) (h_tokp : s.tokp = .comment q) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  simp only [h_tokp]
  repeat' split
  all_goals rfl

theorem feedToken_djvars_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array String) (h_tokp : s.tokp = .djvars arr) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken ParserState.withMath
  simp only [h_tokp]
  repeat' split
  all_goals first | rfl | simp

theorem feedToken_math_nondelim_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser)
    (h_tokp : s.tokp = .math arr p)
    (h_delim : tk.eqArray p.k.delim = false) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken ParserState.withMath
  simp only [h_tokp]
  repeat' split
  all_goals first | rfl | simp_all

theorem feedToken_proof_nondot_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (pr : ProofState) (h_tokp : s.tokp = .proof pr)
    (h_ne : tk.eqArray "$.".toAscii = false) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  simp only [h_tokp]
  repeat' split
  all_goals first | rfl | simp_all

/-! ### The two inserting modes that are not origins -/

theorem feedToken_const_no_new_assert (s : ParserState) (i : Nat) (tk : ByteSlice)
    (seen : Bool) (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_tokp : s.tokp = .const seen) (h_old : s.db.find? n = none) :
    (s.feedToken i tk).db.find? n ≠ some (.assert f fr lbl) := by
  unfold ParserState.feedToken ParserState.sym ParserState.withMath
  simp only [h_tokp]
  repeat' split
  all_goals
    try (exact no_new_assert_of_objects_eq _ s n f fr lbl rfl h_old)
  all_goals
    simp only [ParserState.withDB]
    exact ParserOps.insert_nonassert_no_new_assert _ _ _ _
      (fun _ _ _ h => Object.noConfusion h) n f fr lbl h_old

theorem feedToken_var_no_new_assert (s : ParserState) (i : Nat) (tk : ByteSlice)
    (seen : Bool) (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_tokp : s.tokp = .var seen) (h_old : s.db.find? n = none) :
    (s.feedToken i tk).db.find? n ≠ some (.assert f fr lbl) := by
  unfold ParserState.feedToken ParserState.sym ParserState.withMath
  simp only [h_tokp]
  repeat' split
  all_goals
    try (exact no_new_assert_of_objects_eq _ s n f fr lbl rfl h_old)
  all_goals
    simp only [ParserState.withDB]
    exact ParserOps.insert_nonassert_no_new_assert _ _ _ _
      (fun _ _ _ h => Object.noConfusion h) n f fr lbl h_old

/-! ### The statement-closing dispatcher, non-`$a` kinds -/

theorem feedTokens_nonax_no_new_assert (s : ParserState) (arr : Array Verify.Sym)
    (k : TokensKind) (pos : Pos) (l : String)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_k : k ≠ TokensKind.ax) (h_old : s.db.find? n = none) :
    (s.feedTokens arr ⟨k, pos, l⟩).db.find? n ≠ some (.assert f fr lbl) := by
  intro h_new
  unfold ParserState.feedTokens at h_new
  rw [withAt_find?] at h_new
  cases k with
  | ax => exact h_k rfl
  | float =>
      simp only [Id.run] at h_new
      repeat' split at h_new
      all_goals
        first
          | exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl rfl h_old)
          | (have h_new' : (s.db.insertHyp pos l false arr).find? n
                 = some (.assert f fr lbl) := by
               simpa [ParserState.withDB, DB.find?] using h_new
             exact ParserOps.insertHyp_no_new_assert s.db pos l false arr
               n f fr lbl h_old h_new')
  | ess =>
      simp only [Id.run] at h_new
      repeat' split at h_new
      all_goals
        first
          | exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl rfl h_old)
          | (have h_new' : (s.db.insertHyp pos l true arr).find? n
                 = some (.assert f fr lbl) := by
               simpa [ParserState.withDB, DB.find?] using h_new
             exact ParserOps.insertHyp_no_new_assert s.db pos l true arr
               n f fr lbl h_old h_new')
  | thm =>
      simp only [Id.run] at h_new
      repeat' split at h_new
      all_goals
        exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl rfl h_old)

/-- The global `$(` prefix: in any non-comment mode it only pushes comment mode. -/
theorem feedToken_open_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_nc : ∀ q, s.tokp ≠ .comment q)
    (h_open : tk.eqArray "$(".toAscii = true) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  cases h_tokp : s.tokp <;>
    first
      | exact absurd h_tokp (h_nc _)
      | simp [h_open]

/-- The global `$[` prefix: in any non-comment mode it only gates or switches
to include-path mode. -/
theorem feedToken_incl_objects (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_nc : ∀ q, s.tokp ≠ .comment q)
    (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = true) :
    (s.feedToken i tk).db.objects = s.db.objects := by
  unfold ParserState.feedToken
  cases h_tokp : s.tokp <;>
    first
      | exact absurd h_tokp (h_nc _)
      | (simp only [h_open, h_incl, Bool.false_eq_true, if_false, if_true]
         repeat' split
         all_goals rfl)

/-! ## Assertion origins

Exactly two runtime paths insert an `.assert`: the `$.` closing a `$a`, which
routes `feedTokens` to `insertAxiom`, and the `$.` closing a `$p`, which routes
`feedToken` to `finishProof`.  These definitions name the two so that a later
classification cannot silently omit one. -/

/-- The `$.` that closes a `$a`: math-accumulation mode with kind `.ax`, on the
statement's terminator, completing without error. -/
def AxiomFinishEvent (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser) : Prop :=
  s.tokp = .math arr p ∧
  p.k = TokensKind.ax ∧
  tk.eqArray "$(".toAscii = false ∧
  tk.eqArray "$[".toAscii = false ∧
  tk.eqArray p.k.delim = true ∧
  (s.feedToken i tk).db.error? = none

/-- An axiom finish dispatches through `feedTokens`, whose `.ax` branch is the
only `insertAxiom` call reachable from token dispatch. -/
theorem axiomFinishEvent_feedToken_eq (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser) (h : AxiomFinishEvent s i tk arr p) :
    s.feedToken i tk = s.feedTokens arr p := by
  obtain ⟨h_tokp, _, h_open, h_incl, h_delim, _⟩ := h
  simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_delim]

/-- `withAt` only rewrites an error message, so on an error-free result it leaves
the database alone. -/
theorem withAt_db_of_no_error (l : String) (f : Unit → ParserState)
    (h : (ParserState.withAt l f).db.error? = none) :
    (ParserState.withAt l f).db = (f ()).db := by
  unfold ParserState.withAt at h ⊢
  cases h_err : (f ()).db.error? with
  | none => simp [h_err]
  | some it =>
      cases it with
      | mk e idx =>
          -- only the `.error` payload triggers the message rewrite; the other
          -- interrupt payloads fall through untouched
          cases e <;> simp [h_err, ParserState.withDB] at h ⊢

/-- Exact payload of an axiom finish: the transition is `insertAxiom` on the
statement's own label and accumulated formula. -/
theorem axiomFinishEvent_inserts_axiom (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser)
    (h : AxiomFinishEvent s i tk arr p)
    (h_head : Formula.hasConstHead arr = true) :
    (s.feedToken i tk).db = s.db.insertAxiom p.pos p.label arr := by
  have h_ok := h.2.2.2.2.2
  have h_eq := axiomFinishEvent_feedToken_eq s i tk arr p h
  rw [h_eq] at h_ok ⊢
  have h_kind := h.2.1
  cases p with
  | mk k pos l =>
      subst h_kind
      rw [show ParserState.feedTokens s arr ⟨TokensKind.ax, pos, l⟩
            = ParserState.withAt l (fun _ => Id.run do
                unless Formula.hasConstHead arr do
                  return s.mkErrorFromEvidence pos (.scopeDecl .firstSymbolNotConstant)
                let s := s.withDB fun db => db.insertAxiom pos l arr
                pure { s with tokp := .start }) from rfl] at h_ok ⊢
      rw [withAt_db_of_no_error l _ h_ok]
      simp [Id.run, h_head, ParserState.withDB]

/-- The two origins are disjoint: a token cannot close a `$a` and a `$p` at once,
because the parser is in only one mode. -/
theorem axiomFinish_finishProof_disjoint
    (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser) (pr : ProofState)
    (h_ax : AxiomFinishEvent s i tk arr p) (h_th : FinishProofEvent s i tk pr) :
    False := by
  have h1 : s.tokp = .math arr p := h_ax.1
  have h2 : s.tokp = .proof pr := h_th.1
  rw [h1] at h2
  cases h2

/-- `feedTokens` extends the registry monotonically, in every statement kind. -/
theorem feedTokens_find?_mono (s : ParserState) (arr : Array Verify.Sym)
    (k : TokensKind) (pos : Pos) (l : String)
    (n : String) (o : Object) (h : s.db.find? n = some o) :
    (s.feedTokens arr ⟨k, pos, l⟩).db.find? n = some o := by
  unfold ParserState.feedTokens
  rw [withAt_find?]
  cases k <;>
    simp only [Id.run] <;>
    repeat' split
  all_goals
    first
      | exact h
      | (show _ = some o
         simp only [ParserState.withDB, DB.find?]
         exact h)
      | (simp only [ParserState.withDB, DB.find?]
         first
           | exact h
           | exact ParserOps.insertHyp_find?_mono _ _ _ _ _ n o h
           | exact ParserOps.insertAxiom_find?_mono _ _ _ _ n o h)

/-- `finishProof` extends the registry monotonically. -/
theorem finishProof_find?_mono (s : ParserState) (pr : ProofState)
    (n : String) (o : Object) (h : s.db.find? n = some o) :
    (s.finishProof pr).db.find? n = some o := by
  cases pr with
  | mk pos l fmla fr heap stack ptp inc =>
      unfold ParserState.finishProof
      rw [withAt_find?]
      simp only [Id.run]
      repeat' split
      all_goals
        first
          | exact h
          | (show _ = some o
             simp only [ParserState.withDB, DB.find?]
             exact h)
          | (simp only [ParserState.withDB, DB.find?]
             exact ParserOps.insert_find?_mono _ _ _ _ n o h)
          | (simp only [ParserState.withDB, DB.find?, DB.recordIncomplete]
             split <;> exact ParserOps.insert_find?_mono _ _ _ _ n o h)

/-- `feedToken` extends the registry monotonically: no transition removes or
overwrites an existing entry. -/
theorem feedToken_find?_mono (s : ParserState) (i : Nat) (tk : ByteSlice)
    (n : String) (o : Object) (h : s.db.find? n = some o) :
    (s.feedToken i tk).db.find? n = some o := by
  have h_of_objects : ∀ s' : ParserState, s'.db.objects = s.db.objects →
      s'.db.find? n = some o := by
    intro s' h_eq
    show s'.db.objects[n]? = some o
    rw [h_eq]
    exact h
  cases h_tokp : s.tokp with
  | comment q => exact h_of_objects _ (feedToken_comment_objects s i tk q h_tokp)
  | start => exact h_of_objects _ (feedToken_start_objects s i tk h_tokp)
  | label q lab => exact h_of_objects _ (feedToken_label_objects s i tk q lab h_tokp)
  | includePath r q => exact h_of_objects _ (feedToken_includePath_objects s i tk r q h_tokp)
  | includeClose r q pth =>
      exact h_of_objects _ (feedToken_includeClose_objects s i tk r q pth h_tokp)
  | djvars arr => exact h_of_objects _ (feedToken_djvars_objects s i tk arr h_tokp)
  | const seen =>
      unfold ParserState.feedToken ParserState.sym ParserState.withMath
      simp only [h_tokp]
      repeat' split
      all_goals
        first
          | exact h
          | (show _ = some o
             simp only [ParserState.withDB, DB.find?]
             exact h)
          | (simp only [ParserState.withDB, DB.find?]
             exact ParserOps.insert_find?_mono _ _ _ _ n o h)
  | var seen =>
      unfold ParserState.feedToken ParserState.sym ParserState.withMath
      simp only [h_tokp]
      repeat' split
      all_goals
        first
          | exact h
          | (show _ = some o
             simp only [ParserState.withDB, DB.find?]
             exact h)
          | (simp only [ParserState.withDB, DB.find?]
             exact ParserOps.insert_find?_mono _ _ _ _ n o h)
  | math arr p =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact h_of_objects _ (feedToken_open_objects s i tk h_nc h_open)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact h_of_objects _ (feedToken_incl_objects s i tk h_nc h_open' h_incl)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_delim : tk.eqArray p.k.delim = true
          · have h_eq : s.feedToken i tk = s.feedTokens arr p := by
              simp [ParserState.feedToken, h_tokp, h_open', h_incl', h_delim]
            rw [h_eq]
            cases p with
            | mk k ppos plab => exact feedTokens_find?_mono s arr k ppos plab n o h
          · have h_delim' : tk.eqArray p.k.delim = false := by simpa using h_delim
            exact h_of_objects _
              (feedToken_math_nondelim_objects s i tk arr p h_tokp h_delim')
  | proof pr =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact h_of_objects _ (feedToken_open_objects s i tk h_nc h_open)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact h_of_objects _ (feedToken_incl_objects s i tk h_nc h_open' h_incl)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_dot : tk.eqArray "$.".toAscii = true
          · have h_eq : s.feedToken i tk
                = ({ s with tokp := default } : ParserState).finishProof pr := by
              simp [ParserState.feedToken, h_tokp, h_open', h_incl', h_dot]
            rw [h_eq]
            exact finishProof_find?_mono _ pr n o h
          · have h_dot' : tk.eqArray "$.".toAscii = false := by simpa using h_dot
            exact h_of_objects _
              (feedToken_proof_nondot_objects s i tk pr h_tokp h_dot')

/-- `withAt` neither creates nor clears errors; it only rewrites the message. -/
theorem withAt_error?_none_iff (l : String) (g : Unit → ParserState) :
    (ParserState.withAt l g).db.error? = none ↔ (g ()).db.error? = none := by
  unfold ParserState.withAt
  cases h_err : (g ()).db.error? with
  | none => simp [h_err]
  | some it =>
      cases it with
      | mk e idx => cases e <;> simp [h_err, ParserState.withDB]

/-- If `finishProof` created an entry, the transition succeeded: the insert is
the final database operation, and creation forces its success branch. -/
theorem finishProof_new_entry_success (s : ParserState) (pr : ProofState)
    (n : String) (o : Object)
    (h_err0 : s.db.error? = none)
    (h_old : s.db.find? n = none)
    (h_new : (s.finishProof pr).db.find? n = some o) :
    (s.finishProof pr).db.error? = none := by
  cases pr with
  | mk pos l fmla fr heap stack ptp inc =>
      unfold ParserState.finishProof at h_new ⊢
      rw [withAt_find?] at h_new
      rw [withAt_error?_none_iff]
      simp only [Id.run] at h_new ⊢
      revert h_new
      repeat' split
      all_goals
        intro h_new
        first
          | (exfalso
             have h_new' : s.db.find? n = some o := h_new
             rw [h_old] at h_new'
             cases h_new')
          | (show ((s.withDB fun db => (db.insert pos l
                (.assert fmla fr)).recordIncomplete inc l).db).error? = none
             have h_new' : (s.db.insert pos l (.assert fmla fr)).find? n
                 = some o := by
               simpa [ParserState.withDB, DB.find?] using h_new
             have := ParserOps.insert_new_entry_error_eq s.db pos l
               (.assert fmla fr) n o h_old h_new'
             simp only [ParserState.withDB, DB.recordIncomplete]
             split <;> simp [this, h_err0])

/-- If `feedTokens` created an entry, the dispatch succeeded. -/
theorem feedTokens_new_entry_success (s : ParserState) (arr : Array Verify.Sym)
    (k : TokensKind) (pos : Pos) (l : String) (n : String) (o : Object)
    (h_err0 : s.db.error? = none)
    (h_old : s.db.find? n = none)
    (h_new : (s.feedTokens arr ⟨k, pos, l⟩).db.find? n = some o) :
    (s.feedTokens arr ⟨k, pos, l⟩).db.error? = none := by
  unfold ParserState.feedTokens at h_new ⊢
  rw [withAt_find?] at h_new
  rw [withAt_error?_none_iff]
  cases k <;> simp only [Id.run] at h_new ⊢ <;> revert h_new <;> repeat' split
  all_goals
    intro h_new
    first
      | (exfalso
         have h_new' : s.db.find? n = some o := by
           simpa [ParserState.withDB, DB.find?, ParserState.mkErrorFromEvidence,
             ParserState.mkErrorWithEvidence, ParserState.mkError,
             DB.mkErrorWithEvidence, DB.mkError] using h_new
         rw [h_old] at h_new'
         cases h_new')
      | (have h_new' : (s.db.insertHyp pos l false arr).find? n = some o := by
           simpa [ParserState.withDB, DB.find?] using h_new
         have h_eq := ParserOps.insertHyp_new_entry_error_eq s.db pos l false arr
           n o h_err0 h_old h_new'
         simpa [ParserState.withDB] using h_eq)
      | (have h_new' : (s.db.insertHyp pos l true arr).find? n = some o := by
           simpa [ParserState.withDB, DB.find?] using h_new
         have h_eq := ParserOps.insertHyp_new_entry_error_eq s.db pos l true arr
           n o h_err0 h_old h_new'
         simpa [ParserState.withDB] using h_eq)
      | (have h_new' : (s.db.insertAxiom pos l arr).find? n = some o := by
           simpa [ParserState.withDB, DB.find?] using h_new
         have := ParserOps.insertAxiom_new_entry_error_eq s.db pos l arr n o
           h_old h_new'
         simpa [ParserState.withDB, this] using h_err0)

/-- **Creation implies success**: if a `feedToken` transition created an
assertion, the transition raised no error — the insert is the final database
operation on both creating paths. -/
theorem feedToken_new_assert_success (s : ParserState) (i : Nat) (tk : ByteSlice)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_err0 : s.db.error? = none)
    (h_old : s.db.find? n = none)
    (h_new : (s.feedToken i tk).db.find? n = some (.assert f fr lbl)) :
    (s.feedToken i tk).db.error? = none := by
  have h_of_objects : ∀ s' : ParserState, s'.db.objects = s.db.objects →
      s'.db.find? n = some (.assert f fr lbl) → False := by
    intro s' h_eq h_some
    rw [show s'.db.find? n = s.db.find? n from by simp [DB.find?, h_eq],
      h_old] at h_some
    cases h_some
  cases h_tokp : s.tokp with
  | comment q =>
      exact absurd h_new
        (fun h => h_of_objects _ (feedToken_comment_objects s i tk q h_tokp) h)
  | start =>
      exact absurd h_new
        (fun h => h_of_objects _ (feedToken_start_objects s i tk h_tokp) h)
  | label q lab =>
      exact absurd h_new
        (fun h => h_of_objects _ (feedToken_label_objects s i tk q lab h_tokp) h)
  | includePath r q =>
      exact absurd h_new (fun h => h_of_objects _
        (feedToken_includePath_objects s i tk r q h_tokp) h)
  | includeClose r q pth =>
      exact absurd h_new (fun h => h_of_objects _
        (feedToken_includeClose_objects s i tk r q pth h_tokp) h)
  | djvars arr =>
      exact absurd h_new
        (fun h => h_of_objects _ (feedToken_djvars_objects s i tk arr h_tokp) h)
  | const seen =>
      exact absurd h_new
        (feedToken_const_no_new_assert s i tk seen n f fr lbl h_tokp h_old)
  | var seen =>
      exact absurd h_new
        (feedToken_var_no_new_assert s i tk seen n f fr lbl h_tokp h_old)
  | math arr p =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact absurd h_new
          (fun h => h_of_objects _ (feedToken_open_objects s i tk h_nc h_open) h)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact absurd h_new (fun h => h_of_objects _
            (feedToken_incl_objects s i tk h_nc h_open' h_incl) h)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_delim : tk.eqArray p.k.delim = true
          · have h_eq : s.feedToken i tk = s.feedTokens arr p := by
              simp [ParserState.feedToken, h_tokp, h_open', h_incl', h_delim]
            rw [h_eq] at h_new ⊢
            cases p with
            | mk k ppos plab =>
                exact feedTokens_new_entry_success s arr k ppos plab n _
                  h_err0 h_old h_new
          · have h_delim' : tk.eqArray p.k.delim = false := by simpa using h_delim
            exact absurd h_new (fun h => h_of_objects _
              (feedToken_math_nondelim_objects s i tk arr p h_tokp h_delim') h)
  | proof pr =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact absurd h_new
          (fun h => h_of_objects _ (feedToken_open_objects s i tk h_nc h_open) h)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact absurd h_new (fun h => h_of_objects _
            (feedToken_incl_objects s i tk h_nc h_open' h_incl) h)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_dot : tk.eqArray "$.".toAscii = true
          · have h_eq : s.feedToken i tk
                = ({ s with tokp := default } : ParserState).finishProof pr := by
              simp [ParserState.feedToken, h_tokp, h_open', h_incl', h_dot]
            rw [h_eq] at h_new ⊢
            exact finishProof_new_entry_success _ pr n _ h_err0 h_old h_new
          · have h_dot' : tk.eqArray "$.".toAscii = false := by simpa using h_dot
            exact absurd h_new (fun h => h_of_objects _
              (feedToken_proof_nondot_objects s i tk pr h_tokp h_dot') h)

/-- **Origin coverage** — the master classification.

In a successful `feedToken` transition, a newly created `.assert` entry arises
only from the `$.` that closes a `$a` (an `AxiomFinishEvent`) or the `$.` that
closes a `$p` (a `FinishProofEvent`).  Every token-parser mode and sub-branch is
covered; nothing else in the runtime can manufacture an assertion. -/
theorem feedToken_new_assert_classified (s : ParserState) (i : Nat) (tk : ByteSlice)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_old : s.db.find? n = none)
    (h_success : (s.feedToken i tk).db.error? = none)
    (h_new : (s.feedToken i tk).db.find? n = some (.assert f fr lbl)) :
    (∃ arr p, AxiomFinishEvent s i tk arr p)
      ∨ (∃ pr, FinishProofEvent s i tk pr) := by
  cases h_tokp : s.tokp with
  | comment q =>
      exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
        (feedToken_comment_objects s i tk q h_tokp) h_old)
  | start =>
      exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
        (feedToken_start_objects s i tk h_tokp) h_old)
  | label q lab =>
      exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
        (feedToken_label_objects s i tk q lab h_tokp) h_old)
  | includePath resume q =>
      exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
        (feedToken_includePath_objects s i tk resume q h_tokp) h_old)
  | includeClose resume q path =>
      exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
        (feedToken_includeClose_objects s i tk resume q path h_tokp) h_old)
  | djvars arr =>
      exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
        (feedToken_djvars_objects s i tk arr h_tokp) h_old)
  | const seen =>
      exact absurd h_new (feedToken_const_no_new_assert s i tk seen n f fr lbl h_tokp h_old)
  | var seen =>
      exact absurd h_new (feedToken_var_no_new_assert s i tk seen n f fr lbl h_tokp h_old)
  | math arr p =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
          (feedToken_open_objects s i tk h_nc h_open) h_old)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
            (feedToken_incl_objects s i tk h_nc h_open' h_incl) h_old)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_delim : tk.eqArray p.k.delim = true
          · by_cases h_ax : p.k = TokensKind.ax
            · exact Or.inl ⟨arr, p, h_tokp, h_ax, h_open', h_incl', h_delim, h_success⟩
            · exfalso
              have h_eq : s.feedToken i tk = s.feedTokens arr p := by
                simp [ParserState.feedToken, h_tokp, h_open', h_incl', h_delim]
              rw [h_eq] at h_new
              cases p with
              | mk k ppos plab =>
                  exact feedTokens_nonax_no_new_assert s arr k ppos plab
                    n f fr lbl h_ax h_old h_new
          · have h_delim' : tk.eqArray p.k.delim = false := by simpa using h_delim
            exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
              (feedToken_math_nondelim_objects s i tk arr p h_tokp h_delim') h_old)
  | proof pr =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
          (feedToken_open_objects s i tk h_nc h_open) h_old)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
            (feedToken_incl_objects s i tk h_nc h_open' h_incl) h_old)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_dot : tk.eqArray "$.".toAscii = true
          · exact Or.inr ⟨pr, h_tokp, h_open', h_incl', h_dot, h_success⟩
          · have h_dot' : tk.eqArray "$.".toAscii = false := by simpa using h_dot
            exact absurd h_new (no_new_assert_of_objects_eq _ s n f fr lbl
              (feedToken_proof_nondot_objects s i tk pr h_tokp h_dot') h_old)

/-! ## Chronological lift: classification over `feed`, `feedAll` -/

/-- A concrete transition witnessing creation of a fresh `.assert` entry.
The certificate records the local state, token, and classified event; it does
not itself retain a reachability proof from the caller's initial state. -/
def NewAssertCertificate (n : String) (f : Verify.Formula) (fr : Verify.Frame)
    (lbl : String) : Prop :=
  ∃ (s' : ParserState) (j : Nat) (tk : ByteSlice),
    s'.db.find? n = none ∧
    (s'.feedToken j tk).db.error? = none ∧
    (s'.feedToken j tk).db.find? n = some (.assert f fr lbl) ∧
    ((∃ arr p, AxiomFinishEvent s' j tk arr p) ∨ (∃ pr, FinishProofEvent s' j tk pr))

/-- `feed` extends the registry monotonically. -/
theorem feed_find?_mono (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState)
    (n : String) (o : Object) (h : s.db.find? n = some o) :
    (ParserState.feed base arr i rs s).db.find? n = some o := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState),
      s.db.find? n = some o → arr.size - i = m →
      (ParserState.feed base arr i rs s).db.find? n = some o)
    ?base ?step (arr.size - i) i rs s h rfl
  · intro i rs s h hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.feed
    simp only [hi, ↓reduceDIte]
    exact h
  · intro m ih i rs s h hs
    by_cases hi : i < arr.size
    · have hs' : arr.size - (i + 1) = m := by
        simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
      unfold ParserState.feed
      simp only [hi, ↓reduceDIte]
      split
      · -- whitespace
        split
        · exact ih (i + 1) _ _ (by simpa using h) hs'
        · -- buffered token: flush, then either stop on error or recurse
          rename_i ot
          cases ot with
          | this off =>
              have h_step := feedToken_find?_mono s (base + off) (ByteSlice.mk arr off (i - off)) n o h
              split
              · show _ = some o
                simp_all [DB.find?]
              · exact ih (i + 1) _ _ (by simpa using h_step) hs'
          | old base' off arr' =>
              have h_step := feedToken_find?_mono s (base' + off) (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i)) n o h
              split
              · show _ = some o
                simp_all [DB.find?]
              · exact ih (i + 1) _ _ (by simpa using h_step) hs'
      · -- non-whitespace: same db, deeper index
        exact ih (i + 1) _ _ h hs'
    · unfold ParserState.feed
      simp only [hi, ↓reduceDIte]
      exact h

set_option linter.unusedSimpArgs false in
/-- Classification over `feed`: a fresh `.assert` in the result has a local
classified transition witness.  `NewAssertCertificate` does not retain the
recursive reachability path to that witness. -/
theorem feed_new_assert_classified (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_old : s.db.find? n = none)
    (h_success : (ParserState.feed base arr i rs s).db.error? = none)
    (h_new : (ParserState.feed base arr i rs s).db.find? n
      = some (.assert f fr lbl)) :
    NewAssertCertificate n f fr lbl := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState),
      s.db.find? n = none →
      (ParserState.feed base arr i rs s).db.error? = none →
      (ParserState.feed base arr i rs s).db.find? n = some (.assert f fr lbl) →
      arr.size - i = m →
      NewAssertCertificate n f fr lbl)
    ?base ?step (arr.size - i) i rs s h_old h_success h_new rfl
  · intro i rs s h_old h_success h_new hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.feed at h_new
    simp only [hi, ↓reduceDIte] at h_new
    rw [show ({ s with charp := _ } : ParserState).db.find? n = s.db.find? n
      from rfl, h_old] at h_new
    cases h_new
  · intro m ih i rs s h_old h_success h_new hs
    by_cases hi : i < arr.size
    · have hs' : arr.size - (i + 1) = m := by
        simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
      unfold ParserState.feed at h_success h_new
      simp only [hi, ↓reduceDIte] at h_success h_new
      by_cases h_ws : isWhitespace arr[i] = true
      · rw [if_pos h_ws] at h_success h_new
        cases rs with
        | ws =>
            simp only [] at h_success h_new
            exact ih (i + 1) .ws _ (by simpa using h_old) h_success h_new hs'
        | token ot =>
            simp only [] at h_success h_new
            cases ot with
            | this off =>
                simp only [] at h_success h_new
                split at h_success
                · -- error restamp: final error? = some, contradicting success
                  simp at h_success
                · rename_i h_guard
                  simp only [h_guard] at h_new
                  by_cases h_mid : (s.feedToken (base + off)
                      (ByteSlice.mk arr off (i - off))).db.find? n = none
                  · exact ih (i + 1) .ws _ (by simpa using h_mid)
                      h_success (by simpa using h_new) hs'
                  · cases h_val : (s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).db.find? n with
                    | none => exact absurd h_val h_mid
                    | some entry =>
                        have h_persist := feed_find?_mono base arr (i + 1) .ws
                          ((s.feedToken (base + off)
                            (ByteSlice.mk arr off (i - off))).updateLine
                              (base + i) arr[i]) n entry (by simpa using h_val)
                        have h_entry : entry = .assert f fr lbl := by
                          have h_new' := h_new
                          rw [h_persist] at h_new'
                          exact Option.some.inj h_new'
                        subst h_entry
                        have h_step_ok : (s.feedToken (base + off)
                            (ByteSlice.mk arr off (i - off))).db.error? = none := by
                          cases h_e : (s.feedToken (base + off)
                              (ByteSlice.mk arr off (i - off))).db.error? with
                          | none => rfl
                          | some it =>
                              cases it with
                              | mk e idx =>
                                  have h_e' : ((s.feedToken (base + off)
                                      (ByteSlice.mk arr off (i - off))).updateLine
                                        (base + i) arr[i]).db.error?
                                      = some ⟨e, idx⟩ := by simpa using h_e
                                  exact absurd h_e' (h_guard e idx)
                        exact ⟨s, base + off, ByteSlice.mk arr off (i - off),
                          h_old, h_step_ok, h_val,
                          feedToken_new_assert_classified s (base + off) _
                            n f fr lbl h_old h_step_ok h_val⟩
            | old base' off arr' =>
                simp only [] at h_success h_new
                split at h_success
                · simp at h_success
                · rename_i h_guard
                  simp only [h_guard] at h_new
                  by_cases h_mid : (s.feedToken (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))).db.find? n = none
                  · exact ih (i + 1) .ws _ (by simpa using h_mid)
                      h_success (by simpa using h_new) hs'
                  · cases h_val : (s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).db.find? n with
                    | none => exact absurd h_val h_mid
                    | some entry =>
                        have h_persist := feed_find?_mono base arr (i + 1) .ws
                          ((s.feedToken (base' + off)
                            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                              off (arr'.size - off + i))).updateLine
                              (base + i) arr[i]) n entry (by simpa using h_val)
                        have h_entry : entry = .assert f fr lbl := by
                          have h_new' := h_new
                          rw [h_persist] at h_new'
                          exact Option.some.inj h_new'
                        subst h_entry
                        have h_step_ok : (s.feedToken (base' + off)
                            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                              off (arr'.size - off + i))).db.error? = none := by
                          cases h_e : (s.feedToken (base' + off)
                              (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                                off (arr'.size - off + i))).db.error? with
                          | none => rfl
                          | some it =>
                              cases it with
                              | mk e idx =>
                                  have h_e' : ((s.feedToken (base' + off)
                                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size
                                        i false) off (arr'.size - off + i))).updateLine
                                        (base + i) arr[i]).db.error?
                                      = some ⟨e, idx⟩ := by simpa using h_e
                                  exact absurd h_e' (h_guard e idx)
                        exact ⟨s, base' + off,
                          ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                            (arr'.size - off + i),
                          h_old, h_step_ok, h_val,
                          feedToken_new_assert_classified s (base' + off) _
                            n f fr lbl h_old h_step_ok h_val⟩
      · rw [if_neg h_ws] at h_success h_new
        cases rs with
        | ws =>
            simp only [] at h_success h_new
            exact ih (i + 1) _ s h_old h_success h_new hs'
        | token ot =>
            simp only [] at h_success h_new
            exact ih (i + 1) _ s h_old h_success h_new hs'
    · unfold ParserState.feed at h_new
      simp only [hi, ↓reduceDIte] at h_new
      rw [show ({ s with charp := _ } : ParserState).db.find? n = s.db.find? n
        from rfl, h_old] at h_new
      cases h_new

/-- The initial registry is empty. -/
theorem default_db_find?_none (n : String) : (default : DB).find? n = none := by
  show (default : Std.HashMap String Object)[n]? = none
  rw [show (default : Std.HashMap String Object) = ∅ from rfl]
  simp

/-- `feedAll` extends the registry monotonically. -/
theorem feedAll_find?_mono (s : ParserState) (base : Nat) (arr : ByteArray)
    (n : String) (o : Object) (h : s.db.find? n = some o) :
    (s.feedAll base arr).db.find? n = some o := by
  unfold ParserState.feedAll
  cases h_charp : s.charp with
  | ws => exact feed_find?_mono base arr 0 .ws s n o h
  | token base' tk => exact feed_find?_mono base arr 0 _ _ n o h

/-- Chronological classification over `feedAll`. -/
theorem feedAll_new_assert_classified (s : ParserState) (base : Nat)
    (arr : ByteArray) (n : String) (f : Verify.Formula) (fr : Verify.Frame)
    (lbl : String)
    (h_old : s.db.find? n = none)
    (h_success : (s.feedAll base arr).db.error? = none)
    (h_new : (s.feedAll base arr).db.find? n = some (.assert f fr lbl)) :
    NewAssertCertificate n f fr lbl := by
  unfold ParserState.feedAll at h_success h_new
  cases h_charp : s.charp with
  | ws =>
      simp only [h_charp] at h_success h_new
      exact feed_new_assert_classified base arr 0 .ws s n f fr lbl
        h_old h_success h_new
  | token base' tk =>
      simp only [h_charp] at h_success h_new
      exact feed_new_assert_classified base arr 0 _ _ n f fr lbl
        (show ({ s with charp := default } : ParserState).db.find? n = none from h_old)
        h_success h_new

/-- `done` extends the registry monotonically: the trailing flush is a
`feedToken`, and the finalization dispatch only errors or passes the DB. -/
theorem done_find?_mono (s : ParserState) (base : Nat)
    (n : String) (o : Object) (h : s.db.find? n = some o) :
    (ParserState.done s base).find? n = some o := by
  cases h_e0 : s.db.error? with
  | some it =>
      simp only [ParserState.done, Id.run, DB.error, h_e0, Option.isSome_some,
        reduceIte]
      repeat' split
      all_goals
        simpa [DB.find?, DB.mkParseError, DB.mkErrorFromEvidence,
          DB.mkErrorWithEvidence, DB.mkError] using h
  | none =>
      cases h_charp : s.charp with
      | token pos tk =>
          have h1 := feedToken_find?_mono s pos tk.toSlice n o h
          cases h_e1 : (s.feedToken pos tk.toSlice).db.error? with
          | some it =>
              simp only [ParserState.done, Id.run, DB.error, h_e0, h_charp, h_e1,
              Option.isSome_none, Bool.false_eq_true, reduceIte]
              repeat' split
              all_goals
                simpa [DB.find?, DB.mkParseError, DB.mkErrorFromEvidence,
                  DB.mkErrorWithEvidence, DB.mkError] using h1
          | none =>
              simp only [ParserState.done, Id.run, DB.error, h_e0, h_charp, h_e1,
              Option.isSome_none, Bool.false_eq_true, reduceIte]
              repeat' split
              all_goals
                simpa [DB.find?, DB.mkParseError, DB.mkErrorFromEvidence,
                  DB.mkErrorWithEvidence, DB.mkError] using h1
      | ws =>
          simp only [ParserState.done, Id.run, DB.error, h_e0, h_charp,
            Option.isSome_none, Bool.false_eq_true, reduceIte]
          repeat' split
          all_goals
            simpa [DB.find?, DB.mkParseError, DB.mkErrorFromEvidence,
              DB.mkErrorWithEvidence, DB.mkError] using h

/-- With no prior error and a buffered token, `done`'s registry is exactly the
flush's registry: the finalization dispatch adds nothing. -/
theorem done_find?_eq_flush (s : ParserState) (base : Nat) (pos : Nat)
    (tk : ByteSliceT) (n : String)
    (h_e0 : s.db.error? = none)
    (h_charp : s.charp = .token pos tk)
    (h_e1 : (s.feedToken pos tk.toSlice).db.error? = none) :
    (ParserState.done s base).find? n
      = (s.feedToken pos tk.toSlice).db.find? n := by
  simp only [ParserState.done, Id.run, DB.error,
      Option.isSome_none, Bool.false_eq_true, reduceIte, h_e0, h_charp, h_e1]
  repeat' split
  all_goals
    simp [DB.find?, DB.mkParseError, DB.mkErrorFromEvidence,
      DB.mkErrorWithEvidence]

/-- With no prior error and nothing buffered, `done`'s registry is the input's. -/
theorem done_find?_eq_self (s : ParserState) (base : Nat) (n : String)
    (h_e0 : s.db.error? = none)
    (h_charp : s.charp = .ws) :
    (ParserState.done s base).find? n = s.db.find? n := by
  simp only [ParserState.done, Id.run, DB.error,
      Option.isSome_none, Bool.false_eq_true, reduceIte, h_e0, h_charp]
  repeat' split
  all_goals
    simp [DB.find?, DB.mkParseError, DB.mkErrorFromEvidence,
      DB.mkErrorWithEvidence]

/-- Chronological classification through `done`: the concrete buffered-token
flush is one more classified `feedToken`; the finalization dispatch creates
nothing. -/
theorem done_new_assert_classified (s : ParserState) (base : Nat)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_old : s.db.find? n = none)
    (h_success : (ParserState.done s base).error? = none)
    (h_new : (ParserState.done s base).find? n = some (.assert f fr lbl)) :
    NewAssertCertificate n f fr lbl := by
  have h_e0 : s.db.error? = none :=
    ParserOps.done_no_error_implies_db_no_error s base h_success
  cases h_charp : s.charp with
  | ws =>
      rw [done_find?_eq_self s base n h_e0 h_charp, h_old] at h_new
      cases h_new
  | token pos tk =>
      have h_e1 : (s.feedToken pos tk.toSlice).db.error? = none := by
        cases h_e : (s.feedToken pos tk.toSlice).db.error? with
        | none => rfl
        | some it =>
            exfalso
            have h_stuck : (ParserState.done s base).error? ≠ none := by
              simp only [ParserState.done, Id.run, DB.error, Option.isSome_some,
      Option.isSome_none, Bool.false_eq_true, reduceIte, h_e0, h_charp, h_e]
              simp [h_e]
            exact h_stuck h_success
      rw [done_find?_eq_flush s base pos tk n h_e0 h_charp h_e1] at h_new
      exact ⟨s, pos, tk.toSlice, h_old, h_e1, h_new,
        feedToken_new_assert_classified s pos tk.toSlice n f fr lbl
          h_old h_e1 h_new⟩

/-- `updateLine` touches only line bookkeeping, so every state-level invariant
transports across it. -/
theorem parserStateInv_updateLine (s : ParserState) (i : Nat) (c : UInt8)
    (h : ParserOps.ParserStateInv s) :
    ParserOps.ParserStateInv (s.updateLine i c) := by
  unfold ParserState.updateLine
  split
  · exact h
  · exact h

theorem proofGhost_updateLine (s : ParserState) (i : Nat) (c : UInt8)
    (h : ProofGhost s.db s.tokp) :
    ProofGhost (s.updateLine i c).db (s.updateLine i c).tokp := by
  unfold ParserState.updateLine
  split
  · exact h
  · exact h

/-- `NewAssertCertificate`, strengthened with the reachability facts the
provability composition needs: the creating state satisfies the full parser
invariant and carries the proof ghost. -/
def StrongNewAssertCertificate (n : String) (f : Verify.Formula)
    (fr : Verify.Frame) (lbl : String) : Prop :=
  ∃ (s' : ParserState) (j : Nat) (tk : ByteSlice),
    ParserOps.ParserStateInv s' ∧
    ProofGhost s'.db s'.tokp ∧
    s'.db.error? = none ∧
    s'.db.find? n = none ∧
    (s'.feedToken j tk).db.error? = none ∧
    (s'.feedToken j tk).db.find? n = some (.assert f fr lbl) ∧
    ((∃ arr p, AxiomFinishEvent s' j tk arr p) ∨ (∃ pr, FinishProofEvent s' j tk pr))

set_option linter.unusedSimpArgs false in
/-- The chronological classification, carrying invariants: under a strict
no-duplicate configuration, the creating state is fully invariant-bearing. -/
theorem feed_new_assert_strong_classified (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_old : s.db.find? n = none)
    (h_success : (ParserState.feed base arr i rs s).db.error? = none)
    (h_new : (ParserState.feed base arr i rs s).db.find? n
      = some (.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState),
      ParserOps.ParserStateInv s →
      ProofGhost s.db s.tokp →
      s.db.error? = none →
      s.db.config.rejectUnknownSteps = true →
      s.db.config.allowDuplicateFloat = false →
      s.db.find? n = none →
      (ParserState.feed base arr i rs s).db.error? = none →
      (ParserState.feed base arr i rs s).db.find? n = some (.assert f fr lbl) →
      arr.size - i = m →
      StrongNewAssertCertificate n f fr lbl)
    ?base ?step (arr.size - i) i rs s h_inv h_ghost h_err0 h_strict h_no_dup
      h_old h_success h_new rfl
  · intro i rs s _ _ _ _ _ h_old _ h_new hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.feed at h_new
    simp only [hi, ↓reduceDIte] at h_new
    rw [show ({ s with charp := _ } : ParserState).db.find? n = s.db.find? n
      from rfl, h_old] at h_new
    cases h_new
  · intro m ih i rs s h_inv h_ghost h_err0 h_strict h_no_dup h_old
      h_success h_new hs
    by_cases hi : i < arr.size
    · have hs' : arr.size - (i + 1) = m := by
        simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
      unfold ParserState.feed at h_success h_new
      simp only [hi, ↓reduceDIte] at h_success h_new
      by_cases h_ws : isWhitespace arr[i] = true
      · rw [if_pos h_ws] at h_success h_new
        cases rs with
        | ws =>
            simp only [] at h_success h_new
            exact ih (i + 1) .ws _ (parserStateInv_updateLine s _ _ h_inv)
              (proofGhost_updateLine s _ _ h_ghost)
              (by simpa using h_err0) (by simpa using h_strict)
              (by simpa using h_no_dup) (by simpa using h_old)
              h_success h_new hs'
        | token ot =>
            simp only [] at h_success h_new
            cases ot with
            | this off =>
                simp only [] at h_success h_new
                split at h_success
                · simp at h_success
                · rename_i h_guard
                  simp only [h_guard] at h_new
                  have h_flush_ok : (s.feedToken (base + off)
                      (ByteSlice.mk arr off (i - off))).db.error? = none := by
                    cases h_e : (s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).db.error? with
                    | none => rfl
                    | some it =>
                        exfalso
                        cases it with
                        | mk e idx =>
                            have h_e' : ((s.feedToken (base + off)
                                (ByteSlice.mk arr off (i - off))).updateLine
                                  (base + i) arr[i]).db.error?
                                = some ⟨e, idx⟩ := by simpa using h_e
                            exact absurd h_e' (h_guard e idx)
                  have h_inv1 := ParserOps.feedToken_maintains_stateInv s
                    (base + off) (ByteSlice.mk arr off (i - off))
                    h_inv h_err0 h_no_dup h_flush_ok
                  have h_ghost1 := feedToken_maintains_ghost s (base + off)
                    (ByteSlice.mk arr off (i - off))
                    h_ghost h_inv h_err0 h_strict h_flush_ok
                  by_cases h_mid : (s.feedToken (base + off)
                      (ByteSlice.mk arr off (i - off))).db.find? n = none
                  · exact ih (i + 1) .ws _
                      (parserStateInv_updateLine _ _ _ h_inv1)
                      (proofGhost_updateLine _ _ _ h_ghost1)
                      (by simpa using h_flush_ok)
                      (by simpa using h_strict) (by simpa using h_no_dup)
                      (by simpa using h_mid) h_success (by simpa using h_new) hs'
                  · cases h_val : (s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).db.find? n with
                    | none => exact absurd h_val h_mid
                    | some entry =>
                        have h_persist := feed_find?_mono base arr (i + 1) .ws
                          ((s.feedToken (base + off)
                            (ByteSlice.mk arr off (i - off))).updateLine
                              (base + i) arr[i]) n entry (by simpa using h_val)
                        have h_entry : entry = .assert f fr lbl := by
                          have h_new' := h_new
                          rw [h_persist] at h_new'
                          exact Option.some.inj h_new'
                        subst h_entry
                        exact ⟨s, base + off, ByteSlice.mk arr off (i - off),
                          h_inv, h_ghost, h_err0, h_old, h_flush_ok, h_val,
                          feedToken_new_assert_classified s (base + off) _
                            n f fr lbl h_old h_flush_ok h_val⟩
            | old base' off arr' =>
                simp only [] at h_success h_new
                split at h_success
                · simp at h_success
                · rename_i h_guard
                  simp only [h_guard] at h_new
                  have h_flush_ok : (s.feedToken (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))).db.error? = none := by
                    cases h_e : (s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).db.error? with
                    | none => rfl
                    | some it =>
                        exfalso
                        cases it with
                        | mk e idx =>
                            have h_e' : ((s.feedToken (base' + off)
                                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i
                                  false) off (arr'.size - off + i))).updateLine
                                  (base + i) arr[i]).db.error?
                                = some ⟨e, idx⟩ := by simpa using h_e
                            exact absurd h_e' (h_guard e idx)
                  have h_inv1 := ParserOps.feedToken_maintains_stateInv s
                    (base' + off)
                    (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                      (arr'.size - off + i))
                    h_inv h_err0 h_no_dup h_flush_ok
                  have h_ghost1 := feedToken_maintains_ghost s (base' + off)
                    (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                      (arr'.size - off + i))
                    h_ghost h_inv h_err0 h_strict h_flush_ok
                  by_cases h_mid : (s.feedToken (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))).db.find? n = none
                  · exact ih (i + 1) .ws _
                      (parserStateInv_updateLine _ _ _ h_inv1)
                      (proofGhost_updateLine _ _ _ h_ghost1)
                      (by simpa using h_flush_ok)
                      (by simpa using h_strict) (by simpa using h_no_dup)
                      (by simpa using h_mid) h_success (by simpa using h_new) hs'
                  · cases h_val : (s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).db.find? n with
                    | none => exact absurd h_val h_mid
                    | some entry =>
                        have h_persist := feed_find?_mono base arr (i + 1) .ws
                          ((s.feedToken (base' + off)
                            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                              off (arr'.size - off + i))).updateLine
                              (base + i) arr[i]) n entry (by simpa using h_val)
                        have h_entry : entry = .assert f fr lbl := by
                          have h_new' := h_new
                          rw [h_persist] at h_new'
                          exact Option.some.inj h_new'
                        subst h_entry
                        exact ⟨s, base' + off,
                          ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                            (arr'.size - off + i),
                          h_inv, h_ghost, h_err0, h_old, h_flush_ok, h_val,
                          feedToken_new_assert_classified s (base' + off) _
                            n f fr lbl h_old h_flush_ok h_val⟩
      · rw [if_neg h_ws] at h_success h_new
        cases rs with
        | ws =>
            simp only [] at h_success h_new
            exact ih (i + 1) _ s h_inv h_ghost h_err0 h_strict h_no_dup
              h_old h_success h_new hs'
        | token ot =>
            simp only [] at h_success h_new
            exact ih (i + 1) _ s h_inv h_ghost h_err0 h_strict h_no_dup
              h_old h_success h_new hs'
    · unfold ParserState.feed at h_new
      simp only [hi, ↓reduceDIte] at h_new
      rw [show ({ s with charp := _ } : ParserState).db.find? n = s.db.find? n
        from rfl, h_old] at h_new
      cases h_new

/-- **EOF-inclusive chronological classification for the pure entry point.**

Every `.assert` stored by an accepted `checkBytesCore` run — including one whose
closing `$.` is the very last token of the file, flushed by `done` — has a
classified local transition witness (`AxiomFinishEvent` or
`FinishProofEvent`). -/
theorem checkBytesCore_new_assert_classified (arr : ByteArray)
    (config : ModeConfig)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_success : (checkBytesCore arr config).error? = none)
    (h_new : (checkBytesCore arr config).find? n = some (.assert f fr lbl)) :
    NewAssertCertificate n f fr lbl := by
  unfold checkBytesCore at h_success h_new
  by_cases h_mid :
      (({ (default : ParserState) with
          db := { (default : DB) with config := config } } : ParserState).feedAll
        0 arr).db.find? n = none
  · exact done_new_assert_classified _ arr.size n f fr lbl h_mid h_success h_new
  · cases h_val :
        (({ (default : ParserState) with
            db := { (default : DB) with config := config } } : ParserState).feedAll
          0 arr).db.find? n with
    | none => exact absurd h_val h_mid
    | some entry =>
        have h_persist := done_find?_mono _ arr.size n entry h_val
        have h_entry : entry = .assert f fr lbl := by
          rw [h_persist] at h_new
          exact Option.some.inj h_new
        subst h_entry
        have h_feed_success :
            (({ (default : ParserState) with
                db := { (default : DB) with config := config } } : ParserState).feedAll
              0 arr).db.error? = none :=
          ParserOps.done_no_error_implies_db_no_error _ arr.size h_success
        exact feedAll_new_assert_classified _ 0 arr n f fr lbl
          (default_db_find?_none n) h_feed_success h_val

/-- The same, for `checkBytes`: the well-formedness gate only errors or passes
the core database through. -/
theorem checkBytes_new_assert_classified (arr : ByteArray) (config : ModeConfig)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_success : (checkBytes arr config).error? = none)
    (h_new : (checkBytes arr config).find? n = some (.assert f fr lbl)) :
    NewAssertCertificate n f fr lbl := by
  unfold checkBytes at h_success h_new
  by_cases h_c : (checkBytesCore arr config).error? = none
  · simp only [h_c, reduceIte] at h_success h_new
    by_cases h_g : (((checkBytesCore arr config).config.allowDuplicateFloat
        || (checkBytesCore arr config).wellFormed?)
        && (checkBytesCore arr config).assertDvVarsInFrame?) = true
    · simp only [h_g, if_true] at h_success h_new
      exact checkBytesCore_new_assert_classified arr config n f fr lbl h_c h_new
    · exfalso
      rw [if_neg h_g] at h_success
      simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]
        at h_success
  · exfalso
    rw [if_neg h_c] at h_success
    exact h_c h_success

set_option linter.unusedSimpArgs false in
/-- The chronological classification without a final-success hypothesis: valid
up to and including a run that terminates in an error (e.g. an include-request
interrupt ending a chunk).  An error-terminated flush cannot itself have created
an assertion — creation implies step success — so the terminal branch closes by
contradiction. -/
theorem feed_new_assert_strong_classified_upto (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_old : s.db.find? n = none)
    (h_new : (ParserState.feed base arr i rs s).db.find? n
      = some (.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState),
      ParserOps.ParserStateInv s →
      ProofGhost s.db s.tokp →
      s.db.error? = none →
      s.db.config.rejectUnknownSteps = true →
      s.db.config.allowDuplicateFloat = false →
      s.db.find? n = none →
      (ParserState.feed base arr i rs s).db.find? n = some (.assert f fr lbl) →
      arr.size - i = m →
      StrongNewAssertCertificate n f fr lbl)
    ?base ?step (arr.size - i) i rs s h_inv h_ghost h_err0 h_strict h_no_dup
      h_old h_new rfl
  · intro i rs s _ _ _ _ _ h_old h_new hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.feed at h_new
    simp only [hi, ↓reduceDIte] at h_new
    rw [show ({ s with charp := _ } : ParserState).db.find? n = s.db.find? n
      from rfl, h_old] at h_new
    cases h_new
  · intro m ih i rs s h_inv h_ghost h_err0 h_strict h_no_dup h_old
      h_new hs
    by_cases hi : i < arr.size
    · have hs' : arr.size - (i + 1) = m := by
        simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
      unfold ParserState.feed at h_new
      simp only [hi, ↓reduceDIte] at h_new
      by_cases h_ws : isWhitespace arr[i] = true
      · rw [if_pos h_ws] at h_new
        cases rs with
        | ws =>
            simp only [] at h_new
            exact ih (i + 1) .ws _ (parserStateInv_updateLine s _ _ h_inv)
              (proofGhost_updateLine s _ _ h_ghost)
              (by simpa using h_err0) (by simpa using h_strict)
              (by simpa using h_no_dup) (by simpa using h_old)
              h_new hs'
        | token ot =>
            simp only [] at h_new
            cases ot with
            | this off =>
                simp only [] at h_new
                cases h_g : ((s.feedToken (base + off)
                    (ByteSlice.mk arr off (i - off))).updateLine
                      (base + i) arr[i]).db.error? with
                | some it =>
                    exfalso
                    cases it with
                    | mk e idx =>
                        simp only [h_g] at h_new
                        have h_created : (s.feedToken (base + off)
                            (ByteSlice.mk arr off (i - off))).db.find? n
                            = some (.assert f fr lbl) := by
                          simpa [DB.find?] using h_new
                        have h_ok := feedToken_new_assert_success s (base + off)
                          (ByteSlice.mk arr off (i - off)) n f fr lbl
                          h_err0 h_old h_created
                        have h_bad : ((s.feedToken (base + off)
                            (ByteSlice.mk arr off (i - off))).updateLine
                              (base + i) arr[i]).db.error? = none := by
                          simpa using h_ok
                        rw [h_g] at h_bad
                        cases h_bad
                | none =>
                    rename_i h_guard_dead
                    simp only [h_g] at h_new
                    have h_flush_ok : (s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).db.error? = none := by
                      simpa using h_g
                    have h_inv1 := ParserOps.feedToken_maintains_stateInv s
                      (base + off) (ByteSlice.mk arr off (i - off))
                      h_inv h_err0 h_no_dup h_flush_ok
                    have h_ghost1 := feedToken_maintains_ghost s (base + off)
                      (ByteSlice.mk arr off (i - off))
                      h_ghost h_inv h_err0 h_strict h_flush_ok
                    by_cases h_mid : (s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).db.find? n = none
                    · exact ih (i + 1) .ws _
                        (parserStateInv_updateLine _ _ _ h_inv1)
                        (proofGhost_updateLine _ _ _ h_ghost1)
                        (by simpa using h_flush_ok)
                        (by simpa using h_strict) (by simpa using h_no_dup)
                        (by simpa using h_mid) (by simpa using h_new) hs'
                    · cases h_val : (s.feedToken (base + off)
                          (ByteSlice.mk arr off (i - off))).db.find? n with
                      | none => exact absurd h_val h_mid
                      | some entry =>
                          have h_persist := feed_find?_mono base arr (i + 1) .ws
                            ((s.feedToken (base + off)
                              (ByteSlice.mk arr off (i - off))).updateLine
                                (base + i) arr[i]) n entry (by simpa using h_val)
                          have h_entry : entry = .assert f fr lbl := by
                            have h_new' := h_new
                            rw [h_persist] at h_new'
                            exact Option.some.inj h_new'
                          subst h_entry
                          exact ⟨s, base + off, ByteSlice.mk arr off (i - off),
                            h_inv, h_ghost, h_err0, h_old, h_flush_ok, h_val,
                            feedToken_new_assert_classified s (base + off) _
                              n f fr lbl h_old h_flush_ok h_val⟩
            | old base' off arr' =>
                simp only [] at h_new
                cases h_g : ((s.feedToken (base' + off)
                    (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                      (arr'.size - off + i))).updateLine
                      (base + i) arr[i]).db.error? with
                | some it =>
                    exfalso
                    cases it with
                    | mk e idx =>
                        simp only [h_g] at h_new
                        have h_created : (s.feedToken (base' + off)
                            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                              off (arr'.size - off + i))).db.find? n
                            = some (.assert f fr lbl) := by
                          simpa [DB.find?] using h_new
                        have h_ok := feedToken_new_assert_success s (base' + off)
                          (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                            off (arr'.size - off + i)) n f fr lbl
                          h_err0 h_old h_created
                        have h_bad : ((s.feedToken (base' + off)
                            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                              off (arr'.size - off + i))).updateLine
                              (base + i) arr[i]).db.error? = none := by
                          simpa using h_ok
                        rw [h_g] at h_bad
                        cases h_bad
                | none =>
                    rename_i h_guard_dead
                    simp only [h_g] at h_new
                    have h_flush_ok : (s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).db.error? = none := by
                      simpa using h_g
                    have h_inv1 := ParserOps.feedToken_maintains_stateInv s
                      (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))
                      h_inv h_err0 h_no_dup h_flush_ok
                    have h_ghost1 := feedToken_maintains_ghost s (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))
                      h_ghost h_inv h_err0 h_strict h_flush_ok
                    by_cases h_mid : (s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).db.find? n = none
                    · exact ih (i + 1) .ws _
                        (parserStateInv_updateLine _ _ _ h_inv1)
                        (proofGhost_updateLine _ _ _ h_ghost1)
                        (by simpa using h_flush_ok)
                        (by simpa using h_strict) (by simpa using h_no_dup)
                        (by simpa using h_mid) (by simpa using h_new) hs'
                    · cases h_val : (s.feedToken (base' + off)
                          (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                            (arr'.size - off + i))).db.find? n with
                      | none => exact absurd h_val h_mid
                      | some entry =>
                          have h_persist := feed_find?_mono base arr (i + 1) .ws
                            ((s.feedToken (base' + off)
                              (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                                off (arr'.size - off + i))).updateLine
                                (base + i) arr[i]) n entry (by simpa using h_val)
                          have h_entry : entry = .assert f fr lbl := by
                            have h_new' := h_new
                            rw [h_persist] at h_new'
                            exact Option.some.inj h_new'
                          subst h_entry
                          exact ⟨s, base' + off,
                            ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                              (arr'.size - off + i),
                            h_inv, h_ghost, h_err0, h_old, h_flush_ok, h_val,
                            feedToken_new_assert_classified s (base' + off) _
                              n f fr lbl h_old h_flush_ok h_val⟩
      · rw [if_neg h_ws] at h_new
        cases rs with
        | ws =>
            simp only [] at h_new
            exact ih (i + 1) _ s h_inv h_ghost h_err0 h_strict h_no_dup
              h_old h_new hs'
        | token ot =>
            simp only [] at h_new
            exact ih (i + 1) _ s h_inv h_ghost h_err0 h_strict h_no_dup
              h_old h_new hs'
    · unfold ParserState.feed at h_new
      simp only [hi, ↓reduceDIte] at h_new
      rw [show ({ s with charp := _ } : ParserState).db.find? n = s.db.find? n
        from rfl, h_old] at h_new
      cases h_new

/-- The child-boundary pop touches no registry entry: it either raises a
boundary error or restores line bookkeeping. -/
theorem popExhaustedFrame_objects (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (rest : List IncludeDriverFrame) :
    (popExhaustedFrame s base frame rest).db.objects = s.db.objects := by
  unfold popExhaustedFrame
  repeat' split
  all_goals simp [restoreLineState, ParserState.withDB]

@[simp] theorem clearIncludeRequest_objects (s : ParserState) :
    (clearIncludeRequest s).db.objects = s.db.objects := rfl

theorem popExhaustedFrame_db_config (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (rest : List IncludeDriverFrame) :
    (popExhaustedFrame s base frame rest).db.config = s.db.config := by
  unfold popExhaustedFrame
  repeat' split
  all_goals simp [restoreLineState, ParserState.withDB]

@[simp] theorem clearIncludeRequest_db_config (s : ParserState) :
    (clearIncludeRequest s).db.config = s.db.config := rfl

theorem flushPendingToken_db_config (s : ParserState) :
    (flushPendingToken s).db.config = s.db.config := by
  unfold flushPendingToken
  cases h : s.charp with
  | ws => rfl
  | token pos tk => exact ParserState.feedToken_db_config s pos tk.toSlice

/-- `feedAll` classification without a final-success hypothesis. -/
theorem feedAll_new_assert_strong_classified_upto (s : ParserState) (base : Nat)
    (arr : ByteArray) (n : String) (f : Verify.Formula) (fr : Verify.Frame)
    (lbl : String)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_old : s.db.find? n = none)
    (h_new : (s.feedAll base arr).db.find? n = some (.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  unfold ParserState.feedAll at h_new
  cases h_charp : s.charp with
  | ws =>
      simp only [h_charp] at h_new
      exact feed_new_assert_strong_classified_upto base arr 0 .ws s n f fr lbl
        h_inv h_ghost h_err0 h_strict h_no_dup h_old h_new
  | token base' tk =>
      simp only [h_charp] at h_new
      exact feed_new_assert_strong_classified_upto base arr 0 _
        ({ s with charp := default }) n f fr lbl
        h_inv h_ghost h_err0 h_strict h_no_dup h_old h_new

/-- Result-parser projection of one driver step. -/
def frameStepParser : FrameStep → ParserState
  | .done st => st.parser
  | .fed st => st.parser
  | .push _ _ _ st => st.parser

/-- `withAt` preserves non-request errors: it rewrites only `.error` messages
and passes everything else through. -/
theorem withAt_errorNotRequest (l : String) (g : Unit → ParserState)
    (h : ParserOps.ErrorNotRequest (g ()).db.error?) :
    ParserOps.ErrorNotRequest (ParserState.withAt l g).db.error? := by
  unfold ParserState.withAt
  cases h_err : (g ()).db.error? with
  | none =>
      simp only [h_err]
      intro sf pf idx hx
      simp at hx
  | some it =>
      cases it with
      | mk e idx0 =>
          cases e with
          | error pos msg =>
              simp only [h_err, ParserState.withDB]
              intro sf pf idx hx
              injection hx with hh
              injection hh with he hi
              cases he
          | ax pos l0 f0 fr0 =>
              simp only [h_err]
              exact fun sf pf idx hx => h sf pf idx (h_err ▸ hx)
          | thm pos l0 f0 fr0 =>
              simp only [h_err]
              exact fun sf pf idx hx => h sf pf idx (h_err ▸ hx)
          | includeRequest sf0 pf0 =>
              exact absurd h_err (by
                intro hbad
                exact h sf0 pf0 idx0 hbad)

set_option linter.unnecessarySimpa false in
/-- `feedTokens` never raises an include request. -/
theorem feedTokens_errorNotRequest (s : ParserState) (arr : Array Verify.Sym)
    (k : TokensKind) (pos : Pos) (l : String)
    (h : ParserOps.ErrorNotRequest s.db.error?) :
    ParserOps.ErrorNotRequest (s.feedTokens arr ⟨k, pos, l⟩).db.error? := by
  unfold ParserState.feedTokens
  apply withAt_errorNotRequest
  cases k <;> simp only [Id.run] <;> repeat' split
  all_goals
    first
      | exact h
      | exact fun sf pf idx hx => ParserOps.errorNotRequest_mkError _ _ _ sf pf idx
          (by simpa [ParserState.mkErrorFromEvidence, ParserState.mkErrorWithEvidence,
            ParserState.mkError, ParserState.withDB] using hx)
      | (intro sf pf idx hx
         exact ParserOps.insertHyp_errorNotRequest _ _ _ _ _ h sf pf idx
           (by simpa [ParserState.withDB] using hx))
      | (intro sf pf idx hx
         exact ParserOps.insertAxiom_errorNotRequest _ _ _ _ h sf pf idx
           (by simpa [ParserState.withDB] using hx))
      | (intro sf pf idx hx
         exact h sf pf idx (by simpa [ParserState.withDB] using hx))

/-- `finishProof` never raises an include request. -/
theorem finishProof_errorNotRequest (s : ParserState) (pr : ProofState)
    (h : ParserOps.ErrorNotRequest s.db.error?) :
    ParserOps.ErrorNotRequest (s.finishProof pr).db.error? := by
  cases pr with
  | mk pos l fmla fr heap stack ptp inc =>
      unfold ParserState.finishProof
      apply withAt_errorNotRequest
      simp only [Id.run]
      repeat' split
      all_goals
        first
          | exact h
          | exact fun sf pf idx hx => ParserOps.errorNotRequest_mkError _ _ _ sf pf idx
              (by simpa [ParserState.mkErrorFromEvidence,
                ParserState.mkErrorWithEvidence, ParserState.mkError,
                ParserState.withDB] using hx)
          | (intro sf pf idx hx
             exact ParserOps.insert_errorNotRequest _ _ _ _ h sf pf idx
               (by simpa [ParserState.withDB] using hx))

/-- `feedProof` never raises an include request. -/
theorem feedProof_errorNotRequest (s : ParserState) (tk : ByteSlice)
    (pr : ProofState) (h : ParserOps.ErrorNotRequest s.db.error?) :
    ParserOps.ErrorNotRequest (s.feedProof tk pr).db.error? := by
  unfold ParserState.feedProof
  apply withAt_errorNotRequest
  split
  · exact h
  · exact fun sf pf idx hx => ParserOps.errorNotRequest_mkError _ _ _ sf pf idx
      (by simpa [ParserState.mkErrorFromEvidence, ParserState.mkErrorWithEvidence,
        ParserState.mkError, ParserState.withDB] using hx)

/-- `djvars_loop` never raises an include request. -/
theorem djvars_loop_errorNotRequest (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String)
    (h : ParserOps.ErrorNotRequest s.db.error?) :
    ParserOps.ErrorNotRequest (ParserState.djvars_loop arr s pos tk).db.error? := by
  have h_aux : ∀ (i : Nat) (s' : ParserState),
      ParserOps.ErrorNotRequest s'.db.error? →
      ParserOps.ErrorNotRequest
        (ParserState.djvars_loop_aux arr s' pos tk i).db.error? := by
    intro i s' h'
    refine Nat.rec (motive := fun m => ∀ i (s' : ParserState),
        ParserOps.ErrorNotRequest s'.db.error? →
        arr.size - i = m →
        ParserOps.ErrorNotRequest
          (ParserState.djvars_loop_aux arr s' pos tk i).db.error?)
      ?base ?step (arr.size - i) i s' h' rfl
    · intro i s' h' hs
      have hi : ¬ i < arr.size := by
        intro hi
        have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
        simp [hs] at hpos
      unfold ParserState.djvars_loop_aux
      simp only [hi, ↓reduceDIte]
      exact h'
    · intro m ih i s' h' hs
      by_cases hi : i < arr.size
      · have hs' : arr.size - (i + 1) = m := by
          simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
        unfold ParserState.djvars_loop_aux
        simp only [hi, ↓reduceDIte]
        split
        · exact fun sf pf idx hx => ParserOps.errorNotRequest_mkError _ _ _
            sf pf idx (by simpa [ParserState.mkErrorFromEvidence,
              ParserState.mkErrorWithEvidence, ParserState.mkError,
              ParserState.withDB] using hx)
        · exact ih (i + 1) _ (by
            simpa [ParserState.withDB, DB.withDJ, DB.withFrame] using h') hs'
      · unfold ParserState.djvars_loop_aux
        simp only [hi, ↓reduceDIte]
        exact h'
  unfold ParserState.djvars_loop
  split
  · exact fun sf pf idx hx => ParserOps.errorNotRequest_mkError _ _ _ sf pf idx
      (by simpa [ParserState.mkErrorFromEvidence, ParserState.mkErrorWithEvidence,
        ParserState.mkError, ParserState.withDB] using hx)
  · exact h_aux _ _ h

/-- The live-driver invariant package: what the spine threads between steps. -/
def DriverInv (p : ParserState) : Prop :=
  ParserOps.ParserStateInv p ∧ ProofGhost p.db p.tokp ∧ p.db.error? = none

/-- Clearing a just-raised include request restores the raising state with the
parked continuation installed. -/
theorem clearIncludeRequest_requestInclude_eq (s : ParserState)
    (resume : TokenParser) (path : String)
    (h_err0 : s.db.error? = none) :
    clearIncludeRequest (s.requestInclude resume path)
      = { s with tokp := resume } := by
  cases s with
  | mk db tokp charp line linepos sourceFile =>
      cases db with
      | mk frame scopes activeVars objects interrupt error? errorEvidence? config =>
          simp_all [clearIncludeRequest, ParserState.requestInclude]

theorem popScope_errorNotRequestP (s : ParserState) (pos : Pos)
    (h : ParserOps.ErrorNotRequest s.db.error?) :
    ParserOps.ErrorNotRequest (s.withDB (DB.popScope pos)).db.error? := by
  show ParserOps.ErrorNotRequest (DB.popScope pos s.db).error?
  unfold DB.popScope
  split
  · exact h
  · exact ParserOps.errorNotRequest_mkError _ _ _

theorem label_errorNotRequestP (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (h : ParserOps.ErrorNotRequest s.db.error?) :
    ParserOps.ErrorNotRequest (s.label pos tk).db.error? := by
  unfold ParserState.label
  repeat' split
  all_goals
    first
      | exact h
      | (intro sf pf idx hx
         exact ParserOps.errorNotRequest_mkError _ _ _ sf pf idx
           (by simpa [ParserState.mkErrorFromEvidence,
             ParserState.mkErrorWithEvidence, ParserState.mkError,
             ParserState.withDB] using hx))

set_option linter.unusedSimpArgs false in
/-- Every `feedToken` transition from an error-free state either leaves a
non-request error slot, or *is* a `requestInclude` — whose parked continuation
carries its own `TokpInv` and ghost by the definitions' recursion. -/
theorem feedToken_request_form_or_notRequest (s : ParserState) (i : Nat)
    (tk : ByteSlice)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none) :
    ParserOps.ErrorNotRequest (s.feedToken i tk).db.error?
      ∨ (∃ resume path, s.feedToken i tk = s.requestInclude resume path ∧
          ParserOps.TokpInv s.db resume ∧ ProofGhost s.db resume) := by
  obtain ⟨h_wf, h_scoped, h_ok, h_tokp_inv⟩ := h_inv
  have h_base : ParserOps.ErrorNotRequest s.db.error? := by
    rw [h_err0]
    exact ParserOps.errorNotRequest_none
  have h_mk : ∀ (s' : ParserState) (pos : Pos) (ev : ErrorEvidence),
      ParserOps.ErrorNotRequest (s'.mkErrorFromEvidence pos ev).db.error? := by
    intro s' pos ev sf pf idx hx
    exact ParserOps.errorNotRequest_mkError s'.db pos ev sf pf idx
      (by simpa [ParserState.mkErrorFromEvidence, ParserState.mkErrorWithEvidence,
        ParserState.mkError, ParserState.withDB] using hx)
  unfold ParserState.feedToken
  cases h_tokp : s.tokp with
  | comment q =>
      left
      simp only [h_tokp]
      repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | includePath resume q =>
      rw [h_tokp] at h_tokp_inv h_ghost
      simp only [h_tokp]
      repeat' split
      all_goals
        first
          | (left; exact h_base)
          | (left; exact h_mk _ _ _)
          | (right; exact ⟨resume, _, rfl, h_tokp_inv, h_ghost⟩)
  | includeClose resume q path =>
      rw [h_tokp] at h_tokp_inv h_ghost
      simp only [h_tokp]
      repeat' split
      all_goals
        first
          | (left; exact h_base)
          | (left; exact h_mk _ _ _)
          | (right; exact ⟨resume, path, rfl, h_tokp_inv, h_ghost⟩)
  | start =>
      left
      simp only [h_tokp]
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact popScope_errorNotRequestP s _ h_base
          | exact label_errorNotRequestP s _ tk h_base
  | label q lab =>
      left
      simp only [h_tokp]
      repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | const seen =>
      left
      simp only [h_tokp]
      unfold ParserState.sym ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact ParserOps.insert_errorNotRequest s.db _ _ _ h_base
  | var seen =>
      left
      simp only [h_tokp]
      unfold ParserState.sym ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact ParserOps.insert_errorNotRequest s.db _ _ _ h_base
  | djvars arr =>
      left
      simp only [h_tokp]
      unfold ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact djvars_loop_errorNotRequest _ _ _ _ h_base
  | math arr p =>
      left
      simp only [h_tokp]
      unfold ParserState.withMath
      repeat' split
      all_goals
        try (first
          | exact h_base
          | exact h_mk _ _ _
          | (cases p with
             | mk k ppos plab =>
                 exact feedTokens_errorNotRequest s arr k ppos plab h_base))
      all_goals simp only [Id.run]
      all_goals repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | proof pr =>
      left
      simp only [h_tokp]
      repeat' split
      all_goals
        first
          | exact finishProof_errorNotRequest _ pr h_base
          | exact feedProof_errorNotRequest _ tk pr h_base
          | exact h_base
          | exact h_mk _ _ _

theorem driverInv_updateLine (s : ParserState) (i : Nat) (c : UInt8)
    (h : DriverInv s) : DriverInv (s.updateLine i c) :=
  ⟨parserStateInv_updateLine s i c h.1, proofGhost_updateLine s i c h.2.1, by
    unfold ParserState.updateLine
    split
    · exact h.2.2
    · exact h.2.2⟩

theorem driverInv_feedToken (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h : DriverInv s)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_ok : (s.feedToken i tk).db.error? = none) :
    DriverInv (s.feedToken i tk) :=
  ⟨ParserOps.feedToken_maintains_stateInv s i tk h.1 h.2.2 h_no_dup h_ok,
   feedToken_maintains_ghost s i tk h.2.1 h.1 h.2.2 h_strict h_ok, h_ok⟩

/-- `DriverInv` reads only the database and token mode. -/
theorem driverInv_of_db_tokp_eq (p q : ParserState)
    (hdb : p.db = q.db) (ht : p.tokp = q.tokp) (h : DriverInv q) : DriverInv p := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  exact ⟨⟨hdb ▸ h1, hdb ▸ h2, hdb ▸ h3, by rw [hdb, ht]; exact h4⟩,
    by rw [hdb, ht]; exact h5, by rw [hdb]; exact h6⟩

/-- A transition that raised an include request, cleared, is fully
invariant-bearing: it *was* a `requestInclude`, and clearing restores the
raising state with the parked continuation installed. -/
theorem driverInv_of_request_step (s : ParserState) (i : Nat) (tk : ByteSlice)
    {sf pf : String} {idx : Nat}
    (h_dinv : DriverInv s)
    (h_req : (s.feedToken i tk).db.error?
      = some ⟨.includeRequest sf pf, idx⟩) :
    DriverInv (clearIncludeRequest (s.feedToken i tk)) := by
  rcases feedToken_request_form_or_notRequest s i tk h_dinv.1 h_dinv.2.1
      h_dinv.2.2 with h_nr | ⟨resume, path, h_eq, h_tinv, h_gh⟩
  · exact absurd h_req (h_nr sf pf idx)
  · rw [h_eq, clearIncludeRequest_requestInclude_eq s resume path h_dinv.2.2]
    exact ⟨⟨h_dinv.1.1, h_dinv.1.2.1, h_dinv.1.2.2.1, h_tinv⟩, h_gh, h_dinv.2.2⟩

/-- A chunk run terminating in an include-request error hands the cleared state
back fully invariant-bearing. -/
theorem feed_request_transport (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState)
    (h_dinv : DriverInv s)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    {sf pf : String} {idx : Nat}
    (h_end : (ParserState.feed base arr i rs s).db.error?
      = some ⟨.includeRequest sf pf, idx⟩) :
    DriverInv (clearIncludeRequest (ParserState.feed base arr i rs s)) := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState),
      DriverInv s →
      s.db.config.rejectUnknownSteps = true →
      s.db.config.allowDuplicateFloat = false →
      ∀ idx : Nat,
      (ParserState.feed base arr i rs s).db.error?
        = some ⟨.includeRequest sf pf, idx⟩ →
      arr.size - i = m →
      DriverInv (clearIncludeRequest (ParserState.feed base arr i rs s)))
    ?base ?step (arr.size - i) i rs s h_dinv h_strict h_no_dup idx h_end rfl
  · intro i rs s h_dinv _ _ idx h_end hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    exfalso
    unfold ParserState.feed at h_end
    simp only [hi, ↓reduceDIte] at h_end
    rw [show ({ s with charp := _ } : ParserState).db.error? = s.db.error?
      from rfl, h_dinv.2.2] at h_end
    cases h_end
  · intro m ih i rs s h_dinv h_strict h_no_dup idx h_end hs
    by_cases hi : i < arr.size
    · have hs' : arr.size - (i + 1) = m := by
        simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
      unfold ParserState.feed at h_end ⊢
      simp only [hi, ↓reduceDIte] at h_end ⊢
      by_cases h_ws : isWhitespace arr[i] = true
      · rw [if_pos h_ws] at h_end ⊢
        cases rs with
        | ws =>
            simp only [] at h_end ⊢
            exact ih (i + 1) .ws _ (driverInv_updateLine s _ _ h_dinv)
              (by simpa using h_strict) (by simpa using h_no_dup) idx h_end hs'
        | token ot =>
            simp only [] at h_end ⊢
            cases ot with
            | this off =>
                simp only [] at h_end ⊢
                cases h_g : ((s.feedToken (base + off)
                    (ByteSlice.mk arr off (i - off))).updateLine
                      (base + i) arr[i]).db.error? with
                | none =>
                    simp only [h_g] at h_end ⊢
                    have h_fok : (s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).db.error? = none := by
                      simpa using h_g
                    exact ih (i + 1) .ws _
                      (driverInv_updateLine _ _ _
                        (driverInv_feedToken s _ _ h_dinv h_strict h_no_dup h_fok))
                      (by simpa using h_strict) (by simpa using h_no_dup)
                      idx h_end hs'
                | some it =>
                    cases it with
                    | mk e idx0 =>
                        simp only [h_g] at h_end ⊢
                        have h_pair : (⟨e, i + 1⟩ : Interrupt)
                            = ⟨.includeRequest sf pf, idx⟩ :=
                          Option.some.inj h_end
                        cases h_pair
                        have h_flush_req : (s.feedToken (base + off)
                            (ByteSlice.mk arr off (i - off))).db.error?
                            = some ⟨.includeRequest sf pf, idx0⟩ := by
                          simpa using h_g
                        exact driverInv_of_db_tokp_eq _ _
                          (by unfold clearIncludeRequest ParserState.updateLine
                              split <;> rfl)
                          (by unfold clearIncludeRequest ParserState.updateLine
                              split <;> rfl)
                          (driverInv_of_request_step s (base + off)
                            (ByteSlice.mk arr off (i - off)) h_dinv h_flush_req)
            | old base' off arr' =>
                simp only [] at h_end ⊢
                cases h_g : ((s.feedToken (base' + off)
                    (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                      (arr'.size - off + i))).updateLine
                      (base + i) arr[i]).db.error? with
                | none =>
                    simp only [h_g] at h_end ⊢
                    have h_fok : (s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).db.error? = none := by
                      simpa using h_g
                    exact ih (i + 1) .ws _
                      (driverInv_updateLine _ _ _
                        (driverInv_feedToken s _ _ h_dinv h_strict h_no_dup h_fok))
                      (by simpa using h_strict) (by simpa using h_no_dup)
                      idx h_end hs'
                | some it =>
                    cases it with
                    | mk e idx0 =>
                        simp only [h_g] at h_end ⊢
                        have h_pair : (⟨e, i + 1⟩ : Interrupt)
                            = ⟨.includeRequest sf pf, idx⟩ :=
                          Option.some.inj h_end
                        cases h_pair
                        have h_flush_req : (s.feedToken (base' + off)
                            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                              off (arr'.size - off + i))).db.error?
                            = some ⟨.includeRequest sf pf, idx0⟩ := by
                          simpa using h_g
                        exact driverInv_of_db_tokp_eq _ _
                          (by unfold clearIncludeRequest ParserState.updateLine
                              split <;> rfl)
                          (by unfold clearIncludeRequest ParserState.updateLine
                              split <;> rfl)
                          (driverInv_of_request_step s (base' + off)
                            (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false)
                              off (arr'.size - off + i)) h_dinv h_flush_req)
      · rw [if_neg h_ws] at h_end ⊢
        cases rs with
        | ws =>
            simp only [] at h_end ⊢
            exact ih (i + 1) _ s h_dinv h_strict h_no_dup idx h_end hs'
        | token ot =>
            simp only [] at h_end ⊢
            exact ih (i + 1) _ s h_dinv h_strict h_no_dup idx h_end hs'
    · exfalso
      unfold ParserState.feed at h_end
      simp only [hi, ↓reduceDIte] at h_end
      rw [show ({ s with charp := _ } : ParserState).db.error? = s.db.error?
        from rfl, h_dinv.2.2] at h_end
      cases h_end

theorem driverInv_feedAll_ok (s : ParserState) (base : Nat) (arr : ByteArray)
    (h : DriverInv s)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_ok : (s.feedAll base arr).db.error? = none) :
    DriverInv (s.feedAll base arr) :=
  ⟨ParserOps.feedAll_maintains_stateInv s base arr h.1 h.2.2 h_no_dup h_ok,
   feedAll_maintains_ghost s base arr h.2.1 h.1 h.2.2 h_no_dup h_strict h_ok,
   h_ok⟩

/-- `feedAll` chunk ending in an include request: the cleared state is
invariant-bearing. -/
theorem feedAll_request_transport (s : ParserState) (base : Nat)
    (arr : ByteArray)
    (h_dinv : DriverInv s)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    {sf pf : String} {idx : Nat}
    (h_end : (s.feedAll base arr).db.error?
      = some ⟨.includeRequest sf pf, idx⟩) :
    DriverInv (clearIncludeRequest (s.feedAll base arr)) := by
  unfold ParserState.feedAll at h_end ⊢
  cases h_charp : s.charp with
  | ws =>
      simp only [h_charp] at h_end ⊢
      exact feed_request_transport base arr 0 .ws s h_dinv h_strict h_no_dup h_end
  | token base' tk =>
      simp only [h_charp] at h_end ⊢
      exact feed_request_transport base arr 0 _ ({ s with charp := default })
        (driverInv_of_db_tokp_eq _ s rfl rfl h_dinv)
        h_strict h_no_dup h_end

/-- Line-state restoration is invisible to the invariant package. -/
theorem driverInv_restoreLineState (s : ParserState) (base : Nat)
    (rest : List IncludeDriverFrame) (h : DriverInv s) :
    DriverInv (restoreLineState s base rest) := by
  refine driverInv_of_db_tokp_eq _ s ?_ ?_ h <;>
    (unfold restoreLineState; cases rest <;> rfl)

theorem driverInv_sourceFile (s : ParserState) (f : String) (h : DriverInv s) :
    DriverInv { s with sourceFile := f } :=
  driverInv_of_db_tokp_eq _ s rfl rfl h

theorem driverInv_charp (s : ParserState) (c : CharParser) (h : DriverInv s) :
    DriverInv { s with charp := c } :=
  driverInv_of_db_tokp_eq _ s rfl rfl h

/-- The pending-token flush maintains the package when it succeeds. -/
theorem driverInv_flushPendingToken (s : ParserState)
    (h : DriverInv s)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_ok : (flushPendingToken s).db.error? = none) :
    DriverInv (flushPendingToken s) := by
  revert h_ok
  unfold flushPendingToken
  split
  · intro _
    exact h
  · rename_i pos tk h_charp
    intro h_ok
    have h_ok' : (s.feedToken pos tk.toSlice).db.error? = none := by
      simpa using h_ok
    exact driverInv_of_db_tokp_eq _ (s.feedToken pos tk.toSlice) rfl rfl
      (driverInv_feedToken s pos tk.toSlice h h_strict h_no_dup h_ok')

theorem driverInv_popExhaustedFrame_live (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (rest : List IncludeDriverFrame)
    (h : DriverInv s)
    (h_ok : (popExhaustedFrame s base frame rest).db.error? = none) :
    DriverInv (popExhaustedFrame s base frame rest) := by
  revert h_ok
  unfold popExhaustedFrame
  repeat' split
  all_goals intro h_ok
  all_goals
    first
      | exact h
      | exact driverInv_restoreLineState _ _ _ h
      | (exfalso
         revert h_ok
         simp [ParserState.withDB, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence])

set_option linter.unusedSimpArgs false in
/-- Registry monotonicity across one driver step. -/
theorem stepFrame_find?_mono (st : IncludeDriverState)
    (n : String) (o : Object) (h : st.parser.db.find? n = some o) :
    (frameStepParser (stepFrame st)).db.find? n = some o := by
  unfold stepFrame
  cases h_stack : st.stack with
  | nil => simpa [frameStepParser] using h
  | cons parent tail =>
      by_cases h_sep : parent.needsSep = true
      · simp only [if_pos h_sep, frameStepParser, flushChunkToParser,
          ByteArray.isEmpty, ByteArray.size_push]
        exact feedAll_find?_mono _ _ _ n o h
      · simp only [if_neg h_sep]
        by_cases h_exh : parent.offset ≥ parent.contents.size
        · rw [if_pos h_exh]
          cases h_charp : st.parser.charp with
          | ws =>
              simp only [frameStepParser]
              show (popExhaustedFrame st.parser st.base parent tail).db.objects[n]?
                = some o
              rw [popExhaustedFrame_objects]
              exact h
          | token cpos ctk =>
              have h_flush' : (flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)).db.find? n = some o := by
                unfold flushPendingToken
                simpa using feedToken_find?_mono ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) cpos ctk.toSlice n o h
              simp only [h_charp]
              cases h_e1 : (flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)).db.error? with
              | some it =>
                  cases it with
                  | mk e idx =>
                      simp only [h_e1]
                      cases h_req : parserIncludeRequestOfError? e with
                      | some req =>
                          cases req with
                          | pushFile sf incf =>
                              simp only [frameStepParser]
                              simpa [DB.find?, clearIncludeRequest] using h_flush'
                      | none =>
                          simp only [frameStepParser]
                          exact h_flush'
              | none =>
                  simp only [frameStepParser]
                  show (popExhaustedFrame _ st.base parent tail).db.objects[n]?
                    = some o
                  rw [popExhaustedFrame_objects]
                  exact h_flush'
        · rw [if_neg h_exh]
          have h_chunk : (({ st.parser with sourceFile := parent.fname } : ParserState).feedAll st.base (parent.contents.extract parent.offset parent.contents.size)).db.find? n = some o :=
            feedAll_find?_mono ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _ n o h
          cases h_e1 : (({ st.parser with sourceFile := parent.fname } : ParserState).feedAll st.base (parent.contents.extract parent.offset parent.contents.size)).db.error? with
          | some it =>
              cases it with
              | mk e idx =>
                  simp only [h_e1]
                  cases h_req : parserIncludeRequestOfError? e with
                  | some req =>
                      cases req with
                      | pushFile sf incf =>
                          simp only [frameStepParser]
                          simpa [DB.find?, clearIncludeRequest] using h_chunk
                  | none =>
                      simp only [frameStepParser]
                      exact h_chunk
          | none =>
              simp only [frameStepParser]
              exact h_chunk

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
/-- One driver step preserves the parser configuration.
(The scoped-off linters misfire here: the flagged rewrites drive the goal's
match reduction, and the `simpa` normalizes a sugar mismatch.) -/
theorem stepFrame_db_config (st : IncludeDriverState) :
    (frameStepParser (stepFrame st)).db.config = st.parser.db.config := by
  unfold stepFrame
  cases h_stack : st.stack with
  | nil => simp [frameStepParser]
  | cons parent tail =>
      by_cases h_sep : parent.needsSep = true
      · simp only [if_pos h_sep, frameStepParser, flushChunkToParser,
          ByteArray.isEmpty, ByteArray.size_push]
        exact ParserState.feedAll_db_config _ _ _
      · simp only [if_neg h_sep]
        by_cases h_exh : parent.offset ≥ parent.contents.size
        · rw [if_pos h_exh]
          cases h_charp : st.parser.charp with
          | ws =>
              simp only [frameStepParser]
              exact popExhaustedFrame_db_config st.parser st.base parent tail
          | token cpos ctk =>
              have h_flush' : (flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)).db.config = st.parser.db.config :=
                flushPendingToken_db_config _
              simp only [h_charp]
              cases h_e1 : (flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)).db.error? with
              | some it =>
                  cases it with
                  | mk e idx =>
                      simp only [h_e1]
                      cases h_req : parserIncludeRequestOfError? e with
                      | some req =>
                          cases req with
                          | pushFile sf incf =>
                              simp only [frameStepParser]
                              simpa [clearIncludeRequest] using h_flush'
                      | none =>
                          simp only [frameStepParser]
                          exact h_flush'
              | none =>
                  simp only [frameStepParser]
                  rw [popExhaustedFrame_db_config]
                  exact h_flush'
        · rw [if_neg h_exh]
          have h_chunk : (({ st.parser with sourceFile := parent.fname } : ParserState).feedAll st.base (parent.contents.extract parent.offset parent.contents.size)).db.config = st.parser.db.config :=
            ParserState.feedAll_db_config _ _ _
          cases h_e1 : (({ st.parser with sourceFile := parent.fname } : ParserState).feedAll st.base (parent.contents.extract parent.offset parent.contents.size)).db.error? with
          | some it =>
              cases it with
              | mk e idx =>
                  simp only [h_e1]
                  cases h_req : parserIncludeRequestOfError? e with
                  | some req =>
                      cases req with
                      | pushFile sf incf =>
                          simp only [frameStepParser]
                          simpa [clearIncludeRequest] using h_chunk
                  | none =>
                      simp only [frameStepParser]
                      exact h_chunk
          | none =>
              simp only [frameStepParser]
              exact h_chunk

set_option linter.unreachableTactic false in
/-- One driver step maintains the invariant package on every live path: a
`.done`/`.fed` result with no parser error, or any `.push` result (whose parser
is a cleared include request). -/
theorem stepFrame_maintains_driverInv (st : IncludeDriverState)
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false)
    (h_ok : (frameStepParser (stepFrame st)).db.error? = none
      ∨ ∃ sf incf d st', stepFrame st = .push sf incf d st') :
    DriverInv (frameStepParser (stepFrame st)) := by
  unfold stepFrame at h_ok ⊢
  cases h_stack : st.stack with
  | nil => simpa [h_stack, frameStepParser] using h
  | cons parent tail =>
      simp only [h_stack] at h_ok ⊢
      by_cases h_sep : parent.needsSep = true
      · rw [if_pos h_sep] at h_ok ⊢
        simp only [frameStepParser, flushChunkToParser,
          ByteArray.isEmpty, ByteArray.size_push] at h_ok ⊢
        rcases h_ok with h_ok | ⟨sf, incf, d, st', h_bad⟩
        · exact driverInv_feedAll_ok _ _ _ h h_strict h_no_dup h_ok
        · cases h_bad
      · rw [if_neg h_sep] at h_ok ⊢
        by_cases h_exh : parent.offset ≥ parent.contents.size
        · rw [if_pos h_exh] at h_ok ⊢
          cases h_charp : st.parser.charp with
          | ws =>
              simp only [h_charp, frameStepParser] at h_ok ⊢
              rcases h_ok with h_ok | ⟨sf, incf, d, st', h_bad⟩
              · exact driverInv_popExhaustedFrame_live _ _ _ _ h h_ok
              · cases h_bad
          | token cpos ctk =>
              simp only [h_charp] at h_ok ⊢
              have h_inp : DriverInv ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) :=
                driverInv_of_db_tokp_eq _ st.parser rfl rfl h
              cases h_e1 : (flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)).db.error? with
              | some it =>
                  cases it with
                  | mk e idx =>
                      simp only [h_e1] at h_ok ⊢
                      cases h_req : parserIncludeRequestOfError? e with
                      | some req =>
                          cases req with
                          | pushFile sf incf =>
                              simp only [h_req, frameStepParser] at h_ok ⊢
                              have h_e_shape : e = Error.includeRequest sf incf := by
                                revert h_req
                                unfold parserIncludeRequestOfError?
                                cases e <;> simp <;> (intro h1 h2; simp [h1, h2])
                              subst h_e_shape
                              have h_flush_req : (({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState).feedToken cpos ctk.toSlice).db.error? = some ⟨.includeRequest sf incf, idx⟩ := by
                                revert h_e1
                                unfold flushPendingToken
                                intro h_e1
                                simpa using h_e1
                              exact driverInv_of_db_tokp_eq _ _
                                (by unfold clearIncludeRequest flushPendingToken
                                    rfl)
                                (by unfold clearIncludeRequest flushPendingToken
                                    rfl)
                                (driverInv_of_request_step ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) cpos ctk.toSlice
                                  h_inp h_flush_req)
                      | none =>
                          simp only [h_req, frameStepParser] at h_ok ⊢
                          rcases h_ok with h_ok | ⟨sf, incf, d, st', h_bad⟩
                          · exfalso
                            rw [h_e1] at h_ok
                            cases h_ok
                          · cases h_bad
              | none =>
                  simp only [h_e1, frameStepParser] at h_ok ⊢
                  rcases h_ok with h_ok | ⟨sf, incf, d, st', h_bad⟩
                  · exact driverInv_popExhaustedFrame_live _ _ _ _
                      (driverInv_flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) h_inp h_strict h_no_dup h_e1)
                      h_ok
                  · cases h_bad
        · rw [if_neg h_exh] at h_ok ⊢
          have h_inp : DriverInv ({ st.parser with sourceFile := parent.fname } : ParserState) :=
            driverInv_of_db_tokp_eq _ st.parser rfl rfl h
          cases h_e1 : (({ st.parser with sourceFile := parent.fname } : ParserState).feedAll st.base (parent.contents.extract parent.offset parent.contents.size)).db.error? with
          | some it =>
              cases it with
              | mk e idx =>
                  simp only [h_e1] at h_ok ⊢
                  cases h_req : parserIncludeRequestOfError? e with
                  | some req =>
                      cases req with
                      | pushFile sf incf =>
                          simp only [h_req, frameStepParser] at h_ok ⊢
                          have h_e_shape : e = Error.includeRequest sf incf := by
                            revert h_req
                            unfold parserIncludeRequestOfError?
                            cases e <;> simp <;> (intro h1 h2; simp [h1, h2])
                          subst h_e_shape
                          exact feedAll_request_transport ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _
                            h_inp h_strict h_no_dup (by simpa using h_e1)
                  | none =>
                      simp only [h_req, frameStepParser] at h_ok ⊢
                      rcases h_ok with h_ok | ⟨sf, incf, d, st', h_bad⟩
                      · exfalso
                        rw [h_e1] at h_ok
                        cases h_ok
                      · cases h_bad
          | none =>
              simp only [h_e1, frameStepParser] at h_ok ⊢
              rcases h_ok with h_ok | ⟨sf, incf, d, st', h_bad⟩
              · exact driverInv_feedAll_ok ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _ h_inp h_strict h_no_dup h_e1
              · cases h_bad

/-- Pending-token flush created the entry: certificate on the flushing state. -/
theorem stepFrame_flush_case (s : ParserState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_old : s.db.find? n = none)
    (h_new : (flushPendingToken s).db.find? n = some (Object.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  revert h_new
  unfold flushPendingToken
  split
  · intro h_new
    exfalso
    rw [h_old] at h_new
    cases h_new
  · rename_i pos tk h_charp
    intro h_new
    have h_new' : (s.feedToken pos tk.toSlice).db.find? n
        = some (Object.assert f fr lbl) := by
      simpa [DB.find?] using h_new
    have h_ok := feedToken_new_assert_success s pos tk.toSlice n f fr lbl
      h_err0 h_old h_new'
    exact ⟨s, pos, tk.toSlice, h_inv, h_ghost, h_err0, h_old, h_ok, h_new',
      feedToken_new_assert_classified s pos tk.toSlice n f fr lbl
        h_old h_ok h_new'⟩

/-- Pending-token flush that ended in an error created nothing. -/
theorem stepFrame_flush_errored_case (s : ParserState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_err0 : s.db.error? = none)
    (h_old : s.db.find? n = none)
    {e : Error} {idx : Nat}
    (h_new : (flushPendingToken s).db.find? n = some (Object.assert f fr lbl))
    (h_errored : (flushPendingToken s).db.error? = some ⟨e, idx⟩) :
    False := by
  revert h_new h_errored
  unfold flushPendingToken
  split
  · intro h_new h_errored
    rw [h_old] at h_new
    cases h_new
  · rename_i pos tk h_charp
    intro h_new h_errored
    have h_new' : (s.feedToken pos tk.toSlice).db.find? n
        = some (Object.assert f fr lbl) := by
      simpa [DB.find?] using h_new
    have h_ok := feedToken_new_assert_success s pos tk.toSlice n f fr lbl
      h_err0 h_old h_new'
    have h_errored' : (s.feedToken pos tk.toSlice).db.error? = some ⟨e, idx⟩ := by
      simpa using h_errored
    rw [h_ok] at h_errored'
    cases h_errored'

/-- **Driver-step classification**: a fresh `.assert` across one `stepFrame` was
created by a classified transition.  Every parser mutation the driver performs —
separator flush, chunk `feedAll`, pending-token flush, boundary pop,
include-request clear — is covered, and chunks or flushes terminated by an
include-request error are handled by the success-free chronology. -/
theorem stepFrame_new_assert_strong_classified (st : IncludeDriverState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_inv : ParserOps.ParserStateInv st.parser)
    (h_ghost : ProofGhost st.parser.db st.parser.tokp)
    (h_err0 : st.parser.db.error? = none)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false)
    (h_old : st.parser.db.find? n = none)
    (h_new : (frameStepParser (stepFrame st)).db.find? n
      = some (Object.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  unfold stepFrame at h_new
  cases h_stack : st.stack with
  | nil =>
      simp only [h_stack, frameStepParser] at h_new
      rw [h_old] at h_new
      cases h_new
  | cons parent tail =>
      simp only [h_stack] at h_new
      by_cases h_sep : parent.needsSep = true
      · rw [if_pos h_sep] at h_new
        simp only [frameStepParser, flushChunkToParser,
          ByteArray.isEmpty, ByteArray.size_push] at h_new
        exact feedAll_new_assert_strong_classified_upto st.parser st.base _
          n f fr lbl h_inv h_ghost h_err0 h_strict h_no_dup h_old
          (by simpa [DB.find?] using h_new)
      · rw [if_neg h_sep] at h_new
        by_cases h_exh : parent.offset ≥ parent.contents.size
        · rw [if_pos h_exh] at h_new
          cases h_charp : st.parser.charp with
          | ws =>
              exfalso
              have h_new' : st.parser.db.find? n
                  = some (Object.assert f fr lbl) := by
                simpa [h_charp, frameStepParser, DB.find?,
                  popExhaustedFrame_objects] using h_new
              rw [h_old] at h_new'
              cases h_new'
          | token cpos ctk =>
              simp only [h_charp] at h_new
              cases h_e1 : (flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)).db.error? with
              | some it =>
                  cases it with
                  | mk e idx =>
                      exfalso
                      simp only [h_e1] at h_new
                      cases h_req : parserIncludeRequestOfError? e with
                      | some req =>
                          cases req with
                          | pushFile sf incf =>
                              simp only [h_req, frameStepParser] at h_new
                              exact stepFrame_flush_errored_case ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)
                                n f fr lbl h_err0 h_old
                                (by simpa [DB.find?, clearIncludeRequest]
                                  using h_new) h_e1
                      | none =>
                          simp only [h_req, frameStepParser] at h_new
                          exact stepFrame_flush_errored_case ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)
                            n f fr lbl h_err0 h_old
                            (by simpa [DB.find?] using h_new) h_e1
              | none =>
                  simp only [h_e1, frameStepParser] at h_new
                  exact stepFrame_flush_case ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) n f fr lbl
                    h_inv h_ghost h_err0 h_old
                    (by simpa [DB.find?, popExhaustedFrame_objects] using h_new)
        · rw [if_neg h_exh] at h_new
          cases h_e1 : (({ st.parser with sourceFile := parent.fname } : ParserState).feedAll st.base
              (parent.contents.extract parent.offset
                parent.contents.size)).db.error? with
          | some it =>
              cases it with
              | mk e idx =>
                  simp only [h_e1] at h_new
                  cases h_req : parserIncludeRequestOfError? e with
                  | some req =>
                      cases req with
                      | pushFile sf incf =>
                          simp only [h_req, frameStepParser] at h_new
                          exact feedAll_new_assert_strong_classified_upto
                            ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _ n f fr lbl
                            h_inv h_ghost h_err0 h_strict h_no_dup h_old
                            (by simpa [DB.find?, clearIncludeRequest]
                              using h_new)
                  | none =>
                      simp only [h_req, frameStepParser] at h_new
                      exact feedAll_new_assert_strong_classified_upto
                        ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _ n f fr lbl
                        h_inv h_ghost h_err0 h_strict h_no_dup h_old
                        (by simpa [DB.find?] using h_new)
          | none =>
              simp only [h_e1, frameStepParser] at h_new
              exact feedAll_new_assert_strong_classified_upto
                ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _ n f fr lbl
                h_inv h_ghost h_err0 h_strict h_no_dup h_old
                (by simpa [DB.find?] using h_new)

/-- Strong classification lifted through `feedAll`. -/
theorem feedAll_new_assert_strong_classified (s : ParserState) (base : Nat)
    (arr : ByteArray) (n : String) (f : Verify.Formula) (fr : Verify.Frame)
    (lbl : String)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_old : s.db.find? n = none)
    (h_success : (s.feedAll base arr).db.error? = none)
    (h_new : (s.feedAll base arr).db.find? n = some (.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  unfold ParserState.feedAll at h_success h_new
  cases h_charp : s.charp with
  | ws =>
      simp only [h_charp] at h_success h_new
      exact feed_new_assert_strong_classified base arr 0 .ws s n f fr lbl
        h_inv h_ghost h_err0 h_strict h_no_dup h_old h_success h_new
  | token base' tk =>
      simp only [h_charp] at h_success h_new
      exact feed_new_assert_strong_classified base arr 0 _
        ({ s with charp := default }) n f fr lbl
        h_inv h_ghost h_err0 h_strict h_no_dup h_old h_success h_new

/-- Strong classification through `done`, EOF flush included. -/
theorem done_new_assert_strong_classified (s : ParserState) (base : Nat)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_old : s.db.find? n = none)
    (h_success : (ParserState.done s base).error? = none)
    (h_new : (ParserState.done s base).find? n = some (.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  have h_e0 : s.db.error? = none :=
    ParserOps.done_no_error_implies_db_no_error s base h_success
  cases h_charp : s.charp with
  | ws =>
      rw [done_find?_eq_self s base n h_e0 h_charp, h_old] at h_new
      cases h_new
  | token pos tk =>
      have h_e1 : (s.feedToken pos tk.toSlice).db.error? = none := by
        cases h_e : (s.feedToken pos tk.toSlice).db.error? with
        | none => rfl
        | some it =>
            exfalso
            have h_stuck : (ParserState.done s base).error? ≠ none := by
              simp only [ParserState.done, Id.run, DB.error, Option.isSome_some,
                Option.isSome_none, Bool.false_eq_true, reduceIte,
                h_e0, h_charp, h_e]
              simp [h_e]
            exact h_stuck h_success
      rw [done_find?_eq_flush s base pos tk n h_e0 h_charp h_e1] at h_new
      exact ⟨s, pos, tk.toSlice, h_inv, h_ghost, h_e0, h_old, h_e1, h_new,
        feedToken_new_assert_classified s pos tk.toSlice n f fr lbl
          h_old h_e1 h_new⟩

/-- Strong classification for the pure entry point. -/
theorem checkBytes_new_assert_strong_classified (arr : ByteArray)
    (config : ModeConfig) (h_cfg : config.prefixCertified)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_success : (checkBytes arr config).error? = none)
    (h_new : (checkBytes arr config).find? n = some (.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  unfold checkBytes at h_success h_new
  by_cases h_c : (checkBytesCore arr config).error? = none
  · simp only [h_c, reduceIte] at h_success h_new
    by_cases h_g : (((checkBytesCore arr config).config.allowDuplicateFloat
        || (checkBytesCore arr config).wellFormed?)
        && (checkBytesCore arr config).assertDvVarsInFrame?) = true
    · simp only [h_g, if_true] at h_success h_new
      unfold checkBytesCore at h_c h_new
      by_cases h_mid : (({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr).db.find? n = none
      · exact done_new_assert_strong_classified (({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr) arr.size
          n f fr lbl
          (ParserOps.feedAll_maintains_stateInv ({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState) 0 arr
            (ParserOps.initState_inv config) rfl h_cfg.2
            (ParserOps.done_no_error_implies_db_no_error _ arr.size h_c))
          (feedAll_maintains_ghost ({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState) 0 arr trivial
            (ParserOps.initState_inv config) rfl h_cfg.2 h_cfg.1
            (ParserOps.done_no_error_implies_db_no_error _ arr.size h_c))
          h_mid h_c h_new
      · cases h_val : (({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr).db.find? n with
        | none => exact absurd h_val h_mid
        | some entry =>
            have h_persist := done_find?_mono (({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr) arr.size n
              entry h_val
            have h_entry : entry = .assert f fr lbl := by
              rw [h_persist] at h_new
              exact Option.some.inj h_new
            subst h_entry
            exact feedAll_new_assert_strong_classified ({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState) 0 arr n f fr lbl
              (ParserOps.initState_inv config) trivial rfl h_cfg.1 h_cfg.2
              (default_db_find?_none n)
              (ParserOps.done_no_error_implies_db_no_error _ arr.size h_c) h_val
    · exfalso
      rw [if_neg h_g] at h_success
      simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]
        at h_success
  · exfalso
    rw [if_neg h_c] at h_success
    exact h_c h_success

/-- Field constructor for `FinishProofEvent`.

This packages the five fields; it proves no existential and is **not** evidence
that any event occurs.  It is useful only where a caller already holds the
fields.  Anything claiming that events do occur must construct them from an
actual run. -/
theorem FinishProofEvent.of_fields (s : ParserState) (i : Nat) (tk : ByteSlice)
    (pr : ProofState)
    (h_tokp : s.tokp = .proof pr)
    (h_not_open : tk.eqArray "$(".toAscii = false)
    (h_not_incl : tk.eqArray "$[".toAscii = false)
    (h_close : tk.eqArray "$.".toAscii = true)
    (h_ok : (s.feedToken i tk).db.error? = none) :
    FinishProofEvent s i tk pr :=
  ⟨h_tokp, h_not_open, h_not_incl, h_close, h_ok⟩

/-- A finish-proof event runs `finishProof`: the `$.` token in proof mode is
exactly the branch that discharges the proof and inserts the assertion. -/
theorem finishProofEvent_feedToken_eq (s : ParserState) (i : Nat) (tk : ByteSlice)
    (pr : ProofState) (h_evt : FinishProofEvent s i tk pr) :
    s.feedToken i tk = ({ s with tokp := default }).finishProof pr := by
  obtain ⟨h_tokp, h_open, h_incl, h_close, _⟩ := h_evt
  simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_close]

/-- **Event to entry, with its formula-level justification.** The assertion a
finish-proof event stores is present in the database immediately afterwards,
and its formula was already `Spec.Provable` under the full active frame in the
database as it stood before the event. The proof used is the written proof.

This does not yet identify that active-frame proposition with the declarative
meaning of the exact trimmed statement stored in `pr.frame`.

This reads the guarantee per event-created entry.  It does not by itself say
that every stored `$p` entry arose from such an event; that coverage statement
is separate and still open. -/
theorem finishProofEvent_stores_provable_entry
    (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState)
    (h_inv : ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_no_err : s.db.error? = none)
    (h_evt : FinishProofEvent s i tk pr) :
    (s.feedToken i tk).db
        = (s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame)).recordIncomplete
            pr.incomplete pr.label ∧
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase s.db = some Γ ∧
        toFrame s.db s.db.frame = some fr ∧
        Spec.Provable Γ fr (toExpr pr.fmla) := by
  refine ⟨?_, feedToken_finishProofEvent_prefixProvable s i tk pr h_inv h_ghost
    h_no_err h_evt⟩
  have h_eq := finishProofEvent_feedToken_eq s i tk pr h_evt
  have h_ok : (({ s with tokp := default }).finishProof pr).db.error? = none := by
    rw [← h_eq]; exact h_evt.2.2.2.2
  have h_ins := (ParserOps.finishProof_success_insert { s with tokp := default } pr h_ok).1
  rw [h_eq, h_ins]

/-- Prefix provability over the **feed loop**.

After a successful `checkBytes`, every finish-proof event raised by the feed loop
yields `Spec.Provable` in the database as it stood *at that event* — before the
proved assertion is inserted.  So such a proof is derived from assertions that
already existed, using the proof actually written, with no appeal to the theorem
being proved; `finishProofEvent_stores_provable_entry` turns the event into the
entry it creates.

Read the scope exactly.  This quantifies over finish-proof events **of the feed
loop**.  It does not cover the final token that `feedAll` leaves buffered for
`done`, so a theorem whose closing `$.` is the last token of the file with no
trailing whitespace is outside it.  Nor does it assert that every `$p` in the
source raises an event. -/
theorem checkBytes_feedEvents_prefix_provable
    (arr : ByteArray) (config : ModeConfig)
    (h_strict : config.rejectUnknownSteps = true)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_success : (checkBytes arr config).error? = none) :
    AllFeedAllEventsProvable 0 arr
      { (default : ParserState) with db := { (default : DB) with config := config } } :=
  (checkBytes_prefix_provenance arr config h_strict h_no_dup h_success).1

/-- Eliminator at the **final** `feedAll` state only.

Note the narrowness deliberately: `FinishProofEvent` requires `tokp = .proof`,
while `done` accepts only `tokp = .start`, so this hypothesis is satisfiable
just when the last token of the file is the `$.` that closes a `$p`.  It is a
corner case, not the soundness statement — for that use
`checkBytes_feedEvents_prefix_provable`, which covers the feed loop's
finish-proof events and is the fold-wide content this projects away. -/
theorem checkBytes_finalState_finishProofEvent_prefix_provable
    (arr : ByteArray) (config : ModeConfig)
    (h_strict : config.rejectUnknownSteps = true)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_success : (checkBytes arr config).error? = none) :
    let s₀ : ParserState := { (default : ParserState) with
      db := { (default : DB) with config := config } }
    ∀ (pos : Nat) (tk : ByteSlice) (pr : ProofState),
      FinishProofEvent (s₀.feedAll 0 arr) pos tk pr →
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase (s₀.feedAll 0 arr).db = some Γ ∧
        toFrame (s₀.feedAll 0 arr).db (s₀.feedAll 0 arr).db.frame = some fr ∧
        Spec.Provable Γ fr (toExpr pr.fmla) := by
  intro s₀ pos tk pr h_evt
  exact (checkBytes_prefix_provenance arr config h_strict h_no_dup h_success).2 pos tk pr h_evt

-- ═══════════════════════════════════════════════════════════════════════════════
-- Certified API: prefix-provenance under ModeConfig.prefixCertified
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Certified prefix provenance (`checkBytesCore`): under a `prefixCertified` config,
    every feedToken finishProof event yields `Spec.Provable` in the pre-insertion DB. -/
theorem checkBytesCore_prefix_provenance_certified (arr : ByteArray) (config : ModeConfig)
    (h_cfg : config.prefixCertified)
    (h_success : (checkBytesCore arr config).error? = none) :
    let s₀ : ParserState := { (default : ParserState) with
      db := { (default : DB) with config := config } }
    AllFeedAllEventsProvable 0 arr s₀ ∧
    EventProvableAt (s₀.feedAll 0 arr) :=
  checkBytesCore_prefix_provenance arr config h_cfg.1 h_cfg.2 h_success

/-- Certified prefix provenance (`checkBytes`): under a `prefixCertified` config,
    every feedToken finishProof event yields `Spec.Provable` in the pre-insertion DB. -/
theorem checkBytes_prefix_provenance_certified (arr : ByteArray) (config : ModeConfig)
    (h_cfg : config.prefixCertified)
    (h_success : (checkBytes arr config).error? = none) :
    let s₀ : ParserState := { (default : ParserState) with
      db := { (default : DB) with config := config } }
    AllFeedAllEventsProvable 0 arr s₀ ∧
    EventProvableAt (s₀.feedAll 0 arr) :=
  checkBytes_prefix_provenance arr config h_cfg.1 h_cfg.2 h_success

/-- The certified form of `checkBytes_feedEvents_prefix_provable`; the same feed-loop
scope and the same two exclusions apply. -/
theorem checkBytes_feedEvents_prefix_provable_certified
    (arr : ByteArray) (config : ModeConfig)
    (h_cfg : config.prefixCertified)
    (h_success : (checkBytes arr config).error? = none) :
    AllFeedAllEventsProvable 0 arr
      { (default : ParserState) with db := { (default : DB) with config := config } } :=
  (checkBytes_prefix_provenance_certified arr config h_cfg h_success).1

/-- An axiom-finish event that created an entry pins its whole payload: the
transition *is* `insertAxiom` on the statement's own label and formula, the
stored fields are exactly those, and the constant-head and trim gates passed —
derived from creation. -/
theorem axiomFinishEvent_created (s' : ParserState) (j : Nat) (tk : ByteSlice)
    (arr' : Array Verify.Sym) (p : TokensParser)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_evt : AxiomFinishEvent s' j tk arr' p)
    (h_err0 : s'.db.error? = none)
    (h_before : s'.db.find? n = none)
    (h_after : (s'.feedToken j tk).db.find? n = some (.assert f fr lbl)) :
    (s'.feedToken j tk).db = s'.db.insertAxiom p.pos p.label arr' ∧
      n = p.label ∧ f = arr' ∧ lbl = n ∧ Formula.hasConstHead arr' = true ∧
      s'.db.trimFrame' arr' = .ok fr := by
  have h_eq := axiomFinishEvent_feedToken_eq s' j tk arr' p h_evt
  have h_ok := h_evt.2.2.2.2.2
  rw [h_eq] at h_ok h_after
  cases p with
  | mk k ppos plab =>
      have h_kind : k = TokensKind.ax := h_evt.2.1
      subst h_kind
      have h_head : Formula.hasConstHead arr' = true := by
        cases h_h : Formula.hasConstHead arr' with
        | true => rfl
        | false =>
            exfalso
            have h_after' := h_after
            unfold ParserState.feedTokens at h_after'
            rw [withAt_find?] at h_after'
            simp only [Id.run, h_h] at h_after'
            have h_after'' : s'.db.find? n = some (.assert f fr lbl) := by
              simpa [ParserState.mkErrorFromEvidence,
                ParserState.mkErrorWithEvidence, ParserState.mkError,
                ParserState.withDB, DB.find?, DB.mkErrorWithEvidence,
                DB.mkError] using h_after'
            rw [h_before] at h_after''
            cases h_after''
      have h_body_eq : (ParserState.feedTokens s' arr'
          ⟨TokensKind.ax, ppos, plab⟩).db
          = s'.db.insertAxiom ppos plab arr' := by
        unfold ParserState.feedTokens
        rw [withAt_db_of_no_error plab _ (by
          unfold ParserState.feedTokens at h_ok
          exact h_ok)]
        simp [Id.run, h_head, ParserState.withDB]
      rw [h_eq, h_body_eq]
      rw [h_body_eq] at h_after
      obtain ⟨h_n, h_f, h_lbl, h_hd, h_tf⟩ :=
        ParserOps.insertAxiom_new_assert_origin s'.db ppos plab arr'
          n f fr lbl h_err0 h_before h_after
      exact ⟨rfl, h_n, h_f, h_lbl, h_hd, h_tf⟩

/-- Certified eliminator at the **final** `feedAll` state only.  Narrow by
construction (see `checkBytes_finalState_finishProofEvent_prefix_provable`); it is
not the soundness statement. -/
theorem checkBytes_finalState_finishProofEvent_certified (arr : ByteArray) (config : ModeConfig)
    (h_cfg : config.prefixCertified)
    (h_success : (checkBytes arr config).error? = none) :
    let s₀ : ParserState := { (default : ParserState) with
      db := { (default : DB) with config := config } }
    ∀ (pos : Nat) (tk : ByteSlice) (pr : ProofState),
      FinishProofEvent (s₀.feedAll 0 arr) pos tk pr →
      ∃ (Γ : Spec.Database) (fr : Spec.Frame),
        toDatabase (s₀.feedAll 0 arr).db = some Γ ∧
        toFrame (s₀.feedAll 0 arr).db (s₀.feedAll 0 arr).db.frame = some fr ∧
        Spec.Provable Γ fr (toExpr pr.fmla) :=
  checkBytes_finalState_finishProofEvent_prefix_provable arr config h_cfg.1 h_cfg.2 h_success

/-- A successful finish-proof event's label was fresh: `finishProof` inserts,
and insertion of a non-variable at an occupied label errors.  Together with
registry monotonicity this is the at-most-one direction: after the event the
label is occupied forever, so no second successful finish can carry it. -/
theorem finishProofEvent_label_fresh (s : ParserState) (i : Nat) (tk : ByteSlice)
    (pr : ProofState) (h_evt : FinishProofEvent s i tk pr)
    (h_err0 : s.db.error? = none) :
    s.db.find? pr.label = none := by
  have h_eq := finishProofEvent_feedToken_eq s i tk pr h_evt
  have h_ok := h_evt.2.2.2.2
  rw [h_eq] at h_ok
  have h_ins := ParserOps.finishProof_success_insert _ pr h_ok
  have h_ok2 : (s.db.insert pr.pos pr.label
      (.assert pr.fmla pr.frame)).error? = none := h_ins.2
  exact ParserOps.insert_success_nonvar_fresh s.db pr.pos pr.label
    (.assert pr.fmla pr.frame) h_err0 h_ok2
    (fun v h => by cases h)

/-- Consume a strong certificate into the payload-carrying origin
disjunction: the `$a` side with derived gates and exact insertion equation,
or the `$p` side with the binding equalities and pre-insertion
`Spec.Provable`.  Shared by the pure and single-pass capstones. -/
theorem strongNewAssertCertificate_origin_provable
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (cert : StrongNewAssertCertificate n f fr lbl) :
    (∃ (s' : ParserState) (j : Nat) (tk : ByteSlice)
        (arr' : Array Verify.Sym) (p : TokensParser),
        AxiomFinishEvent s' j tk arr' p ∧
        p.label = n ∧ f = arr' ∧ lbl = n ∧
        Formula.hasConstHead arr' = true ∧
        s'.db.find? n = none ∧
        (s'.feedToken j tk).db = s'.db.insertAxiom p.pos p.label arr' ∧
        s'.db.trimFrame' arr' = .ok fr)
      ∨ (∃ (s' : ParserState) (j : Nat) (tk : ByteSlice) (pr : ProofState)
          (Γ : Spec.Database) (specFr : Spec.Frame),
          FinishProofEvent s' j tk pr ∧
          pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
          s'.db.find? n = none ∧
          (s'.feedToken j tk).db
            = (s'.db.insert pr.pos pr.label
                (.assert pr.fmla pr.frame)).recordIncomplete
                  pr.incomplete pr.label ∧
          toDatabase s'.db = some Γ ∧
          toFrame s'.db s'.db.frame = some specFr ∧
          Spec.Provable Γ specFr (toExpr f)) := by
  obtain ⟨s', j, tk, h_inv, h_ghost, h_err0, h_before, h_step_ok, h_after,
    h_event⟩ := cert
  cases h_event with
  | inl h_ax =>
      obtain ⟨arr', p, h⟩ := h_ax
      obtain ⟨h_ins, h_n, h_f, h_lbl, h_hd, h_tf⟩ :=
        axiomFinishEvent_created s' j tk arr' p n f fr lbl h h_err0
          h_before h_after
      exact Or.inl ⟨s', j, tk, arr', p, h, h_n.symm, h_f, h_lbl, h_hd,
        h_before, h_ins, h_tf⟩
  | inr h_th =>
      obtain ⟨pr, h_evt⟩ := h_th
      obtain ⟨h_ins0, Γ, specFr, h_toDb, h_toFr, h_prov⟩ :=
        finishProofEvent_stores_provable_entry s' j tk pr h_inv h_ghost
          h_err0 h_evt
      have h_ins : (s'.feedToken j tk).db
          = (s'.db.insert pr.pos pr.label
              (.assert pr.fmla pr.frame)).recordIncomplete pr.incomplete
                pr.label := h_ins0
      have h_after' : (s'.db.insert pr.pos pr.label
          (.assert pr.fmla pr.frame)).find? n = some (.assert f fr lbl) := by
        have h_a := h_after
        rw [h_ins, DB.recordIncomplete_find?] at h_a
        exact h_a
      obtain ⟨h_n_eq, h_obj⟩ :=
        ParserOps.insert_new_assert_origin s'.db pr.pos pr.label
          (.assert pr.fmla pr.frame) n f fr lbl h_before h_after'
      have h_fm : pr.fmla = f := by injection h_obj with h1 h2 h3
      have h_fr : pr.frame = fr := by injection h_obj with h1 h2 h3
      have h_lbl : pr.label = lbl := by injection h_obj with h1 h2 h3
      refine Or.inr ⟨s', j, tk, pr, Γ, specFr, h_evt, h_n_eq.symm, h_fm, h_fr,
        ?_, h_before, h_ins, h_toDb, h_toFr, h_fm ▸ h_prov⟩
      rw [← h_lbl, h_n_eq]

/-- **Item-3 capstone: every stored theorem carries its written proof's
derivation.**

Under a proof-certified configuration, every `.assert` stored by an accepted
`checkBytes` run either originated from a `$a` (an `AxiomFinishEvent`), or from
the `$.` of a `$p` — a concrete `FinishProofEvent` whose proof state binds the
stored label, formula and frame exactly, and whose formula is `Spec.Provable`
in the database as it stood **before** the insertion.  Self-citation is
impossible by construction: the derivation lives in the pre-insertion database,
which by `finishProofEvent_label_fresh` does not contain the label at all. -/
theorem checkBytes_assert_origin_provable (arr : ByteArray)
    (config : ModeConfig) (h_cfg : config.prefixCertified)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_success : (checkBytes arr config).error? = none)
    (h_new : (checkBytes arr config).find? n = some (.assert f fr lbl)) :
    (∃ (s' : ParserState) (j : Nat) (tk : ByteSlice)
        (arr' : Array Verify.Sym) (p : TokensParser),
        AxiomFinishEvent s' j tk arr' p ∧
        p.label = n ∧ f = arr' ∧ lbl = n ∧
        Formula.hasConstHead arr' = true ∧
        s'.db.find? n = none ∧
        (s'.feedToken j tk).db = s'.db.insertAxiom p.pos p.label arr' ∧
        s'.db.trimFrame' arr' = .ok fr)
      ∨ (∃ (s' : ParserState) (j : Nat) (tk : ByteSlice) (pr : ProofState)
          (Γ : Spec.Database) (specFr : Spec.Frame),
          FinishProofEvent s' j tk pr ∧
          pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
          s'.db.find? n = none ∧
          (s'.feedToken j tk).db
            = (s'.db.insert pr.pos pr.label
                (.assert pr.fmla pr.frame)).recordIncomplete
                  pr.incomplete pr.label ∧
          toDatabase s'.db = some Γ ∧
          toFrame s'.db s'.db.frame = some specFr ∧
          Spec.Provable Γ specFr (toExpr f)) := by
  exact strongNewAssertCertificate_origin_provable n f fr lbl
    (checkBytes_new_assert_strong_classified arr config h_cfg n f fr lbl
      h_success h_new)


/-! ### Trace-relative uniqueness: at most one creating event per label

`checkBytes_new_assert_classified` gives *existence*: every stored assertion has
a creating event.  This section gives *at-most-one*: a label admits at most one
successful creating event in a chronological run, and at a fixed transition the
event payload is fully determined.  Together those are the "exactly one matching
finish" reading of the origin trace. -/

/-- Chronological reachability: `s` evolves to `s'` by zero or more `feedToken`
steps.  `feed`, `feedAll`, and `done`'s flush all advance the state along this
relation, so any two flush events of one run are comparable through it. -/
inductive FeedReaches : ParserState → ParserState → Prop
  | refl (s : ParserState) : FeedReaches s s
  | step (s : ParserState) (i : Nat) (tk : ByteSlice) {s' : ParserState}
      (h : FeedReaches (s.feedToken i tk) s') : FeedReaches s s'

/-- Write-once monotonicity transported along reachability. -/
theorem feedReaches_find?_mono {s s' : ParserState} (h : FeedReaches s s')
    (n : String) (o : Verify.Object) (h_find : s.db.find? n = some o) :
    s'.db.find? n = some o := by
  induction h with
  | refl s => exact h_find
  | step s i tk h ih => exact ih (feedToken_find?_mono s i tk n o h_find)

/-- A successful finish-proof event leaves its label stored. -/
theorem finishProofEvent_label_stored (s : ParserState) (i : Nat) (tk : ByteSlice)
    (pr : ProofState) (h_evt : FinishProofEvent s i tk pr)
    (h_err0 : s.db.error? = none) :
    (s.feedToken i tk).db.find? pr.label
      = some (Object.assert pr.fmla pr.frame pr.label) := by
  have h_eq := finishProofEvent_feedToken_eq s i tk pr h_evt
  have h_ok := h_evt.2.2.2.2
  rw [h_eq] at h_ok
  have h_ins := ParserOps.finishProof_success_insert _ pr h_ok
  have h_fresh := finishProofEvent_label_fresh s i tk pr h_evt h_err0
  rw [h_eq, h_ins.1, DB.recordIncomplete_find?]
  exact Verify.DB.insert_find?_self s.db pr.pos pr.label
    (.assert pr.fmla pr.frame)
    ((Metamath.ParserCorrectness.error_false_iff_error?_none s.db).2 h_err0)
    h_fresh
    ((Metamath.ParserCorrectness.error_false_iff_error?_none _).2 h_ins.2)

/-- A successful axiom-finish event's guard held: the formula's head is a
constant.  Derived from success, not assumed. -/
theorem axiomFinishEvent_success_hasConstHead (s : ParserState) (i : Nat)
    (tk : ByteSlice) (arr : Array Verify.Sym) (p : TokensParser)
    (h_evt : AxiomFinishEvent s i tk arr p) :
    Formula.hasConstHead arr = true := by
  by_cases h_h : Formula.hasConstHead arr
  · exact h_h
  · exfalso
    have h_eq := axiomFinishEvent_feedToken_eq s i tk arr p h_evt
    have h_ok := h_evt.2.2.2.2.2
    rw [h_eq] at h_ok
    have h_kind := h_evt.2.1
    obtain ⟨k, ppos, plab⟩ := p
    cases h_kind
    unfold ParserState.feedTokens at h_ok
    rw [withAt_error?_none_iff] at h_ok
    simp only [Id.run, h_h, Bool.false_eq_true, if_false] at h_ok
    exact ParserState_mkErrorFromEvidence_sets_error s ppos
      (.scopeDecl .firstSymbolNotConstant) h_ok

/-- A successful axiom-finish event's label was fresh at the event. -/
theorem axiomFinishEvent_label_fresh (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser)
    (h_evt : AxiomFinishEvent s i tk arr p) :
    s.db.find? p.label = none := by
  have h_head := axiomFinishEvent_success_hasConstHead s i tk arr p h_evt
  have h_ins := axiomFinishEvent_inserts_axiom s i tk arr p h_evt h_head
  have h_ok := h_evt.2.2.2.2.2
  rw [h_ins] at h_ok
  exact ParserOps.insertAxiom_success_fresh_db s.db p.pos p.label arr h_ok

/-- A successful axiom-finish event leaves its label stored. -/
theorem axiomFinishEvent_label_stored (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser)
    (h_evt : AxiomFinishEvent s i tk arr p) (h_err0 : s.db.error? = none) :
    ∃ fr, (s.feedToken i tk).db.find? p.label
      = some (Object.assert arr fr p.label) := by
  have h_head := axiomFinishEvent_success_hasConstHead s i tk arr p h_evt
  have h_ins := axiomFinishEvent_inserts_axiom s i tk arr p h_evt h_head
  have h_ok := h_evt.2.2.2.2.2
  rw [h_ins] at h_ok ⊢
  obtain ⟨fr, h_trim, _h_int, h_insert_ok⟩ :=
    ParserOps.insertAxiom_success_conditions s.db p.pos p.label arr h_ok
  have h_fresh := ParserOps.insertAxiom_success_fresh_db s.db p.pos p.label arr h_ok
  refine ⟨fr, ?_⟩
  have h_eq : s.db.insertAxiom p.pos p.label arr
      = s.db.insert p.pos p.label (.assert arr fr) := by
    unfold DB.insertAxiom
    have h_err_bool : s.db.error = false :=
      (Metamath.ParserCorrectness.error_false_iff_error?_none s.db).2 h_err0
    have h_int_false : s.db.interrupt = false := _h_int
    simp only [h_head, if_true, h_err_bool, h_trim, h_int_false,
      Bool.false_eq_true, reduceIte]
  rw [h_eq]
  exact Verify.DB.insert_find?_self s.db p.pos p.label (.assert arr fr)
    ((Metamath.ParserCorrectness.error_false_iff_error?_none s.db).2 h_err0)
    h_fresh
    ((Metamath.ParserCorrectness.error_false_iff_error?_none _).2 h_insert_ok)

/-- A creating event for label `l`: the transition is the `$.` of a `$a` or of a
`$p` whose label is `l`.  Exactly the disjunction the classification masters
produce. -/
def CreatesLabel (s : ParserState) (i : Nat) (tk : ByteSlice) (l : String) : Prop :=
  (∃ arr p, AxiomFinishEvent s i tk arr p ∧ p.label = l)
    ∨ (∃ pr, FinishProofEvent s i tk pr ∧ pr.label = l)

/-- Any creating event leaves its label stored. -/
theorem createsLabel_stored {s : ParserState} {i : Nat} {tk : ByteSlice}
    {l : String} (h : CreatesLabel s i tk l) (h_err0 : s.db.error? = none) :
    ∃ e, (s.feedToken i tk).db.find? l = some e := by
  cases h with
  | inl h_ax =>
      obtain ⟨arr, p, h_evt, h_lbl⟩ := h_ax
      obtain ⟨fr, h_stored⟩ := axiomFinishEvent_label_stored s i tk arr p h_evt h_err0
      exact ⟨_, h_lbl ▸ h_stored⟩
  | inr h_pf =>
      obtain ⟨pr, h_evt, h_lbl⟩ := h_pf
      exact ⟨_, h_lbl ▸ finishProofEvent_label_stored s i tk pr h_evt h_err0⟩

/-- Any creating event's label was fresh at the event. -/
theorem createsLabel_fresh {s : ParserState} {i : Nat} {tk : ByteSlice}
    {l : String} (h : CreatesLabel s i tk l) (h_err0 : s.db.error? = none) :
    s.db.find? l = none := by
  cases h with
  | inl h_ax =>
      obtain ⟨arr, p, h_evt, h_lbl⟩ := h_ax
      exact h_lbl ▸ axiomFinishEvent_label_fresh s i tk arr p h_evt
  | inr h_pf =>
      obtain ⟨pr, h_evt, h_lbl⟩ := h_pf
      exact h_lbl ▸ finishProofEvent_label_fresh s i tk pr h_evt h_err0

/-- **At most one creating event per label.**  If a creating event for `l` fires
and the run then reaches another error-free state, no second creating event for
`l` can fire there: the first event stored the label (write-once monotonicity
keeps it stored), while a second event would require it fresh. -/
theorem createsLabel_at_most_once {s₁ s₂ : ParserState} {i₁ i₂ : Nat}
    {tk₁ tk₂ : ByteSlice} {l : String}
    (h₁ : CreatesLabel s₁ i₁ tk₁ l) (h_err₁ : s₁.db.error? = none)
    (h_reach : FeedReaches (s₁.feedToken i₁ tk₁) s₂)
    (h₂ : CreatesLabel s₂ i₂ tk₂ l) (h_err₂ : s₂.db.error? = none) : False := by
  obtain ⟨e, h_stored⟩ := createsLabel_stored h₁ h_err₁
  have h_still := feedReaches_find?_mono h_reach l e h_stored
  have h_fresh := createsLabel_fresh h₂ h_err₂
  rw [h_fresh] at h_still
  cases h_still

/-- **Trace-relative uniqueness.**  Two creating events for the same label,
one chronologically after the other in either order, are impossible.  Combined
with `checkBytes_new_assert_classified` (existence) and the determinism lemmas
below (payload pinned at a fixed transition), every stored assertion has exactly
one matching creating event in the run. -/
theorem createsLabel_unique {s₁ s₂ : ParserState} {i₁ i₂ : Nat}
    {tk₁ tk₂ : ByteSlice} {l : String}
    (h₁ : CreatesLabel s₁ i₁ tk₁ l) (h_err₁ : s₁.db.error? = none)
    (h₂ : CreatesLabel s₂ i₂ tk₂ l) (h_err₂ : s₂.db.error? = none)
    (h_order : FeedReaches (s₁.feedToken i₁ tk₁) s₂
      ∨ FeedReaches (s₂.feedToken i₂ tk₂) s₁) : False := by
  cases h_order with
  | inl h => exact createsLabel_at_most_once h₁ h_err₁ h h₂ h_err₂
  | inr h => exact createsLabel_at_most_once h₂ h_err₂ h h₁ h_err₁

/-- At a fixed transition, the finish-proof payload is determined. -/
theorem finishProofEvent_deterministic {s : ParserState} {i : Nat}
    {tk : ByteSlice} {pr pr' : ProofState}
    (h₁ : FinishProofEvent s i tk pr) (h₂ : FinishProofEvent s i tk pr') :
    pr = pr' := by
  have h := h₁.1.symm.trans h₂.1
  injection h

/-- At a fixed transition, the axiom-finish payload is determined. -/
theorem axiomFinishEvent_deterministic {s : ParserState} {i : Nat}
    {tk : ByteSlice} {arr arr' : Array Verify.Sym} {p p' : TokensParser}
    (h₁ : AxiomFinishEvent s i tk arr p) (h₂ : AxiomFinishEvent s i tk arr' p') :
    arr = arr' ∧ p = p' := by
  have h := h₁.1.symm.trans h₂.1
  injection h with h_arr h_p
  exact ⟨h_arr, h_p⟩


/-! ### Phase layer: `runPureSteps`

The executable's pure phase, classified.  Every theorem here is proven by the
functional induction of `runPureSteps` itself — the recursion the binary runs —
composing the sealed `stepFrame` pillars step by step. -/

/-- A `.done` phase result is the input state unchanged: only the empty-stack
branch produces it. -/
theorem stepFrame_done_inv (st st' : IncludeDriverState)
    (h : stepFrame st = .done st') : st' = st := by
  unfold stepFrame at h
  cases h_stack : st.stack with
  | nil =>
      rw [h_stack] at h
      dsimp only [] at h
      injection h with h
      exact h.symm
  | cons frame rest =>
      rw [h_stack] at h
      dsimp only [] at h
      by_cases h_sep : frame.needsSep = true
      · rw [if_pos h_sep] at h
        exact absurd h (by simp)
      · rw [if_neg h_sep] at h
        by_cases h_exh : frame.offset ≥ frame.contents.size
        · rw [if_pos h_exh] at h
          cases h_charp : st.parser.charp with
          | ws =>
              rw [h_charp] at h
              dsimp only [] at h
              exact absurd h (by simp)
          | token pos tk =>
              rw [h_charp] at h
              dsimp only [] at h
              cases h_e : (flushPendingToken
                  { db := st.parser.db, tokp := st.parser.tokp,
                    charp := CharParser.token pos tk, line := st.parser.line,
                    linepos := st.parser.linepos,
                    sourceFile := frame.fname }).db.error? with
              | some intr =>
                  obtain ⟨err, consumed⟩ := intr
                  rw [h_e] at h
                  dsimp only [] at h
                  cases h_req : parserIncludeRequestOfError? err with
                  | some req =>
                      cases req with
                      | pushFile src inc =>
                          rw [h_req] at h
                          exact absurd h (by simp)
                  | none =>
                      rw [h_req] at h
                      exact absurd h (by simp)
              | none =>
                  rw [h_e] at h
                  dsimp only [] at h
                  exact absurd h (by simp)
        · rw [if_neg h_exh] at h
          cases h_e : (ParserState.feedAll
              { db := st.parser.db, tokp := st.parser.tokp,
                charp := st.parser.charp, line := st.parser.line,
                linepos := st.parser.linepos, sourceFile := frame.fname }
              st.base
              (frame.contents.extract frame.offset frame.contents.size)).db.error? with
          | some intr =>
              obtain ⟨err, consumed⟩ := intr
              rw [h_e] at h
              dsimp only [] at h
              cases h_req : parserIncludeRequestOfError? err with
              | some req =>
                  cases req with
                  | pushFile src inc =>
                      rw [h_req] at h
                      exact absurd h (by simp)
              | none =>
                  rw [h_req] at h
                  exact absurd h (by simp)
          | none =>
              rw [h_e] at h
              dsimp only [] at h
              exact absurd h (by simp)

/-- Result-parser projection of a pure driver phase. -/
def driverPhaseParser : DriverPhase → ParserState
  | .done st => st.parser
  | .stopped st => st.parser
  | .push _ _ _ st => st.parser

/-- Registry write-once monotonicity across a whole pure phase. -/
theorem runPureSteps_find?_mono (st : IncludeDriverState) (n : String)
    (o : Object) (h : st.parser.db.find? n = some o) :
    (driverPhaseParser (runPureSteps st)).db.find? n = some o := by
  revert h
  fun_induction runPureSteps st
  case case1 st st' _h =>
      intro h
      have h_step := stepFrame_find?_mono st n o h
      rw [_h] at h_step
      simpa [frameStepParser, driverPhaseParser] using h_step
  case case2 st sf incf d st' _h =>
      intro h
      have h_step := stepFrame_find?_mono st n o h
      rw [_h] at h_step
      simpa [frameStepParser, driverPhaseParser] using h_step
  case case3 st st' _h _h_err =>
      intro h
      have h_step := stepFrame_find?_mono st n o h
      rw [_h] at h_step
      simpa [frameStepParser, driverPhaseParser] using h_step
  case case4 st st' _h _h_err ih =>
      intro h
      have h_step := stepFrame_find?_mono st n o h
      rw [_h] at h_step
      simp only [frameStepParser] at h_step
      exact ih h_step

/-- Configuration preservation across a whole pure phase. -/
theorem runPureSteps_db_config (st : IncludeDriverState) :
    (driverPhaseParser (runPureSteps st)).db.config = st.parser.db.config := by
  fun_induction runPureSteps st
  case case1 st st' _h =>
      have h_step := stepFrame_db_config st
      rw [_h] at h_step
      simpa [frameStepParser, driverPhaseParser] using h_step
  case case2 st sf incf d st' _h =>
      have h_step := stepFrame_db_config st
      rw [_h] at h_step
      simpa [frameStepParser, driverPhaseParser] using h_step
  case case3 st st' _h _h_err =>
      have h_step := stepFrame_db_config st
      rw [_h] at h_step
      simpa [frameStepParser, driverPhaseParser] using h_step
  case case4 st st' _h _h_err ih =>
      have h_step := stepFrame_db_config st
      rw [_h] at h_step
      simp only [frameStepParser] at h_step
      rw [ih, h_step]

/-- The invariant package carried to a phase result: live results (`.done`,
`.push`) are invariant-bearing; an error stop carries nothing. -/
def DriverPhaseInv : DriverPhase → Prop
  | .done st => DriverInv st.parser
  | .stopped _ => True
  | .push _ _ _ st => DriverInv st.parser

/-- A pure phase maintains the invariant package on every live result. -/
theorem runPureSteps_driverPhaseInv (st : IncludeDriverState)
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false) :
    DriverPhaseInv (runPureSteps st) := by
  revert h h_strict h_no_dup
  fun_induction runPureSteps st
  case case1 st st' _h =>
      intro h _h_strict _h_no_dup
      have h_eq := stepFrame_done_inv st st' _h
      subst h_eq
      exact h
  case case2 st sf incf d st' _h =>
      intro h h_strict h_no_dup
      have h_inv' := stepFrame_maintains_driverInv st h h_strict h_no_dup
        (Or.inr ⟨sf, incf, d, st', _h⟩)
      rw [_h] at h_inv'
      simpa [frameStepParser, DriverPhaseInv] using h_inv'
  case case3 st st' _h _h_err =>
      intro _ _ _
      trivial
  case case4 st st' _h _h_err ih =>
      intro h h_strict h_no_dup
      have h_err0' : st'.parser.db.error? = none := by
        have := _h_err
        simp only [Bool.not_eq_true, DB.error, Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none] at this
        exact this
      have h_inv' := stepFrame_maintains_driverInv st h h_strict h_no_dup
        (Or.inl (by rw [_h]; simpa [frameStepParser] using h_err0'))
      rw [_h] at h_inv'
      simp only [frameStepParser] at h_inv'
      have h_cfg := stepFrame_db_config st
      rw [_h] at h_cfg
      simp only [frameStepParser] at h_cfg
      exact ih h_inv' (h_cfg ▸ h_strict) (h_cfg ▸ h_no_dup)

/-- A fresh assertion stored across a whole pure phase was created by a
classified transition at an invariant-bearing state the phase actually
reached. -/
theorem runPureSteps_new_assert_strong_classified (st : IncludeDriverState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false)
    (h_old : st.parser.db.find? n = none)
    (h_new : (driverPhaseParser (runPureSteps st)).db.find? n
      = some (Object.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  revert h h_strict h_no_dup h_old h_new
  fun_induction runPureSteps st
  case case1 st st' _h =>
      intro _hInv _hs _hd h_old h_new
      have h_eq := stepFrame_done_inv st st' _h
      subst h_eq
      simp [driverPhaseParser, h_old] at h_new
  case case2 st sf incf d st' _h =>
      intro h h_strict h_no_dup h_old h_new
      refine stepFrame_new_assert_strong_classified st n f fr lbl
        h.1 h.2.1 h.2.2 h_strict h_no_dup h_old ?_
      rw [_h]
      simpa [frameStepParser, driverPhaseParser] using h_new
  case case3 st st' _h _h_err =>
      intro h h_strict h_no_dup h_old h_new
      refine stepFrame_new_assert_strong_classified st n f fr lbl
        h.1 h.2.1 h.2.2 h_strict h_no_dup h_old ?_
      rw [_h]
      simpa [frameStepParser, driverPhaseParser] using h_new
  case case4 st st' _h _h_err ih =>
      intro h h_strict h_no_dup h_old h_new
      cases h_mid : st'.parser.db.find? n with
      | none =>
          have h_err0' : st'.parser.db.error? = none := by
            have := _h_err
            simp only [Bool.not_eq_true, DB.error, Option.isSome_eq_false_iff,
              Option.isNone_iff_eq_none] at this
            exact this
          have h_inv' := stepFrame_maintains_driverInv st h h_strict h_no_dup
            (Or.inl (by rw [_h]; simpa [frameStepParser] using h_err0'))
          rw [_h] at h_inv'
          simp only [frameStepParser] at h_inv'
          have h_cfg := stepFrame_db_config st
          rw [_h] at h_cfg
          simp only [frameStepParser] at h_cfg
          exact ih h_inv' (h_cfg ▸ h_strict) (h_cfg ▸ h_no_dup) h_mid h_new
      | some o2 =>
          have h_end := runPureSteps_find?_mono st' n o2 h_mid
          rw [h_new] at h_end
          injection h_end with h_o2
          subst h_o2
          refine stepFrame_new_assert_strong_classified st n f fr lbl
            h.1 h.2.1 h.2.2 h_strict h_no_dup h_old ?_
          rw [_h]
          simpa [frameStepParser] using h_mid


/-! ### IO layer: the driver loop's actual results

v4.31 represents `IO` as `EST`: an action is a function from a world token to
an `EST.Out` result, so postconditions are stated directly over the value the
run returned -- no weakest-precondition framework, no model.  The three
`io_*_apply` lemmas expose bind/pure/tryCatch application; everything else is
induction over `runDriverLoop`'s own recursion. -/

/-- `>>=` applied to a world steps through the first action's result. -/
theorem io_bind_apply {α β : Type} (a : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (a >>= f) w = match a w with
      | .ok x w' => f x w'
      | .error e w' => .error e w' := by
  show EST.bind a f w = _
  unfold EST.bind
  cases a w <;> rfl
/-- `tryCatch` applied to a world dispatches on the body's result. -/
theorem io_tryCatch_apply {α : Type} (body : IO α) (handler : IO.Error → IO α) (w : Void IO.RealWorld) :
    (tryCatch body handler) w = match body w with
      | .ok x w' => .ok x w'
      | .error e w' => handler e w' := by
  show EST.tryCatch body handler w = _
  unfold EST.tryCatch
  cases body w <;> rfl
/-- `pure` applied to a world returns immediately. -/
theorem io_pure_apply {α : Type} (x : α) (w : Void IO.RealWorld) :
    (pure x : IO α) w = .ok x w := rfl

/-- Any successful include resolution preserves the parser's database, token
mode, and base offset: resolution only touches include bookkeeping, the stack,
and the child's line numbering. -/
theorem resolvePushWithIO_ok_post (rp : String → IO System.FilePath)
    (rf : String → IO ByteArray)
    (src inc : String) (d : Nat) (st st'' : IncludeDriverState)
    (w w' : Void IO.RealWorld)
    (h : resolvePushWithIO rp rf src inc d st w = .ok (.ok st'') w') :
    st''.parser.db = st.parser.db ∧ st''.parser.tokp = st.parser.tokp
      ∧ st''.base = st.base := by
  unfold resolvePushWithIO at h
  rw [io_tryCatch_apply] at h
  rw [io_bind_apply] at h
  split at h
  · rename_i x w2 heq
    injection h with h1 h2
    subst h2
    subst h1
    split at heq
    · rename_i result w3 heq2
      cases result with
      | error err =>
          change (EST.Out.ok (Except.error err) w3 : EST.Out IO.Error IO.RealWorld (Except IncludeError IncludeDriverState)) = EST.Out.ok (Except.ok st'') w2 at heq
          cases heq
      | ok result =>
          rcases result with ⟨frame, processing, seen⟩
          cases frame <;>
            change (EST.Out.ok _ w3 : EST.Out IO.Error IO.RealWorld (Except IncludeError IncludeDriverState)) = EST.Out.ok (Except.ok st'') w2 at heq
          all_goals
            injection heq with stateEq worldEq
            injection stateEq with stateEq
            subst st''
            exact ⟨rfl, rfl, rfl⟩
    · cases heq
  · rename_i e w2 heq
    change (EST.Out.ok (Except.error _) w2 : EST.Out IO.Error IO.RealWorld (Except IncludeError IncludeDriverState)) = EST.Out.ok (Except.ok st'') w' at h
    cases h

/-- Inversion of one driver-loop layer: a successful run is a phase result
that either finishes immediately or resolves one push and recurses with one
unit less fuel. -/
theorem runDriverLoop_ok_inversion
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w') :
    (runPureSteps st = .done rst ∨ runPureSteps st = .stopped rst)
    ∨ (∃ src inc d st' fuel' st'' w₂,
        fuel = fuel' + 1 ∧
        runPureSteps st = .push src inc d st' ∧
        resolvePushWithIO rp rf src inc d st' w = .ok (.ok st'') w₂ ∧
        runDriverLoop rp rf fuel' st'' w₂ = .ok (.ok rst) w') := by
  unfold runDriverLoop at h_run
  cases h_phase : runPureSteps st with
  | done st2 =>
      simp only [h_phase] at h_run
      rw [io_pure_apply] at h_run
      injection h_run with g1 g2
      injection g1 with g1
      exact Or.inl (Or.inl (by rw [g1]))
  | stopped st2 =>
      simp only [h_phase] at h_run
      rw [io_pure_apply] at h_run
      injection h_run with g1 g2
      injection g1 with g1
      exact Or.inl (Or.inr (by rw [g1]))
  | push src inc d st2 =>
      simp only [h_phase] at h_run
      cases fuel with
      | zero =>
          dsimp only [] at h_run
          rw [io_pure_apply] at h_run
          injection h_run with g1 g2
          exact absurd g1 (by simp)
      | succ fuel' =>
          dsimp only [] at h_run
          rw [io_bind_apply] at h_run
          split at h_run
          · rename_i v w₂ heq
            cases v with
            | error e2 =>
                dsimp only [] at h_run
                rw [io_pure_apply] at h_run
                injection h_run with g1 g2
                exact absurd g1 (by simp)
            | ok st'' =>
                exact Or.inr ⟨src, inc, d, st2, fuel', st'', w₂, rfl,
                  rfl, heq, h_run⟩
          · rename_i e w₂ heq
            exact absurd h_run (by simp)

/-- A `.stopped` phase result carries a parser error -- that is the only way
the loop stops early. -/
theorem runPureSteps_stopped_error (st st' : IncludeDriverState)
    (h : runPureSteps st = .stopped st') :
    st'.parser.db.error = true := by
  fun_induction runPureSteps st
  case case1 st st2 _h => exact absurd h (by simp)
  case case2 st sf incf d st2 _h => exact absurd h (by simp)
  case case3 st st2 _h _h_err =>
      injection h with h
      subst h
      exact _h_err
  case case4 st st2 _h _h_err ih => exact ih h

/-- Registry write-once monotonicity across a whole driver run, for whatever
state the run actually returned. -/
theorem runDriverLoop_find?_mono
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w')
    (n : String) (o : Object) (h : st.parser.db.find? n = some o) :
    rst.parser.db.find? n = some o := by
  induction fuel generalizing st w with
  | zero =>
      rcases runDriverLoop_ok_inversion rp rf 0 st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', fuel', st'', w₂, h_eq, _, _, _⟩
      · have h1 := runPureSteps_find?_mono st n o h
        rw [h_d] at h1
        simpa [driverPhaseParser] using h1
      · have h1 := runPureSteps_find?_mono st n o h
        rw [h_s] at h1
        simpa [driverPhaseParser] using h1
      · exact absurd h_eq (by omega)
  | succ fuel' ih =>
      rcases runDriverLoop_ok_inversion rp rf (fuel' + 1) st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', f2, st'', w₂, h_eq, h_p, h_res, h_rec⟩
      · have h1 := runPureSteps_find?_mono st n o h
        rw [h_d] at h1
        simpa [driverPhaseParser] using h1
      · have h1 := runPureSteps_find?_mono st n o h
        rw [h_s] at h1
        simpa [driverPhaseParser] using h1
      · have h_f2 : f2 = fuel' := by omega
        subst h_f2
        have h1 := runPureSteps_find?_mono st n o h
        rw [h_p] at h1
        simp only [driverPhaseParser] at h1
        obtain ⟨h_db, h_tokp, h_base⟩ :=
          resolvePushWithIO_ok_post rp rf src inc d st' st'' w w₂ h_res
        rw [← h_db] at h1
        exact ih st'' w₂ h_rec h1

/-- Configuration preservation across a whole driver run. -/
theorem runDriverLoop_db_config
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w') :
    rst.parser.db.config = st.parser.db.config := by
  induction fuel generalizing st w with
  | zero =>
      rcases runDriverLoop_ok_inversion rp rf 0 st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', fuel', st'', w₂, h_eq, _, _, _⟩
      · have h1 := runPureSteps_db_config st
        rw [h_d] at h1
        simpa [driverPhaseParser] using h1
      · have h1 := runPureSteps_db_config st
        rw [h_s] at h1
        simpa [driverPhaseParser] using h1
      · exact absurd h_eq (by omega)
  | succ fuel' ih =>
      rcases runDriverLoop_ok_inversion rp rf (fuel' + 1) st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', f2, st'', w₂, h_eq, h_p, h_res, h_rec⟩
      · have h1 := runPureSteps_db_config st
        rw [h_d] at h1
        simpa [driverPhaseParser] using h1
      · have h1 := runPureSteps_db_config st
        rw [h_s] at h1
        simpa [driverPhaseParser] using h1
      · have h_f2 : f2 = fuel' := by omega
        subst h_f2
        have h1 := runPureSteps_db_config st
        rw [h_p] at h1
        simp only [driverPhaseParser] at h1
        obtain ⟨h_db, h_tokp, h_base⟩ :=
          resolvePushWithIO_ok_post rp rf src inc d st' st'' w w₂ h_res
        have h2 := ih st'' w₂ h_rec
        rw [h2, h_db, h1]

/-- A successful, error-free driver run maintains the invariant package. -/
theorem runDriverLoop_ok_driverInv
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w')
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false)
    (h_err : rst.parser.db.error? = none) :
    DriverInv rst.parser := by
  induction fuel generalizing st w with
  | zero =>
      rcases runDriverLoop_ok_inversion rp rf 0 st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', fuel', st'', w₂, h_eq, _, _, _⟩
      · have h1 := runPureSteps_driverPhaseInv st h h_strict h_no_dup
        rw [h_d] at h1
        simpa [DriverPhaseInv] using h1
      · have h1 := runPureSteps_stopped_error st rst h_s
        rw [DB.error, h_err] at h1
        simp at h1
      · exact absurd h_eq (by omega)
  | succ fuel' ih =>
      rcases runDriverLoop_ok_inversion rp rf (fuel' + 1) st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', f2, st'', w₂, h_eq, h_p, h_res, h_rec⟩
      · have h1 := runPureSteps_driverPhaseInv st h h_strict h_no_dup
        rw [h_d] at h1
        simpa [DriverPhaseInv] using h1
      · have h1 := runPureSteps_stopped_error st rst h_s
        rw [DB.error, h_err] at h1
        simp at h1
      · have h_f2 : f2 = fuel' := by omega
        subst h_f2
        have h1 := runPureSteps_driverPhaseInv st h h_strict h_no_dup
        rw [h_p] at h1
        simp only [DriverPhaseInv] at h1
        obtain ⟨h_db, h_tokp, h_base⟩ :=
          resolvePushWithIO_ok_post rp rf src inc d st' st'' w w₂ h_res
        have h_inv'' := driverInv_of_db_tokp_eq st''.parser st'.parser h_db h_tokp h1
        have h_cfg := runPureSteps_db_config st
        rw [h_p] at h_cfg
        simp only [driverPhaseParser] at h_cfg
        have h_cfg'' : st''.parser.db.config = st.parser.db.config := by
          rw [h_db, h_cfg]
        exact ih st'' w₂ h_rec h_inv'' (h_cfg'' ▸ h_strict) (h_cfg'' ▸ h_no_dup)

/-- **Driver-loop origin theorem.**  A fresh assertion stored by the stated
`runDriverLoop` result has an invariant-bearing classified local transition
witness.  The returned `StrongNewAssertCertificate` does not retain the path
showing that local state is a member of this particular IO execution. -/
theorem runDriverLoop_new_assert_strong_classified
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w')
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false)
    (h_old : st.parser.db.find? n = none)
    (h_new : rst.parser.db.find? n = some (Object.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  induction fuel generalizing st w with
  | zero =>
      rcases runDriverLoop_ok_inversion rp rf 0 st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', fuel', st'', w₂, h_eq, _, _, _⟩
      · refine runPureSteps_new_assert_strong_classified st n f fr lbl
          h h_strict h_no_dup h_old ?_
        rw [h_d]
        simpa [driverPhaseParser] using h_new
      · refine runPureSteps_new_assert_strong_classified st n f fr lbl
          h h_strict h_no_dup h_old ?_
        rw [h_s]
        simpa [driverPhaseParser] using h_new
      · exact absurd h_eq (by omega)
  | succ fuel' ih =>
      rcases runDriverLoop_ok_inversion rp rf (fuel' + 1) st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', f2, st'', w₂, h_eq, h_p, h_res, h_rec⟩
      · refine runPureSteps_new_assert_strong_classified st n f fr lbl
          h h_strict h_no_dup h_old ?_
        rw [h_d]
        simpa [driverPhaseParser] using h_new
      · refine runPureSteps_new_assert_strong_classified st n f fr lbl
          h h_strict h_no_dup h_old ?_
        rw [h_s]
        simpa [driverPhaseParser] using h_new
      · have h_f2 : f2 = fuel' := by omega
        rw [h_f2] at h_rec
        obtain ⟨h_db, h_tokp, h_base⟩ :=
          resolvePushWithIO_ok_post rp rf src inc d st' st'' w w₂ h_res
        cases h_mid : st'.parser.db.find? n with
        | none =>
            have h1 := runPureSteps_driverPhaseInv st h h_strict h_no_dup
            rw [h_p] at h1
            simp only [DriverPhaseInv] at h1
            have h_inv'' := driverInv_of_db_tokp_eq st''.parser st'.parser h_db h_tokp h1
            have h_cfg := runPureSteps_db_config st
            rw [h_p] at h_cfg
            simp only [driverPhaseParser] at h_cfg
            have h_cfg'' : st''.parser.db.config = st.parser.db.config := by
              rw [h_db, h_cfg]
            have h_mid'' : st''.parser.db.find? n = none := by
              rw [show st''.parser.db = st'.parser.db from h_db]
              exact h_mid
            exact ih st'' w₂ h_rec h_inv'' (h_cfg'' ▸ h_strict)
              (h_cfg'' ▸ h_no_dup) h_mid''
        | some o2 =>
            have h_mid'' : st''.parser.db.find? n = some o2 := by
              rw [show st''.parser.db = st'.parser.db from h_db]
              exact h_mid
            have h_end := runDriverLoop_find?_mono rp rf fuel' st'' w₂ w' rst
              h_rec n o2 h_mid''
            rw [h_new] at h_end
            injection h_end with h_o2
            subst h_o2
            refine runPureSteps_new_assert_strong_classified st n f fr lbl
              h h_strict h_no_dup h_old ?_
            rw [h_p]
            simpa [driverPhaseParser] using h_mid


/-- **Single-pass certificate theorem.**  For the stated `checkSinglePass`
result, every assertion carries an invariant-bearing classified local
`feedToken` witness.  The proof analyzes the include-skip path, driver loop,
and EOF flush, but the certificate proposition does not retain membership of
the witness state in that concrete IO run. -/
theorem checkSinglePass_ok_new_assert_strong_classified
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none)
    (h_new : db.find? n = some (.assert f fr lbl)) :
    StrongNewAssertCertificate n f fr lbl := by
  unfold checkSinglePass at h_run
  rw [io_bind_apply] at h_run
  split at h_run
  case h_2 e w₂ heq => exact absurd h_run (by simp)
  case h_1 result w₂ heq =>
  rw [io_pure_apply] at h_run
  injection h_run with g1 g2
  cases result with
  | error err =>
      rw [← g1] at h_success
      exact absurd h_success (by
        simp [finalizeSinglePassResult, includePreprocessErrorDB])
  | ok triple =>
  obtain ⟨s, base, seenSet⟩ := triple
  rw [← g1] at h_success h_new
  unfold finalizeSinglePassResult at h_success h_new
  dsimp only [] at h_success h_new
  by_cases h_de : (s.done base).error? = none
  · rw [if_pos h_de] at h_success h_new
    by_cases h_g : (((s.done base).config.allowDuplicateFloat
        || (s.done base).wellFormed?) && (s.done base).assertDvVarsInFrame?) = true
    · rw [if_pos h_g] at h_success h_new
      -- Now walk `heq` down to the driver loop.
      unfold singlePassInitialResult processFileSinglePass at heq
      rw [io_bind_apply] at heq
      split at heq
      case h_2 e w₃ heq2 => exact absurd heq (by simp)
      case h_1 r2 w₃ heq2 =>
      cases r2 with
      | error err =>
          dsimp only [] at heq
          rw [io_pure_apply] at heq
          injection heq with g3 g4
          exact absurd g3 (by simp)
      | ok st =>
      dsimp only [] at heq
      rw [io_pure_apply] at heq
      injection heq with g3 g4
      injection g3 with g3
      injection g3 with g5 g6
      injection g6 with g6 g7
      -- g5 : st.parser = s? direction check below; g6 : st.base = base
      unfold processFileSinglePassWithIO at heq2
      rw [io_bind_apply] at heq2
      split at heq2
      case h_2 e w₄ heq3 => exact absurd heq2 (by simp)
      case h_1 pr w₄ heq3 =>
      cases pr with
      | error err =>
          dsimp only [] at heq2
          rw [io_pure_apply] at heq2
          injection heq2 with g8 g9
          exact absurd g8 (by simp)
      | ok body =>
      obtain ⟨opt, p2, s2⟩ := body
      cases opt with
      | none =>
          -- duplicate-skip of the root: the parser is the untouched initial state
          dsimp only [] at heq2
          rw [io_pure_apply] at heq2
          injection heq2 with g8 g9
          injection g8 with g8
          -- g8 : {st0 with seen := s2} = st
          have h_sp : s = ({ (default : ParserState) with
              db := { (default : DB) with config := config } } : ParserState) := by
            rw [← g5, ← g8]
            rfl
          subst h_sp
          refine done_new_assert_strong_classified _ base n f fr lbl
            (ParserOps.initState_inv config) trivial ?_ h_de h_new
          exact default_db_find?_none n
      | some rootFrame =>
          dsimp only [] at heq2
          -- heq2 : runDriverLoop ... = .ok (.ok st) w₃
          have h_sp : s = st.parser := g5.symm
          subst h_sp
          have h_db_err : st.parser.db.error? = none :=
            ParserOps.done_no_error_implies_db_no_error st.parser base h_de
          have h_inv0 : DriverInv ({ (default : ParserState) with
              db := { (default : DB) with config := config } } : ParserState) :=
            ⟨ParserOps.initState_inv config, trivial, rfl⟩
          have h_inv_end := runDriverLoop_ok_driverInv _ _ _ _ _ _ _ heq2
            h_inv0 h_cfg.1 h_cfg.2 h_db_err
          by_cases h_mid : st.parser.db.find? n = none
          · exact done_new_assert_strong_classified st.parser base n f fr lbl
              h_inv_end.1 h_inv_end.2.1 h_mid h_de h_new
          · cases h_val : st.parser.db.find? n with
            | none => exact absurd h_val h_mid
            | some o =>
                have h_pin := done_find?_mono st.parser base n o h_val
                rw [h_new] at h_pin
                injection h_pin with h_o
                subst h_o
                exact runDriverLoop_new_assert_strong_classified _ _ _ _ _ _ _
                  n f fr lbl heq2 h_inv0 h_cfg.1 h_cfg.2
                  (default_db_find?_none n) h_val
    · rw [if_neg h_g] at h_success
      exact absurd h_success (by simp)
  · rw [if_neg h_de] at h_success
    exact absurd h_success h_de

/-- **Single-pass assertion-origin theorem.**  Every assertion in a successful
`checkSinglePass` result has a local `$a`- or `$p`-closing transition witness.
On the `$p` side, the formula was `Spec.Provable` in the witness database before
the insertion, so that witness cannot justify itself by self-citation.

The conclusion deliberately does not claim that the witness state is exposed
as a member of the particular IO execution.  The registry chronology below
retains enough information for creation order and uniqueness, but not full
parser-state execution membership. -/
theorem checkSinglePass_assert_origin_provable
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none)
    (h_new : db.find? n = some (.assert f fr lbl)) :
    (∃ (s' : ParserState) (j : Nat) (tk : ByteSlice)
        (arr' : Array Verify.Sym) (p : TokensParser),
        AxiomFinishEvent s' j tk arr' p ∧
        p.label = n ∧ f = arr' ∧ lbl = n ∧
        Formula.hasConstHead arr' = true ∧
        s'.db.find? n = none ∧
        (s'.feedToken j tk).db = s'.db.insertAxiom p.pos p.label arr' ∧
        s'.db.trimFrame' arr' = .ok fr)
      ∨ (∃ (s' : ParserState) (j : Nat) (tk : ByteSlice) (pr : ProofState)
          (Γ : Spec.Database) (specFr : Spec.Frame),
          FinishProofEvent s' j tk pr ∧
          pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
          s'.db.find? n = none ∧
          (s'.feedToken j tk).db
            = (s'.db.insert pr.pos pr.label
                (.assert pr.fmla pr.frame)).recordIncomplete
                  pr.incomplete pr.label ∧
          toDatabase s'.db = some Γ ∧
          toFrame s'.db s'.db.frame = some specFr ∧
          Spec.Provable Γ specFr (toExpr f)) :=
  strongNewAssertCertificate_origin_provable n f fr lbl
    (checkSinglePass_ok_new_assert_strong_classified fname config h_cfg
      n f fr lbl w w' db h_run h_success h_new)


/-! ### Registry chronology and exactly-one creation

`RunTrace` records `feedToken` transitions in list order and connects their
registries across driver bookkeeping.  Its seams are `db.objects` equalities,
not full parser-state reachability.  It therefore supports registry
monotonicity and unique creation by list position, but it is not an execution
log and must not be used as proof that each local state belongs to one
particular IO run. -/

/-- One recorded transition of a driver run: a `feedToken` application. -/
structure RunStep where
  state : ParserState
  pos : Nat
  tk : ByteSlice
  deriving Inhabited

/-- The state after a recorded step. -/
def RunStep.next (r : RunStep) : ParserState := r.state.feedToken r.pos r.tk

/-- Registry chronology between two anchors: recorded `feedToken` transitions
in order, with object-registry continuity at every seam.  Other parser fields
are intentionally not related by this proposition. -/
inductive RunTrace : ParserState → List RunStep → ParserState → Prop
  | nil (p q : ParserState) (h : p.db.objects = q.db.objects) : RunTrace p [] q
  | cons (p : ParserState) (r : RunStep) (rest : List RunStep) (q : ParserState)
      (h_head : p.db.objects = r.state.db.objects)
      (h_rest : RunTrace r.next rest q) : RunTrace p (r :: rest) q

/-- Retarget the left anchor across registry equality. -/
theorem RunTrace.retarget {p p' q : ParserState} {steps : List RunStep}
    (h_obj : p.db.objects = p'.db.objects)
    (h : RunTrace p' steps q) : RunTrace p steps q := by
  cases h with
  | nil _ _ h2 => exact .nil _ _ (h_obj.trans h2)
  | cons _ r rest _ h_head h_rest => exact .cons _ r rest _ (h_obj.trans h_head) h_rest

/-- Retarget the right anchor across registry equality. -/
theorem RunTrace.retargetEnd {p q q' : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q)
    (h_obj : q.db.objects = q'.db.objects) : RunTrace p steps q' := by
  induction h with
  | nil _ _ h2 => exact .nil _ _ (h2.trans h_obj)
  | cons _ r rest _ h_head _ ih => exact .cons _ r rest _ h_head (ih h_obj)

/-- Traces compose. -/
theorem RunTrace.append {p q r : ParserState} {a b : List RunStep}
    (h1 : RunTrace p a q) (h2 : RunTrace q b r) : RunTrace p (a ++ b) r := by
  induction h1 with
  | nil _ _ h => exact h2.retarget h
  | cons _ s rest _ h_head _ ih => exact .cons _ s (rest ++ b) _ h_head (ih h2)

/-- Registry facts propagate forward along a trace. -/
theorem RunTrace.find?_mono {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (n : String) (o : Object)
    (h_find : p.db.find? n = some o) : q.db.find? n = some o := by
  induction h with
  | nil p q h2 =>
      show q.db.objects[n]? = some o
      rw [← h2]
      exact h_find
  | cons p r rest q h_head _ ih =>
      refine ih (feedToken_find?_mono r.state r.pos r.tk n o ?_)
      show r.state.db.objects[n]? = some o
      rw [← h_head]
      exact h_find

/-- Registry facts propagate forward to any member's entry state. -/
theorem RunTrace.find?_mono_to_member {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (i : Nat) (h_i : i < steps.length)
    (n : String) (o : Object) (h_find : p.db.find? n = some o) :
    (steps[i]!).state.db.find? n = some o := by
  induction h generalizing i with
  | nil _ _ _ => simp at h_i
  | cons p r rest q h_head h_rest ih =>
      cases i with
      | zero =>
          show r.state.db.objects[n]? = some o
          rw [← h_head]
          exact h_find
      | succ i' =>
          simp only [List.getElem!_cons_succ]
          refine ih i' (by simpa using h_i) ?_
          refine feedToken_find?_mono r.state r.pos r.tk n o ?_
          show r.state.db.objects[n]? = some o
          rw [← h_head]
          exact h_find

/-- A creating step for a registry entry. -/
def CreatesEntry (r : RunStep) (n : String) (o : Object) : Prop :=
  r.state.db.find? n = none ∧ r.next.db.find? n = some o

/-- Existence: an entry absent at the left anchor and present at the right
anchor was created at some recorded step. -/
theorem RunTrace.creating_step_exists {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (n : String) (o : Object)
    (h_old : p.db.find? n = none) (h_new : q.db.find? n = some o) :
    ∃ i, i < steps.length ∧ CreatesEntry (steps[i]!) n o := by
  induction h with
  | nil p q h2 =>
      rw [show q.db.find? n = p.db.find? n from by
        show q.db.objects[n]? = p.db.objects[n]?; rw [h2], h_old] at h_new
      cases h_new
  | cons p r rest q h_head h_rest ih =>
      have h_r_old : r.state.db.find? n = none := by
        show r.state.db.objects[n]? = none
        rw [← h_head]
        exact h_old
      cases h_mid : r.next.db.find? n with
      | none =>
          obtain ⟨i, h_i, h_c⟩ := ih h_mid h_new
          exact ⟨i + 1, by simpa using h_i, by simpa using h_c⟩
      | some o' =>
          have h_o' : o' = o := by
            have h_end := h_rest.find?_mono n o' h_mid
            rw [h_new] at h_end
            injection h_end with h_v
            exact h_v.symm
          subst h_o'
          exact ⟨0, by simp, by simpa [CreatesEntry] using ⟨h_r_old, h_mid⟩⟩

/-- Directional core of uniqueness: no creating step can be followed by a
second creating step for the same label — the first stores it, monotonicity
keeps it stored, freshness at the second fails. -/
theorem RunTrace.no_second_create {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (n : String) (o o' : Object)
    (i j : Nat) (h_j : j < steps.length) (h_lt : i < j)
    (h_ci : CreatesEntry (steps[i]!) n o) (h_cj : CreatesEntry (steps[j]!) n o') :
    False := by
  induction h generalizing i j with
  | nil _ _ _ => exact absurd h_j (by simp)
  | cons p r rest q h_head h_rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd h_lt (by simp)
          | succ j' =>
              have h_r : r.next.db.find? n = some o := by
                simpa using h_ci.2
              have h_at_j := h_rest.find?_mono_to_member j' (by simpa using h_j)
                n o h_r
              have h_fresh : (rest[j']!).state.db.find? n = none := by
                simpa using h_cj.1
              rw [h_fresh] at h_at_j
              cases h_at_j
      | succ i' =>
          cases j with
          | zero => exact absurd h_lt (by omega)
          | succ j' =>
              exact ih i' j' (by simpa using h_j) (by omega)
                (by simpa using h_ci) (by simpa using h_cj)

/-- At most one creating step per label, as index equality. -/
theorem RunTrace.creating_step_unique {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (n : String) (o o' : Object)
    (i j : Nat) (h_i : i < steps.length) (h_j : j < steps.length)
    (h_ci : CreatesEntry (steps[i]!) n o) (h_cj : CreatesEntry (steps[j]!) n o') :
    i = j := by
  rcases Nat.lt_trichotomy i j with h_lt | h_eq | h_gt
  · exact absurd (h.no_second_create n o o' i j h_j h_lt h_ci h_cj) not_false
  · exact h_eq
  · exact absurd (h.no_second_create n o' o j i h_i h_gt h_cj h_ci) not_false

/-- Per-step invariant package carried by an emitted trace. -/
def StepsInv (steps : List RunStep) : Prop :=
  ∀ r ∈ steps, ParserOps.ParserStateInv r.state ∧
    ProofGhost r.state.db r.state.tokp ∧ r.state.db.error? = none

theorem stepsInv_nil : StepsInv [] := by intro r h; cases h

theorem stepsInv_cons {r : RunStep} {rest : List RunStep}
    (h_r : ParserOps.ParserStateInv r.state ∧
      ProofGhost r.state.db r.state.tokp ∧ r.state.db.error? = none)
    (h_rest : StepsInv rest) : StepsInv (r :: rest) := by
  intro x hx
  cases hx with
  | head => exact h_r
  | tail _ h => exact h_rest x h


theorem updateLine_db_objects (s : ParserState) (i : Nat) (c : UInt8) :
    (s.updateLine i c).db.objects = s.db.objects := by
  unfold ParserState.updateLine
  split <;> rfl

/-- The byte loop emits its flush transitions as an invariant-bearing trace. -/
theorem feed_emits_trace (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      RunTrace s steps (ParserState.feed base arr i rs s) ∧ StepsInv steps := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState),
      ParserOps.ParserStateInv s →
      ProofGhost s.db s.tokp →
      s.db.error? = none →
      s.db.config.rejectUnknownSteps = true →
      s.db.config.allowDuplicateFloat = false →
      arr.size - i = m →
      ∃ steps : List RunStep,
        RunTrace s steps (ParserState.feed base arr i rs s) ∧ StepsInv steps)
    ?base ?step (arr.size - i) i rs s h_inv h_ghost h_err0 h_strict h_no_dup rfl
  · intro i rs s _ _ _ _ _ hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    refine ⟨[], ?_, stepsInv_nil⟩
    unfold ParserState.feed
    simp only [hi, ↓reduceDIte]
    exact .nil _ _ rfl
  · intro m ih i rs s h_inv h_ghost h_err0 h_strict h_no_dup hs
    by_cases hi : i < arr.size
    · have hs' : arr.size - (i + 1) = m := by
        simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
      by_cases h_ws : isWhitespace arr[i] = true
      · cases rs with
        | ws =>
            obtain ⟨steps, h_tr, h_si⟩ := ih (i + 1) .ws
              (s.updateLine (base + i) arr[i])
              (parserStateInv_updateLine s _ _ h_inv)
              (proofGhost_updateLine s _ _ h_ghost)
              (by simpa using h_err0) (by simpa using h_strict)
              (by simpa using h_no_dup) hs'
            refine ⟨steps, ?_, h_si⟩
            unfold ParserState.feed
            simp only [hi, ↓reduceDIte, h_ws, if_true]
            exact h_tr.retarget (updateLine_db_objects s _ _).symm
        | token ot =>
            cases ot with
            | this off =>
                cases h_g : ((s.feedToken (base + off)
                    (ByteSlice.mk arr off (i - off))).updateLine
                      (base + i) arr[i]).db.error? with
                | some it =>
                    -- error freeze: the flush is the last recorded step
                    refine ⟨[⟨s, base + off, ByteSlice.mk arr off (i - off)⟩],
                      ?_, stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ stepsInv_nil⟩
                    unfold ParserState.feed
                    simp only [hi, ↓reduceDIte, h_ws, if_true, h_g]
                    exact .cons _ _ _ _ rfl
                      (.nil _ _ (by simp [RunStep.next]))
                | none =>
                    have h_flush_ok : (s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).db.error? = none := by
                      simpa using h_g
                    have h_inv1 := ParserOps.feedToken_maintains_stateInv s
                      (base + off) (ByteSlice.mk arr off (i - off))
                      h_inv h_err0 h_no_dup h_flush_ok
                    have h_ghost1 := feedToken_maintains_ghost s (base + off)
                      (ByteSlice.mk arr off (i - off))
                      h_ghost h_inv h_err0 h_strict h_flush_ok
                    obtain ⟨steps, h_tr, h_si⟩ := ih (i + 1) .ws
                      ((s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).updateLine
                          (base + i) arr[i])
                      (parserStateInv_updateLine _ _ _ h_inv1)
                      (proofGhost_updateLine _ _ _ h_ghost1)
                      (by simpa using h_flush_ok)
                      (by simpa using h_strict) (by simpa using h_no_dup) hs'
                    refine ⟨⟨s, base + off, ByteSlice.mk arr off (i - off)⟩ :: steps,
                      ?_, stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ h_si⟩
                    unfold ParserState.feed
                    simp only [hi, ↓reduceDIte, h_ws, if_true, h_g]
                    exact .cons _ _ _ _ rfl
                      (h_tr.retarget (by simp [RunStep.next]))
            | old base' off arr' =>
                cases h_g : ((s.feedToken (base' + off)
                    (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                      (arr'.size - off + i))).updateLine
                      (base + i) arr[i]).db.error? with
                | some it =>
                    refine ⟨[⟨s, base' + off,
                      ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i)⟩],
                      ?_, stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ stepsInv_nil⟩
                    unfold ParserState.feed
                    simp only [hi, ↓reduceDIte, h_ws, if_true, h_g]
                    exact .cons _ _ _ _ rfl
                      (.nil _ _ (by simp [RunStep.next]))
                | none =>
                    have h_flush_ok : (s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).db.error? = none := by
                      simpa using h_g
                    have h_inv1 := ParserOps.feedToken_maintains_stateInv s
                      (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))
                      h_inv h_err0 h_no_dup h_flush_ok
                    have h_ghost1 := feedToken_maintains_ghost s (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))
                      h_ghost h_inv h_err0 h_strict h_flush_ok
                    obtain ⟨steps, h_tr, h_si⟩ := ih (i + 1) .ws
                      ((s.feedToken (base' + off)
                        (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                          (arr'.size - off + i))).updateLine
                          (base + i) arr[i])
                      (parserStateInv_updateLine _ _ _ h_inv1)
                      (proofGhost_updateLine _ _ _ h_ghost1)
                      (by simpa using h_flush_ok)
                      (by simpa using h_strict) (by simpa using h_no_dup) hs'
                    refine ⟨⟨s, base' + off,
                      ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i)⟩ :: steps,
                      ?_, stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ h_si⟩
                    unfold ParserState.feed
                    simp only [hi, ↓reduceDIte, h_ws, if_true, h_g]
                    exact .cons _ _ _ _ rfl
                      (h_tr.retarget (by simp [RunStep.next]))
      · obtain ⟨steps, h_tr, h_si⟩ := ih (i + 1)
          (if let .ws := rs then .token (.this i) else rs) s
          h_inv h_ghost h_err0 h_strict h_no_dup hs'
        refine ⟨steps, ?_, h_si⟩
        unfold ParserState.feed
        simp only [hi, ↓reduceDIte, h_ws, if_false, Bool.false_eq_true]
        cases rs with
        | ws => exact h_tr
        | token ot => exact h_tr
    · exact absurd hs (by omega)

theorem feedAll_emits_trace (s : ParserState) (base : Nat) (arr : ByteArray)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      RunTrace s steps (s.feedAll base arr) ∧ StepsInv steps := by
  unfold ParserState.feedAll
  cases h_charp : s.charp with
  | ws =>
      exact feed_emits_trace base arr 0 .ws s h_inv h_ghost h_err0 h_strict
        h_no_dup
  | token base' tk =>
      obtain ⟨steps, h_tr, h_si⟩ := feed_emits_trace base arr 0
        (.token (.old base' tk.start tk.byteArray))
        ({ s with charp := default }) h_inv h_ghost h_err0 h_strict h_no_dup
      refine ⟨steps, ?_, h_si⟩
      dsimp only []
      refine RunTrace.retarget ?_ h_tr
      rfl

theorem flushPendingToken_emits_trace (s : ParserState)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none) :
    ∃ steps : List RunStep,
      RunTrace s steps (flushPendingToken s) ∧ StepsInv steps := by
  unfold flushPendingToken
  cases h_charp : s.charp with
  | ws => exact ⟨[], .nil _ _ rfl, stepsInv_nil⟩
  | token pos tk =>
      refine ⟨[⟨s, pos, tk.toSlice⟩], ?_,
        stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ stepsInv_nil⟩
      exact .cons _ _ _ _ rfl (.nil _ _ rfl)

set_option linter.unusedSimpArgs false in
/- The scoped-off linter misfires here: the flagged rewrites drive the goal's
match reduction. -/
theorem stepFrame_emits_trace (st : IncludeDriverState)
    (h_dinv : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      RunTrace st.parser steps (frameStepParser (stepFrame st)) ∧
        StepsInv steps := by
  obtain ⟨h_pinv, h_ghost, h_err0⟩ := h_dinv
  unfold stepFrame
  cases h_stack : st.stack with
  | nil =>
      refine ⟨[], ?_, stepsInv_nil⟩
      simp only [frameStepParser]
      exact .nil _ _ rfl
  | cons parent tail =>
      by_cases h_sep : parent.needsSep = true
      · obtain ⟨steps, h_tr, h_si⟩ := feedAll_emits_trace st.parser st.base
          (ByteArray.empty.push ' '.toUInt8) h_pinv h_ghost h_err0 h_strict
          h_no_dup
        refine ⟨steps, ?_, h_si⟩
        simp only [if_pos h_sep, frameStepParser, flushChunkToParser,
          ByteArray.isEmpty, ByteArray.size_push]
        exact h_tr
      · simp only [if_neg h_sep]
        by_cases h_exh : parent.offset ≥ parent.contents.size
        · rw [if_pos h_exh]
          cases h_charp : st.parser.charp with
          | ws =>
              refine ⟨[], ?_, stepsInv_nil⟩
              simp only [frameStepParser]
              exact .nil _ _ (popExhaustedFrame_objects _ _ _ _).symm
          | token cpos ctk =>
              obtain ⟨steps, h_tr, h_si⟩ := flushPendingToken_emits_trace
                ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)
                (show ParserOps.ParserStateInv ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) from h_pinv)
                (show ProofGhost _ _ from h_ghost)
                (show _ = _ from h_err0)
              simp only [h_charp]
              cases h_e1 : (flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)).db.error? with
              | some it =>
                  cases it with
                  | mk e idx =>
                      simp only [h_e1]
                      cases h_req : parserIncludeRequestOfError? e with
                      | some req =>
                          cases req with
                          | pushFile sf incf =>
                              refine ⟨steps, ?_, h_si⟩
                              simp only [frameStepParser]
                              refine RunTrace.retargetEnd (RunTrace.retarget ?_ h_tr) ?_ <;> rfl
                      | none =>
                          refine ⟨steps, ?_, h_si⟩
                          simp only [frameStepParser]
                          refine RunTrace.retarget ?_ h_tr
                          rfl
              | none =>
                  refine ⟨steps, ?_, h_si⟩
                  simp only [frameStepParser]
                  refine RunTrace.retargetEnd (RunTrace.retarget ?_ h_tr) ?_
                  · rfl
                  · exact (popExhaustedFrame_objects _ _ _ _).symm
        · rw [if_neg h_exh]
          obtain ⟨steps, h_tr, h_si⟩ := feedAll_emits_trace
            ({ st.parser with sourceFile := parent.fname } : ParserState)
            st.base (parent.contents.extract parent.offset parent.contents.size)
            (show ParserOps.ParserStateInv ({ st.parser with sourceFile := parent.fname } : ParserState) from h_pinv)
            (show ProofGhost _ _ from h_ghost)
            (show _ = _ from h_err0)
            (show _ = _ from h_strict)
            (show _ = _ from h_no_dup)
          cases h_e1 : (({ st.parser with sourceFile := parent.fname } :
              ParserState).feedAll st.base
              (parent.contents.extract parent.offset
                parent.contents.size)).db.error? with
          | some it =>
              cases it with
              | mk e idx =>
                  simp only [h_e1]
                  cases h_req : parserIncludeRequestOfError? e with
                  | some req =>
                      cases req with
                      | pushFile sf incf =>
                          refine ⟨steps, ?_, h_si⟩
                          simp only [frameStepParser]
                          refine RunTrace.retargetEnd (RunTrace.retarget ?_ h_tr) ?_ <;> rfl
                  | none =>
                      refine ⟨steps, ?_, h_si⟩
                      simp only [frameStepParser]
                      refine RunTrace.retarget ?_ h_tr
                      rfl
          | none =>
              refine ⟨steps, ?_, h_si⟩
              simp only [frameStepParser]
              refine RunTrace.retarget ?_ h_tr
              rfl

theorem stepsInv_append {a b : List RunStep} (ha : StepsInv a) (hb : StepsInv b) :
    StepsInv (a ++ b) := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact ha r h
  · exact hb r h

theorem runPureSteps_emits_trace (st : IncludeDriverState)
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      RunTrace st.parser steps (driverPhaseParser (runPureSteps st)) ∧
        StepsInv steps := by
  revert h h_strict h_no_dup
  fun_induction runPureSteps st
  case case1 st st' _h =>
      intro h hs hd
      obtain ⟨steps, tr, si⟩ := stepFrame_emits_trace st h hs hd
      rw [_h] at tr
      exact ⟨steps, by simpa [frameStepParser, driverPhaseParser] using tr, si⟩
  case case2 st sf incf d st' _h =>
      intro h hs hd
      obtain ⟨steps, tr, si⟩ := stepFrame_emits_trace st h hs hd
      rw [_h] at tr
      exact ⟨steps, by simpa [frameStepParser, driverPhaseParser] using tr, si⟩
  case case3 st st' _h _h_err =>
      intro h hs hd
      obtain ⟨steps, tr, si⟩ := stepFrame_emits_trace st h hs hd
      rw [_h] at tr
      exact ⟨steps, by simpa [frameStepParser, driverPhaseParser] using tr, si⟩
  case case4 st st' _h _h_err ih =>
      intro h hs hd
      obtain ⟨steps, tr, si⟩ := stepFrame_emits_trace st h hs hd
      rw [_h] at tr
      simp only [frameStepParser] at tr
      have h_err0' : st'.parser.db.error? = none := by
        have := _h_err
        simp only [Bool.not_eq_true, DB.error, Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none] at this
        exact this
      have h_inv' := stepFrame_maintains_driverInv st h hs hd
        (Or.inl (by rw [_h]; simpa [frameStepParser] using h_err0'))
      rw [_h] at h_inv'
      simp only [frameStepParser] at h_inv'
      have h_cfg := stepFrame_db_config st
      rw [_h] at h_cfg
      simp only [frameStepParser] at h_cfg
      obtain ⟨steps', tr', si'⟩ := ih h_inv' (h_cfg ▸ hs) (h_cfg ▸ hd)
      exact ⟨steps ++ steps', tr.append tr', stepsInv_append si si'⟩

theorem runDriverLoop_emits_trace
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w')
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      RunTrace st.parser steps rst.parser ∧ StepsInv steps := by
  induction fuel generalizing st w with
  | zero =>
      rcases runDriverLoop_ok_inversion rp rf 0 st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', fuel', st'', w₂, h_eq, _, _, _⟩
      · obtain ⟨steps, tr, si⟩ := runPureSteps_emits_trace st h h_strict h_no_dup
        rw [h_d] at tr
        exact ⟨steps, by simpa [driverPhaseParser] using tr, si⟩
      · obtain ⟨steps, tr, si⟩ := runPureSteps_emits_trace st h h_strict h_no_dup
        rw [h_s] at tr
        exact ⟨steps, by simpa [driverPhaseParser] using tr, si⟩
      · exact absurd h_eq (by omega)
  | succ fuel' ih =>
      rcases runDriverLoop_ok_inversion rp rf (fuel' + 1) st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', f2, st'', w₂, h_eq, h_p, h_res, h_rec⟩
      · obtain ⟨steps, tr, si⟩ := runPureSteps_emits_trace st h h_strict h_no_dup
        rw [h_d] at tr
        exact ⟨steps, by simpa [driverPhaseParser] using tr, si⟩
      · obtain ⟨steps, tr, si⟩ := runPureSteps_emits_trace st h h_strict h_no_dup
        rw [h_s] at tr
        exact ⟨steps, by simpa [driverPhaseParser] using tr, si⟩
      · have h_f2 : f2 = fuel' := by omega
        rw [h_f2] at h_rec
        obtain ⟨steps, tr, si⟩ := runPureSteps_emits_trace st h h_strict h_no_dup
        rw [h_p] at tr
        simp only [driverPhaseParser] at tr
        obtain ⟨h_db, h_tokp, h_base⟩ :=
          resolvePushWithIO_ok_post rp rf src inc d st' st'' w w₂ h_res
        have h1 := runPureSteps_driverPhaseInv st h h_strict h_no_dup
        rw [h_p] at h1
        simp only [DriverPhaseInv] at h1
        have h_inv'' := driverInv_of_db_tokp_eq st''.parser st'.parser h_db h_tokp h1
        have h_cfg := runPureSteps_db_config st
        rw [h_p] at h_cfg
        simp only [driverPhaseParser] at h_cfg
        have h_cfg'' : st''.parser.db.config = st.parser.db.config := by
          rw [h_db, h_cfg]
        obtain ⟨steps', tr', si'⟩ := ih st'' w₂ h_rec h_inv''
          (h_cfg'' ▸ h_strict) (h_cfg'' ▸ h_no_dup)
        refine ⟨steps ++ steps', tr.append (tr'.retarget ?_), stepsInv_append si si'⟩
        rw [h_db]

/-- Registry facts propagate from a member's entry state to the right anchor. -/
theorem RunTrace.find?_mono_from_member {p q : ParserState} {steps : List RunStep}
    (h : RunTrace p steps q) (i : Nat) (h_i : i < steps.length)
    (n : String) (o : Object)
    (h_find : (steps[i]!).state.db.find? n = some o) :
    q.db.find? n = some o := by
  induction h generalizing i with
  | nil _ _ _ => simp at h_i
  | cons p r rest q h_head h_rest ih =>
      cases i with
      | zero =>
          refine h_rest.find?_mono n o ?_
          refine feedToken_find?_mono r.state r.pos r.tk n o ?_
          simpa using h_find
      | succ i' =>
          refine ih i' (by simpa using h_i) ?_
          simpa using h_find

/-- `done` extends a run chronology by at most the EOF flush; the final
database's registry is pointwise that of the extended chronology's end. -/
theorem done_emits_seam (s : ParserState) (base : Nat)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_success : (ParserState.done s base).error? = none) :
    ∃ (steps : List RunStep) (q : ParserState),
      RunTrace s steps q ∧ StepsInv steps ∧
      ∀ n, q.db.find? n = (ParserState.done s base).find? n := by
  cases h_charp : s.charp with
  | ws =>
      exact ⟨[], s, .nil _ _ rfl, stepsInv_nil,
        fun n => (done_find?_eq_self s base n h_err0 h_charp).symm⟩
  | token pos tk =>
      have h_e1 : (s.feedToken pos tk.toSlice).db.error? = none := by
        cases h_e : (s.feedToken pos tk.toSlice).db.error? with
        | none => rfl
        | some it =>
            exfalso
            have h_stuck : (ParserState.done s base).error? ≠ none := by
              simp only [ParserState.done, Id.run, DB.error, Option.isSome_some,
                Option.isSome_none, Bool.false_eq_true, reduceIte,
                h_err0, h_charp, h_e]
              simp [h_e]
            exact h_stuck h_success
      refine ⟨[⟨s, pos, tk.toSlice⟩], s.feedToken pos tk.toSlice,
        .cons _ _ _ _ rfl (.nil _ _ rfl),
        stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ stepsInv_nil,
        fun n => (done_find?_eq_flush s base pos tk n h_err0 h_charp h_e1).symm⟩

/-- A creating run step yields its payload-carrying origin, bound to that
step's own state, position, and token. -/
theorem runStep_creates_origin_provable (r : RunStep)
    (n : String) (f : Verify.Formula) (fr : Verify.Frame) (lbl : String)
    (h_inv : ParserOps.ParserStateInv r.state)
    (h_ghost : ProofGhost r.state.db r.state.tokp)
    (h_err0 : r.state.db.error? = none)
    (h_c : CreatesEntry r n (.assert f fr lbl)) :
    (∃ (arr' : Array Verify.Sym) (p : TokensParser),
        AxiomFinishEvent r.state r.pos r.tk arr' p ∧
        p.label = n ∧ f = arr' ∧ lbl = n ∧
        Formula.hasConstHead arr' = true ∧
        r.state.db.find? n = none ∧
        (r.state.feedToken r.pos r.tk).db
          = r.state.db.insertAxiom p.pos p.label arr' ∧
        r.state.db.trimFrame' arr' = .ok fr)
      ∨ (∃ (pr : ProofState) (Γ : Spec.Database)
          (specFr : Spec.Frame),
          FinishProofEvent r.state r.pos r.tk pr ∧
          pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
          r.state.db.find? n = none ∧
          (r.state.feedToken r.pos r.tk).db
            = (r.state.db.insert pr.pos pr.label
                (.assert pr.fmla pr.frame)).recordIncomplete
                  pr.incomplete pr.label ∧
          Kernel.toDatabase r.state.db = some Γ ∧
          Kernel.toFrame r.state.db r.state.db.frame = some specFr ∧
          Spec.Provable Γ specFr (Kernel.toExpr f)) := by
  obtain ⟨h_old, h_new⟩ := h_c
  have h_succ := feedToken_new_assert_success r.state r.pos r.tk n f fr lbl
    h_err0 h_old h_new
  have h_class := feedToken_new_assert_classified r.state r.pos r.tk n f fr lbl
    h_old h_succ h_new
  cases h_class with
  | inl h_ax =>
      obtain ⟨arr', p, h⟩ := h_ax
      obtain ⟨h_ins, h_n, h_f, h_lbl, h_hd, h_tf⟩ :=
        axiomFinishEvent_created r.state r.pos r.tk arr' p n f fr lbl h h_err0
          h_old h_new
      exact Or.inl ⟨arr', p, h, h_n.symm, h_f, h_lbl, h_hd, h_old, h_ins, h_tf⟩
  | inr h_th =>
      obtain ⟨pr, h_evt⟩ := h_th
      obtain ⟨h_ins0, Γ, specFr, h_toDb, h_toFr, h_prov⟩ :=
        finishProofEvent_stores_provable_entry r.state r.pos r.tk pr h_inv
          h_ghost h_err0 h_evt
      have h_ins : (r.state.feedToken r.pos r.tk).db
          = (r.state.db.insert pr.pos pr.label
              (.assert pr.fmla pr.frame)).recordIncomplete pr.incomplete
                pr.label := h_ins0
      have h_after' : (r.state.db.insert pr.pos pr.label
          (.assert pr.fmla pr.frame)).find? n = some (.assert f fr lbl) := by
        have h_a : ((r.state.feedToken r.pos r.tk).db).find? n
            = some (.assert f fr lbl) := h_new
        rw [h_ins, DB.recordIncomplete_find?] at h_a
        exact h_a
      obtain ⟨h_n_eq, h_obj⟩ :=
        ParserOps.insert_new_assert_origin r.state.db pr.pos pr.label
          (.assert pr.fmla pr.frame) n f fr lbl h_old h_after'
      have h_fm : pr.fmla = f := by injection h_obj with h1 h2 h3
      have h_fr : pr.frame = fr := by injection h_obj with h1 h2 h3
      have h_lbl : pr.label = lbl := by injection h_obj with h1 h2 h3
      refine Or.inr ⟨pr, Γ, specFr, h_evt, h_n_eq.symm, h_fm, h_fr, ?_,
        h_old, h_ins, h_toDb, h_toFr, h_fm ▸ h_prov⟩
      rw [← h_lbl, h_n_eq]

/-- Every successful `checkSinglePass` result has an invariant-bearing
registry chronology from the canonical initial registry to the returned
registry.  Because `RunTrace` relates seams only through `db.objects`, this is
not full parser-state execution membership. -/
theorem checkSinglePass_run_chronology
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none) :
    ∃ (steps : List RunStep) (q : ParserState),
      RunTrace (singlePassInitialState config) steps q ∧
      StepsInv steps ∧
      ∀ n, q.db.find? n = db.find? n := by
  unfold checkSinglePass at h_run
  rw [io_bind_apply] at h_run
  split at h_run
  case h_2 e w₂ heq => exact absurd h_run (by simp)
  case h_1 result w₂ heq =>
  rw [io_pure_apply] at h_run
  injection h_run with g1 g2
  cases result with
  | error err =>
      rw [← g1] at h_success
      exact absurd h_success (by
        simp [finalizeSinglePassResult, includePreprocessErrorDB])
  | ok triple =>
  obtain ⟨s, base, seenSet⟩ := triple
  rw [← g1] at h_success
  have h_db_eq : db = finalizeSinglePassResult config
      (.ok (s, base, seenSet)) := g1.symm
  unfold finalizeSinglePassResult at h_success h_db_eq
  dsimp only [] at h_success h_db_eq
  by_cases h_de : (s.done base).error? = none
  · rw [if_pos h_de] at h_success h_db_eq
    by_cases h_g : (((s.done base).config.allowDuplicateFloat
        || (s.done base).wellFormed?) && (s.done base).assertDvVarsInFrame?)
        = true
    · rw [if_pos h_g] at h_success h_db_eq
      subst h_db_eq
      -- walk `heq` down to the driver loop
      unfold singlePassInitialResult processFileSinglePass at heq
      rw [io_bind_apply] at heq
      split at heq
      case h_2 e w₃ heq2 => exact absurd heq (by simp)
      case h_1 r2 w₃ heq2 =>
      cases r2 with
      | error err =>
          dsimp only [] at heq
          rw [io_pure_apply] at heq
          injection heq with g3 g4
          exact absurd g3 (by simp)
      | ok st =>
      dsimp only [] at heq
      rw [io_pure_apply] at heq
      injection heq with g3 g4
      injection g3 with g3
      injection g3 with g5 g6
      injection g6 with g6 g7
      unfold processFileSinglePassWithIO at heq2
      rw [io_bind_apply] at heq2
      split at heq2
      case h_2 e w₄ heq3 => exact absurd heq2 (by simp)
      case h_1 pr w₄ heq3 =>
      cases pr with
      | error err =>
          dsimp only [] at heq2
          rw [io_pure_apply] at heq2
          injection heq2 with g8 g9
          exact absurd g8 (by simp)
      | ok body =>
      obtain ⟨opt, p2, s2⟩ := body
      cases opt with
      | none =>
          dsimp only [] at heq2
          rw [io_pure_apply] at heq2
          injection heq2 with g8 g9
          injection g8 with g8
          have h_sp : s = ({ (default : ParserState) with
              db := { (default : DB) with config := config } } : ParserState) := by
            rw [← g5, ← g8]
            rfl
          subst h_sp
          obtain ⟨steps, q, tr, si, h_pt⟩ := done_emits_seam _ base
            (ParserOps.initState_inv config) trivial rfl h_de
          exact ⟨steps, q, tr, si, h_pt⟩
      | some rootFrame =>
          dsimp only [] at heq2
          have h_sp : s = st.parser := g5.symm
          subst h_sp
          have h_db_err : st.parser.db.error? = none :=
            ParserOps.done_no_error_implies_db_no_error st.parser
              base h_de
          have h_inv0 : DriverInv ({ (default : ParserState) with
              db := { (default : DB) with config := config } } : ParserState) :=
            ⟨ParserOps.initState_inv config, trivial, rfl⟩
          have h_inv_end := runDriverLoop_ok_driverInv _ _ _ _ _ _ _ heq2
            h_inv0 h_cfg.1 h_cfg.2 h_db_err
          obtain ⟨steps1, tr1, si1⟩ := runDriverLoop_emits_trace _ _ _ _ _ _ _
            heq2 h_inv0 h_cfg.1 h_cfg.2
          obtain ⟨steps2, q, tr2, si2, h_pt⟩ := done_emits_seam st.parser base
            h_inv_end.1 h_inv_end.2.1 h_db_err h_de
          exact ⟨steps1 ++ steps2, q, tr1.append tr2,
            stepsInv_append si1 si2, h_pt⟩
    · rw [if_neg h_g] at h_success
      exact absurd h_success (by simp)
  · rw [if_neg h_de] at h_success
    exact absurd h_success h_de

/-- An invariant-bearing registry chronology with subdatabase, exactly-one,
and bound-payload clauses.  It inherits `RunTrace`'s explicit limitation: the
recorded seams preserve `db.objects`, not full parser-state reachability. -/
def CertifiedRegistryChronology (config : ModeConfig) (db : DB) : Prop :=

    ∃ (steps : List RunStep) (q : ParserState),
      RunTrace (singlePassInitialState config) steps q ∧
      StepsInv steps ∧
      (∀ n, q.db.find? n = db.find? n) ∧
      (∀ i, i < steps.length → ∀ m o,
        (steps[i]!).state.db.find? m = some o → db.find? m = some o) ∧
      (∀ n f fr lbl, db.find? n = some (.assert f fr lbl) →
        ∃ idx : Nat, (idx < steps.length ∧
          CreatesEntry (steps[idx]!) n (.assert f fr lbl)) ∧
          ∀ idx' : Nat, idx' < steps.length →
            CreatesEntry (steps[idx']!) n (.assert f fr lbl) → idx' = idx) ∧
      (∀ idx n f fr lbl, idx < steps.length →
        CreatesEntry (steps[idx]!) n (.assert f fr lbl) →
        (∃ (arr' : Array Verify.Sym) (p : TokensParser),
            AxiomFinishEvent (steps[idx]!).state (steps[idx]!).pos
              (steps[idx]!).tk arr' p ∧
            p.label = n ∧ f = arr' ∧ lbl = n ∧
            Formula.hasConstHead arr' = true ∧
            (steps[idx]!).state.db.find? n = none ∧
            ((steps[idx]!).state.feedToken (steps[idx]!).pos
              (steps[idx]!).tk).db
              = (steps[idx]!).state.db.insertAxiom p.pos p.label arr' ∧
            (steps[idx]!).state.db.trimFrame' arr' = .ok fr)
          ∨ (∃ (pr : ProofState) (Γ : Spec.Database)
              (specFr : Spec.Frame),
              FinishProofEvent (steps[idx]!).state (steps[idx]!).pos
                (steps[idx]!).tk pr ∧
              pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
              (steps[idx]!).state.db.find? n = none ∧
              ((steps[idx]!).state.feedToken (steps[idx]!).pos
                (steps[idx]!).tk).db
                = ((steps[idx]!).state.db.insert pr.pos pr.label
                    (.assert pr.fmla pr.frame)).recordIncomplete
                      pr.incomplete pr.label ∧
              Kernel.toDatabase (steps[idx]!).state.db = some Γ ∧
              Kernel.toFrame (steps[idx]!).state.db
                (steps[idx]!).state.db.frame = some specFr ∧
              Spec.Provable Γ specFr
                (Kernel.toExpr f)))

/-- For the stated successful `checkSinglePass` result under a proof-certified
configuration, construct its certified registry chronology: subdatabase and
exactly-one clauses plus local payloads with pre-insertion `Spec.Provable` on
the `$p` side.  This theorem does not strengthen `RunTrace` into full
IO-execution membership. -/
theorem checkSinglePass_registry_chronology_exactly_one
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none) : CertifiedRegistryChronology config db := by
  obtain ⟨steps, q, tr, si, h_pt⟩ :=
    checkSinglePass_run_chronology fname config h_cfg w w' db h_run h_success
  have h_init_none : ∀ n,
      (singlePassInitialState config).db.find? n = none := by
    intro n
    show ({ (default : DB) with config := config } : DB).objects[n]? = none
    exact default_db_find?_none n
  refine ⟨steps, q, tr, si, h_pt, ?_, ?_, ?_⟩
  · intro i h_i m o h_find
    rw [← h_pt m]
    exact tr.find?_mono_from_member i h_i m o h_find
  · intro n f fr lbl h_new
    have h_q : q.db.find? n = some (.assert f fr lbl) := by
      rw [h_pt n]
      exact h_new
    obtain ⟨idx, h_lt, h_c⟩ :=
      tr.creating_step_exists n (.assert f fr lbl) (h_init_none n) h_q
    refine ⟨idx, ⟨h_lt, h_c⟩, ?_⟩
    intro idx' h_lt' h_c'
    exact tr.creating_step_unique n (.assert f fr lbl) (.assert f fr lbl)
      idx' idx h_lt' h_lt h_c' h_c
  · intro idx n f fr lbl h_lt h_c
    have h_mem : (steps[idx]!) ∈ steps := by
      rw [getElem!_pos steps idx h_lt]
      exact List.getElem_mem h_lt
    obtain ⟨h_inv, h_ghost, h_err0⟩ := si _ h_mem
    exact runStep_creates_origin_provable (steps[idx]!) n f fr lbl
      h_inv h_ghost h_err0 h_c


/-- Registry chronology for the actual `--mode=sound` CLI invocation. -/
theorem checkSinglePass_soundDefault_registry_chronology
    (fname : String) (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname ModeConfig.soundDefault w = .ok db w')
    (h_success : db.error? = none) :
    CertifiedRegistryChronology ModeConfig.soundDefault db :=
  checkSinglePass_registry_chronology_exactly_one fname ModeConfig.soundDefault
    ModeConfig.soundDefault_prefixCertified w w' db h_run h_success

/-- Registry chronology for the actual `--mode=knife` CLI invocation. -/
theorem checkSinglePass_knife_registry_chronology
    (fname : String) (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname ModeConfig.knife w = .ok db w')
    (h_success : db.error? = none) :
    CertifiedRegistryChronology ModeConfig.knife db :=
  checkSinglePass_registry_chronology_exactly_one fname ModeConfig.knife
    ModeConfig.knife_prefixCertified w w' db h_run h_success


/-- A successful certified run exposes the structural invariant used by the
operational/declarative equivalence: the returned projected database is
strongly well formed. -/
theorem checkSinglePass_database_wellFormed_strong
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none) :
    ∃ Γ : Spec.Database,
      toDatabase db = some Γ ∧
      Spec.Equivalence.WellFormedDatabaseStrong Γ (Kernel.toConsts db) ∧
      WF.WellFormedDB db ∧ WF.WellScopedDB db := by
  -- Walk the entrypoint to the finalize gates and the pre-`done` state.
  unfold checkSinglePass at h_run
  rw [io_bind_apply] at h_run
  split at h_run
  case h_2 e w₂ heq => exact absurd h_run (by simp)
  case h_1 result w₂ heq =>
  rw [io_pure_apply] at h_run
  injection h_run with g1 g2
  cases result with
  | error err =>
      rw [← g1] at h_success
      exact absurd h_success (by
        simp [finalizeSinglePassResult, includePreprocessErrorDB])
  | ok triple =>
  obtain ⟨s, base, seenSet⟩ := triple
  rw [← g1] at h_success
  have h_db_eq : db = finalizeSinglePassResult config (.ok (s, base, seenSet)) :=
    g1.symm
  unfold finalizeSinglePassResult at h_success h_db_eq
  dsimp only [] at h_success h_db_eq
  by_cases h_de : (s.done base).error? = none
  · rw [if_pos h_de] at h_success h_db_eq
    by_cases h_g : (((s.done base).config.allowDuplicateFloat
        || (s.done base).wellFormed?) && (s.done base).assertDvVarsInFrame?)
        = true
    · rw [if_pos h_g] at h_success h_db_eq
      subst h_db_eq
      -- Walk `heq` to the driver to learn the pre-`done` state's provenance.
      unfold singlePassInitialResult processFileSinglePass at heq
      rw [io_bind_apply] at heq
      split at heq
      case h_2 e w₃ heq2 => exact absurd heq (by simp)
      case h_1 r2 w₃ heq2 =>
      cases r2 with
      | error err =>
          dsimp only [] at heq
          rw [io_pure_apply] at heq
          injection heq with g3 g4
          exact absurd g3 (by simp)
      | ok st =>
      dsimp only [] at heq
      rw [io_pure_apply] at heq
      injection heq with g3 g4
      injection g3 with g3
      injection g3 with g5 g6
      injection g6 with g6 g7
      unfold processFileSinglePassWithIO at heq2
      rw [io_bind_apply] at heq2
      split at heq2
      case h_2 e w₄ heq3 => exact absurd heq2 (by simp)
      case h_1 pr w₄ heq3 =>
      cases pr with
      | error err =>
          dsimp only [] at heq2
          rw [io_pure_apply] at heq2
          injection heq2 with g8 g9
          exact absurd g8 (by simp)
      | ok body =>
      obtain ⟨opt, p2, s2⟩ := body
      have h_prov : ParserOps.ParserStateInv s ∧ s.db.config = config := by
        cases opt with
        | none =>
            dsimp only [] at heq2
            rw [io_pure_apply] at heq2
            injection heq2 with g8 g9
            injection g8 with g8
            have h_sp : s = ({ (default : ParserState) with
                db := { (default : DB) with config := config } } : ParserState) := by
              rw [← g5, ← g8]
              rfl
            subst h_sp
            exact ⟨ParserOps.initState_inv config, rfl⟩
        | some rootFrame =>
            dsimp only [] at heq2
            have h_sp : s = st.parser := g5.symm
            subst h_sp
            have h_db_err : st.parser.db.error? = none :=
              ParserOps.done_no_error_implies_db_no_error st.parser
                base h_de
            have h_inv0 : DriverInv ({ (default : ParserState) with
                db := { (default : DB) with config := config } } : ParserState) :=
              ⟨ParserOps.initState_inv config, trivial, rfl⟩
            have h_inv_end := runDriverLoop_ok_driverInv _ _ _ _ _ _ _ heq2
              h_inv0 h_cfg.1 h_cfg.2 h_db_err
            have h_cfg_end := runDriverLoop_db_config _ _ _ _ _ _ _ heq2
            exact ⟨h_inv_end.1, h_cfg_end⟩
      -- The final configuration is the invocation configuration.
      have h_cfg_final : (s.done base).config = config := by
        rw [ParserState.done_config]
        exact h_prov.2
      -- Gate booleans under the certified configuration.
      have h_no_dup : (s.done base).config.allowDuplicateFloat = false := by
        rw [h_cfg_final]; exact h_cfg.2
      have h_wfb : (s.done base).wellFormed? = true := by
        rcases Bool.and_eq_true_iff.mp h_g with ⟨h_or, _⟩
        rcases Bool.or_eq_true_iff.mp h_or with h_dup | h_wf
        · rw [h_no_dup] at h_dup; cases h_dup
        · exact h_wf
      have h_dvb : (s.done base).assertDvVarsInFrame? = true :=
        (Bool.and_eq_true_iff.mp h_g).2
      -- Structural facts of the returned database.
      have h_wf : WF.WellFormedDB (s.done base) :=
        WF.wellFormedDB_of_wellFormed? h_wfb
      have h_scoped : WF.WellScopedDB (s.done base) :=
        ParserOps.done_no_error_wellScoped_of_stateInv s base h_prov.1
          (by rw [show s.db.config = config from h_prov.2]; exact h_cfg.2) h_de
      have h_dv := WF.assertDvVarsInFrame_of_assertDvVarsInFrame? h_dvb
      have h_db_ex : ∃ Γ, toDatabase (s.done base) = some Γ := by
        unfold toDatabase; exact ⟨_, rfl⟩
      obtain ⟨Γ, h_db⟩ := h_db_ex
      have h_strong := Kernel.toDatabase_wellFormed_strong (s.done base) h_wf h_scoped
        h_dv Γ h_db
      exact ⟨Γ, h_db, h_strong, h_wf, h_scoped⟩
    · rw [if_neg h_g] at h_success
      exact absurd h_success (by simp)
  · rw [if_neg h_de] at h_success
    exact absurd h_success h_de

/-- **Self-citability of the projected database.** An accepted certified run
returns a database whose projected assertions are well formed enough for each
entry to cite itself under identity substitution. This theorem does not inspect
stored `$p` proofs and is not a source-proof soundness result. -/
theorem checkSinglePass_assertions_selfCitable
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none) :
    ∃ Γ : Spec.Database,
      toDatabase db = some Γ ∧
      ∀ l fr e, Γ l = some (fr, e) → Spec.Provable Γ fr e := by
  obtain ⟨Γ, h_db, h_strong, _h_wf, _h_scoped⟩ :=
    checkSinglePass_database_wellFormed_strong fname config h_cfg w w' db
      h_run h_success
  refine ⟨Γ, h_db, ?_⟩
  intro l fr e h_lookup
  have h_wfe := h_strong.2 l fr e h_lookup
  exact Kernel.assertion_self_provable Γ l fr e h_lookup h_wfe.2 h_wfe.1.1

/-- Self-citability for the actual `--mode=sound` invocation. -/
theorem checkSinglePass_soundDefault_assertions_selfCitable
    (fname : String) (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname ModeConfig.soundDefault w = .ok db w')
    (h_success : db.error? = none) :
    ∃ Γ : Spec.Database,
      toDatabase db = some Γ ∧
      ∀ l fr e, Γ l = some (fr, e) → Spec.Provable Γ fr e :=
  checkSinglePass_assertions_selfCitable fname ModeConfig.soundDefault
    ModeConfig.soundDefault_prefixCertified w w' db h_run h_success

/-- Self-citability for the actual `--mode=knife` invocation. -/
theorem checkSinglePass_knife_assertions_selfCitable
    (fname : String) (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname ModeConfig.knife w = .ok db w')
    (h_success : db.error? = none) :
    ∃ Γ : Spec.Database,
      toDatabase db = some Γ ∧
      ∀ l fr e, Γ l = some (fr, e) → Spec.Provable Γ fr e :=
  checkSinglePass_assertions_selfCitable fname ModeConfig.knife
    ModeConfig.knife_prefixCertified w w' db h_run h_success

end Metamath.PrefixWitnessCheckBytes
