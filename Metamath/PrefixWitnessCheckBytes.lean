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

## Frame Gap: RESOLVED

The frame gap has been closed by changing `stepAssert` to use `db.frame`
(the full scope frame) for DV checking instead of `pr.frame` (trimFrame).
This makes the DV check slightly more conservative but eliminates the
`pr.frame = db.frame` requirement throughout the soundness chain.

Key changes:
- `stepAssert` (Verify.lean): DV checking uses `db.frame` not `pr.frame`
- `ProofStateInv` (KernelClean.lean): uses `db.frame` for frame_ok/frame_wf
- `stepNormal_transfer` (PrefixProvenance.lean): no longer needs frame equality
- `NormalProofReachable_step`: no longer needs `h_frame : pr.frame = db.frame`
- `ProofGhost`: no longer requires `pr.frame = db.frame`
-/

import Metamath.ParserEquivalence
import Metamath.VerifyParserStateThms

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
      · have h_pre : s.db.preload pr (toLabel tk).snd = .ok pr' := by
          simpa [h_ptp, h_close, h_lbl_ok] using h_go
        have h_ptp_eq := preload_preserves_ptp s.db pr pr' (toLabel tk).snd h_pre
        rw [h_ptp_eq, h_ptp]; nofun
      · simp [h_ptp, h_close, h_lbl_ok] at h_go
  | normal =>
    simp [h_ptp] at h_go
    have h_ptp_eq := goNormal_ok_preserves_ptp s tk pr pr' h_go
    rw [h_ptp_eq, h_ptp]; nofun
  | compressed chr =>
    simp [h_ptp] at h_go
    cases h_dec : ParserState.decodeCompressed tk chr with
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
      · have h_pre : s.db.preload pr (toLabel tk).snd = .ok pr' := by
          simpa [h_ptp, h_close, h_lbl_ok] using h_go
        have h_ptp_eq := preload_preserves_ptp s.db pr pr' (toLabel tk).snd h_pre
        rw [h_ptp_eq, h_ptp]; nofun
      · simp [h_ptp, h_close, h_lbl_ok] at h_go
  | compressed chr =>
    simp [h_ptp] at h_go
    cases h_dec : ParserState.decodeCompressed tk chr with
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
    (h_scope : ∀ lbl ∈ fr.hyps.toList, lbl ∈ db.frame.hyps.toList) :
    proofGhostCore db (db'.mkProofState pos l fmla fr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
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
  let pr_init : ProofState := ⟨⟨0,0⟩, pr.label, pr.fmla, db.frame, #[], #[], .normal⟩
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
        obtain ⟨h_start_ghost, h_normal_ghost, h_preload_ghost, h_compressed_ghost⟩ := h_ghost
        refine ⟨?start_clause, ?normal_clause, ?preload_clause, ?compressed_clause⟩
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
            cases h_dec : ParserState.decodeCompressed tk chr with
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
              show CompressedFoldGhost s.db {pr with ptp := .compressed 0}
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
        (trimFrame'_hyps_subset s.db arr fr h_trim)

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
            · exact trivial  -- var → .math → True
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
          cases h_norm : ParserState.normalizeIncludePath s.sourceFile rawPath with
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
  obtain ⟨_h_start, h_normal, _h_preload, h_compressed⟩ := h_ghost
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
    | inr h_ptp_comp0 =>
      have h_cghost : CompressedFoldGhost s.db pr := h_compressed ⟨0, h_ptp_comp0⟩
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
/-- **Prefix Provenance Event-Lift**: In a successful `checkBytesCore` run,
    every feedToken finishProof event (during feed AND the done trailing flush)
    yields `Spec.Provable` in the pre-insertion database.

    This is the top-level event-lift theorem: it bridges the local
    `feedToken_finishProofEvent_prefixProvable` to the entire `checkBytesCore` execution. -/
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

/-- Public eliminator (core): after successful `checkBytesCore`, any concrete
    `FinishProofEvent` at the final `feedAll` state yields pre-insert `Spec.Provable`. -/
theorem checkBytesCore_done_finishProofEvent_prefix_provable
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

/-- Public eliminator (`checkBytes`): after successful `checkBytes`, any concrete
    `FinishProofEvent` at the final `feedAll` state yields pre-insert `Spec.Provable`. -/
theorem checkBytes_done_finishProofEvent_prefix_provable
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

/-- Certified eliminator (`checkBytes`): under a `prefixCertified` config, any concrete
    `FinishProofEvent` at the final `feedAll` state yields pre-insert `Spec.Provable`. -/
theorem checkBytes_done_finishProofEvent_certified (arr : ByteArray) (config : ModeConfig)
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
  checkBytes_done_finishProofEvent_prefix_provable arr config h_cfg.1 h_cfg.2 h_success

end Metamath.PrefixWitnessCheckBytes
