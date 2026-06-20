/-
Prefix Trace — Compressed Proof Full Provenance (Phase C6)

This module proves the parser-level compressed proof provenance theorem:
starting from an actual feedProof token stream in compressed mode
(.start → .preload → .compressed), derive Spec.Provable with NO h_reach
assumption. This mirrors `normal_proof_full_provenance` for compressed proofs.

**Architecture:**
- Step 1: feedProof.go extraction lemmas (case-analysis per ptp mode)
- Step 2: feedProof-level extraction (lift through withAt)
- Step 3: Token predicates (PreloadTokensOK, CompressedTokensOK)
- Step 4: PreloadTokensOK composition → preload fold
- Step 5: applyCA ptp irrelevance + CompressedTokensOK composition
- Step 6: Phase bridges (start→preload, preload→compressed)
- Step 7: End-to-end theorem (compressed_proof_full_provenance)

**Dependencies:**
- PrefixProvenance.lean (Parts 1-16): all foundation + bridge infrastructure
- ParserOperations.lean: parser correctness lemmas
- Verify.lean: parser implementation
-/

import Metamath.PrefixProvenance
import Metamath.VerifyParserStateThms

set_option autoImplicit false

namespace Metamath.PrefixTraceCompressed

open Metamath.Verify
open Metamath.WF
open Metamath.PrefixProvenance
open Metamath.Kernel (toDatabase toFrame toExpr SpecDBSubset
  verify_impl_sound fold_maintains_provable toDatabase_insert_subset
  compressed_proof_sound preload_fold_preserves_frame
  toFrame_some_of_wfFrame)
open Metamath.ParserOps (feedProof_success_db finishProof_success_insert
  insert_success_nonvar_fresh withAt_success_eq
  feedProof_goNormal_ok_preserves_core
  fresh_not_in_assert_frames_of_wf
  preloadMandatoryHyps_ok_preserves_core
  feedProof_go_ok_preserves_core)
open Metamath.ParserLoopInduction
  (ParserState_mkErrorFromEvidence_sets_error withAt_preserves_error)

-- Re-establish Formula to resolve ambiguity with Kernel.Formula
private abbrev Formula := Metamath.Verify.Formula

/-! ## Step 1: feedProof.go Extraction Lemmas

Case-analyze `feedProof.go` for each `ptp` mode and extract the underlying
operations. These are the building blocks for the feedProof-level theorems. -/

/-! ### Step 1a: .start + "(" → preloadMandatoryHyps -/

/-- In `.start` mode with "(" token, `go` calls `preloadMandatoryHyps` and
    transitions to `.preload`. -/
theorem go_start_open_extracts
    (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState)
    (h_ok : ParserState.feedProof.go s tk pr = .ok pr')
    (h_start : pr.ptp = .start) (h_open : tk.eqArray "(".toAscii) :
    ∃ pr_mid,
      s.db.preloadMandatoryHyps pr = .ok pr_mid ∧
      pr' = {pr_mid with ptp := .preload} := by
  unfold ParserState.feedProof.go at h_ok
  simp [h_start, h_open] at h_ok
  cases h_pre : s.db.preloadMandatoryHyps pr with
  | error e => simp [h_pre, Functor.map, Except.map] at h_ok
  | ok mid =>
    simp [h_pre, Functor.map, Except.map] at h_ok
    exact ⟨mid, rfl, h_ok.symm⟩

/-! ### Step 1b: .preload + non-")" → preload label -/

/-- In `.preload` mode with non-")" token, `go` calls `db.preload` with the
    label. Returns both the label validity and preload success. -/
theorem go_preload_label_extracts
    (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState)
    (h_ok : ParserState.feedProof.go s tk pr = .ok pr')
    (h_preload : pr.ptp = .preload) (h_not_close : ¬ tk.eqArray ")".toAscii) :
    (toLabel tk).fst = true ∧ s.db.preload pr (toLabel tk).snd = .ok pr' := by
  unfold ParserState.feedProof.go at h_ok
  simp [h_preload, h_not_close] at h_ok
  by_cases h_lbl : (toLabel tk).fst
  · simp [h_lbl] at h_ok
    exact ⟨h_lbl, h_ok⟩
  · simp [h_lbl] at h_ok

/-! ### Step 1c: .preload + ")" → compressed 0 -/

/-- In `.preload` mode with ")" token, `go` transitions to `.compressed 0`. -/
theorem go_preload_close_extracts
    (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState)
    (h_ok : ParserState.feedProof.go s tk pr = .ok pr')
    (h_preload : pr.ptp = .preload) (h_close : tk.eqArray ")".toAscii) :
    pr' = {pr with ptp := .compressed 0} := by
  unfold ParserState.feedProof.go at h_ok
  simp [h_preload, h_close, pure, Except.pure] at h_ok
  exact h_ok.symm

/-! ### Step 1d: .compressed chr → decode + apply -/

/-- In `.compressed chr` mode, `go` decodes the token and applies compressed
    actions. Returns the decoded actions, new accumulator, and intermediate state. -/
theorem go_compressed_extracts
    (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState) (chr : Nat)
    (h_ok : ParserState.feedProof.go s tk pr = .ok pr')
    (h_comp : pr.ptp = .compressed chr) :
    ∃ acts chr' pr_mid,
      ParserState.decodeCompressed tk chr = .ok (acts, chr') ∧
      ParserState.applyCompressedActions s.db pr acts = .ok pr_mid ∧
      pr' = {pr_mid with ptp := .compressed chr'} := by
  unfold ParserState.feedProof.go at h_ok
  simp [h_comp] at h_ok
  cases h_dec : ParserState.decodeCompressed tk chr with
  | error e => simp [h_dec, bind, Except.bind] at h_ok
  | ok dec =>
    obtain ⟨acts, chr'⟩ := dec
    simp [h_dec, bind, Except.bind] at h_ok
    cases h_apply : ParserState.applyCompressedActions s.db pr acts with
    | error e => simp [h_apply, Functor.map, Except.map] at h_ok
    | ok mid =>
      simp [h_apply, Functor.map, Except.map] at h_ok
      exact ⟨acts, chr', mid, rfl, h_apply, h_ok.symm⟩

/-! ## Step 2: feedProof-Level Extraction

Lift `go` extraction to `feedProof` level through `withAt`. -/

/-- feedProof success implies `go` returned `.ok` and the result is in `tokp`. -/
theorem feedProof_success_go_ok
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_success : (s.feedProof tk pr).db.error? = none) :
    ∃ pr',
      ParserState.feedProof.go s tk pr = .ok pr' ∧
      (s.feedProof tk pr).tokp = .proof pr' := by
  cases h_go : ParserState.feedProof.go s tk pr with
  | error msg =>
    exfalso
    have : (s.feedProof tk pr).db.error? ≠ none := by
      unfold ParserState.feedProof; simp only [h_go]
      exact withAt_preserves_error pr.label _
        (ParserState_mkErrorFromEvidence_sets_error s pr.pos (ProofCheckFail.evidence msg))
    exact this h_success
  | ok pr' =>
    exact ⟨pr', rfl, by unfold ParserState.feedProof; simp [h_go, ParserState.withAt_tokp]⟩

/-- feedProof in compressed mode: extract decoded actions and intermediate state. -/
theorem feedProof_compressed_extracts
    (s : ParserState) (tk : ByteSlice) (pr : ProofState) (chr : Nat)
    (h_success : (s.feedProof tk pr).db.error? = none)
    (h_comp : pr.ptp = .compressed chr) :
    ∃ pr' acts chr' pr_mid,
      (s.feedProof tk pr).tokp = .proof pr' ∧
      ParserState.decodeCompressed tk chr = .ok (acts, chr') ∧
      ParserState.applyCompressedActions s.db pr acts = .ok pr_mid ∧
      pr' = {pr_mid with ptp := .compressed chr'} := by
  obtain ⟨pr', h_go, h_tokp⟩ := feedProof_success_go_ok s tk pr h_success
  obtain ⟨acts, chr', pr_mid, h_dec, h_apply, h_eq⟩ :=
    go_compressed_extracts s tk pr pr' chr h_go h_comp
  exact ⟨pr', acts, chr', pr_mid, h_tokp, h_dec, h_apply, h_eq⟩

/-- feedProof in preload mode with non-")" token: extract preload operation. -/
theorem feedProof_preload_label_extracts
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_success : (s.feedProof tk pr).db.error? = none)
    (h_preload : pr.ptp = .preload) (h_not_close : ¬ tk.eqArray ")".toAscii) :
    ∃ pr',
      (s.feedProof tk pr).tokp = .proof pr' ∧
      s.db.preload pr (toLabel tk).snd = .ok pr' := by
  obtain ⟨pr', h_go, h_tokp⟩ := feedProof_success_go_ok s tk pr h_success
  have h_extract := go_preload_label_extracts s tk pr pr' h_go h_preload h_not_close
  exact ⟨pr', h_tokp, h_extract.2⟩

/-! ## Step 3: Token Predicates

Multi-step predicates for sequences of feedProof calls, analogous to
`NormalTokensOK` (PrefixProvenance Part 9b). -/

/-- A sequence of successful feedProof calls in `.preload` mode.
    Each token is non-")" and produces a preload. This models the preload
    label phase of compressed proofs (between "(" and ")"). -/
def PreloadTokensOK (s : ParserState) : ProofState → List ByteSlice → ProofState → Prop
  | pr, [], pr_final => pr_final = pr
  | pr, tk :: rest, pr_final =>
    ∃ pr_mid,
      (s.feedProof tk pr).db.error? = none ∧
      (s.feedProof tk pr).tokp = .proof pr_mid ∧
      pr.ptp = .preload ∧
      ¬ tk.eqArray ")".toAscii ∧
      PreloadTokensOK s pr_mid rest pr_final

/-- A sequence of successful feedProof calls in `.compressed` mode.
    Each token decodes to actions (no unknowns). Accumulates all decoded
    actions across tokens. This models the compressed body phase. -/
def CompressedTokensOK (s : ParserState) :
    ProofState → List ByteSlice → ProofState → List ParserState.CompressedAction → Prop
  | pr, [], pr_final, acc => pr_final = pr ∧ acc = []
  | pr, tk :: rest, pr_final, acc =>
    ∃ pr_mid acts chr chr' acc_rest,
      (s.feedProof tk pr).db.error? = none ∧
      (s.feedProof tk pr).tokp = .proof pr_mid ∧
      pr.ptp = .compressed chr ∧
      ParserState.decodeCompressed tk chr = .ok (acts, chr') ∧
      (∀ a ∈ acts, a ≠ ParserState.CompressedAction.unknown) ∧
      CompressedTokensOK s pr_mid rest pr_final acc_rest ∧
      acc = acts ++ acc_rest

/-! ## Step 4: PreloadTokensOK Composition

Show that `PreloadTokensOK` extracts to a `foldlM (DB.preload db)` fold. -/

/-- `db.preload` preserves `ptp` (it only modifies heap via pushHeap). -/
theorem preload_preserves_ptp (db : DB) (pr pr' : ProofState) (label : String)
    (h_ok : db.preload pr label = .ok pr') : pr'.ptp = pr.ptp := by
  unfold DB.preload at h_ok
  cases h_find : db.find? label with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok
    cases obj with
    | const _ => simp at h_ok
    | var _ => simp at h_ok
    | hyp _ f _ =>
      by_cases h_mem : label ∈ db.frame.hyps.toList
      · simp [h_mem] at h_ok; cases h_ok; rfl
      · simp [h_mem] at h_ok
    | assert f fr _ => simp at h_ok; cases h_ok; rfl

/-- `db.preload` preserves `label` (it only modifies heap via pushHeap). -/
theorem preload_preserves_label (db : DB) (pr pr' : ProofState) (label : String)
    (h_ok : db.preload pr label = .ok pr') : pr'.label = pr.label := by
  unfold DB.preload at h_ok
  cases h_find : db.find? label with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok
    cases obj with
    | const _ => simp at h_ok
    | var _ => simp at h_ok
    | hyp _ f _ =>
      by_cases h_mem : label ∈ db.frame.hyps.toList
      · simp [h_mem] at h_ok; cases h_ok; rfl
      · simp [h_mem] at h_ok
    | assert f fr _ => simp at h_ok; cases h_ok; rfl

/-- `db.preload` does not read `ptp`: result with modified ptp equals original
    result with ptp adjusted. -/
private theorem preload_ptp_ok (db : DB) (pr : ProofState) (label : String)
    (ptp : ProofTokenParser) (result : ProofState)
    (h_ok : db.preload pr label = .ok result) :
    db.preload {pr with ptp := ptp} label = .ok {result with ptp := ptp} := by
  unfold DB.preload at h_ok ⊢
  cases h_find : db.find? label with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok ⊢
    cases obj with
    | const _ => simp at h_ok
    | var _ => simp at h_ok
    | hyp _ f _ =>
      by_cases h_mem : label ∈ db.frame.hyps.toList
      · simp [h_mem, pure, Except.pure] at h_ok ⊢; cases h_ok; rfl
      · simp [h_mem] at h_ok
    | assert f fr _ =>
      simp [pure, Except.pure] at h_ok ⊢; cases h_ok; rfl

/-- **PreloadTokensOK composition:** the sequence of feedProof calls in preload
    mode corresponds to `db.preload` folded over the extracted labels.
    Preserves ptp, fmla, frame, and label. -/
theorem PreloadTokensOK_extracts_fold
    (s : ParserState) (tokens : List ByteSlice) (pr₀ pr_final : ProofState)
    (h_tokens : PreloadTokensOK s pr₀ tokens pr_final) :
    (tokens.map (fun tk => (toLabel tk).snd)).foldlM (DB.preload s.db) pr₀ = .ok pr_final ∧
    pr_final.ptp = pr₀.ptp ∧
    pr_final.fmla = pr₀.fmla ∧
    pr_final.frame = pr₀.frame ∧
    pr_final.label = pr₀.label := by
  induction tokens generalizing pr₀ with
  | nil =>
    unfold PreloadTokensOK at h_tokens; subst h_tokens
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons tk rest ih =>
    unfold PreloadTokensOK at h_tokens
    obtain ⟨pr_mid, h_ok, h_tokp, h_ptp, h_not_close, h_rest⟩ := h_tokens
    -- Extract go result and preload operation
    obtain ⟨pr_go, h_go, h_tokp_go⟩ := feedProof_success_go_ok s tk pr₀ h_ok
    have h_eq : pr_mid = pr_go := by
      rw [h_tokp] at h_tokp_go; exact TokenParser.proof.inj h_tokp_go
    subst h_eq
    have h_preload_ok : s.db.preload pr₀ (toLabel tk).snd = .ok pr_mid := by
      unfold ParserState.feedProof.go at h_go
      simp [h_ptp, h_not_close] at h_go
      by_cases h_lbl : (toLabel tk).fst
      · simp [h_lbl] at h_go; exact h_go
      · simp [h_lbl] at h_go
    -- Preservation
    have h_mid_core :=
      Metamath.ParserOps.preload_ok_preserves_core s.db pr₀ pr_mid (toLabel tk).snd h_preload_ok
    have h_mid_ptp := preload_preserves_ptp s.db pr₀ pr_mid (toLabel tk).snd h_preload_ok
    have h_mid_label := preload_preserves_label s.db pr₀ pr_mid (toLabel tk).snd h_preload_ok
    -- Apply IH
    obtain ⟨h_fold_rest, h_ptp_rest, h_fmla_rest, h_frame_rest, h_label_rest⟩ := ih pr_mid h_rest
    exact ⟨by simp [List.foldlM_cons, bind, Except.bind, h_preload_ok, h_fold_rest],
      h_ptp_rest.trans h_mid_ptp, h_fmla_rest.trans h_mid_core.1,
      h_frame_rest.trans h_mid_core.2, h_label_rest.trans h_mid_label⟩

/-! ## Step 5: applyCA ptp Irrelevance + CompressedTokensOK Composition

The key enabler for compressed proof composition: `applyCompressedActions` does
not read the `ptp` field of `ProofState`. This allows composing action lists
across ptp transitions between feedProof calls. -/

/-! ### Step 5a: foldlM General Lifting

A general principle: if a one-step function preserves a transformation `g`,
then the entire foldlM preserves it. -/

/-- If each step of `f` commutes with `g`, then foldlM commutes with `g`. -/
private theorem foldlM_lift_ok
    {α β : Type} {ε : Type}
    (f : α → β → Except ε α) (g : α → α)
    (h_step : ∀ (a : α) (b : β) (mid : α), f a b = .ok mid → f (g a) b = .ok (g mid))
    (xs : List β) (a result : α)
    (h_ok : xs.foldlM f a = .ok result) :
    xs.foldlM f (g a) = .ok (g result) := by
  induction xs generalizing a with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure] at h_ok ⊢
    cases h_ok; rfl
  | cons x rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_ok ⊢
    cases h_fx : f a x with
    | error e => simp [h_fx] at h_ok
    | ok mid =>
      simp [h_fx] at h_ok
      have h_fx' := h_step a x mid h_fx
      simp [h_fx']
      exact ih mid h_ok

/-! ### Step 5b: Per-Operation ptp Irrelevance -/

/-- `stepAssert` does not read the `ptp` field: the result with modified ptp
    equals the original result with ptp adjusted. -/
private theorem stepAssert_ptp_ok (db : DB) (pr : ProofState) (f : Formula) (fr : Frame)
    (ptp : ProofTokenParser) (result : ProofState)
    (h_ok : db.stepAssert pr f fr = .ok result) :
    db.stepAssert {pr with ptp := ptp} f fr = .ok {result with ptp := ptp} := by
  cases fr with
  | mk dj hyps =>
    unfold DB.stepAssert at h_ok ⊢
    by_cases h_size : hyps.size ≤ pr.stack.size
    · simp [h_size] at h_ok ⊢
      by_cases h_head : f.hasConstHead
      · simp [h_head] at h_ok ⊢
        by_cases h_syms : db.formulaSymsRespectFrame f { dj := dj, hyps := hyps }
        · simp [h_syms] at h_ok ⊢
          let off : {off // off + hyps.size = pr.stack.size} :=
            ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h_size⟩
          cases h_chk : db.checkHyp hyps pr.stack off 0 ∅ with
          | error err =>
            simp [off, h_chk, Bind.bind, Except.bind] at h_ok
          | ok subst =>
            cases h_dv : DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj dj subst with
            | error err =>
              simp [off, h_chk, h_dv, Bind.bind, Except.bind] at h_ok
            | ok _ =>
              cases h_subst : Metamath.Verify.Formula.subst subst f with
              | error err =>
                simp [off, h_chk, h_dv, h_subst, Bind.bind, Except.bind] at h_ok
                cases h_ok
              | ok concl =>
                have h_ok' :
                    (Except.ok
                      ({ pos := pr.pos, label := pr.label, fmla := pr.fmla, frame := pr.frame,
                         heap := pr.heap,
                         stack := (pr.stack.extract 0 (pr.stack.size - hyps.size)).push concl,
                         ptp := pr.ptp } : ProofState) : Except ProofCheckFail ProofState)
                      = (Except.ok result : Except ProofCheckFail ProofState) := by
                  simpa [off, h_chk, h_dv, h_subst, Bind.bind, Except.bind, Pure.pure,
                    Functor.map, Except.map] using h_ok
                injection h_ok' with hpr
                subst hpr
                simp [h_dv, h_subst, Bind.bind, Except.bind, Functor.map, Except.map]
        · simp [h_syms] at h_ok
      · simp [h_head] at h_ok
    · simp [h_size] at h_ok

/-- `save` does not read the `ptp` field. -/
private theorem save_ptp_ok (pr : ProofState) (ptp : ProofTokenParser) (result : ProofState)
    (h_ok : pr.save = .ok result) :
    ProofState.save {pr with ptp := ptp} = .ok {result with ptp := ptp} := by
  unfold ProofState.save at h_ok ⊢
  dsimp only at h_ok ⊢
  cases h_back : pr.stack.back? with
  | none => simp [h_back] at h_ok
  | some f =>
    simp only [h_back, pure, Except.pure] at h_ok ⊢
    cases h_ok; rfl

/-- `stepProof` does not read the `ptp` field. -/
private theorem stepProof_ptp_ok (db : DB) (pr : ProofState) (n : Nat)
    (ptp : ProofTokenParser) (result : ProofState)
    (h_ok : db.stepProof pr n = .ok result) :
    db.stepProof {pr with ptp := ptp} n = .ok {result with ptp := ptp} := by
  unfold DB.stepProof at h_ok ⊢
  dsimp only at h_ok ⊢
  cases h_heap : pr.heap[n]? with
  | none => simp [h_heap] at h_ok
  | some el =>
    simp only [h_heap] at h_ok ⊢
    cases el with
    | fmla f =>
      simp only [pure, Except.pure] at h_ok ⊢
      cases h_ok; rfl
    | assert f fr =>
      exact stepAssert_ptp_ok db pr f fr ptp result h_ok

/-! ### Step 5c: applyCompressedActions ptp Irrelevance -/

/-- **applyCompressedActions ptp irrelevance**: the compressed action fold does not
    read ptp. This is the critical enabler for composing across ptp transitions. -/
theorem applyCA_ptp_ok (db : DB) (pr : ProofState)
    (acts : List ParserState.CompressedAction)
    (ptp : ProofTokenParser) (result : ProofState)
    (h_ok : ParserState.applyCompressedActions db pr acts = .ok result) :
    ParserState.applyCompressedActions db {pr with ptp := ptp} acts =
      .ok {result with ptp := ptp} := by
  unfold ParserState.applyCompressedActions at h_ok ⊢
  exact foldlM_lift_ok _ (fun pr => {pr with ptp := ptp})
    (fun a act mid h => by
      cases act with
      | step n => exact stepProof_ptp_ok db a n ptp mid h
      | save =>
        dsimp only at h ⊢
        cases h_save : a.save with
        | error e => simp [h_save] at h
        | ok mid' =>
          simp only [h_save, pure, Except.pure] at h
          have h_save' := save_ptp_ok a ptp mid' h_save
          simp only [h_save', pure, Except.pure] at ⊢
          cases h; rfl
      | unknown =>
        dsimp only at h ⊢
        cases h_bool : db.config.rejectUnknownSteps
        · simp [h_bool] at h ⊢; cases h; rfl
        · simp [h_bool] at h
    ) acts pr result h_ok

/-! ### Step 5d: CompressedTokensOK Composition -/

/-- Reverse direction of `applyCA_ptp_ok`: if `applyCA` succeeds on the
    ptp-modified state, then it also succeeds on the original. -/
private theorem applyCA_ptp_rev (db : DB) (pr : ProofState)
    (acts : List ParserState.CompressedAction)
    (ptp : ProofTokenParser) (result : ProofState)
    (h_ok : ParserState.applyCompressedActions db {pr with ptp := ptp} acts = .ok result) :
    ParserState.applyCompressedActions db pr acts = .ok {result with ptp := pr.ptp} :=
  applyCA_ptp_ok db {pr with ptp := ptp} acts pr.ptp result h_ok

/-- **CompressedTokensOK composition:** the accumulated actions from multiple
    compressed tokens compose into a single `applyCompressedActions` call.
    The result has the same stack/heap/fmla/frame as the final feedProof output
    (ptp may differ since feedProof adjusts it per-token). -/
theorem CompressedTokensOK_extracts_applyCA
    (s : ParserState) (tokens : List ByteSlice) (pr₀ pr_final : ProofState)
    (all_acts : List ParserState.CompressedAction)
    (h_tokens : CompressedTokensOK s pr₀ tokens pr_final all_acts) :
    ∃ pr_result,
      ParserState.applyCompressedActions s.db pr₀ all_acts = .ok pr_result ∧
      pr_final.stack = pr_result.stack ∧
      pr_final.heap = pr_result.heap ∧
      pr_final.fmla = pr_result.fmla ∧
      pr_final.frame = pr_result.frame ∧
      (∀ a ∈ all_acts, a ≠ ParserState.CompressedAction.unknown) := by
  induction tokens generalizing pr₀ all_acts with
  | nil =>
    unfold CompressedTokensOK at h_tokens
    obtain ⟨h_eq, h_acc⟩ := h_tokens; subst h_acc; rw [h_eq]
    exact ⟨pr₀, rfl, rfl, rfl, rfl, rfl, nofun⟩
  | cons tk rest ih =>
    unfold CompressedTokensOK at h_tokens
    obtain ⟨pr_mid, acts, chr, chr', acc_rest, h_ok, h_tokp, h_ptp, h_dec,
      h_no_unk, h_rest, h_acc⟩ := h_tokens
    -- Extract the applyCA result from feedProof
    obtain ⟨pr_mid', acts', chr'', pr_inner, h_tokp_go, h_dec', h_apply, h_eq_mid⟩ :=
      feedProof_compressed_extracts s tk pr₀ chr h_ok h_ptp
    -- Unify pr_mid
    have h_mid_eq : pr_mid = pr_mid' := by
      rw [h_tokp] at h_tokp_go; exact TokenParser.proof.inj h_tokp_go
    subst h_mid_eq
    -- Unify decode results
    have h_dec_eq : acts' = acts ∧ chr'' = chr' := by
      have := h_dec'.symm.trans h_dec
      simp only [Except.ok.injEq, Prod.mk.injEq] at this; exact this
    rw [h_dec_eq.1] at h_apply; rw [h_dec_eq.2] at h_eq_mid
    -- IH on rest
    obtain ⟨pr_rest, h_rest_applyCA, h_stack, h_heap, h_fmla, h_frame, h_no_unk_rest⟩ :=
      ih pr_mid acc_rest h_rest
    -- Reverse ptp: pr_mid = {pr_inner with ptp := .compressed chr'} → get applyCA on pr_inner
    have h_inner_rest : ParserState.applyCompressedActions s.db pr_inner acc_rest =
        .ok {pr_rest with ptp := pr_inner.ptp} := by
      rw [h_eq_mid] at h_rest_applyCA
      exact applyCA_ptp_rev s.db pr_inner acc_rest (.compressed chr') pr_rest h_rest_applyCA
    -- Compose via foldlM_append
    subst h_acc
    have h_composed : ParserState.applyCompressedActions s.db pr₀ (acts ++ acc_rest) =
        .ok {pr_rest with ptp := pr_inner.ptp} := by
      unfold ParserState.applyCompressedActions at h_apply h_inner_rest ⊢
      rw [List.foldlM_append, h_apply]; exact h_inner_rest
    -- Field equalities hold (ptp-adjustment doesn't affect stack/heap/fmla/frame)
    refine ⟨{pr_rest with ptp := pr_inner.ptp}, h_composed, h_stack, h_heap, h_fmla, h_frame, ?_⟩
    intro a h_mem; rw [List.mem_append] at h_mem
    cases h_mem with
    | inl h => exact h_no_unk a h
    | inr h => exact h_no_unk_rest a h

/-! ## Step 6: Label Preservation + Phase Bridges

For the end-to-end theorem, we need `pr_final.label = label` and `pr_final.fmla = fmla`.
The fmla chain uses existing `ok_preserves_core` infrastructure. For label, we prove
preservation for `preloadMandatoryHyps`, `applyCompressedActions`, and the token predicates.
We also prove preload fold ptp-reverse for composing with `compressed_full_bridge`. -/

/-- `preloadMandatoryHyps` preserves `label` (only does pushHeap). -/
theorem preloadMandatoryHyps_preserves_label
    (db : DB) (pr pr' : ProofState)
    (h_ok : db.preloadMandatoryHyps pr = .ok pr') :
    pr'.label = pr.label := by
  let body : String → ProofState → Except ProofCheckFail (ForInStep ProofState) :=
    fun lbl acc =>
      match db.find? lbl with
      | some (.hyp _ f _) => pure (.yield (acc.pushHeap (.fmla f)))
      | _ => throw (.proofCheck (.mandatoryHypothesisNotFoundInDatabase lbl))
  have h_for_list : forIn pr.frame.hyps.toList pr body = Except.ok pr' := by
    unfold DB.preloadMandatoryHyps at h_ok
    have h_for : forIn pr.frame.hyps pr body = Except.ok pr' := by
      simp only [body]
      simp only [bind_pure] at h_ok
      exact h_ok
    calc forIn pr.frame.hyps.toList pr body
        = forIn pr.frame.hyps pr body := by
          simp [Array.forIn_toList (xs := pr.frame.hyps) (b := pr) (f := body)]
      _ = Except.ok pr' := h_for
  suffices h_aux :
      ∀ (labels : List String) (acc acc' : ProofState),
        forIn labels acc body = Except.ok acc' →
        acc'.label = acc.label from
    h_aux _ _ _ h_for_list
  intro labels
  induction labels with
  | nil => intro acc acc' h; simp at h; cases h; rfl
  | cons lbl rest ih =>
    intro acc acc' h
    simp [List.forIn_cons, body] at h
    cases h_find : db.find? lbl with
    | none => simp [h_find, Bind.bind, Except.bind] at h
    | some obj =>
      cases obj with
      | const _ => simp [h_find, Bind.bind, Except.bind] at h
      | var _ => simp [h_find, Bind.bind, Except.bind] at h
      | hyp ess f origin =>
        simp [h_find, Bind.bind, Except.bind, pure, Except.pure] at h
        rw [ih _ _ h]; simp [ProofState.pushHeap]
      | assert f fr origin => simp [h_find, Bind.bind, Except.bind] at h

/-- `stepAssert` preserves `label`. Same case analysis as `stepAssert_ok_preserves_core`
    in ParserOperations.lean, but extracting the label field. -/
private theorem stepAssert_preserves_label (db : DB) (pr : ProofState) (f : Formula) (fr : Frame)
    (result : ProofState) (h_ok : db.stepAssert pr f fr = .ok result) :
    result.label = pr.label := by
  cases fr with
  | mk dj hyps =>
    unfold DB.stepAssert at h_ok
    by_cases h_size : hyps.size ≤ pr.stack.size
    · simp [h_size] at h_ok
      by_cases h_head : f.hasConstHead
      · simp [h_head] at h_ok
        by_cases h_syms : db.formulaSymsRespectFrame f { dj := dj, hyps := hyps }
        · simp [h_syms] at h_ok
          let off : {off // off + hyps.size = pr.stack.size} :=
            ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h_size⟩
          cases h_chk : db.checkHyp hyps pr.stack off 0 ∅ with
          | error err => simp [off, h_chk, Bind.bind, Except.bind] at h_ok
          | ok subst =>
            cases h_dv : DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj dj subst with
            | error err => simp [off, h_chk, h_dv, Bind.bind, Except.bind] at h_ok
            | ok _ =>
              cases h_subst : Metamath.Verify.Formula.subst subst f with
              | error err =>
                simp [off, h_chk, h_dv, h_subst, Bind.bind, Except.bind] at h_ok; cases h_ok
              | ok concl =>
                have h_ok' :
                    (Except.ok
                      ({ pos := pr.pos, label := pr.label, fmla := pr.fmla, frame := pr.frame,
                         heap := pr.heap,
                         stack := (pr.stack.extract 0 (pr.stack.size - hyps.size)).push concl,
                         ptp := pr.ptp } : ProofState) : Except ProofCheckFail ProofState)
                      = (Except.ok result : Except ProofCheckFail ProofState) := by
                  simpa [off, h_chk, h_dv, h_subst, Bind.bind, Except.bind, Pure.pure,
                    Functor.map, Except.map] using h_ok
                injection h_ok' with hpr; subst hpr; rfl
        · simp [h_syms] at h_ok
      · simp [h_head] at h_ok
    · simp [h_size] at h_ok

/-- `stepProof` preserves `label`. -/
private theorem stepProof_preserves_label (db : DB) (pr : ProofState) (n : Nat)
    (result : ProofState) (h_ok : db.stepProof pr n = .ok result) :
    result.label = pr.label := by
  unfold DB.stepProof at h_ok
  cases h_heap : pr.heap[n]? with
  | none => simp [h_heap] at h_ok
  | some el =>
    simp only [h_heap] at h_ok
    cases el with
    | fmla f => simp only [pure, Except.pure] at h_ok; cases h_ok; rfl
    | assert f fr => exact stepAssert_preserves_label db pr f fr result h_ok

/-- `save` preserves `label`. -/
private theorem save_preserves_label (pr : ProofState) (result : ProofState)
    (h_ok : pr.save = .ok result) : result.label = pr.label := by
  unfold ProofState.save at h_ok
  cases h_back : pr.stack.back? with
  | none => simp [h_back] at h_ok
  | some f => simp only [h_back, pure, Except.pure] at h_ok; cases h_ok; rfl

/-- General: if each step of a foldlM preserves a field, the fold preserves it. -/
private theorem foldlM_preserves_field_ok
    {α β γ : Type} {ε : Type}
    (f : α → β → Except ε α) (proj : α → γ)
    (h_step : ∀ a b result, f a b = .ok result → proj result = proj a)
    (xs : List β) (a result : α) (h_ok : xs.foldlM f a = .ok result) :
    proj result = proj a := by
  induction xs generalizing a with
  | nil => simp only [List.foldlM_nil, pure, Except.pure] at h_ok; cases h_ok; rfl
  | cons x rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_ok
    cases h_fx : f a x with
    | error e => simp [h_fx] at h_ok
    | ok mid => simp [h_fx] at h_ok; rw [ih mid h_ok, h_step a x mid h_fx]

/-- `applyCompressedActions` preserves `label`. -/
theorem applyCA_preserves_label (db : DB) (pr : ProofState)
    (acts : List ParserState.CompressedAction) (result : ProofState)
    (h_ok : ParserState.applyCompressedActions db pr acts = .ok result) :
    result.label = pr.label := by
  unfold ParserState.applyCompressedActions at h_ok
  exact foldlM_preserves_field_ok _ ProofState.label
    (fun a act mid h => by
      cases act with
      | step n => exact stepProof_preserves_label db a n mid h
      | save =>
        dsimp only at h
        cases h_save : a.save with
        | error e => simp [h_save] at h
        | ok mid' =>
          simp [h_save, pure, Except.pure] at h; cases h
          exact save_preserves_label a mid h_save
      | unknown =>
        dsimp only at h
        cases h_bool : db.config.rejectUnknownSteps
        · simp [h_bool] at h; cases h; rfl
        · simp [h_bool] at h
    ) acts pr result h_ok

/-- `CompressedTokensOK` preserves `label`: feedProof in compressed mode
    only modifies stack/heap/ptp, not label. -/
theorem CompressedTokensOK_preserves_label
    (s : ParserState) (tokens : List ByteSlice) (pr₀ pr_final : ProofState)
    (all_acts : List ParserState.CompressedAction)
    (h_tokens : CompressedTokensOK s pr₀ tokens pr_final all_acts) :
    pr_final.label = pr₀.label := by
  induction tokens generalizing pr₀ all_acts with
  | nil =>
    unfold CompressedTokensOK at h_tokens
    exact h_tokens.1 ▸ rfl
  | cons tk rest ih =>
    unfold CompressedTokensOK at h_tokens
    obtain ⟨pr_mid, acts, chr, chr', acc_rest, h_ok, h_tokp, h_ptp, h_dec,
      _h_no_unk, h_rest, _h_acc⟩ := h_tokens
    -- Extract inner applyCA result
    obtain ⟨pr_go, acts', chr'', pr_inner, h_tokp', h_dec', h_apply, h_eq_mid⟩ :=
      feedProof_compressed_extracts s tk pr₀ chr h_ok h_ptp
    -- Unify pr_mid
    have h_mid_eq : pr_mid = pr_go := by
      rw [h_tokp] at h_tokp'; exact TokenParser.proof.inj h_tokp'
    subst h_mid_eq
    -- pr_mid.label = pr_inner.label (struct update preserves label)
    have h_mid_label : pr_mid.label = pr_inner.label := by rw [h_eq_mid]
    -- pr_inner.label = pr₀.label (applyCA preserves label)
    have h_inner_label : pr_inner.label = pr₀.label :=
      applyCA_preserves_label s.db pr₀ _ pr_inner h_apply
    -- By IH
    rw [ih pr_mid acc_rest h_rest, h_mid_label, h_inner_label]

/-- Preload fold on ptp-adjusted state: reverse direction.
    From `foldlM f ({pr with ptp} = ptp) = .ok result`, derive
    `foldlM f pr = .ok {result with ptp := pr.ptp}`. -/
private theorem preload_fold_ptp_rev (db : DB) (labels : List String)
    (pr : ProofState) (ptp : ProofTokenParser) (result : ProofState)
    (h_ok : labels.foldlM (DB.preload db) {pr with ptp := ptp} = .ok result) :
    labels.foldlM (DB.preload db) pr = .ok {result with ptp := pr.ptp} :=
  -- Apply foldlM_lift_ok with g = {· with ptp := pr.ptp} on the ptp-modified state.
  -- g({pr with ptp := ptp}) = {{pr with ptp := ptp} with ptp := pr.ptp} = pr (struct eta).
  -- g(result) = {result with ptp := pr.ptp}.
  foldlM_lift_ok (DB.preload db) (fun x => {x with ptp := pr.ptp})
    (fun a lbl mid h => preload_ptp_ok db a lbl pr.ptp mid h)
    labels {pr with ptp := ptp} result h_ok

/-! ## Step 7: End-to-End Compressed Proof Provenance -/

/-- **compressed_proof_full_provenance**: From actual feedProof token stream in
    compressed mode, derive `Spec.Provable` with NO `h_reach` assumption.

    Mirrors `normal_proof_full_provenance` for compressed proofs. The token stream:
    1. `tk_open` = "(" → preloadMandatoryHyps → .preload
    2. `preload_toks` → preload labels (fill heap)
    3. `tk_close` = ")" → .compressed 0
    4. `comp_toks` → decode + applyCompressedActions -/
theorem compressed_proof_full_provenance
    (s : ParserState) (label : String) (fmla : Formula)
    (tk_open : ByteSlice) (preload_toks : List ByteSlice)
    (tk_close : ByteSlice) (comp_toks : List ByteSlice)
    (all_acts : List ParserState.CompressedAction)
    (pr₀ pr₁ pr₂ pr₃ pr_final : ProofState)
    -- Initial state (from resumeThm)
    (h_init : pr₀ = ⟨⟨0,0⟩, label, fmla, s.db.frame, #[], #[], .start⟩)
    -- Phase A: "(" opens compressed mode
    (h_open_ok : (s.feedProof tk_open pr₀).db.error? = none)
    (h_open : tk_open.eqArray "(".toAscii)
    (h_open_tokp : (s.feedProof tk_open pr₀).tokp = .proof pr₁)
    -- Phase B: preload labels
    (h_preload : PreloadTokensOK s pr₁ preload_toks pr₂)
    -- Phase B→C: ")" closes preload
    (h_close_ok : (s.feedProof tk_close pr₂).db.error? = none)
    (h_close : tk_close.eqArray ")".toAscii)
    (h_close_tokp : (s.feedProof tk_close pr₂).tokp = .proof pr₃)
    -- Phase C: compressed body
    (h_comp : CompressedTokensOK s pr₃ comp_toks pr_final all_acts)
    -- finishProof + DB conditions
    (h_finish : (s.finishProof pr_final).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db)
    -- Stack conditions at finish
    (h_stack_one : pr_final.stack.size = 1)
    (h_stack_fmla : pr_final.stack[0]? = some pr_final.fmla) :
    ∃ (Γ_final : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase (s.finishProof pr_final).db = some Γ_final ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ_final spec_fr (toExpr pr_final.fmla) := by
  -- Phase A: "(" → preloadMandatoryHyps
  obtain ⟨pr₁', h_go_open, h_tokp_open⟩ := feedProof_success_go_ok s tk_open pr₀ h_open_ok
  have h_eq₁ : pr₁ = pr₁' := by
    rw [h_open_tokp] at h_tokp_open; exact TokenParser.proof.inj h_tokp_open
  subst h_eq₁
  obtain ⟨pr_mand, h_mand, h_pr₁_eq⟩ :=
    go_start_open_extracts s tk_open pr₀ pr₁ h_go_open (by subst h_init; rfl) h_open
  -- Phase B: preload labels
  let user_labels := preload_toks.map (fun tk => (toLabel tk).snd)
  obtain ⟨h_preload_fold, h_ptp₂, h_fmla₂, h_frame₂, h_label₂⟩ :=
    PreloadTokensOK_extracts_fold s preload_toks pr₁ pr₂ h_preload
  -- Phase B→C: ")" closes preload
  obtain ⟨pr₃', h_go_close, h_tokp_close⟩ := feedProof_success_go_ok s tk_close pr₂ h_close_ok
  have h_eq₃ : pr₃ = pr₃' := by
    rw [h_close_tokp] at h_tokp_close; exact TokenParser.proof.inj h_tokp_close
  subst h_eq₃
  have h_ptp₂_val : pr₂.ptp = .preload := by rw [h_ptp₂, h_pr₁_eq]
  have h_pr₃_eq : pr₃ = {pr₂ with ptp := .compressed 0} :=
    go_preload_close_extracts s tk_close pr₂ pr₃ h_go_close h_ptp₂_val h_close
  -- Phase C: compressed body extracts actions
  obtain ⟨pr_result, h_applyCA₃, h_stack_eq, h_heap_eq, h_fmla_eq, h_frame_eq, h_no_unk⟩ :=
    CompressedTokensOK_extracts_applyCA s comp_toks pr₃ pr_final all_acts h_comp
  -- ═══════════════════════════════════════════════════════════════
  -- Bridge to compressed_full_bridge via ptp irrelevance
  -- ═══════════════════════════════════════════════════════════════
  -- Preload fold ptp bridge: token-level fold on {pr_mand with ptp := .preload}
  -- → pure fold on pr_mand
  have h_user_fold : user_labels.foldlM (DB.preload s.db) pr_mand =
      .ok {pr₂ with ptp := pr_mand.ptp} := by
    rw [h_pr₁_eq] at h_preload_fold
    exact preload_fold_ptp_rev s.db user_labels pr_mand .preload pr₂ h_preload_fold
  -- Define the "pure" preload result (same content as pr₂, ptp from pr_mand)
  let pr_pre : ProofState := {pr₂ with ptp := pr_mand.ptp}
  -- applyCA ptp bridge: token-level applyCA on {pr₂ with ptp := .compressed 0}
  -- → pure applyCA on pr_pre
  have h_pr₃_as_pre : pr₃ = {pr_pre with ptp := .compressed 0} := by
    rw [h_pr₃_eq]
  have h_applyCA_pre : ParserState.applyCompressedActions s.db pr_pre all_acts =
      .ok {pr_result with ptp := pr_pre.ptp} := by
    rw [h_pr₃_as_pre] at h_applyCA₃
    exact applyCA_ptp_rev s.db pr_pre all_acts (.compressed 0) pr_result h_applyCA₃
  -- Stack/fmla conditions for compressed_full_bridge
  let pr_bridge : ProofState := {pr_result with ptp := pr_pre.ptp}
  have h_bridge_stack : pr_bridge.stack = pr_final.stack := h_stack_eq.symm
  have h_bridge_stack_one : pr_bridge.stack.size = 1 := by rw [h_bridge_stack]; exact h_stack_one
  -- Derive pr_final.fmla = fmla
  have h_fmla_chain : pr_final.fmla = fmla := by
    have : pr_result.fmla = pr₃.fmla :=
      (Metamath.ParserOps.applyCompressedActions_ok_preserves_core
        s.db pr₃ pr_result all_acts h_applyCA₃).1
    rw [h_fmla_eq, this, h_pr₃_eq, h_fmla₂, h_pr₁_eq]
    exact ((preloadMandatoryHyps_ok_preserves_core s.db pr₀ pr_mand h_mand).1).trans
      (by subst h_init; rfl)
  have h_bridge_stack_fmla : pr_bridge.stack[0]? = some fmla := by
    rw [h_bridge_stack]; rwa [h_fmla_chain] at h_stack_fmla
  -- Apply compressed_full_bridge
  have h_reach : ProofReachableZ s.db label fmla pr_bridge.stack :=
    compressed_full_bridge s.db label fmla pr₀ pr_mand pr_pre pr_bridge
      user_labels all_acts h_init h_mand h_user_fold h_applyCA_pre h_no_unk
      h_wf h_bridge_stack_one h_bridge_stack_fmla
  -- Rewrite to pr_final.stack and derive label/fmla
  rw [h_bridge_stack] at h_reach
  have h_label_chain : pr_final.label = label := by
    have h1 : pr_final.label = pr₃.label :=
      CompressedTokensOK_preserves_label s comp_toks pr₃ pr_final all_acts h_comp
    rw [h1, h_pr₃_eq]; simp
    rw [h_label₂, h_pr₁_eq]; simp
    exact (preloadMandatoryHyps_preserves_label s.db pr₀ pr_mand h_mand).trans
      (by subst h_init; rfl)
  -- Apply prefix_provable_any_proof_z
  rw [← h_label_chain, ← h_fmla_chain] at h_reach
  exact prefix_provable_any_proof_z s pr_final h_finish h_s_ok h_wf h_reach
    h_stack_one h_stack_fmla

/-! ## Phase C7: Compressed Proof Soundness Integration

Integrate compressed proof soundness into the same-DB verified pipeline.
The key bridge: `NormalProofReachable` IS a `stepNormal` fold, so
`fold_maintains_provable` applies directly → `Spec.Provable` against
`toDatabase db` (the SAME database where execution happened). -/

/-- A `NormalProofReachable` fold on a well-formed DB produces `Spec.Provable`
    against the **same** database (`toDatabase db`), not a post-insertion one.
    This is the key bridge from operational execution to spec-level provability
    without going through `finishProof`. -/
theorem NormalProofReachable_same_db_provable
    (db : DB) (label : String) (fmla : Formula) (stack : Array Formula)
    (h : NormalProofReachable db label fmla stack)
    (h_ok : db.error? = none) (h_wf : WellFormedDB db)
    (h_size : stack.size = 1) (h_fmla : stack[0]? = some fmla) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase db = some Γ ∧ toFrame db db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr fmla) := by
  obtain ⟨labels, pr_final, h_fold, h_stack⟩ := h
  -- Transfer stack properties through h_stack : pr_final.stack = stack
  have h_pr_size : pr_final.stack.size = 1 := h_stack ▸ h_size
  have h_pr_fmla : pr_final.stack[0]? = some fmla := h_stack ▸ h_fmla
  -- toDatabase is total (always returns some)
  have ⟨Γ, h_db⟩ : ∃ Γ, toDatabase db = some Γ := by unfold toDatabase; exact ⟨_, rfl⟩
  -- toFrame from WellFormedDB
  have ⟨fr, h_fr⟩ := toFrame_some_of_wfFrame db h_wf.1
  -- Apply fold_maintains_provable directly
  exact ⟨Γ, fr, h_db, h_fr,
    fold_maintains_provable db labels
      ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .normal⟩
      pr_final Γ fr fmla
      h_ok h_wf h_db h_fr h_wf.1 h_fold rfl h_pr_size h_pr_fmla⟩

/-- Any `ProofReachableZ` mode produces `Spec.Provable` against the **same** DB.
    All three modes (normal, compressed, z-compressed) reduce to
    `NormalProofReachable` via existing PrefixProvenance bridges. -/
theorem ProofReachableZ_same_db_provable
    (db : DB) (label : String) (fmla : Formula) (stack : Array Formula)
    (h_reach : ProofReachableZ db label fmla stack)
    (h_ok : db.error? = none) (h_wf : WellFormedDB db)
    (h_size : stack.size = 1) (h_fmla : stack[0]? = some fmla) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase db = some Γ ∧ toFrame db db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr fmla) := by
  -- All three ProofReachableZ constructors reduce to NormalProofReachable
  have h_normal : NormalProofReachable db label fmla stack := by
    cases h_reach with
    | normal h => exact h
    | compressed h => exact compressed_to_normal_reachable db label fmla stack h_wf h
    | zcompressed h =>
        exact z_compressed_to_normal_reachable db label fmla stack h_wf h h_size h_fmla
  exact NormalProofReachable_same_db_provable db label fmla stack h_normal h_ok h_wf h_size h_fmla

/-- **COMPRESSED SOUNDNESS (same DB)**: Compressed execution (mandatory preload +
    user preloads + compressed actions) on a well-formed DB produces
    `Spec.Provable` against the **same** database, not post-insertion.
    This is the operational-level integration theorem for compressed proofs. -/
theorem verify_compressed_impl_sound
    (db : DB) (label : String) (fmla : Formula)
    (pr_init pr_mand pr_preload pr_final : ProofState)
    (user_preloads : List String)
    (all_cacts : List ParserState.CompressedAction)
    (h_init : pr_init = ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .start⟩)
    (h_mand : db.preloadMandatoryHyps pr_init = .ok pr_mand)
    (h_user : user_preloads.foldlM (DB.preload db) pr_mand = .ok pr_preload)
    (h_actions : ParserState.applyCompressedActions db pr_preload all_cacts = .ok pr_final)
    (h_no_unk : ∀ a ∈ all_cacts, a ≠ ParserState.CompressedAction.unknown)
    (h_ok : db.error? = none) (h_wf : WellFormedDB db)
    (h_stack_one : pr_final.stack.size = 1)
    (h_stack_fmla : pr_final.stack[0]? = some fmla) :
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase db = some Γ ∧ toFrame db db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr fmla) := by
  -- compressed_full_bridge → ProofReachableZ against same DB
  have h_reach : ProofReachableZ db label fmla pr_final.stack :=
    compressed_full_bridge db label fmla pr_init pr_mand pr_preload pr_final
      user_preloads all_cacts h_init h_mand h_user h_actions h_no_unk
      h_wf h_stack_one h_stack_fmla
  -- ProofReachableZ → Spec.Provable (same DB)
  exact ProofReachableZ_same_db_provable db label fmla pr_final.stack
    h_reach h_ok h_wf h_stack_one h_stack_fmla

/-- **Compressed ⊂ Normal**: Any `ProofReachableZ` (including compressed execution)
    implies the existence of an equivalent normal `stepNormal` fold producing the
    same result on the stack. -/
theorem compressed_implies_normal_fold
    (db : DB) (label : String) (fmla : Formula) (stack : Array Formula)
    (h_reach : ProofReachableZ db label fmla stack)
    (h_wf : WellFormedDB db)
    (h_size : stack.size = 1) (h_fmla : stack[0]? = some fmla) :
    NormalProofReachable db label fmla stack := by
  cases h_reach with
  | normal h => exact h
  | compressed h => exact compressed_to_normal_reachable db label fmla stack h_wf h
  | zcompressed h =>
      exact z_compressed_to_normal_reachable db label fmla stack h_wf h h_size h_fmla

/-- **UNIFIED SOUNDNESS**: If either normal or compressed execution succeeds
    on a well-formed DB, then the result is `Spec.Provable` against the **same** DB.
    This is the audit-facing integration theorem: both proof modes are now part
    of the verified pipeline with same-DB provability. -/
theorem verify_any_mode_sound
    (db : DB) (label : String) (fmla : Formula)
    (h_ok : db.error? = none) (h_wf : WellFormedDB db) :
    -- Normal mode: stepNormal fold succeeds with singleton stack
    (∃ (proof : Array String) (pr_final : ProofState),
      proof.foldlM (fun pr step => db.stepNormal pr step)
        ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .normal⟩ = .ok pr_final ∧
      pr_final.stack.size = 1 ∧ pr_final.stack[0]? = some fmla)
    ∨
    -- Compressed mode: ProofReachableZ witnessed
    (∃ (stack : Array Formula),
      ProofReachableZ db label fmla stack ∧
      stack.size = 1 ∧ stack[0]? = some fmla) →
    ∃ (Γ : Spec.Database) (fr : Spec.Frame),
      toDatabase db = some Γ ∧ toFrame db db.frame = some fr ∧
      Spec.Provable Γ fr (toExpr fmla) := by
  intro h_mode
  rcases h_mode with ⟨proof, pr_final, h_fold, h_size, h_fmla⟩ | ⟨stack, h_reach, h_size, h_fmla⟩
  · -- Normal mode: wrap fold as NormalProofReachable, then same-DB bridge
    have h_normal : NormalProofReachable db label fmla pr_final.stack :=
      ⟨proof, pr_final, h_fold, rfl⟩
    exact NormalProofReachable_same_db_provable db label fmla pr_final.stack
      h_normal h_ok h_wf h_size h_fmla
  · -- Compressed mode: ProofReachableZ → same-DB bridge
    exact ProofReachableZ_same_db_provable db label fmla stack
      h_reach h_ok h_wf h_size h_fmla

/-- **PREFIX PROVENANCE (compressed, pre-insert DB)**: Compressed trace execution on a
    well-formed DB produces `Spec.Provable` against the **same** (pre-insert) database.
    Follows `compressed_proof_full_provenance` exactly but applies
    `ProofReachableZ_same_db_provable` instead of `prefix_provable_any_proof_z`. -/
theorem compressed_proof_prefix_provenance
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
    (_h_finish : (s.finishProof pr_final).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db)
    (h_stack_one : pr_final.stack.size = 1)
    (h_stack_fmla : pr_final.stack[0]? = some pr_final.fmla) :
    ∃ (Γ : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase s.db = some Γ ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ spec_fr (toExpr pr_final.fmla) := by
  -- Phase A: "(" → preloadMandatoryHyps
  obtain ⟨pr₁', h_go_open, h_tokp_open⟩ := feedProof_success_go_ok s tk_open pr₀ h_open_ok
  have h_eq₁ : pr₁ = pr₁' := by
    rw [h_open_tokp] at h_tokp_open; exact TokenParser.proof.inj h_tokp_open
  subst h_eq₁
  obtain ⟨pr_mand, h_mand, h_pr₁_eq⟩ :=
    go_start_open_extracts s tk_open pr₀ pr₁ h_go_open (by subst h_init; rfl) h_open
  -- Phase B: preload labels
  let user_labels := preload_toks.map (fun tk => (toLabel tk).snd)
  obtain ⟨h_preload_fold, h_ptp₂, h_fmla₂, h_frame₂, h_label₂⟩ :=
    PreloadTokensOK_extracts_fold s preload_toks pr₁ pr₂ h_preload
  -- Phase B→C: ")" closes preload
  obtain ⟨pr₃', h_go_close, h_tokp_close⟩ := feedProof_success_go_ok s tk_close pr₂ h_close_ok
  have h_eq₃ : pr₃ = pr₃' := by
    rw [h_close_tokp] at h_tokp_close; exact TokenParser.proof.inj h_tokp_close
  subst h_eq₃
  have h_ptp₂_val : pr₂.ptp = .preload := by rw [h_ptp₂, h_pr₁_eq]
  have h_pr₃_eq : pr₃ = {pr₂ with ptp := .compressed 0} :=
    go_preload_close_extracts s tk_close pr₂ pr₃ h_go_close h_ptp₂_val h_close
  -- Phase C: compressed body extracts actions
  obtain ⟨pr_result, h_applyCA₃, h_stack_eq, h_heap_eq, h_fmla_eq, h_frame_eq, h_no_unk⟩ :=
    CompressedTokensOK_extracts_applyCA s comp_toks pr₃ pr_final all_acts h_comp
  -- Bridge to compressed_full_bridge via ptp irrelevance
  have h_user_fold : user_labels.foldlM (DB.preload s.db) pr_mand =
      .ok {pr₂ with ptp := pr_mand.ptp} := by
    rw [h_pr₁_eq] at h_preload_fold
    exact preload_fold_ptp_rev s.db user_labels pr_mand .preload pr₂ h_preload_fold
  let pr_pre : ProofState := {pr₂ with ptp := pr_mand.ptp}
  have h_pr₃_as_pre : pr₃ = {pr_pre with ptp := .compressed 0} := by
    rw [h_pr₃_eq]
  have h_applyCA_pre : ParserState.applyCompressedActions s.db pr_pre all_acts =
      .ok {pr_result with ptp := pr_pre.ptp} := by
    rw [h_pr₃_as_pre] at h_applyCA₃
    exact applyCA_ptp_rev s.db pr_pre all_acts (.compressed 0) pr_result h_applyCA₃
  let pr_bridge : ProofState := {pr_result with ptp := pr_pre.ptp}
  have h_bridge_stack : pr_bridge.stack = pr_final.stack := h_stack_eq.symm
  have h_bridge_stack_one : pr_bridge.stack.size = 1 := by rw [h_bridge_stack]; exact h_stack_one
  -- Derive pr_final.fmla = fmla
  have h_fmla_chain : pr_final.fmla = fmla := by
    have : pr_result.fmla = pr₃.fmla :=
      (Metamath.ParserOps.applyCompressedActions_ok_preserves_core
        s.db pr₃ pr_result all_acts h_applyCA₃).1
    rw [h_fmla_eq, this, h_pr₃_eq, h_fmla₂, h_pr₁_eq]
    exact ((preloadMandatoryHyps_ok_preserves_core s.db pr₀ pr_mand h_mand).1).trans
      (by subst h_init; rfl)
  have h_bridge_stack_fmla : pr_bridge.stack[0]? = some fmla := by
    rw [h_bridge_stack]; rwa [h_fmla_chain] at h_stack_fmla
  -- Derive ProofReachableZ
  have h_reach : ProofReachableZ s.db label fmla pr_bridge.stack :=
    compressed_full_bridge s.db label fmla pr₀ pr_mand pr_pre pr_bridge
      user_labels all_acts h_init h_mand h_user_fold h_applyCA_pre h_no_unk
      h_wf h_bridge_stack_one h_bridge_stack_fmla
  rw [h_bridge_stack] at h_reach
  have h_label_chain : pr_final.label = label := by
    have h1 : pr_final.label = pr₃.label :=
      CompressedTokensOK_preserves_label s comp_toks pr₃ pr_final all_acts h_comp
    rw [h1, h_pr₃_eq]; simp
    rw [h_label₂, h_pr₁_eq]; simp
    exact (preloadMandatoryHyps_preserves_label s.db pr₀ pr_mand h_mand).trans
      (by subst h_init; rfl)
  -- Apply ProofReachableZ_same_db_provable (PRE-INSERT, not prefix_provable_any_proof_z)
  rw [← h_label_chain, ← h_fmla_chain] at h_reach
  exact ProofReachableZ_same_db_provable s.db pr_final.label pr_final.fmla pr_final.stack
    h_reach h_s_ok h_wf h_stack_one h_stack_fmla

end Metamath.PrefixTraceCompressed
