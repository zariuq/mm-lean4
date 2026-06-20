/-
Prefix Provenance — Foundation Lemmas (Phase C2)

This module proves the foundational lemmas for the prefix provenance property:
each $p theorem was proof-checked against a prefix database that did NOT contain
the theorem itself, and provability lifts from the prefix to the final database.

**Architecture:**
- Parts 1–3: Generic DB congruence (stepNormal depends only on find? and frame)
- Part 4: Insert-specific stability via existing infrastructure
- Part 5: Prefix provability composition (verify_impl_sound → mono_db lift)
- Part 6: Prefix witness at the finishProof boundary

**Existing infrastructure reused:**
- `feedProof_success_db` (ParserOperations): feedProof preserves s.db
- `finishProof_success_insert` (ParserOperations): finishProof = s.db.insert
- `insert_preserves_find?_ne` (ParserCorrectness): find? stable for other labels
- `insert_frame_unchanged` (ParserCorrectness): frame preserved by insert
- `insert_success_nonvar_fresh` (ParserOperations): insert success → label fresh
- `toDatabase_insert_subset` (KernelClean): SpecDBSubset across insert
- `verify_impl_sound` (KernelClean): proof checking → Spec.Provable

**What remains (future work):**
Parser-trace induction: connecting the parser's actual execution across
multiple feedToken calls to the foldlM hypothesis of verify_impl_sound.
-/

import Metamath.Verify
import Metamath.VerifyDBThms
import Metamath.KernelClean
import Metamath.ParserOperations

set_option autoImplicit false

namespace Metamath.PrefixProvenance

open Metamath.Verify
open Metamath.WF
-- Selective open: avoid Kernel.Formula shadowing Verify.Formula
open Metamath.Kernel (toDatabase toFrame toExpr SpecDBSubset
  verify_impl_sound toDatabase_insert_subset
  compressed_proof_sound preload_fold_preserves_frame
  toFrame_some_of_wfFrame)
open Metamath.ParserOps (feedProof_success_db finishProof_success_insert
  insert_success_nonvar_fresh withAt_success_eq
  feedProof_goNormal_ok_preserves_core
  fresh_not_in_assert_frames_of_wf
  preloadMandatoryHyps_ok_preserves_core)

-- Re-establish Formula to resolve ambiguity with Kernel.Formula
-- (KernelClean defines abbrev Kernel.Formula := Verify.Formula which
-- shadows Verify.Formula when inside namespace Metamath)
abbrev Formula := Verify.Formula

/-! ## Part 1: Helper Function Congruence

These lemmas prove that each helper function used by `stepNormal`/`stepAssert`
depends on `db` only through `db.find?` and `db.frame`. Two DBs that agree
on these produce identical results.
-/

/-- `frameFloatVars` depends on db only through `find?`. -/
theorem frameFloatVars_ext (db₁ db₂ : DB) (fr : Frame)
    (h_find : ∀ k, db₁.find? k = db₂.find? k) :
    db₁.frameFloatVars fr = db₂.frameFloatVars fr := by
  simp only [DB.frameFloatVars]
  congr 1
  funext lbl
  simp [h_find lbl]

/-- `formulaSymsRespectFrame` depends on db only through `find?`. -/
theorem formulaSymsRespectFrame_ext (db₁ db₂ : DB) (f : Formula) (fr : Frame)
    (h_find : ∀ k, db₁.find? k = db₂.find? k) :
    DB.formulaSymsRespectFrame db₁ f fr = DB.formulaSymsRespectFrame db₂ f fr := by
  simp only [DB.formulaSymsRespectFrame]
  rw [frameFloatVars_ext db₁ db₂ fr h_find]

set_option maxHeartbeats 1600000 in
/-- `checkHyp` depends on db only through `find?` (and transitively `formulaSymsRespectFrame`).

    Proof by descending induction on `hyps.size - i`: checkHyp recurses with i+1,
    so the "distance to termination" decreases. At each step, we rewrite `find?`
    and `formulaSymsRespectFrame`, then apply the induction hypothesis for i+1. -/
theorem checkHyp_ext (db₁ db₂ : DB) (hyps : Array String) (stack : Array Formula)
    (off : {off // off + hyps.size = stack.size})
    (h_find : ∀ k, db₁.find? k = db₂.find? k) :
    ∀ (i : Nat) (σ : Std.HashMap String Formula),
      db₁.checkHyp hyps stack off i σ = db₂.checkHyp hyps stack off i σ := by
  suffices h : ∀ (fuel i : Nat) (σ : Std.HashMap String Formula),
      fuel = hyps.size - i →
      db₁.checkHyp hyps stack off i σ = db₂.checkHyp hyps stack off i σ by
    intro i σ; exact h _ i σ rfl
  intro fuel
  induction fuel with
  | zero =>
    intro i σ h_eq
    have : ¬(i < hyps.size) := by omega
    rw [DB.checkHyp_base _ _ _ _ _ _ this, DB.checkHyp_base _ _ _ _ _ _ this]
  | succ n ih =>
    intro i σ h_eq
    by_cases h_lt : i < hyps.size
    · unfold DB.checkHyp
      rw [dif_pos h_lt, dif_pos h_lt, h_find]
      -- Lift to function-level equalities so rw matches partial applications
      have h_fsrf_eq : DB.formulaSymsRespectFrame db₁ = DB.formulaSymsRespectFrame db₂ :=
        funext fun f' => funext fun fr' => formulaSymsRespectFrame_ext db₁ db₂ f' fr' h_find
      have h_rec_eq : db₁.checkHyp hyps stack off (i+1) = db₂.checkHyp hyps stack off (i+1) :=
        funext (fun σ' => ih (i+1) σ' (by omega))
      rw [h_fsrf_eq, h_rec_eq]
    · rw [DB.checkHyp_base _ _ _ _ _ _ h_lt, DB.checkHyp_base _ _ _ _ _ _ h_lt]

/-- `stepAssert` depends on db only through `find?`.
    (The `frame` parameter is for API compatibility with `stepNormal_ext`.) -/
theorem stepAssert_ext (db₁ db₂ : DB) (pr : ProofState) (f : Formula) (fr : Frame)
    (h_find : ∀ k, db₁.find? k = db₂.find? k)
    (h_db_frame : db₁.frame = db₂.frame) :
    db₁.stepAssert pr f fr = db₂.stepAssert pr f fr := by
  unfold DB.stepAssert
  cases fr with
  | mk dj hyps =>
    simp only
    split
    · split
      · rfl
      · rw [formulaSymsRespectFrame_ext db₁ db₂ f _ h_find]
        split
        · rfl
        · rw [checkHyp_ext db₁ db₂ hyps _ _ h_find]
          rw [h_db_frame, frameFloatVars_ext db₁ db₂ db₂.frame h_find]
    · rfl

/-! ## Part 2: stepNormal / stepProof Congruence

The key lemma: `stepNormal` and `stepProof` depend on db only through
`find?` and `frame`. This is the foundation for prefix provenance.
-/

/-- **KEY LEMMA**: `stepNormal` depends on db only through `find?` and `frame`.

    If two databases agree on `find?` for all labels and have the same `frame`,
    then `stepNormal` produces identical results for any proof state and label.

    This means proof checking is insensitive to other DB fields (config, scopes,
    error state, etc.) and is stable under `DB.insert` of unrelated labels. -/
theorem stepNormal_ext (db₁ db₂ : DB) (pr : ProofState) (l : String)
    (h_find : ∀ k, db₁.find? k = db₂.find? k)
    (h_frame : db₁.frame = db₂.frame) :
    db₁.stepNormal pr l = db₂.stepNormal pr l := by
  unfold DB.stepNormal
  rw [h_find]
  split
  · rw [h_frame]
  · exact stepAssert_ext db₁ db₂ pr _ _ h_find h_frame
  · rfl

/-- `stepProof` depends on db only through `find?` and `frame`. -/
theorem stepProof_ext (db₁ db₂ : DB) (pr : ProofState) (idx : Nat)
    (h_find : ∀ k, db₁.find? k = db₂.find? k)
    (h_frame : db₁.frame = db₂.frame) :
    db₁.stepProof pr idx = db₂.stepProof pr idx := by
  unfold DB.stepProof
  split
  · rfl
  · rfl
  · exact stepAssert_ext db₁ db₂ pr _ _ h_find h_frame

/-! ## Part 3: foldlM Extension

Lift `stepNormal_ext` from single steps to entire proof executions via `foldlM`.
-/

/-- Helper: `List.foldlM` is congruent in the step function for the Except monad. -/
private theorem foldlM_congr_list {α β ε : Type}
    (f g : β → α → Except ε β) (l : List α) (init : β)
    (h_eq : ∀ b a, f b a = g b a) :
    l.foldlM f init = l.foldlM g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons]
    rw [h_eq]
    cases g init x with
    | ok b => simp [ih]
    | error e => rfl

/-- Helper: `Array.foldlM` is congruent in the step function for the Except monad. -/
private theorem foldlM_congr_array {α β ε : Type}
    (f g : β → α → Except ε β) (arr : Array α) (init : β)
    (h_eq : ∀ b a, f b a = g b a) :
    arr.foldlM f init = arr.foldlM g init := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact foldlM_congr_list f g arr.toList init h_eq

/-- **Proof execution congruence**: if two DBs agree on `find?` and `frame`,
    then `foldlM (stepNormal db₁)` and `foldlM (stepNormal db₂)` produce
    identical results for any proof array and initial state. -/
theorem foldlM_stepNormal_ext (db₁ db₂ : DB) (proof : Array String) (init : ProofState)
    (h_find : ∀ k, db₁.find? k = db₂.find? k)
    (h_frame : db₁.frame = db₂.frame) :
    proof.foldlM (fun pr step => db₁.stepNormal pr step) init =
    proof.foldlM (fun pr step => db₂.stepNormal pr step) init :=
  foldlM_congr_array _ _ proof init
    (fun pr step => stepNormal_ext db₁ db₂ pr step h_find h_frame)

/-! ## Part 4: Insert-Specific Stability

Corollaries of Parts 1–3 for the `DB.insert` case, using existing infrastructure:
- `insert_preserves_find?_ne` (ParserCorrectness)
- `insert_frame_unchanged` (ParserCorrectness)
-/

/-- After inserting a fresh label, `stepNormal` is unchanged for any labels
    whose `find?` lookup is unaffected by the insert.

    This is a direct corollary of `stepNormal_ext` +
    `insert_preserves_find?_ne` + `insert_frame_unchanged`. -/
theorem stepNormal_stable_under_insert
    (db : DB) (pos : Pos) (new_label : String) (obj : String → Object)
    (pr : ProofState) (l : String)
    (h_find_agree : ∀ k, (db.insert pos new_label obj).find? k = db.find? k) :
    DB.stepNormal (db.insert pos new_label obj) pr l = DB.stepNormal db pr l :=
  stepNormal_ext (db.insert pos new_label obj) db pr l
    h_find_agree (ParserCorrectness.insert_frame_unchanged db pos new_label obj)

/-- Fold stability: if all find? lookups agree after insert, entire proof
    execution is unchanged. -/
theorem foldlM_stable_under_insert
    (db : DB) (pos : Pos) (new_label : String) (obj : String → Object)
    (proof : Array String) (init : ProofState)
    (h_find_agree : ∀ k, (db.insert pos new_label obj).find? k = db.find? k) :
    proof.foldlM (fun pr step => DB.stepNormal (db.insert pos new_label obj) pr step) init =
    proof.foldlM (fun pr step => DB.stepNormal db pr step) init :=
  foldlM_stepNormal_ext (db.insert pos new_label obj) db proof init
    h_find_agree (ParserCorrectness.insert_frame_unchanged db pos new_label obj)

/-! ## Part 5: Prefix Provability Composition

The key theorem: if proof checking succeeds with a prefix database,
then the proved assertion is `Spec.Provable` in that prefix, and
the result lifts to any superset database via monotonicity.

Composes: `verify_impl_sound` + `toDatabase_insert_subset` + `Provable.mono_db`
-/

/-- **Prefix provability lifts to any superset database.**

    If proof checking succeeds with `prefix_db`, the assertion is `Spec.Provable`
    in `toDatabase prefix_db`. By `Provable.mono_db`, this lifts to any
    `Γ_final` that is a superset of `toDatabase prefix_db`. -/
theorem prefix_provable_lifts
    (prefix_db : DB) (label : String) (f : Formula) (proof : Array String)
    (h_prefix_success : prefix_db.error? = none)
    (h_prefix_wf : WellFormedDB prefix_db)
    (h_proof_ok : ∃ pr_final : ProofState,
      proof.foldlM (fun pr step => DB.stepNormal prefix_db pr step)
        ⟨⟨0,0⟩, label, f, prefix_db.frame, #[], #[], ProofTokenParser.normal⟩ =
          Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some f)
    (Γ_prefix Γ_final : Spec.Database)
    (h_Γ : toDatabase prefix_db = some Γ_prefix)
    (h_subset : SpecDBSubset Γ_prefix Γ_final) :
    ∃ fr : Spec.Frame,
      toFrame prefix_db prefix_db.frame = some fr ∧
      Spec.Provable Γ_final fr (toExpr f) := by
  -- Step 1: Apply verify_impl_sound to get Provable in prefix
  obtain ⟨Γ, fr, h_db, h_frame, h_provable⟩ :=
    verify_impl_sound prefix_db label f proof h_prefix_success h_prefix_wf h_proof_ok
  -- Step 2: Γ = Γ_prefix (both from toDatabase prefix_db)
  have h_eq : Γ = Γ_prefix := by
    have h_some : some Γ = some Γ_prefix := by rw [← h_db, ← h_Γ]
    injection h_some
  rw [h_eq] at h_provable
  -- Step 3: Lift to Γ_final via monotonicity
  exact ⟨fr, h_frame, Spec.Provable.mono_db h_subset h_provable⟩

/-! ## Part 6: Prefix Witness at the finishProof Boundary

These theorems compose existing parser infrastructure to characterize the
prefix provenance property at the point where `finishProof` inserts a theorem.

**Key facts from existing infrastructure:**
- `feedProof_success_db`: during proof mode, `s.db` is unchanged
- `finishProof_success_insert`: on success, `s'.db = s.db.insert pos label (.assert fmla fr)`
- Together: the proof was checked against `s.db`, then the theorem was inserted

**Remaining gap (future work):**
Connecting the parser's byte-stream feedProof execution to the `foldlM stepNormal`
hypothesis of `verify_impl_sound`. This requires parser-trace induction: walking
through the sequence of `feedToken` calls and showing that the accumulated proof
tokens produce the same result as `foldlM stepNormal` over the proof array.
-/

/-- At the finishProof boundary, the prefix DB is `s.db` (pre-insert),
    the theorem is fresh in this prefix, and the post-insert DB is an extension.

    Composes:
    - `finishProof_success_insert`: characterizes the insert
    - `insert_success_nonvar_fresh`: derives freshness from insert success -/
theorem finishProof_prefix_characterization
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none)
    (h_s_ok : s.db.error? = none) :
    -- The post-insert DB is exactly s.db.insert ...
    (s.finishProof pr).db = s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame) ∧
    -- The insert succeeded
    (s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame)).error? = none ∧
    -- The theorem label was fresh in s.db
    s.db.find? pr.label = none := by
  obtain ⟨h_db_eq, h_insert_ok⟩ := finishProof_success_insert s pr h_success
  refine ⟨h_db_eq, h_insert_ok, ?_⟩
  exact insert_success_nonvar_fresh s.db pr.pos pr.label (.assert pr.fmla pr.frame)
    h_s_ok h_insert_ok (by intro v; exact Object.noConfusion)

/-- Discharge h_hyp_disjoint from WellFormedDB + label freshness.

    When `db.find? label = none` and `WellFormedDB db`, no assertion's mandatory
    hypotheses contain `label`. This is because WellFormedDB ensures all hyp
    references in assertion frames resolve to existing objects, and a fresh
    label can't be among them.

    This converts from index-based freshness (`fresh_not_in_assert_frames_of_wf`)
    to the `∀ hyp ∈ fr.hyps.toList` form needed by `prefix_provable_lifts_across_insert`. -/
theorem hyp_disjoint_of_fresh (db : DB) (label : String)
    (h_wf : WellFormedDB db) (h_fresh : db.find? label = none) :
    ∀ (l : String) (f : Verify.Formula) (fr : Frame) (n : String),
      db.find? l = some (.assert f fr n) →
      ∀ hyp ∈ fr.hyps.toList, hyp ≠ label := by
  intro l f fr n h_find hyp h_mem
  have h_idx := fresh_not_in_assert_frames_of_wf db h_wf label h_fresh l f fr n h_find
  rw [Array.mem_toList_iff] at h_mem
  obtain ⟨i, hi, h_eq⟩ := Array.getElem_of_mem h_mem
  rw [← h_eq]
  exact h_idx i hi

/-- **Prefix provability lifts across insert at finishProof.**

    Given:
    - A parser state `s` where `finishProof` succeeds
    - The prefix DB `s.db` is well-formed and error-free
    - The proof fold hypothesis (foldlM stepNormal with `s.db` succeeds)
    - The hyp-disjointness condition for SpecDBSubset

    Conclusion: the assertion is `Spec.Provable` in the post-insert database.

    **Note:** The `h_proof_ok` hypothesis is the parser-trace gap.
    In the actual parser execution, this holds because feedProof processes
    the proof tokens one at a time using `s.db.stepNormal`, accumulating
    the same result as `foldlM stepNormal` over the proof array. Connecting
    these requires parser-trace induction (future work). -/
theorem prefix_provable_lifts_across_insert
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db)
    (proof : Array String)
    (h_proof_ok : ∃ pr_final : ProofState,
      proof.foldlM (fun p step => DB.stepNormal s.db p step)
        ⟨⟨0,0⟩, pr.label, pr.fmla, s.db.frame, #[], #[], ProofTokenParser.normal⟩ =
          Except.ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some pr.fmla)
    (h_hyp_disjoint : ∀ (l : String) (f : Verify.Formula) (fr : Frame) (n : String),
      s.db.find? l = some (.assert f fr n) →
      ∀ hyp ∈ fr.hyps.toList, hyp ≠ pr.label) :
    ∃ (Γ_final : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase (s.finishProof pr).db = some Γ_final ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ_final spec_fr (toExpr pr.fmla) := by
  -- Step 1: Characterize the finishProof boundary
  obtain ⟨h_db_eq, h_insert_ok, h_fresh⟩ :=
    finishProof_prefix_characterization s pr h_success h_s_ok
  -- Step 2: Get provability in the prefix via verify_impl_sound
  obtain ⟨Γ_prefix, spec_fr, h_Γ_prefix, h_frame, h_provable_prefix⟩ :=
    verify_impl_sound s.db pr.label pr.fmla proof h_s_ok h_wf h_proof_ok
  -- Step 3: Get the post-insert spec database
  have h_Γ_final : ∃ Γ', toDatabase (s.db.insert pr.pos pr.label
      (.assert pr.fmla pr.frame)) = some Γ' := by
    unfold toDatabase; exact ⟨_, rfl⟩
  obtain ⟨Γ_final, h_Γ_final⟩ := h_Γ_final
  -- Step 4: Freshness → SpecDBSubset
  have h_fresh_assert : ∀ (f : Verify.Formula) (fr : Frame) (n : String),
      s.db.find? pr.label ≠ some (.assert f fr n) := by
    intros; rw [h_fresh]; exact nofun
  have h_subset : SpecDBSubset Γ_prefix Γ_final :=
    toDatabase_insert_subset s.db pr.pos pr.label (.assert pr.fmla pr.frame)
      h_fresh_assert h_hyp_disjoint Γ_prefix h_Γ_prefix Γ_final h_Γ_final
  -- Step 5: Lift provability
  have h_provable_final : Spec.Provable Γ_final spec_fr (toExpr pr.fmla) :=
    Spec.Provable.mono_db h_subset h_provable_prefix
  -- Step 6: Rewrite the post-insert DB
  rw [h_db_eq]
  exact ⟨Γ_final, spec_fr, h_Γ_final, h_frame, h_provable_final⟩

/-! ## Part 7: Normal Proof Trace Bridge (Phase C3)

Close the `h_proof_ok` gap for normal (uncompressed) proofs.

**Key insight**: In normal mode, `feedProof.goNormal` calls `s.db.stepNormal pr l`
for each valid label token. The DB is unchanged throughout (`feedProof_success_db`).
So a sequence of N feedProof calls in normal mode IS `foldlM stepNormal` over
the N parsed labels.

**Architecture**:
- Part 7a: `stepNormal` only reads `pr.stack` and `pr.frame` — transfer lemma
- Part 7b: Lift to `foldlM` — fold transfer lemma
- Part 7c: Ghost array invariant (`NormalProofReachable`)
- Part 7d: Discharge `h_proof_ok` from `NormalProofReachable`
- Part 7e: Assumption-free prefix provability for normal proofs
-/

/-! ### Part 7a: stepNormal ProofState Transfer

`stepNormal` reads only `pr.stack` and `pr.frame` from the ProofState. It modifies
only `pr.stack` (via `push` or `shrink + push`). This means: if two ProofStates agree
on stack and frame, `stepNormal` produces results that agree on stack.

**Existing lemma reused**: `stepNormal_preserves_frame` (KernelClean:7834) — frame is preserved.
-/

open Metamath.Kernel (stepNormal_preserves_frame)

set_option maxHeartbeats 6400000 in
/-- `stepNormal` only modifies `pr.stack`, preserving `pr.label`.
    Used by the feedProof bridge to show label is stable across proof steps. -/
theorem stepNormal_preserves_label (db : DB) (pr pr' : ProofState) (l : String)
    (h_ok : db.stepNormal pr l = .ok pr') :
    pr'.label = pr.label := by
  obtain ⟨pos, label, fmla, frame, heap, stack, ptp⟩ := pr
  unfold DB.stepNormal at h_ok
  cases h_find : db.find? l with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok
    cases obj with
    | const _ => simp at h_ok
    | var _ => simp at h_ok
    | hyp ess f _ =>
      by_cases h_mem : l ∈ db.frame.hyps.toList
      · simp only [h_mem, ↓reduceIte] at h_ok
        cases ess with
        | true =>
          simp only [↓reduceIte] at h_ok
          split at h_ok
          · exact absurd h_ok nofun
          · simp only [pure, Except.pure, Except.ok.injEq] at h_ok; subst h_ok; rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false] at h_ok
          split at h_ok
          · exact absurd h_ok nofun
          · simp only [pure, Except.pure, Except.ok.injEq] at h_ok; subst h_ok; rfl
      · simp [h_mem] at h_ok
    | assert f' fr' _ =>
      simp only [DB.stepAssert] at h_ok
      split at h_ok
      · split at h_ok
        · exact absurd h_ok nofun
        · split at h_ok
          · exact absurd h_ok nofun
          · simp only [bind, Except.bind] at h_ok
            cases h_chk : db.checkHyp fr'.hyps stack
                ⟨stack.size - fr'.hyps.size, by omega⟩ 0 ∅ with
            | error e => simp [h_chk] at h_ok
            | ok σ =>
              simp only [h_chk] at h_ok
              cases h_dv : DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj fr'.dj σ with
              | error e => simp [h_dv] at h_ok
              | ok u =>
                simp only [h_dv] at h_ok
                split at h_ok
                · simp only [pure, Except.pure, Except.ok.injEq] at h_ok
                  subst h_ok; rfl
                · exact absurd h_ok nofun
      · exact absurd h_ok nofun

set_option maxHeartbeats 6400000 in
/-- `stepNormal` preserves `pr.ptp` (like label and fmla, ptp is not touched). -/
theorem stepNormal_preserves_ptp (db : DB) (pr pr' : ProofState) (l : String)
    (h_ok : db.stepNormal pr l = .ok pr') :
    pr'.ptp = pr.ptp := by
  obtain ⟨pos, label, fmla, frame, heap, stack, ptp⟩ := pr
  unfold DB.stepNormal at h_ok
  cases h_find : db.find? l with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok
    cases obj with
    | const _ => simp at h_ok
    | var _ => simp at h_ok
    | hyp ess f _ =>
      by_cases h_mem : l ∈ db.frame.hyps.toList
      · simp only [h_mem, ↓reduceIte] at h_ok
        cases ess with
        | true =>
          simp only [↓reduceIte] at h_ok
          split at h_ok
          · exact absurd h_ok nofun
          · simp only [pure, Except.pure, Except.ok.injEq] at h_ok; subst h_ok; rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false] at h_ok
          split at h_ok
          · exact absurd h_ok nofun
          · simp only [pure, Except.pure, Except.ok.injEq] at h_ok; subst h_ok; rfl
      · simp [h_mem] at h_ok
    | assert f' fr' _ =>
      simp only [DB.stepAssert] at h_ok
      split at h_ok
      · split at h_ok
        · exact absurd h_ok nofun
        · split at h_ok
          · exact absurd h_ok nofun
          · simp only [bind, Except.bind] at h_ok
            cases h_chk : db.checkHyp fr'.hyps stack
                ⟨stack.size - fr'.hyps.size, by omega⟩ 0 ∅ with
            | error e => simp [h_chk] at h_ok
            | ok σ =>
              simp only [h_chk] at h_ok
              cases h_dv : DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj fr'.dj σ with
              | error e => simp [h_dv] at h_ok
              | ok u =>
                simp only [h_dv] at h_ok
                split at h_ok
                · simp only [pure, Except.pure, Except.ok.injEq] at h_ok
                  subst h_ok; rfl
                · exact absurd h_ok nofun
      · exact absurd h_ok nofun

set_option maxHeartbeats 6400000 in
/-- `stepAssert` reads only `pr.stack` (not `pr.frame`) for computation.
    If two ProofStates agree on stack and stepAssert succeeds for one,
    it succeeds for the other with the same resulting stack. -/
theorem stepAssert_transfer (db : DB) (pr₁ pr₂ r₁ : ProofState)
    (f : Formula) (fr : Frame)
    (h_stack : pr₁.stack = pr₂.stack)
    (h_ok : db.stepAssert pr₁ f fr = .ok r₁) :
    ∃ r₂, db.stepAssert pr₂ f fr = .ok r₂ ∧ r₂.stack = r₁.stack := by
  -- Destructure ProofStates so stack becomes a free variable for subst
  obtain ⟨pos₁, label₁, fmla₁, frame₁, heap₁, stack₁, ptp₁⟩ := pr₁
  obtain ⟨pos₂, label₂, fmla₂, frame₂, heap₂, stack₂, ptp₂⟩ := pr₂
  simp only at h_stack
  subst h_stack
  -- Now both ProofStates share the same stack₁ and frame₁.
  -- stepAssert's computation is identical; only the result wrapper differs.
  simp only [DB.stepAssert] at h_ok ⊢
  -- Split goal on the computation branches (same for both)
  split
  · rename_i h_le; rw [dif_pos h_le] at h_ok
    split
    · rename_i h_head; simp [h_head] at h_ok
    · rename_i h_head; rw [if_neg h_head] at h_ok
      split
      · rename_i h_fsrf; simp [h_fsrf] at h_ok
      · rename_i h_fsrf; rw [if_neg h_fsrf] at h_ok
        -- In the do block: checkHyp → dvCheck → subst → push
        -- Unfold bind to expose match on each monadic step
        simp only [bind, Except.bind] at h_ok ⊢
        -- Case split on each step (same computation for both)
        cases h_chk : db.checkHyp fr.hyps stack₁
            ⟨stack₁.size - fr.hyps.size, Nat.sub_add_cancel h_le⟩ 0 ∅ with
        | ok σ =>
          simp only [h_chk] at h_ok ⊢
          cases h_dv : DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj fr.dj σ with
          | ok u =>
            simp only [h_dv] at h_ok ⊢
            -- Split on `match f.subst σ with ...` (same computation for both)
            split
            · -- .ok case in goal; align h_ok to same branch
              rename_i concl h_fsubst
              rw [h_fsubst] at h_ok
              simp only [pure, Except.pure, Except.ok.injEq] at h_ok ⊢
              exact ⟨_, rfl, by subst h_ok; rfl⟩
            · -- .error case in goal
              rename_i e h_fsubst
              rw [h_fsubst] at h_ok
              exact absurd h_ok nofun
          | error e => simp only [h_dv] at h_ok; exact absurd h_ok nofun
        | error e => simp only [h_chk] at h_ok; exact absurd h_ok nofun
  · rename_i h_nle; rw [dif_neg h_nle] at h_ok; exact absurd h_ok nofun

/-- **Single-step transfer**: if two ProofStates agree on stack,
    and `stepNormal` succeeds for one, it succeeds for the other with
    the same resulting stack. (stepNormal uses only pr.stack, not pr.frame.) -/
theorem stepNormal_transfer (db : DB) (pr₁ pr₂ r₁ : ProofState) (l : String)
    (h_stack : pr₁.stack = pr₂.stack)
    (h_ok : db.stepNormal pr₁ l = .ok r₁) :
    ∃ r₂, db.stepNormal pr₂ l = .ok r₂ ∧ r₂.stack = r₁.stack := by
  -- Destructure to make stack substitutable
  obtain ⟨pos₁, label₁, fmla₁, frame₁, heap₁, stack₁, ptp₁⟩ := pr₁
  obtain ⟨pos₂, label₂, fmla₂, frame₂, heap₂, stack₂, ptp₂⟩ := pr₂
  simp only at h_stack
  subst h_stack
  -- Now both share the same stack₁ and frame₁
  unfold DB.stepNormal at h_ok ⊢
  cases h_find : db.find? l with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok ⊢
    cases obj with
    | const _ => simp at h_ok
    | var _ => simp at h_ok
    | hyp ess f' _ =>
      by_cases h_mem : l ∈ db.frame.hyps.toList
      · simp only [h_mem, ↓reduceIte] at h_ok ⊢
        -- Split on ess (essential vs floating hypothesis)
        cases ess with
        | true =>
          simp only [↓reduceIte] at h_ok ⊢
          -- Guard: !f'.hasConstHead
          split
          · rename_i h_guard; simp [h_guard] at h_ok
          · rename_i h_guard; rw [if_neg h_guard] at h_ok
            simp only [pure, Except.pure, Except.ok.injEq] at h_ok ⊢
            exact ⟨_, rfl, by subst h_ok; rfl⟩
        | false =>
          simp only [Bool.false_eq_true, ite_false] at h_ok ⊢
          -- Guard: !f'.isFloatShape
          split
          · rename_i h_guard; simp [h_guard] at h_ok
          · rename_i h_guard; rw [if_neg h_guard] at h_ok
            simp only [pure, Except.pure, Except.ok.injEq] at h_ok ⊢
            exact ⟨_, rfl, by subst h_ok; rfl⟩
      · simp [h_mem] at h_ok
    | assert f' fr' _ =>
      exact stepAssert_transfer db
        ⟨pos₁, label₁, fmla₁, frame₁, heap₁, stack₁, ptp₁⟩
        ⟨pos₂, label₂, fmla₂, frame₂, heap₂, stack₁, ptp₂⟩
        r₁ f' fr' rfl h_ok

/-! ### Part 7b: foldlM Frame Preservation and Transfer

Helper: frame is preserved through a foldlM stepNormal execution.
Then lift the single-step transfer to entire proof executions. -/

/-- Frame is preserved through `foldlM stepNormal`. Uses `stepNormal_preserves_frame`. -/
private theorem foldlM_preserves_frame (db : DB) (labels : List String)
    (init r : ProofState)
    (h_fold : labels.foldlM (fun pr step => db.stepNormal pr step) init = .ok r) :
    r.frame = init.frame := by
  induction labels generalizing init with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure] at h_fold
    cases h_fold; rfl
  | cons l rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_fold
    cases h_step : db.stepNormal init l with
    | error e => rw [h_step] at h_fold; exact absurd h_fold nofun
    | ok mid =>
      rw [h_step] at h_fold
      have h_mid_frame := stepNormal_preserves_frame db init mid l h_step
      rw [ih mid h_fold, h_mid_frame]

/-- **Fold transfer**: if `foldlM stepNormal` succeeds starting from `init₁`,
    it also succeeds starting from `init₂` (same stack),
    and the resulting stacks match. (stepNormal uses only pr.stack.) -/
theorem foldlM_stepNormal_transfer (db : DB) (labels : List String)
    (init₁ init₂ r₁ : ProofState)
    (h_stack : init₁.stack = init₂.stack)
    (h_fold : labels.foldlM (fun pr step => db.stepNormal pr step) init₁ = .ok r₁) :
    ∃ r₂, labels.foldlM (fun pr step => db.stepNormal pr step) init₂ = .ok r₂ ∧
      r₂.stack = r₁.stack := by
  induction labels generalizing init₁ init₂ r₁ with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure] at h_fold ⊢
    exact ⟨init₂, rfl, by cases h_fold; exact h_stack.symm⟩
  | cons l rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_fold ⊢
    -- Extract the first step
    cases h_step : db.stepNormal init₁ l with
    | error e => rw [h_step] at h_fold; exact absurd h_fold nofun
    | ok mid₁ =>
      rw [h_step] at h_fold
      -- Transfer the first step
      obtain ⟨mid₂, h_step₂, h_mid_stack⟩ :=
        stepNormal_transfer db init₁ init₂ mid₁ l h_stack h_step
      rw [h_step₂]
      -- Apply induction hypothesis
      exact ih mid₁ mid₂ r₁ h_mid_stack.symm h_fold

/-- Array version of fold transfer. -/
theorem foldlM_stepNormal_transfer_array (db : DB) (proof : Array String)
    (init₁ init₂ r₁ : ProofState)
    (h_stack : init₁.stack = init₂.stack)
    (h_fold : proof.foldlM (fun pr step => db.stepNormal pr step) init₁ = .ok r₁) :
    ∃ r₂, proof.foldlM (fun pr step => db.stepNormal pr step) init₂ = .ok r₂ ∧
      r₂.stack = r₁.stack := by
  rw [← Array.foldlM_toList] at h_fold ⊢
  exact foldlM_stepNormal_transfer db proof.toList init₁ init₂ r₁ h_stack h_fold

/-! ### Part 7c: Ghost Array Invariant

`NormalProofReachable` captures the invariant maintained by normal-mode proof checking:
the current stack is reachable via `foldlM stepNormal` from the initial state that
`verify_impl_sound` expects. -/

/-- A proof stack is reachable if there exists a label array whose fold via stepNormal
    produces a ProofState with that stack. The init matches `verify_impl_sound`'s expected
    initial state (pos=0, frame=db.frame, empty stack/heap, ptp=.normal). -/
def NormalProofReachable (db : DB) (label : String) (fmla : Formula)
    (stack : Array Formula) : Prop :=
  ∃ (labels : Array String) (pr_final : ProofState),
    labels.foldlM (fun pr step => db.stepNormal pr step)
      ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], ProofTokenParser.normal⟩ = .ok pr_final ∧
    pr_final.stack = stack

/-- Base case: empty stack is reachable with zero labels. -/
theorem NormalProofReachable_init (db : DB) (label : String) (fmla : Formula) :
    NormalProofReachable db label fmla #[] :=
  ⟨#[], ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .normal⟩, rfl, rfl⟩

/-- Helper: append one step to a successful foldlM. -/
private theorem foldlM_append_step (db : DB) (labels : Array String)
    (init mid : ProofState) (l : String) (r : ProofState)
    (h_fold : labels.foldlM (fun pr step => db.stepNormal pr step) init = .ok mid)
    (h_step : db.stepNormal mid l = .ok r) :
    (labels.push l).foldlM (fun pr step => db.stepNormal pr step) init = .ok r := by
  rw [← Array.foldlM_toList] at h_fold ⊢
  rw [Array.toList_push, List.foldlM_append]
  simp only [h_fold, List.foldlM_cons, List.foldlM_nil, bind, Except.bind, h_step, pure,
    Except.pure]

/-- Step case: if the current stack is reachable and stepNormal succeeds,
    the new stack is also reachable. Uses fold transfer + frame preservation. -/
theorem NormalProofReachable_step (db : DB) (label : String) (fmla : Formula)
    (pr pr' : ProofState) (l : String)
    (h_reach : NormalProofReachable db label fmla pr.stack)
    (h_step : db.stepNormal pr l = .ok pr') :
    NormalProofReachable db label fmla pr'.stack := by
  obtain ⟨old_labels, ghost_final, h_ghost_fold, h_ghost_stack⟩ := h_reach
  -- Transfer stepNormal from pr to ghost_final (they agree on stack)
  obtain ⟨ghost_next, h_ghost_step, h_ghost_next_stack⟩ :=
    stepNormal_transfer db pr ghost_final pr' l
      h_ghost_stack.symm h_step
  -- Extend the fold with one more step
  exact ⟨old_labels.push l, ghost_next,
    foldlM_append_step db old_labels _ ghost_final l ghost_next h_ghost_fold h_ghost_step,
    h_ghost_next_stack⟩

/-! ### Part 7d: Discharge h_proof_ok -/

/-- Discharge `h_proof_ok` from `NormalProofReachable` + finishProof success conditions.
    This is the key: `NormalProofReachable` directly provides the existential proof
    array that `verify_impl_sound` needs. -/
theorem normal_proof_h_proof_ok_discharged
    (db : DB) (label : String) (fmla : Formula) (stack : Array Formula)
    (h_reach : NormalProofReachable db label fmla stack)
    (h_stack_one : stack.size = 1)
    (h_stack_fmla : stack[0]? = some fmla) :
    ∃ (proof : Array String) (pr_final : ProofState),
      proof.foldlM (fun p step => DB.stepNormal db p step)
        ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], ProofTokenParser.normal⟩ =
          .ok pr_final ∧
      pr_final.stack.size = 1 ∧
      pr_final.stack[0]? = some fmla := by
  obtain ⟨labels, pr_final, h_fold, h_pr_stack⟩ := h_reach
  exact ⟨labels, pr_final, h_fold,
    by rw [h_pr_stack]; exact h_stack_one,
    by rw [h_pr_stack]; exact h_stack_fmla⟩

/-! ### Part 7e: Assumption-Free Prefix Provability (Normal Proofs) -/

/-- **MAIN THEOREM (normal proofs)**: Prefix provability without `h_proof_ok`
    or `h_hyp_disjoint`.

    Composes `NormalProofReachable` + `normal_proof_h_proof_ok_discharged` +
    `hyp_disjoint_of_fresh` + `prefix_provable_lifts_across_insert`.
    The only assumption about the proof execution is `NormalProofReachable`,
    which is maintained by each feedProof call in normal mode. -/
theorem prefix_provable_normal_proof
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db)
    (h_reach : NormalProofReachable s.db pr.label pr.fmla pr.stack)
    (h_stack_one : pr.stack.size = 1)
    (h_stack_fmla : pr.stack[0]? = some pr.fmla) :
    ∃ (Γ_final : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase (s.finishProof pr).db = some Γ_final ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ_final spec_fr (toExpr pr.fmla) := by
  -- Step 1: Discharge h_proof_ok from NormalProofReachable
  obtain ⟨proof, pr_final, h_fold, h_size, h_stack⟩ :=
    normal_proof_h_proof_ok_discharged s.db pr.label pr.fmla pr.stack
      h_reach h_stack_one h_stack_fmla
  -- Step 2: Derive h_hyp_disjoint from WellFormedDB + label freshness
  have ⟨_, _, h_fresh⟩ := finishProof_prefix_characterization s pr h_success h_s_ok
  have h_hyp_disjoint := hyp_disjoint_of_fresh s.db pr.label h_wf h_fresh
  -- Step 3: Apply the existing prefix theorem
  exact prefix_provable_lifts_across_insert s pr h_success h_s_ok h_wf
    proof ⟨pr_final, h_fold, h_size, h_stack⟩ h_hyp_disjoint

/-! ## Part 8: feedProof Normal Bridge

Connect the parser's `feedProof` execution in normal mode to `NormalProofReachable`.
This discharges the `h_reach` assumption, making prefix provenance automatic for
normal proofs.

**Strategy**: In normal mode, `feedProof.goNormal` with a valid non-"?" label
literally calls `s.db.stepNormal pr (toLabel tk).2`. Extract this and apply
`NormalProofReachable_step`.
-/

/-- In normal mode with a valid non-"?" label, `goNormal` IS a `stepNormal` call.
    Returns both the label and the stepNormal success evidence. -/
theorem goNormal_extracts_stepNormal
    (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState)
    (h_ok : ParserState.feedProof.goNormal s tk pr = .ok pr')
    (h_not_q : ¬ tk.eqArray "?".toAscii) :
    s.db.stepNormal pr (toLabel tk).2 = .ok pr' := by
  unfold ParserState.feedProof.goNormal at h_ok
  simp [h_not_q] at h_ok
  by_cases h_lbl : (toLabel tk).fst
  · simpa [h_lbl] using h_ok
  · simp [h_lbl] at h_ok

/-- `feedProof.go` in `.normal` mode delegates to `goNormal`. -/
private theorem go_normal_eq_goNormal
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_normal : pr.ptp = .normal) :
    ParserState.feedProof.go s tk pr = ParserState.feedProof.goNormal s tk pr := by
  unfold ParserState.feedProof.go
  simp [h_normal]

/-- **Single-step feedProof bridge**: When `feedProof` succeeds in normal mode with
    a valid non-"?" label, `NormalProofReachable` is maintained.

    This is the key theorem that makes `h_reach` automatically maintainable:
    each successful `feedProof` call in normal mode extends the ghost array by one step.

    **Preconditions**: `h_not_q` excludes "?" (incomplete proof steps).
    A theorem about complete normal proofs should never encounter "?". -/
theorem feedProof_normal_maintains_reachable
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_success : (s.feedProof tk pr).db.error? = none)
    (h_normal : pr.ptp = .normal)
    (h_not_q : ¬ tk.eqArray "?".toAscii)
    (h_reach : NormalProofReachable s.db pr.label pr.fmla pr.stack) :
    ∃ pr_mid,
      (s.feedProof tk pr).tokp = .proof pr_mid ∧
      pr_mid.label = pr.label ∧
      pr_mid.fmla = pr.fmla ∧
      pr_mid.frame = pr.frame ∧
      pr_mid.ptp = ProofTokenParser.normal ∧
      NormalProofReachable s.db pr.label pr.fmla pr_mid.stack := by
  -- Step 1: Extract go result from feedProof via withAt
  unfold ParserState.feedProof at h_success ⊢
  have h_inner := withAt_success_eq pr.label
    (fun _ =>
      match ParserState.feedProof.go s tk pr with
      | .ok pr' => { s with tokp := .proof pr' }
      | .error msg => s.mkErrorFromEvidence pr.pos msg.evidence) h_success
  rcases h_inner with ⟨h_inner_ok, _h_inner_eq⟩
  -- Step 2: go succeeds → extract pr'
  cases h_go : ParserState.feedProof.go s tk pr with
  | error msg =>
    -- Error branch: contradicts h_inner_ok
    have h_bad : (s.mkErrorFromEvidence pr.pos msg.evidence).db.error? ≠ none := by
      simp [ParserState.mkErrorFromEvidence, ParserState.withDB]
    have : (s.mkErrorFromEvidence pr.pos msg.evidence).db.error? = none := by
      simpa [h_go] using h_inner_ok
    exact (h_bad this).elim
  | ok pr' =>
    -- Success: feedProof returns { s with tokp := .proof pr' }
    -- Step 3: In normal mode, go = goNormal
    have h_goNormal : ParserState.feedProof.goNormal s tk pr = .ok pr' := by
      rw [← go_normal_eq_goNormal s tk pr h_normal]; exact h_go
    -- Step 4: Extract stepNormal call
    have h_step := goNormal_extracts_stepNormal s tk pr pr' h_goNormal h_not_q
    -- Step 5: Core field preservation from goNormal
    have h_core := feedProof_goNormal_ok_preserves_core s tk pr pr' h_goNormal
    -- Step 6: Apply NormalProofReachable_step
    have h_reach' := NormalProofReachable_step s.db pr.label pr.fmla pr pr'
      (toLabel tk).2 h_reach h_step
    -- Step 7: ptp preservation
    have h_ptp : pr'.ptp = ProofTokenParser.normal :=
      (stepNormal_preserves_ptp s.db pr pr' (toLabel tk).2 h_step).trans h_normal
    -- Step 8: Package the result
    refine ⟨pr', ?_, ?_, h_core.1, h_core.2, h_ptp, ?_⟩
    · -- tokp = .proof pr'
      unfold ParserState.withAt
      have h_no_err : s.db.error? = none := by simpa [h_go] using h_inner_ok
      simp [h_no_err]
    · -- pr'.label = pr.label: stepNormal only modifies stack
      exact stepNormal_preserves_label s.db pr pr' (toLabel tk).2 h_step
    · -- NormalProofReachable maintained
      exact h_reach'

/-! ## Part 9: Start-to-Normal Bridge & Multi-Step Composition

The first feedProof call with `pr.ptp = .start` and `tk ≠ "("` transitions to
normal mode via `goNormal { pr with ptp := .normal }`. Combined with
`NormalProofReachable_init`, this establishes the base case. Subsequent calls
maintain reachability via Part 8. The multi-step theorem composes everything. -/

/-- In `.start` mode with a non-"(" token, `go` delegates to `goNormal` on the .normal variant. -/
private theorem go_start_eq_goNormal
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_start : pr.ptp = .start) (h_not_open : ¬ tk.eqArray "(".toAscii) :
    ParserState.feedProof.go s tk pr =
      ParserState.feedProof.goNormal s tk { pr with ptp := .normal } := by
  unfold ParserState.feedProof.go
  simp [h_start, h_not_open]

set_option maxHeartbeats 6400000 in
/-- **First-token bridge**: When `feedProof` is called with `.start` ptp and
    a non-"(" non-"?" token, it transitions to `.normal` mode and establishes
    `NormalProofReachable` from scratch.

    Combined with `NormalProofReachable_init` (empty stack is reachable)
    and `NormalProofReachable_step`, this gives the base case for multi-step
    reachability induction. -/
theorem feedProof_start_establishes_reachable
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_success : (s.feedProof tk pr).db.error? = none)
    (h_start : pr.ptp = .start)
    (h_not_open : ¬ tk.eqArray "(".toAscii)
    (h_not_q : ¬ tk.eqArray "?".toAscii)
    (h_stack_empty : pr.stack = #[]) :
    ∃ pr_mid,
      (s.feedProof tk pr).tokp = .proof pr_mid ∧
      pr_mid.label = pr.label ∧
      pr_mid.fmla = pr.fmla ∧
      pr_mid.frame = pr.frame ∧
      pr_mid.ptp = ProofTokenParser.normal ∧
      NormalProofReachable s.db pr.label pr.fmla pr_mid.stack := by
  -- Step 1: Extract go result from feedProof via withAt
  unfold ParserState.feedProof at h_success ⊢
  have h_inner := withAt_success_eq pr.label
    (fun _ =>
      match ParserState.feedProof.go s tk pr with
      | .ok pr' => { s with tokp := .proof pr' }
      | .error msg => s.mkErrorFromEvidence pr.pos msg.evidence) h_success
  rcases h_inner with ⟨h_inner_ok, _h_inner_eq⟩
  -- Step 2: go = goNormal { pr with ptp := .normal } in start mode
  have h_start_go := go_start_eq_goNormal s tk pr h_start h_not_open
  -- Step 3: go succeeds → extract pr'
  cases h_go : ParserState.feedProof.go s tk pr with
  | error msg =>
    have h_bad : (s.mkErrorFromEvidence pr.pos msg.evidence).db.error? ≠ none := by
      simp [ParserState.mkErrorFromEvidence, ParserState.withDB]
    have : (s.mkErrorFromEvidence pr.pos msg.evidence).db.error? = none := by
      simpa [h_go] using h_inner_ok
    exact (h_bad this).elim
  | ok pr' =>
    -- Step 4: goNormal succeeded on { pr with ptp := .normal }
    have h_goNormal : ParserState.feedProof.goNormal s tk { pr with ptp := .normal } = .ok pr' := by
      rw [← h_start_go]; exact h_go
    -- Step 5: Extract stepNormal from goNormal
    have h_step := goNormal_extracts_stepNormal s tk { pr with ptp := .normal } pr' h_goNormal h_not_q
    -- Step 6: Core field preservation
    have h_core := feedProof_goNormal_ok_preserves_core s tk { pr with ptp := .normal } pr' h_goNormal
    -- Step 7: ptp preservation through stepNormal
    have h_ptp : pr'.ptp = ProofTokenParser.normal :=
      stepNormal_preserves_ptp s.db { pr with ptp := .normal } pr' (toLabel tk).2 h_step
    -- Step 8: NormalProofReachable base case + step
    have h_reach_init : NormalProofReachable s.db pr.label pr.fmla pr.stack := by
      rw [h_stack_empty]; exact NormalProofReachable_init s.db pr.label pr.fmla
    have h_reach' := NormalProofReachable_step s.db pr.label pr.fmla
      { pr with ptp := .normal } pr' (toLabel tk).2
      (by simpa using h_reach_init) h_step
    -- Step 9: Package result
    refine ⟨pr', ?_, ?_, h_core.1.symm ▸ rfl, h_core.2.symm ▸ rfl, h_ptp, h_reach'⟩
    · -- tokp = .proof pr'
      unfold ParserState.withAt
      have h_no_err : s.db.error? = none := by simpa [h_go] using h_inner_ok
      simp [h_no_err]
    · -- pr'.label = pr.label
      exact stepNormal_preserves_label s.db { pr with ptp := .normal } pr' (toLabel tk).2 h_step

/-! ### Part 9b: Multi-Step Composition

Model a sequence of successful feedProof calls in normal mode and prove
that `NormalProofReachable` is maintained throughout. -/

/-- A sequence of successful feedProof calls in normal mode with non-"?" tokens.
    Each step requires feedProof success, normal ptp, and non-"?" token. -/
def NormalTokensOK (s : ParserState) : ProofState → List ByteSlice → ProofState → Prop
  | pr, [], pr_final => pr_final = pr
  | pr, tk :: rest, pr_final =>
    ∃ pr_mid,
      (s.feedProof tk pr).db.error? = none ∧
      (s.feedProof tk pr).tokp = .proof pr_mid ∧
      pr.ptp = ProofTokenParser.normal ∧
      ¬ tk.eqArray "?".toAscii ∧
      NormalTokensOK s pr_mid rest pr_final

/-- Multi-step invariant: `NormalTokensOK` preserves `NormalProofReachable`
    and all ProofState fields except stack. -/
theorem NormalTokensOK_preserves_invariant
    (s : ParserState) (tokens : List ByteSlice)
    (pr₀ pr_final : ProofState)
    (h_tokens : NormalTokensOK s pr₀ tokens pr_final)
    (h_reach : NormalProofReachable s.db pr₀.label pr₀.fmla pr₀.stack)
    (h_normal : pr₀.ptp = ProofTokenParser.normal) :
    NormalProofReachable s.db pr_final.label pr_final.fmla pr_final.stack ∧
    pr_final.label = pr₀.label ∧
    pr_final.fmla = pr₀.fmla ∧
    pr_final.frame = pr₀.frame ∧
    pr_final.ptp = ProofTokenParser.normal := by
  induction tokens generalizing pr₀ with
  | nil =>
    -- Base: pr_final = pr₀
    unfold NormalTokensOK at h_tokens
    subst h_tokens
    exact ⟨h_reach, rfl, rfl, rfl, h_normal⟩
  | cons tk rest ih =>
    -- Step: extract pr_mid from NormalTokensOK
    unfold NormalTokensOK at h_tokens
    obtain ⟨pr_mid, h_succ, h_tokp, h_ptp, h_not_q, h_rest⟩ := h_tokens
    -- Apply feedProof_normal_maintains_reachable
    obtain ⟨pr_mid', h_tokp', h_label', h_fmla', h_frame', h_ptp', h_reach'⟩ :=
      feedProof_normal_maintains_reachable s tk pr₀ h_succ h_ptp h_not_q h_reach
    -- pr_mid' = pr_mid (from tokp equality)
    have h_eq : pr_mid = pr_mid' := by
      have : (s.feedProof tk pr₀).tokp = .proof pr_mid' := h_tokp'
      rw [h_tokp] at this
      exact TokenParser.proof.inj this
    subst h_eq
    -- Rewrite label/fmla to match pr_mid (they're preserved by feedProof)
    rw [← h_label', ← h_fmla'] at h_reach'
    -- Apply IH
    have ih_result := ih pr_mid h_rest h_reach' h_ptp'
    exact ⟨ih_result.1,
      ih_result.2.1.trans h_label',
      ih_result.2.2.1.trans h_fmla',
      ih_result.2.2.2.1.trans h_frame',
      ih_result.2.2.2.2⟩

/-! ### Part 9c: End-to-End Normal Proof Provenance

The final theorem: starting from `resumeThm` (`.start`, empty stack),
processing the first token (`.start` → `.normal`) and then a list of tokens
in normal mode, finishing with `finishProof` — prefix provability holds
with NO `h_reach` assumption. -/

/-- **END-TO-END** normal proof provenance: h_reach AND h_hyp_disjoint derived, not assumed.

    Starting from `.start` ptp with empty stack, the first non-"(" token
    establishes `NormalProofReachable`, subsequent tokens maintain it,
    and `prefix_provable_normal_proof` gives prefix provability.

    `h_hyp_disjoint` is derived from `WellFormedDB` + label freshness
    (via `hyp_disjoint_of_fresh` + `finishProof_prefix_characterization`). -/
theorem normal_proof_full_provenance
    (s : ParserState) (tk₀ : ByteSlice) (tokens : List ByteSlice)
    (pr₀ pr₁ pr_final : ProofState)
    -- Initial ProofState from resumeThm
    (h_init_stack : pr₀.stack = #[])
    (h_init_start : pr₀.ptp = ProofTokenParser.start)
    -- First token: non-"(", non-"?"
    (h_first_ok : (s.feedProof tk₀ pr₀).db.error? = none)
    (h_first_not_open : ¬ tk₀.eqArray "(".toAscii)
    (h_first_not_q : ¬ tk₀.eqArray "?".toAscii)
    (h_first_tokp : (s.feedProof tk₀ pr₀).tokp = .proof pr₁)
    -- Subsequent tokens
    (h_tokens : NormalTokensOK s pr₁ tokens pr_final)
    -- finishProof success + DB conditions
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
  -- Step 1: First token establishes NormalProofReachable
  obtain ⟨pr₁', h_tokp₁, h_label₁, h_fmla₁, h_frame₁, h_ptp₁, h_reach₁⟩ :=
    feedProof_start_establishes_reachable s tk₀ pr₀
      h_first_ok h_init_start h_first_not_open h_first_not_q h_init_stack
  -- pr₁ = pr₁'
  have h_eq₁ : pr₁ = pr₁' := by
    rw [h_first_tokp] at h_tokp₁
    exact TokenParser.proof.inj h_tokp₁
  subst h_eq₁
  -- Rewrite label/fmla to match pr₁ (they're preserved by first feedProof)
  rw [← h_label₁, ← h_fmla₁] at h_reach₁
  -- Step 2: Multi-step maintains invariant
  obtain ⟨h_reach_final, h_label_final, h_fmla_final, h_frame_final, _h_ptp_final⟩ :=
    NormalTokensOK_preserves_invariant s tokens pr₁ pr_final h_tokens
      h_reach₁ h_ptp₁
  -- Step 3: Apply prefix_provable_normal_proof (h_hyp_disjoint now derived internally)
  exact prefix_provable_normal_proof s pr_final h_finish h_s_ok h_wf
    h_reach_final h_stack_one h_stack_fmla

/-! ## Part 10: Compressed Proof Provenance

For compressed proofs, the parser flow is:
1. `.start` + "(" → `preloadMandatoryHyps` → `.preload`
2. `.preload` + labels → `db.preload pr label` (fills heap)
3. `.preload` + ")" → `.compressed 0`
4. `.compressed` + tokens → `decodeCompressed` → `applyCompressedActions` (step/save/unknown)
5. `finishProof` with `.compressed 0` → validate stack, insert

**Architecture:** Rather than tracing through every compressed token, we define
`CompressedProofReachable` (the save-free model from `compressed_proof_sound`)
and show it implies `NormalProofReachable`. Then `prefix_provable_normal_proof`
gives prefix provability — the same path as normal proofs.

This handles the save-free case. Save support (Z actions that extend the heap
during execution) is documented as future work — saves are an optimization that
can be "inlined" by repeating the original labels, but proving this formally
requires a save-unrolling lemma. -/

/-! ### Part 10a: Preload Stack Preservation

`preload` and `preloadMandatoryHyps` use `pushHeap`, which only modifies the heap.
The stack is untouched. -/

/-- `preload` preserves the stack (it only modifies the heap via `pushHeap`). -/
theorem preload_preserves_stack (db : DB) (pr pr' : ProofState) (label : String)
    (h_ok : db.preload pr label = .ok pr') :
    pr'.stack = pr.stack := by
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
    | assert f fr _ =>
      simp at h_ok; cases h_ok; rfl

/-- `preload` fold preserves the stack. -/
theorem preload_fold_preserves_stack (db : DB) (labels : List String)
    (pr_init pr_final : ProofState)
    (h_fold : labels.foldlM (DB.preload db) pr_init = .ok pr_final) :
    pr_final.stack = pr_init.stack := by
  induction labels generalizing pr_init with
  | nil =>
    simp [List.foldlM] at h_fold; cases h_fold; rfl
  | cons l rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_fold
    cases h_step : DB.preload db pr_init l with
    | error e => rw [h_step] at h_fold; exact absurd h_fold nofun
    | ok mid =>
      rw [h_step] at h_fold
      rw [ih mid h_fold, preload_preserves_stack db pr_init mid l h_step]

/-! ### Part 10b: CompressedProofReachable

The save-free compressed execution model: preload labels into heap, then
execute step indices via `stepProof`. This matches `compressed_proof_sound`'s
hypotheses exactly. -/

/-- A proof stack is reachable via compressed execution if there exist
    preload labels and step indices such that:
    1. Preloading succeeds from canonical init
    2. Executing step indices via `stepProof` succeeds
    3. The final stack matches

    This captures the save-free compressed proof model. -/
def CompressedProofReachable (db : DB) (label : String) (fmla : Formula)
    (stack : Array Formula) : Prop :=
  ∃ (labels : List String) (steps : List Nat)
    (pr_preload pr_final : ProofState),
    labels.foldlM (DB.preload db)
      ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], ProofTokenParser.normal⟩ = .ok pr_preload ∧
    steps.foldlM (fun pr n => DB.stepProof db pr n) pr_preload = .ok pr_final ∧
    pr_final.stack = stack

/-! ### Part 10c: Compressed → Normal Reachability Bridge

The key bridge: `compressed_proof_sound` converts the `stepProof` fold to a
`stepNormal` fold (from `pr_preload`), and `foldlM_stepNormal_transfer` moves
the starting point to canonical init (since `pr_preload` has the same stack
and frame as canonical init). -/

/-- Compressed proof reachability implies normal proof reachability.

    Uses:
    - `compressed_proof_sound`: stepProof fold → stepNormal fold
    - `preload_fold_preserves_stack/frame`: pr_preload has same stack/frame as init
    - `foldlM_stepNormal_transfer`: transfers fold to canonical init -/
theorem compressed_to_normal_reachable (db : DB) (label : String) (fmla : Formula)
    (stack : Array Formula)
    (h_wf : WellFormedDB db)
    (h_reach : CompressedProofReachable db label fmla stack) :
    NormalProofReachable db label fmla stack := by
  obtain ⟨labels, steps, pr_preload, pr_final, h_preload, h_steps, h_stack⟩ := h_reach
  -- Canonical init
  let pr_init : ProofState := ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .normal⟩
  -- Extract Γ and fr (needed by compressed_proof_sound)
  have h_db : ∃ Γ, toDatabase db = some Γ := by unfold toDatabase; exact ⟨_, rfl⟩
  obtain ⟨Γ, h_db⟩ := h_db
  have h_fr : ∃ fr, toFrame db db.frame = some fr := toFrame_some_of_wfFrame db h_wf.1
  obtain ⟨fr, h_fr⟩ := h_fr
  -- Apply compressed_proof_sound: stepProof fold → stepNormal fold
  have h_normal_fold :
      (steps.map (fun n => labels[n]!)).foldlM
        (fun pr lbl => DB.stepNormal db pr lbl) pr_preload = .ok pr_final :=
    compressed_proof_sound db pr_init pr_preload pr_final labels steps Γ fr
      h_db h_fr h_wf.1 rfl h_preload h_steps
  -- pr_preload has same stack and frame as pr_init
  have h_preload_stack : pr_preload.stack = pr_init.stack :=
    preload_fold_preserves_stack db labels pr_init pr_preload h_preload
  have h_preload_frame : pr_preload.frame = pr_init.frame :=
    preload_fold_preserves_frame db labels pr_init pr_preload h_preload
  -- Transfer fold from pr_preload to pr_init (canonical init)
  obtain ⟨r₂, h_fold₂, h_r₂_stack⟩ :=
    foldlM_stepNormal_transfer db (steps.map (fun n => labels[n]!))
      pr_preload pr_init pr_final
      h_preload_stack h_normal_fold
  -- Build NormalProofReachable: proof array is (steps.map labels[·]!).toArray
  rw [← h_stack, ← h_r₂_stack]
  refine ⟨(steps.map (fun n => labels[n]!)).toArray, r₂, ?_, rfl⟩
  -- Convert Array.foldlM → List.foldlM, then simplify toArray.toList
  rw [← Array.foldlM_toList, List.toList_toArray]
  exact h_fold₂

/-! ### Part 10d: Prefix Provability for Compressed Proofs -/

/-- **MAIN THEOREM (compressed proofs)**: Prefix provability for save-free
    compressed proofs.

    Composes `compressed_to_normal_reachable` + `prefix_provable_normal_proof`.
    The only assumption about the proof execution is `CompressedProofReachable`,
    which captures the save-free compressed proof model.

    **Coverage:** Handles compressed proofs without Z (save) actions.
    Save support is future work (requires save-unrolling lemma). -/
theorem prefix_provable_compressed_proof
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db)
    (h_reach : CompressedProofReachable s.db pr.label pr.fmla pr.stack)
    (h_stack_one : pr.stack.size = 1)
    (h_stack_fmla : pr.stack[0]? = some pr.fmla) :
    ∃ (Γ_final : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase (s.finishProof pr).db = some Γ_final ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ_final spec_fr (toExpr pr.fmla) := by
  exact prefix_provable_normal_proof s pr h_success h_s_ok h_wf
    (compressed_to_normal_reachable s.db pr.label pr.fmla pr.stack h_wf h_reach)
    h_stack_one h_stack_fmla

/-! ## Part 11: Unified Dispatcher + Audit Anchor

Dispatches on proof mode to give a single theorem covering both normal and
compressed proofs. The proof mode is determined by the `ProofTokenParser`
field of the final `ProofState`. -/

/-- Proof execution mode at finishProof: either normal or compressed (save-free). -/
inductive ProofReachable (db : DB) (label : String) (fmla : Formula)
    (stack : Array Formula) : Prop where
  | normal : NormalProofReachable db label fmla stack → ProofReachable db label fmla stack
  | compressed : CompressedProofReachable db label fmla stack → ProofReachable db label fmla stack

/-- **UNIFIED THEOREM**: Prefix provability for any reachable proof execution.

    Whether the proof was checked in normal mode or compressed mode (save-free),
    the resulting theorem is provable from the prefix database.

    This is the audit anchor: any theorem inserted by the Metamath verifier
    satisfies `Spec.Provable` against the database state BEFORE insertion. -/
theorem prefix_provable_any_proof
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db)
    (h_reach : ProofReachable s.db pr.label pr.fmla pr.stack)
    (h_stack_one : pr.stack.size = 1)
    (h_stack_fmla : pr.stack[0]? = some pr.fmla) :
    ∃ (Γ_final : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase (s.finishProof pr).db = some Γ_final ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ_final spec_fr (toExpr pr.fmla) := by
  cases h_reach with
  | normal h =>
    exact prefix_provable_normal_proof s pr h_success h_s_ok h_wf h h_stack_one h_stack_fmla
  | compressed h =>
    exact prefix_provable_compressed_proof s pr h_success h_s_ok h_wf h h_stack_one h_stack_fmla

/-! ## Part 12: Stack Extension for stepAssert / stepNormal

The key enabler for Z save support: if `stepNormal` succeeds with stack `args`,
it also succeeds with stack `base ++ args`, and the result has `base` prepended.
This allows derivation "replay" from any stack state.

**Architecture:**
1. `checkHyp_prepend`: checkHyp reads the same values from `base ++ args` with offset
   `base.size` as from `args` with offset 0, so it produces the same substitution.
2. `stepAssert_prepend`: Uses (1) plus array shrink/push lemmas.
3. `stepNormal_prepend`: Wraps (2) for asserts, trivial for hyps.
-/

/-- Array index equality: `(base ++ args)[base.size + i]! = args[i]!` when `i < args.size`. -/
private theorem prepend_val_eq (base args : Array Formula) (i : Nat) (h : i < args.size) :
    (base ++ args)[base.size + i]! = args[i]! := by
  have h1 : base.size + i < (base ++ args).size := by simp; omega
  rw [getElem!_pos (base ++ args) (base.size + i) h1,
      getElem!_pos args i h,
      Array.getElem_append_right (show base.size ≤ base.size + i from Nat.le_add_right _ _)]
  congr 1; omega

set_option maxHeartbeats 6400000 in
/-- `checkHyp` with a prepended base array produces the same result as without it.
    This is because `checkHyp` reads `stack[off + i]` where `off = base.size` for the
    extended stack and `off = 0` for the original, hitting the same elements. -/
theorem checkHyp_prepend
    (db : DB) (hyps : Array String) (base args : Array Formula)
    (h_eq : args.size = hyps.size) :
    ∀ n i σ, n = hyps.size - i →
    db.checkHyp hyps (base ++ args) ⟨base.size, by simp; omega⟩ i σ =
    db.checkHyp hyps args ⟨0, by omega⟩ i σ := by
  intro n
  induction n with
  | zero =>
    intro i σ h_n
    have h_ge : ¬ i < hyps.size := by omega
    rw [DB.checkHyp_base _ _ _ _ _ _ h_ge, DB.checkHyp_base _ _ _ _ _ _ h_ge]
  | succ m ih =>
    intro i σ h_n
    have h_lt : i < hyps.size := by omega
    -- Panicking-access equality (for equation lemma RHS terms)
    have h_val_eq : (base ++ args)[base.size + i]! = args[0 + i]! := by
      simp only [Nat.zero_add]
      exact prepend_val_eq base args i (by omega)
    -- Safe-access equality (for goals after checkHyp unfold)
    have h_safe_eq : (base ++ args)[base.size + i]'(by simp; omega) =
                     args[(0 : Nat) + i]'(by omega) := by
      rw [Array.getElem_append_right (show base.size ≤ base.size + i from Nat.le_add_right _ _)]
      congr 1; omega
    cases h_find : db.find? hyps[i] with
    | none =>
      unfold DB.checkHyp
      simp only [h_lt, ↓reduceDIte, h_find, h_safe_eq]
    | some obj =>
      cases obj with
      | hyp ess f lbl =>
        cases ess with
        | true =>
          rw [DB.checkHyp_step_hyp_true _ _ _ _ _ _ _ _ h_lt h_find,
              DB.checkHyp_step_hyp_true _ _ _ _ _ _ _ _ h_lt h_find]
          simp only [h_val_eq]
          split -- !args[0+i]!.hasConstHead
          · rfl
          · split -- !f.hasConstHead
            · rfl
            · split -- !formulaSymsRespectFrame
              · rfl
              · split -- f[0]! == args[0+i]![0]!
                · split -- match f.subst σ
                  · split -- s == args[0+i]!
                    · exact ih (i + 1) σ (by omega)
                    · rfl
                  · rfl
                · rfl
        | false =>
          rw [DB.checkHyp_step_hyp_false _ _ _ _ _ _ _ _ h_lt h_find,
              DB.checkHyp_step_hyp_false _ _ _ _ _ _ _ _ h_lt h_find]
          simp only [h_val_eq]
          split -- !args[0+i]!.hasConstHead
          · rfl
          · split -- !f.isFloatShape
            · rfl
            · split -- f[0]! == args[0+i]![0]!
              · split -- σ.contains f[1]!.value
                · rfl
                · exact ih (i+1) (σ.insert f[1]!.value args[0+i]!) (by omega)
              · rfl
      | const _ | var _ | assert _ _ _ =>
        unfold DB.checkHyp
        simp only [h_lt, ↓reduceDIte, h_find, h_safe_eq]

set_option maxHeartbeats 6400000 in
/-- stepAssert with a prepended base array produces `.ok` with base prepended to result stack.

    If `stepAssert db pr f ⟨dj, hyps⟩ = .ok result` with `pr.stack.size = hyps.size`,
    then `stepAssert db {pr with stack := base ++ pr.stack} f ⟨dj, hyps⟩`
    `= .ok {result with stack := base ++ result.stack}`.

    This is the core stack extension property for derivation replay. -/
theorem stepAssert_prepend_stack
    (db : DB) (pr : ProofState) (f : Formula) (fr : Frame)
    (base : Array Formula) (result : ProofState)
    (h_eq : pr.stack.size = fr.hyps.size)
    (h_ok : db.stepAssert pr f fr = .ok result) :
    db.stepAssert {pr with stack := base ++ pr.stack} f fr =
      .ok {result with stack := base ++ result.stack} := by
  obtain ⟨dj, hyps⟩ := fr
  simp only at h_eq  -- reduce fr.hyps to hyps
  rw [DB.stepAssert.eq_1] at h_ok ⊢
  have h_le : hyps.size ≤ pr.stack.size := by omega
  have h_le_ext : hyps.size ≤ (base ++ pr.stack).size := by simp; omega
  have h_ext_off : (base ++ pr.stack).size - hyps.size = base.size := by simp; omega
  have h_orig_off : pr.stack.size - hyps.size = 0 := by omega
  simp only [h_le, h_le_ext, ↓reduceDIte, h_ext_off, h_orig_off] at h_ok ⊢
  rw [checkHyp_prepend db hyps base pr.stack h_eq hyps.size 0 ∅ rfl]
  simp only [show (base ++ pr.stack).shrink base.size = base from by
               ext i h <;> simp,
             show pr.stack.shrink 0 = (#[] : Array Formula) from by
               ext i h <;> simp] at h_ok ⊢
  split
  · rename_i h_c; simp [h_c, throw] at h_ok
  · rename_i h_c1; split
    · rename_i h_c; simp [h_c1, h_c, throw] at h_ok
    · rename_i h_c2
      simp only [h_c1, h_c2, ↓reduceIte, Bool.false_eq_true] at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok ⊢
      cases h_chk : DB.checkHyp db hyps pr.stack ⟨0, by omega⟩ 0 ∅ with
      | error e => simp [h_chk] at h_ok
      | ok subst =>
        simp only [h_chk] at h_ok ⊢
        cases h_dv : DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj dj subst with
        | error e => simp [h_dv] at h_ok
        | ok u =>
          simp only [h_dv] at h_ok ⊢
          cases h_sub : Verify.Formula.subst subst f with
          | error e => simp [h_sub] at h_ok
          | ok concl =>
            simp only [h_sub, Except.ok.injEq] at h_ok ⊢
            subst h_ok
            rfl

/-- Shrink distributes over append: `(base ++ stack).shrink (base.size + off) = base ++ stack.shrink off`. -/
private theorem shrink_append_prepend (base stack : Array Formula) (off : Nat) :
    (base ++ stack).shrink (base.size + off) = base ++ stack.shrink off := by
  apply Array.toList_inj.mp
  simp only [Array.toList_shrink, Array.toList_append, List.take_append]
  have h1 : base.toList.length = base.size := by simp
  rw [List.take_of_length_le (by omega : base.toList.length ≤ base.size + off)]
  congr 1
  show List.take (base.size + off - base.toList.length) stack.toList = List.take off stack.toList
  rw [h1]; simp [Nat.add_sub_cancel_left]

set_option maxHeartbeats 6400000 in
/-- General-offset `checkHyp` prepend: reading from `base ++ stack` at offset `base.size + off`
    is the same as reading from `stack` at offset `off`. This generalizes `checkHyp_prepend`
    (which is the special case `off = 0`). -/
theorem checkHyp_prepend_general
    (db : DB) (hyps : Array String) (base stack : Array Formula)
    (off : Nat) (h_off : off + hyps.size = stack.size) :
    ∀ n i σ, n = hyps.size - i →
    db.checkHyp hyps (base ++ stack) ⟨base.size + off, by simp; omega⟩ i σ =
    db.checkHyp hyps stack ⟨off, h_off⟩ i σ := by
  intro n
  induction n with
  | zero =>
    intro i σ h_n
    have h_ge : ¬ i < hyps.size := by omega
    rw [DB.checkHyp_base _ _ _ _ _ _ h_ge, DB.checkHyp_base _ _ _ _ _ _ h_ge]
  | succ m ih =>
    intro i σ h_n
    have h_lt : i < hyps.size := by omega
    have h_val_eq : (base ++ stack)[base.size + off + i]! = stack[off + i]! := by
      have h1 : base.size + off + i < (base ++ stack).size := by simp; omega
      rw [getElem!_pos (base ++ stack) _ h1, getElem!_pos stack _ (by omega),
          Array.getElem_append_right (show base.size ≤ base.size + off + i from by omega)]
      congr 1; omega
    have h_safe_eq : (base ++ stack)[(base.size + off) + i]'(by simp; omega) =
                     stack[off + i]'(by omega) := by
      rw [Array.getElem_append_right (show base.size ≤ (base.size + off) + i from by omega)]
      congr 1; omega
    cases h_find : db.find? hyps[i] with
    | none => unfold DB.checkHyp; simp only [h_lt, ↓reduceDIte, h_find, h_safe_eq]
    | some obj =>
      cases obj with
      | hyp ess f lbl =>
        cases ess with
        | true =>
          rw [DB.checkHyp_step_hyp_true _ _ _ _ _ _ _ _ h_lt h_find,
              DB.checkHyp_step_hyp_true _ _ _ _ _ _ _ _ h_lt h_find]
          -- After equation lemmas, both sides differ only in array values and recursive call.
          -- Rewrite values and recursive call to make both sides identical.
          simp only [h_val_eq, ih (i+1) σ (by omega)]
        | false =>
          rw [DB.checkHyp_step_hyp_false _ _ _ _ _ _ _ _ h_lt h_find,
              DB.checkHyp_step_hyp_false _ _ _ _ _ _ _ _ h_lt h_find]
          simp only [h_val_eq, ih (i+1) (σ.insert f[1]!.value stack[off+i]!) (by omega)]
      | const _ | var _ | assert _ _ _ =>
        unfold DB.checkHyp; simp only [h_lt, ↓reduceDIte, h_find, h_safe_eq]

set_option maxHeartbeats 6400000 in
/-- General stack prepend for stepAssert: if `stepAssert` succeeds with stack having
    at least `hyps.size` elements, then prepending `base` to the stack gives `.ok`
    with `base` prepended to the result stack.

    This generalizes `stepAssert_prepend_stack` (which requires `stack.size = hyps.size`). -/
theorem stepAssert_prepend_stack_le
    (db : DB) (pr : ProofState) (f : Formula) (fr : Frame)
    (base : Array Formula) (result : ProofState)
    (h_le : fr.hyps.size ≤ pr.stack.size)
    (h_ok : db.stepAssert pr f fr = .ok result) :
    db.stepAssert {pr with stack := base ++ pr.stack} f fr =
      .ok {result with stack := base ++ result.stack} := by
  obtain ⟨dj, hyps⟩ := fr
  simp only at h_le
  rw [DB.stepAssert.eq_1] at h_ok ⊢
  have h_le_ext : hyps.size ≤ (base ++ pr.stack).size := by simp; omega
  have h_off : (pr.stack.size - hyps.size) + hyps.size = pr.stack.size := Nat.sub_add_cancel h_le
  have h_ext_off : (base ++ pr.stack).size - hyps.size = base.size + (pr.stack.size - hyps.size) := by
    simp; omega
  simp only [h_le, h_le_ext, ↓reduceDIte, h_ext_off] at h_ok ⊢
  rw [checkHyp_prepend_general db hyps base pr.stack (pr.stack.size - hyps.size) h_off
        hyps.size 0 ∅ rfl]
  rw [shrink_append_prepend base pr.stack (pr.stack.size - hyps.size)]
  split
  · rename_i h_c; simp [h_c, throw] at h_ok
  · rename_i h_c1; split
    · rename_i h_c; simp [h_c1, h_c, throw] at h_ok
    · rename_i h_c2
      simp only [h_c1, h_c2, ↓reduceIte, Bool.false_eq_true] at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok ⊢
      cases h_chk : DB.checkHyp db hyps pr.stack ⟨pr.stack.size - hyps.size, h_off⟩ 0 ∅ with
      | error e => simp [h_chk] at h_ok
      | ok subst =>
        simp only [h_chk] at h_ok ⊢
        cases h_dv : DB.dvCheck (db.frameFloatVars db.frame) db.frame.dj dj subst with
        | error e => simp [h_dv] at h_ok
        | ok u =>
          simp only [h_dv] at h_ok ⊢
          cases h_sub : Verify.Formula.subst subst f with
          | error e => simp [h_sub] at h_ok
          | ok concl =>
            simp only [h_sub, Except.ok.injEq] at h_ok ⊢
            subst h_ok
            simp only [Array.push_eq_append, Array.append_assoc]

/-- If `stepAssert` succeeds, then `fr.hyps.size ≤ pr.stack.size`. -/
private theorem stepAssert_ok_implies_le
    (db : DB) (pr : ProofState) (f : Formula) (fr : Frame) (result : ProofState)
    (h_ok : db.stepAssert pr f fr = .ok result) :
    fr.hyps.size ≤ pr.stack.size := by
  obtain ⟨dj, hyps⟩ := fr
  rw [DB.stepAssert.eq_1] at h_ok
  split at h_ok
  · assumption
  · exact absurd h_ok nofun

set_option maxHeartbeats 6400000 in
/-- **Stack prepend for stepNormal**: if `stepNormal` succeeds with stack `args`,
    it succeeds with `base ++ args` and the result has `base` prepended.

    - **Hyp case**: `push` distributes over append (trivial).
    - **Assert case**: delegates to `stepAssert_prepend_stack_le`. -/
theorem stepNormal_prepend_stack
    (db : DB) (pr : ProofState) (l : String)
    (base : Array Formula) (result : ProofState)
    (h_ok : db.stepNormal pr l = .ok result) :
    db.stepNormal {pr with stack := base ++ pr.stack} l =
      .ok {result with stack := base ++ result.stack} := by
  unfold DB.stepNormal at h_ok ⊢
  cases h_find : db.find? l with
  | none => simp [h_find] at h_ok
  | some obj =>
    simp only [h_find] at h_ok ⊢
    cases obj with
    | const _ => simp at h_ok
    | var _ => simp at h_ok
    | hyp ess f' lbl =>
      by_cases h_mem : l ∈ db.frame.hyps.toList
      · simp only [h_mem, ↓reduceIte] at h_ok ⊢
        cases ess with
        | true =>
          simp only [↓reduceIte] at h_ok ⊢
          -- Guard: if !f'.hasConstHead then throw else return push
          cases h_head : f'.hasConstHead
          · -- hasConstHead = false → !false = true → throw → contradiction
            simp [h_head] at h_ok
          · -- hasConstHead = true → !true = false → return push
            simp [h_head, pure, Except.pure, Except.ok.injEq] at h_ok ⊢
            subst h_ok
            simp only [ProofState.push, Array.push_eq_append, Array.append_assoc]
        | false =>
          simp only [Bool.false_eq_true, ite_false] at h_ok ⊢
          -- Guard: if !f'.isFloatShape then throw else return push
          cases h_float : f'.isFloatShape
          · -- isFloatShape = false → throw → contradiction
            simp [h_float] at h_ok
          · -- isFloatShape = true → return push
            simp [h_float, pure, Except.pure, Except.ok.injEq] at h_ok ⊢
            subst h_ok
            simp only [ProofState.push, Array.push_eq_append, Array.append_assoc]
      · simp [h_mem] at h_ok
    | assert f' fr' origin =>
      exact stepAssert_prepend_stack_le db pr f' fr' base result
        (stepAssert_ok_implies_le db pr f' fr' result h_ok) h_ok

/-- Lift `stepNormal_prepend_stack` to `foldlM`: if the fold succeeds with stack,
    it succeeds with `base` prepended throughout. -/
theorem foldlM_stepNormal_prepend
    (db : DB) (labels : List String) (pr result : ProofState)
    (base : Array Formula)
    (h_ok : labels.foldlM (fun p l => db.stepNormal p l) pr = .ok result) :
    labels.foldlM (fun p l => db.stepNormal p l)
      {pr with stack := base ++ pr.stack} =
      .ok {result with stack := base ++ result.stack} := by
  induction labels generalizing pr result with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h_ok ⊢
    subst h_ok; rfl
  | cons l rest ih =>
    simp only [List.foldlM] at h_ok ⊢
    cases h_step : db.stepNormal pr l with
    | error e => simp [h_step, bind, Except.bind] at h_ok
    | ok mid =>
      simp only [h_step, bind, Except.bind] at h_ok
      have h_step' := stepNormal_prepend_stack db pr l base mid h_step
      simp only [h_step', bind, Except.bind]
      exact ih mid _ h_ok

/-! ## Part 13: Certificate Definitions for Z Save Support

The certificate-based approach to Z save support. Instead of tracing the global
compressed execution, we maintain per-element certificates that each stack/heap
formula is derivable by some normal proof script.

**Key insight**: when `.save` copies `stack.back?` to heap as `.fmla f`, we just
copy the *certificate* that `f` is derivable. No unrolling of compressed execution needed. -/

/-- A certificate that formula `f` is derivable from `db`.
    Existential: there exist labels whose fold via `stepNormal` produces `[f]`.
    The init state uses `db.frame` (the canonical frame), dummy label/fmla fields,
    and empty stack/heap. -/
def DerivCert (db : DB) (f : Formula) : Prop :=
  ∃ (labels : List String) (pr_final : ProofState),
    labels.foldlM (fun p l => db.stepNormal p l)
      ⟨⟨0,0⟩, "", #[], db.frame, #[], #[], .normal⟩ = .ok pr_final ∧
    pr_final.stack = #[f]

/-- Every stack element has a derivation certificate. -/
def StackCert (db : DB) (stack : Array Formula) : Prop :=
  ∀ i (h : i < stack.size), DerivCert db stack[i]

/-- Every heap element has appropriate certification:
    - `.fmla f`: `f` has a derivation certificate
    - `.assert f fr`: there's a label mapping to this assertion in `db` -/
def HeapCert (db : DB) (heap : Array HeapEl) : Prop :=
  ∀ i (h : i < heap.size), match heap[i] with
    | .fmla f => DerivCert db f
    | .assert f fr => ∃ l origin, db.find? l = some (.assert f fr origin)

/-! ### Foundation Lemmas -/

theorem StackCert_empty (db : DB) : StackCert db #[] :=
  fun _ h => absurd h (by simp)

theorem HeapCert_empty (db : DB) : HeapCert db #[] :=
  fun _ h => absurd h (by simp)

theorem StackCert_push (db : DB) (stack : Array Formula) (f : Formula)
    (h_sc : StackCert db stack) (h_cert : DerivCert db f) :
    StackCert db (stack.push f) := by
  intro i h_i
  by_cases h_lt : i < stack.size
  · simp only [Array.getElem_push_lt h_lt]; exact h_sc i h_lt
  · have : i = stack.size := by simp [Array.size_push] at h_i; omega
    subst this; simp only [Array.getElem_push_eq]; exact h_cert

theorem HeapCert_push_fmla (db : DB) (heap : Array HeapEl) (f : Formula)
    (h_hc : HeapCert db heap) (h_cert : DerivCert db f) :
    HeapCert db (heap.push (.fmla f)) := by
  intro i h_i
  by_cases h_lt : i < heap.size
  · simp only [Array.getElem_push_lt h_lt]; exact h_hc i h_lt
  · have : i = heap.size := by simp [Array.size_push] at h_i; omega
    subst this; simp only [Array.getElem_push_eq]; exact h_cert

theorem HeapCert_push_assert (db : DB) (heap : Array HeapEl) (f : Formula) (fr : Frame)
    (h_hc : HeapCert db heap)
    (h_label : ∃ l origin, db.find? l = some (.assert f fr origin)) :
    HeapCert db (heap.push (.assert f fr)) := by
  intro i h_i
  by_cases h_lt : i < heap.size
  · simp only [Array.getElem_push_lt h_lt]; exact h_hc i h_lt
  · have : i = heap.size := by simp [Array.size_push] at h_i; omega
    subst this; simp only [Array.getElem_push_eq]; exact h_label

/-- Extract a DerivCert for the last stack element. -/
theorem StackCert_back (db : DB) (stack : Array Formula)
    (h_sc : StackCert db stack) (h_ne : 0 < stack.size) :
    DerivCert db stack[stack.size - 1] :=
  h_sc (stack.size - 1) (by omega)

/-! ## Part 14: Action-Step Certificate Preservation

Each compressed action (step-fmla, step-assert, save) preserves
StackCert and HeapCert. These are composed in Part 15 to handle the full
compressed execution with Z saves. -/

/-! ### Part 14a: Save Preserves Certs -/

/-- Save preserves both StackCert and HeapCert.
    Save copies `stack.back?` to heap as `.fmla f`. Stack is unchanged. -/
theorem save_preserves_certs (db : DB) (pr pr' : ProofState)
    (h_save : pr.save = .ok pr')
    (h_sc : StackCert db pr.stack) (h_hc : HeapCert db pr.heap) :
    StackCert db pr'.stack ∧ HeapCert db pr'.heap := by
  unfold ProofState.save at h_save
  cases h_back : pr.stack.back? with
  | none => simp [h_back] at h_save
  | some f =>
    simp only [h_back, pure, Except.pure, ProofState.pushHeap, Except.ok.injEq] at h_save
    subst h_save
    -- pr'.stack = pr.stack (unchanged), pr'.heap = pr.heap.push (.fmla f)
    constructor
    · exact h_sc
    · -- Extract DerivCert for f from StackCert: back? gives getElem? at (size-1)
      have h_back' : pr.stack[pr.stack.size - 1]? = some f := by
        unfold Array.back? at h_back; exact h_back
      obtain ⟨h_lt, h_eq⟩ := Array.getElem_of_getElem? h_back'
      have h_cert : DerivCert db f := by
        have h := h_sc (pr.stack.size - 1) h_lt
        rw [h_eq] at h; exact h
      exact HeapCert_push_fmla db pr.heap f h_hc h_cert

/-! ### Part 14b: stepProof on .fmla Preserves Certs -/

/-- When `heap[n] = .fmla f`, stepProof pushes f. Certs are maintained. -/
theorem stepProof_fmla_preserves_certs (db : DB) (pr pr' : ProofState) (n : Nat)
    (h_step : db.stepProof pr n = .ok pr')
    (h_sc : StackCert db pr.stack) (h_hc : HeapCert db pr.heap)
    (h_fmla : ∃ f, pr.heap[n]? = some (.fmla f)) :
    StackCert db pr'.stack ∧ HeapCert db pr'.heap := by
  obtain ⟨f, h_f⟩ := h_fmla
  -- stepProof with .fmla gives pr' = pr.push f
  unfold DB.stepProof at h_step
  simp only [h_f, pure, Except.pure, Except.ok.injEq] at h_step
  subst h_step
  -- pr'.stack = pr.stack.push f, pr'.heap = pr.heap
  constructor
  · -- StackCert: need DerivCert db f from HeapCert
    obtain ⟨h_lt, h_eq⟩ := Array.getElem_of_getElem? h_f
    have h_cert : DerivCert db f := by
      have := h_hc n h_lt
      rw [h_eq] at this
      exact this
    exact StackCert_push db pr.stack f h_sc h_cert
  · exact h_hc

/-! ### Part 14c Infrastructure: stepAssert Helpers -/

/-- stepAssert only modifies stack — heap is preserved. -/
private theorem stepAssert_heap_preserved (db : DB) (pr result : ProofState)
    (f : Formula) (fr : Frame) (h_ok : db.stepAssert pr f fr = .ok result) :
    result.heap = pr.heap := by
  obtain ⟨dj, hyps⟩ := fr
  rw [DB.stepAssert.eq_1] at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- hyps.size ≤ pr.stack.size
    split at h_ok
    · exact absurd h_ok nofun  -- hasConstHead guard
    · split at h_ok
      · exact absurd h_ok nofun  -- formulaSymsRespectFrame guard
      · -- match chains for checkHyp, dvCheck, subst
        split at h_ok
        · exact absurd h_ok nofun  -- checkHyp error
        · split at h_ok
          · exact absurd h_ok nofun  -- dvCheck error
          · split at h_ok
            · -- subst ok → result = { pr with stack := ... }
              cases h_ok; rfl
            · exact absurd h_ok nofun  -- subst error
  · exact absurd h_ok nofun

/-- StackCert for a prefix (shrink) of the stack. -/
theorem StackCert_shrink (db : DB) (stack : Array Formula) (k : Nat)
    (h_k : k ≤ stack.size) (h_sc : StackCert db stack) :
    StackCert db (stack.shrink k) := by
  intro i h_i
  have h_i_lt : i < stack.size := by
    have := Array.size_shrink (xs := stack) (i := k); omega
  rw [Array.getElem_shrink]; exact h_sc i h_i_lt

/-- StackCert for an extract (subarray) of the stack. -/
theorem StackCert_extract (db : DB) (stack : Array Formula) (i j : Nat)
    (h_sc : StackCert db stack) :
    StackCert db (stack.extract i j) := by
  intro k h_k
  have h_k_lt : i + k < stack.size := by
    have := Array.size_extract (xs := stack) (start := i) (stop := j); omega
  rw [Array.getElem_extract]; exact h_sc _ h_k_lt

/-- StackCert implies all toList members have DerivCerts. -/
theorem StackCert_toList_certs (db : DB) (stack : Array Formula)
    (h_sc : StackCert db stack) : ∀ f ∈ stack.toList, DerivCert db f := by
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hf
  have h_lt : i < stack.size := by rwa [Array.length_toList] at hi
  rw [Array.getElem_toList h_lt]; exact h_sc i h_lt

/-! ### Part 14c Infrastructure: Array Split + Cert Composition -/

/-- Array split: shrink ++ extract = original. -/
private theorem array_shrink_extract_eq (a : Array Formula) (k : Nat) (h : k ≤ a.size) :
    a.shrink k ++ a.extract k a.size = a := by
  apply Array.ext'
  simp [Array.toList_extract, List.extract]
  rw [List.take_of_length_le (by simp; omega)]

/-- checkHyp depends only on the stack contents and offset value, not on proof terms.
    When the stacks are equal and the offset values match, the results are equal.
    This handles dependent-type-safe rewriting across different Subtype proofs. -/
private theorem checkHyp_eq_of_stack_off
    (db : DB) (hyps : Array String) {s₁ s₂ : Array Formula}
    (off₁ : {off // off + hyps.size = s₁.size})
    (off₂ : {off // off + hyps.size = s₂.size})
    (h_s : s₁ = s₂) (h_o : off₁.1 = off₂.1)
    (i : Nat) (σ : Std.HashMap String Formula) :
    db.checkHyp hyps s₁ off₁ i σ = db.checkHyp hyps s₂ off₂ i σ := by
  subst h_s; rw [show off₁ = off₂ from Subtype.ext h_o]

set_option maxHeartbeats 6400000 in
/-- stepAssert on just the exact hypothesis elements succeeds with the same conclusion.
    Also characterizes the original result's stack structure. -/
private theorem stepAssert_exact_args
    (db : DB) (pr result : ProofState) (f : Formula) (fr : Frame)
    (h_ok : db.stepAssert pr f fr = .ok result) :
    ∃ concl,
      db.stepAssert {pr with stack := pr.stack.extract (pr.stack.size - fr.hyps.size) pr.stack.size} f fr =
        .ok {pr with stack := #[concl]} ∧
      result = {pr with stack := (pr.stack.shrink (pr.stack.size - fr.hyps.size)).push concl} := by
  obtain ⟨dj, hyps⟩ := fr
  have h_le := stepAssert_ok_implies_le db pr f ⟨dj, hyps⟩ result h_ok
  simp only [] at h_le ⊢
  -- Abbreviations (inlined since `set` tactic unavailable in batteries-only)
  -- off := pr.stack.size - hyps.size
  -- args := pr.stack.extract off pr.stack.size
  -- base := pr.stack.shrink off
  have h_args_size : (pr.stack.extract (pr.stack.size - hyps.size) pr.stack.size).size = hyps.size := by
    simp [Array.size_extract]; omega
  have h_off_k : (pr.stack.size - hyps.size) + hyps.size = pr.stack.size := Nat.sub_add_cancel h_le
  have h_split : pr.stack.shrink (pr.stack.size - hyps.size) ++
      pr.stack.extract (pr.stack.size - hyps.size) pr.stack.size = pr.stack :=
    array_shrink_extract_eq pr.stack (pr.stack.size - hyps.size) (by omega)
  have h_base_size : (pr.stack.shrink (pr.stack.size - hyps.size)).size =
      pr.stack.size - hyps.size := by simp
  -- Unfold original stepAssert to extract intermediate values
  rw [DB.stepAssert.eq_1] at h_ok
  simp only [bind, Except.bind, pure, Except.pure, h_le, ↓reduceDIte] at h_ok
  split at h_ok
  · exact absurd h_ok nofun  -- hasConstHead
  · rename_i h_const
    split at h_ok
    · exact absurd h_ok nofun  -- formulaSymsRespectFrame
    · rename_i h_respect
      split at h_ok
      · exact absurd h_ok nofun  -- checkHyp error
      · rename_i subst h_chk
        split at h_ok
        · exact absurd h_ok nofun  -- dvCheck error
        · rename_i h_dv
          split at h_ok
          · -- subst succeeds with concl
            rename_i concl h_sub
            cases h_ok
            refine ⟨concl, ?_, rfl⟩
            -- Key: checkHyp on extracted args at natural offset = .ok subst
            -- Uses rw chain: offset→0 → prepend_general → stack_eq → h_chk
            have h_chk_args : db.checkHyp hyps
                (pr.stack.extract (pr.stack.size - hyps.size))
                ⟨(pr.stack.extract (pr.stack.size - hyps.size)).size
                  - hyps.size, by omega⟩ 0 ∅ = .ok subst := by
              -- Step 1: simplify offset from (args.size - hyps.size) to 0
              rw [checkHyp_eq_of_stack_off db hyps _ ⟨0, by omega⟩ rfl (by dsimp; omega) 0 ∅]
              -- Step 2: args ⟨0, _⟩ → (base ++ args) ⟨base.size, _⟩
              rw [← checkHyp_prepend_general db hyps
                (pr.stack.shrink (pr.stack.size - hyps.size))
                (pr.stack.extract (pr.stack.size - hyps.size)) 0
                (by omega) hyps.size 0 ∅ rfl]
              -- Step 3: (base ++ args) → pr.stack via h_split
              rw [checkHyp_eq_of_stack_off db hyps _
                ⟨pr.stack.size - hyps.size, h_off_k⟩ h_split (by simp) 0 ∅]
              exact h_chk
            -- Show stepAssert on extracted args succeeds
            rw [DB.stepAssert.eq_1]
            simp only [bind, Except.bind, pure, Except.pure,
                        show hyps.size ≤
                          (pr.stack.extract (pr.stack.size - hyps.size)).size
                          from by omega,
                        ↓reduceDIte]
            simp only [show ¬(!Formula.hasConstHead f) = true from h_const, ↓reduceIte,
                        show ¬(!db.formulaSymsRespectFrame f ⟨dj, hyps⟩) = true from h_respect,
                        Bool.false_eq_true, ↓reduceIte]
            -- Substitute checkHyp result, dvCheck, and f.subst
            simp only [h_chk_args, h_dv, h_sub, Except.ok.injEq]
            -- ProofState equality: simplify shrink (args.size - hyps.size) to shrink 0
            congr 1
            -- Stack: (args.shrink (args.size-hyps.size)).push concl = #[concl]
            have h0 : (pr.stack.extract (pr.stack.size - hyps.size)).size
                - hyps.size = 0 := by omega
            rw [h0]; simp
          · exact absurd h_ok nofun  -- subst error

/-- Extend a successful foldlM by appending one DerivCert.
    If `fold labels from init = .ok acc_pr` with `acc_pr.frame = db.frame`,
    and we have `DerivCert db f`, then there's a longer fold producing
    `acc_pr.stack.push f`. -/
theorem compose_derivcert_step (db : DB)
    (acc_labels : List String) (acc_pr : ProofState)
    (init : ProofState)
    (h_acc_fold : acc_labels.foldlM (fun p l => db.stepNormal p l) init = .ok acc_pr)
    (h_init_frame : init.frame = db.frame)
    (f : Formula) (h_cert : DerivCert db f) :
    ∃ (all_labels : List String) (pr_final : ProofState),
      all_labels.foldlM (fun p l => db.stepNormal p l) init = .ok pr_final ∧
      pr_final.stack = acc_pr.stack.push f ∧
      pr_final.frame = db.frame := by
  obtain ⟨cert_labels, cert_pr, h_cert_fold, h_cert_stack⟩ := h_cert
  -- By prepend: cert fold from {init with stack := acc_pr.stack} gives {cert_pr with stack := acc_pr.stack ++ cert_pr.stack}
  let init₀ : ProofState := ⟨⟨0,0⟩, "", #[], db.frame, #[], #[], .normal⟩
  have h_cert_prepend :=
    foldlM_stepNormal_prepend db cert_labels init₀ cert_pr acc_pr.stack h_cert_fold
  -- {init₀ with stack := acc_pr.stack ++ init₀.stack} = {init₀ with stack := acc_pr.stack}
  have h_init0_stack : init₀.stack = #[] := rfl
  simp only [h_init0_stack, Array.append_empty] at h_cert_prepend
  -- Result: cert fold from {init₀ with stack := acc_pr.stack} = .ok {cert_pr with stack := acc_pr.stack ++ cert_pr.stack}
  rw [h_cert_stack] at h_cert_prepend
  -- = .ok {cert_pr with stack := acc_pr.stack ++ #[f]} = .ok {cert_pr with stack := acc_pr.stack.push f}
  -- Transfer: from {init₀ with stack := acc_pr.stack} to acc_pr (same stack and frame)
  have h_transfer :=
    foldlM_stepNormal_transfer db cert_labels
      ({init₀ with stack := acc_pr.stack}) acc_pr
      ({cert_pr with stack := acc_pr.stack.push f})
      rfl h_cert_prepend
  obtain ⟨r₂, h_r₂_fold, h_r₂_stack⟩ := h_transfer
  -- Compose folds: (acc_labels ++ cert_labels) from init
  refine ⟨acc_labels ++ cert_labels, r₂, ?_, ?_, ?_⟩
  · simp only [List.foldlM_append, h_acc_fold, bind, Except.bind]; exact h_r₂_fold
  · rw [h_r₂_stack]
  · exact foldlM_preserves_frame db (acc_labels ++ cert_labels) init r₂
      (by simp only [List.foldlM_append, h_acc_fold, bind, Except.bind]; exact h_r₂_fold)
      |>.trans h_init_frame

/-- Compose a list of DerivCerts into a single fold producing the multi-element stack.
    This is the key cert composition theorem used for building assertion hypothesis stacks. -/
theorem compose_derivcerts (db : DB) (fs : List Formula)
    (h_certs : ∀ f ∈ fs, DerivCert db f) :
    let init : ProofState := ⟨⟨0,0⟩, "", #[], db.frame, #[], #[], .normal⟩
    ∃ (labels : List String) (pr_final : ProofState),
      labels.foldlM (fun p l => db.stepNormal p l) init = .ok pr_final ∧
      pr_final.stack = fs.toArray ∧
      pr_final.frame = db.frame := by
  intro init
  induction fs with
  | nil => exact ⟨[], init, rfl, rfl, rfl⟩
  | cons f rest ih =>
    -- 1. f's cert: f_labels from init → f_pr with stack #[f]
    obtain ⟨f_labels, f_pr, h_f_fold, h_f_stack⟩ := h_certs f List.mem_cons_self
    -- Bridge: h_f_fold uses DerivCert's struct literal; we need init (the let binding)
    have h_f_fold' : f_labels.foldlM (fun p l => db.stepNormal p l) init = .ok f_pr := h_f_fold
    have h_f_frame : f_pr.frame = db.frame :=
      (foldlM_preserves_frame db f_labels init f_pr h_f_fold').trans rfl
    -- 2. rest IH: rest_labels from init → rest_pr with stack rest.toArray
    obtain ⟨rest_labels, rest_pr, h_rest_fold, h_rest_stack, h_rest_frame⟩ :=
      ih (fun g hg => h_certs g (List.mem_cons_of_mem f hg))
    -- 3. Prepend #[f] to rest fold
    have h_prepend :=
      foldlM_stepNormal_prepend db rest_labels init rest_pr #[f] h_rest_fold
    simp only [show init.stack = #[] from rfl, Array.append_empty] at h_prepend
    rw [h_rest_stack] at h_prepend
    -- h_prepend : rest_labels from {init with stack := #[f]} = .ok {rest_pr with stack := #[f] ++ rest.toArray}
    -- 4. Transfer from {init with stack := #[f]} to f_pr (same stack, same frame)
    have h_transfer := foldlM_stepNormal_transfer db rest_labels
      ({init with stack := #[f]}) f_pr
      ({rest_pr with stack := #[f] ++ rest.toArray})
      (by simp [h_f_stack]) h_prepend
    obtain ⟨r₂, h_r₂_fold, h_r₂_stack⟩ := h_transfer
    -- 5. Compose: f_labels ++ rest_labels from init
    refine ⟨f_labels ++ rest_labels, r₂, ?_, ?_, ?_⟩
    · simp only [List.foldlM_append, h_f_fold', bind, Except.bind]; exact h_r₂_fold
    · have h_eq : r₂.stack = #[f] ++ rest.toArray := h_r₂_stack
      rw [h_eq, ← List.toArray_cons]
    · exact foldlM_preserves_frame db (f_labels ++ rest_labels) init r₂
        (by simp only [List.foldlM_append, h_f_fold', bind, Except.bind]; exact h_r₂_fold)
        |>.trans rfl

/-! ### Part 14c: stepProof on .assert Preserves Certs (KEY LEMMA)

When `heap[n] = .assert f_a fr_a`, stepProof calls stepAssert.
The top `fr_a.hyps.size` stack entries are consumed, and a conclusion is pushed.
Each consumed entry has a DerivCert (from StackCert). Composing their proof
labels with the assertion's label produces a DerivCert for the conclusion.

This is the key lemma that enables Z save support: it shows that stepAssert
produces certified results when all inputs are certified.

`h_frame` is required because DerivCert replays proofs from init with `db.frame`,
and dvCheck in stepAssert uses the ProofState's frame. During compressed proof
execution, `pr.frame = db.frame` throughout (stepProof preserves frame). -/

/-- When `heap[n] = .assert f_a fr_a`, stepProof calls stepAssert.
    The conclusion is certified if the stack entries and assertion are certified. -/
theorem stepProof_assert_preserves_certs (db : DB) (pr pr' : ProofState) (n : Nat)
    (h_step : db.stepProof pr n = .ok pr')
    (h_sc : StackCert db pr.stack) (h_hc : HeapCert db pr.heap)
    (h_assert : ∃ f fr, pr.heap[n]? = some (.assert f fr)) :
    StackCert db pr'.stack ∧ HeapCert db pr'.heap := by
  obtain ⟨f_a, fr_a, h_a⟩ := h_assert
  -- stepProof with .assert calls stepAssert
  unfold DB.stepProof at h_step
  simp only [h_a] at h_step
  -- h_step : db.stepAssert pr f_a fr_a = .ok pr'
  constructor
  · -- StackCert for pr'.stack
    -- Step 1: Extract concl and structure from stepAssert
    obtain ⟨concl, h_exact_args, h_pr'_eq⟩ :=
      stepAssert_exact_args db pr pr' f_a fr_a h_step
    have h_le := stepAssert_ok_implies_le db pr f_a fr_a pr' h_step
    -- pr'.stack = (shrink off).push concl
    have h_pr'_stack : pr'.stack =
        (pr.stack.shrink (pr.stack.size - fr_a.hyps.size)).push concl := by
      rw [h_pr'_eq]
    rw [h_pr'_stack]
    apply StackCert_push
    · exact StackCert_shrink db pr.stack _ (by omega) h_sc
    · -- DerivCert for concl: compose arg certs + assertion label
      -- Step 2: HeapCert gives us the assertion's label in db
      have h_n_bound : n < pr.heap.size := by
        simp only [GetElem?.getElem?, decidableGetElem?] at h_a
        split at h_a <;> [assumption; exact absurd h_a nofun]
      have h_heap_val : pr.heap[n] = .assert f_a fr_a := by
        simp only [GetElem?.getElem?, decidableGetElem?, h_n_bound, ↓reduceDIte] at h_a
        exact Option.some.inj h_a
      have h_hc_n := h_hc n h_n_bound
      rw [h_heap_val] at h_hc_n
      obtain ⟨l_a, origin_a, h_find_a⟩ := h_hc_n
      -- Step 3: Extract args and get certs for them
      have h_args_sc : StackCert db
          (pr.stack.extract (pr.stack.size - fr_a.hyps.size) pr.stack.size) :=
        StackCert_extract db pr.stack _ _ h_sc
      have h_args_certs := StackCert_toList_certs db _ h_args_sc
      -- Step 4: Compose arg certs into a single fold
      obtain ⟨labels₁, pr₁, h_fold₁, h_stack₁, h_frame₁⟩ :=
        compose_derivcerts db
          (pr.stack.extract (pr.stack.size - fr_a.hyps.size) pr.stack.size).toList
          h_args_certs
      -- pr₁.stack = args
      have h_stack₁_args : pr₁.stack =
          pr.stack.extract (pr.stack.size - fr_a.hyps.size) pr.stack.size := by
        rw [h_stack₁, Array.toArray_toList]
      -- Step 5: stepNormal l_a on {pr with stack := args}
      have h_stepN : db.stepNormal
          {pr with stack := pr.stack.extract (pr.stack.size - fr_a.hyps.size) pr.stack.size}
          l_a = .ok {pr with stack := #[concl]} := by
        unfold DB.stepNormal; rw [h_find_a]; exact h_exact_args
      -- Step 6: [l_a].foldlM from {pr with stack := args}
      have h_fold_la : [l_a].foldlM (fun p l => db.stepNormal p l)
          {pr with stack := pr.stack.extract (pr.stack.size - fr_a.hyps.size) pr.stack.size}
          = .ok {pr with stack := #[concl]} := by
        simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind,
          pure, Except.pure, h_stepN]
      -- Step 7: Transfer from {pr with stack := args} to pr₁
      obtain ⟨r₂, h_r₂_fold, h_r₂_stack⟩ := foldlM_stepNormal_transfer db [l_a]
        ({pr with stack :=
            pr.stack.extract (pr.stack.size - fr_a.hyps.size) pr.stack.size})
        pr₁ ({pr with stack := #[concl]})
        (by simp [h_stack₁_args]) h_fold_la
      -- Step 8: Compose labels₁ ++ [l_a] → DerivCert for concl
      refine ⟨labels₁ ++ [l_a], r₂, ?_, h_r₂_stack⟩
      rw [List.foldlM_append, h_fold₁]
      simp only [bind, Except.bind]
      exact h_r₂_fold
  · -- HeapCert: pr'.heap = pr.heap since stepAssert only modifies stack
    rw [stepAssert_heap_preserved db pr pr' f_a fr_a h_step]; exact h_hc

/-! ## Part 15: Z-Aware Compressed Proof Provenance

Full support for compressed proofs WITH Z (save) actions.
The certificate approach: each stack/heap element carries evidence
that it was produced by some normal proof, so saves just copy certs
from stack to heap.

**Architecture:**
1. `StepSaveAction` + `execStepSave`: compressed actions (step/save, no unknown)
2. Frame preservation through actions
3. Cert preservation through a single action + fold
4. Preload HeapCert: the preloaded heap satisfies HeapCert under WellFormedDB
5. `ZCompressedProofReachable`: preload + step/save actions
6. Bridge to NormalProofReachable + upgrade dispatcher
-/

open Metamath.Kernel (stepProof_preserves_frame_heap)

/-! ### Part 15a: StepSaveAction + Execution -/

/-- A compressed action that is either a heap step or a Z save.
    Unknown (?) actions are excluded — they represent incomplete proofs. -/
inductive StepSaveAction where
  | step (n : Nat)
  | save

/-- Execute one step-or-save compressed action. -/
def execStepSave (db : DB) (pr : ProofState) (act : StepSaveAction) :
    Except ProofCheckFail ProofState :=
  match act with
  | .step n => db.stepProof pr n
  | .save =>
    match pr.save with
    | .ok pr' => pure pr'
    | .error err => throw (.compressedSave err)

/-! ### Part 15b: Frame Preservation -/

/-- One step-or-save action preserves the ProofState frame. -/
theorem execStepSave_preserves_frame (db : DB) (pr pr' : ProofState) (act : StepSaveAction)
    (h_ok : execStepSave db pr act = .ok pr') :
    pr'.frame = pr.frame := by
  cases act with
  | step n => exact (stepProof_preserves_frame_heap db pr pr' n h_ok).1
  | save =>
    simp [execStepSave] at h_ok
    cases h_save : pr.save with
    | error e => simp [h_save] at h_ok
    | ok pr'' =>
      simp [h_save, pure, Except.pure] at h_ok; subst h_ok
      unfold ProofState.save at h_save
      cases h_back : pr.stack.back? with
      | none => simp [h_back] at h_save
      | some f =>
        simp [h_back, pure, Except.pure, ProofState.pushHeap] at h_save
        subst h_save; rfl

/-- Frame preservation through a fold of step-or-save actions. -/
theorem execStepSave_fold_preserves_frame (db : DB)
    (acts : List StepSaveAction) (pr result : ProofState)
    (h_fold : acts.foldlM (fun p a => execStepSave db p a) pr = .ok result) :
    result.frame = pr.frame := by
  induction acts generalizing pr with
  | nil =>
    simp [List.foldlM_nil, pure, Except.pure] at h_fold; subst h_fold; rfl
  | cons act rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_fold
    cases h_step : execStepSave db pr act with
    | error e => simp [h_step] at h_fold
    | ok pr' =>
      simp [h_step] at h_fold
      exact (ih pr' h_fold).trans (execStepSave_preserves_frame db pr pr' act h_step)

/-! ### Part 15c: Heap Cases Helper -/

/-- When stepProof succeeds, the heap element is either `.fmla` or `.assert`. -/
private theorem stepProof_heap_cases (db : DB) (pr pr' : ProofState) (n : Nat)
    (h_ok : db.stepProof pr n = .ok pr') :
    (∃ f, pr.heap[n]? = some (.fmla f)) ∨ (∃ f fr, pr.heap[n]? = some (.assert f fr)) := by
  unfold DB.stepProof at h_ok
  cases h_get : pr.heap[n]? with
  | none => simp [h_get] at h_ok
  | some el =>
    cases el with
    | fmla f => exact Or.inl ⟨f, rfl⟩
    | assert f fr => exact Or.inr ⟨f, fr, rfl⟩

/-! ### Part 15d: Cert Preservation for One Action -/

/-- One step-or-save action preserves StackCert and HeapCert. -/
theorem execStepSave_preserves_certs (db : DB) (pr pr' : ProofState) (act : StepSaveAction)
    (h_ok : execStepSave db pr act = .ok pr')
    (h_sc : StackCert db pr.stack) (h_hc : HeapCert db pr.heap) :
    StackCert db pr'.stack ∧ HeapCert db pr'.heap := by
  cases act with
  | step n =>
    simp [execStepSave] at h_ok
    cases stepProof_heap_cases db pr pr' n h_ok with
    | inl h_fmla =>
      exact stepProof_fmla_preserves_certs db pr pr' n h_ok h_sc h_hc h_fmla
    | inr h_assert =>
      exact stepProof_assert_preserves_certs db pr pr' n h_ok h_sc h_hc h_assert
  | save =>
    simp [execStepSave] at h_ok
    cases h_save : pr.save with
    | error e => simp [h_save] at h_ok
    | ok pr'' =>
      simp [h_save, pure, Except.pure] at h_ok; subst h_ok
      exact save_preserves_certs db pr pr'' h_save h_sc h_hc

/-! ### Part 15e: Cert Preservation Through Action Fold -/

/-- Fold of step-or-save actions preserves StackCert and HeapCert. -/
theorem execStepSave_fold_preserves_certs (db : DB)
    (acts : List StepSaveAction) (pr result : ProofState)
    (h_fold : acts.foldlM (fun p a => execStepSave db p a) pr = .ok result)
    (h_sc : StackCert db pr.stack) (h_hc : HeapCert db pr.heap) :
    StackCert db result.stack ∧ HeapCert db result.heap := by
  induction acts generalizing pr with
  | nil =>
    simp [List.foldlM_nil, pure, Except.pure] at h_fold
    subst h_fold; exact ⟨h_sc, h_hc⟩
  | cons act rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_fold
    cases h_step : execStepSave db pr act with
    | error e => simp [h_step] at h_fold
    | ok pr' =>
      simp [h_step] at h_fold
      have ⟨h_sc', h_hc'⟩ :=
        execStepSave_preserves_certs db pr pr' act h_step h_sc h_hc
      exact ih pr' h_fold h_sc' h_hc'

/-! ### Part 15f: Preload HeapCert -/

/-- One-step normal proof yields a DerivCert for any hypothesis in scope.
    Under WellFormedDB, format checks (hasConstHead / isFloatShape) pass. -/
private theorem hyp_derivcert (db : DB) (l : String) (ess : Bool)
    (f : Formula) (origin : String)
    (h_find : db.find? l = some (.hyp ess f origin))
    (h_in_frame : l ∈ db.frame.hyps)
    (h_wf : WellFormedDB db) :
    DerivCert db f := by
  have h_obj_wf := h_wf.2 l _ h_find; simp at h_obj_wf
  have h_in_list : l ∈ db.frame.hyps.toList := Array.mem_toList_iff.mpr h_in_frame
  let init : ProofState := ⟨⟨0,0⟩, "", #[], db.frame, #[], #[], .normal⟩
  have h_step : db.stepNormal init l = .ok (init.push f) := by
    unfold DB.stepNormal; rw [h_find]; simp [h_in_list]
    cases ess with
    | true =>
      have : f.hasConstHead = true := by
        simp at h_obj_wf; obtain ⟨h_pos, c, h_const⟩ := h_obj_wf
        unfold Metamath.Verify.Formula.hasConstHead; simp [h_pos]
        rw [show f[0] = f[0]! from by rw [getElem!_pos f 0 h_pos], h_const]
      simp [this, pure, Except.pure]
    | false =>
      have : f.isFloatShape = true := by
        simp at h_obj_wf; obtain ⟨h_size, c, v, h_const, h_var⟩ := h_obj_wf
        unfold Metamath.Verify.Formula.isFloatShape; simp [h_size]
        rw [show f[0] = f[0]! from by rw [getElem!_pos f 0 (by omega)], h_const,
            show f[1] = f[1]! from by rw [getElem!_pos f 1 (by omega)], h_var]
      simp [this, pure, Except.pure]
  refine ⟨[l], init.push f, ?_, rfl⟩
  rw [show [l].foldlM (fun p l => db.stepNormal p l) init =
      (db.stepNormal init l >>= fun v => pure v) from by
    simp [List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure]]
  rw [h_step]; rfl

/-- One preload step preserves HeapCert.
    For `.hyp` entries, constructs a one-step DerivCert.
    For `.assert` entries, records the label as witness. -/
theorem preload_preserves_heapCert (db : DB) (pr pr' : ProofState) (l : String)
    (h_preload : db.preload pr l = .ok pr')
    (h_hc : HeapCert db pr.heap)
    (h_wf : WellFormedDB db) :
    HeapCert db pr'.heap := by
  unfold DB.preload at h_preload
  cases h_find : db.find? l with
  | none => simp [h_find] at h_preload
  | some obj =>
    cases obj with
    | hyp ess f origin =>
      rw [h_find] at h_preload; simp at h_preload
      by_cases h_in : l ∈ db.frame.hyps
      · simp [h_in, pure, Except.pure] at h_preload
        rw [← h_preload]; simp [ProofState.pushHeap]
        exact HeapCert_push_fmla db pr.heap f h_hc
          (hyp_derivcert db l ess f origin h_find h_in h_wf)
      · simp [h_in] at h_preload
    | assert f fr origin =>
      rw [h_find] at h_preload; simp [pure, Except.pure] at h_preload
      rw [← h_preload]; simp [ProofState.pushHeap]
      exact HeapCert_push_assert db pr.heap f fr h_hc ⟨l, origin, h_find⟩
    | var v => rw [h_find] at h_preload; simp at h_preload
    | const _ => rw [h_find] at h_preload; simp at h_preload

/-- Preload fold preserves HeapCert. -/
theorem preload_fold_preserves_heapCert (db : DB)
    (preloads : List String) (pr result : ProofState)
    (h_fold : preloads.foldlM (DB.preload db) pr = .ok result)
    (h_hc : HeapCert db pr.heap) (h_wf : WellFormedDB db) :
    HeapCert db result.heap := by
  induction preloads generalizing pr with
  | nil =>
    simp [List.foldlM_nil, pure, Except.pure] at h_fold; subst h_fold; exact h_hc
  | cons l rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h_fold
    cases h_step : DB.preload db pr l with
    | error e => simp [h_step] at h_fold
    | ok pr' =>
      simp [h_step] at h_fold
      exact ih pr' h_fold (preload_preserves_heapCert db pr pr' l h_step h_hc h_wf)

/-! ### Part 15g: DerivCert Extraction + Bridge -/

/-- Extract a DerivCert from a StackCert when the formula is at index 0. -/
theorem compressed_final_cert (db : DB) (result : ProofState)
    (h_sc : StackCert db result.stack)
    (fmla : Formula) (h_fmla : result.stack[0]? = some fmla) :
    DerivCert db fmla := by
  obtain ⟨h_lt, h_eq⟩ := Array.getElem_of_getElem? h_fmla
  rw [← h_eq]; exact h_sc 0 h_lt

/-- DerivCert bridges to NormalProofReachable.
    Both definitions use `foldlM stepNormal` from init states with the same
    stack (#[]) and frame (db.frame), differing only in metadata (label, fmla).
    `foldlM_stepNormal_transfer` handles the metadata difference. -/
theorem DerivCert_to_NormalProofReachable
    (db : DB) (label : String) (fmla : Formula) (f : Formula)
    (h_cert : DerivCert db f) :
    NormalProofReachable db label fmla #[f] := by
  obtain ⟨labels, pr_final, h_fold, h_stack⟩ := h_cert
  obtain ⟨r₂, h_r₂_fold, h_r₂_stack⟩ := foldlM_stepNormal_transfer db labels
    (⟨⟨0,0⟩, "", #[], db.frame, #[], #[], .normal⟩)
    (⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .normal⟩)
    pr_final rfl h_fold
  rw [← h_stack, ← h_r₂_stack]
  refine ⟨labels.toArray, r₂, ?_, rfl⟩
  rw [← Array.foldlM_toList, List.toList_toArray]
  exact h_r₂_fold

/-! ### Part 15h: ZCompressedProofReachable -/

/-- Proof execution reachability for compressed proofs WITH Z (save) actions.

    Models the full compressed proof execution:
    1. Preload phase: build heap from label list
    2. Action phase: fold step/save actions over the preloaded state
    3. The final stack matches

    Generalizes `CompressedProofReachable` (which only handles step indices). -/
def ZCompressedProofReachable (db : DB) (label : String) (fmla : Formula)
    (stack : Array Formula) : Prop :=
  ∃ (preloads : List String) (actions : List StepSaveAction)
    (pr_preload pr_final : ProofState),
    preloads.foldlM (DB.preload db)
      ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], ProofTokenParser.normal⟩ = .ok pr_preload ∧
    actions.foldlM (fun p a => execStepSave db p a) pr_preload = .ok pr_final ∧
    pr_final.stack = stack

/-- Array with size 1 and known element at index 0 is a singleton. -/
private theorem array_eq_singleton {α : Type} (a : Array α) (x : α)
    (h_one : a.size = 1) (h_zero : a[0]? = some x) : a = #[x] := by
  obtain ⟨h_lt, h_eq⟩ := Array.getElem_of_getElem? h_zero
  apply Array.ext'
  have h_len : a.toList.length = 1 := by rwa [Array.length_toList]
  rw [List.eq_getElem_of_length_eq_one a.toList h_len]; simp
  exact h_eq

/-- Z-compressed proof reachability implies normal proof reachability.

    The proof:
    1. Preload preserves HeapCert (empty → preloaded, via WellFormedDB)
    2. Actions fold preserves StackCert + HeapCert
    3. Final StackCert gives DerivCert for the formula
    4. DerivCert bridges to NormalProofReachable -/
theorem z_compressed_to_normal_reachable (db : DB) (label : String) (fmla : Formula)
    (stack : Array Formula)
    (h_wf : WellFormedDB db)
    (h_reach : ZCompressedProofReachable db label fmla stack)
    (h_stack_one : stack.size = 1)
    (h_stack_fmla : stack[0]? = some fmla) :
    NormalProofReachable db label fmla stack := by
  obtain ⟨preloads, actions, pr_preload, pr_final, h_preload, h_actions, h_stack⟩ := h_reach
  -- Canonical init
  let pr_init : ProofState :=
    ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .normal⟩
  -- 1. Establish initial certs
  have h_sc_init : StackCert db pr_preload.stack := by
    have h_stack_eq := preload_fold_preserves_stack db preloads pr_init pr_preload h_preload
    rw [h_stack_eq]; exact StackCert_empty db
  have h_hc_init : HeapCert db pr_preload.heap :=
    preload_fold_preserves_heapCert db preloads pr_init pr_preload
      h_preload (HeapCert_empty db) h_wf
  -- 2. Actions preserve certs
  have ⟨h_sc_final, _⟩ :=
    execStepSave_fold_preserves_certs db actions pr_preload pr_final
      h_actions h_sc_init h_hc_init
  -- 3. Extract DerivCert from final stack
  have h_fmla_final : pr_final.stack[0]? = some fmla := h_stack ▸ h_stack_fmla
  have h_cert : DerivCert db fmla :=
    compressed_final_cert db pr_final h_sc_final fmla h_fmla_final
  -- 4. stack = #[fmla], then bridge to NormalProofReachable
  rw [array_eq_singleton stack fmla h_stack_one h_stack_fmla]
  exact DerivCert_to_NormalProofReachable db label fmla fmla h_cert

/-! ### Part 15i: Updated Proof Reachable + Unified Dispatcher -/

/-- Extended proof execution mode: normal, compressed (save-free), or Z-compressed. -/
inductive ProofReachableZ (db : DB) (label : String) (fmla : Formula)
    (stack : Array Formula) : Prop where
  | normal :
      NormalProofReachable db label fmla stack → ProofReachableZ db label fmla stack
  | compressed :
      CompressedProofReachable db label fmla stack → ProofReachableZ db label fmla stack
  | zcompressed :
      ZCompressedProofReachable db label fmla stack → ProofReachableZ db label fmla stack

/-- **UNIFIED THEOREM (Z-AWARE)**: Prefix provability for any reachable proof.

    Covers normal, save-free compressed, and Z-compressed proofs.
    The Z-compressed case requires `WellFormedDB` (for preload HeapCert),
    `stack.size = 1`, and `stack[0]? = some fmla`. -/
theorem prefix_provable_any_proof_z
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none)
    (h_s_ok : s.db.error? = none)
    (h_wf : WellFormedDB s.db)
    (h_reach : ProofReachableZ s.db pr.label pr.fmla pr.stack)
    (h_stack_one : pr.stack.size = 1)
    (h_stack_fmla : pr.stack[0]? = some pr.fmla) :
    ∃ (Γ_final : Spec.Database) (spec_fr : Spec.Frame),
      toDatabase (s.finishProof pr).db = some Γ_final ∧
      toFrame s.db s.db.frame = some spec_fr ∧
      Spec.Provable Γ_final spec_fr (toExpr pr.fmla) := by
  cases h_reach with
  | normal h =>
    exact prefix_provable_normal_proof s pr h_success h_s_ok h_wf h h_stack_one h_stack_fmla
  | compressed h =>
    exact prefix_provable_compressed_proof s pr h_success h_s_ok h_wf h h_stack_one h_stack_fmla
  | zcompressed h =>
    exact prefix_provable_normal_proof s pr h_success h_s_ok h_wf
      (z_compressed_to_normal_reachable s.db pr.label pr.fmla pr.stack h_wf h
        h_stack_one h_stack_fmla)
      h_stack_one h_stack_fmla

/-! ## Part 16: Parser Bridge for Compressed Proofs

Close the `h_reach : ProofReachableZ` gap by deriving reachability from
actual parser execution. The key insight: `applyCompressedActions` (which the
parser uses) and `execStepSave` (which `ZCompressedProofReachable` uses) are
the same function for non-unknown actions.

**Architecture:**
- 16a: Convert `CompressedAction` → `StepSaveAction`, prove fold equivalence
- 16b: Bridge from parser data to `ZCompressedProofReachable`
- 16c: `preloadMandatoryHyps` property lemmas (stack, HeapCert)
- 16d: Full bridge from `preloadMandatoryHyps` + user preloads + compressed actions
-/

/-! ### Part 16a: CompressedAction ↔ StepSaveAction Bridge -/

/-- Convert a `CompressedAction` to a `StepSaveAction`.
    The `.unknown` case maps to `.save` (arbitrary default; unreachable
    when the no-unknown precondition holds). -/
def compressedToStepSave : ParserState.CompressedAction → StepSaveAction
  | .step n => .step n
  | .save => .save
  | .unknown => .save

/-- `applyCompressedActions` equals `execStepSave` fold when no unknowns are present.

    This is the key bridge: the parser's `applyCompressedActions` (which handles
    `.step`, `.save`, and `.unknown`) agrees with `execStepSave` fold (which only
    handles `.step` and `.save`) when the action list contains no `.unknown` entries. -/
theorem applyCA_eq_execSS_fold
    (db : DB) (pr : ProofState)
    (cacts : List ParserState.CompressedAction)
    (h_no_unk : ∀ a ∈ cacts, a ≠ ParserState.CompressedAction.unknown) :
    ParserState.applyCompressedActions db pr cacts =
    (cacts.map compressedToStepSave).foldlM (fun p a => execStepSave db p a) pr := by
  induction cacts generalizing pr with
  | nil => simp [ParserState.applyCompressedActions, List.foldlM]
  | cons act rest ih =>
    have h_rest_no_unk : ∀ a ∈ rest, a ≠ ParserState.CompressedAction.unknown :=
      fun a ha => h_no_unk a (List.mem_cons_of_mem _ ha)
    simp only [ParserState.applyCompressedActions, List.foldlM_cons, List.map_cons,
               bind, Except.bind]
    cases act with
    | step n =>
      simp only [compressedToStepSave, execStepSave]
      cases db.stepProof pr n with
      | error e => rfl
      | ok pr' => exact ih pr' h_rest_no_unk
    | save =>
      simp only [compressedToStepSave, execStepSave]
      cases pr.save with
      | error e => rfl
      | ok pr' =>
        simp only [pure, Except.pure]
        exact ih pr' h_rest_no_unk
    | unknown =>
      exfalso; exact h_no_unk .unknown (by simp) rfl

/-- `applyCompressedActions` distributes over list concatenation. -/
theorem applyCA_append
    (db : DB) (pr : ProofState)
    (acts₁ acts₂ : List ParserState.CompressedAction) :
    ParserState.applyCompressedActions db pr (acts₁ ++ acts₂) =
    (ParserState.applyCompressedActions db pr acts₁).bind
      (fun mid => ParserState.applyCompressedActions db mid acts₂) := by
  simp only [ParserState.applyCompressedActions, List.foldlM_append]; rfl

/-- Composing two `applyCompressedActions` calls: if both succeed, the
    concatenated action list also succeeds with the same final state. -/
theorem applyCA_compose_ok
    (db : DB) (pr₁ pr₂ pr₃ : ProofState)
    (acts₁ acts₂ : List ParserState.CompressedAction)
    (h₁ : ParserState.applyCompressedActions db pr₁ acts₁ = .ok pr₂)
    (h₂ : ParserState.applyCompressedActions db pr₂ acts₂ = .ok pr₃) :
    ParserState.applyCompressedActions db pr₁ (acts₁ ++ acts₂) = .ok pr₃ := by
  simp only [ParserState.applyCompressedActions, List.foldlM_append] at *
  simp only [bind, Except.bind, h₁, h₂]

/-! ### Part 16b: Parser Data → ZCompressedProofReachable -/

/-- Bridge from parser execution data to `ZCompressedProofReachable`.

    Given that preloads via `DB.preload` succeeded and `applyCompressedActions`
    succeeded with no unknown actions, construct `ZCompressedProofReachable`.
    The conversion uses `applyCA_eq_execSS_fold` to translate the
    `applyCompressedActions` fold into an `execStepSave` fold. -/
theorem parser_compressed_to_z_reachable
    (db : DB) (label : String) (fmla : Formula)
    (preloads : List String)
    (cacts : List ParserState.CompressedAction)
    (pr_preload pr_final : ProofState)
    (h_preload : preloads.foldlM (DB.preload db)
      ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .normal⟩ = .ok pr_preload)
    (h_actions : ParserState.applyCompressedActions db pr_preload cacts = .ok pr_final)
    (h_no_unk : ∀ a ∈ cacts, a ≠ ParserState.CompressedAction.unknown) :
    ZCompressedProofReachable db label fmla pr_final.stack := by
  refine ⟨preloads, cacts.map compressedToStepSave, pr_preload, pr_final,
    h_preload, ?_, rfl⟩
  rwa [← applyCA_eq_execSS_fold db pr_preload cacts h_no_unk]

/-! ### Part 16c: preloadMandatoryHyps Property Lemmas

The parser calls `preloadMandatoryHyps` (a `for` loop over `pr.frame.hyps`)
to populate the heap before compressed proof execution. We prove this preserves
stack and establishes `HeapCert`. -/

/-- `preloadMandatoryHyps` preserves the stack (it only modifies the heap). -/
theorem preloadMandatoryHyps_preserves_stack
    (db : DB) (pr pr' : ProofState)
    (h_ok : db.preloadMandatoryHyps pr = .ok pr') :
    pr'.stack = pr.stack := by
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
        acc'.stack = acc.stack from
    h_aux _ _ _ h_for_list
  intro labels
  induction labels with
  | nil =>
    intro acc acc' h; simp at h; cases h; rfl
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

/-- `preloadMandatoryHyps` establishes `HeapCert` on the resulting heap.

    Each mandatory hypothesis label in `pr.frame.hyps` is looked up as `.hyp`,
    yielding formula `f`. `hyp_derivcert` gives `DerivCert db f`, and
    `HeapCert_push_fmla` extends the heap certificate. -/
theorem preloadMandatoryHyps_heapCert
    (db : DB) (pr pr' : ProofState)
    (h_ok : db.preloadMandatoryHyps pr = .ok pr')
    (h_hc : HeapCert db pr.heap)
    (h_frame : pr.frame = db.frame)
    (h_wf : WellFormedDB db) :
    HeapCert db pr'.heap := by
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
        (∀ l ∈ labels, l ∈ db.frame.hyps) →
        forIn labels acc body = Except.ok acc' →
        HeapCert db acc.heap →
        HeapCert db acc'.heap from
    h_aux pr.frame.hyps.toList pr pr'
      (fun l h_mem => h_frame ▸ Array.mem_toList_iff.mp h_mem)
      h_for_list h_hc
  intro labels
  induction labels with
  | nil =>
    intro acc acc' _ h hc; simp at h; cases h; exact hc
  | cons lbl rest ih =>
    intro acc acc' h_in_frame h_fold h_hc_acc
    simp [List.forIn_cons, body] at h_fold
    cases h_find : db.find? lbl with
    | none => simp [h_find, Bind.bind, Except.bind] at h_fold
    | some obj =>
      cases obj with
      | hyp ess f origin =>
        simp [h_find, Bind.bind, Except.bind, pure, Except.pure] at h_fold
        have h_lbl_in : lbl ∈ db.frame.hyps :=
          h_in_frame lbl (List.Mem.head _)
        have h_cert : DerivCert db f :=
          hyp_derivcert db lbl ess f origin h_find h_lbl_in h_wf
        have h_hc_new : HeapCert db (acc.pushHeap (.fmla f)).heap := by
          simp [ProofState.pushHeap]
          exact HeapCert_push_fmla db acc.heap f h_hc_acc h_cert
        exact ih _ _
          (fun l h_mem => h_in_frame l (List.mem_cons_of_mem _ h_mem))
          h_fold h_hc_new
      | const _ => simp [h_find, Bind.bind, Except.bind] at h_fold
      | var _ => simp [h_find, Bind.bind, Except.bind] at h_fold
      | assert _ _ _ => simp [h_find, Bind.bind, Except.bind] at h_fold

/-! ### Part 16d: Full Compressed Proof Bridge

Connect the actual parser compressed flow to `ProofReachableZ`.

The parser's compressed proof execution has two preload sub-phases:
1. `preloadMandatoryHyps`: bulk-preloads all mandatory hypothesis formulas
2. User-specified preloads: individual `DB.preload` calls for each label token

After preloading, compressed tokens are decoded and applied via
`applyCompressedActions`. We bridge the combined preloaded state to
`ZCompressedProofReachable` by showing the preloaded state has HeapCert,
empty stack, and correct frame. -/

/-- Full compressed proof bridge: from `preloadMandatoryHyps` + user preloads +
    `applyCompressedActions` to `ZCompressedProofReachable`.

    Combines mandatory hyps preload with user-specified preloads, then
    bridges compressed actions to the `execStepSave` fold model. -/
theorem compressed_full_bridge
    (db : DB) (label : String) (fmla : Formula)
    (pr_init pr_mand pr_preload pr_final : ProofState)
    (user_preloads : List String)
    (all_cacts : List ParserState.CompressedAction)
    -- Initial state (from resumeThm)
    (h_init : pr_init = ⟨⟨0,0⟩, label, fmla, db.frame, #[], #[], .start⟩)
    -- preloadMandatoryHyps succeeded
    (h_mand : db.preloadMandatoryHyps pr_init = .ok pr_mand)
    -- User preloads succeeded
    (h_user : user_preloads.foldlM (DB.preload db) pr_mand = .ok pr_preload)
    -- Compressed actions succeeded with no unknowns
    (h_actions : ParserState.applyCompressedActions db pr_preload all_cacts = .ok pr_final)
    (h_no_unk : ∀ a ∈ all_cacts, a ≠ ParserState.CompressedAction.unknown)
    -- WellFormedDB for HeapCert
    (h_wf : WellFormedDB db)
    -- Stack and formula conditions at finish
    (h_stack_one : pr_final.stack.size = 1)
    (h_stack_fmla : pr_final.stack[0]? = some fmla) :
    ProofReachableZ db label fmla pr_final.stack := by
  -- Establish initial properties after mandatory preload
  have h_init_frame : pr_init.frame = db.frame := by subst h_init; rfl
  have h_init_stack : pr_init.stack = #[] := by subst h_init; rfl
  have h_init_heap : pr_init.heap = #[] := by subst h_init; rfl
  -- Properties after mandatory preload
  have h_mand_stack : pr_mand.stack = pr_init.stack :=
    preloadMandatoryHyps_preserves_stack db pr_init pr_mand h_mand
  have h_mand_frame : pr_mand.frame = pr_init.frame :=
    (preloadMandatoryHyps_ok_preserves_core db pr_init pr_mand h_mand).2
  have h_mand_hc : HeapCert db pr_mand.heap :=
    preloadMandatoryHyps_heapCert db pr_init pr_mand h_mand
      (by rw [h_init_heap]; exact HeapCert_empty db) h_init_frame h_wf
  -- Properties after user preloads
  have h_pre_stack : pr_preload.stack = pr_mand.stack :=
    preload_fold_preserves_stack db user_preloads pr_mand pr_preload h_user
  have h_pre_frame : pr_preload.frame = pr_mand.frame :=
    preload_fold_preserves_frame db user_preloads pr_mand pr_preload h_user
  have h_pre_hc : HeapCert db pr_preload.heap :=
    preload_fold_preserves_heapCert db user_preloads pr_mand pr_preload
      h_user h_mand_hc h_wf
  -- Combined properties
  have h_pre_stack_empty : pr_preload.stack = #[] := by
    rw [h_pre_stack, h_mand_stack, h_init_stack]
  -- Convert actions to StepSaveAction fold
  have h_ss_actions : (all_cacts.map compressedToStepSave).foldlM
      (fun p a => execStepSave db p a) pr_preload = .ok pr_final := by
    rwa [← applyCA_eq_execSS_fold db pr_preload all_cacts h_no_unk]
  -- Establish certs after action phase
  have ⟨h_sc_final, _⟩ :=
    execStepSave_fold_preserves_certs db (all_cacts.map compressedToStepSave)
      pr_preload pr_final h_ss_actions
      (by rw [h_pre_stack_empty]; exact StackCert_empty db)
      h_pre_hc
  -- Extract DerivCert from final stack → NormalProofReachable
  have h_cert : DerivCert db fmla :=
    compressed_final_cert db pr_final h_sc_final fmla h_stack_fmla
  have h_normal : NormalProofReachable db label fmla #[fmla] :=
    DerivCert_to_NormalProofReachable db label fmla fmla h_cert
  -- pr_final.stack = #[fmla]
  have h_stack_eq : pr_final.stack = #[fmla] :=
    array_eq_singleton pr_final.stack fmla h_stack_one h_stack_fmla
  rw [h_stack_eq]
  exact .normal h_normal

end Metamath.PrefixProvenance
