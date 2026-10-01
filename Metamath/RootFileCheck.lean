import Metamath.RunEmission
import Metamath.AssertDvInvariant

/-!
# `Verify.check` on a single root file, and the stored-`$d` invariant through the include driver

## Root-file bridge

`check fname config` resolves and reads the root file and runs the include
driver (`runDriverLoop` over pure `stepFrame` phases) before the post-check it
shares with `checkBytes`.  On a single root file the two pipelines differ in one
parser field: the driver labels the root's parser state `sourceFile := fname`,
the pure entrypoint `""`.

* `feedToken_relabelStep`: a parser step reads the label only in the two
  include-directive modes, where it enters the payload of an include request or
  of an include-path error; in every other case a step commutes with
  relabelling (`feedToken_withSource_of_not_include`).
* `feed_withSource`, `feedAll_withSource`, `checkBytesCoreAt_rel`: two runs that
  differ only in the label agree except for that payload (`DBAgreeUpToError`),
  and are equal when the unlabelled run is error-free.  Equality on error paths
  is false in general (calibration `"$[ $]"` in `Metamath.Tests.SourceCompletenessCalibration`).
* `runPureSteps_root`, `check_root_checkBytesCoreAt`: on a single root file whose
  labelled run raises no include request, the driver never pushes, and `check`
  returns exactly that run's post-checked database, in the world after the read.
  For a single root the base offset and line bookkeeping of the two pipelines
  coincide (the root pop is the identity), so the label is the only difference
  that can reach the database.
* `check_root_bridge`: if the pure entrypoint does not report an include
  request, `check` agrees with `checkBytes` up to the error payload, and equals
  it whenever `checkBytes` is error-free; `check_eq_checkBytes_of_ok` and
  `checkBytes_eq_of_check_ok` are the two success transfers.

The filesystem conditions are hypotheses about the actual IO actions at the
actual worlds: the depth gate `config.maxIncludeDepth ≠ 0`; `RootResolves`
(canonical modes: `IO.FS.realPath fname` succeeds; literal-path modes perform no
IO); and `IO.FS.readBinFile fname w₁ = .ok bytes w₂`.  Admission of the root by
the cycle/duplicate gate is proved (`gate_root`).  The driver theorems hold for
arbitrary path-resolution and file-reading actions
(`processFileSinglePassWithIO_root`) and are instantiated at the real ones.

## The stored-`$d` invariant through the driver

`AssertDv.DvStateInv` is lifted, in every mode, through `stepFrame`
(`stepFrame_maintains_dvDriverInv`: separator, live chunk, exhausted-frame
flush, pop, include-request clearing), `popExhaustedFrame`,
`flushPendingToken`, `restoreLineState`, include resolution and the whole loop
(`runDriverLoop_ok_dvDriverInv`), for arbitrary path/read actions.  Every
error-free database `check` returns satisfies `AssertDvVarsInFrame`
(`check_assertDvVarsInFrame`, no filesystem hypothesis), and the finalize-time
Boolean `$d` post-check always passes (`runDriverLoop_done_assertDvVarsInFrame`).
-/
set_option autoImplicit false

namespace Metamath.RootFileCheck

open Std (HashSet)
open Metamath.Verify
open Metamath.ParserOps (ErrorNotRequest)
open Metamath.PrefixProvability.Checker (io_bind_apply io_pure_apply)

/-! ## Source-file label independence of one parser step -/

/-- Relabel the current source file. -/
abbrev withSource (f : String) (s : ParserState) : ParserState := { s with sourceFile := f }

theorem withDB_withSource (f : String) (s : ParserState) (g : DB → DB) :
    (withSource f s).withDB g = withSource f (s.withDB g) := rfl

theorem label_withSource (f : String) (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    (withSource f s).label pos tk = withSource f (s.label pos tk) := by
  unfold ParserState.label
  split
  split <;> rfl

theorem withMath_withSource (f : String) (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (g g' : ParserState → String → ParserState)
    (hg : ∀ tk', g (withSource f s) tk' = withSource f (g' s tk')) :
    (withSource f s).withMath pos tk g = withSource f (s.withMath pos tk g') := by
  unfold ParserState.withMath
  split
  split
  · rfl
  · exact hg _

theorem djvars_loop_aux_withSource (f : String) (arr : Array String) (s : ParserState) (pos : Pos)
    (tk : String) (i : Nat) :
    ParserState.djvars_loop_aux arr (withSource f s) pos tk i
      = withSource f (ParserState.djvars_loop_aux arr s pos tk i) := by
  refine Nat.rec (motive := fun m => ∀ i (s : ParserState), arr.size - i = m →
      ParserState.djvars_loop_aux arr (withSource f s) pos tk i
        = withSource f (ParserState.djvars_loop_aux arr s pos tk i)) ?base ?step (arr.size - i) i s rfl
  · intro i s hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.djvars_loop_aux
    simp only [hi, ↓reduceDIte]
  · intro m ih i s hs
    by_cases hi : i < arr.size
    · have hs' : arr.size - (i + 1) = m := by
        simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
      rw [ParserState.djvars_loop_aux, ParserState.djvars_loop_aux]
      simp only [hi, ↓reduceDIte]
      split
      · rfl
      · rw [withDB_withSource]
        exact ih (i + 1) _ hs'
    · unfold ParserState.djvars_loop_aux
      simp only [hi, ↓reduceDIte]

theorem djvars_loop_withSource (f : String) (arr : Array String) (s : ParserState) (pos : Pos)
    (tk : String) :
    ParserState.djvars_loop arr (withSource f s) pos tk
      = withSource f (ParserState.djvars_loop arr s pos tk) := by
  unfold ParserState.djvars_loop
  cases h : s.db.djvarsScopeViolation? tk with
  | some err => rfl
  | none => exact djvars_loop_aux_withSource f arr s pos tk 0

theorem sym_withSource (f : String) (s : ParserState) (pos : Pos) (tk : ByteSlice) (o : String → Object) :
    (withSource f s).sym pos tk o = withSource f (s.sym pos tk o) := by
  unfold ParserState.sym
  split
  · rfl
  · exact withMath_withSource f s pos tk _ _ (fun _ => rfl)

theorem withAt_withSource (f : String) (l : String) (g : Unit → ParserState) :
    ParserState.withAt l (fun u => withSource f (g u)) = withSource f (ParserState.withAt l g) := by
  unfold ParserState.withAt
  dsimp only
  cases h : (g ()).db.error? with
  | none => rfl
  | some it =>
    obtain ⟨e, idx⟩ := it
    cases e <;> rfl


theorem feedTokens_withSource (f : String) (s : ParserState) (arr : Array Verify.Sym) (p : TokensParser) :
    (withSource f s).feedTokens arr p = withSource f (s.feedTokens arr p) := by
  obtain ⟨k, pos, l⟩ := p
  unfold ParserState.feedTokens
  dsimp only
  rw [← withAt_withSource]
  congr 1
  funext u
  cases k <;> dsimp only [Id.run] <;> repeat' split
  all_goals rfl


theorem feedProof_go_withSource (f : String) (s : ParserState) (tk : ByteSlice) (pr : ProofState) :
    ParserState.feedProof.go (withSource f s) tk pr = ParserState.feedProof.go s tk pr := rfl

theorem feedProof_withSource (f : String) (s : ParserState) (tk : ByteSlice) (pr : ProofState) :
    (withSource f s).feedProof tk pr = withSource f (s.feedProof tk pr) := by
  unfold ParserState.feedProof
  rw [← withAt_withSource]
  congr 1
  funext u
  rw [feedProof_go_withSource]
  split <;> rfl

theorem finishProof_withSource (f : String) (s : ParserState) (pr : ProofState) :
    (withSource f s).finishProof pr = withSource f (s.finishProof pr) := by
  obtain ⟨pos, l, fmla, fr, heap, stack, ptp, inc⟩ := pr
  unfold ParserState.finishProof
  dsimp only
  rw [← withAt_withSource]
  congr 1
  funext u
  dsimp only [Id.run]
  repeat' split
  all_goals rfl

/-- Outside the two include-directive modes a parser step neither reads nor
writes the source-file label. -/
theorem feedToken_withSource_of_not_include (f : String) (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (h1 : ∀ r q, s.tokp ≠ .includePath r q) (h2 : ∀ r q p, s.tokp ≠ .includeClose r q p) :
    (withSource f s).feedToken pos tk = withSource f (s.feedToken pos tk) := by
  unfold ParserState.feedToken
  dsimp only
  cases h_tokp : s.tokp with
  | includePath r q => exact absurd h_tokp (h1 r q)
  | includeClose r q p => exact absurd h_tokp (h2 r q p)
  | _ =>
    dsimp only
    repeat' split
    all_goals first
      | rfl
      | exact label_withSource f s _ _
      | (rw [sym_withSource]; rfl)
      | exact feedTokens_withSource f s _ _
      | exact finishProof_withSource f { s with tokp := default } _
      | exact feedProof_withSource f { s with tokp := default } _ _
      | exact withMath_withSource f s _ tk _ _ (fun tk' => djvars_loop_withSource f _ s _ tk')
      | (refine withMath_withSource f s _ tk _ _ (fun tk' => ?_)
         dsimp only [Id.run]
         repeat' split
         all_goals rfl)

/-- Whether include-path normalization succeeds, and with which path, does not
depend on the source-file label (only error payloads mention it). -/
theorem normalizeIncludePath_cases (lit : Bool) (sf sf' raw : String) :
    (∃ p, ParserState.normalizeIncludePath lit sf raw = .ok p ∧
        ParserState.normalizeIncludePath lit sf' raw = .ok p) ∨
    (∃ e e', ParserState.normalizeIncludePath lit sf raw = .error e ∧
        ParserState.normalizeIncludePath lit sf' raw = .error e') := by
  unfold ParserState.normalizeIncludePath
  dsimp only
  by_cases h1 : raw.isEmpty = true
  · simp only [h1, ↓reduceIte]
    exact Or.inr ⟨_, _, rfl, rfl⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : lit = true
    · simp only [h2, ↓reduceIte]
      exact Or.inl ⟨_, rfl, rfl⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      generalize (if raw.startsWith "./" = true then (raw.drop 2).toString else raw) = nm
      by_cases h3 : nm.isEmpty = true
      · simp only [h3, ↓reduceIte]
        exact Or.inr ⟨_, _, rfl, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        exact Or.inl ⟨_, rfl, rfl⟩

/-- The three possible relations between a step from `withSource f s` (`A`) and
the same step from `s` (`B`): equal up to the label; both the same include
request (payloads carry each side's label); or both the same include-path error
(evidence may carry each side's label). -/
def RelabelStep (f : String) (s A B : ParserState) : Prop :=
  A = withSource f B ∨
  (∃ resume path, B = s.requestInclude resume path ∧
      A = (withSource f s).requestInclude resume path) ∨
  (∃ ipos ev ev', B = s.mkErrorFromEvidence ipos ev ∧
      A = (withSource f s).mkErrorFromEvidence ipos ev')

/-- **One parser step under relabelling** (every mode, every state). -/
theorem feedToken_relabelStep (f : String) (s : ParserState) (pos : Nat) (tk : ByteSlice) :
    RelabelStep f s ((withSource f s).feedToken pos tk) (s.feedToken pos tk) := by
  by_cases hI : (∀ r q, s.tokp ≠ .includePath r q) ∧ (∀ r q p, s.tokp ≠ .includeClose r q p)
  · exact Or.inl (feedToken_withSource_of_not_include f s pos tk hI.1 hI.2)
  · unfold ParserState.feedToken
    dsimp only
    cases h_tokp : s.tokp with
    | includePath resume q =>
        dsimp only
        split
        · exact Or.inl rfl
        · split
          · split <;> exact Or.inl rfl
          · split
            · exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl⟩)
            · rcases normalizeIncludePath_cases s.db.config.literalIncludePaths f s.sourceFile
                  (ParserState.includePathFromToken tk).fst with ⟨p, h1, h2⟩ | ⟨e, e', h1, h2⟩
              · rw [h1, h2]
                dsimp only
                split
                · exact Or.inr (Or.inl ⟨resume, p, rfl, rfl⟩)
                · exact Or.inl rfl
              · rw [h1, h2]
                exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl⟩)
    | includeClose resume q path =>
        dsimp only
        split
        · exact Or.inl rfl
        · split
          · split <;> exact Or.inl rfl
          · split
            · exact Or.inr (Or.inl ⟨resume, path, rfl, rfl⟩)
            · exact Or.inl rfl
    | _ => exact absurd ⟨fun r q h => by simp [h_tokp] at h, fun r q p h => by simp [h_tokp] at h⟩ hI

/-! ## Byte-loop equations -/

/-- The pending token that whitespace at index `i` terminates, exactly as
`ParserState.feed` assembles and flushes it. -/
def flushOld (s : ParserState) (base : Nat) (arr : ByteArray) (i : Nat) :
    ParserState.OldToken → ParserState
  | .this off => s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
  | .old base' off arr' => s.feedToken (base' + off)
      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))

/-- What `feed` does after a flush at index `i`: freeze on error, else continue. -/
def continueAfter (base : Nat) (arr : ByteArray) (i : Nat) (s1 : ParserState) : ParserState :=
  if let some ⟨e, _⟩ := s1.db.error? then
    { s1 with db := { s1.db with error? := some ⟨e, i+1⟩ } }
  else s1.feed base arr (i+1) .ws

theorem feed_eof (base : Nat) (arr : ByteArray) (i : Nat) (rs : ParserState.FeedState)
    (s : ParserState) (hi : ¬ i < arr.size) :
    s.feed base arr i rs = { s with charp :=
      match rs with
      | .ws => .ws
      | .token ot =>
        match ot with
        | .this off => .token base (ByteSliceT.mk arr off)
        | .old base off arr' => .token base (ByteSliceT.mk (arr' ++ arr) off) } := by
  conv => lhs; unfold ParserState.feed
  simp only [hi, ↓reduceDIte]
  rfl

theorem feed_ws_ws (base : Nat) (arr : ByteArray) (i : Nat) (s : ParserState)
    (hi : i < arr.size) (hw : s.db.config.isWhitespace arr[i] = true) :
    s.feed base arr i .ws = (s.updateLine (base + i) arr[i]).feed base arr (i+1) .ws := by
  conv => lhs; unfold ParserState.feed
  simp only [hi, ↓reduceDIte, hw, if_true]

theorem feed_ws_token (base : Nat) (arr : ByteArray) (i : Nat) (s : ParserState)
    (ot : ParserState.OldToken)
    (hi : i < arr.size) (hw : s.db.config.isWhitespace arr[i] = true) :
    s.feed base arr i (.token ot) =
      continueAfter base arr i ((flushOld s base arr i ot).updateLine (base + i) arr[i]) := by
  conv => lhs; unfold ParserState.feed
  simp only [hi, ↓reduceDIte, hw, if_true]
  cases ot <;> rfl

theorem feed_nonws (base : Nat) (arr : ByteArray) (i : Nat) (s : ParserState)
    (rs : ParserState.FeedState)
    (hi : i < arr.size) (hw : ¬ s.db.config.isWhitespace arr[i] = true) :
    s.feed base arr i rs =
      s.feed base arr (i+1) (if let .ws := rs then .token (.this i) else rs) := by
  have hw' : s.db.config.isWhitespace arr[i] = false := by simpa using hw
  conv => lhs; unfold ParserState.feed
  simp only [hi, ↓reduceDIte, hw', Bool.false_eq_true, if_false]
  cases rs <;> rfl

/-! ## Driver-step and EOF equations -/

theorem runPureSteps_of_done (st st' : IncludeDriverState) (h : stepFrame st = .done st') :
    runPureSteps st = .done st' := by
  unfold runPureSteps
  split <;> simp_all

theorem runPureSteps_of_fed_err (st st' : IncludeDriverState) (h : stepFrame st = .fed st')
    (h_err : st'.parser.db.error? ≠ none) :
    runPureSteps st = .stopped st' := by
  unfold runPureSteps
  split
  · simp_all
  · simp_all
  · rename_i st'' h2
    rw [h] at h2
    cases h2
    have : st'.parser.db.error = true := by simpa [DB.error, Option.isSome_iff_ne_none] using h_err
    simp [this]

theorem runPureSteps_of_fed_ok (st st' : IncludeDriverState) (h : stepFrame st = .fed st')
    (h_err : st'.parser.db.error? = none) :
    runPureSteps st = runPureSteps st' := by
  conv => lhs; unfold runPureSteps
  split
  · simp_all
  · simp_all
  · rename_i st'' h2
    rw [h] at h2
    cases h2
    have : st'.parser.db.error = false := by simp [DB.error, h_err]
    simp [this]

theorem done_of_error (s : ParserState) (base : Nat) (h : s.db.error? ≠ none) :
    s.done base = s.db := by
  have h' : s.db.error = true := by simpa [DB.error, Option.isSome_iff_ne_none] using h
  simp only [ParserState.done, Id.run, h', if_true]
  rfl

theorem done_withSource_ws (f : String) (s : ParserState) (base : Nat) (h : s.charp = .ws) :
    ({ s with sourceFile := f } : ParserState).done base = s.done base := by
  obtain ⟨db, tokp, charp, line, linepos, sf⟩ := s
  dsimp only at h
  subst h
  rfl

theorem done_flush (s : ParserState) (base : Nat) (h : s.db.error? = none) :
    (flushPendingToken s).done base = s.done base := by
  unfold flushPendingToken
  cases hc : s.charp with
  | ws => rfl
  | token pos tk =>
      dsimp only
      have h0 : s.db.error = false := by simp [DB.error, h]
      simp only [ParserState.done, Id.run, h0, hc, Bool.false_eq_true, if_false]
      by_cases h1 : (s.feedToken pos tk.toSlice).db.error = true
      · simp only [h1, if_true]
      · simp only [h1, Bool.false_eq_true, if_false]
        rfl



/-! ## Runs that differ only in the source-file label -/

theorem updateLine_withSource (f : String) (s : ParserState) (i : Nat) (c : UInt8) :
    (withSource f s).updateLine i c = withSource f (s.updateLine i c) := by
  unfold ParserState.updateLine
  split <;> rfl

/-- A parser state with its source-file label and error payload (interrupt and
evidence) erased. -/
def eraseErr (s : ParserState) : ParserState :=
  { s with sourceFile := "", db := { s.db with error? := none, errorEvidence? := none } }

theorem eraseErr_updateLine (s : ParserState) (i : Nat) (c : UInt8) :
    eraseErr (s.updateLine i c) = (eraseErr s).updateLine i c := by
  unfold ParserState.updateLine
  split <;> rfl

/-- Two parser states agree except for the source-file label and the error
payload: same error status and same include-request status. -/
def AgreeUpToError (A B : ParserState) : Prop :=
  eraseErr A = eraseErr B ∧ (A.db.error? = none ↔ B.db.error? = none) ∧
    (ErrorNotRequest A.db.error? ↔ ErrorNotRequest B.db.error?)

theorem agreeUpToError_withSource (f : String) (B : ParserState) : AgreeUpToError (withSource f B) B :=
  ⟨rfl, Iff.rfl, Iff.rfl⟩

theorem agreeUpToError_updateLine {A B : ParserState} (h : AgreeUpToError A B) (i : Nat) (c : UInt8) :
    AgreeUpToError (A.updateLine i c) (B.updateLine i c) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [eraseErr_updateLine, eraseErr_updateLine, h1], ?_, ?_⟩
  · simpa only [ParserState.updateLine_db] using h2
  · simpa only [ParserState.updateLine_db] using h3

/-- Whether an interrupt is an include request does not depend on its index. -/
theorem errorNotRequest_some_idx (e : Error) (k k' : Nat) :
    ErrorNotRequest (some ⟨e, k⟩) ↔ ErrorNotRequest (some ⟨e, k'⟩) := by
  constructor
  · intro h sf pf idx hx
    injection hx with hx
    injection hx with he _
    exact h sf pf k (by rw [he])
  · intro h sf pf idx hx
    injection hx with hx
    injection hx with he _
    exact h sf pf k' (by rw [he])

/-- The three `RelabelStep` outcomes collapse to: identical up to the label, or both
erroneous and loosely agreeing. -/
theorem relabelStep_cases {f : String} {s A B : ParserState} (h : RelabelStep f s A B) :
    A = withSource f B ∨ (AgreeUpToError A B ∧ A.db.error? ≠ none ∧ B.db.error? ≠ none) := by
  rcases h with h | ⟨resume, path, hB, hA⟩ | ⟨ipos, ev, ev', hB, hA⟩
  · exact Or.inl h
  · subst hA hB
    refine Or.inr ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [ParserState.requestInclude, ErrorNotRequest]
  · subst hA hB
    refine Or.inr ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [ParserState.mkErrorFromEvidence, ParserState.withDB, DB.mkErrorFromEvidence,
        DB.mkErrorWithEvidence, ErrorNotRequest]

theorem flushOld_relabelStep (f : String) (s : ParserState) (base : Nat) (arr : ByteArray) (i : Nat)
    (ot : ParserState.OldToken) :
    RelabelStep f s (flushOld (withSource f s) base arr i ot) (flushOld s base arr i ot) := by
  cases ot <;> exact feedToken_relabelStep f s _ _

/-- The relation a label change leaves between two byte-loop results. -/
def RelabelRel (f : String) (A B : ParserState) : Prop :=
  AgreeUpToError A B ∧ (B.db.error? = none → A = withSource f B)

theorem relabelRel_withSource (f : String) (B : ParserState) : RelabelRel f (withSource f B) B :=
  ⟨agreeUpToError_withSource f B, fun _ => rfl⟩

theorem relabelRel_of_eq {f : String} {A B : ParserState} (h : A = withSource f B) : RelabelRel f A B := by
  subst h
  exact relabelRel_withSource f B

theorem continueAfter_rel (f : String) (base : Nat) (arr : ByteArray) (i : Nat)
    (s1A s1B : ParserState)
    (h : s1A = withSource f s1B ∨ (AgreeUpToError s1A s1B ∧ s1A.db.error? ≠ none ∧ s1B.db.error? ≠ none))
    (ih : ∀ s' : ParserState, s'.db.error? = none →
      RelabelRel f ((withSource f s').feed base arr (i+1) .ws) (s'.feed base arr (i+1) .ws)) :
    RelabelRel f (continueAfter base arr i s1A) (continueAfter base arr i s1B) := by
  rcases h with h | ⟨hL, hA, hB⟩
  · subst h
    unfold continueAfter
    cases h_e : s1B.db.error? with
    | some it =>
        obtain ⟨e, k⟩ := it
        exact relabelRel_of_eq rfl
    | none =>
        exact ih s1B h_e
  · obtain ⟨itA, h_eA⟩ := Option.ne_none_iff_exists'.mp hA
    obtain ⟨itB, h_eB⟩ := Option.ne_none_iff_exists'.mp hB
    obtain ⟨eA, kA⟩ := itA
    obtain ⟨eB, kB⟩ := itB
    unfold continueAfter
    rw [h_eA, h_eB]
    refine ⟨⟨hL.1, ?_, ?_⟩, ?_⟩
    · simp
    · show ErrorNotRequest (some ⟨eA, i+1⟩) ↔ ErrorNotRequest (some ⟨eB, i+1⟩)
      rw [errorNotRequest_some_idx eA (i+1) kA, errorNotRequest_some_idx eB (i+1) kB,
        ← h_eA, ← h_eB]
      exact hL.2.2
    · intro h_none
      simp at h_none

/-- **Byte loop under a label change.**  From an error-free state, relabelling
the source file changes the byte loop's result only in the label and, on an
include-path error or include request, in the error payload; an error-free
result is exactly the relabelled one. -/
theorem feed_withSource (f : String) (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState) (h_err0 : s.db.error? = none) :
    RelabelRel f ((withSource f s).feed base arr i rs) (s.feed base arr i rs) := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState), s.db.error? = none →
      arr.size - i = m →
      RelabelRel f ((withSource f s).feed base arr i rs) (s.feed base arr i rs))
    ?base ?step (arr.size - i) i rs s h_err0 rfl
  · intro i rs s _ hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    rw [feed_eof base arr i rs _ hi, feed_eof base arr i rs _ hi]
    exact relabelRel_of_eq rfl
  · intro m ih i rs s h_err0 hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        simp [hz] at hs
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    by_cases hw : s.db.config.isWhitespace arr[i] = true
    · cases rs with
      | ws =>
          rw [feed_ws_ws base arr i (withSource f s) hi hw, feed_ws_ws base arr i s hi hw,
            updateLine_withSource]
          exact ih (i + 1) .ws _ (by simpa using h_err0) hs'
      | token ot =>
          rw [feed_ws_token base arr i (withSource f s) ot hi hw, feed_ws_token base arr i s ot hi hw]
          apply continueAfter_rel f base arr i
          · rcases relabelStep_cases (flushOld_relabelStep f s base arr i ot) with h | ⟨hL, hA, hB⟩
            · left
              rw [h, updateLine_withSource]
            · right
              refine ⟨agreeUpToError_updateLine hL _ _, ?_, ?_⟩
              · simpa only [ParserState.updateLine_db] using hA
              · simpa only [ParserState.updateLine_db] using hB
          · intro s' h'
            exact ih (i + 1) .ws s' h' hs'
    · rw [feed_nonws base arr i (withSource f s) rs hi hw, feed_nonws base arr i s rs hi hw]
      cases rs <;> exact ih (i + 1) _ s h_err0 hs'

theorem feedAll_withSource (f : String) (s : ParserState) (base : Nat) (arr : ByteArray)
    (h_err0 : s.db.error? = none) :
    RelabelRel f ((withSource f s).feedAll base arr) (s.feedAll base arr) := by
  cases h : s.charp with
  | ws =>
      have hA : (withSource f s).feedAll base arr = (withSource f s).feed base arr 0 .ws := by
        simp only [ParserState.feedAll, h]
      have hB : s.feedAll base arr = s.feed base arr 0 .ws := by
        simp only [ParserState.feedAll, h]
      rw [hA, hB]
      exact feed_withSource f base arr 0 .ws s h_err0
  | token base' tk =>
      have hA : (withSource f s).feedAll base arr = (withSource f { s with charp := default }).feed
          base arr 0 (.token (.old base' tk.start tk.byteArray)) := by
        simp only [ParserState.feedAll, h]
      have hB : s.feedAll base arr = ({ s with charp := default } : ParserState).feed
          base arr 0 (.token (.old base' tk.start tk.byteArray)) := by
        simp only [ParserState.feedAll, h]
      rw [hA, hB]
      exact feed_withSource f base arr 0 _ { s with charp := default } h_err0


/-! ## The pure pipeline under a label change -/

/-- Two databases agree except for the error payload (interrupt and evidence):
equal once those are erased, with the same error status and the same
include-request status. -/
def DBAgreeUpToError (d₁ d₂ : DB) : Prop :=
  { d₁ with error? := none, errorEvidence? := none } =
      { d₂ with error? := none, errorEvidence? := none } ∧
    (d₁.error? = none ↔ d₂.error? = none) ∧
    (ErrorNotRequest d₁.error? ↔ ErrorNotRequest d₂.error?)

theorem dbAgreeUpToError_refl (d : DB) : DBAgreeUpToError d d := ⟨rfl, Iff.rfl, Iff.rfl⟩

theorem dbAgreeUpToError_of_agree {A B : ParserState} (h : AgreeUpToError A B) : DBAgreeUpToError A.db B.db :=
  ⟨congrArg ParserState.db h.1, h.2.1, h.2.2⟩

/-- The pure parser's pre-post-check database, started with source-file label
`f`.  `checkBytesCore` is the label `""`. -/
def checkBytesCoreAt (f : String) (arr : ByteArray) (config : ModeConfig) : DB :=
  ((withSource f (singlePassInitialState config)).feedAll 0 arr).done arr.size

/-- The EOF step under a label change. -/
theorem done_withSource_rel (f : String) (B : ParserState) (base : Nat)
    (hB : B.db.error? = none) :
    DBAgreeUpToError ((withSource f B).done base) (B.done base) ∧
    ((B.done base).error? = none → (withSource f B).done base = B.done base) := by
  cases hc : B.charp with
  | ws =>
      rw [done_withSource_ws f B base hc]
      exact ⟨dbAgreeUpToError_refl _, fun _ => rfl⟩
  | token pos tk =>
      rw [← done_flush (withSource f B) base hB, ← done_flush B base hB]
      have hFA : flushPendingToken (withSource f B)
          = { (withSource f B).feedToken pos tk.toSlice with charp := .ws } := by
        simp only [flushPendingToken, hc]
      have hFB : flushPendingToken B = { B.feedToken pos tk.toSlice with charp := .ws } := by
        simp only [flushPendingToken, hc]
      rw [hFA, hFB]
      rcases relabelStep_cases (feedToken_relabelStep f B pos tk.toSlice) with h | ⟨hL, hA, hBe⟩
      · rw [h]
        have h_eq : ({ withSource f (B.feedToken pos tk.toSlice) with charp := .ws } : ParserState)
            = withSource f { B.feedToken pos tk.toSlice with charp := .ws } := rfl
        rw [h_eq, done_withSource_ws f _ base rfl]
        exact ⟨dbAgreeUpToError_refl _, fun _ => rfl⟩
      · have e1 : ({ (withSource f B).feedToken pos tk.toSlice with charp := .ws } :
            ParserState).done base = ((withSource f B).feedToken pos tk.toSlice).db :=
          done_of_error _ base hA
        have e2 : ({ B.feedToken pos tk.toSlice with charp := .ws } : ParserState).done base
            = (B.feedToken pos tk.toSlice).db :=
          done_of_error _ base hBe
        rw [e1, e2]
        exact ⟨⟨congrArg ParserState.db hL.1, hL.2.1, hL.2.2⟩, fun h => absurd h hBe⟩

/-- **The pure pipeline is independent of the source-file label**, except for
the payload of an include-path error or include request (which names the
file); an error-free run is literally unchanged. -/
theorem checkBytesCoreAt_rel (f : String) (arr : ByteArray) (config : ModeConfig) :
    DBAgreeUpToError (checkBytesCoreAt f arr config) (checkBytesCoreAt "" arr config) ∧
    ((checkBytesCoreAt "" arr config).error? = none → checkBytesCoreAt f arr config = checkBytesCoreAt "" arr config) := by
  have h0 : (singlePassInitialState config).db.error? = none := rfl
  obtain ⟨hL, hS⟩ := feedAll_withSource f (singlePassInitialState config) 0 arr h0
  have hE : withSource "" (singlePassInitialState config) = singlePassInitialState config := rfl
  unfold checkBytesCoreAt
  rw [hE]
  by_cases hB : ((singlePassInitialState config).feedAll 0 arr).db.error? = none
  · rw [hS hB]
    exact done_withSource_rel f _ arr.size hB
  · have hA : ((withSource f (singlePassInitialState config)).feedAll 0 arr).db.error? ≠ none :=
      fun h => hB (hL.2.1.mp h)
    rw [done_of_error _ _ hA, done_of_error _ _ hB]
    exact ⟨dbAgreeUpToError_of_agree hL, fun h => absurd h hB⟩

/-- The post-check shared by `checkBytes` and `finalizeSinglePassResult`. -/
def postCheck (db : DB) : DB :=
  if db.error? = none then
    if (db.config.allowDuplicateFloat || db.wellFormed?) && db.assertDvVarsInFrame? then db
    else db.mkErrorFromEvidence ⟨0, 0⟩
      (.internalGate db.config.allowDuplicateFloat db.wellFormed? db.assertDvVarsInFrame?)
  else db

theorem checkBytes_eq_postCheck (arr : ByteArray) (config : ModeConfig) :
    checkBytes arr config = postCheck (checkBytesCore arr config) := rfl

theorem postCheck_of_error (d : DB) (h : d.error? ≠ none) : postCheck d = d := by
  unfold postCheck
  rw [if_neg h]

theorem errorNotRequest_of_postCheck (d : DB) (h : ErrorNotRequest (postCheck d).error?) :
    ErrorNotRequest d.error? := by
  by_cases h0 : d.error? = none
  · rw [h0]
    exact ParserOps.errorNotRequest_none
  · rwa [postCheck_of_error d h0] at h

/-- An error-free post-check result is its input: the gate passed. -/
theorem postCheck_eq_of_ok (d : DB) (h : (postCheck d).error? = none) : postCheck d = d := by
  unfold postCheck at h ⊢
  by_cases h0 : d.error? = none
  · rw [if_pos h0] at h ⊢
    by_cases hg : ((d.config.allowDuplicateFloat || d.wellFormed?) && d.assertDvVarsInFrame?) = true
    · rw [if_pos hg]
    · rw [if_neg hg] at h
      simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at h
  · rw [if_neg h0]

theorem postCheck_rel {d₁ d₂ : DB} (h : DBAgreeUpToError d₁ d₂) (hs : d₂.error? = none → d₁ = d₂) :
    DBAgreeUpToError (postCheck d₁) (postCheck d₂) ∧
    ((postCheck d₂).error? = none → postCheck d₁ = postCheck d₂) := by
  by_cases h2 : d₂.error? = none
  · rw [hs h2]
    exact ⟨dbAgreeUpToError_refl _, fun _ => rfl⟩
  · have h1 : d₁.error? ≠ none := fun h' => h2 (h.2.1.mp h')
    rw [postCheck_of_error _ h1, postCheck_of_error _ h2]
    exact ⟨h, fun h' => absurd h' h2⟩


/-! ## The driver on a single root file -/

/-- The root key computation succeeds with key `key`: literal-path modes
perform no IO and key on the name as written; canonical modes call `realPath`
successfully and key on the canonical path. -/
def RootKey (rp : String → IO System.FilePath) (fname : String) (literal : Bool)
    (w w₁ : Void IO.RealWorld) (key : String) : Prop :=
  (literal = true ∧ key = fname ∧ w₁ = w) ∨
  (literal = false ∧ ∃ p : System.FilePath, rp fname w = .ok p w₁ ∧ key = p.toString)

def rootFrame (fname key : String) (bytes : ByteArray) (d : Nat) : IncludeDriverFrame :=
  { fname := fname, canonStr := key, contents := bytes, nextDepth := d, entryScopeDepth := 0 }

theorem gate_root (fname key : String) (d : Nat) (rej : Bool) :
    includeFrameGate fname key (d + 1) rej (HashSet.emptyWithCapacity 16)
        (HashSet.emptyWithCapacity 16)
      = .ok (.admit (d + 1) ((HashSet.emptyWithCapacity 16).insert key)
          ((HashSet.emptyWithCapacity 16).insert key)) := by
  simp [includeFrameGate, Std.HashSet.contains_emptyWithCapacity]

theorem prepare_root (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fname : String) (d : Nat) (rej lit : Bool) (w w₁ w₂ : Void IO.RealWorld)
    (key : String) (bytes : ByteArray)
    (h_key : RootKey rp fname lit w w₁ key) (h_read : rf fname w₁ = .ok bytes w₂) :
    prepareIncludeFrameWithIO rp rf fname (d + 1) 0 rej lit
        (HashSet.emptyWithCapacity 16) (HashSet.emptyWithCapacity 16) w
      = .ok (.ok (some (rootFrame fname key bytes d),
          (HashSet.emptyWithCapacity 16).insert key,
          (HashSet.emptyWithCapacity 16).insert key)) w₂ := by
  unfold prepareIncludeFrameWithIO
  dsimp only
  rcases h_key with ⟨hl, hk, hw⟩ | ⟨hl, p, hp, hk⟩
  · subst hl hw
    subst key
    rw [if_pos rfl, io_bind_apply, io_pure_apply]
    dsimp only
    rw [show includeIdentityKey true fname "" = fname from rfl, gate_root]
    dsimp only
    rw [io_bind_apply, h_read]
    rfl
  · subst hl
    subst key
    rw [if_neg (by simp), io_bind_apply, hp]
    dsimp only
    rw [io_bind_apply, io_pure_apply]
    dsimp only
    rw [show includeIdentityKey false fname p.toString = p.toString from rfl, gate_root]
    dsimp only
    rw [io_bind_apply, h_read]
    rfl


theorem parserIncludeRequestOfError?_eq_none (err : Error) (c : Nat)
    (h : ErrorNotRequest (some ⟨err, c⟩)) : parserIncludeRequestOfError? err = none := by
  cases err with
  | includeRequest sf p => exact absurd rfl (h sf p c)
  | _ => rfl

theorem stepFrame_nil (st : IncludeDriverState) (h : st.stack = []) : stepFrame st = .done st := by
  unfold stepFrame
  rw [h]

theorem stepFrame_live_ok (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame)
    (h_stack : st.stack = frame :: rest) (h_sep : frame.needsSep = false)
    (h_live : ¬ frame.offset ≥ frame.contents.size)
    (h_ok : (({ st.parser with sourceFile := frame.fname } : ParserState).feedAll st.base
      (frame.contents.extract frame.offset frame.contents.size)).db.error? = none) :
    stepFrame st = .fed { st with
      parser := ({ st.parser with sourceFile := frame.fname } : ParserState).feedAll st.base
        (frame.contents.extract frame.offset frame.contents.size),
      base := st.base + (frame.contents.extract frame.offset frame.contents.size).size,
      stack := { frame with offset := frame.contents.size } :: rest } := by
  unfold stepFrame
  rw [h_stack]
  simp [h_sep, h_live, h_ok]

theorem stepFrame_live_err (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) (err : Error) (c : Nat)
    (h_stack : st.stack = frame :: rest) (h_sep : frame.needsSep = false)
    (h_live : ¬ frame.offset ≥ frame.contents.size)
    (h_err : (({ st.parser with sourceFile := frame.fname } : ParserState).feedAll st.base
      (frame.contents.extract frame.offset frame.contents.size)).db.error? = some ⟨err, c⟩)
    (h_nreq : parserIncludeRequestOfError? err = none) :
    stepFrame st = .fed { st with
      parser := ({ st.parser with sourceFile := frame.fname } : ParserState).feedAll st.base
        (frame.contents.extract frame.offset frame.contents.size),
      base := st.base + c } := by
  unfold stepFrame
  rw [h_stack]
  simp [h_sep, h_live, h_err, h_nreq]

theorem stepFrame_exhausted_flush_err (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) (pos : Nat) (tk : ByteSliceT) (err : Error) (c : Nat)
    (h_stack : st.stack = frame :: rest) (h_sep : frame.needsSep = false)
    (h_exhausted : frame.offset ≥ frame.contents.size)
    (h_tok : st.parser.charp = .token pos tk)
    (h_err : (flushPendingToken
      { st.parser with charp := .token pos tk, sourceFile := frame.fname }).db.error?
        = some ⟨err, c⟩)
    (h_nreq : parserIncludeRequestOfError? err = none) :
    stepFrame st = .fed { st with
      parser := flushPendingToken
        { st.parser with charp := .token pos tk, sourceFile := frame.fname },
      base := st.base + c } := by
  unfold stepFrame
  rw [h_stack]
  simp [h_sep, h_exhausted, h_tok, h_err, h_nreq]


/-- `stepFrame_exhausted_flushed` for an arbitrary buffered token. -/
theorem stepFrame_exhausted_flush_ok (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) (pos : Nat) (tk : ByteSliceT)
    (h_stack : st.stack = frame :: rest) (h_sep : frame.needsSep = false)
    (h_exhausted : frame.offset ≥ frame.contents.size)
    (h_tok : st.parser.charp = .token pos tk)
    (h_ok : (flushPendingToken
      { st.parser with charp := .token pos tk, sourceFile := frame.fname }).db.error? = none) :
    stepFrame st = .fed { st with
      parser := popExhaustedFrame
        (flushPendingToken { st.parser with charp := .token pos tk, sourceFile := frame.fname })
        st.base frame rest,
      processing := st.processing.erase frame.canonStr,
      stack := rest } := by
  unfold stepFrame
  rw [h_stack]
  simp [h_sep, h_exhausted, h_tok, h_ok]

theorem setCharpSrc_eq (p : ParserState) (pos : Nat) (tk : ByteSliceT) (f : String)
    (h_tok : p.charp = .token pos tk) (h_src : p.sourceFile = f) :
    ({ p with charp := .token pos tk, sourceFile := f } : ParserState) = p := by
  obtain ⟨db, tokp, charp, line, linepos, sf⟩ := p
  simp only at h_tok h_src
  subst h_tok h_src
  rfl

/-- A single exhausted frame with nothing buffered is popped and the phase ends. -/
theorem runPureSteps_single_ws (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (h_stack : st.stack = [frame]) (h_sep : frame.needsSep = false)
    (h_exh : frame.offset ≥ frame.contents.size) (h_ws : st.parser.charp = .ws)
    (h_err : st.parser.db.error? = none) (X : DB) (hX : st.parser.done st.base = X) :
    ∃ stF : IncludeDriverState,
      (runPureSteps st = .done stF ∨ runPureSteps st = .stopped stF) ∧
      stF.parser.done stF.base = X := by
  have h1 := stepFrame_exhausted_ws st frame [] h_stack h_sep h_exh h_ws
  rw [ParserState.popExhaustedFrame_root] at h1
  refine ⟨{ st with processing := st.processing.erase frame.canonStr, stack := [] },
    Or.inl ?_, hX⟩
  rw [runPureSteps_of_fed_ok _ _ h1 h_err]
  exact runPureSteps_of_done _ _ (stepFrame_nil _ rfl)

/-- A single exhausted frame with one buffered token: the token is flushed under
the frame's label; on success the frame is popped, on a (non-request) error the
phase stops. -/
theorem runPureSteps_single_flush (st : IncludeDriverState) (frame : IncludeDriverFrame)
    (pos : Nat) (tk : ByteSliceT)
    (h_stack : st.stack = [frame]) (h_sep : frame.needsSep = false)
    (h_exh : frame.offset ≥ frame.contents.size) (h_tok : st.parser.charp = .token pos tk)
    (h_src : st.parser.sourceFile = frame.fname)
    (h_nreq : ErrorNotRequest (flushPendingToken st.parser).db.error?)
    (X : DB) (hX : (flushPendingToken st.parser).done st.base = X) :
    ∃ stF : IncludeDriverState,
      (runPureSteps st = .done stF ∨ runPureSteps st = .stopped stF) ∧
      stF.parser.done stF.base = X := by
  have h_in := setCharpSrc_eq st.parser pos tk frame.fname h_tok h_src
  cases h3 : (flushPendingToken st.parser).db.error? with
  | some it =>
      obtain ⟨err, c⟩ := it
      have h_nreq' : parserIncludeRequestOfError? err = none :=
        parserIncludeRequestOfError?_eq_none err c (h3 ▸ h_nreq)
      have h_step := stepFrame_exhausted_flush_err st frame [] pos tk err c h_stack h_sep h_exh
        h_tok (by rw [h_in]; exact h3) h_nreq'
      rw [h_in] at h_step
      refine ⟨_, Or.inr (runPureSteps_of_fed_err _ _ h_step (by simp [h3])), ?_⟩
      rw [← hX]
      show (flushPendingToken st.parser).done (st.base + c) = _
      rw [done_of_error _ _ (by simp [h3]), done_of_error _ _ (by simp [h3])]
  | none =>
      have h_step := stepFrame_exhausted_flush_ok st frame [] pos tk h_stack h_sep h_exh h_tok
        (by rw [h_in]; exact h3)
      rw [h_in, ParserState.popExhaustedFrame_root] at h_step
      refine ⟨{ st with
                parser := flushPendingToken st.parser
                processing := st.processing.erase frame.canonStr
                stack := [] }, Or.inl ?_, hX⟩
      rw [runPureSteps_of_fed_ok _ _ h_step h3]
      exact runPureSteps_of_done _ _ (stepFrame_nil _ rfl)

/-- The driver state right after the root frame is admitted. -/
def rootState (config : ModeConfig) (fname key : String) (bytes : ByteArray) (d : Nat) :
    IncludeDriverState :=
  { parser := singlePassInitialState config, base := 0,
    processing := (HashSet.emptyWithCapacity 16).insert key,
    seen := (HashSet.emptyWithCapacity 16).insert key,
    stack := [rootFrame fname key bytes d] }

/-- **The pure driver phase on a single root file.**  When the root file's
pure run (under its own label) raises no include request, the driver's pure
phase finishes without pushing, and finalizing its parser state gives exactly
that pure run's database. -/
theorem runPureSteps_root (config : ModeConfig) (fname key : String) (bytes : ByteArray)
    (d : Nat) (h_noreq : ErrorNotRequest (checkBytesCoreAt fname bytes config).error?) :
    ∃ stF : IncludeDriverState,
      (runPureSteps (rootState config fname key bytes d) = .done stF ∨
        runPureSteps (rootState config fname key bytes d) = .stopped stF) ∧
      stF.parser.done stF.base = checkBytesCoreAt fname bytes config := by
  have h_init_err : (singlePassInitialState config).db.error? = none := rfl
  have h_init_ws : (singlePassInitialState config).charp = .ws := rfl
  have h_core : checkBytesCoreAt fname bytes config
      = ((withSource fname (singlePassInitialState config)).feedAll 0 bytes).done bytes.size := rfl
  by_cases hsz : bytes.size = 0
  · -- an empty root file is popped at once
    apply runPureSteps_single_ws _ (rootFrame fname key bytes d) rfl rfl
      (by simp [rootFrame, hsz]) h_init_ws h_init_err
    show (singlePassInitialState config).done 0 = checkBytesCoreAt fname bytes config
    have hfa : (withSource fname (singlePassInitialState config)).feedAll 0 bytes
        = withSource fname (singlePassInitialState config) := by
      simp only [ParserState.feedAll, h_init_ws]
      rw [feed_eof 0 bytes 0 .ws _ (by omega)]
      rfl
    rw [h_core, hfa, hsz, done_withSource_ws fname _ 0 h_init_ws]
  · have h_live : ¬ (rootFrame fname key bytes d).offset
        ≥ (rootFrame fname key bytes d).contents.size := by
      simp only [rootFrame]
      omega
    have h_chunk : (rootFrame fname key bytes d).contents.extract
        (rootFrame fname key bytes d).offset (rootFrame fname key bytes d).contents.size
          = bytes := ByteArray.extract_zero_size
    have h_s1 : ({ (rootState config fname key bytes d).parser with
          sourceFile := (rootFrame fname key bytes d).fname } : ParserState).feedAll
          (rootState config fname key bytes d).base
          ((rootFrame fname key bytes d).contents.extract
            (rootFrame fname key bytes d).offset (rootFrame fname key bytes d).contents.size)
        = (withSource fname (singlePassInitialState config)).feedAll 0 bytes := by
      rw [h_chunk]
      rfl
    obtain ⟨hL, hS⟩ := feedAll_withSource fname (singlePassInitialState config) 0 bytes h_init_err
    cases h1 : ((withSource fname (singlePassInitialState config)).feedAll 0 bytes).db.error? with
    | some it =>
        -- the root chunk stops on a (non-request) error
        obtain ⟨err, c⟩ := it
        have h_done1 : checkBytesCoreAt fname bytes config
            = ((withSource fname (singlePassInitialState config)).feedAll 0 bytes).db := by
          rw [h_core]
          exact done_of_error _ _ (by rw [h1]; simp)
        have h_nreq : parserIncludeRequestOfError? err = none := by
          apply parserIncludeRequestOfError?_eq_none err c
          rw [← h1, ← h_done1]
          exact h_noreq
        have h_step := stepFrame_live_err (rootState config fname key bytes d)
          (rootFrame fname key bytes d) [] err c rfl rfl h_live (by rw [h_s1]; exact h1) h_nreq
        rw [h_s1] at h_step
        refine ⟨_, Or.inr (runPureSteps_of_fed_err _ _ h_step (by simp [h1])), ?_⟩
        rw [h_done1]
        exact done_of_error _ _ (by simp [h1])
    | none =>
        have h_step := stepFrame_live_ok (rootState config fname key bytes d)
          (rootFrame fname key bytes d) [] rfl rfl h_live (by rw [h_s1]; exact h1)
        rw [h_s1, h_chunk] at h_step
        rw [runPureSteps_of_fed_ok _ _ h_step h1]
        have h_B : ((singlePassInitialState config).feedAll 0 bytes).db.error? = none :=
          hL.2.1.mp h1
        have h_eq := hS h_B
        cases h2 : ((withSource fname (singlePassInitialState config)).feedAll 0 bytes).charp with
        | ws =>
            apply runPureSteps_single_ws _ { rootFrame fname key bytes d with
                offset := (rootFrame fname key bytes d).contents.size } rfl rfl
              (Nat.le_refl _) h2 h1
            show ((withSource fname (singlePassInitialState config)).feedAll 0 bytes).done
              (0 + bytes.size) = checkBytesCoreAt fname bytes config
            rw [Nat.zero_add, h_core]
        | token pos tk =>
            -- the root file ends inside a token: flush it under the root's label
            have h_src : ((withSource fname (singlePassInitialState config)).feedAll 0 bytes).sourceFile
                = fname := by
              rw [h_eq]
            have h_flush_done : (flushPendingToken
                ((withSource fname (singlePassInitialState config)).feedAll 0 bytes)).done bytes.size
                = checkBytesCoreAt fname bytes config := by
              rw [done_flush _ _ h1, h_core]
            have h_nreq : ErrorNotRequest (flushPendingToken
                ((withSource fname (singlePassInitialState config)).feedAll 0 bytes)).db.error? := by
              cases h3 : (flushPendingToken
                  ((withSource fname (singlePassInitialState config)).feedAll 0 bytes)).db.error? with
              | none => exact ParserOps.errorNotRequest_none
              | some it =>
                  have h_done2 : checkBytesCoreAt fname bytes config = (flushPendingToken
                      ((withSource fname (singlePassInitialState config)).feedAll 0 bytes)).db := by
                    rw [← h_flush_done]
                    exact done_of_error _ _ (by rw [h3]; simp)
                  rw [← h3, ← h_done2]
                  exact h_noreq
            apply runPureSteps_single_flush _ { rootFrame fname key bytes d with
                offset := (rootFrame fname key bytes d).contents.size } pos tk rfl rfl
              (Nat.le_refl _) h2 h_src h_nreq
            show (flushPendingToken ((withSource fname (singlePassInitialState config)).feedAll
              0 bytes)).done (0 + bytes.size) = checkBytesCoreAt fname bytes config
            rw [Nat.zero_add, h_flush_done]


theorem runDriverLoop_root (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (config : ModeConfig) (fname key : String) (bytes : ByteArray) (d : Nat)
    (w : Void IO.RealWorld) (h_noreq : ErrorNotRequest (checkBytesCoreAt fname bytes config).error?) :
    ∃ stF : IncludeDriverState,
      runDriverLoop rp rf fuel (rootState config fname key bytes d) w = .ok (.ok stF) w ∧
      stF.parser.done stF.base = checkBytesCoreAt fname bytes config := by
  obtain ⟨stF, h_run, h_done⟩ := runPureSteps_root config fname key bytes d h_noreq
  refine ⟨stF, ?_, h_done⟩
  unfold runDriverLoop
  rcases h_run with h | h <;> rw [h] <;> rfl

/-- The driver state `check` starts from. -/
def initDriverState (config : ModeConfig) : IncludeDriverState :=
  { parser := singlePassInitialState config, base := 0,
    processing := HashSet.emptyWithCapacity 16, seen := HashSet.emptyWithCapacity 16,
    stack := [] }

theorem processFileSinglePassWithIO_root (rp : String → IO System.FilePath)
    (rf : String → IO ByteArray) (fname : String) (config : ModeConfig) (d : Nat)
    (w w₁ w₂ : Void IO.RealWorld) (key : String) (bytes : ByteArray)
    (h_key : RootKey rp fname config.literalIncludePaths w w₁ key)
    (h_read : rf fname w₁ = .ok bytes w₂)
    (h_noreq : ErrorNotRequest (checkBytesCoreAt fname bytes config).error?) :
    ∃ stF : IncludeDriverState,
      processFileSinglePassWithIO rp rf fname config (d + 1) (initDriverState config) w
        = .ok (.ok stF) w₂ ∧
      stF.parser.done stF.base = checkBytesCoreAt fname bytes config := by
  obtain ⟨stF, h_loop, h_done⟩ := runDriverLoop_root rp rf config.maxIncludeResolutions config
    fname key bytes d w₂ h_noreq
  refine ⟨stF, ?_, h_done⟩
  unfold processFileSinglePassWithIO
  rw [io_bind_apply]
  have hp := prepare_root rp rf fname d config.rejectIncludeCycles config.literalIncludePaths
    w w₁ w₂ key bytes h_key h_read
  erw [hp]
  exact h_loop


/-! ## The actual `check` entrypoint on a single root file -/

/-- The root path resolves: literal-path modes perform no IO for it; canonical
modes need the path-resolution action to succeed on `fname`. -/
def RootResolves (rp : String → IO System.FilePath) (fname : String) (literal : Bool)
    (w w₁ : Void IO.RealWorld) : Prop :=
  (literal = true ∧ w₁ = w) ∨
  (literal = false ∧ ∃ p : System.FilePath, rp fname w = .ok p w₁)

theorem rootKey_of_resolves {rp : String → IO System.FilePath} {fname : String}
    {literal : Bool} {w w₁ : Void IO.RealWorld} (h : RootResolves rp fname literal w w₁) :
    ∃ key, RootKey rp fname literal w w₁ key := by
  rcases h with ⟨hl, hw⟩ | ⟨hl, p, hp⟩
  · exact ⟨fname, Or.inl ⟨hl, rfl, hw⟩⟩
  · exact ⟨p.toString, Or.inr ⟨hl, p, hp, rfl⟩⟩

theorem check_root_checkBytesCoreAt (fname : String) (config : ModeConfig) (bytes : ByteArray)
    (w w₁ w₂ : Void IO.RealWorld)
    (h_depth : config.maxIncludeDepth ≠ 0)
    (h_path : RootResolves (fun path => IO.FS.realPath path) fname
      config.literalIncludePaths w w₁)
    (h_read : IO.FS.readBinFile fname w₁ = .ok bytes w₂)
    (h_noreq : ErrorNotRequest (checkBytesCoreAt fname bytes config).error?) :
    check fname config w = .ok (postCheck (checkBytesCoreAt fname bytes config)) w₂ := by
  obtain ⟨key, h_key⟩ := rootKey_of_resolves h_path
  obtain ⟨d, hd⟩ : ∃ d, config.maxIncludeDepth = d + 1 :=
    ⟨config.maxIncludeDepth - 1, by omega⟩
  obtain ⟨stF, h_pf, h_done⟩ := processFileSinglePassWithIO_root
    (fun path => IO.FS.realPath path) (fun path => IO.FS.readBinFile path) fname config d
    w w₁ w₂ key bytes h_key h_read h_noreq
  unfold check singlePassInitialResult processFileSinglePass
  rw [io_bind_apply, io_bind_apply, hd]
  erw [h_pf]
  rw [← h_done]
  rfl


/-! ## The stored-`$d` invariant through the include driver

`AssertDv.DvStateInv` (the `$d` invariant, its token-state companion and the
`$f` shape fact) is mode-free.  It is lifted here through every include-driver
operation — `stepFrame` (separator, live chunk, exhausted-frame flush, pop,
include-request clearing), `popExhaustedFrame`, `flushPendingToken`,
`restoreLineState` — and through include resolution, so it holds for the
database every error-free `check` run returns, in every mode. -/

section DvDriver

open Metamath.AssertDv
open Metamath.PrefixProvability.Checker (popScope_errorNotRequestP label_errorNotRequestP
  djvars_loop_errorNotRequest feedTokens_errorNotRequest finishProof_errorNotRequest
  feedProof_errorNotRequest clearIncludeRequest_requestInclude_eq popExhaustedFrame_objects
  frameStepParser resolvePushWithIO_ok_post runDriverLoop_ok_inversion
  runPureSteps_stopped_error stepFrame_done_inv)

/-- Mode-free form of `feedToken_request_form_or_notRequest`: from an
error-free state a step either leaves a non-request error slot or *is* a
`requestInclude`. -/
theorem feedToken_request_form (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_err0 : s.db.error? = none) :
    ParserOps.ErrorNotRequest (s.feedToken i tk).db.error?
      ∨ (∃ resume path, s.feedToken i tk = s.requestInclude resume path) := by
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
      simp only
      repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | includePath resume q =>
      simp only
      repeat' split
      all_goals
        first
          | (left; exact h_base)
          | (left; exact h_mk _ _ _)
          | (right; exact ⟨resume, _, rfl⟩)
  | includeClose resume q path =>
      simp only
      repeat' split
      all_goals
        first
          | (left; exact h_base)
          | (left; exact h_mk _ _ _)
          | (right; exact ⟨resume, path, rfl⟩)
  | start =>
      left
      simp only
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact popScope_errorNotRequestP s _ h_base
          | exact label_errorNotRequestP s _ tk h_base
  | label q lab =>
      left
      simp only
      repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | const seen =>
      left
      simp only
      unfold ParserState.sym ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact ParserOps.insert_errorNotRequest s.db _ _ _ h_base
  | var seen =>
      left
      simp only
      unfold ParserState.sym ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact ParserOps.insert_errorNotRequest s.db _ _ _ h_base
  | djvars arr =>
      left
      simp only
      unfold ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact djvars_loop_errorNotRequest _ _ _ _ h_base
  | math arr p =>
      left
      simp only
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
      simp only
      repeat' split
      all_goals
        first
          | exact finishProof_errorNotRequest _ pr h_base
          | exact feedProof_errorNotRequest _ tk pr h_base
          | exact h_base
          | exact h_mk _ _ _

/-- The `$d` invariant package on a live (error-free) parser state. -/
def DvDriverInv (p : ParserState) : Prop := DvStateInv p ∧ p.db.error? = none

/-- `DvStateInv` reads the database only through its registry, plus the token
mode. -/
theorem dvStateInv_of_objects_tokp {p q : ParserState} (h_obj : p.db.objects = q.db.objects)
    (h_tokp : p.tokp = q.tokp) (h : DvStateInv q) : DvStateInv p := by
  obtain ⟨h1, h2, h3⟩ := h
  have h_find : ∀ n, p.db.find? n = q.db.find? n := fun n => by
    show p.db.objects[n]? = q.db.objects[n]?
    rw [h_obj]
  refine ⟨floatHypsShaped_of_objects_eq h_obj h1, assertDvVarsInFrame_of_find?_eq h_find h2, ?_⟩
  rw [h_tokp]
  exact proofDvInv_mono (fun n o h => by rw [h_find]; exact h) _ h3

theorem dvDriverInv_of_db_tokp_eq (p q : ParserState) (hdb : p.db = q.db) (ht : p.tokp = q.tokp)
    (h : DvDriverInv q) : DvDriverInv p :=
  ⟨dvStateInv_of_objects_tokp (by rw [hdb]) ht h.1, by rw [hdb]; exact h.2⟩

theorem dvDriverInv_updateLine (s : ParserState) (i : Nat) (c : UInt8) (h : DvDriverInv s) :
    DvDriverInv (s.updateLine i c) :=
  dvDriverInv_of_db_tokp_eq _ s (ParserState.updateLine_db s i c)
    (by unfold ParserState.updateLine; split <;> rfl) h

/-- **Include-request clearing.**  A step that raised an include request,
cleared, is `$d`-invariant-bearing: it was a `requestInclude`, and clearing
restores the raising state with the parked continuation, whose proof frame the
companion already covers. -/
theorem dvDriverInv_of_request_step (s : ParserState) (i : Nat) (tk : ByteSlice)
    {sf pf : String} {idx : Nat} (h : DvDriverInv s)
    (h_req : (s.feedToken i tk).db.error? = some ⟨.includeRequest sf pf, idx⟩) :
    DvDriverInv (clearIncludeRequest (s.feedToken i tk)) := by
  rcases feedToken_request_form s i tk h.2 with h_nr | ⟨resume, path, h_eq⟩
  · exact absurd h_req (h_nr sf pf idx)
  · have h_pdv : ProofDvInv s.db (s.feedToken i tk).tokp :=
      feedToken_proofDvInv_pre s i tk h.1.1 h.1.2.2
    rw [h_eq] at h_pdv ⊢
    rw [clearIncludeRequest_requestInclude_eq s resume path h.2]
    exact ⟨⟨h.1.1, h.1.2.1, h_pdv⟩, h.2⟩

/-- Clearing a frozen interrupt: database and token mode as if clearing the
unfrozen state. -/
theorem clear_freeze_updateLine (s : ParserState) (i : Nat) (c : UInt8) (x : Option Interrupt) :
    (clearIncludeRequest { s.updateLine i c with
      db := { (s.updateLine i c).db with error? := x } }).db = (clearIncludeRequest s).db ∧
    (clearIncludeRequest { s.updateLine i c with
      db := { (s.updateLine i c).db with error? := x } }).tokp = (clearIncludeRequest s).tokp := by
  unfold ParserState.updateLine
  split <;> exact ⟨rfl, rfl⟩

theorem flushOld_eq_feedToken (s : ParserState) (base : Nat) (arr : ByteArray) (i : Nat)
    (ot : ParserState.OldToken) :
    ∃ p tk, flushOld s base arr i ot = s.feedToken p tk := by
  cases ot <;> exact ⟨_, _, rfl⟩

/-- A byte loop ending in an include request hands the cleared state back
`$d`-invariant-bearing. -/
theorem feed_request_transport_dv (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState) (h : DvDriverInv s)
    {sf pf : String} {idx : Nat}
    (h_end : (s.feed base arr i rs).db.error? = some ⟨.includeRequest sf pf, idx⟩) :
    DvDriverInv (clearIncludeRequest (s.feed base arr i rs)) := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState), DvDriverInv s → ∀ idx : Nat,
      (s.feed base arr i rs).db.error? = some ⟨.includeRequest sf pf, idx⟩ →
      arr.size - i = m → DvDriverInv (clearIncludeRequest (s.feed base arr i rs)))
    ?base ?step (arr.size - i) i rs s h idx h_end rfl
  · intro i rs s h idx h_end hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    rw [feed_eof base arr i rs s hi] at h_end
    have h2 := h.2
    exact absurd (h_end.symm.trans h2) (by simp)
  · intro m ih i rs s h idx h_end hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        simp [hz] at hs
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    by_cases hw : s.db.config.isWhitespace arr[i] = true
    · cases rs with
      | ws =>
          rw [feed_ws_ws base arr i s hi hw] at h_end ⊢
          exact ih (i + 1) .ws _ (dvDriverInv_updateLine s _ _ h) idx h_end hs'
      | token ot =>
          rw [feed_ws_token base arr i s ot hi hw] at h_end ⊢
          obtain ⟨p, tk, h_fl⟩ := flushOld_eq_feedToken s base arr i ot
          rw [h_fl] at h_end ⊢
          unfold continueAfter at h_end ⊢
          cases h_e : ((s.feedToken p tk).updateLine (base + i) arr[i]).db.error? with
          | none =>
              rw [h_e] at h_end
              have h_ok : (s.feedToken p tk).db.error? = none := by
                simpa only [ParserState.updateLine_db] using h_e
              have h1 : DvDriverInv ((s.feedToken p tk).updateLine (base + i) arr[i]) :=
                dvDriverInv_updateLine _ _ _
                  ⟨feedToken_maintains_dvStateInv s p tk h.1 h.2 h_ok, h_ok⟩
              exact ih (i + 1) .ws _ h1 idx h_end hs'
          | some it =>
              obtain ⟨e, k⟩ := it
              rw [h_e] at h_end
              have h_pair : (⟨e, i + 1⟩ : Interrupt) = ⟨.includeRequest sf pf, idx⟩ :=
                Option.some.inj h_end
              cases h_pair
              have h_req : (s.feedToken p tk).db.error? = some ⟨.includeRequest sf pf, k⟩ := by
                simpa only [ParserState.updateLine_db] using h_e
              obtain ⟨h_db, h_tp⟩ := clear_freeze_updateLine (s.feedToken p tk) (base + i) arr[i]
                (some ⟨.includeRequest sf pf, i + 1⟩)
              exact dvDriverInv_of_db_tokp_eq _ _ h_db h_tp (dvDriverInv_of_request_step s p tk h h_req)
    · rw [feed_nonws base arr i s rs hi hw] at h_end ⊢
      exact ih (i + 1) _ s h idx h_end hs'

theorem feedAll_eq_feed_cases (s : ParserState) (base : Nat) (arr : ByteArray) :
    (s.charp = .ws ∧ s.feedAll base arr = s.feed base arr 0 .ws) ∨
    (∃ base' tk, s.charp = .token base' tk ∧
      s.feedAll base arr = ({ s with charp := default } : ParserState).feed base arr 0
        (.token (.old base' tk.start tk.byteArray))) := by
  cases h : s.charp with
  | ws => exact Or.inl ⟨rfl, by simp only [ParserState.feedAll, h]⟩
  | token base' tk => exact Or.inr ⟨base', tk, rfl, by simp only [ParserState.feedAll, h]⟩

theorem feedAll_request_transport_dv (s : ParserState) (base : Nat) (arr : ByteArray)
    (h : DvDriverInv s) {sf pf : String} {idx : Nat}
    (h_end : (s.feedAll base arr).db.error? = some ⟨.includeRequest sf pf, idx⟩) :
    DvDriverInv (clearIncludeRequest (s.feedAll base arr)) := by
  rcases feedAll_eq_feed_cases s base arr with ⟨_, h_eq⟩ | ⟨base', tk, _, h_eq⟩
  · rw [h_eq] at h_end ⊢
    exact feed_request_transport_dv base arr 0 .ws s h h_end
  · rw [h_eq] at h_end ⊢
    exact feed_request_transport_dv base arr 0 _ _ (dvDriverInv_of_db_tokp_eq _ s rfl rfl h) h_end

theorem dvDriverInv_feedAll_ok (s : ParserState) (base : Nat) (arr : ByteArray) (h : DvDriverInv s)
    (h_ok : (s.feedAll base arr).db.error? = none) : DvDriverInv (s.feedAll base arr) :=
  ⟨feedAll_maintains_dvStateInv s base arr h.1 h.2 h_ok, h_ok⟩

/-- **`flushPendingToken`** keeps the package when the flush succeeds. -/
theorem dvDriverInv_flushPendingToken (s : ParserState) (h : DvDriverInv s)
    (h_ok : (flushPendingToken s).db.error? = none) : DvDriverInv (flushPendingToken s) := by
  revert h_ok
  unfold flushPendingToken
  split
  · intro _
    exact h
  · rename_i pos tk _
    intro h_ok
    have h_ok' : (s.feedToken pos tk.toSlice).db.error? = none := by simpa using h_ok
    exact dvDriverInv_of_db_tokp_eq _ (s.feedToken pos tk.toSlice) rfl rfl
      ⟨feedToken_maintains_dvStateInv s pos tk.toSlice h.1 h.2 h_ok', h_ok'⟩

theorem popExhaustedFrame_tokp (s : ParserState) (base : Nat) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) :
    (popExhaustedFrame s base frame rest).tokp = s.tokp := by
  unfold popExhaustedFrame
  repeat' split
  all_goals simp [restoreLineState, ParserState.withDB]

/-- **`popExhaustedFrame`** keeps `DvStateInv` unconditionally (a boundary error
touches no registry entry and no token mode), and the whole package whenever the
pop raises no boundary error. -/
theorem dvStateInv_popExhaustedFrame (s : ParserState) (base : Nat)
    (frame : IncludeDriverFrame) (rest : List IncludeDriverFrame) (h : DvStateInv s) :
    DvStateInv (popExhaustedFrame s base frame rest) :=
  dvStateInv_of_objects_tokp (popExhaustedFrame_objects s base frame rest)
    (popExhaustedFrame_tokp s base frame rest) h

theorem dvDriverInv_popExhaustedFrame (s : ParserState) (base : Nat) (frame : IncludeDriverFrame)
    (rest : List IncludeDriverFrame) (h : DvDriverInv s)
    (h_ok : (popExhaustedFrame s base frame rest).db.error? = none) :
    DvDriverInv (popExhaustedFrame s base frame rest) :=
  ⟨dvStateInv_popExhaustedFrame s base frame rest h.1, h_ok⟩

set_option linter.unreachableTactic false in
/-- **`stepFrame`** maintains the `$d` package on every live path, in every
mode: a `.done`/`.fed` result with no parser error (separator, live chunk,
flushed pop), or any `.push` result (a cleared include request whose parked
continuation resumes after the child). -/
theorem stepFrame_maintains_dvDriverInv (st : IncludeDriverState)
    (h : DvDriverInv st.parser)
    (h_ok : (frameStepParser (stepFrame st)).db.error? = none
      ∨ ∃ sf incf d st', stepFrame st = .push sf incf d st') :
    DvDriverInv (frameStepParser (stepFrame st)) := by
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
        · exact dvDriverInv_feedAll_ok _ _ _ h h_ok
        · cases h_bad
      · rw [if_neg h_sep] at h_ok ⊢
        by_cases h_exh : parent.offset ≥ parent.contents.size
        · rw [if_pos h_exh] at h_ok ⊢
          cases h_charp : st.parser.charp with
          | ws =>
              simp only [h_charp, frameStepParser] at h_ok ⊢
              rcases h_ok with h_ok | ⟨sf, incf, d, st', h_bad⟩
              · exact dvDriverInv_popExhaustedFrame _ _ _ _ h h_ok
              · cases h_bad
          | token cpos ctk =>
              simp only [h_charp] at h_ok ⊢
              have h_inp : DvDriverInv ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) :=
                dvDriverInv_of_db_tokp_eq _ st.parser rfl rfl h
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
                              exact dvDriverInv_of_db_tokp_eq _ _
                                (by unfold clearIncludeRequest flushPendingToken
                                    rfl)
                                (by unfold clearIncludeRequest flushPendingToken
                                    rfl)
                                (dvDriverInv_of_request_step ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) cpos ctk.toSlice
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
                  · exact dvDriverInv_popExhaustedFrame _ _ _ _
                      (dvDriverInv_flushPendingToken ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) h_inp h_e1)
                      h_ok
                  · cases h_bad
        · rw [if_neg h_exh] at h_ok ⊢
          have h_inp : DvDriverInv ({ st.parser with sourceFile := parent.fname } : ParserState) :=
            dvDriverInv_of_db_tokp_eq _ st.parser rfl rfl h
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
                          exact feedAll_request_transport_dv ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _
                            h_inp (by simpa using h_e1)
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
              · exact dvDriverInv_feedAll_ok ({ st.parser with sourceFile := parent.fname } : ParserState) st.base _ h_inp h_e1
              · cases h_bad


/-- The `$d` package carried to a pure-phase result. -/
def DvPhaseInv : DriverPhase → Prop
  | .done st => DvDriverInv st.parser
  | .stopped _ => True
  | .push _ _ _ st => DvDriverInv st.parser

/-- A pure driver phase keeps the package on every live result. -/
theorem runPureSteps_dvPhaseInv (st : IncludeDriverState) (h : DvDriverInv st.parser) :
    DvPhaseInv (runPureSteps st) := by
  revert h
  fun_induction runPureSteps st
  case case1 st st' _h =>
      intro h
      have h_eq := stepFrame_done_inv st st' _h
      subst h_eq
      exact h
  case case2 st sf incf d st' _h =>
      intro h
      have h' := stepFrame_maintains_dvDriverInv st h (Or.inr ⟨sf, incf, d, st', _h⟩)
      rw [_h] at h'
      simpa [frameStepParser, DvPhaseInv] using h'
  case case3 st st' _h _h_err =>
      intro _
      trivial
  case case4 st st' _h _h_err ih =>
      intro h
      have h_err0' : st'.parser.db.error? = none := by
        have := _h_err
        simp only [Bool.not_eq_true, DB.error, Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none] at this
        exact this
      have h' := stepFrame_maintains_dvDriverInv st h
        (Or.inl (by rw [_h]; simpa [frameStepParser] using h_err0'))
      rw [_h] at h'
      simp only [frameStepParser] at h'
      exact ih h'

/-- **Include resolution and the whole driver loop.**  For arbitrary
path-resolution and file-reading actions (any file tree, any include
structure), a successful driver run from a `$d`-invariant-bearing state ends in
a `$d`-invariant-bearing state whenever it ends error-free.  Resolution
(`resolvePushWithIO`) touches only include bookkeeping, the stack and the
child's line numbering, never the database or the token mode. -/
theorem runDriverLoop_ok_dvDriverInv (rp : String → IO System.FilePath)
    (rf : String → IO ByteArray) (fuel : Nat) (st : IncludeDriverState)
    (w w' : Void IO.RealWorld) (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w')
    (h : DvDriverInv st.parser) (h_err : rst.parser.db.error? = none) :
    DvDriverInv rst.parser := by
  induction fuel generalizing st w with
  | zero =>
      rcases runDriverLoop_ok_inversion rp rf 0 st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', fuel', st'', w₂, h_eq, _, _, _⟩
      · have h1 := runPureSteps_dvPhaseInv st h
        rw [h_d] at h1
        exact h1
      · have h1 := runPureSteps_stopped_error st rst h_s
        rw [DB.error, h_err] at h1
        simp at h1
      · exact absurd h_eq (by omega)
  | succ fuel' ih =>
      rcases runDriverLoop_ok_inversion rp rf (fuel' + 1) st w w' rst h_run with
        (h_d | h_s) | ⟨src, inc, d, st', f2, st'', w₂, h_eq, h_p, h_res, h_rec⟩
      · have h1 := runPureSteps_dvPhaseInv st h
        rw [h_d] at h1
        exact h1
      · have h1 := runPureSteps_stopped_error st rst h_s
        rw [DB.error, h_err] at h1
        simp at h1
      · have h_f2 : f2 = fuel' := by omega
        subst h_f2
        have h1 := runPureSteps_dvPhaseInv st h
        rw [h_p] at h1
        obtain ⟨h_db, h_tokp, _⟩ :=
          resolvePushWithIO_ok_post rp rf src inc d st' st'' w w₂ h_res
        exact ih st'' w₂ h_rec (dvDriverInv_of_db_tokp_eq _ _ h_db h_tokp h1)

/-- EOF finalization keeps the stored-`$d` invariant on an error-free result. -/
theorem done_assertDvVarsInFrame (s : ParserState) (base : Nat) (h : DvDriverInv s)
    (h_ok : (s.done base).error? = none) : AssertDvVarsInFrame (s.done base) := by
  cases h_charp : s.charp with
  | ws =>
      exact assertDvVarsInFrame_of_find?_eq
        (fun n => PrefixProvability.Checker.done_find?_eq_self s base n h.2 h_charp) h.1.2.1
  | token pos tk =>
      have h_e1 : (s.feedToken pos tk.toSlice).db.error? = none := by
        cases h_e : (s.feedToken pos tk.toSlice).db.error? with
        | none => rfl
        | some it =>
            exfalso
            have h_flush : flushPendingToken s = { s.feedToken pos tk.toSlice with charp := .ws } := by
              simp only [flushPendingToken, h_charp]
            have e1 : ({ s.feedToken pos tk.toSlice with charp := .ws } : ParserState).done base
                = (s.feedToken pos tk.toSlice).db :=
              done_of_error _ base (by rw [h_e]; simp)
            have h_stuck : (s.done base).error? ≠ none := by
              rw [← done_flush s base h.2, h_flush, e1, h_e]
              simp
            exact h_stuck h_ok
      have h_flush := feedToken_maintains_assertDvVarsInFrame_of_floatHypsShaped s pos
        tk.toSlice h.1.1 h.1.2.1 h.1.2.2 h.2 h_e1
      exact assertDvVarsInFrame_of_find?_eq
        (fun n => PrefixProvability.Checker.done_find?_eq_flush s base pos tk n h.2 h_charp h_e1)
        h_flush

theorem initState_dvDriverInv (config : ModeConfig) : DvDriverInv (singlePassInitialState config) :=
  ⟨initState_dvStateInv config, rfl⟩

/-- **The finalize-time `$d` post-check is redundant for the IO driver, in every
mode and for every file tree.**  Whatever the path-resolution and file-reading
actions, a successful driver run from the entrypoint's initial state whose
finalized database is error-free satisfies the stored-`$d` invariant, so the
Boolean post-check `assertDvVarsInFrame?` in `finalizeSinglePassResult` passes. -/
theorem runDriverLoop_done_assertDvVarsInFrame (rp : String → IO System.FilePath)
    (rf : String → IO ByteArray) (fuel : Nat) (config : ModeConfig)
    (st : IncludeDriverState) (h_init : st.parser = singlePassInitialState config)
    (w w' : Void IO.RealWorld) (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w')
    (h_ok : (rst.parser.done rst.base).error? = none) :
    AssertDvVarsInFrame (rst.parser.done rst.base) ∧
      (rst.parser.done rst.base).assertDvVarsInFrame? = true := by
  have h_err : rst.parser.db.error? = none :=
    ParserOps.done_no_error_implies_db_no_error rst.parser rst.base h_ok
  have h_live := runDriverLoop_ok_dvDriverInv rp rf fuel st w w' rst h_run
    (by rw [h_init]; exact initState_dvDriverInv config) h_err
  have h_dv := done_assertDvVarsInFrame rst.parser rst.base h_live h_ok
  exact ⟨h_dv, assertDvVarsInFrame?_of_assertDvVarsInFrame h_dv⟩


theorem processFileSinglePassWithIO_done_assertDvVarsInFrame
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fname : String) (config : ModeConfig) (depth : Nat)
    (w w' : Void IO.RealWorld) (st : IncludeDriverState)
    (h_run : processFileSinglePassWithIO rp rf fname config depth (initDriverState config) w
      = .ok (.ok st) w')
    (h_ok : (st.parser.done st.base).error? = none) :
    AssertDvVarsInFrame (st.parser.done st.base) := by
  unfold processFileSinglePassWithIO at h_run
  rw [io_bind_apply] at h_run
  split at h_run
  · rename_i r w₂ heq
    rcases r with err | ⟨opt, P, S⟩
    · dsimp only at h_run
      rw [io_pure_apply] at h_run
      cases h_run
    · cases opt with
      | none =>
          injection h_run with h1 _
          injection h1 with h1
          subst h1
          exact done_assertDvVarsInFrame _ _ (initState_dvDriverInv config) h_ok
      | some root =>
          exact (runDriverLoop_done_assertDvVarsInFrame rp rf _ config _ rfl w₂ w' st h_run
            h_ok).1
  · exact absurd h_run (by simp)

/-- **The stored-`$d` invariant for the database `check` returns.**  In every
mode, for every file tree and every world: if `check` returns an error-free
database, every stored assertion's `$d` variables are float variables of its
own frame. -/
theorem check_assertDvVarsInFrame (fname : String) (config : ModeConfig)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : check fname config w = .ok db w') (h_success : db.error? = none) :
    AssertDvVarsInFrame db := by
  unfold check singlePassInitialResult processFileSinglePass at h_run
  rw [io_bind_apply, io_bind_apply] at h_run
  split at h_run
  · rename_i r w₂ heq
    split at heq
    · rename_i r0 w₃ heq0
      rcases r0 with err | st
      · injection heq with h1 _
        subst h1
        injection h_run with h2 _
        subst h2
        exact absurd h_success (by simp [finalizeSinglePassResult, includePreprocessErrorDB,
          DB.mkErrorFromEvidence, DB.mkErrorWithEvidence])
      · injection heq with h1 _
        subst h1
        injection h_run with h2 _
        subst h2
        have h_post : finalizeSinglePassResult config (.ok (st.parser, st.base, st.seen))
            = postCheck (st.parser.done st.base) := rfl
        rw [h_post] at h_success ⊢
        have h_core_ok : (st.parser.done st.base).error? = none := by
          by_contra h_ne
          rw [postCheck_of_error _ h_ne] at h_success
          exact h_ne h_success
        have h_dv := processFileSinglePassWithIO_done_assertDvVarsInFrame
          (fun path => IO.FS.realPath path) (fun path => IO.FS.readBinFile path) fname config
          config.maxIncludeDepth w w₃ st heq0 h_core_ok
        have h_gate : postCheck (st.parser.done st.base) = st.parser.done st.base :=
          postCheck_eq_of_ok _ h_success
        rw [h_gate]
        exact h_dv
    · exact absurd heq (by simp)
  · exact absurd h_run (by simp)

end DvDriver

/-! ## Headline theorems -/

/-- **Root-file bridge.**  Let the root path of `fname` pass the depth gate,
resolve (canonical modes: `IO.FS.realPath` succeeds; literal modes: no IO), and
read successfully to `bytes`, and let the pure entrypoint on `bytes` report no
include request.  Then `check fname config` returns (in the world after the
read) a database that agrees with `checkBytes bytes config` on the registry,
`find?`, `incompleteProofs`, frame, scopes, active variables, interrupt flag,
configuration, error status and include-request status; the two differ at most
in the payload of an include-path error, which names the file.  Whenever
`checkBytes` is error-free the two databases are equal. -/
theorem check_root_bridge (fname : String) (config : ModeConfig) (bytes : ByteArray)
    (w w₁ w₂ : Void IO.RealWorld)
    (h_depth : config.maxIncludeDepth ≠ 0)
    (h_path : RootResolves (fun path => IO.FS.realPath path) fname
      config.literalIncludePaths w w₁)
    (h_read : IO.FS.readBinFile fname w₁ = .ok bytes w₂)
    (h_noreq : ErrorNotRequest (checkBytes bytes config).error?) :
    ∃ db : DB, check fname config w = .ok db w₂ ∧
      DBAgreeUpToError db (checkBytes bytes config) ∧
      ((checkBytes bytes config).error? = none → db = checkBytes bytes config) := by
  obtain ⟨hA, hS⟩ := checkBytesCoreAt_rel fname bytes config
  have h_noreq0 : ErrorNotRequest (checkBytesCoreAt "" bytes config).error? :=
    errorNotRequest_of_postCheck _ h_noreq
  have h_noreqF : ErrorNotRequest (checkBytesCoreAt fname bytes config).error? := hA.2.2.mpr h_noreq0
  exact ⟨_, check_root_checkBytesCoreAt fname config bytes w w₁ w₂ h_depth h_path h_read h_noreqF,
    postCheck_rel hA hS⟩

/-- **Success transfers from the pure entrypoint to `check`, literally.**  No
include condition is needed: an error-free pure run raised none. -/
theorem check_eq_checkBytes_of_ok (fname : String) (config : ModeConfig) (bytes : ByteArray)
    (w w₁ w₂ : Void IO.RealWorld)
    (h_depth : config.maxIncludeDepth ≠ 0)
    (h_path : RootResolves (fun path => IO.FS.realPath path) fname
      config.literalIncludePaths w w₁)
    (h_read : IO.FS.readBinFile fname w₁ = .ok bytes w₂)
    (h_ok : (checkBytes bytes config).error? = none) :
    check fname config w = .ok (checkBytes bytes config) w₂ := by
  obtain ⟨db, h_run, _, h_eq⟩ := check_root_bridge fname config bytes w w₁ w₂ h_depth h_path
    h_read (by rw [h_ok]; exact ParserOps.errorNotRequest_none)
  rw [h_run, h_eq h_ok]

/-- **Success transfers from `check` to the pure entrypoint.**  If `check`
returns an error-free database on this world, it is `checkBytes bytes config`,
returned in the world after the read. -/
theorem checkBytes_eq_of_check_ok (fname : String) (config : ModeConfig) (bytes : ByteArray)
    (w w₁ w₂ w' : Void IO.RealWorld) (db : DB)
    (h_depth : config.maxIncludeDepth ≠ 0)
    (h_path : RootResolves (fun path => IO.FS.realPath path) fname
      config.literalIncludePaths w w₁)
    (h_read : IO.FS.readBinFile fname w₁ = .ok bytes w₂)
    (h_noreq : ErrorNotRequest (checkBytes bytes config).error?)
    (h_run : check fname config w = .ok db w') (h_ok : db.error? = none) :
    db = checkBytes bytes config ∧ w' = w₂ := by
  obtain ⟨db0, h_run0, hA, hS⟩ := check_root_bridge fname config bytes w w₁ w₂ h_depth h_path
    h_read h_noreq
  rw [h_run0] at h_run
  injection h_run with h_db h_w
  subst h_db h_w
  exact ⟨hS (hA.2.1.mp h_ok), rfl⟩

/-! ## Non-vacuity -/

/-- The filesystem hypotheses are satisfiable: pure path-resolution and
file-reading actions meet them, and the driver theorem then computes the result
with no IO. -/
example (fname : String) (bytes : ByteArray) (config : ModeConfig) (d : Nat)
    (w : Void IO.RealWorld)
    (h_noreq : ErrorNotRequest (checkBytesCoreAt fname bytes config).error?) :
    ∃ stF : IncludeDriverState,
      processFileSinglePassWithIO (fun _ => pure ⟨fname⟩) (fun _ => pure bytes) fname config
        (d + 1) (initDriverState config) w = .ok (.ok stF) w ∧
      stF.parser.done stF.base = checkBytesCoreAt fname bytes config := by
  refine processFileSinglePassWithIO_root _ _ fname config d w w w fname bytes ?_ rfl h_noreq
  cases h : config.literalIncludePaths
  · exact Or.inr ⟨rfl, ⟨fname⟩, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩

end Metamath.RootFileCheck
