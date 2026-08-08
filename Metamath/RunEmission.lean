/-
Execution-indexed emission chronology for the single-pass driver.

`RunTrace` (PrefixWitnessCheckBytes) chains recorded `feedToken` transitions
through `db.objects` seams only, so it certifies registry continuity — not
that each recorded parser state belongs to one particular IO execution.

This module closes that gap.  Each driver layer gets a proof-only *emission
relation* whose constructors premise on equations about the actual executable
functions applied to the actual inputs (only the byte loop `ParserState.feed`
needs a genuinely recursive mirror; every layer above premises on the
executable's own step functions).  Together with:

- an *emission theorem* — the successful run inhabits the relation with a
  step list that simultaneously carries the existing `RunTrace`/`StepsInv`
  chronology; and
- a *determinism theorem* — the relation admits at most one step list per
  input (and per world at the IO layers),

the step list obtained from a successful `checkSinglePass` invocation is THE
emission chronology of that invocation: every recorded state is a state the
run itself produced, in the order the run produced them.
-/

import Metamath.StoredStatementSoundness

set_option autoImplicit false

namespace Metamath.RunEmission

open Std (HashSet)
open Metamath.Verify
open Metamath.PrefixWitnessCheckBytes
open Metamath.ParserOps (ParserStateInv feedToken_maintains_stateInv)

/-! ## Byte-loop emission

`FeedEmission base arr i rs s steps` mirrors the branch structure of
`ParserState.feed`: it holds exactly when the byte loop entered at index `i`
with pending-token state `rs` and parser state `s` records precisely the
`feedToken` transitions in `steps`.  The output parser state is not carried:
it is `ParserState.feed base arr i rs s`, a function of the inputs. -/

inductive FeedEmission (base : Nat) (arr : ByteArray) :
    Nat → ParserState.FeedState → ParserState → List RunStep → Prop
  /-- Input exhausted: the trailing token (if any) is buffered, not flushed. -/
  | eof (i : Nat) (rs : ParserState.FeedState) (s : ParserState)
      (h : ¬ i < arr.size) :
      FeedEmission base arr i rs s []
  /-- Whitespace while between tokens: line bookkeeping only. -/
  | wsSkip (i : Nat) (s : ParserState) (steps : List RunStep)
      (h : i < arr.size) (h_ws : isWhitespace (arr[i]'h) = true)
      (h_rest : FeedEmission base arr (i + 1) .ws
        (s.updateLine (base + i) (arr[i]'h)) steps) :
      FeedEmission base arr i .ws s steps
  /-- Whitespace terminating a token of this chunk: flush it and continue. -/
  | flushThis (i off : Nat) (s : ParserState) (steps : List RunStep)
      (h : i < arr.size) (h_ws : isWhitespace (arr[i]'h) = true)
      (h_ok : ((s.feedToken (base + off)
          (ByteSlice.mk arr off (i - off))).updateLine
            (base + i) (arr[i]'h)).db.error? = none)
      (h_rest : FeedEmission base arr (i + 1) .ws
        ((s.feedToken (base + off) (ByteSlice.mk arr off (i - off))).updateLine
          (base + i) (arr[i]'h)) steps) :
      FeedEmission base arr i (.token (.this off)) s
        (⟨s, base + off, ByteSlice.mk arr off (i - off)⟩ :: steps)
  /-- Whitespace terminating a token of this chunk whose flush errors: the
  loop freezes with that flush as the final recorded transition. -/
  | flushThisFreeze (i off : Nat) (s : ParserState)
      (h : i < arr.size) (h_ws : isWhitespace (arr[i]'h) = true)
      (h_err : ((s.feedToken (base + off)
          (ByteSlice.mk arr off (i - off))).updateLine
            (base + i) (arr[i]'h)).db.error? ≠ none) :
      FeedEmission base arr i (.token (.this off)) s
        [⟨s, base + off, ByteSlice.mk arr off (i - off)⟩]
  /-- Whitespace terminating a token spliced from the previous chunk. -/
  | flushOld (i off base' : Nat) (arrOld : ByteArray) (s : ParserState)
      (steps : List RunStep)
      (h : i < arr.size) (h_ws : isWhitespace (arr[i]'h) = true)
      (h_ok : ((s.feedToken (base' + off)
          (ByteSlice.mk (arr.copySlice 0 arrOld arrOld.size i false) off
            (arrOld.size - off + i))).updateLine
            (base + i) (arr[i]'h)).db.error? = none)
      (h_rest : FeedEmission base arr (i + 1) .ws
        ((s.feedToken (base' + off)
          (ByteSlice.mk (arr.copySlice 0 arrOld arrOld.size i false) off
            (arrOld.size - off + i))).updateLine
            (base + i) (arr[i]'h)) steps) :
      FeedEmission base arr i (.token (.old base' off arrOld)) s
        (⟨s, base' + off,
          ByteSlice.mk (arr.copySlice 0 arrOld arrOld.size i false) off
            (arrOld.size - off + i)⟩ :: steps)
  /-- Spliced-token flush whose result errors: freeze after recording it. -/
  | flushOldFreeze (i off base' : Nat) (arrOld : ByteArray) (s : ParserState)
      (h : i < arr.size) (h_ws : isWhitespace (arr[i]'h) = true)
      (h_err : ((s.feedToken (base' + off)
          (ByteSlice.mk (arr.copySlice 0 arrOld arrOld.size i false) off
            (arrOld.size - off + i))).updateLine
            (base + i) (arr[i]'h)).db.error? ≠ none) :
      FeedEmission base arr i (.token (.old base' off arrOld)) s
        [⟨s, base' + off,
          ByteSlice.mk (arr.copySlice 0 arrOld arrOld.size i false) off
            (arrOld.size - off + i)⟩]
  /-- Non-whitespace while between tokens: begin a token at this index. -/
  | accumWs (i : Nat) (s : ParserState) (steps : List RunStep)
      (h : i < arr.size) (h_ws : ¬ isWhitespace (arr[i]'h) = true)
      (h_rest : FeedEmission base arr (i + 1) (.token (.this i)) s steps) :
      FeedEmission base arr i .ws s steps
  /-- Non-whitespace inside a token: extend it. -/
  | accumTok (i : Nat) (ot : ParserState.OldToken) (s : ParserState)
      (steps : List RunStep)
      (h : i < arr.size) (h_ws : ¬ isWhitespace (arr[i]'h) = true)
      (h_rest : FeedEmission base arr (i + 1) (.token ot) s steps) :
      FeedEmission base arr i (.token ot) s steps

/-- The byte loop inhabits its emission relation, and the inhabiting step
list carries the invariant-bearing registry chronology. -/
theorem feed_emission_trace (base : Nat) (arr : ByteArray) (i : Nat)
    (rs : ParserState.FeedState) (s : ParserState)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      FeedEmission base arr i rs s steps ∧
      RunTrace s steps (ParserState.feed base arr i rs s) ∧ StepsInv steps := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState),
      ParserOps.ParserStateInv s →
      ProofGhost s.db s.tokp →
      s.db.error? = none →
      s.db.config.rejectUnknownSteps = true →
      s.db.config.allowDuplicateFloat = false →
      arr.size - i = m →
      ∃ steps : List RunStep,
        FeedEmission base arr i rs s steps ∧
        RunTrace s steps (ParserState.feed base arr i rs s) ∧ StepsInv steps)
    ?base ?step (arr.size - i) i rs s h_inv h_ghost h_err0 h_strict h_no_dup rfl
  · intro i rs s _ _ _ _ _ hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    refine ⟨[], .eof i rs s hi, ?_, stepsInv_nil⟩
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
            obtain ⟨steps, h_em, h_tr, h_si⟩ := ih (i + 1) .ws
              (s.updateLine (base + i) arr[i])
              (parserStateInv_updateLine s _ _ h_inv)
              (proofGhost_updateLine s _ _ h_ghost)
              (by simpa using h_err0) (by simpa using h_strict)
              (by simpa using h_no_dup) hs'
            refine ⟨steps, .wsSkip i s steps hi h_ws h_em, ?_, h_si⟩
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
                    refine ⟨[⟨s, base + off, ByteSlice.mk arr off (i - off)⟩],
                      .flushThisFreeze i off s hi h_ws (by rw [h_g]; simp),
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
                    obtain ⟨steps, h_em, h_tr, h_si⟩ := ih (i + 1) .ws
                      ((s.feedToken (base + off)
                        (ByteSlice.mk arr off (i - off))).updateLine
                          (base + i) arr[i])
                      (parserStateInv_updateLine _ _ _ h_inv1)
                      (proofGhost_updateLine _ _ _ h_ghost1)
                      (by simpa using h_flush_ok)
                      (by simpa using h_strict) (by simpa using h_no_dup) hs'
                    refine ⟨⟨s, base + off, ByteSlice.mk arr off (i - off)⟩ :: steps,
                      .flushThis i off s steps hi h_ws h_g h_em,
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
                      .flushOldFreeze i off base' arr' s hi h_ws (by rw [h_g]; simp),
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
                    obtain ⟨steps, h_em, h_tr, h_si⟩ := ih (i + 1) .ws
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
                      .flushOld i off base' arr' s steps hi h_ws h_g h_em,
                      ?_, stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ h_si⟩
                    unfold ParserState.feed
                    simp only [hi, ↓reduceDIte, h_ws, if_true, h_g]
                    exact .cons _ _ _ _ rfl
                      (h_tr.retarget (by simp [RunStep.next]))
      · obtain ⟨steps, h_em, h_tr, h_si⟩ := ih (i + 1)
          (if let .ws := rs then .token (.this i) else rs) s
          h_inv h_ghost h_err0 h_strict h_no_dup hs'
        refine ⟨steps, ?_, ?_, h_si⟩
        · cases rs with
          | ws => exact .accumWs i s steps hi h_ws h_em
          | token ot => exact .accumTok i ot s steps hi h_ws h_em
        · unfold ParserState.feed
          simp only [hi, ↓reduceDIte, h_ws, if_false, Bool.false_eq_true]
          cases rs with
          | ws => exact h_tr
          | token ot => exact h_tr
    · exact absurd hs (by omega)

/-- The byte loop emits at most one step list per input. -/
theorem FeedEmission.unique {base : Nat} {arr : ByteArray} :
    ∀ {i : Nat} {rs : ParserState.FeedState} {s : ParserState}
      {steps₁ steps₂ : List RunStep},
      FeedEmission base arr i rs s steps₁ →
      FeedEmission base arr i rs s steps₂ → steps₁ = steps₂ := by
  intro i rs s steps₁ steps₂ h₁ h₂
  induction h₁ generalizing steps₂ with
  | eof i rs s h =>
      cases h₂ with
      | eof => rfl
      | wsSkip _ _ _ h' => exact absurd h' h
      | flushThis _ _ _ _ h' => exact absurd h' h
      | flushThisFreeze _ _ _ h' => exact absurd h' h
      | flushOld _ _ _ _ _ _ h' => exact absurd h' h
      | flushOldFreeze _ _ _ _ _ h' => exact absurd h' h
      | accumWs _ _ _ h' => exact absurd h' h
      | accumTok _ _ _ _ h' => exact absurd h' h
  | wsSkip i s steps h h_ws h_rest ih =>
      cases h₂ with
      | eof _ _ _ h' => exact absurd h h'
      | wsSkip _ _ _ h' h_ws' h_rest' => exact ih h_rest'
      | accumWs _ _ _ h' h_ws' => exact absurd h_ws h_ws'
  | flushThis i off s steps h h_ws h_ok h_rest ih =>
      cases h₂ with
      | eof _ _ _ h' => exact absurd h h'
      | flushThis _ _ _ _ h' h_ws' h_ok' h_rest' =>
          exact congrArg _ (ih h_rest')
      | flushThisFreeze _ _ _ h' h_ws' h_err' => exact absurd h_ok h_err'
      | accumTok _ _ _ _ h' h_ws' => exact absurd h_ws h_ws'
  | flushThisFreeze i off s h h_ws h_err =>
      cases h₂ with
      | eof _ _ _ h' => exact absurd h h'
      | flushThis _ _ _ _ h' h_ws' h_ok' => exact absurd h_ok' h_err
      | flushThisFreeze => rfl
      | accumTok _ _ _ _ h' h_ws' => exact absurd h_ws h_ws'
  | flushOld i off base' arrOld s steps h h_ws h_ok h_rest ih =>
      cases h₂ with
      | eof _ _ _ h' => exact absurd h h'
      | flushOld _ _ _ _ _ _ h' h_ws' h_ok' h_rest' =>
          exact congrArg _ (ih h_rest')
      | flushOldFreeze _ _ _ _ _ h' h_ws' h_err' => exact absurd h_ok h_err'
      | accumTok _ _ _ _ h' h_ws' => exact absurd h_ws h_ws'
  | flushOldFreeze i off base' arrOld s h h_ws h_err =>
      cases h₂ with
      | eof _ _ _ h' => exact absurd h h'
      | flushOld _ _ _ _ _ _ h' h_ws' h_ok' => exact absurd h_ok' h_err
      | flushOldFreeze => rfl
      | accumTok _ _ _ _ h' h_ws' => exact absurd h_ws h_ws'
  | accumWs i s steps h h_ws h_rest ih =>
      cases h₂ with
      | eof _ _ _ h' => exact absurd h h'
      | wsSkip _ _ _ h' h_ws' => exact absurd h_ws' h_ws
      | accumWs _ _ _ h' h_ws' h_rest' => exact ih h_rest'
  | accumTok i ot s steps h h_ws h_rest ih =>
      cases h₂ with
      | eof _ _ _ h' => exact absurd h h'
      | flushThis _ _ _ _ h' h_ws' => exact absurd h_ws' h_ws
      | flushThisFreeze _ _ _ h' h_ws' => exact absurd h_ws' h_ws
      | flushOld _ _ _ _ _ _ h' h_ws' => exact absurd h_ws' h_ws
      | flushOldFreeze _ _ _ _ _ h' h_ws' => exact absurd h_ws' h_ws
      | accumTok _ _ _ _ h' h_ws' h_rest' => exact ih h_rest'

/-! ## Chunk-entry emission

`feedAll` prepends the buffered cross-chunk token (if any) and enters the
byte loop at index 0; `flushPendingToken` finalizes the one buffered token
without rereading source bytes. -/

/-- Emission of one `feedAll` call, discriminated by the buffered-token
state exactly as the executable discriminates. -/
inductive FeedAllEmission (base : Nat) (arr : ByteArray) :
    ParserState → List RunStep → Prop
  | ws (s : ParserState) (steps : List RunStep)
      (h : s.charp = .ws)
      (h_rest : FeedEmission base arr 0 .ws s steps) :
      FeedAllEmission base arr s steps
  | token (s : ParserState) (base' : Nat) (tk : ByteSliceT)
      (steps : List RunStep)
      (h : s.charp = .token base' tk)
      (h_rest : FeedEmission base arr 0
        (.token (.old base' tk.start tk.byteArray))
        { s with charp := default } steps) :
      FeedAllEmission base arr s steps

theorem feedAll_emission_trace (s : ParserState) (base : Nat) (arr : ByteArray)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_strict : s.db.config.rejectUnknownSteps = true)
    (h_no_dup : s.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      FeedAllEmission base arr s steps ∧
      RunTrace s steps (s.feedAll base arr) ∧ StepsInv steps := by
  unfold ParserState.feedAll
  cases h_charp : s.charp with
  | ws =>
      obtain ⟨steps, h_em, h_tr, h_si⟩ := feed_emission_trace base arr 0 .ws s
        h_inv h_ghost h_err0 h_strict h_no_dup
      exact ⟨steps, .ws s steps h_charp h_em, h_tr, h_si⟩
  | token base' tk =>
      obtain ⟨steps, h_em, h_tr, h_si⟩ := feed_emission_trace base arr 0
        (.token (.old base' tk.start tk.byteArray))
        ({ s with charp := default }) h_inv h_ghost h_err0 h_strict h_no_dup
      refine ⟨steps, .token s base' tk steps h_charp h_em, ?_, h_si⟩
      dsimp only []
      refine RunTrace.retarget ?_ h_tr
      rfl

theorem FeedAllEmission.unique {base : Nat} {arr : ByteArray}
    {s : ParserState} {steps₁ steps₂ : List RunStep}
    (h₁ : FeedAllEmission base arr s steps₁)
    (h₂ : FeedAllEmission base arr s steps₂) : steps₁ = steps₂ := by
  cases h₁ with
  | ws _ h h_rest =>
      cases h₂ with
      | ws _ h' h_rest' => exact h_rest.unique h_rest'
      | token _ _ _ h' h_rest' => rw [h] at h'; exact absurd h' (by simp)
  | token base' tk _ h h_rest =>
      cases h₂ with
      | ws _ h' h_rest' => rw [h] at h'; exact absurd h' (by simp)
      | token base'' tk'' _ h' h_rest' =>
          rw [h] at h'
          injection h' with hb ht
          subst hb; subst ht
          exact h_rest.unique h_rest'

/-- Emission of one `flushPendingToken` call. -/
inductive FlushEmission : ParserState → List RunStep → Prop
  | ws (s : ParserState) (h : s.charp = .ws) : FlushEmission s []
  | token (s : ParserState) (pos : Nat) (tk : ByteSliceT)
      (h : s.charp = .token pos tk) :
      FlushEmission s [⟨s, pos, tk.toSlice⟩]

theorem flushPendingToken_emission_trace (s : ParserState)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none) :
    ∃ steps : List RunStep,
      FlushEmission s steps ∧
      RunTrace s steps (flushPendingToken s) ∧ StepsInv steps := by
  unfold flushPendingToken
  cases h_charp : s.charp with
  | ws => exact ⟨[], .ws s h_charp, .nil _ _ rfl, stepsInv_nil⟩
  | token pos tk =>
      refine ⟨[⟨s, pos, tk.toSlice⟩], .token s pos tk h_charp, ?_,
        stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ stepsInv_nil⟩
      exact .cons _ _ _ _ rfl (.nil _ _ rfl)

theorem FlushEmission.unique {s : ParserState} {steps₁ steps₂ : List RunStep}
    (h₁ : FlushEmission s steps₁) (h₂ : FlushEmission s steps₂) :
    steps₁ = steps₂ := by
  cases h₁ with
  | ws h =>
      cases h₂ with
      | ws => rfl
      | token _ _ h' => rw [h] at h'; exact absurd h' (by simp)
  | token pos tk h =>
      cases h₂ with
      | ws h' => rw [h] at h'; exact absurd h' (by simp)
      | token pos' tk' h' =>
          rw [h] at h'
          injection h' with hp ht
          subst hp; subst ht
          rfl

/-! ## Frame-step emission

`FrameStepEmission st steps` mirrors `stepFrame`'s branch structure: injected
separator, exhausted frame (quiet or with one buffered token to flush), or a
live chunk feed.  The recorded steps are those of the inner byte-loop entry;
the driver's own bookkeeping (frame pop, include-request extraction, offset
advance) records nothing, exactly as the executable records nothing. -/

inductive FrameStepEmission : IncludeDriverState → List RunStep → Prop
  | stackEmpty (st : IncludeDriverState) (h : st.stack = []) :
      FrameStepEmission st []
  | sep (st : IncludeDriverState) (frame : IncludeDriverFrame)
      (rest : List IncludeDriverFrame) (steps : List RunStep)
      (h : st.stack = frame :: rest) (h_sep : frame.needsSep = true)
      (h_rest : FeedAllEmission st.base (ByteArray.empty.push ' '.toUInt8)
        st.parser steps) :
      FrameStepEmission st steps
  | exhaustedQuiet (st : IncludeDriverState) (frame : IncludeDriverFrame)
      (rest : List IncludeDriverFrame)
      (h : st.stack = frame :: rest) (h_sep : ¬ frame.needsSep = true)
      (h_exh : frame.offset ≥ frame.contents.size)
      (h_charp : st.parser.charp = .ws) :
      FrameStepEmission st []
  | exhaustedFlush (st : IncludeDriverState) (frame : IncludeDriverFrame)
      (rest : List IncludeDriverFrame) (pos : Nat) (tk : ByteSliceT)
      (steps : List RunStep)
      (h : st.stack = frame :: rest) (h_sep : ¬ frame.needsSep = true)
      (h_exh : frame.offset ≥ frame.contents.size)
      (h_charp : st.parser.charp = .token pos tk)
      (h_rest : FlushEmission
        { st.parser with sourceFile := frame.fname } steps) :
      FrameStepEmission st steps
  | live (st : IncludeDriverState) (frame : IncludeDriverFrame)
      (rest : List IncludeDriverFrame) (steps : List RunStep)
      (h : st.stack = frame :: rest) (h_sep : ¬ frame.needsSep = true)
      (h_exh : ¬ frame.offset ≥ frame.contents.size)
      (h_rest : FeedAllEmission st.base
        (frame.contents.extract frame.offset frame.contents.size)
        { st.parser with sourceFile := frame.fname } steps) :
      FrameStepEmission st steps

set_option linter.unusedSimpArgs false in
/- The scoped-off linter misfires here: the flagged rewrites drive the goal's
match reduction. -/
theorem stepFrame_emission_trace (st : IncludeDriverState)
    (h_dinv : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      FrameStepEmission st steps ∧
      RunTrace st.parser steps (frameStepParser (stepFrame st)) ∧
        StepsInv steps := by
  obtain ⟨h_pinv, h_ghost, h_err0⟩ := h_dinv
  unfold stepFrame
  cases h_stack : st.stack with
  | nil =>
      refine ⟨[], .stackEmpty st h_stack, ?_, stepsInv_nil⟩
      simp only [frameStepParser]
      exact .nil _ _ rfl
  | cons parent tail =>
      by_cases h_sep : parent.needsSep = true
      · obtain ⟨steps, h_em, h_tr, h_si⟩ := feedAll_emission_trace st.parser
          st.base (ByteArray.empty.push ' '.toUInt8) h_pinv h_ghost h_err0
          h_strict h_no_dup
        refine ⟨steps, .sep st parent tail steps h_stack h_sep h_em, ?_, h_si⟩
        simp only [if_pos h_sep, frameStepParser, flushChunkToParser,
          ByteArray.isEmpty, ByteArray.size_push]
        exact h_tr
      · simp only [if_neg h_sep]
        by_cases h_exh : parent.offset ≥ parent.contents.size
        · rw [if_pos h_exh]
          cases h_charp : st.parser.charp with
          | ws =>
              refine ⟨[], .exhaustedQuiet st parent tail h_stack h_sep h_exh
                h_charp, ?_, stepsInv_nil⟩
              simp only [frameStepParser]
              exact .nil _ _ (popExhaustedFrame_objects _ _ _ _).symm
          | token cpos ctk =>
              obtain ⟨steps, h_em, h_tr, h_si⟩ := flushPendingToken_emission_trace
                ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState)
                (show ParserOps.ParserStateInv ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) from h_pinv)
                (show ProofGhost _ _ from h_ghost)
                (show _ = _ from h_err0)
              have h_em' : FrameStepEmission st steps := by
                refine .exhaustedFlush st parent tail cpos ctk steps h_stack
                  h_sep h_exh h_charp ?_
                have h_eq : ({ st.parser with sourceFile := parent.fname } : ParserState)
                    = ({ st.parser with charp := CharParser.token cpos ctk, sourceFile := parent.fname } : ParserState) := by
                  rw [← h_charp]
                rw [h_eq]
                exact h_em
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
                              refine ⟨steps, h_em', ?_, h_si⟩
                              simp only [frameStepParser]
                              refine RunTrace.retargetEnd (RunTrace.retarget ?_ h_tr) ?_ <;> rfl
                      | none =>
                          refine ⟨steps, h_em', ?_, h_si⟩
                          simp only [frameStepParser]
                          refine RunTrace.retarget ?_ h_tr
                          rfl
              | none =>
                  refine ⟨steps, h_em', ?_, h_si⟩
                  simp only [frameStepParser]
                  refine RunTrace.retargetEnd (RunTrace.retarget ?_ h_tr) ?_
                  · rfl
                  · exact (popExhaustedFrame_objects _ _ _ _).symm
        · rw [if_neg h_exh]
          obtain ⟨steps, h_em, h_tr, h_si⟩ := feedAll_emission_trace
            ({ st.parser with sourceFile := parent.fname } : ParserState)
            st.base (parent.contents.extract parent.offset parent.contents.size)
            (show ParserOps.ParserStateInv ({ st.parser with sourceFile := parent.fname } : ParserState) from h_pinv)
            (show ProofGhost _ _ from h_ghost)
            (show _ = _ from h_err0)
            (show _ = _ from h_strict)
            (show _ = _ from h_no_dup)
          have h_em' : FrameStepEmission st steps :=
            .live st parent tail steps h_stack h_sep h_exh h_em
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
                          refine ⟨steps, h_em', ?_, h_si⟩
                          simp only [frameStepParser]
                          refine RunTrace.retargetEnd (RunTrace.retarget ?_ h_tr) ?_ <;> rfl
                  | none =>
                      refine ⟨steps, h_em', ?_, h_si⟩
                      simp only [frameStepParser]
                      refine RunTrace.retarget ?_ h_tr
                      rfl
          | none =>
              refine ⟨steps, h_em', ?_, h_si⟩
              simp only [frameStepParser]
              refine RunTrace.retarget ?_ h_tr
              rfl

theorem FrameStepEmission.unique {st : IncludeDriverState}
    {steps₁ steps₂ : List RunStep}
    (h₁ : FrameStepEmission st steps₁)
    (h₂ : FrameStepEmission st steps₂) : steps₁ = steps₂ := by
  cases h₁ with
  | stackEmpty h =>
      cases h₂ with
      | stackEmpty => rfl
      | sep _ _ _ h' => rw [h] at h'; exact absurd h' (by simp)
      | exhaustedQuiet _ _ h' => rw [h] at h'
      | exhaustedFlush _ _ _ _ _ h' => rw [h] at h'; exact absurd h' (by simp)
      | live _ _ _ h' => rw [h] at h'; exact absurd h' (by simp)
  | sep frame rest _ h h_sep h_rest =>
      cases h₂ with
      | stackEmpty h' => rw [h'] at h; exact absurd h (by simp)
      | sep frame' rest' _ h' h_sep' h_rest' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact h_rest.unique h_rest'
      | exhaustedQuiet frame' rest' h' h_sep' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_sep h_sep'
      | exhaustedFlush frame' rest' _ _ _ h' h_sep' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_sep h_sep'
      | live frame' rest' _ h' h_sep' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_sep h_sep'
  | exhaustedQuiet frame rest h h_sep h_exh h_charp =>
      cases h₂ with
      | stackEmpty h' => rw [h'] at h
      | sep frame' rest' _ h' h_sep' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_sep' h_sep
      | exhaustedQuiet => rfl
      | exhaustedFlush frame' rest' _ _ _ h' h_sep' h_exh' h_charp' =>
          rw [h_charp] at h_charp'
          exact absurd h_charp' (by simp)
      | live frame' rest' _ h' h_sep' h_exh' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_exh h_exh'
  | exhaustedFlush frame rest pos tk _ h h_sep h_exh h_charp h_rest =>
      cases h₂ with
      | stackEmpty h' => rw [h'] at h; exact absurd h (by simp)
      | sep frame' rest' _ h' h_sep' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_sep' h_sep
      | exhaustedQuiet frame' rest' h' h_sep' h_exh' h_charp' =>
          rw [h_charp] at h_charp'
          exact absurd h_charp' (by simp)
      | exhaustedFlush frame' rest' pos' tk' _ h' h_sep' h_exh' h_charp' h_rest' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact h_rest.unique h_rest'
      | live frame' rest' _ h' h_sep' h_exh' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_exh h_exh'
  | live frame rest _ h h_sep h_exh h_rest =>
      cases h₂ with
      | stackEmpty h' => rw [h'] at h; exact absurd h (by simp)
      | sep frame' rest' _ h' h_sep' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_sep' h_sep
      | exhaustedQuiet frame' rest' h' h_sep' h_exh' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_exh' h_exh
      | exhaustedFlush frame' rest' _ _ _ h' h_sep' h_exh' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact absurd h_exh' h_exh
      | live frame' rest' _ h' h_sep' h_exh' h_rest' =>
          rw [h] at h'
          injection h' with hf hr
          subst hf
          exact h_rest.unique h_rest'

/-! ## Pure-phase emission

`PureStepsEmission st steps` mirrors `runPureSteps`: iterate `stepFrame`
until the pass finishes, an error stops it, or an include push needs IO.
Constructor premises are equations about `stepFrame` itself, so a derivation
is pinned to the executable's own phase computation. -/

inductive PureStepsEmission : IncludeDriverState → List RunStep → Prop
  | halt (st st' : IncludeDriverState) (steps : List RunStep)
      (h : stepFrame st = .done st')
      (h_fr : FrameStepEmission st steps) :
      PureStepsEmission st steps
  | interrupt (st : IncludeDriverState) (src inc : String) (d : Nat)
      (st' : IncludeDriverState) (steps : List RunStep)
      (h : stepFrame st = .push src inc d st')
      (h_fr : FrameStepEmission st steps) :
      PureStepsEmission st steps
  | stop (st st' : IncludeDriverState) (steps : List RunStep)
      (h : stepFrame st = .fed st')
      (h_err : st'.parser.db.error = true)
      (h_fr : FrameStepEmission st steps) :
      PureStepsEmission st steps
  | fed (st st' : IncludeDriverState) (steps₁ steps₂ : List RunStep)
      (h : stepFrame st = .fed st')
      (h_err : ¬ st'.parser.db.error = true)
      (h_fr : FrameStepEmission st steps₁)
      (h_rest : PureStepsEmission st' steps₂) :
      PureStepsEmission st (steps₁ ++ steps₂)

theorem runPureSteps_emission_trace (st : IncludeDriverState)
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      PureStepsEmission st steps ∧
      RunTrace st.parser steps (driverPhaseParser (runPureSteps st)) ∧
        StepsInv steps := by
  revert h h_strict h_no_dup
  fun_induction runPureSteps st
  case case1 st st' _h =>
      intro h hs hd
      obtain ⟨steps, em, tr, si⟩ := stepFrame_emission_trace st h hs hd
      rw [_h] at tr
      exact ⟨steps, .halt st st' steps _h em,
        by simpa [frameStepParser, driverPhaseParser] using tr, si⟩
  case case2 st sf incf d st' _h =>
      intro h hs hd
      obtain ⟨steps, em, tr, si⟩ := stepFrame_emission_trace st h hs hd
      rw [_h] at tr
      exact ⟨steps, .interrupt st sf incf d st' steps _h em,
        by simpa [frameStepParser, driverPhaseParser] using tr, si⟩
  case case3 st st' _h _h_err =>
      intro h hs hd
      obtain ⟨steps, em, tr, si⟩ := stepFrame_emission_trace st h hs hd
      rw [_h] at tr
      exact ⟨steps, .stop st st' steps _h (by simpa using _h_err) em,
        by simpa [frameStepParser, driverPhaseParser] using tr, si⟩
  case case4 st st' _h _h_err ih =>
      intro h hs hd
      obtain ⟨steps, em, tr, si⟩ := stepFrame_emission_trace st h hs hd
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
      obtain ⟨steps', em', tr', si'⟩ := ih h_inv' (h_cfg ▸ hs) (h_cfg ▸ hd)
      exact ⟨steps ++ steps',
        .fed st st' steps steps' _h (by simpa using _h_err) em em',
        tr.append tr', stepsInv_append si si'⟩

theorem PureStepsEmission.unique {st : IncludeDriverState}
    {steps₁ steps₂ : List RunStep}
    (h₁ : PureStepsEmission st steps₁)
    (h₂ : PureStepsEmission st steps₂) : steps₁ = steps₂ := by
  induction h₁ generalizing steps₂ with
  | halt st st' steps h h_fr =>
      cases h₂ with
      | halt _ st'' _ h' h_fr' => exact h_fr.unique h_fr'
      | interrupt _ _ _ _ _ _ h' _ => rw [h] at h'; exact absurd h' (by simp)
      | stop _ _ _ h' _ _ => rw [h] at h'; exact absurd h' (by simp)
      | fed _ _ _ _ h' _ _ _ => rw [h] at h'; exact absurd h' (by simp)
  | interrupt st src inc d st' steps h h_fr =>
      cases h₂ with
      | halt _ _ _ h' _ => rw [h] at h'; exact absurd h' (by simp)
      | interrupt _ _ _ _ _ _ h' h_fr' => exact h_fr.unique h_fr'
      | stop _ _ _ h' _ _ => rw [h] at h'; exact absurd h' (by simp)
      | fed _ _ _ _ h' _ _ _ => rw [h] at h'; exact absurd h' (by simp)
  | stop st st' steps h h_err h_fr =>
      cases h₂ with
      | halt _ _ _ h' _ => rw [h] at h'; exact absurd h' (by simp)
      | interrupt _ _ _ _ _ _ h' _ => rw [h] at h'; exact absurd h' (by simp)
      | stop _ _ _ h' h_err' h_fr' => exact h_fr.unique h_fr'
      | fed _ st'' _ _ h' h_err' _ _ =>
          rw [h] at h'
          injection h' with h'
          subst h'
          exact absurd h_err h_err'
  | fed st st' steps₁' steps₂' h h_err h_fr h_rest ih =>
      cases h₂ with
      | halt _ _ _ h' _ => rw [h] at h'; exact absurd h' (by simp)
      | interrupt _ _ _ _ _ _ h' _ => rw [h] at h'; exact absurd h' (by simp)
      | stop _ st'' _ h' h_err' _ =>
          rw [h] at h'
          injection h' with h'
          subst h'
          exact absurd h_err' h_err
      | fed _ st'' steps₁'' steps₂'' h' h_err' h_fr' h_rest' =>
          rw [h] at h'
          injection h' with h'
          subst h'
          rw [h_fr.unique h_fr', ih h_rest']

/-! ## Driver-loop emission (IO layer)

`IO` in this toolchain is a function of the world token, so the loop applied
to a fixed world is deterministic; the emission relation threads the worlds
through its include-resolution premises and is therefore single-valued per
`(fuel, state, world)`. -/

/-- `runDriverLoop_ok_inversion` strengthened with the world bookkeeping of
the immediate-finish branches. -/
theorem runDriverLoop_ok_inversion_worlds
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w') :
    ((runPureSteps st = .done rst ∨ runPureSteps st = .stopped rst) ∧ w' = w)
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
      exact Or.inl ⟨Or.inl (by rw [g1]), g2.symm⟩
  | stopped st2 =>
      simp only [h_phase] at h_run
      rw [io_pure_apply] at h_run
      injection h_run with g1 g2
      injection g1 with g1
      exact Or.inl ⟨Or.inr (by rw [g1]), g2.symm⟩
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

/-- Emission of the driver loop: alternate pure phases with include
resolutions, threading the world through each resolution. -/
inductive LoopEmission (rp : String → IO System.FilePath)
    (rf : String → IO ByteArray) :
    Nat → IncludeDriverState → Void IO.RealWorld →
    List RunStep → IncludeDriverState → Void IO.RealWorld → Prop
  | finishDone (fuel : Nat) (st rst : IncludeDriverState)
      (w : Void IO.RealWorld) (steps : List RunStep)
      (h : runPureSteps st = .done rst)
      (h_p : PureStepsEmission st steps) :
      LoopEmission rp rf fuel st w steps rst w
  | finishStopped (fuel : Nat) (st rst : IncludeDriverState)
      (w : Void IO.RealWorld) (steps : List RunStep)
      (h : runPureSteps st = .stopped rst)
      (h_p : PureStepsEmission st steps) :
      LoopEmission rp rf fuel st w steps rst w
  | resolve (fuel' : Nat) (st : IncludeDriverState)
      (w : Void IO.RealWorld) (src inc : String) (d : Nat)
      (st' st'' : IncludeDriverState) (w₂ : Void IO.RealWorld)
      (rst : IncludeDriverState) (w' : Void IO.RealWorld)
      (steps₁ steps₂ : List RunStep)
      (h : runPureSteps st = .push src inc d st')
      (h_res : resolvePushWithIO rp rf src inc d st' w = .ok (.ok st'') w₂)
      (h_p : PureStepsEmission st steps₁)
      (h_rest : LoopEmission rp rf fuel' st'' w₂ steps₂ rst w') :
      LoopEmission rp rf (fuel' + 1) st w (steps₁ ++ steps₂) rst w'

theorem runDriverLoop_emission_trace
    (rp : String → IO System.FilePath) (rf : String → IO ByteArray)
    (fuel : Nat) (st : IncludeDriverState) (w w' : Void IO.RealWorld)
    (rst : IncludeDriverState)
    (h_run : runDriverLoop rp rf fuel st w = .ok (.ok rst) w')
    (h : DriverInv st.parser)
    (h_strict : st.parser.db.config.rejectUnknownSteps = true)
    (h_no_dup : st.parser.db.config.allowDuplicateFloat = false) :
    ∃ steps : List RunStep,
      LoopEmission rp rf fuel st w steps rst w' ∧
      RunTrace st.parser steps rst.parser ∧ StepsInv steps := by
  induction fuel generalizing st w with
  | zero =>
      rcases runDriverLoop_ok_inversion_worlds rp rf 0 st w w' rst h_run with
        ⟨h_d | h_s, h_w⟩ | ⟨src, inc, d, st', fuel', st'', w₂, h_eq, _, _, _⟩
      · obtain ⟨steps, em, tr, si⟩ := runPureSteps_emission_trace st h h_strict
          h_no_dup
        rw [h_d] at tr
        subst h_w
        exact ⟨steps, .finishDone 0 st rst w' steps h_d em,
          by simpa [driverPhaseParser] using tr, si⟩
      · obtain ⟨steps, em, tr, si⟩ := runPureSteps_emission_trace st h h_strict
          h_no_dup
        rw [h_s] at tr
        subst h_w
        exact ⟨steps, .finishStopped 0 st rst w' steps h_s em,
          by simpa [driverPhaseParser] using tr, si⟩
      · exact absurd h_eq (by omega)
  | succ fuel' ih =>
      rcases runDriverLoop_ok_inversion_worlds rp rf (fuel' + 1) st w w' rst
          h_run with
        ⟨h_d | h_s, h_w⟩ | ⟨src, inc, d, st', f2, st'', w₂, h_eq, h_p, h_res, h_rec⟩
      · obtain ⟨steps, em, tr, si⟩ := runPureSteps_emission_trace st h h_strict
          h_no_dup
        rw [h_d] at tr
        subst h_w
        exact ⟨steps, .finishDone (fuel' + 1) st rst w' steps h_d em,
          by simpa [driverPhaseParser] using tr, si⟩
      · obtain ⟨steps, em, tr, si⟩ := runPureSteps_emission_trace st h h_strict
          h_no_dup
        rw [h_s] at tr
        subst h_w
        exact ⟨steps, .finishStopped (fuel' + 1) st rst w' steps h_s em,
          by simpa [driverPhaseParser] using tr, si⟩
      · have h_f2 : f2 = fuel' := by omega
        rw [h_f2] at h_rec
        obtain ⟨steps, em, tr, si⟩ := runPureSteps_emission_trace st h h_strict
          h_no_dup
        rw [h_p] at tr
        simp only [driverPhaseParser] at tr
        obtain ⟨h_db, h_tokp, h_base⟩ :=
          resolvePushWithIO_ok_post rp rf src inc d st' st'' w w₂ h_res
        have h1 := runPureSteps_driverPhaseInv st h h_strict h_no_dup
        rw [h_p] at h1
        simp only [DriverPhaseInv] at h1
        have h_inv'' := driverInv_of_db_tokp_eq st''.parser st'.parser h_db
          h_tokp h1
        have h_cfg := runPureSteps_db_config st
        rw [h_p] at h_cfg
        simp only [driverPhaseParser] at h_cfg
        have h_cfg'' : st''.parser.db.config = st.parser.db.config := by
          rw [h_db, h_cfg]
        obtain ⟨steps', em', tr', si'⟩ := ih st'' w₂ h_rec h_inv''
          (h_cfg'' ▸ h_strict) (h_cfg'' ▸ h_no_dup)
        exact ⟨steps ++ steps',
          .resolve fuel' st w src inc d st' st'' w₂ rst w' steps steps' h_p
            h_res em em',
          tr.append (tr'.retarget (by rw [h_db])), stepsInv_append si si'⟩

theorem LoopEmission.unique
    {rp : String → IO System.FilePath} {rf : String → IO ByteArray} :
    ∀ {fuel : Nat} {st : IncludeDriverState} {w : Void IO.RealWorld}
      {steps₁ steps₂ : List RunStep} {rst₁ rst₂ : IncludeDriverState}
      {w₁ w₂ : Void IO.RealWorld},
      LoopEmission rp rf fuel st w steps₁ rst₁ w₁ →
      LoopEmission rp rf fuel st w steps₂ rst₂ w₂ →
      steps₁ = steps₂ ∧ rst₁ = rst₂ ∧ w₁ = w₂ := by
  intro fuel st w steps₁ steps₂ rst₁ rst₂ w₁ w₂ h₁ h₂
  induction h₁ generalizing steps₂ rst₂ w₂ with
  | finishDone fuel st rst w steps h h_p =>
      cases h₂ with
      | finishDone _ _ rst' _ _ h' h_p' =>
          rw [h] at h'
          injection h' with h'
          exact ⟨h_p.unique h_p', h', rfl⟩
      | finishStopped _ _ rst' _ _ h' h_p' =>
          rw [h] at h'
          exact absurd h' (by simp)
      | resolve _ _ _ _ _ _ _ _ _ _ _ _ _ h' =>
          rw [h] at h'
          exact absurd h' (by simp)
  | finishStopped fuel st rst w steps h h_p =>
      cases h₂ with
      | finishDone _ _ rst' _ _ h' h_p' =>
          rw [h] at h'
          exact absurd h' (by simp)
      | finishStopped _ _ rst' _ _ h' h_p' =>
          rw [h] at h'
          injection h' with h'
          exact ⟨h_p.unique h_p', h', rfl⟩
      | resolve _ _ _ _ _ _ _ _ _ _ _ _ _ h' =>
          rw [h] at h'
          exact absurd h' (by simp)
  | resolve fuel' st w src inc d st' st'' w₂' rst w' steps₁' steps₂' h h_res
      h_p h_rest ih =>
      cases h₂ with
      | finishDone _ _ rst' _ _ h' h_p' =>
          rw [h] at h'
          exact absurd h' (by simp)
      | finishStopped _ _ rst' _ _ h' h_p' =>
          rw [h] at h'
          exact absurd h' (by simp)
      | resolve _ _ _ src2 inc2 d2 st'2 st''2 w₂2 rst2 w'2 steps₁2 steps₂2
          h' h_res' h_p' h_rest' =>
          rw [h] at h'
          injection h' with hsrc hinc hd hst
          subst hsrc; subst hinc; subst hd; subst hst
          rw [h_res] at h_res'
          injection h_res' with hst2 hw2
          injection hst2 with hst2
          subst hst2; subst hw2
          obtain ⟨hs, hr, hw⟩ := ih h_rest'
          exact ⟨by rw [h_p.unique h_p', hs], hr, hw⟩

/-- The EOF seam: `done` records at most the final flush, and the recorded
step is exactly the `FlushEmission` of the pre-`done` state. -/
theorem done_emission_seam (s : ParserState) (base : Nat)
    (h_inv : ParserOps.ParserStateInv s)
    (h_ghost : ProofGhost s.db s.tokp)
    (h_err0 : s.db.error? = none)
    (h_success : (ParserState.done s base).error? = none) :
    ∃ (steps : List RunStep) (q : ParserState),
      FlushEmission s steps ∧
      RunTrace s steps q ∧ StepsInv steps ∧
      ∀ n, q.db.find? n = (ParserState.done s base).find? n := by
  cases h_charp : s.charp with
  | ws =>
      exact ⟨[], s, .ws s h_charp, .nil _ _ rfl, stepsInv_nil,
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
        .token s pos tk h_charp,
        .cons _ _ _ _ rfl (.nil _ _ rfl),
        stepsInv_cons ⟨h_inv, h_ghost, h_err0⟩ stepsInv_nil,
        fun n => (done_find?_eq_flush s base pos tk n h_err0 h_charp h_e1).symm⟩

/-! ## Entrypoint emission

`SinglePassEmission fname config w steps p w'` states that the actual
`checkSinglePass` invocation on world `w` drives its include-aware recursion
so that `steps` is the recorded chronology, `p` the pre-`done` parser state,
and `w'` the returned world.  Constructor premises are equations about the
entrypoint's own IO actions applied to `w`, so the relation is single-valued
per `(fname, config, w)`. -/

inductive SinglePassEmission (fname : String) (config : ModeConfig)
    (w : Void IO.RealWorld) :
    List RunStep → ParserState → Void IO.RealWorld → Prop
  /-- The root file is suppressed by include-once bookkeeping: no bytes are
  fed; only the (empty) EOF seam of the initial state is recorded. -/
  | skip (w₂ : Void IO.RealWorld) (pr2 seen2 : HashSet String)
      (steps : List RunStep)
      (h_prep : prepareIncludeFrameWithIO (fun path => IO.FS.realPath path)
          (fun path => IO.FS.readBinFile path) fname config.maxIncludeDepth
          ((singlePassInitialState config).db.scopes.size)
          config.rejectIncludeCycles config.literalIncludePaths
          (HashSet.emptyWithCapacity 16) (HashSet.emptyWithCapacity 16) w
        = .ok (.ok (none, pr2, seen2)) w₂)
      (h_done : FlushEmission (singlePassInitialState config) steps) :
      SinglePassEmission fname config w steps (singlePassInitialState config) w₂
  /-- The root frame is admitted and the driver loop runs to completion,
  followed by the EOF seam on the loop's final parser state. -/
  | driven (w₂ w₃ : Void IO.RealWorld) (rootFrame : IncludeDriverFrame)
      (pr2 seen2 : HashSet String) (rst : IncludeDriverState)
      (steps₁ steps₂ : List RunStep)
      (h_prep : prepareIncludeFrameWithIO (fun path => IO.FS.realPath path)
          (fun path => IO.FS.readBinFile path) fname config.maxIncludeDepth
          ((singlePassInitialState config).db.scopes.size)
          config.rejectIncludeCycles config.literalIncludePaths
          (HashSet.emptyWithCapacity 16) (HashSet.emptyWithCapacity 16) w
        = .ok (.ok (some rootFrame, pr2, seen2)) w₂)
      (h_loop : LoopEmission (fun path => IO.FS.realPath path)
          (fun path => IO.FS.readBinFile path)
          config.maxIncludeResolutions
          { parser := singlePassInitialState config, base := 0,
            processing := pr2, seen := seen2, stack := [rootFrame] }
          w₂ steps₁ rst w₃)
      (h_done : FlushEmission rst.parser steps₂) :
      SinglePassEmission fname config w (steps₁ ++ steps₂) rst.parser w₃

/-- The successful entrypoint inhabits its emission relation with a step
list that simultaneously carries the invariant-bearing registry chronology
from the canonical initial state to a state pointwise equal to the returned
database. -/
theorem checkSinglePass_emission_chronology
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none) :
    ∃ (steps : List RunStep) (p : ParserState) (q : ParserState),
      SinglePassEmission fname config w steps p w' ∧
      RunTrace (singlePassInitialState config) steps q ∧
      StepsInv steps ∧
      (∀ n, q.db.find? n = db.find? n) := by
  unfold checkSinglePass at h_run
  rw [io_bind_apply] at h_run
  split at h_run
  case h_2 e w₂ heq => exact absurd h_run (by simp)
  case h_1 result w₂ heq =>
  rw [io_pure_apply] at h_run
  injection h_run with g1 g2
  subst g2
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
      subst g4
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
          subst g9
          injection g8 with g8
          have h_sp : s = ({ (default : ParserState) with
              db := { (default : DB) with config := config } } : ParserState) := by
            rw [← g5, ← g8]
            rfl
          subst h_sp
          obtain ⟨steps, q, h_em, tr, si, h_pt⟩ := done_emission_seam _ base
            (ParserOps.initState_inv config) trivial rfl h_de
          refine ⟨steps, _, q, .skip _ p2 s2 steps (by exact heq3) h_em,
            tr, si, h_pt⟩
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
          obtain ⟨steps1, em1, tr1, si1⟩ := runDriverLoop_emission_trace _ _ _ _
            _ _ _ heq2 h_inv0 h_cfg.1 h_cfg.2
          obtain ⟨steps2, q, em2, tr2, si2, h_pt⟩ := done_emission_seam
            st.parser base h_inv_end.1 h_inv_end.2.1 h_db_err h_de
          refine ⟨steps1 ++ steps2, _, q,
            .driven _ _ rootFrame p2 s2 st steps1 steps2 (by exact heq3)
              (by exact em1) em2,
            tr1.append tr2, stepsInv_append si1 si2, h_pt⟩
    · rw [if_neg h_g] at h_success
      exact absurd h_success (by simp)
  · rw [if_neg h_de] at h_success
    exact absurd h_success h_de

/-- The entrypoint emission relation is single-valued per invocation: the
step list, the pre-`done` parser state, and the returned world are all
functions of `(fname, config, w)`. -/
theorem SinglePassEmission.unique {fname : String} {config : ModeConfig}
    {w : Void IO.RealWorld} {steps₁ steps₂ : List RunStep}
    {p₁ p₂ : ParserState} {w₁ w₂ : Void IO.RealWorld}
    (h₁ : SinglePassEmission fname config w steps₁ p₁ w₁)
    (h₂ : SinglePassEmission fname config w steps₂ p₂ w₂) :
    steps₁ = steps₂ ∧ p₁ = p₂ ∧ w₁ = w₂ := by
  cases h₁ with
  | skip wa pra seena stepsa h_prep h_done =>
      cases h₂ with
      | skip wb prb seenb stepsb h_prep' h_done' =>
          rw [h_prep] at h_prep'
          injection h_prep' with hv hw
          injection hv with hv
          injection hv with hopt hps
          exact ⟨h_done.unique h_done', rfl, hw⟩
      | driven wb wc rootb prb seenb rstb stepsb1 stepsb2 h_prep' h_loop'
          h_done' =>
          rw [h_prep] at h_prep'
          injection h_prep' with hv hw
          injection hv with hv
          injection hv with hopt hps
          exact absurd hopt (by simp)
  | driven wa wb roota pra seena rsta stepsa1 stepsa2 h_prep h_loop h_done =>
      cases h₂ with
      | skip wc prb seenb stepsb h_prep' h_done' =>
          rw [h_prep] at h_prep'
          injection h_prep' with hv hw
          injection hv with hv
          injection hv with hopt hps
          exact absurd hopt (by simp)
      | driven wc wd rootb prb seenb rstb stepsb1 stepsb2 h_prep' h_loop'
          h_done' =>
          rw [h_prep] at h_prep'
          injection h_prep' with hv hw
          injection hv with hv
          injection hv with hopt hps
          injection hps with hpr hseen
          injection hopt with hroot
          subst hroot; subst hpr; subst hseen; subst hw
          obtain ⟨hs1, hrst, hw3⟩ := h_loop.unique h_loop'
          subst hrst
          exact ⟨by rw [hs1, h_done.unique h_done'], rfl, hw3⟩

/-! ## Execution-indexed chronology and crowns

The step list below is tied to the particular invocation twice over: the run
inhabits `SinglePassEmission` (refinement), and the relation is single-valued
per `(fname, config, w)` (determinism).  The registry-chronology clauses —
subdatabase, exactly-one creation, bound payloads — therefore hold of THE
run's own chronology, not merely of a registry-continuous candidate. -/

open Metamath
open Metamath.Spec
open Metamath.Spec.Equivalence
open Metamath.WF (WellFormedDB)
open Metamath.Kernel (toDatabase toFrame toExpr)
open Metamath.StoredStatementSoundness
open Metamath.StoredStatementSoundness.Runtime (AxiomEventOfTrace
  assertion_projection_of_find finishProof_storedStatement_prefixProvable
  toFrame_stable_of_find_mono)

/-- The execution-indexed strengthening of `CertifiedRegistryChronology`:
the same subdatabase / exactly-one / payload clauses, now over a step list
that the actual invocation emits (`SinglePassEmission`) and that is the only
list any invocation-emission can produce (single-valuedness). -/
def ExecutionChronology (fname : String) (config : ModeConfig)
    (w w' : Void IO.RealWorld) (db : DB) : Prop :=
  ∃ (steps : List RunStep) (p q : ParserState),
    SinglePassEmission fname config w steps p w' ∧
    (∀ (steps' : List RunStep) (p' : ParserState) (w'' : Void IO.RealWorld),
      SinglePassEmission fname config w steps' p' w'' → steps' = steps) ∧
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
          Verify.Formula.hasConstHead arr' = true ∧
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
            Spec.Provable Γ specFr (Kernel.toExpr f)))

/-- Every accepted certified run carries its execution-indexed chronology:
the emitted step list is the run's own, unique to the invocation, with the
subdatabase, exactly-one creation, and bound-payload clauses over it. -/
theorem checkSinglePass_execution_chronology_exactly_one
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none) :
    ExecutionChronology fname config w w' db := by
  obtain ⟨steps, p, q, h_em, tr, si, h_pt⟩ :=
    checkSinglePass_emission_chronology fname config h_cfg w w' db h_run
      h_success
  have h_init_none : ∀ n,
      (singlePassInitialState config).db.find? n = none := by
    intro n
    show ({ (default : DB) with config := config } : DB).objects[n]? = none
    exact default_db_find?_none n
  refine ⟨steps, p, q, h_em,
    fun steps' p' w'' h' => (h'.unique h_em).1, tr, si, h_pt, ?_, ?_, ?_⟩
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

/-- **Execution-indexed derived-rule elimination.**  The trace-relative
theorem `checkSinglePass_every_theorem_provable_from_trace_axiom_events`
strengthened to THE run's chronology: the step list is emitted by the actual
invocation and is the only list any emission of this invocation can produce.
Every stored `$p` statement is declaratively provable from the run-wide
`$a`-event theory of that chronology.  The construction eliminates `$p`
dependencies by cut along strict creation order, obtaining dependency
witnesses only from earlier registry entries and interpreting each written
proof against its pre-insertion database. -/
theorem checkSinglePass_every_theorem_provable_from_run_axiom_events
    (fname : String) (config : ModeConfig) (h_cfg : config.prefixCertified)
    (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname config w = .ok db w')
    (h_success : db.error? = none) :
    ∃ (Γ : Spec.Database) (steps : List RunStep) (p q : ParserState),
      Kernel.toDatabase db = some Γ ∧
      SinglePassEmission fname config w steps p w' ∧
      (∀ (steps' : List RunStep) (p' : ParserState)
        (w'' : Void IO.RealWorld),
        SinglePassEmission fname config w steps' p' w'' → steps' = steps) ∧
      RunTrace (singlePassInitialState config) steps q ∧
      (∀ n, q.db.find? n = db.find? n) ∧
      ∀ n f fr lbl, db.find? n = some (.assert f fr lbl) →
        ∃ (idx : Nat) (target : Spec.Frame),
          idx < steps.length ∧
          CreatesEntry (steps[idx]!) n (.assert f fr lbl) ∧
          Kernel.toFrame db fr = some target ∧
          Γ n = some (target, Kernel.toExpr f) ∧
          ((∃ (arr : Array Verify.Sym) (p : TokensParser),
              AxiomFinishEvent (steps[idx]!).state (steps[idx]!).pos
                (steps[idx]!).tk arr p ∧
              p.label = n ∧ f = arr ∧ lbl = n ∧
              AxiomEventOfTrace steps Γ
                (Semantic.statementOfFrame target (Kernel.toExpr f)))
            ∨ (∃ pr : ProofState,
              FinishProofEvent (steps[idx]!).state (steps[idx]!).pos
                (steps[idx]!).tk pr ∧
              pr.label = n ∧ pr.fmla = f ∧ pr.frame = fr ∧ lbl = n ∧
              (Semantic.statementOfFrame target (Kernel.toExpr f)).Provable
                (AxiomEventOfTrace steps Γ))) := by
  have h_final :=
    checkSinglePass_database_wellFormed_strong fname config h_cfg w w' db
      h_run h_success
  let Γ := Classical.choose h_final
  have h_final_tail := Classical.choose_spec h_final
  have h_final_db : Kernel.toDatabase db = some Γ := h_final_tail.1
  have h_strong :
      Spec.Equivalence.WellFormedDatabaseStrong Γ (Kernel.toConsts db) :=
    h_final_tail.2.1
  have h_final_wf : WF.WellFormedDB db := h_final_tail.2.2.1
  obtain ⟨steps, p, q, h_em, h_unique, h_trace, h_steps_inv, h_pointwise,
      h_member_mono, h_origin, h_payload⟩ :=
    checkSinglePass_execution_chronology_exactly_one fname config h_cfg w w'
      db h_run h_success
  let A := AxiomEventOfTrace steps Γ
  have h_created : ∀ idx : Nat, idx < steps.length →
      ∀ n f fr lbl,
        db.find? n = some (.assert f fr lbl) →
        CreatesEntry (steps[idx]!) n (.assert f fr lbl) →
        ∃ target : Spec.Frame,
          Kernel.toFrame db fr = some target ∧
          Γ n = some (target, Kernel.toExpr f) ∧
          (A (Semantic.statementOfFrame target (Kernel.toExpr f)) ∨
            (Semantic.statementOfFrame target (Kernel.toExpr f)).Provable A) := by
    intro idx
    induction idx using Nat.strongRecOn with
    | ind idx ih =>
      intro h_idx n f fr lbl h_find_final h_creates
      have h_step_mem : steps[idx]! ∈ steps := by
        rw [getElem!_pos steps idx h_idx]
        exact List.getElem_mem h_idx
      obtain ⟨h_inv, h_ghost, _h_error_free⟩ :=
        h_steps_inv (steps[idx]!) h_step_mem
      have h_mono : ∀ label obj,
          (steps[idx]!).state.db.find? label = some obj →
          db.find? label = some obj :=
        h_member_mono idx h_idx
      obtain ⟨target, h_target_final, h_lookup_final⟩ :=
        assertion_projection_of_find db Γ n f fr lbl h_final_db h_final_wf
          h_find_final
      rcases h_payload idx n f fr lbl h_idx h_creates with h_axiom | h_theorem
      · obtain ⟨arr, p2, h_event, h_label, h_fmla, h_lbl, _h_head,
          _h_fresh, _h_insert, _h_trim⟩ := h_axiom
        refine ⟨target, h_target_final, h_lookup_final, Or.inl ?_⟩
        change AxiomEventOfTrace steps Γ
          (Semantic.statementOfFrame target (Kernel.toExpr f))
        exact ⟨idx, n, f, fr, lbl, target, arr, p2, h_idx, h_creates,
          h_event, h_label, h_fmla, h_lbl, h_lookup_final, rfl⟩
      · obtain ⟨pr, prefixΓ, source, h_event, h_label, h_fmla, h_frame,
          h_lbl, _h_fresh, _h_insert, h_prefix_db, h_source,
          h_prefix_provable⟩ := h_theorem
        have h_trim :
            (steps[idx]!).state.db.trimFrame' pr.fmla = .ok pr.frame :=
          finishProofEvent_trimFrame (steps[idx]!).state (steps[idx]!).pos
            (steps[idx]!).tk pr h_ghost h_event
        have h_find_final' :
            db.find? n = some (.assert pr.fmla pr.frame n) := by
          simpa [h_label, h_fmla, h_frame, h_lbl] using h_find_final
        obtain ⟨storedTarget, h_stored_target, h_prefix_exact⟩ :=
          finishProof_storedStatement_prefixProvable
            (steps[idx]!).state.db db pr n prefixΓ Γ source h_inv.1
            h_inv.2.1.1 h_mono h_final_db h_strong h_final_wf h_find_final'
            h_trim h_prefix_db h_source (by
              rw [h_fmla]
              exact h_prefix_provable)
        have h_source_exact :
            (Semantic.statementOfFrame storedTarget
              (Kernel.toExpr pr.fmla)).Provable A := by
          apply Semantic.replaceDerivedAxioms h_prefix_exact
          intro a ha
          obtain ⟨l, specFr, e, h_lookup_prefix, h_ctx, h_afmla⟩ := ha
          obtain ⟨f₀, fr₀, lbl₀, h_find_prefix, h_toFrame_prefix,
              h_toExpr⟩ :=
            Kernel.toDatabase_lookup (steps[idx]!).state.db prefixΓ l specFr e
              h_prefix_db h_lookup_prefix
          have h_find_final₀ : db.find? l = some (.assert f₀ fr₀ lbl₀) :=
            h_mono l (.assert f₀ fr₀ lbl₀) h_find_prefix
          obtain ⟨j, ⟨h_j, h_create_j⟩, _h_unique_j⟩ :=
            h_origin l f₀ fr₀ lbl₀ h_find_final₀
          have h_j_lt : j < idx :=
            Metamath.StoredStatementSoundness.Runtime.RunTrace.creation_before_member
              h_trace idx j h_idx h_j l
              (.assert f₀ fr₀ lbl₀) h_find_prefix h_create_j
          obtain ⟨target₀, h_target_final₀, _h_lookup_final₀, h_old⟩ :=
            ih j h_j_lt h_j l f₀ fr₀ lbl₀ h_find_final₀ h_create_j
          have h_target_from_prefix : Kernel.toFrame db fr₀ = some specFr :=
            toFrame_stable_of_find_mono (steps[idx]!).state.db db fr₀ specFr
              h_mono h_toFrame_prefix
          have h_target_eq : target₀ = specFr := by
            rw [h_target_final₀] at h_target_from_prefix
            exact Option.some.inj h_target_from_prefix
          have h_stmt_eq :
              a = Semantic.statementOfFrame target₀ (Kernel.toExpr f₀) := by
            rw [h_target_eq, h_toExpr]
            cases a with
            | mk actx afmla =>
                dsimp only at h_ctx h_afmla ⊢
                unfold Semantic.statementOfFrame
                rw [h_ctx, h_afmla]
          rw [h_stmt_eq]
          rcases h_old with h_ax | h_th
          · exact Semantic.sourceAxiom_self_provable h_ax
          · exact h_th
        have h_stored_eq : storedTarget = target := by
          have h_target_final' : Kernel.toFrame db pr.frame = some target := by
            simpa [h_frame] using h_target_final
          rw [h_stored_target] at h_target_final'
          exact Option.some.inj h_target_final'
        refine ⟨target, h_target_final, h_lookup_final, Or.inr ?_⟩
        simpa [h_stored_eq, h_fmla] using h_source_exact
  refine ⟨Γ, steps, p, q, h_final_db, h_em, h_unique, h_trace,
    h_pointwise, ?_⟩
  intro n f fr lbl h_find_final
  obtain ⟨idx, ⟨h_idx, h_creates⟩, _h_unique⟩ :=
    h_origin n f fr lbl h_find_final
  obtain ⟨target, h_target, h_lookup, h_result⟩ :=
    h_created idx h_idx n f fr lbl h_find_final h_creates
  refine ⟨idx, target, h_idx, h_creates, h_target, h_lookup, ?_⟩
  rcases h_payload idx n f fr lbl h_idx h_creates with h_axiom | h_theorem
  · obtain ⟨arr, p2, h_event, h_label, h_fmla, h_lbl, _h_head,
      _h_fresh, _h_insert, _h_trim⟩ := h_axiom
    apply Or.inl
    refine ⟨arr, p2, h_event, h_label, h_fmla, h_lbl, ?_⟩
    change AxiomEventOfTrace steps Γ
      (Semantic.statementOfFrame target (Kernel.toExpr f))
    exact ⟨idx, n, f, fr, lbl, target, arr, p2, h_idx, h_creates,
      h_event, h_label, h_fmla, h_lbl, h_lookup, rfl⟩
  · obtain ⟨pr, _prefixΓ, _source, h_event, h_label, h_fmla, h_frame,
      h_lbl, _h_fresh, _h_insert, _h_prefix_db, _h_source,
      _h_prefix_provable⟩ := h_theorem
    apply Or.inr
    refine ⟨pr, h_event, h_label, h_fmla, h_frame, h_lbl, ?_⟩
    rcases h_result with h_ax | h_th
    · exact Semantic.sourceAxiom_self_provable h_ax
    · exact h_th

/-- Execution-indexed chronology for the actual `--mode=sound` invocation. -/
theorem checkSinglePass_soundDefault_execution_chronology
    (fname : String) (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname ModeConfig.soundDefault w = .ok db w')
    (h_success : db.error? = none) :
    ExecutionChronology fname ModeConfig.soundDefault w w' db :=
  checkSinglePass_execution_chronology_exactly_one fname
    ModeConfig.soundDefault ModeConfig.soundDefault_prefixCertified w w' db
    h_run h_success

/-- Execution-indexed chronology for the actual `--mode=knife` invocation. -/
theorem checkSinglePass_knife_execution_chronology
    (fname : String) (w w' : Void IO.RealWorld) (db : DB)
    (h_run : checkSinglePass fname ModeConfig.knife w = .ok db w')
    (h_success : db.error? = none) :
    ExecutionChronology fname ModeConfig.knife w w' db :=
  checkSinglePass_execution_chronology_exactly_one fname ModeConfig.knife
    ModeConfig.knife_prefixCertified w w' db h_run h_success

end Metamath.RunEmission
