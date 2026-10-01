import Metamath.SourceCompleteness.Bytes
import Metamath.SourceCompleteness.Render
import Metamath.CheckerCompleteness

/-!
# Feeding concatenated source text

`ParserState.feed base arr i rs` reads `arr` from index `i` one byte at a time. It collects the
pending token `rs`, hands it to `feedToken` at the next whitespace byte, and records a token still
pending at the end of `arr` in the character scanner `charp`. On a token error it stops at once and
records the error offset `i + 1`, an offset local to `arr`. Two runs that read the same bytes at
different offsets therefore agree up to that offset and up to the representation of a token still
pending at the end; the statements below are about runs that end without error and between tokens.
Tokens with the same bytes give the same step (`feedToken_congr`), so such runs agree.

* `feedToken_charp`: `feedToken` leaves the character scanner alone.
* `feed_sim`: runs over the same bytes, placed at different offsets of two arrays, hand the same
  tokens to `feedToken` at the same source positions.
* `feed_append_prefix`, `feed_append_shift`: feeding `A ++ B` splits at `A.size`.
* `afterSource_append`: reading more source text continues from `afterSource config arr`.
* `feedAll_renderText`: feeding the text rendered from a token list is `runTokens`.
* `afterSource_append_renderText`: the two combined.
* `renderText_append`, `size_renderText`, `runTokens_append`: splitting token lists.
-/

set_option autoImplicit false

namespace Metamath.SourceCompleteness

open Metamath.Verify
open Metamath.CheckerCompleteness

/-! ### `feedToken` leaves the character scanner alone -/

theorem withAt_charp (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).charp = (f ()).charp := by
  unfold ParserState.withAt
  dsimp only
  split <;> rfl

theorem label_charp (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    (s.label pos tk).charp = s.charp := by
  unfold ParserState.label
  repeat' split
  all_goals rfl

theorem withMath_charp (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) (hf : ∀ tk', (f s tk').charp = s.charp) :
    (s.withMath pos tk f).charp = s.charp := by
  unfold ParserState.withMath
  repeat' split
  · rfl
  · exact hf _

theorem sym_charp (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) :
    (s.sym pos tk f).charp = s.charp := by
  unfold ParserState.sym
  split
  · rfl
  · exact withMath_charp _ _ _ _ fun _ => rfl

theorem djvars_loop_aux_charp (arr : Array String) (pos : Pos) (tk : String) :
    ∀ (n i : Nat) (s : ParserState), arr.size - i = n →
      (ParserState.djvars_loop_aux arr s pos tk i).charp = s.charp := by
  intro n
  induction n with
  | zero =>
    intro i s h
    rw [ParserState.djvars_loop_aux]
    rw [dif_neg (by omega)]
  | succ n ih =>
    intro i s h
    rw [ParserState.djvars_loop_aux]
    rw [dif_pos (by omega)]
    dsimp only
    split
    · rfl
    · exact ih (i + 1) _ (by omega)

theorem djvars_loop_charp (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) :
    (ParserState.djvars_loop arr s pos tk).charp = s.charp := by
  unfold ParserState.djvars_loop
  split
  · rfl
  · exact djvars_loop_aux_charp arr pos tk _ 0 s rfl

theorem feedTokens_charp (s : ParserState) (arr : Array Verify.Sym) (p : TokensParser) :
    (s.feedTokens arr p).charp = s.charp := by
  obtain ⟨k, pos, l⟩ := p
  unfold ParserState.feedTokens
  rw [withAt_charp]
  simp only [Id.run]
  repeat' split
  all_goals rfl

theorem feedProof_charp (s : ParserState) (tk : ByteSlice) (pr : ProofState) :
    (s.feedProof tk pr).charp = s.charp := by
  unfold ParserState.feedProof
  rw [withAt_charp]
  split <;> rfl

theorem finishProof_charp (s : ParserState) (pr : ProofState) :
    (s.finishProof pr).charp = s.charp := by
  obtain ⟨pos, l, fmla, fr, _, stack, ptp, incomplete⟩ := pr
  unfold ParserState.finishProof
  rw [withAt_charp]
  simp only [Id.run]
  repeat' split
  all_goals rfl

/-- `feedToken` leaves the character scanner alone. -/
theorem feedToken_charp (s : ParserState) (pos : Nat) (tk : ByteSlice) :
    (s.feedToken pos tk).charp = s.charp := by
  unfold ParserState.feedToken
  cases h : s.tokp <;> simp only <;> repeat' split
  all_goals first
    | rfl
    | exact label_charp _ _ _
    | exact sym_charp _ _ _ _
    | exact feedTokens_charp _ _ _
    | exact feedProof_charp _ _ _
    | exact finishProof_charp _ _
    | exact withMath_charp _ _ _ _ fun _ => djvars_loop_charp _ _ _ _
    | exact withMath_charp _ _ _ _ fun _ => by
        simp only [Id.run]
        repeat' split
        all_goals rfl

/-! ### Bytes of slices -/

/-- A slice of `X` and the slice of `P ++ X ++ S` at the same place in `X` have the same bytes. -/
theorem bytes_shift (P X S : ByteArray) (o k : Nat) (hk : k ≤ X.size) :
    (ByteSlice.mk (P ++ X ++ S) (o + P.size) (k + P.size - (o + P.size))).bytes =
      (ByteSlice.mk X o (k - o)).bytes := by
  simp only [ByteSlice.bytes_mk, ByteArray.toList_eq_data_toList]
  have hk' : k ≤ X.data.toList.length := by simpa using hk
  have e1 : k + P.size - (o + P.size) = k - o := by omega
  rw [e1]
  simp only [ByteArray.data_append, Array.toList_append, List.append_assoc]
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append]
  have e2 : o + P.size - P.data.toList.length = o := by simp
  rw [e2, List.drop_append, List.take_append]
  have e3 : k - o - (List.drop o X.data.toList).length = 0 := by simp; omega
  rw [e3, List.take_zero, List.append_nil]

theorem copySlice_append (X S a : ByteArray) (k : Nat) (hk : k ≤ X.size) :
    (X ++ S).copySlice 0 a a.size k false = X.copySlice 0 a a.size k false := by
  unfold ByteArray.copySlice
  have hk' : k ≤ X.data.size := hk
  simp only [ByteArray.data_append, Array.size_append, Nat.sub_zero, Nat.zero_add]
  rw [Array.extract_append]
  have e1 : k - X.data.size = 0 := by omega
  rw [e1]
  simp only [Nat.zero_sub, Array.extract_zero, Array.append_empty]
  congr 3
  omega

theorem getElem_shift (P X S : ByteArray) (k : Nat) (hk : k < X.size) :
    (P ++ X ++ S)[k + P.size]'(by simp; omega) = X[k] := by
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_right (by omega)]
  simp

/-! ### One step of `feed` -/

/-- The character-scanner state that `feed` records on reaching the end of `arr` with the pending
state `rs`. -/
def endCharp (base : Nat) (arr : ByteArray) : ParserState.FeedState → CharParser
  | .ws => .ws
  | .token (.this off) => .token base (ByteSliceT.mk arr off)
  | .token (.old base' off arr') => .token base' (ByteSliceT.mk (arr' ++ arr) off)

theorem endCharp_eq_ws (base : Nat) (arr : ByteArray) (rs : ParserState.FeedState) :
    endCharp base arr rs = .ws ↔ rs = .ws := by
  rcases rs with _ | (_ | _) <;> simp [endCharp]

/-- The state after `feed` hands the pending token `ot`, which ends before index `i` of `arr`, to
`feedToken`. -/
def flushTok (base : Nat) (arr : ByteArray) (i : Nat) (s : ParserState) :
    ParserState.OldToken → ParserState
  | .this off => s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
  | .old base' off arr' => s.feedToken (base' + off)
      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))

theorem updateLine_charp (s : ParserState) (i : Nat) (c : UInt8) :
    (s.updateLine i c).charp = s.charp := by
  unfold ParserState.updateLine
  split <;> rfl

theorem flushTok_charp (base : Nat) (arr : ByteArray) (i : Nat) (s : ParserState)
    (ot : ParserState.OldToken) : (flushTok base arr i s ot).charp = s.charp := by
  cases ot <;> exact feedToken_charp _ _ _

section Steps

variable (base : Nat) (arr : ByteArray) (i : Nat) (s : ParserState)

theorem feed_end (rs : ParserState.FeedState) (h : arr.size ≤ i) :
    s.feed base arr i rs = { s with charp := endCharp base arr rs } := by
  rw [ParserState.feed.eq_def, dif_neg (by omega)]
  rcases rs with _ | (_ | _) <;> rfl

theorem feed_ws_ws (h : i < arr.size) (hw : s.db.config.isWhitespace arr[i] = true) :
    s.feed base arr i .ws = (s.updateLine (base + i) arr[i]).feed base arr (i + 1) .ws := by
  conv => lhs; rw [ParserState.feed.eq_def]
  rw [dif_pos h]
  simp only [hw, if_true]

theorem feed_nonws_ws (h : i < arr.size) (hw : s.db.config.isWhitespace arr[i] = false) :
    s.feed base arr i .ws = s.feed base arr (i + 1) (.token (.this i)) := by
  conv => lhs; rw [ParserState.feed.eq_def]
  rw [dif_pos h]
  simp only [hw, Bool.false_eq_true, if_false]

theorem feed_nonws_token (ot : ParserState.OldToken) (h : i < arr.size)
    (hw : s.db.config.isWhitespace arr[i] = false) :
    s.feed base arr i (.token ot) = s.feed base arr (i + 1) (.token ot) := by
  conv => lhs; rw [ParserState.feed.eq_def]
  rw [dif_pos h]
  simp only [hw, Bool.false_eq_true, if_false]

theorem feed_ws_token_ok (ot : ParserState.OldToken) (h : i < arr.size)
    (hw : s.db.config.isWhitespace arr[i] = true)
    (he : ((flushTok base arr i s ot).updateLine (base + i) arr[i]).db.error? = none) :
    s.feed base arr i (.token ot) =
      ((flushTok base arr i s ot).updateLine (base + i) arr[i]).feed base arr (i + 1) .ws := by
  conv => lhs; rw [ParserState.feed.eq_def]
  rw [dif_pos h]
  cases ot <;> simp only [flushTok] at he ⊢ <;> simp only [hw, he, if_true]

theorem feed_ws_token_err (ot : ParserState.OldToken) (h : i < arr.size)
    (hw : s.db.config.isWhitespace arr[i] = true)
    (he : ((flushTok base arr i s ot).updateLine (base + i) arr[i]).db.error?.isSome) :
    (s.feed base arr i (.token ot)).db.error?.isSome := by
  rw [ParserState.feed.eq_def, dif_pos h]
  cases ot <;> simp only [flushTok] at he ⊢ <;> simp only [hw, if_true] <;> split
  all_goals first
    | rfl
    | rename_i hne
      obtain ⟨⟨e, idx⟩, hx⟩ := Option.isSome_iff_exists.mp he
      exact absurd hx (hne e idx)

end Steps

/-! ### Two runs over the same bytes -/

/-- Pending states of two runs that read the same bytes, the second `d` positions later in its
array: no pending token; a token of the current array, starting `d` positions later in the second;
or, when `d = 0`, the same token carried over from an earlier array. -/
inductive FeedRel (d : Nat) : ParserState.FeedState → ParserState.FeedState → Prop
  | ws : FeedRel d .ws .ws
  | this (off : Nat) : FeedRel d (.token (.this off)) (.token (.this (off + d)))
  | old (base off : Nat) (arr : ByteArray) (h : d = 0) :
      FeedRel d (.token (.old base off arr)) (.token (.old base off arr))

theorem FeedRel.eq_ws {d : Nat} {rs rs' : ParserState.FeedState} (h : FeedRel d rs rs')
    (hws : rs = .ws) : rs' = .ws := by
  cases h with
  | ws => rfl
  | this => cases hws
  | old => cases hws

theorem flushTok_sim (P X S : ByteArray) (bY k : Nat) (hk : k < X.size)
    (s : ParserState) (otX otY : ParserState.OldToken)
    (hrel : FeedRel P.size (.token otX) (.token otY)) :
    flushTok (bY + P.size) X k s otX = flushTok bY (P ++ X ++ S) (k + P.size) s otY := by
  cases hrel with
  | this off =>
    simp only [flushTok]
    rw [show bY + P.size + off = bY + (off + P.size) by omega]
    exact feedToken_congr (bytes_shift P X S off k (Nat.le_of_lt hk)).symm _ _
  | old b off a h0 =>
    obtain rfl := ByteArray.size_eq_zero_iff.mp h0
    simp only [flushTok, ByteArray.empty_append, ByteArray.size_empty, Nat.add_zero]
    rw [copySlice_append X S a k (Nat.le_of_lt hk)]

/-- **Simulation.** Read `X` from index `i` at base `bY + P.size`, and `P ++ X ++ S` from index
`i + P.size` at base `bY`, with related pending states. Either both runs stop at the same token
error, or they reach the end of `X` in the same state `t` with related pending states: the first
run then ends there, the second continues from index `X.size + P.size`. -/
theorem feed_sim (P X S : ByteArray) (bY : Nat) :
    ∀ (n i : Nat), X.size - i = n → i ≤ X.size →
    ∀ (rsX rsY : ParserState.FeedState) (s : ParserState), FeedRel P.size rsX rsY →
      ((s.feed (bY + P.size) X i rsX).db.error?.isSome ∧
          (s.feed bY (P ++ X ++ S) (i + P.size) rsY).db.error?.isSome) ∨
        ∃ (t : ParserState) (rsE rsE' : ParserState.FeedState), t.charp = s.charp ∧
          FeedRel P.size rsE rsE' ∧
          s.feed (bY + P.size) X i rsX = { t with charp := endCharp (bY + P.size) X rsE } ∧
          s.feed bY (P ++ X ++ S) (i + P.size) rsY =
            t.feed bY (P ++ X ++ S) (X.size + P.size) rsE' := by
  intro n
  induction n with
  | zero =>
    intro i hn hi rsX rsY s hrel
    have hiX : i = X.size := by omega
    subst hiX
    exact Or.inr ⟨s, rsX, rsY, rfl, hrel, feed_end _ _ _ _ _ (Nat.le_refl _), rfl⟩
  | succ n ih =>
    intro i hn hi rsX rsY s hrel
    have hiX : i < X.size := by omega
    have hiY : i + P.size < (P ++ X ++ S).size := by simp; omega
    have hc' : (P ++ X ++ S)[i + P.size] = X[i] := getElem_shift P X S i hiX
    have hpos : bY + (i + P.size) = bY + P.size + i := by omega
    have hidx : i + P.size + 1 = i + 1 + P.size := by omega
    have ih' := ih (i + 1) (by omega) hiX
    cases hw : s.db.config.isWhitespace X[i]
    · have hwY : s.db.config.isWhitespace (P ++ X ++ S)[i + P.size] = false := by
        rw [hc']; exact hw
      cases hrel with
      | ws =>
        rw [feed_nonws_ws _ _ _ _ hiX hw, feed_nonws_ws _ _ _ _ hiY hwY, hidx]
        exact ih' _ _ s (.this i)
      | this off =>
        rw [feed_nonws_token _ _ _ _ _ hiX hw, feed_nonws_token _ _ _ _ _ hiY hwY, hidx]
        exact ih' _ _ s (.this off)
      | old b off a h0 =>
        rw [feed_nonws_token _ _ _ _ _ hiX hw, feed_nonws_token _ _ _ _ _ hiY hwY, hidx]
        exact ih' _ _ s (.old b off a h0)
    · have hwY : s.db.config.isWhitespace (P ++ X ++ S)[i + P.size] = true := by
        rw [hc']; exact hw
      have tok : ∀ otX otY, FeedRel P.size (.token otX) (.token otY) →
          ((s.feed (bY + P.size) X i (.token otX)).db.error?.isSome ∧
              (s.feed bY (P ++ X ++ S) (i + P.size) (.token otY)).db.error?.isSome) ∨
            ∃ (t : ParserState) (rsE rsE' : ParserState.FeedState), t.charp = s.charp ∧
              FeedRel P.size rsE rsE' ∧
              s.feed (bY + P.size) X i (.token otX) =
                { t with charp := endCharp (bY + P.size) X rsE } ∧
              s.feed bY (P ++ X ++ S) (i + P.size) (.token otY) =
                t.feed bY (P ++ X ++ S) (X.size + P.size) rsE' := by
        intro otX otY hrel'
        have hflush := flushTok_sim P X S bY i hiX s otX otY hrel'
        have hY2 : (flushTok bY (P ++ X ++ S) (i + P.size) s otY).updateLine (bY + (i + P.size))
            (P ++ X ++ S)[i + P.size] =
            (flushTok (bY + P.size) X i s otX).updateLine (bY + P.size + i) X[i] := by
          rw [← hflush, hpos, hc']
        cases he :
            ((flushTok (bY + P.size) X i s otX).updateLine (bY + P.size + i) X[i]).db.error? with
        | some v =>
          refine Or.inl ⟨feed_ws_token_err _ _ _ _ _ hiX hw (by rw [he]; rfl),
            feed_ws_token_err _ _ _ _ _ hiY hwY (by rw [hY2, he]; rfl)⟩
        | none =>
          rw [feed_ws_token_ok _ _ _ _ _ hiX hw he,
            feed_ws_token_ok _ _ _ _ _ hiY hwY (by rw [hY2, he]), hY2, hidx]
          rcases ih' _ _ _ .ws with h | ⟨t, rsE, rsE', ht, hE, h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨t, rsE, rsE', by rw [ht, updateLine_charp, flushTok_charp], hE, h1, h2⟩
      cases hrel with
      | ws =>
        rw [feed_ws_ws _ _ _ _ hiX hw, feed_ws_ws _ _ _ _ hiY hwY, hidx, hc', hpos]
        rcases ih' _ _ (s.updateLine (bY + P.size + i) X[i]) .ws with
          h | ⟨t, rsE, rsE', ht, hE, h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨t, rsE, rsE', by rw [ht, updateLine_charp], hE, h1, h2⟩
      | this off => exact tok _ _ (.this off)
      | old b off a h0 => exact tok _ _ (.old b off a h0)

theorem with_charp_eq_self (t : ParserState) (c : CharParser) (h : t.charp = c) :
    { t with charp := c } = t := by
  cases t
  cases h
  rfl

/-! ### 1. Prefix -/

/-- **Prefix.** If feeding `A` from index `i` ends without error and between tokens in the state
`r`, then feeding `A ++ B` from `i` passes index `A.size` in `r`, with the character scanner of the
start state. -/
theorem feed_append_prefix (A B : ByteArray) (base i : Nat)
    (rs : ParserState.FeedState) (s : ParserState) (hi : i ≤ A.size)
    (h_err : (s.feed base A i rs).db.error? = none)
    (h_ws : (s.feed base A i rs).charp = .ws) :
    s.feed base (A ++ B) i rs =
      { s.feed base A i rs with charp := s.charp }.feed base (A ++ B) A.size .ws := by
  have hrel : FeedRel ByteArray.empty.size rs rs := by
    rcases rs with _ | (off | ⟨b, off, a⟩)
    · exact .ws
    · exact .this off
    · exact .old b off a ByteArray.size_empty
  rcases feed_sim ByteArray.empty A B base _ i rfl hi rs rs s hrel with
    ⟨h1, _⟩ | ⟨t, rsE, rsE', ht, hE, h1, h2⟩
  · simp only [ByteArray.size_empty, Nat.add_zero] at h1
    rw [h_err] at h1
    exact absurd h1 (by simp)
  · simp only [ByteArray.size_empty, Nat.add_zero, ByteArray.empty_append] at h1 h2
    rw [h1] at h_ws ⊢
    have hE0 : rsE = .ws := (endCharp_eq_ws _ _ _).mp h_ws
    rw [h2, hE.eq_ws hE0]
    show _ = ({ t with charp := s.charp } : ParserState).feed base (A ++ B) A.size .ws
    rw [with_charp_eq_self t s.charp ht]

/-! ### 2. Shift -/

/-- **Shift.** Feeding `A ++ B` from index `A.size + j` is feeding `B` from `j` at base
`base + A.size`, with the offsets of a pending token of the current array moved by `A.size`: one
run is error-free iff the other is, and error-free runs that end between tokens are equal. -/
theorem feed_append_shift (A B : ByteArray) (base j : Nat)
    (rs rs' : ParserState.FeedState) (hrs : FeedRel A.size rs rs') (s : ParserState) :
    ((s.feed base (A ++ B) (A.size + j) rs').db.error? = none ↔
        (s.feed (base + A.size) B j rs).db.error? = none) ∧
      ((s.feed (base + A.size) B j rs).db.error? = none →
        (s.feed (base + A.size) B j rs).charp = .ws →
        s.feed base (A ++ B) (A.size + j) rs' = s.feed (base + A.size) B j rs) := by
  by_cases hj : j ≤ B.size
  · rcases feed_sim A B ByteArray.empty base _ j rfl hj rs rs' s hrs with
      ⟨h1, h2⟩ | ⟨t, rsE, rsE', ht, hE, h1, h2⟩
    · simp only [ByteArray.append_empty] at h2
      rw [Nat.add_comm j] at h2
      have n1 : (s.feed (base + A.size) B j rs).db.error? ≠ none := by
        intro h; rw [h] at h1; exact absurd h1 (by simp)
      have n2 : (s.feed base (A ++ B) (A.size + j) rs').db.error? ≠ none := by
        intro h; rw [h] at h2; exact absurd h2 (by simp)
      exact ⟨iff_of_false n2 n1, fun h => absurd h n1⟩
    · simp only [ByteArray.append_empty] at h2
      rw [feed_end base (A ++ B) (B.size + A.size) t rsE' (by simp; omega)] at h2
      rw [Nat.add_comm j] at h2
      rw [h1, h2]
      refine ⟨Iff.rfl, fun _ hws => ?_⟩
      have hE0 := (endCharp_eq_ws _ _ _).mp hws
      rw [hE0, hE.eq_ws hE0]
      rfl
  · rw [feed_end (base + A.size) B j s rs (by omega),
      feed_end base (A ++ B) (A.size + j) s rs' (by simp; omega)]
    refine ⟨Iff.rfl, fun _ hws => ?_⟩
    have h0 := (endCharp_eq_ws _ _ _).mp hws
    rw [h0, hrs.eq_ws h0]
    rfl

/-! ### End of input -/

/-- `arr` is empty or its last byte is whitespace. -/
def EndsInWs (arr : ByteArray) : Prop :=
  ∀ (k : Nat) (hk : k < arr.size), k + 1 = arr.size → isWhitespace arr[k] = true

/-- An error-free run over an array that ends in whitespace ends between tokens. -/
theorem feed_charp_eq_ws (base : Nat) (arr : ByteArray) (harr : EndsInWs arr) :
    ∀ (n i : Nat), arr.size - i = n → ∀ (rs : ParserState.FeedState) (s : ParserState),
      (arr.size ≤ i → rs = .ws) → (s.feed base arr i rs).db.error? = none →
      (s.feed base arr i rs).charp = .ws := by
  intro n
  induction n with
  | zero =>
    intro i hn rs s hrs _
    rw [feed_end base arr i s rs (by omega)]
    show endCharp base arr rs = .ws
    rw [hrs (by omega)]
    rfl
  | succ n ih =>
    intro i hn rs s hrs herr
    have hi : i < arr.size := by omega
    cases hw : s.db.config.isWhitespace arr[i]
    · have hi1 : i + 1 < arr.size := by
        refine Nat.lt_of_le_of_ne hi (fun h => ?_)
        rw [s.db.config.isWhitespace_of_isWhitespace (harr i hi h)] at hw
        exact absurd hw (by decide)
      have hrs' : arr.size ≤ i + 1 → ∀ rs' : ParserState.FeedState, rs' = .ws :=
        fun h => absurd h (by omega)
      rcases rs with _ | ot
      · rw [feed_nonws_ws base arr i s hi hw] at herr ⊢
        exact ih (i + 1) (by omega) _ s (fun h => hrs' h _) herr
      · rw [feed_nonws_token base arr i s ot hi hw] at herr ⊢
        exact ih (i + 1) (by omega) _ s (fun h => hrs' h _) herr
    · rcases rs with _ | ot
      · rw [feed_ws_ws base arr i s hi hw] at herr ⊢
        exact ih (i + 1) (by omega) .ws _ (fun _ => rfl) herr
      · cases he : ((flushTok base arr i s ot).updateLine (base + i) arr[i]).db.error? with
        | some v =>
          have h := feed_ws_token_err base arr i s ot hi hw (by rw [he]; rfl)
          rw [herr] at h
          exact absurd h (by simp)
        | none =>
          rw [feed_ws_token_ok base arr i s ot hi hw he] at herr ⊢
          exact ih (i + 1) (by omega) .ws _ (fun _ => rfl) herr

theorem feedAll_of_ws (s : ParserState) (base : Nat) (arr : ByteArray) (h : s.charp = .ws) :
    s.feedAll base arr = s.feed base arr 0 .ws := by
  unfold ParserState.feedAll
  rw [h]

/-! ### 3. Whole source -/

/-- The parser state after reading the source text `arr` from the start, in mode `config`. -/
def afterSource (config : ModeConfig) (arr : ByteArray) : ParserState :=
  ({ (default : ParserState) with db := { (default : DB) with config := config } } :
    ParserState).feedAll 0 arr

theorem afterSource_eq_feed (config : ModeConfig) (arr : ByteArray) :
    afterSource config arr =
      ({ (default : ParserState) with db := { (default : DB) with config := config } } :
        ParserState).feed 0 arr 0 .ws :=
  feedAll_of_ws _ 0 arr rfl

/-- **Whole source**, with the end condition that feeding `text` ends between tokens. -/
theorem afterSource_append_of_charp (config : ModeConfig)
    (arr text : ByteArray) (h_err : (afterSource config arr).db.error? = none)
    (h_ws : (afterSource config arr).charp = .ws) :
    ((afterSource config (arr ++ text)).db.error? = none ↔
        ((afterSource config arr).feedAll arr.size text).db.error? = none) ∧
      (((afterSource config arr).feedAll arr.size text).db.error? = none →
        ((afterSource config arr).feedAll arr.size text).charp = .ws →
        afterSource config (arr ++ text) = (afterSource config arr).feedAll arr.size text) := by
  have hA := afterSource_eq_feed config arr
  have hpre := feed_append_prefix arr text 0 0 .ws _ (Nat.zero_le _) (hA ▸ h_err) (hA ▸ h_ws)
  rw [← hA] at hpre
  have hs : ({ afterSource config arr with charp := .ws } : ParserState) = afterSource config arr :=
    with_charp_eq_self _ _ h_ws
  have hsh := feed_append_shift arr text 0 0 .ws .ws .ws (afterSource config arr)
  simp only [Nat.add_zero, Nat.zero_add] at hsh
  rw [afterSource_eq_feed config (arr ++ text), hpre, feedAll_of_ws _ _ _ h_ws]
  exact hs ▸ hsh

/-- **Whole source.** After source text `arr` read without error and between tokens, reading
`text` that ends in whitespace from the start of `arr ++ text` is feeding `text` to
`afterSource config arr`. -/
theorem afterSource_append (config : ModeConfig) (arr text : ByteArray)
    (h_err : (afterSource config arr).db.error? = none)
    (h_ws : (afterSource config arr).charp = .ws) (h_text : EndsInWs text) :
    ((afterSource config (arr ++ text)).db.error? = none ↔
        ((afterSource config arr).feedAll arr.size text).db.error? = none) ∧
      ((afterSource config (arr ++ text)).db.error? = none ∨
          ((afterSource config arr).feedAll arr.size text).db.error? = none →
        afterSource config (arr ++ text) = (afterSource config arr).feedAll arr.size text) := by
  obtain ⟨hiff, heq⟩ := afterSource_append_of_charp config arr text h_err h_ws
  refine ⟨hiff, fun h => ?_⟩
  have h' : ((afterSource config arr).feedAll arr.size text).db.error? = none := h.elim hiff.mp id
  refine heq h' ?_
  rw [feedAll_of_ws _ _ _ h_ws] at h' ⊢
  exact feed_charp_eq_ws arr.size text h_text _ 0 rfl .ws _ (fun _ => rfl) h'

/-! ### 4. Lexer -/

theorem renderText_nil : renderText [] = ByteArray.empty := rfl

theorem renderText_cons (t : String) (ts : List String) :
    renderText (t :: ts) = t.toUTF8 ++ " ".toUTF8 ++ renderText ts := by
  simp only [renderText, List.map_cons, String.join_cons, String.toUTF8_eq_toByteArray,
    String.toByteArray_append]

theorem runTokens_charp (s : ParserState) (base : Nat) (toks : List String) :
    (runTokens s base toks).charp = s.charp := by
  induction toks generalizing s base with
  | nil => rfl
  | cons t ts ih =>
    rw [runTokens.eq_2]
    split
    · exact feedToken_charp _ _ _
    · rw [ih, feedToken_charp]

theorem feed_scan (base : Nat) (arr : ByteArray) (ot : ParserState.OldToken) (s : ParserState)
    (j : Nat) (hj : j ≤ arr.size) :
    ∀ (n i : Nat), j - i = n → i ≤ j →
      (∀ (k : Nat) (hk : k < arr.size), i ≤ k → k < j → s.db.config.isWhitespace arr[k] = false) →
      s.feed base arr i (.token ot) = s.feed base arr j (.token ot) := by
  intro n
  induction n with
  | zero =>
    intro i hn hij _
    have : i = j := by omega
    subst this
    rfl
  | succ n ih =>
    intro i hn hij hnw
    have hi : i < arr.size := by omega
    rw [feed_nonws_token base arr i s ot hi (hnw i hi (Nat.le_refl _) (by omega))]
    exact ih (i + 1) (by omega) (by omega) fun k hk h1 h2 => hnw k hk (by omega) h2

theorem feed_renderText (toks : List String)
    (h_toks : ∀ t ∈ toks, t.toUTF8.toList ≠ [] ∧
      ∀ b ∈ t.toUTF8.toList, isPrintable b = true ∧ isWhitespace b = false) :
    ∀ (s : ParserState) (base : Nat), s.charp = .ws →
      ((s.feed base (renderText toks) 0 .ws).db.error? = none ↔
          (runTokens s base toks).db.error? = none) ∧
        ((runTokens s base toks).db.error? = none →
          s.feed base (renderText toks) 0 .ws = runTokens s base toks) := by
  induction toks with
  | nil =>
    intro s base h_ws
    have h : s.feed base (renderText []) 0 .ws = s := by
      rw [feed_end base _ 0 s .ws (Nat.zero_le _)]
      exact with_charp_eq_self s _ h_ws
    rw [h]
    exact ⟨Iff.rfl, fun _ => rfl⟩
  | cons t ts ih =>
    intro s base h_ws
    obtain ⟨hne, hnw⟩ := h_toks t (List.mem_cons_self ..)
    have ih' := ih (fun u hu => h_toks u (List.mem_cons_of_mem _ hu))
    have hT : ∀ (k : Nat) (hk : k < t.toUTF8.size), s.db.config.isWhitespace t.toUTF8[k] = false := by
      intro k hk
      have hmem : t.toUTF8[k] ∈ t.toUTF8.toList := by
        rw [ByteArray.toList_eq_data_toList, ByteArray.getElem_eq_getElem_data]
        exact Array.getElem_mem_toList _
      obtain ⟨hp, hw⟩ := hnw _ hmem
      rw [s.db.config.isWhitespace_of_isPrintable hp]
      exact hw
    have hpos : 0 < t.toUTF8.size := by
      rw [ByteArray.toList_eq_data_toList] at hne
      have := List.length_pos_iff.mpr hne
      simpa using this
    have hsp : " ".toUTF8.size = 1 := rfl
    rw [renderText_cons]
    have hYsize : (t.toUTF8 ++ " ".toUTF8 ++ renderText ts).size =
        t.toUTF8.size + 1 + (renderText ts).size := by
      rw [ByteArray.size_append, ByteArray.size_append, hsp]
    have hYT : ∀ (k : Nat) (hk : k < t.toUTF8.size),
        (t.toUTF8 ++ " ".toUTF8 ++ renderText ts)[k]'(by omega) = t.toUTF8[k] := by
      intro k hk
      rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, hsp]; omega),
        ByteArray.getElem_append_left hk]
    have hYsp : (t.toUTF8 ++ " ".toUTF8 ++ renderText ts)[t.toUTF8.size]'(by omega) = 32 := by
      rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, hsp]; omega),
        ByteArray.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self]
      rfl
    rw [feed_nonws_ws base _ 0 s (by omega) (by rw [hYT 0 hpos]; exact hT 0 hpos),
      feed_scan base _ (.this 0) s t.toUTF8.size (by omega) _ 1 rfl (by omega)
        (fun k hk _ h2 => by rw [hYT k h2]; exact hT k h2)]
    have hwsp : s.db.config.isWhitespace
        (t.toUTF8 ++ " ".toUTF8 ++ renderText ts)[t.toUTF8.size] = true := by
      rw [hYsp]
      exact s.db.config.isWhitespace_of_isWhitespace rfl
    have hflush : (flushTok base (t.toUTF8 ++ " ".toUTF8 ++ renderText ts) t.toUTF8.size s
        (.this 0)).updateLine (base + t.toUTF8.size)
          (t.toUTF8 ++ " ".toUTF8 ++ renderText ts)[t.toUTF8.size] =
        s.feedToken base t.toUTF8.toByteSlice := by
      rw [hYsp]
      show (s.feedToken (base + 0) _).updateLine _ 32 = _
      unfold ParserState.updateLine
      rw [if_neg (by decide), Nat.add_zero]
      apply feedToken_congr
      simp only [ByteSlice.bytes_mk, ByteSlice.bytes_toByteSlice_self,
        ByteArray.toList_eq_data_toList]
      rw [List.drop_zero, Nat.sub_zero, ByteArray.data_append,
        ByteArray.data_append, Array.toList_append, Array.toList_append, List.append_assoc,
        List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
    rw [runTokens.eq_2]
    cases he : (s.feedToken base t.toUTF8.toByteSlice).db.error? with
    | some v =>
      have h1 := feed_ws_token_err base _ t.toUTF8.size s (.this 0) (by omega) hwsp
        (by rw [hflush, he]; rfl)
      have n1 : (s.feed base (t.toUTF8 ++ " ".toUTF8 ++ renderText ts) t.toUTF8.size
          (.token (.this 0))).db.error? ≠ none := by
        intro h; rw [h] at h1; exact absurd h1 (by simp)
      have n2 : (s.feedToken base t.toUTF8.toByteSlice).db.error? ≠ none := by
        rw [he]; simp
      rw [if_pos (by rfl)]
      exact ⟨iff_of_false n1 n2, fun h => absurd h n2⟩
    | none =>
      rw [feed_ws_token_ok base _ t.toUTF8.size s (.this 0) (by omega) hwsp (by rw [hflush, he]),
        hflush, if_neg (by simp)]
      have h1ws : (s.feedToken base t.toUTF8.toByteSlice).charp = .ws := by
        rw [feedToken_charp, h_ws]
      have hsh := feed_append_shift (t.toUTF8 ++ " ".toUTF8) (renderText ts) base 0 .ws .ws .ws
        (s.feedToken base t.toUTF8.toByteSlice)
      rw [ByteArray.size_append, hsp, Nat.add_zero, ← Nat.add_assoc] at hsh
      obtain ⟨hiff, heq⟩ := ih' (s.feedToken base t.toUTF8.toByteSlice)
        (base + t.toUTF8.size + 1) h1ws
      refine ⟨hsh.1.trans hiff, fun h => ?_⟩
      have h0 := heq h
      rw [hsh.2 (hiff.mpr h) (by rw [h0, runTokens_charp, h1ws]), h0]

/-- **Lexer.** Between tokens, feeding the text rendered from nonempty tokens without whitespace
bytes feeds exactly those tokens, at the positions they have in the text. -/
theorem feedAll_renderText (s : ParserState) (base : Nat)
    (toks : List String) (h_ws : s.charp = .ws)
    (h_toks : ∀ t ∈ toks, t.toUTF8.toList ≠ [] ∧
      ∀ b ∈ t.toUTF8.toList, isPrintable b = true ∧ isWhitespace b = false) :
    ((s.feedAll base (renderText toks)).db.error? = none ↔
        (runTokens s base toks).db.error? = none) ∧
      ((s.feedAll base (renderText toks)).db.error? = none ∨
          (runTokens s base toks).db.error? = none →
        s.feedAll base (renderText toks) = runTokens s base toks) := by
  rw [feedAll_of_ws s base _ h_ws]
  obtain ⟨hiff, heq⟩ := feed_renderText toks h_toks s base h_ws
  exact ⟨hiff, fun h => heq (h.elim hiff.mp id)⟩

/-! ### 5. Assembly -/

/-- **Assembly.** After source text `arr` read without error and between tokens, reading the
rendered tokens `toks` from the start of `arr ++ renderText toks` is `runTokens` from
`afterSource config arr` at `arr.size`. -/
theorem afterSource_append_renderText (config : ModeConfig)
    (arr : ByteArray) (toks : List String)
    (h_err : (afterSource config arr).db.error? = none)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_toks : ∀ t ∈ toks, t.toUTF8.toList ≠ [] ∧
      ∀ b ∈ t.toUTF8.toList, isPrintable b = true ∧ isWhitespace b = false) :
    ((afterSource config (arr ++ renderText toks)).db.error? = none ↔
        (runTokens (afterSource config arr) arr.size toks).db.error? = none) ∧
      ((afterSource config (arr ++ renderText toks)).db.error? = none ∨
          (runTokens (afterSource config arr) arr.size toks).db.error? = none →
        afterSource config (arr ++ renderText toks) =
          runTokens (afterSource config arr) arr.size toks) := by
  obtain ⟨hiff1, heq1⟩ := afterSource_append_of_charp config arr (renderText toks) h_err h_ws
  obtain ⟨hiff2, heq2⟩ := feedAll_renderText (afterSource config arr) arr.size toks h_ws h_toks
  refine ⟨hiff1.trans hiff2, fun h => ?_⟩
  have hR : (runTokens (afterSource config arr) arr.size toks).db.error? = none :=
    h.elim (fun h => hiff2.mp (hiff1.mp h)) id
  have hM := heq2 (Or.inr hR)
  rw [heq1 (hiff2.mpr hR) (by rw [hM, runTokens_charp, h_ws]), hM]

/-! ### 6. Token-list splitting -/

theorem renderText_append (xs ys : List String) :
    renderText (xs ++ ys) = renderText xs ++ renderText ys := by
  simp only [renderText, List.map_append, String.join_append, String.toUTF8_eq_toByteArray,
    String.toByteArray_append]

theorem size_renderText (toks : List String) :
    (renderText toks).size = (toks.map (·.toUTF8.size + 1)).sum := by
  induction toks with
  | nil => rfl
  | cons t ts ih =>
    rw [renderText_cons, ByteArray.size_append, ByteArray.size_append, ih, List.map_cons,
      List.sum_cons]
    rfl

/-- `runTokens` over `xs ++ ys` runs `xs`, then `ys` unless `xs` stopped at an error. The start
state must be error-free or `xs` nonempty: `runTokens` does not test the error of its start state,
see `runTokens_append_counterexample`. -/
theorem runTokens_append (s : ParserState) (base : Nat) (xs ys : List String)
    (h : s.db.error? = none ∨ xs ≠ []) :
    runTokens s base (xs ++ ys) =
      let s' := runTokens s base xs
      if s'.db.error?.isSome then s' else runTokens s' (base + (renderText xs).size) ys := by
  induction xs generalizing s base with
  | nil =>
    have h0 : s.db.error? = none := h.resolve_right (fun h => h rfl)
    simp [runTokens, h0, renderText_nil]
  | cons x xs ih =>
    simp only [List.cons_append]
    rw [runTokens.eq_2, runTokens.eq_2]
    split
    · rfl
    · rename_i hx
      have hx' : (s.feedToken base x.toUTF8.toByteSlice).db.error? = none := by
        simpa using hx
      rw [ih _ _ (Or.inl hx'), renderText_cons, ByteArray.size_append, ByteArray.size_append]
      simp only [Nat.add_assoc]
      rfl

/-- Without its side condition `runTokens_append` fails: from a start state that carries an error,
`runTokens` still feeds the token `$c`, while splitting after the empty prefix returns the start
state. -/
theorem runTokens_append_counterexample :
    ∃ (s : ParserState) (base : Nat) (xs ys : List String),
      runTokens s base (xs ++ ys) ≠
        (let s' := runTokens s base xs
         if s'.db.error?.isSome then s' else runTokens s' (base + (renderText xs).size) ys) := by
  refine ⟨{ (default : ParserState) with
      db := { (default : DB) with error? := some ⟨.error ⟨0, 0⟩ "", 0⟩ } },
    0, [], ["$c"], fun h => ?_⟩
  have h' := congrArg (fun s : ParserState => match s.tokp with | .const _ => true | _ => false) h
  revert h'
  decide

end Metamath.SourceCompleteness
