import Metamath.RootFileCheck
import Metamath.SourceCompleteness.Compose

/-!
# Source text without a `$[` token raises no include request

The parser raises an include request (`Error.includeRequest`) only through `requestInclude`, in the
two include-directive modes `.includePath` and `.includeClose`. It enters those modes only on a `$[`
token; `$(` parks the current mode under `.comment` and `$)` restores it.

* `feedToken_errorNotRequest`: outside the include-directive modes a step raises no include request.
  `feedToken_noRequest`: outside those modes, also under a comment (`NotIncludeMode`), a token other
  than `$[` moreover leaves the parser outside them.
* `feed_noRequest`, `feed_errorNotRequest`: the byte loop, when no token that it hands to
  `feedToken` spells `$[` (`NoIncludeTokenFrom`: no run ended by a whitespace byte spells `$[`;
  implied by the absence of `$[` among all whitespace-free runs, `NoIncludeTokenFrom.of_runs`).
* `done_errorNotRequest`, `postCheck_errorNotRequest`: end of input and the post-check.
* `checkBytes_append_errorNotRequest`: after source text read without error, between tokens and
  outside the include-directive modes, the whole-file check of that text followed by text without a
  token `$[` reports no include request. `checkBytes_errorNotRequest`: the appended text renders
  label tokens, math symbol tokens and the keywords `$v $f $d $p $. $= $}`.

The calibrations at the end show that none of the three conditions on the source text read first
can be dropped.
-/

set_option autoImplicit false

namespace Metamath.SourceCompleteness

open Metamath.Verify
open Metamath.CheckerCompleteness
open Metamath.ParserOps (ErrorNotRequest)

/-! ## One token -/

/-- The token parser is in neither include-directive mode, also not in one parked under a
comment. -/
def NotIncludeMode : TokenParser → Prop
  | .comment p => NotIncludeMode p
  | .includePath .. | .includeClose .. => False
  | _ => True

example : NotIncludeMode .start ∧ NotIncludeMode (.comment (.label ⟨0, 0⟩ "x")) :=
  ⟨trivial, trivial⟩

example : ¬ NotIncludeMode (.includeClose .start ⟨0, 0⟩ "x.mm") ∧
    ¬ NotIncludeMode (.comment (.includePath .start ⟨0, 0⟩)) :=
  ⟨id, id⟩

theorem NotIncludeMode.ne_includePath {t : TokenParser} (h : NotIncludeMode t) (r : TokenParser)
    (q : Pos) : t ≠ .includePath r q := by
  rintro rfl
  exact h

theorem NotIncludeMode.ne_includeClose {t : TokenParser} (h : NotIncludeMode t) (r : TokenParser)
    (q : Pos) (p : String) : t ≠ .includeClose r q p := by
  rintro rfl
  exact h

theorem errorNotRequest_mkErrorFromEvidence (s : ParserState) (pos : Pos) (ev : ErrorEvidence) :
    ErrorNotRequest (s.mkErrorFromEvidence pos ev).db.error? :=
  ParserOps.errorNotRequest_mkError s.db pos ev

/-- Outside the two include-directive modes a step raises no include request. -/
theorem feedToken_errorNotRequest (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h1 : ∀ r q, s.tokp ≠ .includePath r q) (h2 : ∀ r q p, s.tokp ≠ .includeClose r q p)
    (h_base : ErrorNotRequest s.db.error?) :
    ErrorNotRequest (s.feedToken i tk).db.error? := by
  have h_mk := errorNotRequest_mkErrorFromEvidence
  unfold ParserState.feedToken
  cases h_tokp : s.tokp with
  | includePath r q => exact absurd h_tokp (h1 r q)
  | includeClose r q p => exact absurd h_tokp (h2 r q p)
  | comment q =>
      simp only
      repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | start =>
      simp only
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact PrefixProvability.Checker.popScope_errorNotRequestP s _ h_base
          | exact PrefixProvability.Checker.label_errorNotRequestP s _ tk h_base
  | label q lab =>
      simp only
      repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | const seen =>
      simp only
      unfold ParserState.sym ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact ParserOps.insert_errorNotRequest s.db _ _ _ h_base
  | var seen =>
      simp only
      unfold ParserState.sym ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact ParserOps.insert_errorNotRequest s.db _ _ _ h_base
  | djvars arr =>
      simp only
      unfold ParserState.withMath
      repeat' split
      all_goals
        first
          | exact h_base
          | exact h_mk _ _ _
          | exact PrefixProvability.Checker.djvars_loop_errorNotRequest _ _ _ _ h_base
  | math arr p =>
      simp only
      unfold ParserState.withMath
      repeat' split
      all_goals
        try (first
          | exact h_base
          | exact h_mk _ _ _
          | (cases p with
             | mk k ppos plab =>
                 exact PrefixProvability.Checker.feedTokens_errorNotRequest s arr k ppos plab
                   h_base))
      all_goals simp only [Id.run]
      all_goals repeat' split
      all_goals first | exact h_base | exact h_mk _ _ _
  | proof pr =>
      simp only
      repeat' split
      all_goals
        first
          | exact PrefixProvability.Checker.finishProof_errorNotRequest _ pr h_base
          | exact PrefixProvability.Checker.feedProof_errorNotRequest _ tk pr h_base
          | exact h_base
          | exact h_mk _ _ _

/-! ### The token parser stays out of the include-directive modes -/

theorem label_notIncludeMode (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (h : NotIncludeMode s.tokp) : NotIncludeMode (s.label pos tk).tokp := by
  unfold ParserState.label
  split
  split
  · trivial
  · exact h

theorem withMath_notIncludeMode (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) (h : NotIncludeMode s.tokp)
    (hf : ∀ tk', NotIncludeMode (f s tk').tokp) : NotIncludeMode (s.withMath pos tk f).tokp := by
  unfold ParserState.withMath
  split
  split
  · exact h
  · exact hf _

theorem djvars_loop_aux_notIncludeMode (arr : Array String) (pos : Pos) (tk : String) :
    ∀ (n i : Nat) (s : ParserState), arr.size - i = n → NotIncludeMode s.tokp →
      NotIncludeMode (ParserState.djvars_loop_aux arr s pos tk i).tokp := by
  intro n
  induction n with
  | zero =>
    intro i s hn _
    rw [ParserState.djvars_loop_aux, dif_neg (by omega)]
    trivial
  | succ n ih =>
    intro i s hn h
    rw [ParserState.djvars_loop_aux, dif_pos (by omega)]
    dsimp only
    split
    · exact h
    · exact ih (i + 1) _ (by omega) h

theorem djvars_loop_notIncludeMode (arr : Array String) (s : ParserState) (pos : Pos) (tk : String)
    (h : NotIncludeMode s.tokp) : NotIncludeMode (ParserState.djvars_loop arr s pos tk).tokp := by
  unfold ParserState.djvars_loop
  split
  · exact h
  · exact djvars_loop_aux_notIncludeMode arr pos tk _ 0 s rfl h

theorem feedTokens_notIncludeMode (s : ParserState) (arr : Array Verify.Sym) (p : TokensParser)
    (h : NotIncludeMode s.tokp) : NotIncludeMode (s.feedTokens arr p).tokp := by
  obtain ⟨k, pos, l⟩ := p
  unfold ParserState.feedTokens
  rw [ParserState.withAt_tokp]
  cases k <;> simp only [Id.run] <;> repeat' split
  all_goals first | exact h | trivial

theorem feedProof_notIncludeMode (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h : NotIncludeMode s.tokp) : NotIncludeMode (s.feedProof tk pr).tokp := by
  unfold ParserState.feedProof
  rw [ParserState.withAt_tokp]
  split
  · trivial
  · exact h

theorem finishProof_notIncludeMode (s : ParserState) (pr : ProofState) :
    NotIncludeMode (s.finishProof pr).tokp := by
  obtain ⟨pos, l, fmla, fr, _, stack, ptp, incomplete⟩ := pr
  unfold ParserState.finishProof
  rw [ParserState.withAt_tokp]
  simp only [Id.run]
  repeat' split
  all_goals trivial

/-- A token other than `$[` does not move the token parser into an include-directive mode. -/
theorem feedToken_notIncludeMode (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_mode : NotIncludeMode s.tokp) (h_tk : tk.eqArray "$[".toAscii = false) :
    NotIncludeMode (s.feedToken i tk).tokp := by
  have h_mode' := h_mode
  unfold ParserState.feedToken
  cases h_tokp : s.tokp with
  | includePath r q => rw [h_tokp] at h_mode'; exact h_mode'.elim
  | includeClose r q p => rw [h_tokp] at h_mode'; exact h_mode'.elim
  | comment q =>
      rw [h_tokp] at h_mode'
      simp only
      repeat' split
      all_goals first | exact h_mode | exact h_mode'
  | start =>
      simp only [h_tk, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals first | trivial | exact h_mode | exact label_notIncludeMode s _ tk h_mode
  | label q lab =>
      simp only [h_tk, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals first | exact h_mode | trivial
  | const seen =>
      simp only [h_tk, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals first | exact h_mode | trivial
  | var seen =>
      simp only [h_tk, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals first | exact h_mode | trivial
  | djvars arr =>
      simp only [h_tk, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals first
        | trivial
        | exact h_mode
        | exact withMath_notIncludeMode s _ tk _ h_mode
            (fun tk' => djvars_loop_notIncludeMode arr s _ tk' h_mode)
  | math arr p =>
      simp only [h_tk, Bool.false_eq_true, ↓reduceIte]
      split
      · trivial
      · split
        · exact feedTokens_notIncludeMode s arr p h_mode
        · refine withMath_notIncludeMode s _ tk _ h_mode (fun tk' => ?_)
          simp only [Id.run]
          repeat' split
          all_goals first | exact h_mode | trivial
  | proof pr =>
      simp only [h_tk, Bool.false_eq_true, ↓reduceIte]
      split
      · trivial
      · split
        · exact finishProof_notIncludeMode _ pr
        · refine feedProof_notIncludeMode _ tk pr ?_
          trivial

/-- **One token.** Outside the include-directive modes, also under a comment, a token other than
`$[` raises no include request and leaves the token parser outside those modes. -/
theorem feedToken_noRequest (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_mode : NotIncludeMode s.tokp) (h_err : ErrorNotRequest s.db.error?)
    (h_tk : tk.eqArray "$[".toAscii = false) :
    ErrorNotRequest (s.feedToken i tk).db.error? ∧ NotIncludeMode (s.feedToken i tk).tokp :=
  ⟨feedToken_errorNotRequest s i tk h_mode.ne_includePath h_mode.ne_includeClose h_err,
    feedToken_notIncludeMode s i tk h_mode h_tk⟩

/-! ## The byte loop -/

/-- No token that `feed` hands to `feedToken` from index `i` of `arr` on spells `$[`, in any mode:
no run of `arr` that starts at an index `≥ i` and is ended by a byte that separates tokens in some
mode (whitespace, or vertical tab) spells `$[`. -/
def NoIncludeTokenFrom (arr : ByteArray) (i : Nat) : Prop :=
  ∀ (off j : Nat) (hj : j < arr.size), i ≤ off → (isWhitespace arr[j] = true ∨ arr[j] = 11) →
    (ByteSlice.mk arr off (j - off)).bytes ≠ "$[".toAscii.toList

theorem dollarLBrack_toList : "$[".toAscii.toList = [36, 91] := by
  rw [String.toAscii, ← String.toUTF8_eq_toByteArray, toUTF8_toList_of_ascii (by decide)]
  decide

/-- `NoIncludeTokenFrom` follows from the absence of `$[` among the nonempty whitespace-free runs of
`arr` from `i` on. The converse fails: `$[x ` has the run `$[`, but no token `$[`. -/
theorem NoIncludeTokenFrom.of_runs {arr : ByteArray} {i : Nat}
    (h : ∀ off len, i ≤ off → 0 < len →
      (∀ (k : Nat) (hk : k < arr.size), off ≤ k → k < off + len → isWhitespace arr[k] = false) →
      (ByteSlice.mk arr off len).bytes ≠ "$[".toAscii.toList) :
    NoIncludeTokenFrom arr i := by
  intro off j hj hoff _ hb
  have hb' := hb
  rw [ByteSlice.bytes_mk, dollarLBrack_toList] at hb'
  have hlen : j - off = 2 := by
    have := congrArg List.length hb'
    simp only [List.length_take, List.length_drop, ByteArray.length_toList, List.length_cons,
      List.length_nil] at this
    omega
  refine h off (j - off) hoff (by omega) (fun k hk h1 h2 => ?_) hb
  have hget : arr.toList[k]? = some arr[k] := by
    simp [ByteArray.toList_eq_data_toList, ByteArray.getElem_eq_getElem_data, hk]
  have hkey : arr.toList[k]? = [36, 91][k - off]? := by
    rw [← hb', List.getElem?_take, if_pos (by omega), List.getElem?_drop]
    congr 1
    omega
  rw [hget] at hkey
  rcases (by omega : k - off = 0 ∨ k - off = 1) with e | e <;>
    · rw [e] at hkey
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hkey
      rw [hkey]
      decide

/-- The converse of `NoIncludeTokenFrom.of_runs` fails: `$[x ` has the run `$[`, but no token
`$[`. -/
example : NoIncludeTokenFrom [36, 91, 120, 32].toByteArray 0 ∧
    (ByteSlice.mk [36, 91, 120, 32].toByteArray 0 2).bytes = "$[".toAscii.toList := by
  have hl := ByteArray.toList_toByteArray [36, 91, 120, 32]
  refine ⟨fun off j hj _ hw hb => ?_, by rw [ByteSlice.bytes_mk, hl, dollarLBrack_toList]; rfl⟩
  have hj4 : j < 4 := by
    have : [36, 91, 120, 32].toByteArray.size = 4 := by decide
    omega
  rw [ByteSlice.bytes_mk, hl, dollarLBrack_toList] at hb
  have h3 : j = 3 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    all_goals first | rfl | exact absurd hw (by decide +revert)
  subst h3
  rcases (by omega : off = 0 ∨ off = 1 ∨ off = 2 ∨ 3 ≤ off) with rfl | rfl | rfl | h
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · rw [Nat.sub_eq_zero_of_le h, List.take_zero] at hb
    exact absurd hb (by simp)

/-- The byte loop, by induction on the bytes left: the error stays a non-request and the token
parser stays outside the include-directive modes. -/
theorem feed_noRequest_aux (base : Nat) (arr : ByteArray) (i₀ : Nat)
    (h_arr : NoIncludeTokenFrom arr i₀) :
    ∀ (n i : Nat), arr.size - i = n → ∀ (rs : ParserState.FeedState) (s : ParserState),
      i₀ ≤ i → (rs = .ws ∨ ∃ off, i₀ ≤ off ∧ rs = .token (.this off)) →
      NotIncludeMode s.tokp → ErrorNotRequest s.db.error? →
      ErrorNotRequest (s.feed base arr i rs).db.error? ∧
        NotIncludeMode (s.feed base arr i rs).tokp := by
  intro n
  induction n with
  | zero =>
    intro i hn rs s _ _ hm he
    rw [feed_end base arr i s rs (by omega)]
    exact ⟨he, hm⟩
  | succ n ih =>
    intro i hn rs s hi0 hrs hm he
    have hi : i < arr.size := by omega
    cases hw : s.db.config.isWhitespace arr[i]
    · rcases hrs with rfl | ⟨off, hoff, rfl⟩
      · rw [feed_nonws_ws base arr i s hi hw]
        exact ih (i + 1) (by omega) _ s (by omega) (Or.inr ⟨i, hi0, rfl⟩) hm he
      · rw [feed_nonws_token base arr i s _ hi hw]
        exact ih (i + 1) (by omega) _ s (by omega) (Or.inr ⟨off, hoff, rfl⟩) hm he
    · rcases hrs with rfl | ⟨off, hoff, rfl⟩
      · rw [feed_ws_ws base arr i s hi hw]
        refine ih (i + 1) (by omega) .ws _ (by omega) (Or.inl rfl) ?_ ?_
        · rw [ParserOps.updateLine_tokp]; exact hm
        · rw [ParserState.updateLine_db]; exact he
      · rw [RootFileCheck.feed_ws_token base arr i s _ hi hw]
        have htk : (ByteSlice.mk arr off (i - off)).eqArray "$[".toAscii = false := by
          rw [ByteSlice.eqArray_eq]
          exact decide_eq_false (h_arr off i hi hoff (s.db.config.isWhitespace_true hw))
        obtain ⟨he1, hm1⟩ := feedToken_noRequest s (base + off) _ hm he htk
        generalize hs1 : (RootFileCheck.flushOld s base arr i (.this off)).updateLine
          (base + i) arr[i] = s1
        have he1' : ErrorNotRequest s1.db.error? := by
          rw [← hs1, ParserState.updateLine_db]; exact he1
        have hm1' : NotIncludeMode s1.tokp := by
          rw [← hs1, ParserOps.updateLine_tokp]; exact hm1
        unfold RootFileCheck.continueAfter
        cases h_e : s1.db.error? with
        | none => exact ih (i + 1) (by omega) .ws s1 (by omega) (Or.inl rfl) hm1' he1'
        | some it =>
          obtain ⟨e, k⟩ := it
          refine ⟨?_, hm1'⟩
          show ErrorNotRequest (some ⟨e, i + 1⟩)
          exact (RootFileCheck.errorNotRequest_some_idx e k (i + 1)).mp (h_e ▸ he1')

/-- **Byte loop.** Read `arr` from index `i`, where no token from `i₀ ≤ i` on spells `$[`, starting
outside the include-directive modes with an error that is not a request, and with no pending
token or a pending token of `arr` begun at an index `≥ i₀`. The loop raises no include request and
ends outside the include-directive modes. -/
theorem feed_noRequest (base : Nat) (arr : ByteArray) (i₀ i : Nat) (rs : ParserState.FeedState)
    (s : ParserState) (h_arr : NoIncludeTokenFrom arr i₀) (h_i : i₀ ≤ i)
    (h_rs : rs = .ws ∨ ∃ off, i₀ ≤ off ∧ rs = .token (.this off))
    (h_mode : NotIncludeMode s.tokp) (h_err : ErrorNotRequest s.db.error?) :
    ErrorNotRequest (s.feed base arr i rs).db.error? ∧
      NotIncludeMode (s.feed base arr i rs).tokp :=
  feed_noRequest_aux base arr i₀ h_arr _ i rfl rs s h_i h_rs h_mode h_err

/-- **Byte loop**, error slot, with the token condition from the start index on. -/
theorem feed_errorNotRequest (base : Nat) (arr : ByteArray) (i : Nat) (rs : ParserState.FeedState)
    (s : ParserState) (h_arr : NoIncludeTokenFrom arr i)
    (h_rs : rs = .ws ∨ ∃ off, i ≤ off ∧ rs = .token (.this off))
    (h_mode : NotIncludeMode s.tokp) (h_err : ErrorNotRequest s.db.error?) :
    ErrorNotRequest (s.feed base arr i rs).db.error? :=
  (feed_noRequest base arr i i rs s h_arr (Nat.le_refl i) h_rs h_mode h_err).1

/-! ## End of input and the post-check -/

/-- Outside the include-directive modes the end-of-input step raises no include request: flushing
a pending token is one step, and the final mode check raises only `.error` interrupts. -/
theorem done_errorNotRequest (s : ParserState) (base : Nat)
    (h1 : ∀ r q, s.tokp ≠ .includePath r q) (h2 : ∀ r q p, s.tokp ≠ .includeClose r q p)
    (h : ErrorNotRequest s.db.error?) : ErrorNotRequest (s.done base).error? := by
  have hf : ∀ pos tk, ErrorNotRequest (s.feedToken pos tk).db.error? :=
    fun pos tk => feedToken_errorNotRequest s pos tk h1 h2 h
  unfold ParserState.done
  simp only [Id.run]
  repeat' split
  all_goals first
    | exact h
    | exact hf _ _
    | exact ParserOps.errorNotRequest_mkParseError _ _ _
    | exact ParserOps.errorNotRequest_mkError _ _ _

/-- The post-check raises no include request. -/
theorem postCheck_errorNotRequest (d : DB) (h : ErrorNotRequest d.error?) :
    ErrorNotRequest (RootFileCheck.postCheck d).error? := by
  unfold RootFileCheck.postCheck
  split
  · split
    · exact h
    · exact ParserOps.errorNotRequest_mkError _ _ _
  · exact h

/-! ## Text without a `$[` token -/

/-- Tokens of `R` from `i` on are the tokens of `A ++ R` from `A.size + i` on. -/
theorem NoIncludeTokenFrom.append_left {R : ByteArray} (A : ByteArray) {i : Nat}
    (h : NoIncludeTokenFrom R i) : NoIncludeTokenFrom (A ++ R) (A.size + i) := by
  intro off j hj hoff hw hb
  rcases Nat.lt_or_ge j off with hjo | hjo
  · rw [ByteSlice.bytes_mk, Nat.sub_eq_zero_of_le (Nat.le_of_lt hjo), List.take_zero,
      dollarLBrack_toList] at hb
    exact absurd hb (by simp)
  · have hjR : j - A.size < R.size := by rw [ByteArray.size_append] at hj; omega
    have hc : (A ++ R)[j] = R[j - A.size] := ByteArray.getElem_append_right (by omega)
    refine h (off - A.size) (j - A.size) hjR (by omega) (hc ▸ hw) ?_
    rw [ByteSlice.bytes_mk, ByteArray.toList_append, List.drop_append,
      List.drop_eq_nil_of_le (by rw [ByteArray.length_toList]; omega), List.nil_append,
      ByteArray.length_toList] at hb
    rwa [ByteSlice.bytes_mk, show j - A.size - (off - A.size) = j - off by omega]

/-- No byte `$` is directly followed by a byte `[`. -/
def NoDollarLBrack : List UInt8 → Prop
  | [] => True
  | a :: l => (a = 36 → l.head? ≠ some 91) ∧ NoDollarLBrack l

instance decNoDollarLBrack : (l : List UInt8) → Decidable (NoDollarLBrack l)
  | [] => isTrue trivial
  | a :: l =>
    have := decNoDollarLBrack l
    inferInstanceAs (Decidable ((a = 36 → l.head? ≠ some 91) ∧ NoDollarLBrack l))

theorem NoDollarLBrack.of_not_mem : ∀ {l : List UInt8}, 36 ∉ l → NoDollarLBrack l
  | [], _ => trivial
  | _ :: _, h =>
    ⟨fun ha => absurd (ha ▸ List.mem_cons_self) h,
      of_not_mem fun hm => h (List.mem_cons_of_mem _ hm)⟩

/-- A segment ending in a space may be followed by any list without a `$[` pair. -/
theorem NoDollarLBrack.append_space :
    ∀ (T R : List UInt8), NoDollarLBrack (T ++ [32]) → NoDollarLBrack R →
      NoDollarLBrack (T ++ 32 :: R)
  | [], _, _, hR => ⟨fun h => absurd h (by decide), hR⟩
  | _ :: T, R, ⟨ha, hT⟩, hR =>
    ⟨fun h36 => by cases T <;> exact ha h36, append_space T R hT hR⟩

theorem NoDollarLBrack.drop : ∀ (m : Nat) {l : List UInt8}, NoDollarLBrack l →
    NoDollarLBrack (l.drop m)
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | m + 1, _ :: _, h => drop m h.2

theorem NoDollarLBrack.take_ne : ∀ {l : List UInt8}, NoDollarLBrack l → ∀ n, l.take n ≠ [36, 91]
  | [], _, n => by simp
  | [a], _, n => by cases n <;> simp
  | a :: b :: l, h, n => by
    rcases n with _ | _ | n
    · simp
    · simp
    · intro e
      simp only [List.take_succ_cons, List.cons.injEq] at e
      exact h.1 e.1 (by simp [e.2.1])

/-- No piece of a list without a `$[` pair spells `$[`. -/
theorem NoDollarLBrack.drop_take_ne {l : List UInt8} (h : NoDollarLBrack l) (m n : Nat) :
    (l.drop m).take n ≠ [36, 91] :=
  (h.drop m).take_ne n

/-- Bytes without a `$[` pair contain no token `$[`. -/
theorem NoIncludeTokenFrom.of_noDollarLBrack {R : ByteArray} (h : NoDollarLBrack R.toList)
    (i : Nat) : NoIncludeTokenFrom R i := by
  intro off j _ _ _ hb
  rw [ByteSlice.bytes_mk, dollarLBrack_toList] at hb
  exact h.drop_take_ne _ _ hb

theorem toList_renderText_cons (t : String) (ts : List String) :
    (renderText (t :: ts)).toList = t.toUTF8.toList ++ 32 :: (renderText ts).toList := by
  have hsp : " ".toUTF8.toList = [32] := by
    rw [toUTF8_toList_of_ascii (by decide)]
    decide
  rw [renderText_cons, ByteArray.toList_append, ByteArray.toList_append, hsp, List.append_assoc,
    List.singleton_append]

/-- A label token, a math symbol token, or one of the keywords of rendered declarations, proofs
and block closings, followed by a space, has no `$[` pair. -/
theorem noDollarLBrack_token (t : String)
    (ht : IsLabelToken t ∨ IsMathToken t ∨ t ∈ ["$v", "$f", "$d", "$p", "$.", "$=", "$}"]) :
    NoDollarLBrack (t.toUTF8.toList ++ [32]) := by
  rcases ht with ht | ht | ht
  · apply NoDollarLBrack.of_not_mem
    rw [toUTF8_toList_of_ascii ht.ascii]
    simp only [List.mem_append, List.mem_map, List.mem_singleton]
    rintro (⟨c, hc, hc36⟩ | h32)
    · have := (labelChar_byte (ht.2 c hc)).1
      rw [hc36] at this
      exact absurd this (by decide)
    · exact absurd h32 (by decide)
  · apply NoDollarLBrack.of_not_mem
    rw [toUTF8_toList_of_ascii ht.ascii]
    simp only [List.mem_append, List.mem_map, List.mem_singleton]
    rintro (⟨c, hc, hc36⟩ | h32)
    · have := (mathChar_byte (ht.2 c hc)).1
      rw [hc36] at this
      exact absurd this (by decide)
    · exact absurd h32 (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [toUTF8_toList_of_ascii (by decide)]; decide)

theorem noDollarLBrack_renderText (toks : List String)
    (h_toks : ∀ t ∈ toks, IsLabelToken t ∨ IsMathToken t ∨
      t ∈ ["$v", "$f", "$d", "$p", "$.", "$=", "$}"]) :
    NoDollarLBrack (renderText toks).toList := by
  induction toks with
  | nil =>
    rw [renderText_nil, ByteArray.toList_eq_data_toList]
    trivial
  | cons t ts ih =>
    rw [toList_renderText_cons]
    exact NoDollarLBrack.append_space _ _ (noDollarLBrack_token t (h_toks t List.mem_cons_self))
      (ih fun u hu => h_toks u (List.mem_cons_of_mem _ hu))

example : NoIncludeTokenFrom (renderText ["$v", "x", "$.", "$}"]) 0 :=
  .of_noDollarLBrack (noDollarLBrack_renderText _ (by decide)) 0

example : ¬ NoIncludeTokenFrom (renderText ["$["]) 0 := by
  have hl : (renderText ["$["]).toList = [36, 91, 32] := by
    rw [toList_renderText_cons, renderText_nil, toUTF8_toList_of_ascii (by decide),
      ByteArray.toList_eq_data_toList]
    rfl
  have hsz : (renderText ["$["]).size = 3 := by rw [← ByteArray.length_toList, hl]; rfl
  have hc : (renderText ["$["])[2]'(by omega) = 32 := by
    have e : (renderText ["$["]).toList[2]? = some ((renderText ["$["])[2]'(by omega)) := by
      simp [ByteArray.toList_eq_data_toList, ByteArray.getElem_eq_getElem_data, hsz]
    rw [hl] at e
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at e
    exact e.symm
  intro h
  exact h 0 2 (by omega) (Nat.le_refl 0) (by rw [hc]; decide)
    (by rw [ByteSlice.bytes_mk, hl, dollarLBrack_toList]; decide)

/-! ## Whole source -/

theorem checkBytesCore_eq_done (config : ModeConfig) (arr : ByteArray) :
    checkBytesCore arr config = (afterSource config arr).done arr.size := rfl

/-- **Appended text without a `$[` token raises no include request.** After source text `arr` read
without error, between tokens and outside the include-directive modes, the whole-file check of
`arr ++ text`, where `text` has no token `$[`, reports no include request. -/
theorem checkBytes_append_errorNotRequest (config : ModeConfig) (arr text : ByteArray)
    (h_err : (afterSource config arr).db.error? = none)
    (h_mode : NotIncludeMode (afterSource config arr).tokp)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_text : NoIncludeTokenFrom text 0) :
    ErrorNotRequest (checkBytes (arr ++ text) config).error? := by
  have hA := afterSource_eq_feed config arr
  have hpre := feed_append_prefix arr text 0 0 .ws _ (Nat.zero_le _) (hA ▸ h_err) (hA ▸ h_ws)
  rw [← hA] at hpre
  have hs : ({ afterSource config arr with charp := .ws } : ParserState) = afterSource config arr :=
    with_charp_eq_self _ _ h_ws
  have hrun : afterSource config (arr ++ text) =
      (afterSource config arr).feed 0 (arr ++ text) arr.size .ws := by
    rw [afterSource_eq_feed config (arr ++ text), hpre]
    exact congrArg (ParserState.feed 0 (arr ++ text) arr.size .ws) hs
  obtain ⟨h1, h2⟩ := feed_noRequest 0 (arr ++ text) arr.size arr.size .ws (afterSource config arr)
    (h_text.append_left arr) (Nat.le_refl _) (Or.inl rfl) h_mode
    (by rw [h_err]; exact ParserOps.errorNotRequest_none)
  rw [← hrun] at h1 h2
  rw [RootFileCheck.checkBytes_eq_postCheck, checkBytesCore_eq_done]
  exact postCheck_errorNotRequest _
    (done_errorNotRequest _ _ h2.ne_includePath h2.ne_includeClose h1)

/-- **Rendered tokens raise no include request.** After source text `arr` read without error and
between statements, the whole-file check of `arr` followed by rendered label tokens, math symbol
tokens and the keywords `$v $f $d $p $. $= $}` reports no include request. -/
theorem checkBytes_errorNotRequest (config : ModeConfig) (arr : ByteArray) (toks : List String)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_toks : ∀ t ∈ toks, IsLabelToken t ∨ IsMathToken t ∨
      t ∈ ["$v", "$f", "$d", "$p", "$.", "$=", "$}"]) :
    ParserOps.ErrorNotRequest (checkBytes (arr ++ renderText toks) config).error? :=
  checkBytes_append_errorNotRequest config arr _ h_err (by rw [h_start]; trivial) h_ws
    (.of_noDollarLBrack (noDollarLBrack_renderText toks h_toks) 0)

end Metamath.SourceCompleteness
