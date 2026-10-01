import Metamath.SourceCompleteness.Tokens

/-!
# The bytes of a token

The parser reads each token as a `ByteSlice`. `ByteSlice.bytes` is its content; this file shows
that every operation the parser applies to a token is a function of that content
(`feedToken_congr`), characterizes the lexical tokens `feed` produces (`LexToken`: nonempty, no
whitespace byte) and what `toLabel` and `toMath` accept on them, and gives the content of a slice
that spells a label token, a math symbol token or a keyword (`spells_label`, `spells_math`,
`spells_eqArray`, `spells_dollar_*`).
-/

set_option autoImplicit false

universe u v

/-! ## Byte arrays as lists -/

namespace ByteArray

theorem toList_loop_eq (bs : ByteArray) (i : Nat) (r : List UInt8) :
    toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction toList.loop bs i r with
  | case1 i r h ih =>
    have hi : i < bs.data.toList.length := by simpa using h
    rw [ih, List.drop_eq_getElem_cons (l := bs.data.toList) hi]
    simp [ByteArray.get!, h]
  | case2 i r h =>
    rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt h)]
    simp

theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  simp [toList, toList_loop_eq]

theorem length_toList (bs : ByteArray) : bs.toList.length = bs.size := by
  simp [toList_eq_data_toList]

theorem toList_inj {a b : ByteArray} : a.toList = b.toList ↔ a = b := by
  rw [toList_eq_data_toList, toList_eq_data_toList, Array.toList_inj]
  exact ⟨ByteArray.ext, fun h => h ▸ rfl⟩

theorem toList_toByteArray (l : List UInt8) : l.toByteArray.toList = l := by
  rw [toList_eq_data_toList, List.toList_data_toByteArray]

theorem toList_append (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  simp only [ByteArray.toList_eq_data_toList, ByteArray.data_append, Array.toList_append]

theorem getElem!_eq_getD (a : ByteArray) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  unfold getElem! instGetElem?OfGetElemOfDecidable
  simp only [decidableGetElem?]
  by_cases h : i < a.size
  · simp [h, toList_eq_data_toList, List.getD_eq_getElem?_getD, ByteArray.getElem_eq_getElem_data]
  · simp [h, toList_eq_data_toList, List.getD_eq_getElem?_getD]
    rfl

end ByteArray

/-! ## The bytes of a slice -/

namespace ByteSlice

theorem start_add_size_le (s : ByteSlice) : s.start + s.size ≤ s.byteArray.size := by
  rw [← stop_eq_start_add_size]; exact s.stop_le_size_byteArray

theorem bytes_eq_take_drop (s : ByteSlice) :
    s.bytes = (s.byteArray.toList.drop s.start).take s.size := by
  simp [bytes, toByteArray, ByteArray.toList_eq_data_toList, ByteArray.data_extract,
    Array.toList_extract, List.extract]

theorem length_bytes (s : ByteSlice) : s.bytes.length = s.size := by
  have := s.start_add_size_le
  rw [bytes_eq_take_drop, ByteArray.toList_eq_data_toList]
  simp; omega

theorem size_eq_length (s : ByteSlice) : s.size = s.bytes.length := s.length_bytes.symm

theorem len_eq_length (s : ByteSlice) : s.len = s.bytes.length := s.size_eq_length

theorem getElem_eq_getElem_bytes (s : ByteSlice) (i : Nat) (h : i < s.size) :
    s[i] = s.bytes[i]'(by rw [length_bytes]; exact h) := by
  have := s.start_add_size_le
  show s.byteArray[s.start + i]'(by omega) = _
  simp [bytes_eq_take_drop, ByteArray.toList_eq_data_toList, ByteArray.getElem_eq_getElem_data]

theorem getElem!_eq_getD (s : ByteSlice) (i : Nat) : s[i]! = s.bytes.getD i 0 := by
  unfold getElem! instGetElem?OfGetElemOfDecidable
  simp only [decidableGetElem?]
  by_cases h : i < s.size
  · have h' : i < s.bytes.length := by rw [length_bytes]; exact h
    simp [h, getElem_eq_getElem_bytes, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h']
  · have : s.bytes.length ≤ i := by rw [length_bytes]; omega
    simp [h, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
    rfl

/-- The bytes of `A.toByteSlice a b`: the bounds are clamped as `toByteSlice` clamps them. -/
theorem bytes_toByteSlice (A : ByteArray) (a b : Nat) :
    (A.toByteSlice a b).bytes = (A.toList.drop a).take (b - a) := by
  unfold ByteArray.toByteSlice
  split
  · split
    · simp only [bytes_eq_take_drop, size, start, stop, byteArray]
    · simp only [bytes_eq_take_drop, size, start, stop, byteArray]; simp; omega
  · have hl : (A.toList.drop a).length ≤ b - a := by
      simp [ByteArray.toList_eq_data_toList]; omega
    split
    · simp only [bytes_eq_take_drop, size, start, stop, byteArray]
      rw [List.take_of_length_le hl,
        List.take_of_length_le (by simp [ByteArray.toList_eq_data_toList])]
    · simp only [bytes_eq_take_drop, size, start, stop, byteArray]
      simp [ByteArray.toList_eq_data_toList]; omega

theorem bytes_toByteSlice_self (A : ByteArray) : A.toByteSlice.bytes = A.toList := by
  rw [bytes_toByteSlice, List.take_of_length_le (by simp [ByteArray.toList_eq_data_toList])]
  simp

/-- `ByteSlice.mk A off len` spells `len` bytes of `A` from `off`, clamped to the end of `A`. -/
theorem bytes_mk (A : ByteArray) (off len : Nat) :
    (ByteSlice.mk A off len).bytes = (A.toList.drop off).take len := by
  simp [ByteSlice.mk, bytes_toByteSlice]

/-- A function satisfying the recursion equations of the loop of `ByteSlice.forIn` runs `f` over
the bytes that remain. -/
theorem loop_eq_forIn {m : Type u → Type v} {β : Type u} [Monad m] (s : ByteSlice)
    (f : UInt8 → β → m (ForInStep β)) (L : (i : Nat) → i ≤ s.size → β → m β)
    (h0 : ∀ h b, L 0 h b = pure b)
    (hs : ∀ i h b, L (i + 1) h b = (do
      match (← f s[s.size - 1 - i] b) with
      | ForInStep.done b => pure b
      | ForInStep.yield b => L i (Nat.le_of_succ_le h) b)) :
    ∀ i h b, L i h b = forIn (s.bytes.drop (s.size - i)) b f := by
  intro i
  induction i with
  | zero =>
    intro h b
    rw [h0, Nat.sub_zero, List.drop_eq_nil_of_le (by rw [length_bytes]; exact Nat.le_refl _)]
    rfl
  | succ i ih =>
    intro h b
    have hlt : s.size - (i + 1) < s.bytes.length := by rw [length_bytes]; omega
    have e1 : s.size - 1 - i = s.size - (i + 1) := by omega
    have e2 : s.size - (i + 1) + 1 = s.size - i := by omega
    rw [hs, List.drop_eq_getElem_cons hlt, List.forIn_cons, getElem_eq_getElem_bytes s _ (by omega)]
    simp only [e1, e2]
    congr 1
    funext r
    cases r with
    | done b => rfl
    | yield b => exact ih _ b

/-- `for` over a slice runs over its bytes. -/
theorem forIn_eq_forIn_bytes {m : Type u → Type v} {β : Type u} [Monad m] (s : ByteSlice)
    (init : β) (f : UInt8 → β → m (ForInStep β)) :
    forIn s init f = forIn s.bytes init f := by
  show ByteSlice.forIn s init f = _
  unfold ByteSlice.forIn
  rw [show s.bytes = s.bytes.drop (s.size - s.size) by simp]
  refine loop_eq_forIn s f _ ?_ ?_ s.size _ init
  · intro h b; rfl
  · intro i h b; rfl

/-! ## Operations on a slice are functions of its bytes -/

open Metamath.Verify

theorem forIn_congr {m : Type u → Type v} {β : Type u} [Monad m] {s s' : ByteSlice}
    (h : s.bytes = s'.bytes) (init : β) (f : UInt8 → β → m (ForInStep β)) :
    forIn s init f = forIn s' init f := by
  rw [forIn_eq_forIn_bytes, forIn_eq_forIn_bytes, h]

private theorem eqArray_loop (a : ByteArray) (l : List UInt8) (i : Nat)
    (hi : i + l.length ≤ a.size) :
    (forIn (m := Id) l (i, true) fun b r =>
      if a[r.1]! ≠ b then pure (ForInStep.done (r.1, false))
      else pure (ForInStep.yield (r.1 + 1, r.2))).run.2 =
    decide (l = (a.toList.drop i).take l.length) := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    have hi' : i < a.toList.length := by
      rw [ByteArray.length_toList]; simp at hi; omega
    have ha : a[i]! = a.toList[i] := by
      rw [ByteArray.getElem!_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
    rw [List.forIn_cons, List.drop_eq_getElem_cons hi', List.length_cons, List.take_succ_cons]
    by_cases hb : a.toList[i] = b
    · have := ih (i + 1) (by simp at hi; omega)
      simpa [ha, hb] using this
    · have hb' : ¬ b = a.toList[i] := fun e => hb e.symm
      simp [ha, hb, hb']

/-- `eqArray` compares the bytes of a slice with the bytes of an array. -/
theorem eqArray_eq (s : ByteSlice) (a : ByteArray) : s.eqArray a = decide (s.bytes = a.toList) := by
  unfold eqArray
  dsimp only
  rw [forIn_eq_forIn_bytes]
  by_cases hsz : s.size = a.size
  · have hl : 0 + s.bytes.length ≤ a.size := by rw [length_bytes]; omega
    have key := eqArray_loop a s.bytes 0 hl
    rw [List.drop_zero,
      List.take_of_length_le (by rw [length_bytes, ByteArray.length_toList]; omega)] at key
    simp only [hsz, ne_eq, not_true_eq_false, if_false]
    exact key
  · have : s.bytes ≠ a.toList := fun e => hsz (by
      rw [size_eq_length, e, ByteArray.length_toList])
    simp [hsz, this]

theorem eqArray_congr {s s' : ByteSlice} (h : s.bytes = s'.bytes) (a : ByteArray) :
    s.eqArray a = s'.eqArray a := by
  rw [eqArray_eq, eqArray_eq, h]

theorem len_congr {s s' : ByteSlice} (h : s.bytes = s'.bytes) : s.len = s'.len := by
  rw [len_eq_length, len_eq_length, h]

theorem getElem!_congr {s s' : ByteSlice} (h : s.bytes = s'.bytes) (i : Nat) : s[i]! = s'[i]! := by
  rw [getElem!_eq_getD, getElem!_eq_getD, h]

private theorem push_loop (g : UInt8 → Char) (l : List UInt8) (str : String) :
    (forIn (m := Id) l str fun c r => pure (ForInStep.yield (r.push (g c)))).run =
    str ++ String.ofList (l.map g) := by
  rw [List.forIn_pure_yield_eq_foldl, Id.run_pure]
  induction l generalizing str with
  | nil => simp [String.append_empty]
  | cons c l ih =>
    rw [List.foldl_cons, ih]
    apply String.ext
    simp [String.toList_append, String.toList_ofList, String.toList_push]

/-- `toString` spells the bytes as characters. -/
theorem toString_eq (s : ByteSlice) : s.toString = String.ofList (s.bytes.map Char.ofUInt8) := by
  unfold ByteSlice.toString
  dsimp only
  rw [forIn_eq_forIn_bytes]
  have := push_loop Char.ofUInt8 s.bytes ""
  rw [String.empty_append] at this
  exact this

theorem toString_congr {s s' : ByteSlice} (h : s.bytes = s'.bytes) : s.toString = s'.toString := by
  rw [toString_eq, toString_eq, h]

end ByteSlice

namespace Metamath.SourceCompleteness

open Metamath.Verify

private theorem check_loop (p : UInt8 → Bool) (l : List UInt8) (ok : Bool) (str : String) :
    (forIn (m := Id) l (ok, str) fun c r =>
      if p c = true then pure (ForInStep.yield (r.1, r.2.push (uint8ToChar c)))
      else pure (ForInStep.yield (false, r.2.push (uint8ToChar c)))).run =
    (ok && l.all p, str ++ String.ofList (l.map uint8ToChar)) := by
  induction l generalizing ok str with
  | nil => simp [String.append_empty]
  | cons c l ih =>
    have e : str.push (uint8ToChar c) ++ String.ofList (l.map uint8ToChar) =
        str ++ String.ofList (uint8ToChar c :: l.map uint8ToChar) := by
      apply String.ext
      simp [String.toList_append, String.toList_ofList, String.toList_push]
    by_cases hc : p c = true
    · simp [List.forIn_cons, hc, ih, e]
    · simp [List.forIn_cons, hc, ih, e]


/-- `toLabel` checks that every byte is a label character and spells the bytes as characters. -/
theorem toLabel_eq (s : ByteSlice) :
    toLabel s = (s.bytes.all isLabelChar, String.ofList (s.bytes.map uint8ToChar)) := by
  unfold toLabel
  dsimp only
  rw [ByteSlice.forIn_eq_forIn_bytes]
  have := check_loop isLabelChar s.bytes true ""
  rw [Bool.true_and, String.empty_append] at this
  rw [Id.run_bind, this]
  rfl

/-- `toMath` checks that every byte is a math character and spells the bytes as characters. -/
theorem toMath_eq (s : ByteSlice) :
    toMath s = (s.bytes.all isMathChar, String.ofList (s.bytes.map uint8ToChar)) := by
  unfold toMath
  dsimp only
  rw [ByteSlice.forIn_eq_forIn_bytes]
  have := check_loop isMathChar s.bytes true ""
  rw [Bool.true_and, String.empty_append] at this
  rw [Id.run_bind, this]
  rfl

section Congruence

variable {tk tk' : ByteSlice}

theorem toLabel_congr (h : tk.bytes = tk'.bytes) : toLabel tk = toLabel tk' := by
  rw [toLabel_eq, toLabel_eq, h]

theorem toMath_congr (h : tk.bytes = tk'.bytes) : toMath tk = toMath tk' := by
  rw [toMath_eq, toMath_eq, h]

open ParserState

theorem label_congr (h : tk.bytes = tk'.bytes) (s : ParserState) (pos : Pos) :
    s.label pos tk = s.label pos tk' := by
  unfold ParserState.label; rw [toLabel_congr h]

theorem withMath_congr (h : tk.bytes = tk'.bytes) (s : ParserState) (pos : Pos)
    (f : ParserState → String → ParserState) : s.withMath pos tk f = s.withMath pos tk' f := by
  unfold ParserState.withMath; rw [toMath_congr h]

theorem sym_congr (h : tk.bytes = tk'.bytes) (s : ParserState) (pos : Pos) (f : String → Object) :
    s.sym pos tk f = s.sym pos tk' f := by
  unfold ParserState.sym; rw [ByteSlice.eqArray_congr h, withMath_congr h]

theorem includePathFromToken_congr (h : tk.bytes = tk'.bytes) :
    includePathFromToken tk = includePathFromToken tk' := by
  unfold includePathFromToken; rw [ByteSlice.toString_congr h]

theorem decodeCompressed_congr (h : tk.bytes = tk'.bytes) (phase : CompressedPhase)
    (p : CompressedInvalidBytePolicy) (q : CompressedSavePlacement) :
    decodeCompressed tk phase p q = decodeCompressed tk' phase p q := by
  unfold decodeCompressed; dsimp only; rw [ByteSlice.forIn_congr h]

theorem feedProof_goNormal_congr (h : tk.bytes = tk'.bytes) (s : ParserState) (pr : ProofState) :
    feedProof.goNormal s tk pr = feedProof.goNormal s tk' pr := by
  unfold feedProof.goNormal; rw [ByteSlice.eqArray_congr h, toLabel_congr h]

theorem feedProof_go_congr (h : tk.bytes = tk'.bytes) (s : ParserState) (pr : ProofState) :
    feedProof.go s tk pr = feedProof.go s tk' pr := by
  unfold feedProof.go
  simp only [ByteSlice.eqArray_congr h, toLabel_congr h, decodeCompressed_congr h,
    feedProof_goNormal_congr h]

theorem feedProof_congr (h : tk.bytes = tk'.bytes) (s : ParserState) (pr : ProofState) :
    s.feedProof tk pr = s.feedProof tk' pr := by
  unfold feedProof; rw [feedProof_go_congr h]

theorem firstNonSourceByte?_congr (h : tk.bytes = tk'.bytes) :
    firstNonSourceByte? tk = firstNonSourceByte? tk' := by
  unfold firstNonSourceByte?; rw [ByteSlice.forIn_congr h]

theorem hasCommentDelimiter_congr (h : tk.bytes = tk'.bytes) :
    hasCommentDelimiter tk = hasCommentDelimiter tk' := by
  unfold hasCommentDelimiter; simp only [ByteSlice.forIn_congr h]

/-- `feedToken` reads a token only through its bytes. -/
theorem feedToken_congr (h : tk.bytes = tk'.bytes) (s : ParserState) (pos : Nat) :
    s.feedToken pos tk = s.feedToken pos tk' := by
  unfold feedToken
  simp only [ByteSlice.eqArray_congr h, ByteSlice.len_congr h, ByteSlice.getElem!_congr h,
    label_congr h, sym_congr h, withMath_congr h, toLabel_congr h, includePathFromToken_congr h,
    ByteSlice.toString_congr h, feedProof_congr h, hasCommentDelimiter_congr h,
    firstNonSourceByte?_congr h]

end Congruence

/-! ## Characters of the two token classes -/

/-- A property of all bytes, checked value by value. -/
theorem byte_forall {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n)) (b : UInt8) :
    P b := by
  have := h b.toNat (UInt8.toNat_lt b)
  rwa [UInt8.ofNat_toNat] at this

/-- A property of all ASCII characters, checked value by value. -/
theorem ascii_forall {P : Char → Prop} (h : ∀ n, n < 128 → P (Char.ofNat n)) (c : Char)
    (hc : c.toNat < 128) : P c := by
  have := h c.toNat hc
  rwa [Char.ofNat_toNat] at this

theorem isLabelChar_char (b : UInt8) (h : isLabelChar b = true) :
    (uint8ToChar b).isAlphanum ∨ uint8ToChar b = '-' ∨ uint8ToChar b = '_' ∨
      uint8ToChar b = '.' :=
  byte_forall (P := fun b => isLabelChar b = true →
      (uint8ToChar b).isAlphanum ∨ uint8ToChar b = '-' ∨ uint8ToChar b = '_' ∨
        uint8ToChar b = '.')
    (by decide +kernel) b h

theorem isMathChar_char (b : UInt8) (h : isMathChar b = true) (hw : isWhitespace b = false) :
    33 ≤ (uint8ToChar b).toNat ∧ (uint8ToChar b).toNat ≤ 126 ∧ uint8ToChar b ≠ '$' :=
  byte_forall (P := fun b => isMathChar b = true → isWhitespace b = false →
      33 ≤ (uint8ToChar b).toNat ∧ (uint8ToChar b).toNat ≤ 126 ∧ uint8ToChar b ≠ '$')
    (by decide +kernel) b h hw

theorem uint8ToChar_toUInt8 (c : Char) (hc : c.toNat < 128) : uint8ToChar c.toUInt8 = c :=
  ascii_forall (P := fun c => uint8ToChar c.toUInt8 = c) (by decide +kernel) c hc

/-- The characters of a label token are ASCII. -/
theorem labelChar_lt {c : Char} (h : c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = '.') :
    c.toNat < 128 := by
  rcases h with h | rfl | rfl | rfl
  · simp only [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le, ge_iff_le] at h
    have : c.toNat = c.val.toNat := rfl
    have : 'Z'.val.toNat = 90 := rfl
    have : 'z'.val.toNat = 122 := rfl
    have : '9'.val.toNat = 57 := rfl
    omega
  all_goals decide

theorem labelChar_byte {c : Char} (h : c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = '.') :
    isLabelChar c.toUInt8 = true ∧ isWhitespace c.toUInt8 = false :=
  ascii_forall (P := fun c => (c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = '.') →
      isLabelChar c.toUInt8 = true ∧ isWhitespace c.toUInt8 = false)
    (by decide +kernel) c (labelChar_lt h) h

theorem mathChar_byte {c : Char} (h : 33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '$') :
    isMathChar c.toUInt8 = true ∧ isWhitespace c.toUInt8 = false :=
  ascii_forall (P := fun c => (33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '$') →
      isMathChar c.toUInt8 = true ∧ isWhitespace c.toUInt8 = false)
    (by decide +kernel) c (by omega) h

theorem IsLabelToken.ascii {t : String} (ht : IsLabelToken t) : ∀ c ∈ t.toList, c.toNat < 128 :=
  fun c hc => labelChar_lt (ht.2 c hc)

theorem IsMathToken.ascii {t : String} (ht : IsMathToken t) : ∀ c ∈ t.toList, c.toNat < 128 :=
  fun c hc => by have := ht.2 c hc; omega

theorem labelChar_printable {c : Char} (h : c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = '.') :
    isPrintable c.toUInt8 = true :=
  ascii_forall (P := fun c => (c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = '.') →
      isPrintable c.toUInt8 = true)
    (by decide +kernel) c (labelChar_lt h) h

theorem mathChar_printable {c : Char} (h : 33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '$') :
    isPrintable c.toUInt8 = true :=
  ascii_forall (P := fun c => (33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '$') →
      isPrintable c.toUInt8 = true)
    (by decide +kernel) c (by omega) h

/-! ## Lexical tokens -/

/-- A token as the lexer cuts it: nonempty and free of whitespace. -/
def LexToken (tk : ByteSlice) : Prop :=
  tk.bytes ≠ [] ∧ ∀ b ∈ tk.bytes, isWhitespace b = false

theorem ofList_ne_empty {l : List Char} (h : l ≠ []) : String.ofList l ≠ "" := by
  intro e
  apply h
  rw [← String.toList_ofList (l := l), e]
  exact String.toList_eq_nil_iff.mpr rfl

/-- A lexical token that `toLabel` accepts spells a label token. -/
theorem toLabel_isLabelToken {tk : ByteSlice} (hl : LexToken tk) (h : (toLabel tk).1 = true) :
    IsLabelToken (toLabel tk).2 := by
  rw [toLabel_eq] at h ⊢
  refine ⟨ofList_ne_empty (by simpa using hl.1), fun c hc => ?_⟩
  rw [String.toList_ofList, List.mem_map] at hc
  obtain ⟨b, hb, rfl⟩ := hc
  exact isLabelChar_char b (List.all_eq_true.mp h b hb)

/-- A lexical token that `toMath` accepts spells a math symbol token. -/
theorem toMath_isMathToken {tk : ByteSlice} (hl : LexToken tk) (h : (toMath tk).1 = true) :
    IsMathToken (toMath tk).2 := by
  rw [toMath_eq] at h ⊢
  refine ⟨ofList_ne_empty (by simpa using hl.1), fun c hc => ?_⟩
  rw [String.toList_ofList, List.mem_map] at hc
  obtain ⟨b, hb, rfl⟩ := hc
  exact isMathChar_char b (List.all_eq_true.mp h b hb) (hl.2 b hb)

/-! ## Slices spelling a string -/

/-- The UTF-8 bytes of a string. -/
theorem toUTF8_toList (t : String) : t.toUTF8.toList = t.toList.flatMap String.utf8EncodeChar := by
  conv => lhs; rw [← String.ofList_toList (s := t)]
  rw [String.toUTF8_eq_toByteArray]
  exact ByteArray.toList_toByteArray _

theorem flatMap_utf8EncodeChar_of_ascii (l : List Char) (h : ∀ c ∈ l, c.toNat < 128) :
    l.flatMap String.utf8EncodeChar = l.map Char.toUInt8 := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : c.utf8Size = 1 := by
      rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
      have h1 := h c (by simp)
      have h2 : c.toNat = c.val.toNat := rfl
      have h3 : (127 : UInt32).toNat = 127 := rfl
      omega
    rw [List.flatMap_cons, String.utf8EncodeChar_eq_singleton hc, Char.toUInt8_val, List.map_cons,
      ih (fun d hd => h d (by simp [hd]))]
    rfl

/-- The UTF-8 bytes of an ASCII string are the codes of its characters. -/
theorem toUTF8_toList_of_ascii {t : String} (h : ∀ c ∈ t.toList, c.toNat < 128) :
    t.toUTF8.toList = t.toList.map Char.toUInt8 := by
  rw [toUTF8_toList, flatMap_utf8EncodeChar_of_ascii _ h]

/-- A slice spelling `t` compares with the bytes of `u` exactly when `t = u`. -/
theorem spells_eqArray {t : String} {tk : ByteSlice} (h : tk.bytes = t.toUTF8.toList) (u : String) :
    tk.eqArray u.toAscii = decide (t = u) := by
  rw [ByteSlice.eqArray_eq, h, String.toAscii, String.toUTF8_eq_toByteArray]
  by_cases e : t = u
  · simp [e]
  · have : t.toByteArray.toList ≠ u.toByteArray.toList := fun h' =>
      e (String.toByteArray_inj.mp (ByteArray.toList_inj.mp h'))
    simp [e, this]

theorem spells_ascii {t : String} (h : ∀ c ∈ t.toList, c.toNat < 128) {tk : ByteSlice}
    (htk : tk.bytes = t.toUTF8.toList) : String.ofList (tk.bytes.map uint8ToChar) = t := by
  rw [htk, toUTF8_toList_of_ascii h, List.map_map,
    List.map_congr_left (f := uint8ToChar ∘ Char.toUInt8) (g := id)
      (fun c hc => uint8ToChar_toUInt8 c (h c hc)), List.map_id, String.ofList_toList]

/-- A slice spelling a label token is a lexical token that `toLabel` reads as that label. -/
theorem spells_label {t : String} (ht : IsLabelToken t) {tk : ByteSlice}
    (h : tk.bytes = t.toUTF8.toList) : toLabel tk = (true, t) ∧ LexToken tk := by
  have hb : tk.bytes = t.toList.map Char.toUInt8 := by rw [h, toUTF8_toList_of_ascii ht.ascii]
  have hne : t.toList ≠ [] := fun e => ht.1 (String.toList_eq_nil_iff.mp e)
  refine ⟨?_, ?_, ?_⟩
  · rw [toLabel_eq, spells_ascii ht.ascii h, hb]
    congr 1
    rw [List.all_eq_true]
    intro b hmem
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
    exact (labelChar_byte (ht.2 c hc)).1
  · rw [hb]; simpa using hne
  · intro b hmem
    rw [hb] at hmem
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
    exact (labelChar_byte (ht.2 c hc)).2

/-- A slice spelling a math symbol token is a lexical token that `toMath` reads as that symbol. -/
theorem spells_math {t : String} (ht : IsMathToken t) {tk : ByteSlice}
    (h : tk.bytes = t.toUTF8.toList) : toMath tk = (true, t) ∧ LexToken tk := by
  have hb : tk.bytes = t.toList.map Char.toUInt8 := by rw [h, toUTF8_toList_of_ascii ht.ascii]
  have hne : t.toList ≠ [] := fun e => ht.1 (String.toList_eq_nil_iff.mp e)
  refine ⟨?_, ?_, ?_⟩
  · rw [toMath_eq, spells_ascii ht.ascii h, hb]
    congr 1
    rw [List.all_eq_true]
    intro b hmem
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
    exact (mathChar_byte (ht.2 c hc)).1
  · rw [hb]; simpa using hne
  · intro b hmem
    rw [hb] at hmem
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
    exact (mathChar_byte (ht.2 c hc)).2

/-! ## Keywords -/

theorem spells_two {tk : ByteSlice} {a b : Char} (ha : a.toNat < 128) (hb : b.toNat < 128)
    (h : tk.bytes = (String.ofList [a, b]).toUTF8.toList) :
    tk.len = 2 ∧ tk[0]! = a.toUInt8 ∧ tk[1]! = b.toUInt8 ∧
      uint8ToChar tk[0]! = a ∧ uint8ToChar tk[1]! = b := by
  have hab : ∀ c ∈ (String.ofList [a, b]).toList, c.toNat < 128 := by
    intro c hc
    rw [String.toList_ofList] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  rw [toUTF8_toList_of_ascii hab, String.toList_ofList] at h
  simp [ByteSlice.len_eq_length, ByteSlice.getElem!_eq_getD, h, uint8ToChar_toUInt8 a ha,
    uint8ToChar_toUInt8 b hb]

theorem spells_dollar_v {tk : ByteSlice} (h : tk.bytes = "$v".toUTF8.toList) :
    tk.len = 2 ∧ tk[0]! = '$'.toUInt8 ∧ tk[1]! = 'v'.toUInt8 ∧
      uint8ToChar tk[0]! = '$' ∧ uint8ToChar tk[1]! = 'v' :=
  spells_two (a := '$') (b := 'v') (by decide) (by decide) h

theorem spells_dollar_d {tk : ByteSlice} (h : tk.bytes = "$d".toUTF8.toList) :
    tk.len = 2 ∧ tk[0]! = '$'.toUInt8 ∧ tk[1]! = 'd'.toUInt8 ∧
      uint8ToChar tk[0]! = '$' ∧ uint8ToChar tk[1]! = 'd' :=
  spells_two (a := '$') (b := 'd') (by decide) (by decide) h

theorem spells_dollar_rbrace {tk : ByteSlice} (h : tk.bytes = "$}".toUTF8.toList) :
    tk.len = 2 ∧ tk[0]! = '$'.toUInt8 ∧ tk[1]! = '}'.toUInt8 ∧
      uint8ToChar tk[0]! = '$' ∧ uint8ToChar tk[1]! = '}' :=
  spells_two (a := '$') (b := '}') (by decide) (by decide) h

theorem spells_dollar_f {tk : ByteSlice} (h : tk.bytes = "$f".toUTF8.toList) :
    tk.len = 2 ∧ tk[0]! = '$'.toUInt8 ∧ tk[1]! = 'f'.toUInt8 ∧
      uint8ToChar tk[0]! = '$' ∧ uint8ToChar tk[1]! = 'f' :=
  spells_two (a := '$') (b := 'f') (by decide) (by decide) h

theorem spells_dollar_p {tk : ByteSlice} (h : tk.bytes = "$p".toUTF8.toList) :
    tk.len = 2 ∧ tk[0]! = '$'.toUInt8 ∧ tk[1]! = 'p'.toUInt8 ∧
      uint8ToChar tk[0]! = '$' ∧ uint8ToChar tk[1]! = 'p' :=
  spells_two (a := '$') (b := 'p') (by decide) (by decide) h

/-- A slice spelling a label token does not start with `$`. -/
theorem spells_label_head {t : String} (ht : IsLabelToken t) {tk : ByteSlice}
    (h : tk.bytes = t.toUTF8.toList) : tk[0]! ≠ '$'.toUInt8 := by
  rw [ByteSlice.getElem!_eq_getD, h, toUTF8_toList_of_ascii ht.ascii]
  cases hl : t.toList with
  | nil => exact absurd (String.toList_eq_nil_iff.mp hl) ht.1
  | cons c l =>
    have hc := (labelChar_byte (ht.2 c (by simp [hl]))).1
    intro e
    simp only [List.map_cons, List.getD_cons_zero] at e
    rw [e] at hc
    exact absurd hc (by decide)

/-- The parser's test for a `$` keyword fails on a slice spelling a label token. -/
theorem spells_label_not_keyword {t : String} (ht : IsLabelToken t) {tk : ByteSlice}
    (h : tk.bytes = t.toUTF8.toList) : (tk.len == 2 && tk[0]! == '$'.toUInt8) = false := by
  simp [spells_label_head ht h]

theorem IsLabelToken.ne {t u : String} (ht : IsLabelToken t) (hu : ¬ IsLabelToken u) : t ≠ u :=
  fun e => hu (e ▸ ht)

theorem IsMathToken.ne {t u : String} (ht : IsMathToken t) (hu : ¬ IsMathToken u) : t ≠ u :=
  fun e => hu (e ▸ ht)

example : ¬ IsMathToken "$." ∧ ¬ IsLabelToken "?" ∧ ¬ IsLabelToken "(" ∧
    IsMathToken "(" := by
  decide

end Metamath.SourceCompleteness
