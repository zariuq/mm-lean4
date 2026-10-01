import Metamath.SourceCompleteness.Render
import Metamath.SourceCompleteness.Bytes

/-!
# Running the dummy declarations

`runTokens_declTokens`: the tokens `declTokens` of fresh dummy declarations, fed one by one from a
parser state between statements, take it to the state that `Verify.DB.declareDummies` describes.
The proof follows the parser token by token: one lemma per parser mode and token kind
(`feedToken_start_v`, `feedToken_var_sym`, ...), the eight tokens `$v d $. lbl $f tc d $.` of one
dummy (`runTokens_declareDummy`), their fold (`runTokens_foldl_declareDummy`), one `$d v w $.`
statement (`runTokens_dj`) and the fold over the pairs (`runTokens_djs`). Positions reach the
database only in error messages, so on these successful paths the result does not depend on them.
-/

set_option autoImplicit false

namespace Metamath.SourceCompleteness

open Metamath.Verify Metamath.CheckerCompleteness

/-! ## One token -/

/-- A slice spelling `t` differs from the bytes of any other string. -/
theorem eqArray_of_spells {t u : String} {tk : ByteSlice} (htk : tk.bytes = t.toUTF8.toList)
    (h : t ≠ u) : tk.eqArray u.toAscii = false := by
  rw [spells_eqArray htk]; exact decide_eq_false h

/-- A slice spelling `t` equals the bytes of `t`. -/
theorem eqArray_self_of_spells {t : String} {tk : ByteSlice} (htk : tk.bytes = t.toUTF8.toList) :
    tk.eqArray t.toAscii = true := by
  rw [spells_eqArray htk]; exact decide_eq_true rfl

/-- `$v` between statements opens a variable declaration. -/
theorem feedToken_start_v (s : ParserState) (base : Nat) (h : s.tokp = .start) (tk : ByteSlice)
    (htk : tk.bytes = "$v".toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .var false } := by
  obtain ⟨h1, h2, -, -, h5⟩ := spells_dollar_v htk
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (u := "$(") (by decide),
    eqArray_of_spells htk (u := "$[") (by decide), h1, h2, h5]
  simp

/-- `$d` between statements opens a disjoint-variable statement. -/
theorem feedToken_start_d (s : ParserState) (base : Nat) (h : s.tokp = .start) (tk : ByteSlice)
    (htk : tk.bytes = "$d".toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .djvars #[] } := by
  obtain ⟨h1, h2, -, -, h5⟩ := spells_dollar_d htk
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (u := "$(") (by decide),
    eqArray_of_spells htk (u := "$[") (by decide), h1, h2, h5]
  simp

/-- A label token between statements starts a labeled statement. -/
theorem feedToken_start_label (s : ParserState) (base : Nat) (h : s.tokp = .start) (t : String)
    (ht : IsLabelToken t) (tk : ByteSlice) (htk : tk.bytes = t.toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .label (s.mkPos base) t } := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (ht.ne (u := "$(") (by decide)),
    eqArray_of_spells htk (ht.ne (u := "$[") (by decide)), spells_label_not_keyword ht htk]
  unfold ParserState.label
  simp only [(spells_label ht htk).1]
  simp

/-- A math token in a `$v` statement declares it. -/
theorem feedToken_var_sym (s : ParserState) (base : Nat) (seen : Bool) (h : s.tokp = .var seen)
    (t : String) (ht : IsMathToken t) (tk : ByteSlice) (htk : tk.bytes = t.toUTF8.toList) :
    s.feedToken base tk =
      { s with db := s.db.insert (s.mkPos base) t .var, tokp := .var true } := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (ht.ne (u := "$(") (by decide)),
    eqArray_of_spells htk (ht.ne (u := "$[") (by decide)),
    eqArray_of_spells htk (ht.ne (u := "$.") (by decide))]
  unfold ParserState.sym ParserState.withMath
  simp only [eqArray_of_spells htk (ht.ne (u := "$.") (by decide)), (spells_math ht htk).1]
  simp [ParserState.withDB]

/-- `$.` closes a nonempty `$v` statement. -/
theorem feedToken_var_dot (s : ParserState) (base : Nat) (h : s.tokp = .var true) (tk : ByteSlice)
    (htk : tk.bytes = "$.".toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .start } := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (u := "$(") (by decide),
    eqArray_of_spells htk (u := "$[") (by decide), eqArray_self_of_spells htk]
  simp

/-- `$f` after a label starts a floating hypothesis. -/
theorem feedToken_label_f (s : ParserState) (base : Nat) (q : Pos) (lab : String)
    (h : s.tokp = .label q lab) (tk : ByteSlice) (htk : tk.bytes = "$f".toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .math #[] ⟨.float, q, lab⟩ } := by
  obtain ⟨h1, h2, -, -, h5⟩ := spells_dollar_f htk
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (u := "$(") (by decide),
    eqArray_of_spells htk (u := "$[") (by decide), h1, h2, h5]
  simp

/-- A math token is not a statement delimiter. -/
theorem delim_of_mathToken {t : String} (ht : IsMathToken t) {tk : ByteSlice}
    (htk : tk.bytes = t.toUTF8.toList) (k : TokensKind) : tk.eqArray k.delim = false := by
  cases k <;> simp only [TokensKind.delim] <;>
    first
    | exact eqArray_of_spells htk (ht.ne (u := "$=") (by decide))
    | exact eqArray_of_spells htk (ht.ne (u := "$.") (by decide))

/-- A declared constant in a statement's math string. -/
theorem feedToken_math_const (s : ParserState) (base : Nat) (arr : Array Verify.Sym)
    (p : TokensParser) (h : s.tokp = .math arr p) (t c : String) (ht : IsMathToken t)
    (h_find : s.db.find? t = some (.const c)) (tk : ByteSlice) (htk : tk.bytes = t.toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .math (arr.push (.const t)) p } := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (ht.ne (u := "$(") (by decide)),
    eqArray_of_spells htk (ht.ne (u := "$[") (by decide)), delim_of_mathToken ht htk]
  unfold ParserState.withMath
  simp only [(spells_math ht htk).1, h_find]
  rfl

/-- An active variable in a statement's math string. -/
theorem feedToken_math_var (s : ParserState) (base : Nat) (arr : Array Verify.Sym)
    (p : TokensParser) (h : s.tokp = .math arr p) (t v : String) (ht : IsMathToken t)
    (h_find : s.db.find? t = some (.var v)) (h_act : s.db.isActiveVar t = true) (tk : ByteSlice)
    (htk : tk.bytes = t.toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .math (arr.push (.var t)) p } := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (ht.ne (u := "$(") (by decide)),
    eqArray_of_spells htk (ht.ne (u := "$[") (by decide)), delim_of_mathToken ht htk]
  unfold ParserState.withMath
  simp only [(spells_math ht htk).1, h_find, h_act]
  rfl

/-- `$.` ends the math string of a floating hypothesis. -/
theorem feedToken_math_dot (s : ParserState) (base : Nat) (arr : Array Verify.Sym) (q : Pos)
    (lab : String) (h : s.tokp = .math arr ⟨.float, q, lab⟩) (tk : ByteSlice)
    (htk : tk.bytes = "$.".toUTF8.toList) :
    s.feedToken base tk = s.feedTokens arr ⟨.float, q, lab⟩ := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (u := "$(") (by decide),
    eqArray_of_spells htk (u := "$[") (by decide), TokensKind.delim, eqArray_self_of_spells htk]
  simp

/-- A math token in a `$d` statement. -/
theorem feedToken_djvars_sym (s : ParserState) (base : Nat) (arr : Array String)
    (h : s.tokp = .djvars arr) (t : String) (ht : IsMathToken t) (tk : ByteSlice)
    (htk : tk.bytes = t.toUTF8.toList) :
    s.feedToken base tk = ParserState.djvars_loop arr s (s.mkPos base) t := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (ht.ne (u := "$(") (by decide)),
    eqArray_of_spells htk (ht.ne (u := "$[") (by decide)),
    eqArray_of_spells htk (ht.ne (u := "$.") (by decide))]
  unfold ParserState.withMath
  simp only [(spells_math ht htk).1]
  simp

/-- `$.` closes a `$d` statement of at least two variables. -/
theorem feedToken_djvars_dot (s : ParserState) (base : Nat) (arr : Array String)
    (h : s.tokp = .djvars arr) (h_size : 2 ≤ arr.size) (tk : ByteSlice)
    (htk : tk.bytes = "$.".toUTF8.toList) :
    s.feedToken base tk = { s with tokp := .start } := by
  unfold ParserState.feedToken
  simp only [h, eqArray_of_spells htk (u := "$(") (by decide),
    eqArray_of_spells htk (u := "$[") (by decide), eqArray_self_of_spells htk]
  have : ¬ arr.size < 2 := by omega
  simp [this]

/-! ## The parser's actions on the declarations -/

/-- The first variable of a `$d` statement, when active. -/
theorem djvars_loop_first (s : ParserState) (q : Pos) (t : String)
    (h_act : s.db.isActiveVar t = true) :
    ParserState.djvars_loop #[] s q t = { s with tokp := .djvars #[t] } := by
  unfold ParserState.djvars_loop
  simp only [DB.djvarsScopeViolation?, h_act, if_true]
  rw [ParserState.djvars_loop_aux, dif_neg (by simp)]
  rfl

/-- The second variable of a `$d` statement, when active and greater than the first: the pair is
recorded in the active frame. -/
theorem djvars_loop_second (s : ParserState) (q : Pos) (u t : String)
    (h_act : s.db.isActiveVar t = true) (h_lt : u < t) :
    ParserState.djvars_loop #[u] s q t =
      { s with db := s.db.withDJ (·.push (u, t)), tokp := .djvars #[u, t] } := by
  have h_ne : u ≠ t := fun h => (String.lt_irrefl t) (h ▸ h_lt)
  unfold ParserState.djvars_loop
  simp only [DB.djvarsScopeViolation?, h_act, if_true]
  rw [ParserState.djvars_loop_aux, dif_pos (by simp)]
  simp only [List.getElem_toArray, List.getElem_cons_zero, beq_iff_eq, h_ne, if_false, h_lt,
    if_true]
  rw [ParserState.djvars_loop_aux, dif_neg (by simp)]
  rfl

/-- The math string `tc v` of a floating hypothesis is stored when the insertion succeeds. -/
theorem feedTokens_float_eq (s : ParserState) (q : Pos) (lab tc v : String)
    (h_ok : (s.db.insertHyp q lab false #[.const tc, .var v]).error? = none) :
    s.feedTokens #[.const tc, .var v] ⟨.float, q, lab⟩ =
      { s with db := s.db.insertHyp q lab false #[.const tc, .var v], tokp := .start } := by
  unfold ParserState.feedTokens ParserState.withAt
  simp [Formula.hasConstHead, Formula.isFloatShape, ParserState.withDB, h_ok]

/-! ## Running token lists -/

/-- One step of `runTokens`, when the token is accepted without error. -/
theorem runTokens_cons_of_eq {s s' : ParserState} {base : Nat} {t : String} (ts : List String)
    (h : s.feedToken base t.toUTF8.toByteSlice = s') (h_err : s'.db.error? = none) :
    runTokens s base (t :: ts) = runTokens s' (base + t.toUTF8.size + 1) ts := by
  simp only [runTokens, h, h_err, Option.isSome_none, Bool.false_eq_true, if_false]

/-- Running `l1 ++ l2` runs `l2` after `l1`, when `l1` ends without error. -/
private theorem runTokens_append_ok (s : ParserState) (base : Nat) (l1 l2 : List String)
    (h : (runTokens s base l1).db.error? = none) :
    ∃ b, runTokens s base (l1 ++ l2) = runTokens (runTokens s base l1) b l2 := by
  induction l1 generalizing s base with
  | nil => exact ⟨base, rfl⟩
  | cons t ts ih =>
    cases he : (s.feedToken base t.toUTF8.toByteSlice).db.error? with
    | some e =>
      simp only [runTokens, he, Option.isSome_some, if_true] at h
      cases h
    | none =>
      rw [List.cons_append, runTokens_cons_of_eq _ rfl he, runTokens_cons_of_eq _ rfl he]
      rw [runTokens_cons_of_eq _ rfl he] at h
      exact ih _ _ h

/-- `runTokens_cons_of_eq`, in the form used to step through a token list. -/
theorem runTokens_cons_step {s : ParserState} {base : Nat} {t : String} {ts : List String}
    {R : ParserState} (s' : ParserState) (h : s.feedToken base t.toUTF8.toByteSlice = s')
    (h_err : s'.db.error? = none) (h_rest : runTokens s' (base + t.toUTF8.size + 1) ts = R) :
    runTokens s base (t :: ts) = R := by
  rw [runTokens_cons_of_eq ts h h_err, h_rest]

/-! ## Registry facts -/

/-- A constant is registered as a constant. -/
theorem find?_const_of_isConst {db : DB} {c : String} (h : db.isConst c = true) :
    ∃ c', db.find? c = some (.const c') := by
  unfold DB.isConst at h
  split at h
  · next c' h_eq => exact ⟨c', h_eq⟩
  · cases h

/-- A variable is registered as a variable. -/
theorem find?_var_of_isVar {db : DB} {v : String} (h : db.isVar v = true) :
    ∃ v', db.find? v = some (.var v') := by
  unfold DB.isVar at h
  split at h
  · next v' h_eq => exact ⟨v', h_eq⟩
  · cases h

/-- An active variable has an entry in the activity stack. -/
theorem exists_mem_activeVars_of_isActiveVar {db : DB} {v : String}
    (h : db.isActiveVar v = true) : ∃ n, (v, n) ∈ db.activeVars.toList := by
  simp only [DB.isActiveVar, Bool.and_eq_true] at h
  obtain ⟨_, h2⟩ := h
  rw [Array.any_eq_true'] at h2
  obtain ⟨⟨v', n⟩, hmem, heq⟩ := h2
  simp only [beq_iff_eq] at heq
  subst heq
  exact ⟨n, Array.mem_toList_iff.mpr hmem⟩

/-- A registered variable with an entry in the activity stack is active. -/
theorem isActiveVar_of_mem {db : DB} {v : String} {n : Nat} (h_var : db.isVar v = true)
    (h_mem : (v, n) ∈ db.activeVars.toList) : db.isActiveVar v = true := by
  simp only [DB.isActiveVar, h_var, Bool.true_and]
  rw [Array.any_eq_true']
  exact ⟨_, Array.mem_toList_iff.mp h_mem, by simp⟩

/-- A float variable of the active frame has an entry in the activity stack. -/
theorem mem_activeVars_of_mem_frameFloatVars {db : DB} (h_act : FloatVarsActive db) {v : String}
    (hv : v ∈ db.frameFloatVars db.frame) : ∃ d, (v, d) ∈ db.activeVars.toList := by
  unfold DB.frameFloatVars at hv
  rw [List.mem_filterMap] at hv
  obtain ⟨lbl, hlbl, hsome⟩ := hv
  obtain ⟨k, hk, hk_eq⟩ := List.mem_iff_getElem.mp hlbl
  split at hsome
  · rename_i f nm h_find
    split at hsome
    · split at hsome
      · rename_i w h_w
        cases hsome
        have hk' : k < db.frame.hyps.size := by simpa using hk
        have h_find' : db.find? db.frame.hyps[k] = some (.hyp false f nm) := by
          rw [← h_find, ← hk_eq]
          simp
        obtain ⟨d, hd, _⟩ := h_act k hk' f nm h_find'
        rw [h_w] at hd
        exact ⟨d, by simpa [Verify.Sym.value] using hd⟩
      · cases hsome
    · cases hsome
  · cases hsome

/-- A float variable of the active frame that names a variable is active. -/
theorem isActiveVar_of_mem_frameFloatVars {db : DB} (h_act : FloatVarsActive db) {v : String}
    (hv : v ∈ db.frameFloatVars db.frame) (h_var : db.isVar v = true) :
    db.isActiveVar v = true := by
  obtain ⟨d, hd⟩ := mem_activeVars_of_mem_frameFloatVars h_act hv
  exact isActiveVar_of_mem h_var hd

/-! ## One dummy -/

/-- `$v d $.` and `lbl $f tc d $.` for one fresh dummy, from a state between statements. -/
theorem runTokens_declareDummy (s : ParserState) (pos : Pos) (d : DummyDecl) (base : Nat)
    (h_start : s.tokp = .start) (h_err : s.db.error? = none)
    (h_var : s.db.find? d.var = none) (h_lbl : s.db.find? d.lbl = none) (h_ne : d.var ≠ d.lbl)
    (h_occ : s.db.floatVarOccursInFrame d.var = false) (h_tc : s.db.isConst d.tc = true)
    (hv : IsMathToken d.var) (hl : IsLabelToken d.lbl) (ht : IsMathToken d.tc) :
    runTokens s base ["$v", d.var, "$.", d.lbl, "$f", d.tc, d.var, "$."] =
      s.withDB (·.declareDummy pos d) := by
  obtain ⟨db, tokp, charp, line, linepos, sf⟩ := s
  dsimp only at h_start h_err h_var h_lbl h_occ h_tc
  subst h_start
  have hb : ∀ t : String, t.toUTF8.toByteSlice.bytes = t.toUTF8.toList :=
    fun t => ByteSlice.bytes_toByteSlice_self t.toUTF8
  obtain ⟨c, h_c⟩ := find?_const_of_isConst h_tc
  have h_tc_ne : d.var ≠ d.tc := by
    intro h; rw [h, h_c] at h_var; cases h_var
  have h_ins0 := insert_var_fresh_eq db pos d.var h_err h_var
  have h_ins : ∀ q, db.insert q d.var .var = db.insert pos d.var .var := fun q => by
    rw [insert_var_fresh_eq db q d.var h_err h_var, h_ins0]
  have h_hyp : ∀ q, (db.insert pos d.var .var).insertHyp q d.lbl false
      #[.const d.tc, .var d.var] = db.declareDummy pos d := by
    intro q
    rw [← h_ins q]
    show db.declareDummy q d = _
    rw [declareDummy_eq db q d h_err h_var h_lbl h_ne h_occ,
      declareDummy_eq db pos d h_err h_var h_lbl h_ne h_occ]
  have h_ftc : (db.insert pos d.var .var).find? d.tc = some (.const c) := by
    rw [h_ins0]
    simp only [DB.find?, Std.HashMap.getElem?_insert, beq_iff_eq, h_tc_ne, if_false]
    exact h_c
  have h_fvar : (db.insert pos d.var .var).find? d.var = some (.var d.var) := by
    rw [h_ins0]
    simp [DB.find?]
  have h_act1 : (db.insert pos d.var .var).isActiveVar d.var = true := by
    refine isActiveVar_of_mem (n := db.scopes.size) (by simp [DB.isVar, h_fvar]) ?_
    rw [h_ins0]
    simp
  have h_err1 : (db.insert pos d.var .var).error? = none := by rw [h_ins0]; exact h_err
  generalize db.insert pos d.var .var = db1 at h_ins h_hyp h_ftc h_fvar h_act1 h_err1
  have h_err2 : (db.declareDummy pos d).error? = none := by
    rw [declareDummy_eq db pos d h_err h_var h_lbl h_ne h_occ]; exact h_err
  -- `$v`
  refine runTokens_cons_step ⟨db, .var false, charp, line, linepos, sf⟩
    (feedToken_start_v _ _ rfl _ (hb _)) h_err ?_
  -- `d`
  refine runTokens_cons_step ⟨db1, .var true, charp, line, linepos, sf⟩
    ((feedToken_var_sym _ _ false rfl d.var hv _ (hb _)).trans (by rw [h_ins])) h_err1 ?_
  -- `$.`
  refine runTokens_cons_step ⟨db1, .start, charp, line, linepos, sf⟩
    (feedToken_var_dot _ _ rfl _ (hb _)) h_err1 ?_
  -- `lbl`
  refine runTokens_cons_step _ (feedToken_start_label _ _ rfl d.lbl hl _ (hb _)) h_err1 ?_
  -- `$f`
  refine runTokens_cons_step _ (feedToken_label_f _ _ _ _ rfl _ (hb _)) h_err1 ?_
  -- `tc`
  refine runTokens_cons_step _
    (feedToken_math_const _ _ _ _ rfl d.tc c ht h_ftc _ (hb _)) h_err1 ?_
  -- `d`
  refine runTokens_cons_step _
    (feedToken_math_var _ _ _ _ rfl d.var d.var hv h_fvar h_act1 _ (hb _)) h_err1 ?_
  -- `$.`
  refine runTokens_cons_step ⟨db.declareDummy pos d, .start, charp, line, linepos, sf⟩
    ((feedToken_math_dot _ _ _ _ _ rfl _ (hb _)).trans
      ((feedTokens_float_eq _ _ _ _ _ (by rw [h_hyp]; exact h_err2)).trans
        (by rw [h_hyp]))) h_err2 ?_
  rfl

/-! ## The dummies one by one -/

/-- The declarations of the dummies `ds`, one after the other, from a state between statements. -/
theorem runTokens_foldl_declareDummy (pos : Pos) :
    ∀ (ds : List DummyDecl) (s : ParserState) (base : Nat),
      s.tokp = .start → s.db.error? = none →
      (∀ d ∈ ds, s.db.find? d.var = none) → (∀ d ∈ ds, s.db.find? d.lbl = none) →
      (ds.map (·.var) ++ ds.map (·.lbl)).Nodup →
      (∀ d ∈ ds, s.db.floatVarOccursInFrame d.var = false) →
      (∀ d ∈ ds, s.db.isConst d.tc = true) →
      (∀ d ∈ ds, IsMathToken d.var) → (∀ d ∈ ds, IsLabelToken d.lbl) →
      (∀ d ∈ ds, IsMathToken d.tc) →
      runTokens s base (ds.flatMap fun d => ["$v", d.var, "$.", d.lbl, "$f", d.tc, d.var, "$."]) =
        s.withDB (fun db => ds.foldl (fun db d => db.declareDummy pos d) db)
  | [], s, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | d :: ds, s, base, h_start, h_err, h_var, h_lbl, h_nd, h_occ, h_tc, hv, hl, ht => by
      obtain ⟨h_ne, h_rest, h_nd'⟩ := nodup_dummy_cons h_nd
      have h_var_d := h_var d (List.mem_cons_self ..)
      have h_lbl_d := h_lbl d (List.mem_cons_self ..)
      have h_occ_d := h_occ d (List.mem_cons_self ..)
      have h_find := declareDummy_find? s.db pos d h_err h_var_d h_lbl_d h_ne h_occ_d
      have h_eq := declareDummy_eq s.db pos d h_err h_var_d h_lbl_d h_ne h_occ_d
      have h_err1 : (s.db.declareDummy pos d).error? = none := by rw [h_eq]; exact h_err
      have h_var1 : ∀ e ∈ ds, (s.db.declareDummy pos d).find? e.var = none := by
        intro e he
        obtain ⟨h1, h2, _, _⟩ := h_rest e he
        rw [h_find, if_neg (Ne.symm h2), if_neg (Ne.symm h1)]
        exact h_var e (List.mem_cons_of_mem _ he)
      have h_lbl1 : ∀ e ∈ ds, (s.db.declareDummy pos d).find? e.lbl = none := by
        intro e he
        obtain ⟨_, _, h3, h4⟩ := h_rest e he
        rw [h_find, if_neg (Ne.symm h4), if_neg (Ne.symm h3)]
        exact h_lbl e (List.mem_cons_of_mem _ he)
      have h_occ1 :
          ∀ e ∈ ds, (s.db.declareDummy pos d).floatVarOccursInFrame e.var = false := by
        intro e he
        exact declareDummy_floatVarOccursInFrame s.db pos d h_err h_var_d h_lbl_d h_ne h_occ_d
          e.var (Ne.symm (h_rest e he).1) (h_occ e (List.mem_cons_of_mem _ he))
      have h_mono1 : ∀ l o, s.db.find? l = some o →
          (s.db.declareDummy pos d).find? l = some o := by
        intro l o h_l
        have h1 : d.lbl ≠ l := by
          intro h; rw [← h, h_lbl_d] at h_l; cases h_l
        have h2 : d.var ≠ l := by
          intro h; rw [← h, h_var_d] at h_l; cases h_l
        rw [h_find, if_neg h1, if_neg h2]
        exact h_l
      have h_tc1 : ∀ e ∈ ds, (s.db.declareDummy pos d).isConst e.tc = true :=
        fun e he => isConst_of_find?_mono h_mono1 (h_tc e (List.mem_cons_of_mem _ he))
      have h_one := runTokens_declareDummy s pos d base h_start h_err h_var_d h_lbl_d h_ne h_occ_d
        (h_tc d (List.mem_cons_self ..)) (hv d (List.mem_cons_self ..))
        (hl d (List.mem_cons_self ..)) (ht d (List.mem_cons_self ..))
      rw [List.flatMap_cons]
      obtain ⟨b, hb⟩ := runTokens_append_ok s base _ _ (by rw [h_one]; exact h_err1)
      rw [hb, h_one, runTokens_foldl_declareDummy pos ds (s.withDB (·.declareDummy pos d)) b
        h_start h_err1 h_var1 h_lbl1 h_nd' h_occ1 h_tc1
        (fun e he => hv e (List.mem_cons_of_mem _ he))
        (fun e he => hl e (List.mem_cons_of_mem _ he))
        (fun e he => ht e (List.mem_cons_of_mem _ he))]
      rfl

/-! ## The `$d` statements -/

/-- `$d v w $.` for two active variables `v < w`, from a state between statements: the pair
`(v, w)` is recorded in the active frame. -/
theorem runTokens_dj (s : ParserState) (p : Verify.DJ) (base : Nat)
    (h_start : s.tokp = .start) (h_err : s.db.error? = none) (h_lt : p.1 < p.2)
    (h1 : s.db.isActiveVar p.1 = true) (h2 : s.db.isActiveVar p.2 = true)
    (ht1 : IsMathToken p.1) (ht2 : IsMathToken p.2) :
    runTokens s base ["$d", p.1, p.2, "$."] = s.withDB (·.withDJ (·.push p)) := by
  obtain ⟨db, tokp, charp, line, linepos, sf⟩ := s
  dsimp only at h_start h_err h1 h2
  subst h_start
  have hb : ∀ t : String, t.toUTF8.toByteSlice.bytes = t.toUTF8.toList :=
    fun t => ByteSlice.bytes_toByteSlice_self t.toUTF8
  have h_err' : (db.withDJ (·.push p)).error? = none := h_err
  refine runTokens_cons_step ⟨db, .djvars #[], charp, line, linepos, sf⟩
    (feedToken_start_d _ _ rfl _ (hb _)) h_err ?_
  refine runTokens_cons_step ⟨db, .djvars #[p.1], charp, line, linepos, sf⟩
    ((feedToken_djvars_sym _ _ _ rfl p.1 ht1 _ (hb _)).trans (djvars_loop_first _ _ _ h1))
    h_err ?_
  refine runTokens_cons_step
    ⟨db.withDJ (·.push p), .djvars #[p.1, p.2], charp, line, linepos, sf⟩
    ((feedToken_djvars_sym _ _ _ rfl p.2 ht2 _ (hb _)).trans
      (djvars_loop_second _ _ _ _ h2 h_lt)) h_err' ?_
  refine runTokens_cons_step ⟨db.withDJ (·.push p), .start, charp, line, linepos, sf⟩
    (feedToken_djvars_dot _ _ _ rfl (by simp) _ (hb _)) h_err' ?_
  rfl

/-- The `$d` statements of the pairs `L`, one after the other, from a state between statements. -/
theorem runTokens_djs :
    ∀ (L : List Verify.DJ) (s : ParserState) (base : Nat),
      s.tokp = .start → s.db.error? = none →
      (∀ p ∈ L, p.1 < p.2 ∧ s.db.isActiveVar p.1 = true ∧ s.db.isActiveVar p.2 = true ∧
        IsMathToken p.1 ∧ IsMathToken p.2) →
      runTokens s base (L.flatMap fun p => ["$d", p.1, p.2, "$."]) =
        s.withDB (·.withDJ (· ++ L.toArray))
  | [], s, _, _, _, _ => by
      show s = _
      simp [ParserState.withDB, DB.withDJ, DB.withFrame]
  | p :: L, s, base, h_start, h_err, h_L => by
      obtain ⟨h_lt, h1, h2, ht1, ht2⟩ := h_L p (List.mem_cons_self ..)
      have h_one := runTokens_dj s p base h_start h_err h_lt h1 h2 ht1 ht2
      rw [List.flatMap_cons]
      obtain ⟨b, hb⟩ := runTokens_append_ok s base _ _ (by rw [h_one]; exact h_err)
      rw [hb, h_one, runTokens_djs L (s.withDB (·.withDJ (·.push p))) b h_start h_err
        (fun q hq => h_L q (List.mem_cons_of_mem _ hq))]
      simp [ParserState.withDB, DB.withDJ, DB.withFrame]

/-! ## The declarations -/

/-- The tokens `declTokens` that declare fresh dummy variables, fed one by one from a state between
statements, take it to the state that `Verify.DB.declareDummies` describes, for every position
`pos`: on these successful paths the database does not depend on positions. -/
theorem runTokens_declTokens (s : ParserState) (base : Nat) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_inv : ParserOps.ParserStateInv s) (h_keys : KeysAreTokens s.db)
    (h_act : FloatVarsActive s.db) (h_start : s.tokp = .start) (h_err : s.db.error? = none)
    (h_fresh : DummyDeclsFresh s.db label ds) (h_var : ∀ d ∈ ds, IsMathToken d.var)
    (h_lbl : ∀ d ∈ ds, IsLabelToken d.lbl) :
    runTokens s base (declTokens (s.db.frameFloatVars s.db.frame) ds) =
      s.withDB (·.declareDummies pos ds) := by
  obtain ⟨h_wf, h_sc, _, _⟩ := h_inv
  have h_tc : ∀ d ∈ ds, IsMathToken d.tc := fun d hd => by
    obtain ⟨c, hc⟩ := find?_const_of_isConst (h_fresh.tc_const d hd)
    exact h_keys _ _ hc
  have h_occ : ∀ d ∈ ds, s.db.floatVarOccursInFrame d.var = false := fun d hd =>
    floatVarOccursInFrame_of_find?_none s.db h_wf h_sc.1 d.var (h_fresh.var_fresh d hd)
  have h_decl := runTokens_foldl_declareDummy pos ds s base h_start h_err h_fresh.var_fresh
    h_fresh.lbl_fresh h_fresh.nodup_names h_occ h_fresh.tc_const h_var h_lbl h_tc
  have hF := declaredDummies_foldl s.db pos label ds h_err h_wf h_sc.1 h_fresh
  generalize h_F : ds.foldl (fun db d => db.declareDummy pos d) s.db = F at hF
  have h_errF : F.error? = none := hF.error.trans h_err
  -- every name of a new `$d` pair is an active variable spelled by a math token
  have h_monoF : ∀ l o, s.db.find? l = some o → F.find? l = some o := by
    intro l o h_l
    have h_v : l ∉ ds.map (·.var) := by
      intro h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      rw [h_fresh.var_fresh d hd] at h_l
      cases h_l
    have h_b : l ∉ ds.map (·.lbl) := by
      intro h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      rw [h_fresh.lbl_fresh d hd] at h_l
      cases h_l
    rw [hF.find_of_not_mem l h_v h_b]
    exact h_l
  have h_new : ∀ v ∈ ds.map (·.var), F.isActiveVar v = true ∧ IsMathToken v := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    refine ⟨isActiveVar_of_mem (n := s.db.scopes.size) ?_ ?_, h_var d hd⟩
    · simp [DB.isVar, hF.find_var d hd]
    · rw [hF.activeVars]
      simp only [Array.toList_append, List.mem_append, List.mem_map]
      exact Or.inr ⟨d, hd, rfl⟩
  have h_old :
      ∀ w ∈ s.db.frameFloatVars s.db.frame, F.isActiveVar w = true ∧ IsMathToken w := by
    intro w hw
    have h_isVar := Metamath.WF.frameFloatVars_mem_isVar s.db s.db.frame h_sc.1 w hw
    obtain ⟨n, hn⟩ := exists_mem_activeVars_of_isActiveVar
      (isActiveVar_of_mem_frameFloatVars h_act hw h_isVar)
    refine ⟨isActiveVar_of_mem (n := n) (isVar_of_find?_mono h_monoF h_isVar) ?_, ?_⟩
    · rw [hF.activeVars]
      simp only [Array.toList_append, List.mem_append]
      exact Or.inl hn
    · obtain ⟨w', hw'⟩ := find?_var_of_isVar h_isVar
      exact h_keys _ _ hw'
  have h_vs_fresh : ∀ v ∈ ds.map (·.var), v ∉ s.db.frameFloatVars s.db.frame := by
    intro v hv h_mem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    have h_isVar := Metamath.WF.frameFloatVars_mem_isVar s.db s.db.frame h_sc.1 d.var h_mem
    simp [DB.isVar, h_fresh.var_fresh d hd] at h_isVar
  have h_vs_nd : (ds.map (·.var)).Nodup :=
    List.Nodup.sublist (List.sublist_append_left _ _) h_fresh.nodup_names
  have h_pairs : ∀ p ∈ dummyDJs (s.db.frameFloatVars s.db.frame) (ds.map (·.var)),
      p.1 < p.2 ∧ F.isActiveVar p.1 = true ∧ F.isActiveVar p.2 = true ∧
        IsMathToken p.1 ∧ IsMathToken p.2 := by
    intro p hp
    obtain ⟨v, w, rfl, hv, hw, h_ne⟩ :=
      mem_dummyDJs_canon (ds.map (·.var)) _ p h_vs_fresh h_vs_nd hp
    have h_v := h_new v hv
    have h_w : F.isActiveVar w = true ∧ IsMathToken w := by
      rcases hw with hw | hw
      · exact h_old w hw
      · exact h_new w hw
    obtain ⟨h_lt, h_cases⟩ := canonDJ_ordered h_ne
    have h_fst : F.isActiveVar (canonDJ v w).1 = true ∧ IsMathToken (canonDJ v w).1 := by
      rcases h_cases with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]; exact h_v
      · rw [h1]; exact h_w
    have h_snd : F.isActiveVar (canonDJ v w).2 = true ∧ IsMathToken (canonDJ v w).2 := by
      rcases h_cases with ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [h2]; exact h_w
      · rw [h2]; exact h_v
    exact ⟨h_lt, h_fst.1, h_snd.1, h_fst.2, h_snd.2⟩
  have h_decl' : runTokens s base
      (ds.flatMap fun d => ["$v", d.var, "$.", d.lbl, "$f", d.tc, d.var, "$."]) =
        s.withDB (fun _ => F) := by
    rw [h_decl, ← h_F]
    rfl
  unfold declTokens
  obtain ⟨b, hb⟩ := runTokens_append_ok s base _ _ (by rw [h_decl']; exact h_errF)
  rw [hb, h_decl', runTokens_djs _ (s.withDB fun _ => F) b h_start h_errF h_pairs]
  simp only [ParserState.withDB, DB.declareDummies, h_F]

end Metamath.SourceCompleteness
