import Metamath.CheckerCompleteness.Trim

/-!
# `$d` variables of stored assertions are float variables of their frames

`AssertDvVarsInFrame db` says that every `$d` pair of a stored assertion consists
of variables that have a floating hypothesis in that assertion's own frame.  The
end-of-parse runtime check `DB.assertDvVarsInFrame?` tests exactly this.  Here it
is a parser invariant: it holds at every error-free state reached by `feedToken`,
`feed` and `feedAll` from the initial state, in every mode.

Assertions are created only by `DB.insertAxiom` (`$a`) and `finishProof` (`$p`),
each with a frame produced by `DB.trimFrame'`.  A successful trim keeps a `$d`
pair only when both variables are mandatory, and keeps the `$f` of every mandatory
variable (`trimFrame'_frameDvVarsInFrame`).  The only fact about the database
this needs is that registered `$f` hypotheses have the `$f C v` shape
(`FloatHypsShaped`), which the parser checks before every `$f` insertion in every
mode.  For `$p` the trimmed frame is computed at `$=` and carried in the `.proof`
token state, so the companion `ProofDvInv` records the property for the carried
frame.  The property of an existing assertion reads only `find?`, which the
parser never shrinks or overwrites, so it survives every later step.

`DvStateInv` packages the three facts; it is preserved by every successful
`feedToken` step from an error-free state (`feedToken_maintains_dvStateInv`) and
holds initially (`initState_dvStateInv`).  Consequently an error-free
`checkBytesCore` run always passes the `$d` part of the post-check
(`checkBytesCore_assertDvVarsInFrame?_eq_true`).
-/

set_option autoImplicit false

namespace Metamath.AssertDv

open Metamath.Verify
open Metamath.WF
open Metamath.ParserOps (ParserStateInv)
open Metamath.StoredStatementSoundness.Runtime (trimVars)

/-! ## The invariant -/

/-- Every `$d` pair of `fr` consists of float variables of `fr`. -/
def FrameDvVarsInFrame (db : DB) (fr : Verify.Frame) : Prop :=
  ∀ v w, (v, w) ∈ fr.dj.toList →
    v ∈ db.frameFloatVars fr ∧ w ∈ db.frameFloatVars fr

/-- Every stored assertion's `$d` variables are float variables of its frame. -/
def AssertDvVarsInFrame (db : DB) : Prop :=
  ∀ lbl f fr name, db.find? lbl = some (.assert f fr name) →
    ∀ v w, (v, w) ∈ fr.dj.toList → v ∈ db.frameFloatVars fr ∧ w ∈ db.frameFloatVars fr

/-! ## Registry growth preserves the property -/

/-- `frameFloatVars` only reads `find?`, so a registry that only grows keeps
every float variable of a frame. -/
theorem frameFloatVars_mono {db db' : DB}
    (h_mono : ∀ n o, db.find? n = some o → db'.find? n = some o)
    (fr : Verify.Frame) {v : String} (h : v ∈ db.frameFloatVars fr) :
    v ∈ db'.frameFloatVars fr := by
  obtain ⟨lbl, f, lbl', h_mem, h_find, h_shape, h_f1⟩ :=
    (frameFloatVars_mem_iff' db fr v).1 h
  exact (frameFloatVars_mem_iff' db' fr v).2
    ⟨lbl, f, lbl', h_mem, h_mono lbl _ h_find, h_shape, h_f1⟩

theorem frameDvVarsInFrame_mono {db db' : DB}
    (h_mono : ∀ n o, db.find? n = some o → db'.find? n = some o)
    {fr : Verify.Frame} (h : FrameDvVarsInFrame db fr) : FrameDvVarsInFrame db' fr := by
  intro v w h_mem
  obtain ⟨hv, hw⟩ := h v w h_mem
  exact ⟨frameFloatVars_mono h_mono fr hv, frameFloatVars_mono h_mono fr hw⟩

/-- `frameFloatVars` depends on the database only through `find?`. -/
theorem frameFloatVars_congr {db db' : DB} (h : ∀ n, db'.find? n = db.find? n)
    (fr : Verify.Frame) : db'.frameFloatVars fr = db.frameFloatVars fr := by
  unfold DB.frameFloatVars
  simp only [h]

/-- The invariant depends on the database only through `find?`. -/
theorem assertDvVarsInFrame_of_find?_eq {db db' : DB}
    (h : ∀ n, db'.find? n = db.find? n) (h_dv : AssertDvVarsInFrame db) :
    AssertDvVarsInFrame db' := by
  intro lbl f fr name h_find v w h_mem
  rw [frameFloatVars_congr h fr]
  exact h_dv lbl f fr name (by rw [← h lbl]; exact h_find) v w h_mem

/-! ## Registered `$f` hypotheses are float-shaped -/

/-- Every registered floating hypothesis has the `$f C v` shape.  Unlike
`WellFormedDB`, this does not depend on `allowDuplicateFloat`. -/
def FloatHypsShaped (db : DB) : Prop :=
  ∀ l f n, db.find? l = some (.hyp false f n) → f.isFloatShape = true

theorem floatHypsShaped_of_objects_eq {db db' : DB} (h_eq : db'.objects = db.objects)
    (h : FloatHypsShaped db) : FloatHypsShaped db' := by
  intro l f n h_find
  exact h l f n (by
    show db.objects[l]? = _
    rw [← h_eq]
    exact h_find)

/-! ## A successful trim yields the property -/

/-- The frame produced by a successful `trimFrame'` keeps a `$d` pair only when
both variables are mandatory, and keeps the `$f` of each mandatory variable, so
its `$d` variables are float variables of the trimmed frame itself. -/
theorem trimFrame'_frameDvVarsInFrame (db : DB) (fmla : Verify.Formula) (fr : Verify.Frame)
    (h_fs : FloatHypsShaped db) (h_trim : db.trimFrame' fmla = .ok fr) :
    FrameDvVarsInFrame db fr := by
  intro v w h_mem
  have h_pair : db.trimFrame fmla = (true, fr) := ParserOps.trimFrame'_ok_iff.mp h_trim
  have h_fr : fr = (db.trimFrame fmla).2 := by rw [h_pair]
  have h_hyps : fr.hyps = DB.trimFrameHyps db (trimVars db fmla) db.frame.hyps := by
    rw [h_fr, StoredStatementSoundness.Runtime.trimFrame_hyps_eq]
  have h_dj : (v, w) ∈ db.frame.dj.toList.filter
      (fun p => (trimVars db fmla).contains p.1 && (trimVars db fmla).contains p.2) := by
    rw [← StoredStatementSoundness.Runtime.trimFrame_dj_toList_eq_filter, ← h_fr]
    exact h_mem
  have h_c := (List.mem_filter.mp h_dj).2
  simp only [Bool.and_eq_true] at h_c
  have h_ok : CheckerCompleteness.trimOk (trimVars db fmla)
      (CheckerCompleteness.trimVarsWithF db (trimVars db fmla)) = true := by
    rw [← CheckerCompleteness.trimFrame_fst_eq, h_pair]
  rw [CheckerCompleteness.trimOk_eq_true_iff] at h_ok
  -- every mandatory variable has a `$f` in the active frame, and the trim keeps it
  have key : ∀ u, (trimVars db fmla).contains u = true → u ∈ db.frameFloatVars fr := by
    intro u hu
    have h_cov := h_ok u hu
    rw [CheckerCompleteness.trimVarsWithF_eq_collect] at h_cov
    obtain ⟨lbl, f, lbl', h_lbl, h_find, h_val⟩ :=
      ParserOps.collectFloatVarsFromHypsList_contains_implies db _ _ u h_cov
    have h_shape := h_fs lbl f lbl' h_find
    obtain ⟨_, c, v', _, h1⟩ := wellFormedFloat_of_isFloatShape h_shape
    have h_v' : v' = u := by
      have h_value : (f[1]!).value = v' := by rw [h1]; rfl
      exact h_value.symm.trans h_val
    subst h_v'
    have h_kept : lbl ∈ fr.hyps.toList := by
      rw [h_hyps, StoredStatementSoundness.Runtime.trimFrameHyps_mem_iff]
      obtain ⟨i, hi, h_at⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp h_lbl)
      refine ⟨i, hi, h_at, ?_⟩
      unfold DB.trimFrameKeep
      rw [h_at, h_find]
      simp only [h1, Sym.value]
      exact hu
    exact (frameFloatVars_mem_iff' db fr v').2 ⟨lbl, f, lbl', h_kept, h_find, h_shape, h1⟩
  exact ⟨key v h_c.1, key w h_c.2⟩

/-! ## The token-state companion

A `$p` statement stores the frame trimmed at its `$=`, which the `.proof` token
state carries until the closing `$.`.  `ProofDvInv` records the property for
that carried frame, looking through comment and include administration exactly
as the parser suspends and resumes the mode. -/

/-- The `$d` property of the frame carried by a pending `$p` proof. -/
def ProofDvInv (db : DB) : TokenParser → Prop
  | .proof pr => FrameDvVarsInFrame db pr.frame
  | .comment inner => ProofDvInv db inner
  | .includePath resume _ => ProofDvInv db resume
  | .includeClose resume _ _ => ProofDvInv db resume
  | .start => True
  | .const _ => True
  | .var _ => True
  | .djvars _ => True
  | .math _ _ => True
  | .label _ _ => True

/-- No proof mode occurs beneath the administrative wrappers. -/
def ProofModeAbsent : TokenParser → Prop
  | .proof _ => False
  | .comment inner => ProofModeAbsent inner
  | .includePath resume _ => ProofModeAbsent resume
  | .includeClose resume _ _ => ProofModeAbsent resume
  | .start => True
  | .const _ => True
  | .var _ => True
  | .djvars _ => True
  | .math _ _ => True
  | .label _ _ => True

theorem proofDvInv_mono {db db' : DB}
    (h_mono : ∀ n o, db.find? n = some o → db'.find? n = some o) :
    ∀ tp, ProofDvInv db tp → ProofDvInv db' tp := by
  intro tp
  induction tp with
  | proof pr => exact frameDvVarsInFrame_mono h_mono
  | comment inner ih => exact ih
  | includePath resume _ ih => exact ih
  | includeClose resume _ _ ih => exact ih
  | start => intro _; trivial
  | const _ => intro _; trivial
  | var _ => intro _; trivial
  | djvars _ => intro _; trivial
  | math _ _ => intro _; trivial
  | label _ _ => intro _; trivial

theorem proofDvInv_of_absent {db : DB} :
    ∀ {tp : TokenParser}, ProofModeAbsent tp → ProofDvInv db tp := by
  intro tp
  induction tp with
  | proof pr => intro h; exact h.elim
  | comment inner ih => exact ih
  | includePath resume _ ih => exact ih
  | includeClose resume _ _ ih => exact ih
  | start => intro _; trivial
  | const _ => intro _; trivial
  | var _ => intro _; trivial
  | djvars _ => intro _; trivial
  | math _ _ => intro _; trivial
  | label _ _ => intro _; trivial

/-! ### `feedToken` and the companion, mode by mode

Each lemma evaluates the companion of the *output* token state at the *input*
database; `feedToken_find?_mono` then transports it to the output database. -/

/-- The `$(` and `$[` prefixes of every non-comment mode only wrap, keep or
error on the current mode. -/
theorem feedToken_prefix_proofDvInv (db : DB) (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_nc : ∀ q, s.tokp ≠ .comment q)
    (h_pre : tk.eqArray "$(".toAscii = true ∨
      (tk.eqArray "$(".toAscii = false ∧ tk.eqArray "$[".toAscii = true))
    (h_pdv : ProofDvInv db s.tokp) :
    ProofDvInv db (s.feedToken i tk).tokp := by
  rcases h_pre with h_open | ⟨h_open, h_incl⟩
  · have h_tp : (s.feedToken i tk).tokp = .comment s.tokp := by
      unfold ParserState.feedToken
      cases h_tokp : s.tokp <;>
        first
          | exact absurd h_tokp (h_nc _)
          | simp [h_open]
    rw [h_tp]
    exact h_pdv
  · have h_tp : (s.feedToken i tk).tokp = s.tokp ∨
        (s.feedToken i tk).tokp = .includePath s.tokp (s.mkPos i) := by
      unfold ParserState.feedToken
      cases h_tokp : s.tokp <;>
        first
          | exact absurd h_tokp (h_nc _)
          | (simp only [h_open, h_incl, Bool.false_eq_true, if_false, if_true]
             split
             · exact Or.inl h_tokp
             · exact Or.inr rfl)
    rcases h_tp with h_tp | h_tp <;> rw [h_tp] <;> exact h_pdv

theorem feedToken_comment_proofDvInv (db : DB) (s : ParserState) (i : Nat) (tk : ByteSlice)
    (inner : TokenParser) (h_tokp : s.tokp = .comment inner)
    (h_pdv : ProofDvInv db inner) :
    ProofDvInv db (s.feedToken i tk).tokp := by
  have h_tp : (s.feedToken i tk).tokp = inner ∨
      (s.feedToken i tk).tokp = .comment inner := by
    unfold ParserState.feedToken
    simp only [h_tokp]
    repeat' split
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact Or.inr h_tokp
  rcases h_tp with h_tp | h_tp <;> rw [h_tp] <;> exact h_pdv

theorem label_absent (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (h : ProofModeAbsent s.tokp) : ProofModeAbsent (s.label pos tk).tokp := by
  unfold ParserState.label
  repeat' split
  all_goals first | exact h | trivial

theorem withMath_absent (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState)
    (h : ProofModeAbsent s.tokp) (hf : ∀ tk', ProofModeAbsent (f s tk').tokp) :
    ProofModeAbsent (s.withMath pos tk f).tokp := by
  unfold ParserState.withMath
  repeat' split
  all_goals first | exact h | exact hf _

theorem djvars_loop_aux_absent (arr : Array String) (s : ParserState) (pos : Pos)
    (tk : String) (i : Nat) (h : ProofModeAbsent s.tokp) :
    ProofModeAbsent (ParserState.djvars_loop_aux arr s pos tk i).tokp := by
  refine Nat.rec
    (motive := fun m => ∀ i (s : ParserState), arr.size - i = m →
      ProofModeAbsent s.tokp →
      ProofModeAbsent (ParserState.djvars_loop_aux arr s pos tk i).tokp)
    ?base ?step (arr.size - i) i s rfl h
  · intro i s hs h
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    trivial
  · intro m ih i s hs h
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        simp [hz] at hs
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    unfold ParserState.djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    split
    · exact h
    · exact ih (i + 1) _ hs' h

theorem djvars_loop_absent (arr : Array String) (s : ParserState) (pos : Pos)
    (tk : String) (h : ProofModeAbsent s.tokp) :
    ProofModeAbsent (ParserState.djvars_loop arr s pos tk).tokp := by
  unfold ParserState.djvars_loop
  split
  · exact h
  · exact djvars_loop_aux_absent arr s pos tk 0 h

/-- The declaration modes never enter proof mode. -/
theorem feedToken_decl_absent (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_mode : s.tokp = .start ∨ (∃ b, s.tokp = .const b) ∨ (∃ b, s.tokp = .var b) ∨
      (∃ arr, s.tokp = .djvars arr) ∨ (∃ pos lab, s.tokp = .label pos lab))
    (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) :
    ProofModeAbsent (s.feedToken i tk).tokp := by
  rcases h_mode with h_tokp | ⟨b, h_tokp⟩ | ⟨b, h_tokp⟩ | ⟨arr, h_tokp⟩ | ⟨pos, lab, h_tokp⟩
  · unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
    repeat' split
    all_goals
      first
        | trivial
        | exact label_absent _ _ _ (by rw [h_tokp]; trivial)
        | (show ProofModeAbsent s.tokp
           rw [h_tokp]; trivial)
  · unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
    repeat' split
    all_goals
      first
        | trivial
        | (show ProofModeAbsent s.tokp
           rw [h_tokp]; trivial)
  · unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
    repeat' split
    all_goals
      first
        | trivial
        | (show ProofModeAbsent s.tokp
           rw [h_tokp]; trivial)
  · unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
    repeat' split
    all_goals
      first
        | trivial
        | (show ProofModeAbsent s.tokp
           rw [h_tokp]; trivial)
        | exact withMath_absent _ _ _ _ (by rw [h_tokp]; trivial)
            (fun tk' => djvars_loop_absent _ _ _ _ (by rw [h_tokp]; trivial))
  · unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
    repeat' split
    all_goals
      first
        | trivial
        | (show ProofModeAbsent s.tokp
           rw [h_tokp]; trivial)

/-- A statement closed by its delimiter either stays out of proof mode or, at
`$=`, opens a proof carrying a successfully trimmed frame. -/
theorem feedTokens_proofDvInv (s : ParserState) (arr : Array Verify.Sym) (p : TokensParser)
    (h_fs : FloatHypsShaped s.db) (h_absent : ProofModeAbsent s.tokp) :
    ProofDvInv s.db (s.feedTokens arr p).tokp := by
  obtain ⟨k, pos, l⟩ := p
  unfold ParserState.feedTokens
  rw [ParserState.withAt_tokp]
  cases k with
  | thm =>
    simp only [Id.run]
    split
    · split
      · rename_i _ fr h_trim
        split
        · exact proofDvInv_of_absent h_absent
        · exact trimFrame'_frameDvVarsInFrame s.db arr fr h_fs h_trim
      · exact proofDvInv_of_absent h_absent
    · exact proofDvInv_of_absent h_absent
  | _ =>
    simp only [Id.run]
    repeat' split
    all_goals first
      | exact proofDvInv_of_absent h_absent
      | trivial

/-- Symbol accumulation stays in math mode or errors in place; the delimiter
dispatches to `feedTokens`. -/
theorem feedToken_math_proofDvInv (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser) (h_tokp : s.tokp = .math arr p)
    (h_fs : FloatHypsShaped s.db)
    (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) :
    ProofDvInv s.db (s.feedToken i tk).tokp := by
  have h_absent : ProofModeAbsent s.tokp := by rw [h_tokp]; trivial
  by_cases h_delim : tk.eqArray p.k.delim = true
  · have h_eq : s.feedToken i tk = s.feedTokens arr p := by
      simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_delim]
    rw [h_eq]
    exact feedTokens_proofDvInv s arr p h_fs h_absent
  · have h_delim' : tk.eqArray p.k.delim = false := by simpa using h_delim
    unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, h_delim', Bool.false_eq_true, if_false]
    apply proofDvInv_of_absent
    apply withMath_absent _ _ _ _ h_absent
    intro tk'
    simp only [Id.run]
    repeat' split
    all_goals trivial

/-- Include administration keeps, restores or re-wraps the suspended mode. -/
theorem feedToken_include_proofDvInv (db : DB) (s : ParserState) (i : Nat) (tk : ByteSlice)
    (resume : TokenParser)
    (h_mode : (∃ q, s.tokp = .includePath resume q) ∨
      (∃ q path, s.tokp = .includeClose resume q path))
    (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false)
    (h_pdv : ProofDvInv db resume) :
    ProofDvInv db (s.feedToken i tk).tokp := by
  rcases h_mode with ⟨q, h_tokp⟩ | ⟨q, path, h_tokp⟩
  · unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
    repeat' split
    all_goals
      first
        | exact h_pdv
        | (show ProofDvInv db s.tokp
           rw [h_tokp]; exact h_pdv)
  · unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
    repeat' split
    all_goals
      first
        | exact h_pdv
        | (show ProofDvInv db s.tokp
           rw [h_tokp]; exact h_pdv)

/-- Proof steps keep the carried frame; the closing `$.` leaves proof mode. -/
theorem feedToken_proof_proofDvInv (s : ParserState) (i : Nat) (tk : ByteSlice)
    (pr : ProofState) (h_tokp : s.tokp = .proof pr)
    (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false)
    (h_pdv : FrameDvVarsInFrame s.db pr.frame) :
    ProofDvInv s.db (s.feedToken i tk).tokp := by
  by_cases h_end : tk.eqArray "$.".toAscii = true
  · have h_eq : s.feedToken i tk = ({ s with tokp := default } : ParserState).finishProof pr := by
      simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_end]
    rw [h_eq, ParserOps.finishProof_tokp_start]
    trivial
  · have h_end' : tk.eqArray "$.".toAscii = false := by simpa using h_end
    have h_eq : s.feedToken i tk = ({ s with tokp := default } : ParserState).feedProof tk pr := by
      simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_end']
    rw [h_eq]
    unfold ParserState.feedProof
    rw [ParserState.withAt_tokp]
    cases h_go : ParserState.feedProof.go ({ s with tokp := default } : ParserState) tk pr with
    | ok pr' =>
        have h_core := ParserOps.feedProof_go_ok_preserves_core _ tk pr pr' h_go
        dsimp only
        show FrameDvVarsInFrame s.db pr'.frame
        rw [h_core.2]
        exact h_pdv
    | error err =>
        dsimp only
        trivial

/-- The companion of the output token state already holds at the input
database. -/
theorem feedToken_proofDvInv_pre (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_fs : FloatHypsShaped s.db) (h_pdv : ProofDvInv s.db s.tokp) :
    ProofDvInv s.db (s.feedToken i tk).tokp := by
  by_cases h_c : ∃ q, s.tokp = .comment q
  · obtain ⟨inner, h_tokp⟩ := h_c
    rw [h_tokp] at h_pdv
    exact feedToken_comment_proofDvInv s.db s i tk inner h_tokp h_pdv
  have h_nc : ∀ q, s.tokp ≠ .comment q := fun q h => h_c ⟨q, h⟩
  by_cases h_open : tk.eqArray "$(".toAscii = true
  · exact feedToken_prefix_proofDvInv s.db s i tk h_nc (Or.inl h_open) h_pdv
  have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
  by_cases h_incl : tk.eqArray "$[".toAscii = true
  · exact feedToken_prefix_proofDvInv s.db s i tk h_nc (Or.inr ⟨h_open', h_incl⟩) h_pdv
  have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
  cases h_tokp : s.tokp with
  | comment inner => exact absurd h_tokp (h_nc inner)
  | start =>
      exact proofDvInv_of_absent
        (feedToken_decl_absent s i tk (Or.inl h_tokp) h_open' h_incl')
  | const b =>
      exact proofDvInv_of_absent
        (feedToken_decl_absent s i tk (Or.inr (Or.inl ⟨b, h_tokp⟩)) h_open' h_incl')
  | var b =>
      exact proofDvInv_of_absent
        (feedToken_decl_absent s i tk (Or.inr (Or.inr (Or.inl ⟨b, h_tokp⟩))) h_open' h_incl')
  | djvars arr =>
      exact proofDvInv_of_absent
        (feedToken_decl_absent s i tk (Or.inr (Or.inr (Or.inr (Or.inl ⟨arr, h_tokp⟩))))
          h_open' h_incl')
  | label pos lab =>
      exact proofDvInv_of_absent
        (feedToken_decl_absent s i tk (Or.inr (Or.inr (Or.inr (Or.inr ⟨pos, lab, h_tokp⟩))))
          h_open' h_incl')
  | math arr p => exact feedToken_math_proofDvInv s i tk arr p h_tokp h_fs h_open' h_incl'
  | includePath resume q =>
      rw [h_tokp] at h_pdv
      exact feedToken_include_proofDvInv s.db s i tk resume (Or.inl ⟨q, h_tokp⟩)
        h_open' h_incl' h_pdv
  | includeClose resume q path =>
      rw [h_tokp] at h_pdv
      exact feedToken_include_proofDvInv s.db s i tk resume (Or.inr ⟨q, path, h_tokp⟩)
        h_open' h_incl' h_pdv
  | proof pr =>
      rw [h_tokp] at h_pdv
      exact feedToken_proof_proofDvInv s i tk pr h_tokp h_open' h_incl' h_pdv

/-- **Companion maintenance.**  `feedToken` keeps the `$d` property of the frame
carried by a pending `$p` proof.  No success hypothesis is needed: error paths
keep or reset the token state, and the carried frame is only ever a successful
trim or the unchanged frame of the previous proof state. -/
theorem feedToken_maintains_proofDvInv (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_fs : FloatHypsShaped s.db) (h_pdv : ProofDvInv s.db s.tokp) :
    ProofDvInv (s.feedToken i tk).db (s.feedToken i tk).tokp :=
  proofDvInv_mono (fun n o h => PrefixProvability.Checker.feedToken_find?_mono s i tk n o h) _
    (feedToken_proofDvInv_pre s i tk h_fs h_pdv)

/-! ## Every step registers `$f` hypotheses only after the shape check -/

/-- `insert` either leaves the registry alone or writes `obj l` at `l`. -/
theorem insert_objects_cases (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).objects = db.objects ∨
      (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  unfold DB.insert
  cases obj l <;> dsimp only <;> repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl

theorem floatHypsShaped_insert {db : DB} (pos : Pos) (l : String) (obj : String → Object)
    (h : FloatHypsShaped db)
    (h_obj : ∀ f m, obj l = .hyp false f m → f.isFloatShape = true) :
    FloatHypsShaped (db.insert pos l obj) := by
  rcases insert_objects_cases db pos l obj with h_eq | h_eq
  · exact floatHypsShaped_of_objects_eq h_eq h
  · intro n f m h_find
    have h_find' : (db.objects.insert l (obj l))[n]? = some (.hyp false f m) := by
      rw [← h_eq]
      exact h_find
    rw [Std.HashMap.getElem?_insert] at h_find'
    split at h_find'
    · exact h_obj f m (Option.some.inj h_find')
    · exact h n f m h_find'

/-- The `$f` shape gate is part of the success of `insertHypChecks`. -/
theorem insertHypChecks_float_shape (db : DB) (pos : Pos) (f : Verify.Formula)
    (h_ok : (db.insertHypChecks pos false f).error = false) : f.isFloatShape = true := by
  by_contra h_shape
  have h_shape' : f.isFloatShape = false := by simpa using h_shape
  revert h_ok
  unfold DB.insertHypChecks
  simp only [h_shape', Bool.false_eq_true, if_false]
  repeat' split
  all_goals simp_all [DB.error, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]

theorem floatHypsShaped_insertHyp {db : DB} (pos : Pos) (l : String) (ess : Bool)
    (f : Verify.Formula) (h : FloatHypsShaped db) :
    FloatHypsShaped (db.insertHyp pos l ess f) := by
  have h1 : FloatHypsShaped (db.insertHypChecks pos ess f) :=
    floatHypsShaped_of_objects_eq (ParserOps.insertHypChecks_objects db pos ess f) h
  simp only [DB.insertHyp]
  split
  · exact h1
  · rename_i h_chk
    have h_chk' : (db.insertHypChecks pos ess f).error = false := by simpa using h_chk
    have h2 : FloatHypsShaped ((db.insertHypChecks pos ess f).insert pos l (.hyp ess f)) := by
      apply floatHypsShaped_insert pos l _ h1
      intro g m h_eq
      injection h_eq with h_ess h_g _
      subst h_ess
      subst h_g
      exact insertHypChecks_float_shape db pos _ h_chk'
    split
    · exact h2
    · exact floatHypsShaped_of_objects_eq rfl h2

theorem floatHypsShaped_insertAxiom {db : DB} (pos : Pos) (l : String) (fmla : Verify.Formula)
    (h : FloatHypsShaped db) : FloatHypsShaped (db.insertAxiom pos l fmla) := by
  have h_nh : ∀ (fr : Verify.Frame) f m,
      (Object.assert fmla fr : String → Object) l = .hyp false f m → f.isFloatShape = true := by
    intro fr f m h_eq
    cases h_eq
  simp only [DB.insertAxiom]
  repeat' split
  all_goals first
    | exact h
    | exact floatHypsShaped_of_objects_eq rfl h
    | exact floatHypsShaped_insert _ _ _ h (h_nh _)

theorem floatHypsShaped_recordIncomplete {db : DB} (b : Bool) (l : String)
    (h : FloatHypsShaped db) : FloatHypsShaped (db.recordIncomplete b l) := by
  unfold DB.recordIncomplete
  split
  · exact floatHypsShaped_of_objects_eq rfl h
  · exact h

theorem floatHypsShaped_finishProof (s : ParserState) (pr : ProofState)
    (h : FloatHypsShaped s.db) : FloatHypsShaped (s.finishProof pr).db := by
  cases pr with
  | mk pos l fmla fr heap stack ptp inc =>
      unfold ParserState.finishProof
      apply floatHypsShaped_of_objects_eq (PrefixProvability.Checker.withAt_objects _ _)
      simp only [Id.run]
      repeat' split
      all_goals first
        | exact h
        | exact floatHypsShaped_recordIncomplete _ _
            (floatHypsShaped_insert _ _ _ h (fun f m h_eq => by cases h_eq))

theorem floatHypsShaped_feedTokens (s : ParserState) (arr : Array Verify.Sym)
    (p : TokensParser) (h : FloatHypsShaped s.db) :
    FloatHypsShaped (s.feedTokens arr p).db := by
  obtain ⟨k, pos, l⟩ := p
  unfold ParserState.feedTokens
  apply floatHypsShaped_of_objects_eq (PrefixProvability.Checker.withAt_objects _ _)
  cases k <;> simp only [Id.run] <;> repeat' split
  all_goals first
    | exact h
    | exact floatHypsShaped_insertHyp _ _ _ _ h
    | exact floatHypsShaped_insertAxiom _ _ _ h

/-- Every `feedToken` step, in every mode and on every path, registers a `$f`
hypothesis only after its shape check. -/
theorem feedToken_maintains_floatHypsShaped (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h : FloatHypsShaped s.db) : FloatHypsShaped (s.feedToken i tk).db := by
  have h_of_objects : ∀ s' : ParserState, s'.db.objects = s.db.objects →
      FloatHypsShaped s'.db := fun s' h_eq => floatHypsShaped_of_objects_eq h_eq h
  cases h_tokp : s.tokp with
  | comment q =>
      exact h_of_objects _ (PrefixProvability.Checker.feedToken_comment_objects s i tk q h_tokp)
  | start =>
      exact h_of_objects _ (PrefixProvability.Checker.feedToken_start_objects s i tk h_tokp)
  | label q lab =>
      exact h_of_objects _
        (PrefixProvability.Checker.feedToken_label_objects s i tk q lab h_tokp)
  | includePath r q =>
      exact h_of_objects _
        (PrefixProvability.Checker.feedToken_includePath_objects s i tk r q h_tokp)
  | includeClose r q pth =>
      exact h_of_objects _
        (PrefixProvability.Checker.feedToken_includeClose_objects s i tk r q pth h_tokp)
  | djvars arr =>
      exact h_of_objects _ (PrefixProvability.Checker.feedToken_djvars_objects s i tk arr h_tokp)
  | const seen =>
      unfold ParserState.feedToken ParserState.sym ParserState.withMath
      simp only [h_tokp]
      repeat' split
      all_goals first
        | exact h
        | exact floatHypsShaped_insert _ _ _ h (fun f m h_eq => by cases h_eq)
  | var seen =>
      unfold ParserState.feedToken ParserState.sym ParserState.withMath
      simp only [h_tokp]
      repeat' split
      all_goals first
        | exact h
        | exact floatHypsShaped_insert _ _ _ h (fun f m h_eq => by cases h_eq)
  | math arr p =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact h_of_objects _
          (PrefixProvability.Checker.feedToken_open_objects s i tk h_nc h_open)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact h_of_objects _
            (PrefixProvability.Checker.feedToken_incl_objects s i tk h_nc h_open' h_incl)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_delim : tk.eqArray p.k.delim = true
          · have h_eq : s.feedToken i tk = s.feedTokens arr p := by
              simp [ParserState.feedToken, h_tokp, h_open', h_incl', h_delim]
            rw [h_eq]
            exact floatHypsShaped_feedTokens s arr p h
          · have h_delim' : tk.eqArray p.k.delim = false := by simpa using h_delim
            exact h_of_objects _
              (PrefixProvability.Checker.feedToken_math_nondelim_objects s i tk arr p
                h_tokp h_delim')
  | proof pr =>
      have h_nc : ∀ q, s.tokp ≠ .comment q := by simp [h_tokp]
      by_cases h_open : tk.eqArray "$(".toAscii = true
      · exact h_of_objects _
          (PrefixProvability.Checker.feedToken_open_objects s i tk h_nc h_open)
      · have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
        by_cases h_incl : tk.eqArray "$[".toAscii = true
        · exact h_of_objects _
            (PrefixProvability.Checker.feedToken_incl_objects s i tk h_nc h_open' h_incl)
        · have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
          by_cases h_dot : tk.eqArray "$.".toAscii = true
          · have h_eq : s.feedToken i tk
                = ({ s with tokp := default } : ParserState).finishProof pr := by
              simp [ParserState.feedToken, h_tokp, h_open', h_incl', h_dot]
            rw [h_eq]
            exact floatHypsShaped_finishProof _ pr h
          · have h_dot' : tk.eqArray "$.".toAscii = false := by simpa using h_dot
            exact h_of_objects _
              (PrefixProvability.Checker.feedToken_proof_nondot_objects s i tk pr h_tokp h_dot')

/-! ## `feedToken` preserves the invariant -/

/-- **One parser step.**  Old assertions keep the property because `find?` only
grows; an assertion created by the step is either a `$a`, whose frame is a
successful trim of the current database, or a `$p`, whose frame is the one the
companion carries. -/
theorem feedToken_maintains_assertDvVarsInFrame_of_floatHypsShaped
    (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_fs : FloatHypsShaped s.db)
    (h_dv : AssertDvVarsInFrame s.db)
    (h_pdv : ProofDvInv s.db s.tokp)
    (h_no_err : s.db.error? = none)
    (h_success : (s.feedToken i tk).db.error? = none) :
    AssertDvVarsInFrame (s.feedToken i tk).db := by
  have h_mono : ∀ n o, s.db.find? n = some o → (s.feedToken i tk).db.find? n = some o :=
    fun n o h => PrefixProvability.Checker.feedToken_find?_mono s i tk n o h
  intro lbl f fr name h_find
  show FrameDvVarsInFrame _ fr
  cases h_old : s.db.find? lbl with
  | some o =>
      have h_o := h_mono lbl o h_old
      rw [h_find] at h_o
      cases h_o
      exact frameDvVarsInFrame_mono h_mono (h_dv lbl f fr name h_old)
  | none =>
      rcases PrefixProvability.Checker.feedToken_new_assert_classified s i tk lbl f fr name
          h_old h_success h_find with ⟨arr, p, h_ax⟩ | ⟨pr, h_pf⟩
      · -- `$a`: the stored frame is a successful trim of `s.db`
        have h_head := PrefixProvability.Checker.axiomFinishEvent_success_hasConstHead
          s i tk arr p h_ax
        have h_eq := PrefixProvability.Checker.axiomFinishEvent_inserts_axiom
          s i tk arr p h_ax h_head
        rw [h_eq] at h_find
        obtain ⟨_, _, _, _, h_trim⟩ := ParserOps.insertAxiom_new_assert_origin
          s.db p.pos p.label arr lbl f fr name h_no_err h_old h_find
        exact frameDvVarsInFrame_mono h_mono
          (trimFrame'_frameDvVarsInFrame s.db arr fr h_fs h_trim)
      · -- `$p`: the stored frame is the one carried by the proof state
        have h_eq := PrefixProvability.Checker.finishProofEvent_feedToken_eq s i tk pr h_pf
        have h_ok : (({ s with tokp := default } : ParserState).finishProof pr).db.error? = none := by
          rw [← h_eq]
          exact h_pf.2.2.2.2
        have h_ins := (ParserOps.finishProof_success_insert _ pr h_ok).1
        have h_find' : (s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame)).find? lbl =
            some (.assert f fr name) := by
          rw [h_eq, h_ins, DB.recordIncomplete_find?] at h_find
          exact h_find
        obtain ⟨_, h_obj⟩ := ParserOps.insert_new_assert_origin s.db pr.pos pr.label _ lbl
          f fr name h_old h_find'
        have h_fr : pr.frame = fr := by
          injection h_obj
        have h_carried : FrameDvVarsInFrame s.db pr.frame := by
          have h := h_pdv
          rw [h_pf.1] at h
          exact h
        rw [← h_fr]
        exact frameDvVarsInFrame_mono h_mono h_carried

/-! ## The parser loop -/

/-- The `$d` invariant, its token-state companion, and the `$f` shape fact they
rely on.  It carries no mode assumption. -/
def DvStateInv (s : ParserState) : Prop :=
  FloatHypsShaped s.db ∧ AssertDvVarsInFrame s.db ∧ ProofDvInv s.db s.tokp

theorem feedToken_maintains_dvStateInv (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h : DvStateInv s)
    (h_no_err : s.db.error? = none)
    (h_success : (s.feedToken i tk).db.error? = none) :
    DvStateInv (s.feedToken i tk) :=
  ⟨feedToken_maintains_floatHypsShaped s i tk h.1,
   feedToken_maintains_assertDvVarsInFrame_of_floatHypsShaped s i tk h.1 h.2.1 h.2.2
     h_no_err h_success,
   feedToken_maintains_proofDvInv s i tk h.1 h.2.2⟩

theorem dvStateInv_updateLine (s : ParserState) (i : Nat) (c : UInt8)
    (h : DvStateInv s) : DvStateInv (s.updateLine i c) := by
  unfold ParserState.updateLine
  split
  · exact h
  · exact h

/-- Successful `feed` preserves the invariant package. -/
theorem feed_maintains_dvStateInv
    (base : Nat) (arr : ByteArray) (i : Nat) (rs : ParserState.FeedState) (s : ParserState)
    (h_dv : DvStateInv s)
    (h_no_err : s.db.error? = none)
    (h_success : (s.feed base arr i rs).db.error? = none) :
    DvStateInv (s.feed base arr i rs) := by
  refine Nat.rec
    (motive := fun m =>
      ∀ i rs (s : ParserState),
        arr.size - i = m →
        DvStateInv s →
        s.db.error? = none →
        (s.feed base arr i rs).db.error? = none →
        DvStateInv (s.feed base arr i rs))
    ?base ?step (arr.size - i) i rs s rfl h_dv h_no_err h_success
  · intro i rs s hs h_dv _h_no_err _h_success
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.feed
    simp only [hi, ↓reduceDIte]
    exact h_dv
  · intro m ih i rs s hs h_dv h_no_err h_success
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        simp [hz] at hs
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    by_cases h_ws : s.db.config.isWhitespace arr[i] = true
    · cases rs with
      | ws =>
          have h_success_rec :
              ((s.updateLine (base + i) arr[i]).feed base arr (i + 1) .ws).db.error? = none := by
            unfold ParserState.feed at h_success
            simpa [hi, h_ws] using h_success
          have h_rec := ih (i + 1) .ws (s.updateLine (base + i) arr[i]) hs'
            (dvStateInv_updateLine s _ _ h_dv) (by simpa using h_no_err) h_success_rec
          unfold ParserState.feed
          simpa [hi, h_ws] using h_rec
      | token ot =>
          cases ot with
          | this off =>
              let s0 := s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
              let s1 : ParserState := s0.updateLine (base + i) arr[i]
              cases h_err : s1.db.error? with
              | some intr =>
                  have h_err0 : s0.db.error? = some intr := by
                    simpa [s1] using h_err
                  have h_bad : (s.feed base arr i (.token (.this off))).db.error? ≠ none := by
                    unfold ParserState.feed
                    simp [hi, h_ws, s0, h_err0]
                  exact (h_bad h_success).elim
              | none =>
                  have h_tok_ok : s0.db.error? = none := by
                    simpa [s1] using h_err
                  have h_dv0 : DvStateInv s0 :=
                    feedToken_maintains_dvStateInv s (base + off)
                      (ByteSlice.mk arr off (i - off)) h_dv h_no_err h_tok_ok
                  have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
                    unfold ParserState.feed at h_success
                    simp [hi, h_ws, s0, h_tok_ok] at h_success
                    exact h_success
                  have h_rec := ih (i + 1) .ws s1 hs' (dvStateInv_updateLine s0 _ _ h_dv0)
                    h_err h_success_rec
                  unfold ParserState.feed
                  simpa [hi, h_ws, s0, s1, h_tok_ok] using h_rec
          | old base' off arr' =>
              let s0 := s.feedToken (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
              let s1 : ParserState := s0.updateLine (base + i) arr[i]
              cases h_err : s1.db.error? with
              | some intr =>
                  have h_err0 : s0.db.error? = some intr := by
                    simpa [s1] using h_err
                  have h_bad :
                      (s.feed base arr i (.token (.old base' off arr'))).db.error? ≠ none := by
                    unfold ParserState.feed
                    simp [hi, h_ws, s0, h_err0]
                  exact (h_bad h_success).elim
              | none =>
                  have h_tok_ok : s0.db.error? = none := by
                    simpa [s1] using h_err
                  have h_dv0 : DvStateInv s0 :=
                    feedToken_maintains_dvStateInv s (base' + off)
                      (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off
                        (arr'.size - off + i))
                      h_dv h_no_err h_tok_ok
                  have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
                    unfold ParserState.feed at h_success
                    simp [hi, h_ws, s0, h_tok_ok] at h_success
                    exact h_success
                  have h_rec := ih (i + 1) .ws s1 hs' (dvStateInv_updateLine s0 _ _ h_dv0)
                    h_err h_success_rec
                  unfold ParserState.feed
                  simpa [hi, h_ws, s0, s1, h_tok_ok] using h_rec
    · have h_ws' : s.db.config.isWhitespace arr[i] = false := by simpa using h_ws
      cases rs with
      | ws =>
          have h_success_rec : (s.feed base arr (i + 1) (.token (.this i))).db.error? = none := by
            unfold ParserState.feed at h_success
            simpa [hi, h_ws'] using h_success
          have h_rec := ih (i + 1) (.token (.this i)) s hs' h_dv h_no_err h_success_rec
          unfold ParserState.feed
          simpa [hi, h_ws'] using h_rec
      | token ot =>
          have h_success_rec : (s.feed base arr (i + 1) (.token ot)).db.error? = none := by
            unfold ParserState.feed at h_success
            simpa [hi, h_ws'] using h_success
          have h_rec := ih (i + 1) (.token ot) s hs' h_dv h_no_err h_success_rec
          unfold ParserState.feed
          simpa [hi, h_ws'] using h_rec

/-- Successful `feedAll` preserves the invariant package. -/
theorem feedAll_maintains_dvStateInv
    (s : ParserState) (base : Nat) (arr : ByteArray)
    (h_dv : DvStateInv s)
    (h_no_err : s.db.error? = none)
    (h_success : (s.feedAll base arr).db.error? = none) :
    DvStateInv (s.feedAll base arr) := by
  cases h_charp : s.charp with
  | ws =>
      simp only [ParserState.feedAll, h_charp] at h_success ⊢
      exact feed_maintains_dvStateInv base arr 0 .ws s h_dv h_no_err h_success
  | token base' tk =>
      simp only [ParserState.feedAll, h_charp] at h_success ⊢
      exact feed_maintains_dvStateInv base arr 0 _ { s with charp := default }
        h_dv h_no_err h_success

/-! ## From the initial state -/

/-- The initial parser state of `checkBytesCore` (empty registry, `.start`), for
any mode. -/
theorem initState_dvStateInv (config : ModeConfig) :
    DvStateInv ({ (default : ParserState) with
      db := { (default : DB) with config := config } } : ParserState) := by
  have h_none : ∀ n, ({ (default : DB) with config := config } : DB).find? n = none :=
    fun n => PrefixProvability.Checker.default_db_find?_none n
  refine ⟨?_, ?_, trivial⟩
  · intro l f n h_find
    rw [h_none] at h_find
    cases h_find
  · intro lbl f fr name h_find
    rw [h_none] at h_find
    cases h_find

/-- Every error-free state reached by `feedAll` from the initial state, in any
mode, satisfies the invariant together with its companion. -/
theorem feedAll_init_dvStateInv (config : ModeConfig) (arr : ByteArray)
    (h_success : (({ (default : ParserState) with
      db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr).db.error?
        = none) :
    DvStateInv (({ (default : ParserState) with
      db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr) :=
  feedAll_maintains_dvStateInv _ 0 arr (initState_dvStateInv config) rfl h_success

theorem feedAll_init_assertDvVarsInFrame (config : ModeConfig) (arr : ByteArray)
    (h_success : (({ (default : ParserState) with
      db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr).db.error?
        = none) :
    AssertDvVarsInFrame (({ (default : ParserState) with
      db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr).db :=
  (feedAll_init_dvStateInv config arr h_success).2.1

/-- The pure parser's final database satisfies the invariant whenever it is
error-free, in any mode. -/
theorem checkBytesCore_assertDvVarsInFrame (arr : ByteArray) (config : ModeConfig)
    (h_ok : (checkBytesCore arr config).error? = none) :
    AssertDvVarsInFrame (checkBytesCore arr config) := by
  let s0 : ParserState := { (default : ParserState) with
    db := { (default : DB) with config := config } }
  let sF : ParserState := s0.feedAll 0 arr
  have h_eq : checkBytesCore arr config = sF.done arr.size := rfl
  rw [h_eq] at h_ok ⊢
  have h_e0 : sF.db.error? = none := ParserOps.done_no_error_implies_db_no_error sF arr.size h_ok
  have h_dvF : DvStateInv sF := feedAll_init_dvStateInv config arr h_e0
  cases h_charp : sF.charp with
  | ws =>
      exact assertDvVarsInFrame_of_find?_eq
        (fun n => PrefixProvability.Checker.done_find?_eq_self sF arr.size n h_e0 h_charp)
        h_dvF.2.1
  | token pos tk =>
      have h_e1 : (sF.feedToken pos tk.toSlice).db.error? = none := by
        cases h_e : (sF.feedToken pos tk.toSlice).db.error? with
        | none => rfl
        | some it =>
            exfalso
            have h_stuck : (ParserState.done sF arr.size).error? ≠ none := by
              simp only [ParserState.done, Id.run, DB.error, Option.isSome_some,
                Option.isSome_none, Bool.false_eq_true, reduceIte, h_e0, h_charp, h_e]
              simp [h_e]
            exact h_stuck h_ok
      have h_flush := feedToken_maintains_assertDvVarsInFrame_of_floatHypsShaped sF pos
        tk.toSlice h_dvF.1 h_dvF.2.1 h_dvF.2.2 h_e0 h_e1
      exact assertDvVarsInFrame_of_find?_eq
        (fun n => PrefixProvability.Checker.done_find?_eq_flush sF arr.size pos tk n
          h_e0 h_charp h_e1)
        h_flush

/-- The Boolean post-check agrees with the invariant. -/
theorem assertDvVarsInFrame?_of_assertDvVarsInFrame {db : DB}
    (h : AssertDvVarsInFrame db) : db.assertDvVarsInFrame? = true := by
  unfold DB.assertDvVarsInFrame?
  rw [List.all_eq_true]
  intro kv h_mem
  obtain ⟨k, o⟩ := kv
  cases o with
  | assert f fr name =>
      have h_find : db.find? k = some (.assert f fr name) :=
        (Std.HashMap.mem_toList_iff_getElem?_eq_some).1 h_mem
      unfold DB.frameDvVarsInFrame?
      rw [List.all_eq_true]
      intro p hp
      exact decide_eq_true (h k f fr name h_find p.1 p.2 hp)
  | const _ => rfl
  | var _ => rfl
  | hyp _ _ _ => rfl

/-- An error-free `checkBytesCore` run always passes the `$d` part of the
`checkBytes` post-check, in every mode. -/
theorem checkBytesCore_assertDvVarsInFrame?_eq_true (arr : ByteArray) (config : ModeConfig)
    (h_ok : (checkBytesCore arr config).error? = none) :
    (checkBytesCore arr config).assertDvVarsInFrame? = true :=
  assertDvVarsInFrame?_of_assertDvVarsInFrame (checkBytesCore_assertDvVarsInFrame arr config h_ok)

/-! ## Examples

Kernel-checked instances: a stored `$d x y` backed by `$f` hypotheses for both
variables satisfies the invariant, and the same `$d` stored with no `$f` in its
frame violates it, so the invariant (and the runtime post-check it replaces) is
not vacuous. -/

namespace Examples

/-- `wx $f wff x $.` -/
def objX : Object := .hyp false #[.const "wff", .var "x"] "wx"
/-- `wy $f wff y $.` -/
def objY : Object := .hyp false #[.const "wff", .var "y"] "wy"
/-- `$d x y` with the `$f` hypotheses of both variables. -/
def frGood : Verify.Frame := ⟨#[("x", "y")], #["wx", "wy"]⟩
/-- `$d x y` with no `$f` hypotheses. -/
def frBad : Verify.Frame := ⟨#[("x", "y")], #[]⟩
/-- The claim `|- x y`. -/
def fXY : Verify.Formula := #[.const "|-", .var "x", .var "y"]

def dbGood : DB :=
  { (default : DB) with
    objects := (((∅ : Std.HashMap String Object).insert "wx" objX).insert "wy" objY).insert
      "ax" (.assert fXY frGood "ax") }

def dbBad : DB :=
  { (default : DB) with
    objects := (∅ : Std.HashMap String Object).insert "ax" (.assert fXY frBad "ax") }

/-- Negative: `$d x y` stored without any `$f` in its frame. -/
theorem dbBad_violates : ¬ AssertDvVarsInFrame dbBad := by
  intro h
  have h_find : dbBad.find? "ax" = some (.assert fXY frBad "ax") :=
    Std.HashMap.getElem?_insert_self
  have h_mem : ("x", "y") ∈ frBad.dj.toList := List.mem_singleton.mpr rfl
  have h_x := (h "ax" fXY frBad "ax" h_find "x" "y" h_mem).1
  simp [DB.frameFloatVars, frBad] at h_x

/-- Positive: `$d x y` stored with `wx` and `wy` in its frame. -/
theorem dbGood_satisfies : AssertDvVarsInFrame dbGood := by
  have h_wx : dbGood.find? "wx" = some objX := by
    show ((((∅ : Std.HashMap String Object).insert "wx" objX).insert "wy" objY).insert
      "ax" (.assert fXY frGood "ax"))["wx"]? = some objX
    simp only [Std.HashMap.getElem?_insert]
    rfl
  have h_wy : dbGood.find? "wy" = some objY := by
    show ((((∅ : Std.HashMap String Object).insert "wx" objX).insert "wy" objY).insert
      "ax" (.assert fXY frGood "ax"))["wy"]? = some objY
    simp only [Std.HashMap.getElem?_insert]
    rfl
  intro lbl f fr name h_find v w h_mem
  have h_find' : ((((∅ : Std.HashMap String Object).insert "wx" objX).insert "wy" objY).insert
      "ax" (.assert fXY frGood "ax"))[lbl]? = some (.assert f fr name) := h_find
  simp only [Std.HashMap.getElem?_insert] at h_find'
  split at h_find'
  · -- the only assertion, `ax`
    have h_fr : fr = frGood := by
      injection h_find' with h_obj
      injection h_obj with _ h_fr _
      exact h_fr.symm
    subst h_fr
    have h_vw : (v, w) = ("x", "y") := List.mem_singleton.mp h_mem
    injection h_vw with h_v h_w
    subst h_v
    subst h_w
    refine ⟨(frameFloatVars_mem_iff' dbGood frGood "x").2 ?_,
      (frameFloatVars_mem_iff' dbGood frGood "y").2 ?_⟩
    · exact ⟨"wx", #[.const "wff", .var "x"], "wx", by simp [frGood], h_wx, by decide, rfl⟩
    · exact ⟨"wy", #[.const "wff", .var "y"], "wy", by simp [frGood], h_wy, by decide, rfl⟩
  · split at h_find'
    · cases h_find'
    · split at h_find'
      · cases h_find'
      · simp at h_find'

end Examples

end Metamath.AssertDv
