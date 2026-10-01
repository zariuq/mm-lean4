import Metamath.SourceCompleteness.Invariants
import Metamath.SourceCompleteness.Compose
import Metamath.SourceCompleteness.DeclTokens
import Metamath.SourceCompleteness.ThmTokens
import Metamath.RootFileCheck
import Metamath.SourceCompleteness.NoRequest
import Metamath.Spec.DeclarativeOriginal

/-!
# Completeness for source text

The checker is complete for Mario Carneiro's semantics at the level of source text. Let the parser
read the text `arr` from the start without error, in a mode without duplicate `$f` statements,
ending between statements with no token pending (`tokp = .start`, `charp = .ws`). Take a claim `f`
with a constant head and declared symbols under a fresh label token, whose frame trims to `frImpl`
with stored statement `fr`.

* `statementProvable_iff_sourceAccepts`: the stored statement is provable from the assertions read
  so far iff, for some admissible dummy declarations `ds` and normal proof `proof`, the parser reads
  the text `render s ds label f proof` after `arr` without error, ends between statements with no
  token pending, stores `label` as exactly `f` with the frame `frImpl`, and records no new incomplete
  proof (`SourceAccepts`).
* `afterSource_declTokens`, `sourceAccepts_toDatabaseTotal`: the declarations leave the assertion
  database and the claim's trimmed frame unchanged; the accepted continuation adds exactly the one
  assertion and keeps every earlier object.
* `statementProvable_iff_fileAccepts`: the same for the complete file, closed by one `$}` for each
  open block and checked by `checkBytes`, post-checks included (`FileAccepts`);
  `fileAccepts_verified`: a prefix without incomplete proofs gives a verified file.
* `check_accepts_of_statementProvable`, `statementProvable_of_check`: the same through
  `Verify.check`, for a root file that resolves and reads as exactly those bytes; the rendered file
  raises no include request (`checkBytes_errorNotRequest`), so `check` agrees with `checkBytes` on
  it (`Metamath.RootFileCheck`).
* `acceptedWithDummies_iff_statementProvable_afterSource`: the database-action form
  (`AcceptedWithDummies`) at such a point of the source text.

`statementProvable_iff_sourceAccepts_originalRule` and `statementProvable_iff_fileAccepts_originalRule`
state the same for Mario Carneiro's original `ax` rule.

Provability is relative to the assertions read so far: an earlier theorem with an incomplete proof
(`?`, accepted in the default mode) counts as an assertion of the prefix. The theorems are about the
parser's reading of the source, and they are existence statements: they do not compute the dummy
declarations or the proof.

`Admissible` restricts the witnesses to fresh dummies and legal tokens, with a normal proof made of
label tokens, so the rendered text holds only the declarations and the one `$p` statement. The
invariants the argument uses hold at every error-free checkpoint (`afterSource_invariants`).
`runTokens_render` is the core: the rendered tokens run as `declareDummies` followed by the
parser's `$p` path, which succeeds exactly when `ProofAccepted` holds.
-/

set_option autoImplicit false

namespace Metamath.SourceCompleteness

open Metamath.Verify Metamath.CheckerCompleteness
open Metamath.WF (WellFormedDB WellScopedDB FormulaSymbolsDeclared)

/-! ## Tokens of the witnesses -/

theorem isMathToken_dummyName (b i : Nat) : IsMathToken (Spec.DummyExtension.dummyName b i) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg String.length h
    simp [Spec.DummyExtension.dummyName] at this
  · intro c hc
    simp [Spec.DummyExtension.dummyName] at hc
    subst hc
    decide

theorem isLabelToken_dummyLabel (b i : Nat) : IsLabelToken (dummyLabel b i) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg String.length h
    simp [dummyLabel] at this
  · intro c hc
    simp [dummyLabel] at hc
    subst hc
    decide

/-- The symbols of a claim whose symbols are declared are math symbol tokens. -/
theorem claim_tokens_of_declared {db : DB} {f : Verify.Formula} (h_keys : KeysAreTokens db)
    (h_decl : FormulaSymbolsDeclared db f) : ∀ x ∈ f.toList, IsMathToken x.value := by
  intro x hx
  have h := h_decl x hx
  cases x with
  | const c =>
    simp only [DB.isConst] at h
    split at h
    · rename_i o h_find
      exact h_keys c _ h_find
    · cases h
  | var v =>
    simp only [DB.isVar] at h
    split at h
    · rename_i o h_find
      exact h_keys v _ h_find
    · cases h

/-- A declared constant is a math symbol token. -/
theorem isMathToken_of_isConst {db : DB} {c : String} (h_keys : KeysAreTokens db)
    (h : db.isConst c = true) : IsMathToken c := by
  simp only [DB.isConst] at h
  split at h
  · rename_i o h_find
    exact h_keys c _ h_find
  · cases h

/-- A proof step that succeeds names a hypothesis or an assertion. -/
theorem stepNormal_ok_find? {db : DB} {pr pr' : ProofState} {l : String}
    (h : db.stepNormal pr l = .ok pr') :
    ∃ o, db.find? l = some o ∧
      ((∃ ess f n, o = .hyp ess f n) ∨ (∃ f fr n, o = .assert f fr n)) := by
  unfold DB.stepNormal at h
  split at h
  · rename_i ess f n h_find
    exact ⟨_, h_find, Or.inl ⟨ess, f, n, rfl⟩⟩
  · rename_i f fr n h_find
    exact ⟨_, h_find, Or.inr ⟨f, fr, n, rfl⟩⟩
  · cases h

/-! ## Active claim variables -/

/-- The float variables of the active frame are math symbol tokens. -/
theorem frameFloatVars_tokens {db : DB} (h_keys : KeysAreTokens db) (h_act : FloatVarsActive db)
    (h_sound : db.ActiveVarsSound) : ∀ v ∈ db.frameFloatVars db.frame, IsMathToken v := by
  intro v hv
  obtain ⟨d, hd⟩ := mem_activeVars_of_mem_frameFloatVars h_act hv
  have h_var : db.isVar v = true := h_sound _ hd
  simp only [DB.isVar] at h_var
  split at h_var
  · rename_i o h_find
    exact h_keys v _ h_find
  · cases h_var

/-- The variables of a claim whose frame trims are active. -/
theorem claimVars_active_of_trim (db : DB) (f : Verify.Formula) (frImpl : Verify.Frame)
    (h_wf : WellFormedDB db) (h_scoped : WellScopedDB db) (h_act : FloatVarsActive db)
    (h_head : f.hasConstHead = true) (h_decl : FormulaSymbolsDeclared db f)
    (h_trim : db.trimFrame' f = .ok frImpl) :
    ∀ v, Verify.Sym.var v ∈ f.toList → db.isActiveVar v = true := by
  intro v hv
  have h_resp := formulaSymsRespectFrame_active_of_trim db f frImpl h_wf h_scoped h_decl h_trim
  have h_tail : Verify.Sym.var v ∈ f.toList.tail := by
    have h_pos : 0 < f.size := by
      unfold Formula.hasConstHead at h_head
      split at h_head
      · assumption
      · cases h_head
    have h_cons : f.toList = f[0] :: f.toList.tail := by
      cases h : f.toList with
      | nil => simp [← Array.length_toList, h] at h_pos
      | cons x xs =>
        simp only [List.tail_cons, List.cons.injEq, and_true]
        have := congrArg (·[0]?) h
        simp at this
        obtain ⟨_, hx⟩ := this
        exact hx.symm
    rw [h_cons] at hv
    rcases List.mem_cons.mp hv with h0 | ht
    · exfalso
      unfold Formula.hasConstHead at h_head
      rw [if_pos h_pos, Array.getBang_eq_get_nat f 0 h_pos, ← h0] at h_head
      cases h_head
    · exact ht
  unfold DB.formulaSymsRespectFrame at h_resp
  have h_mem := List.all_eq_true.mp h_resp _ h_tail
  simp only [decide_eq_true_eq] at h_mem
  have h_var : db.isVar v = true := h_decl _ hv
  exact isActiveVar_of_mem_frameFloatVars h_act h_mem h_var

/-! ## Proof labels -/

/-- Every step of a normal proof that runs names a hypothesis or an assertion. -/
theorem foldlM_stepNormal_labels (db : DB) (proof : Array String) (pr pr' : ProofState)
    (h : proof.foldlM (fun pr l => db.stepNormal pr l) pr = .ok pr') :
    ∀ l ∈ proof.toList, ∃ o, db.find? l = some o ∧
      ((∃ ess f n, o = .hyp ess f n) ∨ (∃ f fr n, o = .assert f fr n)) := by
  rw [← Array.foldlM_toList] at h
  generalize proof.toList = ls at h ⊢
  induction ls generalizing pr with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldlM_cons] at h
    cases h1 : db.stepNormal pr l with
    | error e =>
      rw [h1] at h
      cases h
    | ok pr1 =>
      rw [h1] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact stepNormal_ok_find? h1
      · exact ih pr1 h x hx

/-- The labels of a normal proof that runs are label tokens when every name is a token. -/
theorem proof_tokens_of_foldlM (db : DB) (h_keys : KeysAreTokens db) (proof : Array String)
    (pr pr' : ProofState) (h : proof.foldlM (fun pr l => db.stepNormal pr l) pr = .ok pr') :
    ∀ l ∈ proof.toList, IsLabelToken l := by
  intro l hl
  obtain ⟨o, h_find, h_o⟩ := foldlM_stepNormal_labels db proof pr pr' h l hl
  have := h_keys l o h_find
  rcases h_o with ⟨ess, f, n, rfl⟩ | ⟨f, fr, n, rfl⟩ <;> exact this

/-! ## Incomplete proofs -/

@[simp] theorem insert_incompleteProofs (db : DB) (pos : Pos) (l : String)
    (obj : String → Object) : (db.insert pos l obj).incompleteProofs = db.incompleteProofs := by
  unfold DB.insert
  dsimp only
  repeat' split
  all_goals rfl

@[simp] theorem insertHypChecks_incompleteProofs (db : DB) (pos : Pos) (ess : Bool)
    (f : Verify.Formula) : (db.insertHypChecks pos ess f).incompleteProofs = db.incompleteProofs := by
  unfold DB.insertHypChecks
  dsimp only
  repeat' split
  all_goals rfl

@[simp] theorem insertHyp_incompleteProofs (db : DB) (pos : Pos) (l : String) (ess : Bool)
    (f : Verify.Formula) : (db.insertHyp pos l ess f).incompleteProofs = db.incompleteProofs := by
  unfold DB.insertHyp
  dsimp only
  repeat' split
  all_goals simp only [DB.withHyps, DB.withFrame, insert_incompleteProofs,
    insertHypChecks_incompleteProofs]

theorem declareDummies_incompleteProofs (db : DB) (pos : Pos) (ds : List DummyDecl) :
    (db.declareDummies pos ds).incompleteProofs = db.incompleteProofs := by
  unfold DB.declareDummies
  simp only [DB.withDJ, DB.withFrame]
  generalize db = db0
  induction ds generalizing db0 with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [DB.declareDummy]

/-! ## Activity -/

/-- Declaring dummies keeps every active variable active. -/
theorem declareDummies_isActiveVar (db : DB) (pos : Pos) (label : String) (ds : List DummyDecl)
    (h_err : db.error? = none) (h_wf : WellFormedDB db) (h_sc : WellScopedDB db)
    (h_fresh : DummyDeclsFresh db label ds) {v : String} (h : db.isActiveVar v = true) :
    (db.declareDummies pos ds).isActiveVar v = true := by
  have h_mono := declareDummies_find?_mono db pos label ds h_err h_wf h_sc h_fresh
  obtain ⟨_, _, _, h_av⟩ := declareDummies_fields db pos label ds h_err h_wf h_sc h_fresh
  simp only [DB.isActiveVar, Bool.and_eq_true] at h ⊢
  refine ⟨?_, ?_⟩
  · have hv := h.1
    simp only [DB.isVar] at hv ⊢
    split at hv
    · rename_i o h_find
      rw [h_mono v _ h_find]
    · cases hv
  · rw [h_av, Array.any_append, h.2, Bool.true_or]

/-! ## Positions -/

/-- A one-element stack holding `f`. -/
theorem stack_eq_singleton {S : Array Verify.Formula} {f : Verify.Formula} (h_size : S.size = 1)
    (h_top : S[0]? = some f) : S = #[f] := by
  apply Array.ext
  · simpa using h_size
  · intro i h1 h2
    have hi : i = 0 := by simp at h2; omega
    subst hi
    simp only [Array.getElem?_eq_getElem h1, Option.some.injEq] at h_top
    simpa using h_top

/-- Proof acceptance does not depend on the position recorded for the proof, which only enters
error messages. -/
theorem proofAccepted_pos {s : ParserState} {pos pos' : Pos} {label : String}
    {f : Verify.Formula} {proof : Array String} (h_fresh : s.db.find? label = none)
    (h_err : s.db.error? = none) (h : ProofAccepted s pos label f proof) :
    ProofAccepted s pos' label f proof := by
  obtain ⟨h_head, h_int, frImpl, pr, h_trim, h_fold, h_fin⟩ := h
  obtain ⟨r, h_fold', h_st⟩ := Metamath.PrefixProvenance.foldlM_stepNormal_transfer_array s.db
    proof { s.db.mkProofState pos label f frImpl with ptp := .normal }
    { s.db.mkProofState pos' label f frImpl with ptp := .normal } pr rfl h_fold
  have h_r := foldlM_stepNormal_preserves_fields s.db proof _ r h_fold'
  have h_pr := foldlM_stepNormal_preserves_fields s.db proof _ pr h_fold
  obtain ⟨h_size, h_top, _⟩ :=
    Metamath.ParserAnyFormatEquivalence.finishProof_success_stack_conditions s pr h_fin
  have h_stack : r.stack = #[r.fmla] := by
    rw [h_st, h_r.2.2.1, ← (show pr.fmla = f from h_pr.2.2.1)]
    exact stack_eq_singleton h_size h_top
  refine ⟨h_head, h_int, frImpl, r, h_trim, h_fold', ?_⟩
  exact (finishProof_of_exact s r h_r.2.2.2.2.2.1 h_stack h_r.2.2.2.2.2.2
    (by rw [h_r.2.1]; exact h_fresh) h_err).2

/-! ## Preservation -/

open Metamath.Kernel (toDatabaseTotal toFrame toExpr toExprOpt)

/-- Declaring dummies with legal names keeps every name a token of its kind. -/
theorem keysAreTokens_declareDummies (db : DB) (pos : Pos) (label : String) (ds : List DummyDecl)
    (h_err : db.error? = none) (h_wf : WellFormedDB db) (h_sc : WellScopedDB db)
    (h_fresh : DummyDeclsFresh db label ds) (h_keys : KeysAreTokens db)
    (h_var : ∀ d ∈ ds, IsMathToken d.var) (h_lbl : ∀ d ∈ ds, IsLabelToken d.lbl) :
    KeysAreTokens (db.declareDummies pos ds) := by
  obtain ⟨h_old, h_v, h_l⟩ := declareDummies_find? db pos label ds h_err h_wf h_sc h_fresh
  intro l o h_find
  by_cases hv : l ∈ ds.map (·.var)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    rw [h_v d hd] at h_find
    cases h_find
    exact h_var d hd
  · by_cases hl : l ∈ ds.map (·.lbl)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hl
      rw [h_l d hd] at h_find
      cases h_find
      exact h_lbl d hd
    · rw [h_old l hv hl] at h_find
      exact h_keys l o h_find

theorem find?_insert_assert (db : DB) (pos : Pos) (label : String) (f : Verify.Formula)
    (frImpl : Verify.Frame) (h_err : db.error? = none) (h_label : db.find? label = none)
    (l : String) :
    (db.insert pos label (.assert f frImpl)).find? l =
      if l = label then some (.assert f frImpl label) else db.find? l := by
  rw [insert_assert_fresh_eq db pos label f frImpl h_label h_err]
  simp only [DB.find?, Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases h : l = label
  · simp [h]
  · simp [h, Ne.symm h]

/-- Storing a fresh assertion adds exactly its statement to the assertion database and keeps
every other entry. -/
theorem toDatabaseTotal_insert_assert (db : DB) (pos : Pos) (label : String) (f : Verify.Formula)
    (frImpl : Verify.Frame) (fr : Spec.Frame) (h_err : db.error? = none) (h_wf : WellFormedDB db)
    (h_label : db.find? label = none) (h_size : 0 < f.size) (h_fr : toFrame db frImpl = some fr) :
    toDatabaseTotal (db.insert pos label (.assert f frImpl)) label = some (fr, toExpr f) ∧
    ∀ l, l ≠ label →
      toDatabaseTotal (db.insert pos label (.assert f frImpl)) l = toDatabaseTotal db l := by
  have h_find := find?_insert_assert db pos label f frImpl h_err h_label
  have h_mono : ∀ l o, db.find? l = some o →
      (db.insert pos label (.assert f frImpl)).find? l = some o := by
    intro l o h
    rw [h_find]
    have : l ≠ label := fun h' => by rw [h', h_label] at h; cases h
    simp [this, h]
  refine ⟨?_, ?_⟩
  · unfold toDatabaseTotal
    rw [h_find, if_pos rfl]
    simp only
    rw [Metamath.StoredStatementSoundness.Runtime.toFrame_stable_of_find_mono db _ frImpl fr
      h_mono h_fr, (Metamath.Kernel.toExprOpt_some_iff_toExpr f (toExpr f)).2 ⟨h_size, rfl⟩]
  · intro l hl
    unfold toDatabaseTotal
    rw [h_find, if_neg hl]
    cases h_l : db.find? l with
    | none => rfl
    | some o =>
      cases o with
      | assert g frL n =>
        have h_obj := h_wf.2 l (.assert g frL n) h_l
        obtain ⟨frS, h_frS⟩ := Metamath.Kernel.toFrame_some_of_wfFrame_any db frL h_obj.2
        simp only
        rw [Metamath.StoredStatementSoundness.Runtime.toFrame_stable_of_find_mono db _ frL frS
          h_mono h_frS, h_frS]
      | const _ => rfl
      | var _ => rfl
      | hyp _ _ _ => rfl

/-! ## Rendered tokens -/

/-- A string whose bytes form one lexical token in every mode: nonempty, printable, without
whitespace. -/
def Lexical (t : String) : Prop :=
  t.toUTF8.toList ≠ [] ∧ ∀ b ∈ t.toUTF8.toList, isPrintable b = true ∧ isWhitespace b = false

instance (t : String) : Decidable (Lexical t) := by
  unfold Lexical
  infer_instance

theorem IsLabelToken.lexical {t : String} (h : IsLabelToken t) : Lexical t := by
  have := (spells_label h (ByteSlice.bytes_toByteSlice_self t.toUTF8)).2
  unfold LexToken at this
  rw [ByteSlice.bytes_toByteSlice_self] at this
  refine ⟨this.1, fun b hb => ⟨?_, this.2 b hb⟩⟩
  rw [toUTF8_toList_of_ascii h.ascii] at hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact labelChar_printable (h.2 c hc)

theorem IsMathToken.lexical {t : String} (h : IsMathToken t) : Lexical t := by
  have := (spells_math h (ByteSlice.bytes_toByteSlice_self t.toUTF8)).2
  unfold LexToken at this
  rw [ByteSlice.bytes_toByteSlice_self] at this
  refine ⟨this.1, fun b hb => ⟨?_, this.2 b hb⟩⟩
  rw [toUTF8_toList_of_ascii h.ascii] at hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact mathChar_printable (h.2 c hc)

theorem lexical_keyword : ∀ t ∈ ["$v", "$f", "$d", "$p", "$.", "$=", "$}"], Lexical t := by
  decide +kernel

theorem mem_dummyDJs {seen vs : List String} {p : Verify.DJ} (h : p ∈ dummyDJs seen vs) :
    (p.1 ∈ seen ∨ p.1 ∈ vs) ∧ (p.2 ∈ seen ∨ p.2 ∈ vs) := by
  induction vs generalizing seen with
  | nil => simp [dummyDJs] at h
  | cons v vs ih =>
    simp only [dummyDJs, List.mem_append, List.mem_map] at h
    rcases h with ⟨w, hw, rfl⟩ | h
    · unfold canonDJ
      by_cases hvw : v < w <;> simp [hvw, hw]
    · obtain ⟨h1, h2⟩ := ih h
      simp only [List.mem_append, List.mem_cons] at h1 h2 ⊢
      exact ⟨by rcases h1 with (h | h) | h <;> simp_all, by rcases h2 with (h | h) | h <;> simp_all⟩

/-- The tokens a rendered text holds: label tokens, math symbol tokens and the keywords. -/
def RenderedToken (t : String) : Prop :=
  IsLabelToken t ∨ IsMathToken t ∨ t ∈ ["$v", "$f", "$d", "$p", "$.", "$=", "$}"]

theorem RenderedToken.lexical {t : String} (h : RenderedToken t) : Lexical t := by
  rcases h with h | h | h
  · exact h.lexical
  · exact h.lexical
  · exact lexical_keyword t h

/-- The tokens of rendered declarations. -/
theorem declTokens_rendered {seen : List String} {ds : List DummyDecl}
    (h_seen : ∀ v ∈ seen, IsMathToken v) (h_var : ∀ d ∈ ds, IsMathToken d.var)
    (h_lbl : ∀ d ∈ ds, IsLabelToken d.lbl) (h_tc : ∀ d ∈ ds, IsMathToken d.tc) :
    ∀ t ∈ declTokens seen ds, RenderedToken t := by
  have kw : ∀ t ∈ ["$v", "$f", "$d", "$p", "$.", "$=", "$}"], RenderedToken t :=
    fun t ht => Or.inr (Or.inr ht)
  have h_names : ∀ v, v ∈ seen ∨ v ∈ ds.map (·.var) → IsMathToken v := by
    rintro v (hv | hv)
    · exact h_seen v hv
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      exact h_var d hd
  intro t ht
  simp only [declTokens, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with ⟨d, hd, ht⟩ | ⟨p, hp, ht⟩
  · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact kw _ (by simp)
    · exact Or.inr (Or.inl (h_var d hd))
    · exact kw _ (by simp)
    · exact Or.inl (h_lbl d hd)
    · exact kw _ (by simp)
    · exact Or.inr (Or.inl (h_tc d hd))
    · exact Or.inr (Or.inl (h_var d hd))
    · exact kw _ (by simp)
  · obtain ⟨h1, h2⟩ := mem_dummyDJs hp
    rcases ht with rfl | rfl | rfl | rfl
    · exact kw _ (by simp)
    · exact Or.inr (Or.inl (h_names _ h1))
    · exact Or.inr (Or.inl (h_names _ h2))
    · exact kw _ (by simp)

/-- The tokens of a rendered `$p` statement. -/
theorem thmTokens_rendered {label : String} {f : Verify.Formula} {proof : Array String}
    (h_label : IsLabelToken label) (h_claim : ∀ x ∈ f.toList, IsMathToken x.value)
    (h_proof : ∀ l ∈ proof.toList, IsLabelToken l) :
    ∀ t ∈ thmTokens label f proof, RenderedToken t := by
  have kw : ∀ t ∈ ["$v", "$f", "$d", "$p", "$.", "$=", "$}"], RenderedToken t :=
    fun t ht => Or.inr (Or.inr ht)
  intro t ht
  simp only [thmTokens, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false] at ht
  rcases ht with rfl | rfl | ⟨x, hx, rfl⟩ | rfl | ht | rfl
  · exact Or.inl h_label
  · exact kw _ (by simp)
  · exact Or.inr (Or.inl (h_claim x hx))
  · exact kw _ (by simp)
  · exact Or.inl (h_proof t ht)
  · exact kw _ (by simp)

/-- The tokens of the rendered text. -/
theorem renderTokens_rendered {seen : List String} {ds : List DummyDecl} {label : String}
    {f : Verify.Formula} {proof : Array String} (h_seen : ∀ v ∈ seen, IsMathToken v)
    (h_var : ∀ d ∈ ds, IsMathToken d.var) (h_lbl : ∀ d ∈ ds, IsLabelToken d.lbl)
    (h_tc : ∀ d ∈ ds, IsMathToken d.tc) (h_label : IsLabelToken label)
    (h_claim : ∀ x ∈ f.toList, IsMathToken x.value) (h_proof : ∀ l ∈ proof.toList, IsLabelToken l) :
    ∀ t ∈ renderTokens seen ds label f proof, RenderedToken t := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact declTokens_rendered h_seen h_var h_lbl h_tc t ht
  · exact thmTokens_rendered h_label h_claim h_proof t ht

theorem closeTokens_rendered (k : Nat) : ∀ t ∈ List.replicate k "$}", RenderedToken t := by
  intro t ht
  rw [(List.mem_replicate.mp ht).2]
  exact Or.inr (Or.inr (by simp))

/-! ## End of file -/

theorem popScope_fields (pos : Pos) (db : DB) (h : 0 < db.scopes.size) :
    (db.popScope pos).objects = db.objects ∧ (db.popScope pos).error? = db.error? ∧
      (db.popScope pos).scopes.size = db.scopes.size - 1 ∧
      (db.popScope pos).incompleteProofs = db.incompleteProofs ∧
      (db.popScope pos).config = db.config ∧ (db.popScope pos).interrupt = db.interrupt := by
  unfold DB.popScope
  obtain ⟨sc, h_back⟩ : ∃ sc, db.scopes.back? = some sc :=
    ⟨db.scopes[db.scopes.size - 1], by rw [Array.back?_eq_getElem?]; simp⟩
  simp [h_back]

/-- `$}` between statements closes the innermost block. -/
theorem feedToken_close (s : ParserState) (pos : Nat) (h_start : s.tokp = .start) :
    s.feedToken pos "$}".toUTF8.toByteSlice = s.withDB (.popScope (s.mkPos pos)) := by
  have hb : ("$}".toUTF8.toByteSlice).bytes = "$}".toUTF8.toList :=
    ByteSlice.bytes_toByteSlice_self _
  generalize "$}".toUTF8.toByteSlice = tk at hb ⊢
  obtain ⟨h1, h2, _, _, h5⟩ := spells_dollar_rbrace hb
  have hc1 : tk.eqArray "$(".toAscii = false := by
    rw [spells_eqArray hb]; decide
  have hc2 : tk.eqArray "$[".toAscii = false := by
    rw [spells_eqArray hb]; decide
  unfold ParserState.feedToken
  simp [h_start, hc1, hc2, h1, h2, h5]

/-- Closing `k` blocks between statements, with at least `k` blocks open: no error, the objects
and incomplete proofs are kept, and `k` blocks fewer are open. -/
theorem runTokens_close : ∀ (k : Nat) (s : ParserState) (base : Nat),
    s.tokp = .start → s.db.error? = none → k ≤ s.db.scopes.size →
    (runTokens s base (List.replicate k "$}")).db.error? = none ∧
    (runTokens s base (List.replicate k "$}")).tokp = .start ∧
    (runTokens s base (List.replicate k "$}")).db.objects = s.db.objects ∧
    (runTokens s base (List.replicate k "$}")).db.incompleteProofs = s.db.incompleteProofs ∧
    (runTokens s base (List.replicate k "$}")).db.scopes.size = s.db.scopes.size - k ∧
    (runTokens s base (List.replicate k "$}")).charp = s.charp
  | 0, s, base, h_start, h_err, _ => by
    simp [runTokens, h_start, h_err]
  | k + 1, s, base, h_start, h_err, h_k => by
    have h_pos : 0 < s.db.scopes.size := by omega
    obtain ⟨h_obj, h_e, h_sc, h_inc, _, _⟩ := popScope_fields (s.mkPos base) s.db h_pos
    have h_step := feedToken_close s base h_start
    simp only [List.replicate_succ, runTokens, h_step, ParserState.withDB, h_e, h_err,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := runTokens_close k
      { s with db := s.db.popScope (s.mkPos base) } _ h_start (by simpa using h_e.trans h_err)
      (by simp only; omega)
    refine ⟨r1, r2, r3.trans h_obj, r4.trans h_inc, ?_, r6⟩
    rw [r5]
    simp only [h_sc]
    omega

/-- At the end of the source text, a clean checkpoint with no open block is accepted as it is. -/
theorem done_of_clean (s : ParserState) (base : Nat) (h_ws : s.charp = .ws)
    (h_start : s.tokp = .start) (h_sc : s.db.scopes.size = 0) :
    s.done base = s.db := by
  unfold ParserState.done
  simp [h_ws, h_start, h_sc]


/-! ## The checkpoint -/

open Metamath.Kernel (toDatabaseTotal toFrame toExpr)
open Metamath.Spec.StoredStatement (statementOfFrame)
open Metamath.Spec.Equivalence (dbToAxioms)
open Metamath.ParserOps (ParserStateInv)
open Metamath.AssertDv (AssertDvVarsInFrame)

/-- The invariants at the end of an error-free read of source text, derived from reachability: the
parser invariant, the source invariant and the stored-`$d` invariant. -/
theorem afterSource_invariants (config : ModeConfig) (arr : ByteArray)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none) :
    ParserStateInv (afterSource config arr) ∧ SourceInv (afterSource config arr) ∧
      AssertDvVarsInFrame (afterSource config arr).db :=
  ⟨ParserOps.feedAll_maintains_stateInv _ 0 arr (ParserOps.initState_inv config) rfl h_no_dup
      h_err,
    feedAll_init_sourceInv config arr h_err,
    AssertDv.feedAll_init_assertDvVarsInFrame config arr h_err⟩

/-- **At a point of the source text.** Let the parser read the source text `arr` from the start
without error, ending between statements, in a mode without duplicate `$f` statements. Then the
statement that a `$p` claim `f` stores is provable in Mario Carneiro's semantics from the assertions
read so far iff, after declaring finitely many fresh dummy variables, the parser accepts a
normal-mode proof of `f`. -/
theorem acceptedWithDummies_iff_statementProvable_afterSource (config : ModeConfig)
    (arr : ByteArray) (pos : Pos) (label : String) (f : Verify.Formula) (frImpl : Verify.Frame)
    (fr : Spec.Frame) (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_label : (afterSource config arr).db.find? label = none)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr) :
    AcceptedWithDummies (afterSource config arr) pos label f ↔
      (statementOfFrame fr (toExpr f)).Provable
        (dbToAxioms (toDatabaseTotal (afterSource config arr).db)) :=
  have ⟨h_inv, ⟨_, _, h_int, _⟩, h_dv⟩ := afterSource_invariants config arr h_no_dup h_err
  acceptedWithDummies_iff_statementProvable _ pos label f frImpl fr h_inv h_start h_err h_int
    h_label h_head h_decl h_trim h_fr h_dv

/-- The spec-frame premise is always met: a frame that trims at an error-free checkpoint has a
spec frame. -/
theorem exists_toFrame_of_trim (config : ModeConfig) (arr : ByteArray) (f : Verify.Formula)
    (frImpl : Verify.Frame) (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl) :
    ∃ fr, toFrame (afterSource config arr).db frImpl = some fr :=
  Kernel.toFrame_some_of_wfFrame_any _ _
    (ParserOps.trimFrame'_success_implies_wellformed_frame _ f frImpl
      (afterSource_invariants config arr h_no_dup h_err).1.1 h_trim)

/-- The position of the `$p` label in the text rendered at `s`, placed at `base`. -/
def labelPos (s : ParserState) (base : Nat) (ds : List DummyDecl) : Pos :=
  s.mkPos (base + (renderText (declTokens (s.db.frameFloatVars s.db.frame) ds)).size)

/-- **Running the rendered tokens.** At a state between statements that satisfies the parser and
source invariants, the rendered declarations of admissible dummies run as `declareDummies`; the
rendered `$p` statement then runs without error iff `ProofAccepted` holds, and in that case ends
with exactly the assertion inserted. -/
theorem runTokens_render (s : ParserState) (base : Nat) (ds : List DummyDecl) (label : String)
    (f : Verify.Formula) (proof : Array String) (frImpl : Verify.Frame)
    (h_pinv : ParserStateInv s) (h_sinv : SourceInv s) (h_start : s.tokp = .start)
    (h_err : s.db.error? = none) (h_label : s.db.find? label = none)
    (h_head : f.hasConstHead = true) (h_decl : FormulaSymbolsDeclared s.db f)
    (h_trim : s.db.trimFrame' f = .ok frImpl) (h_adm : Admissible s ds label f proof) :
    ((runTokens s base (renderTokens (s.db.frameFloatVars s.db.frame) ds label f proof)).db.error?
        = none ↔
      ProofAccepted (s.withDB (·.declareDummies (labelPos s base ds) ds)) (labelPos s base ds)
        label f proof) ∧
    (ProofAccepted (s.withDB (·.declareDummies (labelPos s base ds) ds)) (labelPos s base ds)
        label f proof →
      runTokens s base (renderTokens (s.db.frameFloatVars s.db.frame) ds label f proof) =
        { s with
          tokp := .start
          db := (s.db.declareDummies (labelPos s base ds) ds).insert (labelPos s base ds) label
            (.assert f frImpl) }) := by
  have h_wf : WellFormedDB s.db := h_pinv.1
  have h_sc : WellScopedDB s.db := h_pinv.2.1.1
  have h_keys : KeysAreTokens s.db := h_sinv.1
  have h_act : FloatVarsActive s.db := h_sinv.2.1
  have h_decl_run : runTokens s base (declTokens (s.db.frameFloatVars s.db.frame) ds) =
      s.withDB (·.declareDummies (labelPos s base ds) ds) :=
    runTokens_declTokens s base _ label ds h_pinv h_keys h_act h_start h_err h_adm.fresh
      h_adm.var_token h_adm.lbl_token
  have h_err1 : (s.db.declareDummies (labelPos s base ds) ds).error? = none :=
    declareDummies_error s.db _ label ds h_err h_wf h_sc h_adm.fresh
  have h_split : runTokens s base (renderTokens (s.db.frameFloatVars s.db.frame) ds label f
      proof) = runTokens (s.withDB (·.declareDummies (labelPos s base ds) ds))
        (base + (renderText (declTokens (s.db.frameFloatVars s.db.frame) ds)).size)
        (thmTokens label f proof) := by
    rw [renderTokens, runTokens_append s base _ _ (Or.inl h_err), h_decl_run]
    simp [ParserState.withDB, h_err1]
  obtain ⟨frAct, h_frAct⟩ := Kernel.toFrame_some_of_wfFrame s.db h_wf.1
  have hD := dummiesDeclared_of_fresh s (labelPos s base ds) label ds frAct h_pinv h_start
    h_err h_label h_adm.fresh h_frAct
  have h_trim1 := trimFrame'_declareDummies s _ label ds frAct f frImpl h_wf h_sc h_decl
    h_adm.fresh hD h_trim
  have h_decl1 := formulaSymbolsDeclared_mono hD.mono h_decl
  have h_active1 : ∀ v, Verify.Sym.var v ∈ f.toList →
      (s.db.declareDummies (labelPos s base ds) ds).isActiveVar v = true := fun v hv =>
    declareDummies_isActiveVar s.db _ label ds h_err h_wf h_sc h_adm.fresh
      (claimVars_active_of_trim s.db f frImpl h_wf h_sc h_act h_head h_decl h_trim v hv)
  have h_thm := runTokens_thmTokens_iff (s.withDB (·.declareDummies (labelPos s base ds) ds))
    (base + (renderText (declTokens (s.db.frameFloatVars s.db.frame) ds)).size) label f proof
    h_start h_err1 h_adm.label_token h_adm.claim_tokens h_adm.proof_tokens h_decl1 h_active1
  refine ⟨?_, fun h_acc => ?_⟩
  · rw [h_split]
    exact h_thm
  · have h_run := runTokens_thmTokens_eq
      (s.withDB (·.declareDummies (labelPos s base ds) ds))
      (base + (renderText (declTokens (s.db.frameFloatVars s.db.frame) ds)).size) label f
      proof frImpl h_start h_err1 hD.label h_adm.label_token h_adm.claim_tokens
      h_adm.proof_tokens h_decl1 h_active1 h_acc h_trim1
    rw [h_split, h_run]
    rfl

/-- **Reading a rendered continuation.** At a clean checkpoint of an error-free read of source
text, the parser reads the rendered declarations of admissible dummies as `declareDummies`. It then
reads the rendered `$p` statement without error iff `ProofAccepted` holds, and in that case ends
with exactly the assertion inserted. -/
theorem afterSource_render (config : ModeConfig) (arr : ByteArray) (ds : List DummyDecl)
    (label : String) (f : Verify.Formula) (proof : Array String) (frImpl : Verify.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_adm : Admissible (afterSource config arr) ds label f proof) :
    ((afterSource config (arr ++ render (afterSource config arr) ds label f proof)).db.error? =
        none ↔
      ProofAccepted ((afterSource config arr).withDB
          (·.declareDummies (labelPos (afterSource config arr) arr.size ds) ds))
        (labelPos (afterSource config arr) arr.size ds) label f proof) ∧
    (ProofAccepted ((afterSource config arr).withDB
          (·.declareDummies (labelPos (afterSource config arr) arr.size ds) ds))
        (labelPos (afterSource config arr) arr.size ds) label f proof →
      afterSource config (arr ++ render (afterSource config arr) ds label f proof) =
        { afterSource config arr with
          tokp := .start
          db := ((afterSource config arr).db.declareDummies
              (labelPos (afterSource config arr) arr.size ds) ds).insert
            (labelPos (afterSource config arr) arr.size ds) label (.assert f frImpl) }) := by
  obtain ⟨h_pinv, h_sinv, _⟩ := afterSource_invariants config arr h_no_dup h_err
  have h_lex := fun t ht => (renderTokens_rendered
    (seen := (afterSource config arr).db.frameFloatVars (afterSource config arr).db.frame)
    (frameFloatVars_tokens h_sinv.1 h_sinv.2.1 h_pinv.2.2.1.2.2.2.1)
    h_adm.var_token h_adm.lbl_token h_adm.tc_token h_adm.label_token h_adm.claim_tokens
    h_adm.proof_tokens t ht).lexical
  obtain ⟨h_iff, h_eq⟩ := afterSource_append_renderText config arr _ h_err h_ws h_lex
  obtain ⟨H1, H2⟩ := runTokens_render (afterSource config arr) arr.size ds label f proof frImpl
    h_pinv h_sinv h_start h_err h_label h_head h_decl h_trim h_adm
  exact ⟨h_iff.trans H1, fun h => (h_eq (Or.inr (H1.mpr h))).trans (H2 h)⟩

/-! ## Completeness for source text -/

/-- The parser reads the source text `text` after `arr` without error, ends between tokens and
statements, stores `label` as the assertion `f` with the frame `frImpl`, and records no new
incomplete proof. -/
structure SourceAccepts (config : ModeConfig) (arr text : ByteArray) (label : String)
    (f : Verify.Formula) (frImpl : Verify.Frame) : Prop where
  error : (afterSource config (arr ++ text)).db.error? = none
  start : (afterSource config (arr ++ text)).tokp = .start
  ws : (afterSource config (arr ++ text)).charp = .ws
  stored : (afterSource config (arr ++ text)).db.find? label = some (.assert f frImpl label)
  complete : (afterSource config (arr ++ text)).db.incompleteProofs =
    (afterSource config arr).db.incompleteProofs

/-- The state `afterSource_render` ends in satisfies `SourceAccepts`. -/
theorem sourceAccepts_of_eq {config : ModeConfig} {arr text : ByteArray} {label : String}
    {f : Verify.Formula} {frImpl : Verify.Frame} {pos : Pos} {ds : List DummyDecl}
    (h_ws : (afterSource config arr).charp = .ws)
    (h_err1 : ((afterSource config arr).db.declareDummies pos ds).error? = none)
    (h_fresh1 : ((afterSource config arr).db.declareDummies pos ds).find? label = none)
    (h_eq : afterSource config (arr ++ text) =
      { afterSource config arr with
        tokp := .start
        db := ((afterSource config arr).db.declareDummies pos ds).insert pos label
          (.assert f frImpl) }) :
    SourceAccepts config arr text label f frImpl where
  error := by
    rw [h_eq]
    show (DB.insert _ _ _ _).error? = none
    rw [insert_assert_fresh_eq _ _ _ _ _ h_fresh1 h_err1]
    exact h_err1
  start := by rw [h_eq]
  ws := by rw [h_eq]; exact h_ws
  stored := by
    rw [h_eq]
    show (DB.insert _ _ _ _).find? label = _
    rw [find?_insert_assert _ _ _ _ _ h_err1 h_fresh1, if_pos rfl]
  complete := by
    rw [h_eq]
    show (DB.insert _ _ _ _).incompleteProofs = _
    rw [insert_incompleteProofs, declareDummies_incompleteProofs]

/-- **Completeness for source text.** Let the parser read the source text `arr` from the start
without error, in a mode without duplicate `$f` statements, ending at a clean checkpoint: between
statements, with no token pending. Let `label` be a fresh label token and `f` a claim with a
constant head and declared symbols, whose frame trims to `frImpl` with stored statement `fr`.

The stored statement is provable in Mario Carneiro's semantics from the assertions read so far iff
some admissible dummy declarations and normal proof render to source text that the parser reads
after `arr` without error, ending at a clean checkpoint with `label` stored as `f` with the frame
`frImpl` and no new incomplete proof. -/
theorem statementProvable_iff_sourceAccepts (config : ModeConfig) (arr : ByteArray)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none) (h_label_tok : IsLabelToken label)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr) :
    (statementOfFrame fr (toExpr f)).Provable
        (dbToAxioms (toDatabaseTotal (afterSource config arr).db)) ↔
      ∃ ds proof, Admissible (afterSource config arr) ds label f proof ∧
        SourceAccepts config arr (render (afterSource config arr) ds label f proof) label f
          frImpl := by
  obtain ⟨h_pinv, h_sinv, h_dv⟩ := afterSource_invariants config arr h_no_dup h_err
  have h_wf : WellFormedDB (afterSource config arr).db := h_pinv.1
  have h_sc : WellScopedDB (afterSource config arr).db := h_pinv.2.1.1
  constructor
  · intro h_prov
    obtain ⟨ds, h_fresh, h_names, proof, h_acc⟩ :=
      acceptedWithGeneratedDummies_of_statementProvable (afterSource config arr) ⟨0, 0⟩ label f
        frImpl fr h_pinv h_start h_err h_sinv.2.2.1 h_label h_head h_decl h_trim h_fr h_dv h_prov
    have h_var : ∀ d ∈ ds, IsMathToken d.var := fun d hd => by
      obtain ⟨⟨b, i, h⟩, _⟩ := h_names d hd
      rw [h]
      exact isMathToken_dummyName b i
    have h_lbl : ∀ d ∈ ds, IsLabelToken d.lbl := fun d hd => by
      obtain ⟨_, b, i, h⟩ := h_names d hd
      rw [h]
      exact isLabelToken_dummyLabel b i
    have h_keys1 := keysAreTokens_declareDummies _ ⟨0, 0⟩ label ds h_err h_wf h_sc h_fresh
      h_sinv.1 h_var h_lbl
    have h_adm : Admissible (afterSource config arr) ds label f proof :=
      { fresh := h_fresh
        var_token := h_var
        lbl_token := h_lbl
        tc_token := fun d hd => isMathToken_of_isConst h_sinv.1 (h_fresh.tc_const d hd)
        label_token := h_label_tok
        claim_tokens := claim_tokens_of_declared h_sinv.1 h_decl
        proof_tokens := by
          obtain ⟨_, _, _, pr, _, h_fold, _⟩ := h_acc
          exact proof_tokens_of_foldlM _ h_keys1 proof _ pr h_fold }
    refine ⟨ds, proof, h_adm, ?_⟩
    -- The declarations do not depend on the position they are given.
    have h_same : ∀ q q' : Pos, (afterSource config arr).withDB (·.declareDummies q ds) =
        (afterSource config arr).withDB (·.declareDummies q' ds) := fun q q' =>
      (runTokens_declTokens _ arr.size q label ds h_pinv h_sinv.1 h_sinv.2.1 h_start h_err h_fresh
          h_var h_lbl).symm.trans
        (runTokens_declTokens _ arr.size q' label ds h_pinv h_sinv.1 h_sinv.2.1 h_start h_err
          h_fresh h_var h_lbl)
    have h_err1 := declareDummies_error _ (labelPos (afterSource config arr) arr.size ds) label ds
      h_err h_wf h_sc h_fresh
    obtain ⟨frAct, h_frAct⟩ := Kernel.toFrame_some_of_wfFrame _ h_wf.1
    have hD := dummiesDeclared_of_fresh (afterSource config arr)
      (labelPos (afterSource config arr) arr.size ds) label ds frAct h_pinv h_start h_err h_label
      h_fresh h_frAct
    rw [h_same ⟨0, 0⟩ (labelPos (afterSource config arr) arr.size ds)] at h_acc
    have h_acc' := proofAccepted_pos (pos' := labelPos (afterSource config arr) arr.size ds)
      hD.label h_err1 h_acc
    exact sourceAccepts_of_eq h_ws h_err1 hD.label
      ((afterSource_render config arr ds label f proof frImpl h_no_dup h_err h_start h_ws h_label
        h_head h_decl h_trim h_adm).2 h_acc')
  · rintro ⟨ds, proof, h_adm, h_acc⟩
    have h_pa := (afterSource_render config arr ds label f proof frImpl h_no_dup h_err h_start
      h_ws h_label h_head h_decl h_trim h_adm).1.mp h_acc.error
    exact statementProvable_of_acceptedWithDummies (afterSource config arr)
      (labelPos (afterSource config arr) arr.size ds) label f frImpl fr h_pinv h_start h_err
      h_label h_decl h_trim h_fr h_dv ⟨ds, h_adm.fresh, proof, h_pa⟩

/-! ## What the continuation changes -/

/-- **The declarations keep the assertions.** After the rendered declarations of fresh dummies,
the parser has no error, the assertion database is that of the prefix, and the claim's frame still
trims to `frImpl`: no mandatory hypothesis or `$d` condition of the target changes. -/
theorem afterSource_declTokens (config : ModeConfig) (arr : ByteArray) (ds : List DummyDecl)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fresh : DummyDeclsFresh (afterSource config arr).db label ds)
    (h_var : ∀ d ∈ ds, IsMathToken d.var) (h_lbl : ∀ d ∈ ds, IsLabelToken d.lbl) :
    (afterSource config (arr ++ renderText (declTokens
        ((afterSource config arr).db.frameFloatVars (afterSource config arr).db.frame) ds))).db.error?
        = none ∧
    toDatabaseTotal (afterSource config (arr ++ renderText (declTokens
        ((afterSource config arr).db.frameFloatVars (afterSource config arr).db.frame) ds))).db =
      toDatabaseTotal (afterSource config arr).db ∧
    (afterSource config (arr ++ renderText (declTokens
        ((afterSource config arr).db.frameFloatVars (afterSource config arr).db.frame) ds))).db.trimFrame'
        f = .ok frImpl := by
  obtain ⟨h_pinv, h_sinv, _⟩ := afterSource_invariants config arr h_no_dup h_err
  have h_wf : WellFormedDB (afterSource config arr).db := h_pinv.1
  have h_sc : WellScopedDB (afterSource config arr).db := h_pinv.2.1.1
  obtain ⟨_, h_eq⟩ := afterSource_append_renderText config arr _ h_err h_ws
    fun t ht => (declTokens_rendered (frameFloatVars_tokens h_sinv.1 h_sinv.2.1
      h_pinv.2.2.1.2.2.2.1) h_var h_lbl
      (fun d hd => isMathToken_of_isConst h_sinv.1 (h_fresh.tc_const d hd)) t ht).lexical
  have h_run := runTokens_declTokens _ arr.size ⟨0, 0⟩ label ds h_pinv h_sinv.1 h_sinv.2.1 h_start
    h_err h_fresh h_var h_lbl
  have h_err1 := declareDummies_error _ ⟨0, 0⟩ label ds h_err h_wf h_sc h_fresh
  obtain ⟨frAct, h_frAct⟩ := Kernel.toFrame_some_of_wfFrame _ h_wf.1
  have hD := dummiesDeclared_of_fresh (afterSource config arr) ⟨0, 0⟩ label ds frAct h_pinv h_start
    h_err h_label h_fresh h_frAct
  rw [h_eq (Or.inr (by rw [h_run]; exact h_err1)), h_run]
  exact ⟨h_err1, hD.toDB, trimFrame'_declareDummies _ _ label ds frAct f frImpl h_wf h_sc h_decl
    h_fresh hD h_trim⟩

/-- **Exactly one new assertion.** After an accepted rendered continuation, the assertion database
is that of the prefix with the claim's stored statement added under `label`, and every object of
the prefix keeps its lookup. -/
theorem sourceAccepts_toDatabaseTotal (config : ModeConfig) (arr : ByteArray)
    (ds : List DummyDecl) (label : String) (f : Verify.Formula) (proof : Array String)
    (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr)
    (h_adm : Admissible (afterSource config arr) ds label f proof)
    (h_acc : SourceAccepts config arr (render (afterSource config arr) ds label f proof) label f
      frImpl) :
    toDatabaseTotal (afterSource config (arr ++ render (afterSource config arr) ds label f proof)).db
        label = some (fr, toExpr f) ∧
    (∀ l, l ≠ label →
      toDatabaseTotal (afterSource config (arr ++ render (afterSource config arr) ds label f
        proof)).db l = toDatabaseTotal (afterSource config arr).db l) ∧
    (∀ l o, (afterSource config arr).db.find? l = some o →
      (afterSource config (arr ++ render (afterSource config arr) ds label f proof)).db.find? l =
        some o) := by
  obtain ⟨h_pinv, _, _⟩ := afterSource_invariants config arr h_no_dup h_err
  have h_wf : WellFormedDB (afterSource config arr).db := h_pinv.1
  have h_sc : WellScopedDB (afterSource config arr).db := h_pinv.2.1.1
  obtain ⟨h_iff, h_run⟩ := afterSource_render config arr ds label f proof frImpl h_no_dup h_err
    h_start h_ws h_label h_head h_decl h_trim h_adm
  rw [h_run (h_iff.mp h_acc.error)]
  obtain ⟨frAct, h_frAct⟩ := Kernel.toFrame_some_of_wfFrame _ h_wf.1
  have hD := dummiesDeclared_of_fresh (afterSource config arr)
    (labelPos (afterSource config arr) arr.size ds) label ds frAct h_pinv h_start h_err h_label
    h_adm.fresh h_frAct
  have h_err1 := declareDummies_error _ (labelPos (afterSource config arr) arr.size ds) label ds
    h_err h_wf h_sc h_adm.fresh
  have h_fr1 := Metamath.StoredStatementSoundness.Runtime.toFrame_stable_of_find_mono _ _ frImpl fr
    hD.mono h_fr
  obtain ⟨h_new, h_old⟩ := toDatabaseTotal_insert_assert _ _ label f frImpl fr h_err1 hD.inv.1
    hD.label (Kernel.hasConstHead_true_size_pos h_head) h_fr1
  refine ⟨h_new, fun l hl => (h_old l hl).trans (congrFun hD.toDB l), fun l o h_find => ?_⟩
  show (DB.insert _ _ _ _).find? l = some o
  have hl : l ≠ label := fun h => by rw [h, h_label] at h_find; cases h_find
  rw [find?_insert_assert _ _ _ _ _ h_err1 hD.label, if_neg hl]
  exact hD.mono l o h_find

/-! ## The complete file -/

/-- An error in the text read so far is not undone by reading more. -/
theorem afterSource_error_of_append (config : ModeConfig) (A B : ByteArray)
    (h : (afterSource config (A ++ B)).db.error? = none) :
    (afterSource config A).db.error? = none := by
  rw [afterSource_eq_feed] at h ⊢
  rcases feed_sim ByteArray.empty A B 0 _ 0 rfl (Nat.zero_le _) .ws .ws _ .ws with
    ⟨_, h2⟩ | ⟨t, rsE, rsE', _, _, h1, h2⟩
  · simp only [ByteArray.size_empty, Nat.add_zero, ByteArray.empty_append] at h2
    rw [h] at h2
    exact absurd h2 (by simp)
  · simp only [ByteArray.size_empty, Nat.add_zero, ByteArray.empty_append] at h1 h2
    rw [h1]
    show t.db.error? = none
    rw [h2] at h
    by_contra h_t
    exact Metamath.ParserLoopInduction.feed_stops_on_error 0 (A ++ B) A.size rsE' t h_t h

/-- At the end of the text, an error-free clean checkpoint with no open block passes `checkBytes`
unchanged, post-checks included. -/
theorem checkBytes_of_clean (config : ModeConfig) (bytes : ByteArray)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config bytes).db.error? = none)
    (h_start : (afterSource config bytes).tokp = .start)
    (h_ws : (afterSource config bytes).charp = .ws)
    (h_sc : (afterSource config bytes).db.scopes.size = 0) :
    checkBytes bytes config = (afterSource config bytes).db := by
  have h_core : checkBytesCore bytes config = (afterSource config bytes).db :=
    done_of_clean (afterSource config bytes) bytes.size h_ws h_start h_sc
  have h_wf : (afterSource config bytes).db.wellFormed? = true :=
    WF.wellFormed?_of_wellFormedDB (afterSource_invariants config bytes h_no_dup h_err).1.1
  have h_dv := AssertDv.checkBytesCore_assertDvVarsInFrame?_eq_true bytes config
    (h_core ▸ h_err)
  have h_cfg := checkBytesCore_config bytes config
  unfold checkBytes
  rw [h_core] at h_dv h_cfg ⊢
  simp [h_err, h_wf, h_dv]

/-- `checkBytes` has no error only if the text is read without error. -/
theorem afterSource_error_of_checkBytes (config : ModeConfig) (bytes : ByteArray)
    (h : (checkBytes bytes config).error? = none) :
    (afterSource config bytes).db.error? = none := by
  have h_core : (checkBytesCore bytes config).error? = none := by
    by_contra h_c
    unfold checkBytes at h
    simp only [h_c, if_false] at h
  exact ParserOps.done_no_error_implies_db_no_error (afterSource config bytes) bytes.size h_core

/-- `checkBytes` accepts the complete file `bytes`, stores `label` as the assertion `f` with the
frame `frImpl`, and lists exactly the incomplete proofs `incomplete`. -/
structure FileAccepts (config : ModeConfig) (bytes : ByteArray) (label : String)
    (f : Verify.Formula) (frImpl : Verify.Frame) (incomplete : Array String) : Prop where
  error : (checkBytes bytes config).error? = none
  stored : (checkBytes bytes config).find? label = some (.assert f frImpl label)
  complete : (checkBytes bytes config).incompleteProofs = incomplete

/-- **Completeness for complete files.** Under the premises of
`statementProvable_iff_sourceAccepts`, the stored statement is provable in Mario Carneiro's
semantics iff some admissible dummy declarations and normal proof render to text that, followed by
one `$}` for each open block, completes `arr` to a file that `checkBytes` accepts, with `label`
stored as `f` with the frame `frImpl` and no new incomplete proof. -/
theorem statementProvable_iff_fileAccepts (config : ModeConfig) (arr : ByteArray)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none) (h_label_tok : IsLabelToken label)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr) :
    (statementOfFrame fr (toExpr f)).Provable
        (dbToAxioms (toDatabaseTotal (afterSource config arr).db)) ↔
      ∃ ds proof, Admissible (afterSource config arr) ds label f proof ∧
        FileAccepts config (arr ++ render (afterSource config arr) ds label f proof ++
            closeBlocks (afterSource config arr).db.scopes.size) label f frImpl
          (afterSource config arr).db.incompleteProofs := by
  rw [statementProvable_iff_sourceAccepts config arr label f frImpl fr h_no_dup h_err h_start h_ws
    h_label h_label_tok h_head h_decl h_trim h_fr]
  obtain ⟨h_pinv, _, _⟩ := afterSource_invariants config arr h_no_dup h_err
  have h_wf : WellFormedDB (afterSource config arr).db := h_pinv.1
  have h_sc : WellScopedDB (afterSource config arr).db := h_pinv.2.1.1
  refine exists_congr fun ds => exists_congr fun proof => and_congr_right fun h_adm => ?_
  obtain ⟨h_iff, h_run⟩ := afterSource_render config arr ds label f proof frImpl h_no_dup h_err
    h_start h_ws h_label h_head h_decl h_trim h_adm
  constructor
  · intro h_acc
    -- the continuation leaves the block structure of the prefix
    have h_scopes : (afterSource config (arr ++ render (afterSource config arr) ds label f
        proof)).db.scopes = (afterSource config arr).db.scopes := by
      rw [h_run (h_iff.mp h_acc.error)]
      have h_err1 := declareDummies_error _ (labelPos (afterSource config arr) arr.size ds) label ds
        h_err h_wf h_sc h_adm.fresh
      obtain ⟨frAct, h_frAct⟩ := Kernel.toFrame_some_of_wfFrame _ h_wf.1
      have hD := dummiesDeclared_of_fresh (afterSource config arr)
        (labelPos (afterSource config arr) arr.size ds) label ds frAct h_pinv h_start h_err h_label
        h_adm.fresh h_frAct
      show (DB.insert _ _ _ _).scopes = _
      rw [insert_assert_fresh_eq _ _ _ _ _ hD.label h_err1]
      exact (declareDummies_fields _ _ label ds h_err h_wf h_sc h_adm.fresh).2.2.1
    have h_close := runTokens_close (afterSource config arr).db.scopes.size
      (afterSource config (arr ++ render (afterSource config arr) ds label f proof))
      (arr ++ render (afterSource config arr) ds label f proof).size h_acc.start h_acc.error
      (by rw [h_scopes]; exact Nat.le_refl _)
    obtain ⟨c_err, c_start, c_obj, c_inc, c_sc, c_ws⟩ := h_close
    obtain ⟨_, h_eq⟩ := afterSource_append_renderText config
      (arr ++ render (afterSource config arr) ds label f proof)
      (List.replicate (afterSource config arr).db.scopes.size "$}") h_acc.error h_acc.ws
      (fun t ht => (closeTokens_rendered _ t ht).lexical)
    have h_file := h_eq (Or.inr c_err)
    have h_check := checkBytes_of_clean config (arr ++ render (afterSource config arr) ds label f
        proof ++ closeBlocks (afterSource config arr).db.scopes.size) h_no_dup
      (by unfold closeBlocks; rw [h_file]; exact c_err)
      (by unfold closeBlocks; rw [h_file]; exact c_start)
      (by unfold closeBlocks; rw [h_file, c_ws]; exact h_acc.ws)
      (by unfold closeBlocks; rw [h_file, c_sc, h_scopes]; simp)
    refine ⟨?_, ?_, ?_⟩
    · rw [h_check]; unfold closeBlocks; rw [h_file]; exact c_err
    · rw [h_check]; unfold closeBlocks; rw [h_file]
      simp only [DB.find?, c_obj]
      exact h_acc.stored
    · rw [h_check]; unfold closeBlocks; rw [h_file, c_inc]
      exact h_acc.complete
  · intro h_file
    have h_prefix := afterSource_error_of_append config _ _
      (afterSource_error_of_checkBytes config _ h_file.error)
    have h_pa := h_iff.mp h_prefix
    have h_eq := h_run h_pa
    have h_err1 := declareDummies_error _ (labelPos (afterSource config arr) arr.size ds) label ds
      h_err h_wf h_sc h_adm.fresh
    obtain ⟨frAct, h_frAct⟩ := Kernel.toFrame_some_of_wfFrame _ h_wf.1
    have hD := dummiesDeclared_of_fresh (afterSource config arr)
      (labelPos (afterSource config arr) arr.size ds) label ds frAct h_pinv h_start h_err h_label
      h_adm.fresh h_frAct
    exact sourceAccepts_of_eq h_ws h_err1 hD.label h_eq

/-! ## Mario Carneiro's original `ax` rule

`DeclarativeSpec.lean` restricts the typing premise of the `ax` rule to the variables of the
applied statement, the book's clause C.2.5 2(a). `Spec/DeclarativeOriginal.lean` keeps Mario
Carneiro's original rule, which types every variable, and proves the two agree on trimmed axiom
sets, which the translated databases are. -/

/-- `statementProvable_iff_sourceAccepts` for Mario Carneiro's original `ax` rule. -/
theorem statementProvable_iff_sourceAccepts_originalRule (config : ModeConfig) (arr : ByteArray)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none) (h_label_tok : IsLabelToken label)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr) :
    Spec.DeclarativeOriginal.StatementProvable
        (dbToAxioms (toDatabaseTotal (afterSource config arr).db))
        (statementOfFrame fr (toExpr f)) ↔
      ∃ ds proof, Admissible (afterSource config arr) ds label f proof ∧
        SourceAccepts config arr (render (afterSource config arr) ds label f proof) label f
          frImpl :=
  (Spec.DeclarativeOriginal.statementProvable_iff
      (fun _ h => Spec.Equivalence.dbToAxioms_trimmed h)).trans
    (statementProvable_iff_sourceAccepts config arr label f frImpl fr h_no_dup h_err h_start
      h_ws h_label h_label_tok h_head h_decl h_trim h_fr)

/-- `statementProvable_iff_fileAccepts` for Mario Carneiro's original `ax` rule. -/
theorem statementProvable_iff_fileAccepts_originalRule (config : ModeConfig) (arr : ByteArray)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none) (h_label_tok : IsLabelToken label)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr) :
    Spec.DeclarativeOriginal.StatementProvable
        (dbToAxioms (toDatabaseTotal (afterSource config arr).db))
        (statementOfFrame fr (toExpr f)) ↔
      ∃ ds proof, Admissible (afterSource config arr) ds label f proof ∧
        FileAccepts config (arr ++ render (afterSource config arr) ds label f proof ++
            closeBlocks (afterSource config arr).db.scopes.size) label f frImpl
          (afterSource config arr).db.incompleteProofs :=
  (Spec.DeclarativeOriginal.statementProvable_iff
      (fun _ h => Spec.Equivalence.dbToAxioms_trimmed h)).trans
    (statementProvable_iff_fileAccepts config arr label f frImpl fr h_no_dup h_err h_start
      h_ws h_label h_label_tok h_head h_decl h_trim h_fr)

/-- **Verified files.** When the prefix records no incomplete proof, the complete file is verified:
`checkBytes` reports no error and no incomplete proof, with `label` stored as `f`. -/
theorem fileAccepts_verified {config : ModeConfig} {bytes : ByteArray} {label : String}
    {f : Verify.Formula} {frImpl : Verify.Frame}
    (h : FileAccepts config bytes label f frImpl #[]) :
    (checkBytes bytes config).error? = none ∧ (checkBytes bytes config).incompleteProofs = #[] :=
  ⟨h.error, h.complete⟩

/-! ## The checker's entry point -/

/-- **Completeness for the checker's entry point.** Under the premises of
`statementProvable_iff_sourceAccepts`, if the stored statement is provable, then some admissible
dummy declarations and normal proof complete `arr` to a file such that, whenever the root file
`fname` resolves and reads as exactly that file, `Verify.check fname config` returns the database
`checkBytes` returns for it, which accepts the file (`FileAccepts`). -/
theorem check_accepts_of_statementProvable (config : ModeConfig) (arr : ByteArray)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (fname : String) (h_depth : config.maxIncludeDepth ≠ 0)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none) (h_label_tok : IsLabelToken label)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr)
    (h_prov : (statementOfFrame fr (toExpr f)).Provable
      (dbToAxioms (toDatabaseTotal (afterSource config arr).db))) :
    ∃ ds proof, Admissible (afterSource config arr) ds label f proof ∧
      ∀ w w₁ w₂ : Void IO.RealWorld,
        RootFileCheck.RootResolves (fun path => IO.FS.realPath path) fname
          config.literalIncludePaths w w₁ →
        IO.FS.readBinFile fname w₁ = .ok (arr ++ render (afterSource config arr) ds label f proof ++
          closeBlocks (afterSource config arr).db.scopes.size) w₂ →
        check fname config w = .ok (checkBytes (arr ++ render (afterSource config arr) ds label f
          proof ++ closeBlocks (afterSource config arr).db.scopes.size) config) w₂ ∧
        FileAccepts config (arr ++ render (afterSource config arr) ds label f proof ++
          closeBlocks (afterSource config arr).db.scopes.size) label f frImpl
          (afterSource config arr).db.incompleteProofs := by
  obtain ⟨ds, proof, h_adm, h_file⟩ := (statementProvable_iff_fileAccepts config arr label f frImpl
    fr h_no_dup h_err h_start h_ws h_label h_label_tok h_head h_decl h_trim h_fr).mp h_prov
  exact ⟨ds, proof, h_adm, fun w w₁ w₂ h_path h_read =>
    ⟨RootFileCheck.check_eq_checkBytes_of_ok fname config _ w w₁ w₂ h_depth h_path h_read
      h_file.error, h_file⟩⟩

/-- **Soundness for complete files.** Under the premises of `statementProvable_iff_sourceAccepts`,
if `checkBytes` reports no error on the file completed by admissible dummy declarations and a normal
proof, the stored statement is provable. -/
theorem statementProvable_of_checkBytes (config : ModeConfig) (arr : ByteArray)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr)
    (ds : List DummyDecl) (proof : Array String)
    (h_adm : Admissible (afterSource config arr) ds label f proof)
    (h_ok : (checkBytes (arr ++ render (afterSource config arr) ds label f proof ++
      closeBlocks (afterSource config arr).db.scopes.size) config).error? = none) :
    (statementOfFrame fr (toExpr f)).Provable
      (dbToAxioms (toDatabaseTotal (afterSource config arr).db)) := by
  obtain ⟨h_pinv, _, h_dv⟩ := afterSource_invariants config arr h_no_dup h_err
  have h_prefix := afterSource_error_of_append config _ _
    (afterSource_error_of_checkBytes config _ h_ok)
  have h_pa := (afterSource_render config arr ds label f proof frImpl h_no_dup h_err h_start h_ws
    h_label h_head h_decl h_trim h_adm).1.mp h_prefix
  exact statementProvable_of_acceptedWithDummies (afterSource config arr)
    (labelPos (afterSource config arr) arr.size ds) label f frImpl fr h_pinv h_start h_err h_label
    h_decl h_trim h_fr h_dv ⟨ds, h_adm.fresh, proof, h_pa⟩

/-- **Soundness through the checker's entry point.** Under the premises of
`statementProvable_iff_sourceAccepts`, let the root file `fname` resolve and read as exactly the
file completed by admissible dummy declarations and a normal proof. If `Verify.check fname config`
returns a database with no error, the stored statement is provable. -/
theorem statementProvable_of_check (config : ModeConfig) (arr : ByteArray)
    (label : String) (f : Verify.Formula) (frImpl : Verify.Frame) (fr : Spec.Frame)
    (fname : String) (h_depth : config.maxIncludeDepth ≠ 0)
    (h_no_dup : config.allowDuplicateFloat = false)
    (h_err : (afterSource config arr).db.error? = none)
    (h_start : (afterSource config arr).tokp = .start)
    (h_ws : (afterSource config arr).charp = .ws)
    (h_label : (afterSource config arr).db.find? label = none)
    (h_head : f.hasConstHead = true)
    (h_decl : FormulaSymbolsDeclared (afterSource config arr).db f)
    (h_trim : (afterSource config arr).db.trimFrame' f = .ok frImpl)
    (h_fr : toFrame (afterSource config arr).db frImpl = some fr)
    (ds : List DummyDecl) (proof : Array String)
    (h_adm : Admissible (afterSource config arr) ds label f proof)
    (w w₁ w₂ w' : Void IO.RealWorld) (db : DB)
    (h_path : RootFileCheck.RootResolves (fun path => IO.FS.realPath path) fname
      config.literalIncludePaths w w₁)
    (h_read : IO.FS.readBinFile fname w₁ = .ok (arr ++ render (afterSource config arr) ds label f
      proof ++ closeBlocks (afterSource config arr).db.scopes.size) w₂)
    (h_run : check fname config w = .ok db w') (h_ok : db.error? = none) :
    (statementOfFrame fr (toExpr f)).Provable
      (dbToAxioms (toDatabaseTotal (afterSource config arr).db)) := by
  obtain ⟨h_pinv, h_sinv, _⟩ := afterSource_invariants config arr h_no_dup h_err
  have h_bytes : arr ++ render (afterSource config arr) ds label f proof ++
      closeBlocks (afterSource config arr).db.scopes.size =
      arr ++ renderText (renderTokens ((afterSource config arr).db.frameFloatVars
        (afterSource config arr).db.frame) ds label f proof ++
        List.replicate (afterSource config arr).db.scopes.size "$}") := by
    rw [renderText_append, ByteArray.append_assoc]
    rfl
  have h_noreq : ParserOps.ErrorNotRequest (checkBytes (arr ++ render (afterSource config arr) ds
      label f proof ++ closeBlocks (afterSource config arr).db.scopes.size) config).error? := by
    rw [h_bytes]
    refine checkBytes_errorNotRequest config arr _ h_err h_start h_ws fun t ht => ?_
    rcases List.mem_append.mp ht with ht | ht
    · exact renderTokens_rendered (frameFloatVars_tokens h_sinv.1 h_sinv.2.1 h_pinv.2.2.1.2.2.2.1)
        h_adm.var_token h_adm.lbl_token h_adm.tc_token h_adm.label_token h_adm.claim_tokens
        h_adm.proof_tokens t ht
    · exact closeTokens_rendered _ t ht
  obtain ⟨h_db, _⟩ := RootFileCheck.checkBytes_eq_of_check_ok fname config _ w w₁ w₂ w' db h_depth
    h_path h_read h_noreq h_run h_ok
  exact statementProvable_of_checkBytes config arr label f frImpl fr h_no_dup h_err h_start h_ws
    h_label h_head h_decl h_trim h_fr ds proof h_adm (h_db ▸ h_ok)

end Metamath.SourceCompleteness
