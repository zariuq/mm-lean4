import Metamath.SourceCompleteness.Render
import Metamath.SourceCompleteness.Bytes
import Metamath.CheckerCompleteness.Exact

/-!
# Running the tokens of a `$p` statement

`runTokens_thmTokens_iff`: at a parser state between statements, the tokens
`label $p f $= proof $.` of a normal-mode proof run without error iff the parser accepts the proof
(`ProofAccepted`), provided the tokens have the right lexical kinds and the claim's symbols are
declared constants and active variables. `runTokens_thmTokens_eq`: an accepted proof under a fresh
label ends exactly in the state that stores the assertion.

The label's position is the one the proof state records; the positions of the later tokens enter
only error messages. The first proof step starts the normal proof (`ptp := .normal`), as in
`ProofAccepted`; the empty proof fails on both sides, since `finishProof` needs a one-element stack.
-/

set_option autoImplicit false

namespace Metamath.SourceCompleteness

open Metamath.Verify Metamath.CheckerCompleteness
open Metamath.WF (FormulaSymbolsDeclared)

/-! ## Running a list of tokens -/

/-- A token that leaves no error: the run continues after it. -/
private theorem runTokens_cons_of_eq (s s' : ParserState) (base : Nat) (t : String)
    (ts : List String) (h : s.feedToken base t.toUTF8.toByteSlice = s') (h' : s'.db.error? = none) :
    runTokens s base (t :: ts) = runTokens s' (base + t.toUTF8.size + 1) ts := by
  simp only [runTokens, h, h', Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/-- A token that sets an error: the run stops there. -/
private theorem runTokens_cons_of_error (s : ParserState) (base : Nat) (t : String)
    (ts : List String) (h : (s.feedToken base t.toUTF8.toByteSlice).db.error? ≠ none) :
    runTokens s base (t :: ts) = s.feedToken base t.toUTF8.toByteSlice := by
  have h' : (s.feedToken base t.toUTF8.toByteSlice).db.error?.isSome = true :=
    Option.isSome_iff_ne_none.mpr h
  simp only [runTokens, h', ↓reduceIte]

private theorem runTokens_singleton (s : ParserState) (base : Nat) (t : String) :
    runTokens s base [t] = s.feedToken base t.toUTF8.toByteSlice := by
  simp only [runTokens]
  split <;> rfl

/-! ## One token -/

/-- A label token at the start of a statement is recorded with its position. -/
private theorem feedToken_start_label (s : ParserState) (b : Nat) (label : String) {tk : ByteSlice}
    (h : tk.bytes = label.toUTF8.toList) (h_start : s.tokp = .start)
    (h_label : IsLabelToken label) :
    s.feedToken b tk = { s with tokp := .label (s.mkPos b) label } := by
  obtain ⟨hl, -⟩ := spells_label h_label h
  have h1 : label ≠ "$(" := h_label.ne (by decide)
  have h2 : label ≠ "$[" := h_label.ne (by decide)
  simp [ParserState.feedToken, h_start, spells_eqArray h, h1, h2,
    spells_label_head h_label h, ParserState.label, hl]

/-- `$p` after a label opens the claim of a theorem. -/
theorem feedToken_label_p (s : ParserState) (b : Nat) (P : Pos) (label : String)
    {tk : ByteSlice} (h : tk.bytes = "$p".toUTF8.toList) (h_tokp : s.tokp = .label P label) :
    s.feedToken b tk = { s with tokp := .math #[] ⟨.thm, P, label⟩ } := by
  obtain ⟨h1, h2, -, -, h5⟩ := spells_dollar_p h
  simp [ParserState.feedToken, h_tokp, spells_eqArray h, h1, h2, h5]

/-- A math symbol token is not the delimiter of a math string. -/
private theorem spells_math_not_delim {t : String} (ht : IsMathToken t) {tk : ByteSlice}
    (h : tk.bytes = t.toUTF8.toList) (k : TokensKind) : tk.eqArray k.delim = false := by
  have h1 : t ≠ "$=" := ht.ne (by decide)
  have h2 : t ≠ "$." := ht.ne (by decide)
  cases k <;> simp [TokensKind.delim, spells_eqArray h, h1, h2]

/-- A declared constant in a math string is pushed as a constant. -/
private theorem feedToken_math_const (s : ParserState) (b : Nat) (arr : Array Verify.Sym)
    (p : TokensParser) (c : String) {tk : ByteSlice} (h : tk.bytes = c.toUTF8.toList)
    (h_tokp : s.tokp = .math arr p) (hc : IsMathToken c) (h_const : s.db.isConst c = true) :
    s.feedToken b tk = { s with tokp := .math (arr.push (.const c)) p } := by
  obtain ⟨hm, -⟩ := spells_math hc h
  have h1 : c ≠ "$(" := hc.ne (by decide)
  have h2 : c ≠ "$[" := hc.ne (by decide)
  obtain ⟨o, ho⟩ : ∃ o, s.db.find? c = some (.const o) := by
    unfold DB.isConst at h_const
    split at h_const
    · rename_i o h_find
      exact ⟨o, h_find⟩
    · exact absurd h_const (by decide)
  simp [ParserState.feedToken, h_tokp, spells_eqArray h, h1, h2, spells_math_not_delim hc h,
    ParserState.withMath, hm, ho]
  rfl

/-- An active variable in a math string is pushed as a variable. -/
private theorem feedToken_math_var (s : ParserState) (b : Nat) (arr : Array Verify.Sym)
    (p : TokensParser) (v : String) {tk : ByteSlice} (h : tk.bytes = v.toUTF8.toList)
    (h_tokp : s.tokp = .math arr p) (hv : IsMathToken v) (h_act : s.db.isActiveVar v = true) :
    s.feedToken b tk = { s with tokp := .math (arr.push (.var v)) p } := by
  obtain ⟨hm, -⟩ := spells_math hv h
  have h1 : v ≠ "$(" := hv.ne (by decide)
  have h2 : v ≠ "$[" := hv.ne (by decide)
  obtain ⟨o, ho⟩ : ∃ o, s.db.find? v = some (.var o) := by
    have h_var := DB.isActiveVar_isVar h_act
    unfold DB.isVar at h_var
    split at h_var
    · rename_i o h_find
      exact ⟨o, h_find⟩
    · exact absurd h_var (by decide)
  simp [ParserState.feedToken, h_tokp, spells_eqArray h, h1, h2, spells_math_not_delim hv h,
    ParserState.withMath, hm, ho, h_act]
  rfl

/-- `$=` ends the claim of a theorem. -/
theorem feedToken_math_eq (s : ParserState) (b : Nat) (f : Verify.Formula) (P : Pos)
    (label : String) {tk : ByteSlice} (h : tk.bytes = "$=".toUTF8.toList)
    (h_tokp : s.tokp = .math f ⟨.thm, P, label⟩) :
    s.feedToken b tk = s.feedTokens f ⟨.thm, P, label⟩ := by
  simp [ParserState.feedToken, h_tokp, spells_eqArray h, TokensKind.delim]

/-- `finishProof` resets the token parser first, so it ignores the incoming one. -/
theorem finishProof_tokp (s : ParserState) (t : TokenParser) (pr : ProofState) :
    ({ s with tokp := t } : ParserState).finishProof pr = s.finishProof pr := by
  cases pr
  rfl

/-- `$.` ends the proof. -/
theorem feedToken_proof_dot (s : ParserState) (b : Nat) (pr : ProofState) {tk : ByteSlice}
    (h : tk.bytes = "$.".toUTF8.toList) (h_tokp : s.tokp = .proof pr) :
    s.feedToken b tk = s.finishProof pr := by
  simp [ParserState.feedToken, h_tokp, spells_eqArray h]
  exact finishProof_tokp s _ pr

/-- A label token is one step of a normal proof, from the start of the proof or in normal mode. -/
theorem feedProof_go_label (s : ParserState) (pr : ProofState) (l : String) {tk : ByteSlice}
    (h : tk.bytes = l.toUTF8.toList) (hl : IsLabelToken l)
    (h_ptp : pr.ptp = .start ∨ pr.ptp = .normal) :
    ParserState.feedProof.go s tk pr = s.db.stepNormal { pr with ptp := .normal } l := by
  obtain ⟨hlab, -⟩ := spells_label hl h
  have hq : l ≠ "?" := hl.ne (by decide)
  have hp : l ≠ "(" := hl.ne (by decide)
  rcases h_ptp with h_ptp | h_ptp
  · simp [ParserState.feedProof.go, ParserState.feedProof.goNormal, h_ptp, spells_eqArray h, hq,
      hp, hlab]
  · obtain ⟨pos, lab, fmla, fr, heap, stack, ptp, inc⟩ := pr
    simp only at h_ptp
    subst h_ptp
    simp [ParserState.feedProof.go, ParserState.feedProof.goNormal, spells_eqArray h, hq, hlab]

/-- A successful proof step on a label token. -/
theorem feedToken_proof_label_ok (s : ParserState) (b : Nat) (pr pr' : ProofState) (l : String)
    {tk : ByteSlice} (h : tk.bytes = l.toUTF8.toList) (h_tokp : s.tokp = .proof pr)
    (hl : IsLabelToken l) (h_ptp : pr.ptp = .start ∨ pr.ptp = .normal)
    (h_err : s.db.error? = none)
    (h_step : s.db.stepNormal { pr with ptp := .normal } l = .ok pr') :
    s.feedToken b tk = { s with tokp := .proof pr' } := by
  have h1 : l ≠ "$(" := hl.ne (by decide)
  have h2 : l ≠ "$[" := hl.ne (by decide)
  have h3 : l ≠ "$." := hl.ne (by decide)
  simp [ParserState.feedToken, h_tokp, spells_eqArray h, h1, h2, h3, ParserState.feedProof,
    feedProof_go_label (h := h) (hl := hl) (h_ptp := h_ptp), h_step, ParserState.withAt, h_err]

/-- A failed proof step on a label token sets an error. -/
theorem feedToken_proof_label_error (s : ParserState) (b : Nat) (pr : ProofState) (l : String)
    {tk : ByteSlice} (h : tk.bytes = l.toUTF8.toList) (h_tokp : s.tokp = .proof pr)
    (hl : IsLabelToken l) (h_ptp : pr.ptp = .start ∨ pr.ptp = .normal) (e : ProofCheckFail)
    (h_step : s.db.stepNormal { pr with ptp := .normal } l = .error e) :
    (s.feedToken b tk).db.error? ≠ none := by
  have h1 : l ≠ "$(" := hl.ne (by decide)
  have h2 : l ≠ "$[" := hl.ne (by decide)
  have h3 : l ≠ "$." := hl.ne (by decide)
  simp only [ParserState.feedToken, h_tokp, spells_eqArray h, h1, h2, h3, decide_false,
    Bool.false_eq_true, ↓reduceIte, ParserState.feedProof,
    feedProof_go_label (h := h) (hl := hl) (h_ptp := h_ptp), h_step]
  rw [Ne, Metamath.PrefixProvability.Checker.withAt_error?_none_iff]
  simp [ParserState.mkErrorFromEvidence, ParserState.withDB]

/-! ## The claim ends: frame trimming -/

/-- `$=` of a theorem whose claim has a constant head and a trimmed frame, with no interrupt
requested, starts its proof. -/
theorem feedTokens_thm_ok (s : ParserState) (f : Verify.Formula) (P : Pos) (label : String)
    (fr : Frame) (h_head : f.hasConstHead = true) (h_trim : s.db.trimFrame' f = .ok fr)
    (h_int : s.db.interrupt = false) (h_err : s.db.error? = none) :
    s.feedTokens f ⟨.thm, P, label⟩ =
      { s with tokp := .proof (s.db.mkProofState P label f fr) } := by
  simp [ParserState.feedTokens, h_head, h_trim, h_int, ParserState.resumeThm,
    ParserState.withAt, h_err]

/-- `$=` of a theorem succeeds only on a claim with a constant head and a trimmed frame, with no
interrupt requested. -/
theorem feedTokens_thm_of_no_error (s : ParserState) (f : Verify.Formula) (P : Pos)
    (label : String) (h : (s.feedTokens f ⟨.thm, P, label⟩).db.error? = none) :
    f.hasConstHead = true ∧ s.db.interrupt = false ∧ ∃ fr, s.db.trimFrame' f = .ok fr := by
  unfold ParserState.feedTokens at h
  rw [Metamath.PrefixProvability.Checker.withAt_error?_none_iff] at h
  by_cases hh : f.hasConstHead = true
  · cases ht : s.db.trimFrame' f with
    | error e =>
      simp [hh, ht, ParserState.mkErrorFromEvidence, ParserState.withDB] at h
    | ok fr =>
      cases hi : s.db.interrupt with
      | true => simp [hh, ht, hi, ParserState.withDB] at h
      | false => exact ⟨hh, rfl, fr, rfl⟩
  · simp [hh, ParserState.mkErrorFromEvidence, ParserState.withDB] at h

/-! ## The claim -/

/-- The symbol tokens of a claim rebuild it in the math string. -/
private theorem runTokens_math (s : ParserState) (p : TokensParser) (rest : List String)
    (h_err : s.db.error? = none) :
    ∀ (xs : List Verify.Sym) (arr : Array Verify.Sym) (b : Nat),
      (∀ x ∈ xs, IsMathToken x.value) →
      (∀ c, Verify.Sym.const c ∈ xs → s.db.isConst c = true) →
      (∀ v, Verify.Sym.var v ∈ xs → s.db.isActiveVar v = true) →
      ∃ b', runTokens { s with tokp := .math arr p } b (xs.map (·.value) ++ rest) =
        runTokens { s with tokp := .math (arr ++ xs.toArray) p } b' rest
  | [], arr, b, _, _, _ => ⟨b, by simp⟩
  | x :: xs, arr, b, hx, hc, hv => by
    have step : ({ s with tokp := .math arr p } : ParserState).feedToken b
        x.value.toUTF8.toByteSlice = { s with tokp := .math (arr.push x) p } := by
      cases x with
      | const c =>
        exact feedToken_math_const _ b arr p c (ByteSlice.bytes_toByteSlice_self _) rfl
          (hx _ (List.mem_cons_self ..)) (hc c (List.mem_cons_self ..))
      | var v =>
        exact feedToken_math_var _ b arr p v (ByteSlice.bytes_toByteSlice_self _) rfl
          (hx _ (List.mem_cons_self ..)) (hv v (List.mem_cons_self ..))
    obtain ⟨b', hb'⟩ := runTokens_math s p rest h_err xs (arr.push x)
      (b + x.value.toUTF8.size + 1) (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      (fun c hy => hc c (List.mem_cons_of_mem _ hy)) (fun v hy => hv v (List.mem_cons_of_mem _ hy))
    refine ⟨b', ?_⟩
    rw [List.map_cons, List.cons_append, runTokens_cons_of_eq _ _ _ _ _ step h_err, hb']
    simp

/-! ## The proof -/

/-- A successful run of normal proof steps, then `$.`, ends in `finishProof` of the final proof
state. The first step may start the proof. -/
theorem runTokens_proof_ok (s : ParserState) (h_err : s.db.error? = none) :
    ∀ (ls : List String) (pr r : ProofState) (b : Nat), (∀ l ∈ ls, IsLabelToken l) →
      (pr.ptp = .start ∨ pr.ptp = .normal) → (ls ≠ [] ∨ pr.ptp = .normal) →
      ls.foldlM (fun pr l => s.db.stepNormal pr l) { pr with ptp := .normal } = .ok r →
      runTokens { s with tokp := .proof pr } b (ls ++ ["$."]) = s.finishProof r
  | [], pr, r, b, _, _, h_ne, h_fold => by
    have h_ptp : pr.ptp = .normal := h_ne.resolve_left (fun h => h rfl)
    obtain ⟨pos, lab, fmla, fr, heap, stack, ptp, inc⟩ := pr
    simp only at h_ptp
    subst h_ptp
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h_fold
    subst h_fold
    rw [List.nil_append, runTokens_singleton,
      feedToken_proof_dot _ b _ (ByteSlice.bytes_toByteSlice_self _) rfl, finishProof_tokp]
  | l :: ls, pr, r, b, hls, h_ptp, _, h_fold => by
    rw [List.foldlM_cons] at h_fold
    cases h_step : s.db.stepNormal { pr with ptp := .normal } l with
    | error e => simp [h_step, bind, Except.bind] at h_fold
    | ok r₁ =>
      simp only [h_step, bind, Except.bind] at h_fold
      have h_r₁ : r₁.ptp = .normal := by
        rw [stepNormal_ok_shape s.db _ r₁ l h_step]
      have h_eta : { r₁ with ptp := .normal } = r₁ := by
        obtain ⟨pos, lab, fmla, fr, heap, stack, ptp, inc⟩ := r₁
        simp only at h_r₁
        subst h_r₁
        rfl
      have e := feedToken_proof_label_ok { s with tokp := .proof pr } b pr r₁ l
        (ByteSlice.bytes_toByteSlice_self _) rfl (hls l (List.mem_cons_self ..)) h_ptp h_err h_step
      rw [List.cons_append, runTokens_cons_of_eq _ { s with tokp := .proof r₁ } _ _ _ e h_err]
      exact runTokens_proof_ok s h_err ls r₁ r _ (fun l' h' => hls l' (List.mem_cons_of_mem _ h'))
        (Or.inr h_r₁) (Or.inr h_r₁) (h_eta ▸ h_fold)

/-- `finishProof` rejects a proof state still at the start of the proof. -/
theorem finishProof_start_error (s : ParserState) (pr : ProofState) (h : pr.ptp = .start) :
    (s.finishProof pr).db.error? ≠ none := by
  intro h_ok
  obtain ⟨-, -, h_ptp⟩ :=
    Metamath.ParserAnyFormatEquivalence.finishProof_success_stack_conditions s pr h_ok
  rw [h] at h_ptp
  rcases h_ptp with h_ptp | h_ptp | h_ptp <;> exact nomatch h_ptp

/-- An error-free run of proof tokens, then `$.`, is a successful run of normal proof steps, and
not the empty proof at the start of the proof. -/
theorem runTokens_proof_no_error (s : ParserState) (h_err : s.db.error? = none) :
    ∀ (ls : List String) (pr : ProofState) (b : Nat), (∀ l ∈ ls, IsLabelToken l) →
      (pr.ptp = .start ∨ pr.ptp = .normal) →
      (runTokens { s with tokp := .proof pr } b (ls ++ ["$."])).db.error? = none →
      (ls ≠ [] ∨ pr.ptp = .normal) ∧
        ∃ r, ls.foldlM (fun pr l => s.db.stepNormal pr l) { pr with ptp := .normal } = .ok r
  | [], pr, b, _, h_ptp, h_ok => by
    rw [List.nil_append, runTokens_singleton,
      feedToken_proof_dot _ b _ (ByteSlice.bytes_toByteSlice_self _) rfl, finishProof_tokp] at h_ok
    rcases h_ptp with h_ptp | h_ptp
    · exact absurd h_ok (finishProof_start_error s pr h_ptp)
    · exact ⟨Or.inr h_ptp, _, rfl⟩
  | l :: ls, pr, b, hls, h_ptp, h_ok => by
    refine ⟨Or.inl (List.cons_ne_nil _ _), ?_⟩
    rw [List.foldlM_cons]
    cases h_step : s.db.stepNormal { pr with ptp := .normal } l with
    | error e =>
      have h_bad := feedToken_proof_label_error { s with tokp := .proof pr } b pr l
        (ByteSlice.bytes_toByteSlice_self _) rfl (hls l (List.mem_cons_self ..)) h_ptp e h_step
      rw [List.cons_append, runTokens_cons_of_error _ _ _ _ h_bad] at h_ok
      exact absurd h_ok h_bad
    | ok r₁ =>
      simp only [bind, Except.bind]
      have h_r₁ : r₁.ptp = .normal := by
        rw [stepNormal_ok_shape s.db _ r₁ l h_step]
      have h_eta : { r₁ with ptp := .normal } = r₁ := by
        obtain ⟨pos, lab, fmla, fr, heap, stack, ptp, inc⟩ := r₁
        simp only at h_r₁
        subst h_r₁
        rfl
      have e := feedToken_proof_label_ok { s with tokp := .proof pr } b pr r₁ l
        (ByteSlice.bytes_toByteSlice_self _) rfl (hls l (List.mem_cons_self ..)) h_ptp h_err h_step
      rw [List.cons_append,
        runTokens_cons_of_eq _ { s with tokp := .proof r₁ } _ _ _ e h_err] at h_ok
      obtain ⟨-, r, h_fold⟩ := runTokens_proof_no_error s h_err ls r₁ _
        (fun l' h' => hls l' (List.mem_cons_of_mem _ h')) (Or.inr h_r₁) h_ok
      exact ⟨r, h_eta ▸ h_fold⟩

/-! ## The `$p` statement -/

/-- The label, `$p` and the claim's symbols reach the end of the claim, with the claim rebuilt and
the label's position recorded. -/
theorem runTokens_thmTokens_claim (s : ParserState) (base : Nat) (label : String)
    (f : Verify.Formula) (proof : Array String) (h_start : s.tokp = .start)
    (h_err : s.db.error? = none) (h_label_tok : IsLabelToken label)
    (h_claim : ∀ x ∈ f.toList, IsMathToken x.value) (h_decl : FormulaSymbolsDeclared s.db f)
    (h_active : ∀ v, Verify.Sym.var v ∈ f.toList → s.db.isActiveVar v = true) :
    ∃ b, runTokens s base (thmTokens label f proof) =
      runTokens { s with tokp := .math f ⟨.thm, s.mkPos base, label⟩ } b
        ("$=" :: (proof.toList ++ ["$."])) := by
  have e1 := feedToken_start_label s base label (ByteSlice.bytes_toByteSlice_self _) h_start
    h_label_tok
  have e2 := feedToken_label_p { s with tokp := .label (s.mkPos base) label }
    (base + label.toUTF8.size + 1) (s.mkPos base) label (ByteSlice.bytes_toByteSlice_self _) rfl
  obtain ⟨b, hb⟩ := runTokens_math s ⟨.thm, s.mkPos base, label⟩
    ("$=" :: (proof.toList ++ ["$."])) h_err f.toList #[] _ h_claim (fun c hc => h_decl _ hc)
    h_active
  refine ⟨b, ?_⟩
  unfold thmTokens
  rw [runTokens_cons_of_eq _ _ _ _ _ e1 h_err,
    runTokens_cons_of_eq _ { s with tokp := .math #[] ⟨.thm, s.mkPos base, label⟩ } _ _ _ e2
      h_err, hb]
  simp

/-- An accepted proof runs to `finishProof` of its final proof state. -/
theorem runTokens_thmTokens_of_accepted (s : ParserState) (base : Nat) (label : String)
    (f : Verify.Formula) (proof : Array String) (h_start : s.tokp = .start)
    (h_err : s.db.error? = none) (h_label_tok : IsLabelToken label)
    (h_claim : ∀ x ∈ f.toList, IsMathToken x.value)
    (h_proof : ∀ l ∈ proof.toList, IsLabelToken l)
    (h_decl : FormulaSymbolsDeclared s.db f)
    (h_active : ∀ v, Verify.Sym.var v ∈ f.toList → s.db.isActiveVar v = true)
    (frImpl : Verify.Frame) (pr : ProofState) (h_head : f.hasConstHead = true)
    (h_int : s.db.interrupt = false) (h_trim : s.db.trimFrame' f = .ok frImpl)
    (h_fold : proof.foldlM (fun pr l => s.db.stepNormal pr l)
      { s.db.mkProofState (s.mkPos base) label f frImpl with ptp := .normal } = .ok pr)
    (h_fin : (s.finishProof pr).db.error? = none) :
    runTokens s base (thmTokens label f proof) = s.finishProof pr := by
  obtain ⟨b, hb⟩ := runTokens_thmTokens_claim s base label f proof h_start h_err h_label_tok
    h_claim h_decl h_active
  rw [hb]
  have e3 := feedToken_math_eq { s with tokp := .math f ⟨.thm, s.mkPos base, label⟩ } b f
    (s.mkPos base) label (ByteSlice.bytes_toByteSlice_self _) rfl
  have e4 := feedTokens_thm_ok { s with tokp := .math f ⟨.thm, s.mkPos base, label⟩ } f
    (s.mkPos base) label frImpl h_head h_trim h_int h_err
  rw [runTokens_cons_of_eq _
    { s with tokp := .proof (s.db.mkProofState (s.mkPos base) label f frImpl) } _ _ _
    (e3.trans e4) h_err]
  rw [← Array.foldlM_toList] at h_fold
  have h_ne : proof.toList ≠ [] := by
    intro h_nil
    rw [h_nil] at h_fold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h_fold
    subst h_fold
    obtain ⟨h_size, -, -⟩ :=
      Metamath.ParserAnyFormatEquivalence.finishProof_success_stack_conditions s _ h_fin
    simp [DB.mkProofState] at h_size
  exact runTokens_proof_ok s h_err proof.toList _ pr _ h_proof (Or.inl rfl) (Or.inl h_ne) h_fold

theorem runTokens_thmTokens_iff (s : ParserState) (base : Nat) (label : String)
    (f : Verify.Formula) (proof : Array String) (h_start : s.tokp = .start)
    (h_err : s.db.error? = none) (h_label_tok : IsLabelToken label)
    (h_claim : ∀ x ∈ f.toList, IsMathToken x.value)
    (h_proof : ∀ l ∈ proof.toList, IsLabelToken l)
    (h_decl : FormulaSymbolsDeclared s.db f)
    (h_active : ∀ v, Verify.Sym.var v ∈ f.toList → s.db.isActiveVar v = true) :
    (runTokens s base (thmTokens label f proof)).db.error? = none ↔
      ProofAccepted s (s.mkPos base) label f proof := by
  constructor
  · intro h_ok
    obtain ⟨b, hb⟩ := runTokens_thmTokens_claim s base label f proof h_start h_err h_label_tok
      h_claim h_decl h_active
    rw [hb] at h_ok
    have e3 := feedToken_math_eq { s with tokp := .math f ⟨.thm, s.mkPos base, label⟩ } b f
      (s.mkPos base) label (ByteSlice.bytes_toByteSlice_self _) rfl
    by_cases h3 : (({ s with tokp := .math f ⟨.thm, s.mkPos base, label⟩ } :
        ParserState).feedTokens f ⟨.thm, s.mkPos base, label⟩).db.error? = none
    · obtain ⟨h_head, h_int, fr, h_trim⟩ :=
        feedTokens_thm_of_no_error _ f (s.mkPos base) label h3
      have e4 := feedTokens_thm_ok { s with tokp := .math f ⟨.thm, s.mkPos base, label⟩ } f
        (s.mkPos base) label fr h_head h_trim h_int h_err
      rw [runTokens_cons_of_eq _
        { s with tokp := .proof (s.db.mkProofState (s.mkPos base) label f fr) } _ _ _
        (e3.trans e4) h_err] at h_ok
      obtain ⟨h_ne, r, h_fold⟩ :=
        runTokens_proof_no_error s h_err proof.toList _ _ h_proof (Or.inl rfl) h_ok
      have h_ne' : proof.toList ≠ [] := h_ne.resolve_right (by simp [DB.mkProofState])
      rw [runTokens_proof_ok s h_err proof.toList _ r _ h_proof (Or.inl rfl) (Or.inl h_ne')
        h_fold] at h_ok
      refine ⟨h_head, h_int, fr, r, h_trim, ?_, h_ok⟩
      rw [← Array.foldlM_toList]
      exact h_fold
    · rw [← e3] at h3
      rw [runTokens_cons_of_error _ _ _ _ h3] at h_ok
      exact absurd h_ok h3
  · rintro ⟨h_head, h_int, frImpl, pr, h_trim, h_fold, h_fin⟩
    rw [runTokens_thmTokens_of_accepted s base label f proof h_start h_err h_label_tok h_claim
      h_proof h_decl h_active frImpl pr h_head h_int h_trim h_fold h_fin]
    exact h_fin

theorem runTokens_thmTokens_eq (s : ParserState) (base : Nat) (label : String)
    (f : Verify.Formula) (proof : Array String) (frImpl : Verify.Frame) (h_start : s.tokp = .start)
    (h_err : s.db.error? = none) (h_fresh : s.db.find? label = none)
    (h_label_tok : IsLabelToken label)
    (h_claim : ∀ x ∈ f.toList, IsMathToken x.value)
    (h_proof : ∀ l ∈ proof.toList, IsLabelToken l)
    (h_decl : FormulaSymbolsDeclared s.db f)
    (h_active : ∀ v, Verify.Sym.var v ∈ f.toList → s.db.isActiveVar v = true)
    (h_acc : ProofAccepted s (s.mkPos base) label f proof)
    (h_trim : s.db.trimFrame' f = .ok frImpl) :
    runTokens s base (thmTokens label f proof) =
      { s with tokp := .start, db := s.db.insert (s.mkPos base) label (.assert f frImpl) } := by
  obtain ⟨h_head, h_int, frImpl', pr, h_trim', h_fold, h_fin⟩ := h_acc
  have h_eq : frImpl' = frImpl := by
    rw [h_trim] at h_trim'
    exact (Except.ok.inj h_trim').symm
  subst h_eq
  rw [runTokens_thmTokens_of_accepted s base label f proof h_start h_err h_label_tok h_claim
    h_proof h_decl h_active frImpl' pr h_head h_int h_trim' h_fold h_fin]
  obtain ⟨h_pos, h_label, h_fmla, h_frame, -, h_ptp, h_inc⟩ :=
    foldlM_stepNormal_preserves_fields s.db proof _ pr h_fold
  obtain ⟨h_size, h_top, -⟩ :=
    Metamath.ParserAnyFormatEquivalence.finishProof_success_stack_conditions s pr h_fin
  have h_stack : pr.stack = #[pr.fmla] := by
    apply Array.ext
    · simp [h_size]
    · intro i hi _
      have hi0 : i = 0 := by omega
      subst hi0
      rw [Array.getElem?_eq_getElem hi] at h_top
      simpa using h_top
  have h_label' : pr.label = label := h_label
  rw [finishProof_of_exact_state s pr h_ptp h_stack h_inc (h_label' ▸ h_fresh) h_err]
  have h_pos' : pr.pos = s.mkPos base := h_pos
  have h_fmla' : pr.fmla = f := h_fmla
  have h_frame' : pr.frame = frImpl' := h_frame
  rw [h_pos', h_label', h_fmla', h_frame']

end Metamath.SourceCompleteness
