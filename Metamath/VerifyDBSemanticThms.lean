import Metamath.Verify

namespace Metamath
namespace Verify
namespace DB

theorem parseErrorCode?_sound (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code → s.ParserSpecViolation code := by
  intro h_code
  unfold DB.parseErrorCode? at h_code
  cases h_err : s.error? with
  | none =>
      simp [h_err] at h_code
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e with
          | error pos msg =>
              cases h_ev : s.errorEvidence? with
              | none =>
                  simp [h_err, h_ev] at h_code
              | some ev =>
                  cases ev with
                  | doneMode err =>
                      have h_code' : DoneModeError.code err = code := by
                        simpa [DB.parseErrorCode?, h_err, h_ev] using h_code
                      refine ⟨pos, msg, idx, .doneMode err, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [ErrorEvidence.code] using h_code'
                  | tokenForm err =>
                      refine ⟨pos, msg, idx, .tokenForm err, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | scopeDecl err =>
                      refine ⟨pos, msg, idx, .scopeDecl err, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | includeErr err =>
                      refine ⟨pos, msg, idx, .includeErr err, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | proofCheck err =>
                      refine ⟨pos, msg, idx, .proofCheck err, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | theoremFinality err =>
                      refine ⟨pos, msg, idx, .theoremFinality err, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | compressedSave err =>
                      refine ⟨pos, msg, idx, .compressedSave err, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
                  | internalGate allowDup wf dv =>
                      refine ⟨pos, msg, idx, .internalGate allowDup wf dv, ?_, ?_, ?_⟩
                      · simp [h_err]
                      · exact h_ev
                      · simpa [h_err, h_ev] using h_code
          | ax pos l f fr =>
              simp [h_err] at h_code
          | thm pos l f fr =>
              simp [h_err] at h_code
          | includeRequest sourceFile includePath =>
              simp [h_err] at h_code

/-- Parser-level clause soundness from decoded code + code-to-clause map. -/
theorem parseErrorCode?_clause_sound
    (s : DB) (code : ParseErrorCode) (clause : SpecClause) :
    s.parseErrorCode? = some code →
    ParseErrorCode.specClause code = clause →
    s.ParserSpecClauseViolation clause := by
  intro h_code h_clause
  exact ⟨code, h_code, h_clause⟩

/-- Parser-level clause soundness with the canonical clause chosen by the code. -/
theorem parseErrorCode?_specClause_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact ⟨code, h_code, rfl⟩

/-- All-code evidence soundness:
decoded parser code carries a concrete evidence witness for that code. -/
theorem parseErrorCode?_allCodePayloadShape_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.AllCodePayloadShapeViolation code := by
  intro h_code
  obtain ⟨pos, msg, idx, ev, h_err, h_ev, h_code'⟩ := parseErrorCode?_sound s code h_code
  have h_code_ev : s.parseErrorCode? = some ev.code := by
    simpa [h_code'] using h_code
  have h_allowed : ErrorEvidence.allowed ev := by
    simp [ErrorEvidence.allowed]
  exact ⟨pos, msg, idx, ev, h_err, h_ev, h_code', h_allowed⟩

/-- Clause witness derivable directly from all-code payload-shape witness. -/
theorem allCodePayloadShape_implies_specClauseViolation
    (s : DB) (code : ParseErrorCode) :
    s.AllCodePayloadShapeViolation code →
    s.ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_shape
  rcases h_shape with ⟨pos, msg, idx, ev, h_err, h_ev, h_code, h_allowed⟩
  refine ⟨code, ?_, rfl⟩
  have h_parse : s.parseErrorCode? = some code := by
    unfold DB.parseErrorCode?
    cases ev <;> simpa [h_err, h_ev, ErrorEvidence.code] using h_code
  exact h_parse

/-- All-code semantic soundness:
decoded parser code carries a semantic witness for that code. -/
theorem parseErrorCode?_allCodeSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.AllCodeSemanticViolation code := by
  intro h_code
  exact parseErrorCode?_allCodePayloadShape_sound s code h_code

/-- Lift any code-indexed semantic witness to the corresponding clause-indexed one. -/
theorem allCodeSemantic_implies_clauseSemantic
    (s : DB) (code : ParseErrorCode) :
    s.AllCodeSemanticViolation code →
    s.AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) := by
  intro h_sem
  exact ⟨code, rfl, h_sem⟩

/-- Clause-indexed semantic soundness for any decoded parser code. -/
theorem parseErrorCode?_allCodeClauseSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact allCodeSemantic_implies_clauseSemantic s code
    (parseErrorCode?_allCodeSemantic_sound s code h_code)

/-- Concrete parser-spec predicate:
decoded-code clause witness paired with all-code payload-shape evidence. -/
def ConcreteSpecPredicate (s : DB) (code : ParseErrorCode) : Prop :=
  s.ParserSpecClauseViolation (ParseErrorCode.specClause code) ∧
    s.AllCodePayloadShapeViolation code

/-- Canonical all-code semantic clause predicate:
decoded-code clause witness paired with semantic payload-shape evidence. -/
def ConcreteSemanticClausePredicate (s : DB) (code : ParseErrorCode) : Prop :=
  s.AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) ∧
    s.AllCodeSemanticViolation code

/-- Canonical all-code packaging theorem from decoded parser code
to concrete spec predicate (clause + payload-shape). -/
theorem parseErrorCode?_concrete_spec_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ConcreteSpecPredicate code := by
  intro h_code
  have h_shape : s.AllCodePayloadShapeViolation code :=
    parseErrorCode?_allCodePayloadShape_sound s code h_code
  exact ⟨allCodePayloadShape_implies_specClauseViolation s code h_shape, h_shape⟩

/-- Canonical all-code semantic packaging theorem from decoded parser code
to semantic clause predicate (clause + semantic payload-shape). -/
theorem parseErrorCode?_concrete_semantic_clause_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ConcreteSemanticClausePredicate code := by
  intro h_code
  have h_sem : s.AllCodeSemanticViolation code :=
    parseErrorCode?_allCodeSemantic_sound s code h_code
  exact ⟨allCodeSemantic_implies_clauseSemantic s code h_sem, h_sem⟩

/-- Canonical parser rule-semantic soundness for any decoded code. -/
theorem parseErrorCode?_ruleSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.RuleSemanticViolation code := by
  intro h_code
  obtain ⟨pos, msg, idx, ev, h_err, h_ev, h_code'⟩ := parseErrorCode?_sound s code h_code
  have h_code_ev : s.parseErrorCode? = some ev.code := by
    simpa [h_code'] using h_code
  cases ev with
  | doneMode err =>
      have h_code_eq : code = DoneModeError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_sem := parseErrorCode?_allCodeSemantic_sound s (DoneModeError.code err) h_code_ev
      cases err <;> simpa [DB.RuleSemanticViolation, DB.DoneModeViolation, DoneModeError.code] using h_sem
  | tokenForm err =>
      have h_code_eq : code = TokenFormError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_tf : s.TokenFormViolation (TokenFormError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (TokenFormError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_tf
      exact h_rule
  | scopeDecl err =>
      have h_code_eq : code = ScopeDeclError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_sc : s.ScopeDeclViolation (ScopeDeclError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (ScopeDeclError.code err) := by
        cases err <;> simpa [ScopeDeclError.code, DB.RuleSemanticViolation] using h_sc
      exact h_rule
  | includeErr err =>
      have h_code_eq : code = IncludeError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_inc : s.IncludeViolation (IncludeError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (IncludeError.code err) := by
        cases err <;> simpa [IncludeError.code, DB.RuleSemanticViolation, DB.IncludeReadFailureViolation] using h_inc
      exact h_rule
  | proofCheck err =>
      have h_code_eq : code = ProofCheckError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_pc : s.ProofCheckViolation (ProofCheckError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (ProofCheckError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_pc
      exact h_rule
  | theoremFinality err =>
      have h_code_eq : code = TheoremFinalityError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_tf : s.TheoremFinalityViolation (TheoremFinalityError.code err) := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (TheoremFinalityError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_tf
      exact h_rule
  | compressedSave err =>
      have h_code_eq : code = CompressedSaveError.code err := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_cs : s.CompressedSaveViolation := ⟨err, h_ev, rfl⟩
      have h_rule : s.RuleSemanticViolation (CompressedSaveError.code err) := by
        cases err <;> simpa [DB.RuleSemanticViolation] using h_cs
      exact h_rule
  | internalGate allowDup wf dv =>
      have h_code_eq : code = ParseErrorCode.internalIllFormedDatabaseAfterParse := by
        simpa [ErrorEvidence.code] using Eq.symm h_code'
      subst code
      have h_ic : s.InternalConsistencyViolation := ⟨allowDup, wf, dv, h_ev⟩
      exact Or.inr (Or.inr h_ic)

/-- Canonical parser rule+clause semantic soundness for any decoded code. -/
theorem parseErrorCode?_ruleClauseSemantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.RuleClauseSemanticViolation code := by
  intro h_code
  exact ⟨
    parseErrorCode?_ruleSemantic_sound s code h_code,
    parseErrorCode?_specClause_sound s code h_code
  ⟩

/-- Canonical parser-level semantic soundness:
decoded code implies both concrete code witness and clause witness. -/
theorem parseErrorCode?_semantic_sound
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    s.ParserSemanticViolation code := by
  intro h_code
  exact ⟨
    parseErrorCode?_sound s code h_code,
    parseErrorCode?_specClause_sound s code h_code,
    parseErrorCode?_ruleSemantic_sound s code h_code
  ⟩

end DB
end Verify
end Metamath
