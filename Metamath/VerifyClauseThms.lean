import Metamath.Verify

namespace Metamath
namespace Verify

@[simp] theorem isSpecWhitespace_formFeed : isSpecWhitespace (0x0c : UInt8) = true := by
  decide

namespace ParseErrorCode

@[simp] theorem ofNat?_toNat (code : ParseErrorCode) :
    ofNat? (toNat code) = some code := by
  cases code <;> rfl

@[simp] theorem message_ofNat?_toNat (code : ParseErrorCode) :
    (ofNat? (toNat code)).map message = some (message code) := by
  simp

@[simp] theorem specClause?_unclosedDjvars :
    specClause? .unclosedDjvars = some .sec4_2_4_djvars := rfl

end ParseErrorCode

section HighValueParseErrorClauseLinks

theorem parseErrorCode_specClause_invalidLabel :
    ParseErrorCode.specClause .invalidLabel = .sec4_2_1_labels := rfl

theorem parseErrorCode_specClause_duplicateDisjointVariable :
    ParseErrorCode.specClause .duplicateDisjointVariable = .sec4_2_4_djvars := rfl

theorem parseErrorCode_specClause_disjointStatementTooShort :
    ParseErrorCode.specClause .disjointStatementTooShort = .sec4_2_4_djvars := rfl

theorem parseErrorCode_specClause_tokenNotInScope :
    ParseErrorCode.specClause .tokenNotInScope = .sec4_2_4_djvars := rfl

theorem parseErrorCode_specClause_tokenNotConstantOrVariable :
    ParseErrorCode.specClause .tokenNotConstantOrVariable = .sec4_2_2_constantsVariables := rfl

theorem parseErrorCode_specClause_tokenNotVariable :
    ParseErrorCode.specClause .tokenNotVariable = .sec4_2_4_djvars := rfl

theorem parseErrorCode_specClause_topLevelEssentialNotAllowed :
    ParseErrorCode.specClause .topLevelEssentialNotAllowed = .sec4_2_8_scoping := rfl

theorem parseErrorCode_specClause_outOfOrderHypothesesInFrame :
    ParseErrorCode.specClause .outOfOrderHypothesesInFrame = .sec4_2_7_frames := rfl

theorem parseErrorCode_specClause_typeErrorInSubstitution :
    ParseErrorCode.specClause .typeErrorInSubstitution = .sec4_3_substitution := rfl

theorem parseErrorCode_specClause_badTypecodeInSubstitution :
    ParseErrorCode.specClause .badTypecodeInSubstitution = .sec4_3_substitution := rfl

theorem parseErrorCode_specClause_disjointVariableViolation :
    ParseErrorCode.specClause .disjointVariableViolation = .sec4_3_substitution := rfl

theorem parseErrorCode_specClause_stackUnderflow :
    ParseErrorCode.specClause .stackUnderflow = .sec4_3_stackDiscipline := rfl

theorem parseErrorCode_specClause_theoremMoreThanOneStackElement :
    ParseErrorCode.specClause .theoremMoreThanOneStackElement = .sec4_3_stackDiscipline := rfl

theorem parseErrorCode_specClause_statementNotFound :
    ParseErrorCode.specClause .statementNotFound = .sec4_3_labelResolution := rfl

theorem parseErrorCode_specClause_hypothesisNotInDatabaseScope :
    ParseErrorCode.specClause .hypothesisNotInDatabaseScope = .sec4_3_labelResolution := rfl

theorem parseErrorCode_specClause_mandatoryHypothesisNotFoundInDatabase :
    ParseErrorCode.specClause .mandatoryHypothesisNotFoundInDatabase = .sec4_3_labelResolution := rfl

theorem parseErrorCode_specClause_hypothesisNotFound :
    ParseErrorCode.specClause .hypothesisNotFound = .sec4_3_labelResolution := rfl

end HighValueParseErrorClauseLinks

section HighValueClausePredicates

theorem invalidLabel_violation_implies_sec4_2_1
    (s : DB) :
    s.InvalidLabelViolation →
    s.Sec4_2_1_LabelSyntaxViolation := by
  intro h
  simpa [DB.Sec4_2_1_LabelSyntaxViolation] using h

theorem duplicateDisjointVariable_violation_implies_sec4_2_4_duplicate
    (s : DB) :
    s.DuplicateDisjointVariableViolation →
    s.Sec4_2_4_DjvarsDuplicateViolation := by
  intro h
  simpa [DB.Sec4_2_4_DjvarsDuplicateViolation] using h

theorem disjointStatementTooShort_violation_implies_sec4_2_4_arity
    (s : DB) :
    s.DisjointStatementTooShortViolation →
    s.Sec4_2_4_DjvarsArityViolation := by
  intro h
  simpa [DB.Sec4_2_4_DjvarsArityViolation] using h

theorem tokenNotInScope_violation_implies_sec4_2_4_scope
    (s : DB) :
    s.TokenNotInScopeViolation →
    s.Sec4_2_4_DjvarsScopeViolation := by
  intro h
  simpa [DB.Sec4_2_4_DjvarsScopeViolation] using h

end HighValueClausePredicates

/-- Concrete clause theorem for the `$d`-at-EOF parser error. -/
theorem checkBytes_unclosedDjvars_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedDjvars →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_4_djvars := by
  intro h_code
  exact ⟨.unclosedDjvars, h_code, rfl⟩

theorem checkBytes_invalidLabel_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_1_labels := by
  intro h_code
  exact ⟨.invalidLabel, h_code, rfl⟩

theorem checkBytes_duplicateDisjointVariable_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_4_djvars := by
  intro h_code
  exact ⟨.duplicateDisjointVariable, h_code, rfl⟩

theorem checkBytes_disjointStatementTooShort_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .disjointStatementTooShort →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_4_djvars := by
  intro h_code
  exact ⟨.disjointStatementTooShort, h_code, rfl⟩

theorem checkBytes_tokenNotInScope_implies_clause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).ParserSpecClauseViolation .sec4_2_4_djvars := by
  intro h_code
  exact ⟨.tokenNotInScope, h_code, rfl⟩

end Verify
end Metamath
