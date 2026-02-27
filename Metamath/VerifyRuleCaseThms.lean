import Metamath.Verify
import Metamath.VerifyPackagingThms

namespace Metamath
namespace Verify

theorem checkBytes_parseErrorCode?_invalidLabel_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).InvalidLabelViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .invalidLabel h_code
  simpa [DB.RuleSemanticViolation, DB.InvalidLabelViolation] using h_rule

theorem checkBytes_parseErrorCode?_duplicateDisjointVariable_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).DuplicateDisjointVariableViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .duplicateDisjointVariable h_code
  simpa [DB.RuleSemanticViolation, DB.DuplicateDisjointVariableViolation] using h_rule

theorem checkBytes_parseErrorCode?_tokenNotInScope_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).TokenNotInScopeViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .tokenNotInScope h_code
  simpa [DB.RuleSemanticViolation, DB.TokenNotInScopeViolation] using h_rule

theorem checkBytes_parseErrorCode?_cantSaveEmptyStack_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .cantSaveEmptyStack →
    (checkBytes arr config).CompressedSaveViolation := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .cantSaveEmptyStack h_code
  simpa [DB.RuleSemanticViolation, DB.CompressedSaveViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedBlock_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedBlock →
    (checkBytes arr config).DoneModeViolation .unclosedBlock := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedBlock h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedComment_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedComment →
    (checkBytes arr config).DoneModeViolation .unclosedComment := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedComment h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedConst_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedConst →
    (checkBytes arr config).DoneModeViolation .unclosedConst := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedConst h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedVar_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedVar →
    (checkBytes arr config).DoneModeViolation .unclosedVar := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedVar h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedDjvars_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedDjvars →
    (checkBytes arr config).DoneModeViolation .unclosedDjvars := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedDjvars h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedFloat_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedFloat →
    (checkBytes arr config).DoneModeViolation .unclosedFloat := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedFloat h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedEss_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedEss →
    (checkBytes arr config).DoneModeViolation .unclosedEss := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedEss h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedAx_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedAx →
    (checkBytes arr config).DoneModeViolation .unclosedAx := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedAx h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedThm_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedThm →
    (checkBytes arr config).DoneModeViolation .unclosedThm := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedThm h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_unclosedProof_violation
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedProof →
    (checkBytes arr config).DoneModeViolation .unclosedProof := by
  intro h_code
  have h_rule := checkBytes_parseErrorCode?_ruleSemantic_sound arr config .unclosedProof h_code
  simpa [DB.RuleSemanticViolation, DB.DoneModeViolation] using h_rule

theorem checkBytes_parseErrorCode?_cantSaveEmptyStack_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .cantSaveEmptyStack →
    (checkBytes arr config).RuleClauseSemanticViolation .cantSaveEmptyStack := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .cantSaveEmptyStack h_code

theorem checkBytes_parseErrorCode?_unclosedBlock_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedBlock →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedBlock := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedBlock h_code

theorem checkBytes_parseErrorCode?_unclosedComment_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedComment →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedComment := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedComment h_code

theorem checkBytes_parseErrorCode?_unclosedConst_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedConst →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedConst := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedConst h_code

theorem checkBytes_parseErrorCode?_unclosedVar_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedVar →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedVar := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedVar h_code

theorem checkBytes_parseErrorCode?_unclosedDjvars_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedDjvars →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedDjvars := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedDjvars h_code

theorem checkBytes_parseErrorCode?_unclosedFloat_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedFloat →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedFloat := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedFloat h_code

theorem checkBytes_parseErrorCode?_unclosedEss_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedEss →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedEss := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedEss h_code

theorem checkBytes_parseErrorCode?_unclosedAx_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedAx →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedAx := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedAx h_code

theorem checkBytes_parseErrorCode?_unclosedThm_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedThm →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedThm := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedThm h_code

theorem checkBytes_parseErrorCode?_notACommand_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .notACommand →
    (checkBytes arr config).RuleClauseSemanticViolation .notACommand := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .notACommand h_code

theorem checkBytes_parseErrorCode?_unclosedProof_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unclosedProof →
    (checkBytes arr config).RuleClauseSemanticViolation .unclosedProof := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unclosedProof h_code

theorem checkBytes_parseErrorCode?_cantPopGlobalScope_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .cantPopGlobalScope →
    (checkBytes arr config).RuleClauseSemanticViolation .cantPopGlobalScope := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .cantPopGlobalScope h_code

theorem checkBytes_parseErrorCode?_constMustBeOutermost_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .constMustBeOutermost →
    (checkBytes arr config).RuleClauseSemanticViolation .constMustBeOutermost := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .constMustBeOutermost h_code

theorem checkBytes_parseErrorCode?_duplicateSymbolOrAssert_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateSymbolOrAssert →
    (checkBytes arr config).RuleClauseSemanticViolation .duplicateSymbolOrAssert := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .duplicateSymbolOrAssert h_code

theorem checkBytes_parseErrorCode?_firstSymbolNotConstant_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .firstSymbolNotConstant →
    (checkBytes arr config).RuleClauseSemanticViolation .firstSymbolNotConstant := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .firstSymbolNotConstant h_code

theorem checkBytes_parseErrorCode?_hypothesisSymbolsNotInFrame_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .hypothesisSymbolsNotInFrame →
    (checkBytes arr config).RuleClauseSemanticViolation .hypothesisSymbolsNotInFrame := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .hypothesisSymbolsNotInFrame h_code

theorem checkBytes_parseErrorCode?_expectedConstantAndVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .expectedConstantAndVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .expectedConstantAndVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .expectedConstantAndVariable h_code

theorem checkBytes_parseErrorCode?_variableAlreadyHasFloatHyp_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .variableAlreadyHasFloatHyp →
    (checkBytes arr config).RuleClauseSemanticViolation .variableAlreadyHasFloatHyp := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .variableAlreadyHasFloatHyp h_code

theorem checkBytes_parseErrorCode?_stackFormulaNoConstantHead_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .stackFormulaNoConstantHead →
    (checkBytes arr config).RuleClauseSemanticViolation .stackFormulaNoConstantHead := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .stackFormulaNoConstantHead h_code

theorem checkBytes_parseErrorCode?_hypothesisNoConstantHead_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .hypothesisNoConstantHead →
    (checkBytes arr config).RuleClauseSemanticViolation .hypothesisNoConstantHead := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .hypothesisNoConstantHead h_code

theorem checkBytes_parseErrorCode?_typeErrorInSubstitution_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .typeErrorInSubstitution →
    (checkBytes arr config).RuleClauseSemanticViolation .typeErrorInSubstitution := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .typeErrorInSubstitution h_code

theorem checkBytes_parseErrorCode?_badTypecodeInSubstitution_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .badTypecodeInSubstitution →
    (checkBytes arr config).RuleClauseSemanticViolation .badTypecodeInSubstitution := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .badTypecodeInSubstitution h_code

theorem checkBytes_parseErrorCode?_duplicateFloatVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateFloatVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .duplicateFloatVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .duplicateFloatVariable h_code

theorem checkBytes_parseErrorCode?_disjointVariableViolation_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .disjointVariableViolation →
    (checkBytes arr config).RuleClauseSemanticViolation .disjointVariableViolation := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .disjointVariableViolation h_code

theorem checkBytes_parseErrorCode?_assertionNoConstantHead_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .assertionNoConstantHead →
    (checkBytes arr config).RuleClauseSemanticViolation .assertionNoConstantHead := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .assertionNoConstantHead h_code

theorem checkBytes_parseErrorCode?_assertionVarsNotInFrame_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .assertionVarsNotInFrame →
    (checkBytes arr config).RuleClauseSemanticViolation .assertionVarsNotInFrame := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .assertionVarsNotInFrame h_code

theorem checkBytes_parseErrorCode?_stackUnderflow_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .stackUnderflow →
    (checkBytes arr config).RuleClauseSemanticViolation .stackUnderflow := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .stackUnderflow h_code

theorem checkBytes_parseErrorCode?_proofBackrefIndexOutOfRange_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .proofBackrefIndexOutOfRange →
    (checkBytes arr config).RuleClauseSemanticViolation .proofBackrefIndexOutOfRange := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .proofBackrefIndexOutOfRange h_code

theorem checkBytes_parseErrorCode?_invalidLabel_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).RuleClauseSemanticViolation .invalidLabel := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .invalidLabel h_code

theorem checkBytes_parseErrorCode?_invalidMathString_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidMathString →
    (checkBytes arr config).RuleClauseSemanticViolation .invalidMathString := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .invalidMathString h_code

theorem checkBytes_parseErrorCode?_duplicateDisjointVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .duplicateDisjointVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .duplicateDisjointVariable h_code

theorem checkBytes_parseErrorCode?_tokenNotInScope_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).RuleClauseSemanticViolation .tokenNotInScope := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .tokenNotInScope h_code

theorem checkBytes_parseErrorCode?_tokenNotVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .tokenNotVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .tokenNotVariable h_code

theorem checkBytes_parseErrorCode?_unknownStepQuestionRejected_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unknownStepQuestionRejected →
    (checkBytes arr config).RuleClauseSemanticViolation .unknownStepQuestionRejected := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unknownStepQuestionRejected h_code

theorem checkBytes_parseErrorCode?_topLevelEssentialNotAllowed_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
    (checkBytes arr config).RuleClauseSemanticViolation .topLevelEssentialNotAllowed := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .topLevelEssentialNotAllowed h_code

theorem checkBytes_parseErrorCode?_proofParseError_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .proofParseError →
    (checkBytes arr config).RuleClauseSemanticViolation .proofParseError := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .proofParseError h_code

theorem checkBytes_parseErrorCode?_theoremMoreThanOneStackElement_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .theoremMoreThanOneStackElement →
    (checkBytes arr config).RuleClauseSemanticViolation .theoremMoreThanOneStackElement := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .theoremMoreThanOneStackElement h_code

theorem checkBytes_parseErrorCode?_theoremClaimMismatch_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .theoremClaimMismatch →
    (checkBytes arr config).RuleClauseSemanticViolation .theoremClaimMismatch := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .theoremClaimMismatch h_code

theorem checkBytes_parseErrorCode?_nestedCommentDelimiter_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .nestedCommentDelimiter →
    (checkBytes arr config).RuleClauseSemanticViolation .nestedCommentDelimiter := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .nestedCommentDelimiter h_code

theorem checkBytes_parseErrorCode?_tokenNotConstantOrVariable_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
    (checkBytes arr config).RuleClauseSemanticViolation .tokenNotConstantOrVariable := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .tokenNotConstantOrVariable h_code

theorem checkBytes_parseErrorCode?_unknownStatementType_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .unknownStatementType →
    (checkBytes arr config).RuleClauseSemanticViolation .unknownStatementType := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .unknownStatementType h_code

theorem checkBytes_parseErrorCode?_internalIllFormedDatabaseAfterParse_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .internalIllFormedDatabaseAfterParse →
    (checkBytes arr config).RuleClauseSemanticViolation .internalIllFormedDatabaseAfterParse := by
  intro h_code
  exact checkBytes_parseErrorCode?_ruleClauseSemantic_sound arr config .internalIllFormedDatabaseAfterParse h_code


end Verify
end Metamath
