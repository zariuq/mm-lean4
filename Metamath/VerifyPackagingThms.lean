import Metamath.Verify
import Metamath.VerifyDBSemanticThms
import Metamath.VerifyDBPayloadThms

namespace Metamath
namespace Verify

/-- Canonical parser-entry semantic soundness:
`checkBytes` decoded code implies bundled semantic violation witness. -/
theorem checkBytes_parseErrorCode?_semantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ParserSemanticViolation code := by
  intro h_code
  exact DB.parseErrorCode?_semantic_sound (s := checkBytes arr config) code h_code

/-- Parser-level soundness at the byte-stream entrypoint. -/
theorem checkBytes_parseErrorCode?_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ParserSpecViolation code := by
  intro h_code
  exact (checkBytes_parseErrorCode?_semantic_sound arr config code h_code).1

/-- `checkBytes` clause-level soundness from decoded code + code-to-clause mapping. -/
theorem checkBytes_parseErrorCode?_clause_sound
    (arr : ByteArray) (config : ModeConfig)
    (code : ParseErrorCode) (clause : SpecClause) :
    (checkBytes arr config).parseErrorCode? = some code →
    ParseErrorCode.specClause code = clause →
    (checkBytes arr config).ParserSpecClauseViolation clause := by
  intro h_code h_clause
  rcases (checkBytes_parseErrorCode?_semantic_sound arr config code h_code).2.1 with
    ⟨code', h_code', h_clause'⟩
  exact ⟨code', h_code', h_clause'.trans h_clause⟩

/-- `checkBytes` clause soundness using the canonical clause attached to the code. -/
theorem checkBytes_parseErrorCode?_specClause_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact (checkBytes_parseErrorCode?_semantic_sound arr config code h_code).2.1

theorem checkBytes_parseErrorCode?_invalidLabel_payload_inversion
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).InvalidLabelPayloadWitness := by
  intro h_code
  exact DB.parseErrorCode?_invalidLabel_payload_inversion
    (s := checkBytes arr config) h_code

theorem checkBytes_parseErrorCode?_topLevelEssentialNotAllowed_payload_inversion
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
    (checkBytes arr config).TopLevelEssentialPayloadWitness := by
  intro h_code
  exact DB.parseErrorCode?_topLevelEssentialNotAllowed_payload_inversion
    (s := checkBytes arr config) h_code

theorem checkBytes_allCodePayloadShape_implies_specClauseViolation
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).AllCodePayloadShapeViolation code →
    (checkBytes arr config).ParserSpecClauseViolation (ParseErrorCode.specClause code) := by
  intro h_shape
  exact DB.allCodePayloadShape_implies_specClauseViolation (s := checkBytes arr config) code h_shape

/-- `checkBytes` all-code clause-semantic soundness:
decoded parser code yields semantic witness for the code's mapped clause. -/
theorem checkBytes_parseErrorCode?_allCodeClauseSemantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).AllCodeClauseSemanticViolation (ParseErrorCode.specClause code) := by
  intro h_code
  exact DB.parseErrorCode?_allCodeClauseSemantic_sound (s := checkBytes arr config) code h_code

/-- Canonical all-code parser-entry packaging theorem:
decoded code yields concrete spec predicate (clause + payload-shape) for all constructors. -/
theorem checkBytes_parseErrorCode?_concrete_spec_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ConcreteSpecPredicate code := by
  intro h_code
  exact DB.parseErrorCode?_concrete_spec_sound (s := checkBytes arr config) code h_code

/-- Canonical all-code parser-entry semantic packaging theorem:
decoded code yields concrete semantic clause predicate for all constructors. -/
theorem checkBytes_parseErrorCode?_concrete_semantic_clause_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).ConcreteSemanticClausePredicate code := by
  intro h_code
  exact DB.parseErrorCode?_concrete_semantic_clause_sound
    (s := checkBytes arr config) code h_code

/-- Canonical parser-entry rule-semantic soundness for any decoded code. -/
theorem checkBytes_parseErrorCode?_ruleSemantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).RuleSemanticViolation code := by
  intro h_code
  exact DB.parseErrorCode?_ruleSemantic_sound (s := checkBytes arr config) code h_code

/-- Canonical parser-entry rule+clause semantic soundness for any decoded code. -/
theorem checkBytes_parseErrorCode?_ruleClauseSemantic_sound
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    (checkBytes arr config).RuleClauseSemanticViolation code := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) code h_code

end Verify
end Metamath
