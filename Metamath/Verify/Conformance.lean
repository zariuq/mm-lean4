import Metamath.Verify
import Metamath.Verify.Clause
import Metamath.Verify.DB

namespace Metamath
namespace Verify
open Std (HashSet)

namespace ModeConfig

theorem isSound_sound : IsSound sound :=
  ⟨rfl, rfl⟩

theorem isSound_knife : IsSound knife :=
  ⟨rfl, rfl⟩

theorem not_isSound_zar : ¬ IsSound zar :=
  fun ⟨h, _⟩ => by simp [zar] at h

theorem not_isSound_exe : ¬ IsSound exe :=
  fun ⟨h, _⟩ => by simp [exe] at h

theorem not_isSound_permissive : ¬ IsSound permissive :=
  fun ⟨h, _⟩ => by simp [permissive] at h

end ModeConfig

/-- In every mode that does not treat vertical tab as whitespace, the parser separates tokens exactly
at the Metamath spec's whitespace (§4.1.1). -/
theorem checkBytes_tokenization_whitespace_matches_spec (cfg : ModeConfig)
    (h : cfg.allowVerticalTabWhitespace = false) (c : UInt8) :
    cfg.isWhitespace c = isSpecWhitespace c := by
  simp [ModeConfig.isWhitespace, h, isWhitespace, isSpecWhitespace]

theorem checkBytes_invalidLabel_implies_sec4_2_1
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .invalidLabel →
    (checkBytes arr config).Sec4_2_1_LabelSyntaxViolation := by
  intro h_code
  have h_sem := DB.parseErrorCode?_semantic_sound (s := checkBytes arr config) .invalidLabel h_code
  have h_rule : (checkBytes arr config).RuleSemanticViolation .invalidLabel := h_sem.2.2
  have h_vio : (checkBytes arr config).InvalidLabelViolation := by
    simpa [DB.RuleSemanticViolation, DB.InvalidLabelViolation] using h_rule
  exact invalidLabel_violation_implies_sec4_2_1 (s := checkBytes arr config)
    h_vio

theorem checkBytes_duplicateDisjointVariable_implies_sec4_2_4_duplicate
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .duplicateDisjointVariable →
    (checkBytes arr config).Sec4_2_4_DjvarsDuplicateViolation := by
  intro h_code
  have h_sem :=
    DB.parseErrorCode?_semantic_sound (s := checkBytes arr config) .duplicateDisjointVariable h_code
  have h_rule : (checkBytes arr config).RuleSemanticViolation .duplicateDisjointVariable := h_sem.2.2
  have h_vio : (checkBytes arr config).DuplicateDisjointVariableViolation := by
    simpa [DB.RuleSemanticViolation, DB.DuplicateDisjointVariableViolation] using h_rule
  exact duplicateDisjointVariable_violation_implies_sec4_2_4_duplicate (s := checkBytes arr config)
    h_vio

theorem checkBytes_disjointStatementTooShort_implies_sec4_2_4_arity
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .disjointStatementTooShort →
    (checkBytes arr config).Sec4_2_4_DjvarsArityViolation := by
  intro h_code
  have h_sem :=
    DB.parseErrorCode?_semantic_sound (s := checkBytes arr config) .disjointStatementTooShort h_code
  have h_rule : (checkBytes arr config).RuleSemanticViolation .disjointStatementTooShort :=
    h_sem.2.2
  have h_vio : (checkBytes arr config).DisjointStatementTooShortViolation := by
    simpa [DB.RuleSemanticViolation, DB.DisjointStatementTooShortViolation] using h_rule
  exact disjointStatementTooShort_violation_implies_sec4_2_4_arity (s := checkBytes arr config)
    h_vio

theorem checkBytes_tokenNotInScope_implies_sec4_2_4_scope
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotInScope →
    (checkBytes arr config).Sec4_2_4_DjvarsScopeViolation := by
  intro h_code
  have h_sem := DB.parseErrorCode?_semantic_sound (s := checkBytes arr config) .tokenNotInScope h_code
  have h_rule : (checkBytes arr config).RuleSemanticViolation .tokenNotInScope := h_sem.2.2
  have h_vio : (checkBytes arr config).TokenNotInScopeViolation := by
    simpa [DB.RuleSemanticViolation, DB.TokenNotInScopeViolation] using h_rule
  exact tokenNotInScope_violation_implies_sec4_2_4_scope (s := checkBytes arr config)
    h_vio

end Verify
end Metamath
