import Metamath.Verify
import Metamath.VerifyClauseThms
import Metamath.VerifyDBThms

namespace Metamath
namespace Verify
open Std (HashSet)

namespace ModeConfig

theorem soundDefault_prefixCertified : prefixCertified soundDefault :=
  ⟨rfl, rfl⟩

theorem knife_prefixCertified : prefixCertified knife :=
  ⟨rfl, rfl⟩

theorem not_zar_prefixCertified : ¬ prefixCertified zar :=
  fun ⟨h, _⟩ => by simp [zar] at h

theorem not_exe_prefixCertified : ¬ prefixCertified exe :=
  fun ⟨h, _⟩ => by simp [exe] at h

theorem not_permissive_prefixCertified : ¬ prefixCertified permissive :=
  fun ⟨h, _⟩ => by simp [permissive] at h

end ModeConfig

/-- Parser tokenization whitespace now matches the Metamath spec set (§4.1.1). -/
theorem checkBytes_tokenization_whitespace_matches_spec (c : UInt8) :
    isWhitespace c = isSpecWhitespace c := by
  rfl

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
