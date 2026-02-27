import Metamath.Verify
import Metamath.VerifyDBThms
import Metamath.VerifyPackagingThms

namespace Metamath
namespace Verify

/-- Decoded `.statementNotFound` yields proof-check evidence with label. -/
theorem DB.parseErrorCode?_statementNotFound_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .statementNotFound →
    ∃ label, s.errorEvidence? = some (.proofCheck (.statementNotFound label)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .statementNotFound h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

/-- Decoded `.hypothesisNotFound` yields proof-check evidence with label. -/
theorem DB.parseErrorCode?_hypothesisNotFound_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .hypothesisNotFound →
    ∃ label, s.errorEvidence? = some (.proofCheck (.hypothesisNotFound label)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .hypothesisNotFound h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

/-- Decoded `.hypothesisNotInDatabaseScope` yields proof-check evidence with label. -/
theorem DB.parseErrorCode?_hypothesisNotInDatabaseScope_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .hypothesisNotInDatabaseScope →
    ∃ label, s.errorEvidence? = some (.proofCheck (.hypothesisNotInDatabaseScope label)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .hypothesisNotInDatabaseScope h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

/-- Decoded `.mandatoryHypothesisNotFoundInDatabase` yields proof-check evidence with label. -/
theorem DB.parseErrorCode?_mandatoryHypothesisNotFoundInDatabase_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .mandatoryHypothesisNotFoundInDatabase →
    ∃ label,
      s.errorEvidence? = some (.proofCheck (.mandatoryHypothesisNotFoundInDatabase label)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .mandatoryHypothesisNotFoundInDatabase h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

/-- Decoded `.stackUnderflow` yields proof-check evidence with stack sizes. -/
theorem DB.parseErrorCode?_stackUnderflow_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .stackUnderflow →
    ∃ needed haveSize,
      s.errorEvidence? = some (.proofCheck (.stackUnderflow needed haveSize)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .stackUnderflow h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

/-- Decoded `.disjointVariableViolation` yields proof-check evidence (no payload). -/
theorem DB.parseErrorCode?_disjointVariableViolation_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .disjointVariableViolation →
    s.errorEvidence? = some (.proofCheck .disjointVariableViolation) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .disjointVariableViolation h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

/-- Decoded `.typeErrorInSubstitution` yields proof-check evidence (no payload). -/
theorem DB.parseErrorCode?_typeErrorInSubstitution_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .typeErrorInSubstitution →
    s.errorEvidence? = some (.proofCheck .typeErrorInSubstitution) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .typeErrorInSubstitution h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

/-- Decoded `.proofBackrefIndexOutOfRange` yields proof-check evidence with index + heap size. -/
theorem DB.parseErrorCode?_proofBackrefIndexOutOfRange_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .proofBackrefIndexOutOfRange →
    ∃ index heapSize,
      s.errorEvidence? = some (.proofCheck (.proofBackrefIndexOutOfRange index heapSize)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .proofBackrefIndexOutOfRange h_code
  simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [ProofCheckError.code]

-- TheoremFinality family (both codes)

/-- Decoded `.theoremClaimMismatch` yields theorem-finality evidence with claim + top formulas. -/
theorem DB.parseErrorCode?_theoremClaimMismatch_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .theoremClaimMismatch →
    ∃ claim top,
      s.errorEvidence? = some (.theoremFinality (.theoremClaimMismatch claim top)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .theoremClaimMismatch h_code
  simp only [DB.RuleSemanticViolation, DB.TheoremFinalityViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [TheoremFinalityError.code]

/-- Decoded `.theoremMoreThanOneStackElement` yields theorem-finality evidence with stack size. -/
theorem DB.parseErrorCode?_theoremMoreThanOneStackElement_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .theoremMoreThanOneStackElement →
    ∃ stackSize,
      s.errorEvidence? = some (.theoremFinality (.theoremMoreThanOneStackElement stackSize)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .theoremMoreThanOneStackElement h_code
  simp only [DB.RuleSemanticViolation, DB.TheoremFinalityViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [TheoremFinalityError.code]

-- checkBytes lifts for the new guardFacts

theorem checkBytes_parseErrorCode?_statementNotFound_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .statementNotFound →
    ∃ label, (checkBytes arr config).errorEvidence? =
      some (.proofCheck (.statementNotFound label)) := by
  exact DB.parseErrorCode?_statementNotFound_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_hypothesisNotFound_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .hypothesisNotFound →
    ∃ label, (checkBytes arr config).errorEvidence? =
      some (.proofCheck (.hypothesisNotFound label)) := by
  exact DB.parseErrorCode?_hypothesisNotFound_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_hypothesisNotInDatabaseScope_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .hypothesisNotInDatabaseScope →
    ∃ label, (checkBytes arr config).errorEvidence? =
      some (.proofCheck (.hypothesisNotInDatabaseScope label)) := by
  exact DB.parseErrorCode?_hypothesisNotInDatabaseScope_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_mandatoryHypothesisNotFoundInDatabase_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .mandatoryHypothesisNotFoundInDatabase →
    ∃ label, (checkBytes arr config).errorEvidence? =
      some (.proofCheck (.mandatoryHypothesisNotFoundInDatabase label)) := by
  exact DB.parseErrorCode?_mandatoryHypothesisNotFoundInDatabase_guardFacts
    (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_stackUnderflow_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .stackUnderflow →
    ∃ needed haveSize, (checkBytes arr config).errorEvidence? =
      some (.proofCheck (.stackUnderflow needed haveSize)) := by
  exact DB.parseErrorCode?_stackUnderflow_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_disjointVariableViolation_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .disjointVariableViolation →
    (checkBytes arr config).errorEvidence? =
      some (.proofCheck .disjointVariableViolation) := by
  exact DB.parseErrorCode?_disjointVariableViolation_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_typeErrorInSubstitution_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .typeErrorInSubstitution →
    (checkBytes arr config).errorEvidence? =
      some (.proofCheck .typeErrorInSubstitution) := by
  exact DB.parseErrorCode?_typeErrorInSubstitution_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_proofBackrefIndexOutOfRange_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .proofBackrefIndexOutOfRange →
    ∃ index heapSize, (checkBytes arr config).errorEvidence? =
      some (.proofCheck (.proofBackrefIndexOutOfRange index heapSize)) := by
  exact DB.parseErrorCode?_proofBackrefIndexOutOfRange_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_theoremClaimMismatch_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .theoremClaimMismatch →
    ∃ claim top, (checkBytes arr config).errorEvidence? =
      some (.theoremFinality (.theoremClaimMismatch claim top)) := by
  exact DB.parseErrorCode?_theoremClaimMismatch_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_theoremMoreThanOneStackElement_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .theoremMoreThanOneStackElement →
    ∃ stackSize, (checkBytes arr config).errorEvidence? =
      some (.theoremFinality (.theoremMoreThanOneStackElement stackSize)) := by
  exact DB.parseErrorCode?_theoremMoreThanOneStackElement_guardFacts (s := checkBytes arr config)

end Verify
end Metamath
