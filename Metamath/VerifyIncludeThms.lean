import Metamath.Verify
import Metamath.VerifyIncludeBoundary
import Metamath.VerifyDBSemanticThms
import Metamath.VerifyDBPayloadThms
import Metamath.VerifyClauseThms

namespace Metamath
namespace Verify

theorem includeDirectiveViolation?_inInnerScope_iff
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.inInnerScope pos scopeDepth inStatement config.allowIncludeInnerScope) ↔
      (!config.allowIncludeInnerScope && scopeDepth > 0) = true := by
  unfold includeDirectiveViolation?
  by_cases h_inner : (!config.allowIncludeInnerScope && scopeDepth > 0) = true
  · simp [h_inner]
  · simp [h_inner]

theorem includeDirectiveViolation?_insideStatement_iff
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing) ↔
      (!config.allowIncludeInnerScope && scopeDepth > 0) = false ∧
      (!config.allowTokenSplicing && inStatement) = true := by
  unfold includeDirectiveViolation?
  by_cases h_inner : (!config.allowIncludeInnerScope && scopeDepth > 0) = true
  · simp [h_inner]
  · by_cases h_stmt : (!config.allowTokenSplicing && inStatement) = true
    · simp [h_inner, h_stmt]
    · simp [h_inner, h_stmt]

theorem includeDirectiveViolation?_inInnerScope_implies_scopeDepth_pos
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.inInnerScope pos scopeDepth inStatement config.allowIncludeInnerScope) →
      (scopeDepth > 0) = true := by
  intro h_inner
  have h_gate :=
    (includeDirectiveViolation?_inInnerScope_iff config scopeDepth inStatement pos).1 h_inner
  have h_parts : (!config.allowIncludeInnerScope = true) ∧ ((scopeDepth > 0) = true) := by
    simpa [Bool.and_eq_true] using h_gate
  exact h_parts.2

theorem includeDirectiveViolation?_inInnerScope_implies_allowIncludeInnerScope_false
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.inInnerScope pos scopeDepth inStatement config.allowIncludeInnerScope) →
      config.allowIncludeInnerScope = false := by
  intro h_inner
  have h_gate :=
    (includeDirectiveViolation?_inInnerScope_iff config scopeDepth inStatement pos).1 h_inner
  have h_parts : (!config.allowIncludeInnerScope = true) ∧ ((scopeDepth > 0) = true) := by
    simpa [Bool.and_eq_true] using h_gate
  by_cases h_allow : config.allowIncludeInnerScope
  · have : False := by
      simp [h_allow] at h_parts
    exact False.elim this
  · simp [h_allow]

theorem includeDirectiveViolation?_insideStatement_implies_inStatement_true
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing) →
      inStatement = true := by
  intro h_stmt
  have h_gate :=
    (includeDirectiveViolation?_insideStatement_iff config scopeDepth inStatement pos).1 h_stmt
  have h_parts : (!config.allowTokenSplicing = true) ∧ (inStatement = true) := by
    simpa [Bool.and_eq_true] using h_gate.2
  exact h_parts.2

theorem includeDirectiveViolation?_insideStatement_implies_allowTokenSplicing_false
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing) →
      config.allowTokenSplicing = false := by
  intro h_stmt
  have h_gate :=
    (includeDirectiveViolation?_insideStatement_iff config scopeDepth inStatement pos).1 h_stmt
  have h_parts : (!config.allowTokenSplicing = true) ∧ (inStatement = true) := by
    simpa [Bool.and_eq_true] using h_gate.2
  by_cases h_allow : config.allowTokenSplicing
  · have : False := by
      simp [h_allow] at h_parts
    exact False.elim this
  · simp [h_allow]

theorem includeDirectiveViolation?_inInnerScope_implies_guardFacts
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.inInnerScope pos scopeDepth inStatement config.allowIncludeInnerScope) →
      config.allowIncludeInnerScope = false ∧ (scopeDepth > 0) = true := by
  intro h_inner
  exact ⟨
    includeDirectiveViolation?_inInnerScope_implies_allowIncludeInnerScope_false config scopeDepth inStatement pos h_inner,
    includeDirectiveViolation?_inInnerScope_implies_scopeDepth_pos config scopeDepth inStatement pos h_inner
  ⟩

theorem includeDirectiveViolation?_insideStatement_implies_guardFacts
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing) →
      config.allowTokenSplicing = false ∧ inStatement = true := by
  intro h_stmt
  exact ⟨
    includeDirectiveViolation?_insideStatement_implies_allowTokenSplicing_false config scopeDepth inStatement pos h_stmt,
    includeDirectiveViolation?_insideStatement_implies_inStatement_true config scopeDepth inStatement pos h_stmt
  ⟩

@[simp] theorem includePreprocessErrorDB_errorEvidence
    (config : ModeConfig) (err : IncludeError) :
    (includePreprocessErrorDB config err).errorEvidence? = some (.includeErr err) := by
  simp [includePreprocessErrorDB, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]

@[simp] theorem includePreprocessErrorDB_parseErrorCode
    (config : ModeConfig) (err : IncludeError) :
    (includePreprocessErrorDB config err).parseErrorCode? = some (IncludeError.code err) := by
  simp [includePreprocessErrorDB, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.parseErrorCode?, ErrorEvidence.code, IncludeError.code]

/-- Include-preprocessor inversion (inner-scope): decoded code implies live gate facts. -/
theorem includePreprocessErrorDB_inInnerScope_guardFacts
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    (includePreprocessErrorDB config
      (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)).parseErrorCode? =
      some .includeInInnerScope ->
      config.allowIncludeInnerScope = false ∧ depth ≠ 0 := by
  intro _h_code
  exact ⟨h_allow, h_depth⟩

/-- Include-preprocessor inversion (inner-scope), parameterized by the pure gate witness
instead of manual assumptions. -/
theorem includePreprocessErrorDB_inInnerScope_guardFacts_of_gate
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config depth inStatement pos =
        some (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)) :
    (includePreprocessErrorDB config
      (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)).parseErrorCode? =
      some .includeInInnerScope ->
      config.allowIncludeInnerScope = false ∧ depth ≠ 0 := by
  intro h_code
  have h_guard :=
    includeDirectiveViolation?_inInnerScope_implies_guardFacts
      config depth inStatement pos h_gate
  have h_depth_ne_zero : depth ≠ 0 := by
    intro h_zero
    have h_depth_pos_true : (depth > 0) = true := h_guard.2
    simp [h_zero] at h_depth_pos_true
  exact includePreprocessErrorDB_inInnerScope_guardFacts
    config pos depth inStatement h_guard.1 h_depth_ne_zero h_code

/-- Include-preprocessor inversion (inside-statement): decoded code implies live gate facts. -/
theorem includePreprocessErrorDB_insideStatement_guardFacts
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    (includePreprocessErrorDB config
      (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)).parseErrorCode? =
      some .includeInsideStatement ->
      config.allowTokenSplicing = false ∧ inStatement = true := by
  intro _h_code
  exact ⟨h_allow, h_stmt⟩

/-- Include-preprocessor inversion (inside-statement), parameterized by the pure gate
witness instead of manual assumptions. -/
theorem includePreprocessErrorDB_insideStatement_guardFacts_of_gate
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config scopeDepth inStatement pos =
        some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)) :
    (includePreprocessErrorDB config
      (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)).parseErrorCode? =
      some .includeInsideStatement ->
      config.allowTokenSplicing = false ∧ inStatement = true := by
  intro h_code
  have h_guard :=
    includeDirectiveViolation?_insideStatement_implies_guardFacts
      config scopeDepth inStatement pos h_gate
  exact includePreprocessErrorDB_insideStatement_guardFacts
    config pos scopeDepth inStatement h_guard.1 h_guard.2 h_code

/-- End-to-end include inversion at the check-entry boundary (inner-scope branch). -/
theorem checkExpandedResult_inInnerScope_guardFacts
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    (checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope ->
      config.allowIncludeInnerScope = false ∧ depth ≠ 0 := by
  intro h_code
  simpa [checkExpandedResult] using
    (includePreprocessErrorDB_inInnerScope_guardFacts config pos depth inStatement h_allow h_depth h_code)

/-- End-to-end include inversion at the check-entry boundary (inner-scope branch),
parameterized by the pure include gate witness. -/
theorem checkExpandedResult_inInnerScope_guardFacts_of_gate
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config depth inStatement pos =
        some (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)) :
    (checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope ->
      config.allowIncludeInnerScope = false ∧ depth ≠ 0 := by
  intro h_code
  simpa [checkExpandedResult] using
    (includePreprocessErrorDB_inInnerScope_guardFacts_of_gate
      config pos depth inStatement h_gate h_code)

/-- End-to-end include inversion at the check-entry boundary (inside-statement branch). -/
theorem checkExpandedResult_insideStatement_guardFacts
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    (checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement ->
      config.allowTokenSplicing = false ∧ inStatement = true := by
  intro h_code
  simpa [checkExpandedResult] using
    (includePreprocessErrorDB_insideStatement_guardFacts config pos scopeDepth inStatement h_allow h_stmt h_code)

/-- End-to-end include inversion at the check-entry boundary (inside-statement branch),
parameterized by the pure include gate witness. -/
theorem checkExpandedResult_insideStatement_guardFacts_of_gate
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config scopeDepth inStatement pos =
        some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)) :
    (checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement ->
      config.allowTokenSplicing = false ∧ inStatement = true := by
  intro h_code
  simpa [checkExpandedResult] using
    (includePreprocessErrorDB_insideStatement_guardFacts_of_gate
      config pos scopeDepth inStatement h_gate h_code)

theorem checkBytes_parseErrorCode?_includeInInnerScope_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
    ∃ pos depth inStatement allowIncludeInnerScopeWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness)) := by
  intro h_code
  exact DB.parseErrorCode?_includeInInnerScope_guardFacts
    (s := checkBytes arr config) h_code

theorem checkBytes_parseErrorCode?_includeInsideStatement_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
    ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness)) := by
  intro h_code
  exact DB.parseErrorCode?_includeInsideStatement_guardFacts
    (s := checkBytes arr config) h_code

/-- Backward-compatible alias for include-in-inner-scope checkBytes guard facts. -/
theorem checkBytes_parseErrorCode?_includeInInnerScope_guardFacts_of_gateWitness
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
    ∃ pos depth inStatement allowIncludeInnerScopeWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness)) := by
  intro h_code
  exact checkBytes_parseErrorCode?_includeInInnerScope_guardFacts arr config h_code

/-- Backward-compatible alias for include-inside-statement checkBytes guard facts. -/
theorem checkBytes_parseErrorCode?_includeInsideStatement_guardFacts_of_gateWitness
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
    ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness)) := by
  intro h_code
  exact checkBytes_parseErrorCode?_includeInsideStatement_guardFacts arr config h_code

/-- Decoded `.includeCycleDetected` yields include-cycle evidence with the cycle path. -/
theorem DB.parseErrorCode?_includeCycleDetected_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .includeCycleDetected →
    ∃ path, s.errorEvidence? = some (.includeErr (.cycleDetected path)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .includeCycleDetected h_code
  simp only [DB.RuleSemanticViolation, DB.IncludeViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [IncludeError.code]

/-- Decoded `.includeDepthExceeded` yields depth-limit evidence with the file path. -/
theorem DB.parseErrorCode?_includeDepthExceeded_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .includeDepthExceeded →
    ∃ path, s.errorEvidence? = some (.includeErr (.depthExceeded path)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .includeDepthExceeded h_code
  simp only [DB.RuleSemanticViolation, DB.IncludeViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [IncludeError.code]

/-- Decoded `.includeExtractedEmptyPath` yields evidence with positional context. -/
theorem DB.parseErrorCode?_includeExtractedEmptyPath_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .includeExtractedEmptyPath →
    ∃ startPos endPos file,
      s.errorEvidence? = some (.includeErr (.extractedEmptyPath startPos endPos file)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .includeExtractedEmptyPath h_code
  simp only [DB.RuleSemanticViolation, DB.IncludeViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [IncludeError.code]

/-- Decoded `.includeEmptyPathBeforeNormalization` yields evidence with file context. -/
theorem DB.parseErrorCode?_includeEmptyPathBeforeNormalization_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .includeEmptyPathBeforeNormalization →
    ∃ file,
      s.errorEvidence? = some (.includeErr (.emptyPathBeforeNormalization file)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .includeEmptyPathBeforeNormalization h_code
  simp only [DB.RuleSemanticViolation, DB.IncludeViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [IncludeError.code]

/-- Decoded `.includePathEmptyAfterNormalization` yields evidence with original path + file. -/
theorem DB.parseErrorCode?_includePathEmptyAfterNormalization_guardFacts
    (s : DB) :
    s.parseErrorCode? = some .includePathEmptyAfterNormalization →
    ∃ origPath file,
      s.errorEvidence? = some (.includeErr (.pathEmptyAfterNormalization origPath file)) := by
  intro h_code
  have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .includePathEmptyAfterNormalization h_code
  simp only [DB.RuleSemanticViolation, DB.IncludeViolation] at h_rule
  obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
  cases err <;> simp_all [IncludeError.code]

theorem checkBytes_parseErrorCode?_includeCycleDetected_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeCycleDetected →
    ∃ path, (checkBytes arr config).errorEvidence? =
      some (.includeErr (.cycleDetected path)) := by
  exact DB.parseErrorCode?_includeCycleDetected_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_includeExtractedEmptyPath_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeExtractedEmptyPath →
    ∃ startPos endPos file, (checkBytes arr config).errorEvidence? =
      some (.includeErr (.extractedEmptyPath startPos endPos file)) := by
  exact DB.parseErrorCode?_includeExtractedEmptyPath_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_includeEmptyPathBeforeNormalization_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeEmptyPathBeforeNormalization →
    ∃ file, (checkBytes arr config).errorEvidence? =
      some (.includeErr (.emptyPathBeforeNormalization file)) := by
  exact DB.parseErrorCode?_includeEmptyPathBeforeNormalization_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_includePathEmptyAfterNormalization_guardFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includePathEmptyAfterNormalization →
    ∃ origPath file, (checkBytes arr config).errorEvidence? =
      some (.includeErr (.pathEmptyAfterNormalization origPath file)) := by
  exact DB.parseErrorCode?_includePathEmptyAfterNormalization_guardFacts (s := checkBytes arr config)

theorem checkBytes_parseErrorCode?_includeInInnerScope_payload_inversion
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
    (checkBytes arr config).IncludeInInnerScopePayloadWitness := by
  intro h_code
  exact DB.parseErrorCode?_includeInInnerScope_payload_inversion
    (s := checkBytes arr config) h_code

theorem checkBytes_parseErrorCode?_includeInsideStatement_payload_inversion
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
    (checkBytes arr config).IncludeInsideStatementPayloadWitness := by
  intro h_code
  exact DB.parseErrorCode?_includeInsideStatement_payload_inversion
    (s := checkBytes arr config) h_code

theorem checkBytes_parseErrorCode?_includeCycleDetected_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeCycleDetected →
    (checkBytes arr config).RuleClauseSemanticViolation .includeCycleDetected := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) .includeCycleDetected h_code

theorem checkBytes_parseErrorCode?_includeInInnerScope_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
    (checkBytes arr config).RuleClauseSemanticViolation .includeInInnerScope := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) .includeInInnerScope h_code

theorem checkBytes_parseErrorCode?_includeInsideStatement_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
    (checkBytes arr config).RuleClauseSemanticViolation .includeInsideStatement := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) .includeInsideStatement h_code

theorem checkBytes_parseErrorCode?_includeExtractedEmptyPath_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeExtractedEmptyPath →
    (checkBytes arr config).RuleClauseSemanticViolation .includeExtractedEmptyPath := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) .includeExtractedEmptyPath h_code

theorem checkBytes_parseErrorCode?_includeEmptyPathBeforeNormalization_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeEmptyPathBeforeNormalization →
    (checkBytes arr config).RuleClauseSemanticViolation .includeEmptyPathBeforeNormalization := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) .includeEmptyPathBeforeNormalization h_code

theorem checkBytes_parseErrorCode?_includePathEmptyAfterNormalization_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includePathEmptyAfterNormalization →
    (checkBytes arr config).RuleClauseSemanticViolation .includePathEmptyAfterNormalization := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) .includePathEmptyAfterNormalization h_code

theorem checkBytes_parseErrorCode?_includeReadFailure_ruleClause
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeReadFailure →
    (checkBytes arr config).RuleClauseSemanticViolation .includeReadFailure := by
  intro h_code
  exact DB.parseErrorCode?_ruleClauseSemantic_sound
    (s := checkBytes arr config) .includeReadFailure h_code

theorem parseErrorCode_specClause_includeInInnerScope :
    ParseErrorCode.specClause .includeInInnerScope = .sec4_1_2_includes := rfl

theorem parseErrorCode_specClause_includeInsideStatement :
    ParseErrorCode.specClause .includeInsideStatement = .sec4_1_2_includes := rfl

theorem parseErrorCode_specClause_includeCycleDetected :
    ParseErrorCode.specClause .includeCycleDetected = .sec4_1_2_includes := rfl

theorem parseErrorCode_specClause_includeReadFailure :
    ParseErrorCode.specClause .includeReadFailure = .sec4_1_2_includes := rfl

/-- Any decoded `includePreprocessErrorDB` code carries concrete error evidence. -/
theorem includePreprocessErrorDB_parseErrorCode?_has_evidence
    (config : ModeConfig) (err : IncludeError) (code : ParseErrorCode) :
    (includePreprocessErrorDB config err).parseErrorCode? = some code →
    ∃ ev, (includePreprocessErrorDB config err).errorEvidence? = some ev := by
  intro h_code
  rcases DB.parseErrorCode?_sound (s := includePreprocessErrorDB config err) code h_code with
    ⟨_pos, _msg, _idx, ev, _h_err, h_ev, _h_ev_code⟩
  exact ⟨ev, h_ev⟩

/-- Any decoded `checkExpandedResult` code carries concrete error evidence. -/
theorem checkExpandedResult_parseErrorCode?_has_evidence
    (config : ModeConfig)
    (expanded : Except IncludeError (ByteArray × Std.HashSet String))
    (code : ParseErrorCode) :
    (checkExpandedResult config expanded).parseErrorCode? = some code →
    ∃ ev, (checkExpandedResult config expanded).errorEvidence? = some ev := by
  intro h_code
  rcases DB.parseErrorCode?_sound (s := checkExpandedResult config expanded) code h_code with
    ⟨_pos, _msg, _idx, ev, _h_err, h_ev, _h_ev_code⟩
  exact ⟨ev, h_ev⟩

/-- Non-internal include-preprocessor codes are evidence-first and exclude the legacy
raw-error compatibility payload. -/
theorem includePreprocessErrorDB_nonInternal_evidenceFirst
    (config : ModeConfig) (err : IncludeError) (code : ParseErrorCode)
    (h_code : (includePreprocessErrorDB config err).parseErrorCode? = some code)
    (h_noninternal : code ≠ .internalIllFormedDatabaseAfterParse) :
    ∃ ev,
      (includePreprocessErrorDB config err).errorEvidence? = some ev ∧
      ev ≠ .internalGate false false false := by
  rcases DB.parseErrorCode?_sound (s := includePreprocessErrorDB config err) code h_code with
    ⟨_pos, _msg, _idx, ev, _h_err, h_ev, h_ev_code⟩
  refine ⟨ev, h_ev, ?_⟩
  intro h_ev_internal
  have h_code_internal : code = .internalIllFormedDatabaseAfterParse := by
    have h_internal_code : (ErrorEvidence.internalGate false false false).code = code := by
      simpa [h_ev_internal] using h_ev_code
    simpa [ErrorEvidence.code] using h_internal_code.symm
  exact h_noninternal h_code_internal

/-- Non-internal check-entry (`checkExpandedResult`) decoded codes are evidence-first and
exclude the legacy raw-error compatibility payload. -/
theorem checkExpandedResult_nonInternal_evidenceFirst
    (config : ModeConfig)
    (expanded : Except IncludeError (ByteArray × Std.HashSet String))
    (code : ParseErrorCode)
    (h_code : (checkExpandedResult config expanded).parseErrorCode? = some code)
    (h_noninternal : code ≠ .internalIllFormedDatabaseAfterParse) :
    ∃ ev,
      (checkExpandedResult config expanded).errorEvidence? = some ev ∧
      ev ≠ .internalGate false false false := by
  rcases DB.parseErrorCode?_sound (s := checkExpandedResult config expanded) code h_code with
    ⟨_pos, _msg, _idx, ev, _h_err, h_ev, h_ev_code⟩
  refine ⟨ev, h_ev, ?_⟩
  intro h_ev_internal
  have h_code_internal : code = .internalIllFormedDatabaseAfterParse := by
    have h_internal_code : (ErrorEvidence.internalGate false false false).code = code := by
      simpa [h_ev_internal] using h_ev_code
    simpa [ErrorEvidence.code] using h_internal_code.symm
  exact h_noninternal h_code_internal

end Verify
end Metamath
