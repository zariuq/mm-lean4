import Metamath.Verify
import Metamath.Spec.Frontend
import Metamath.FrontendCertified

namespace Metamath.Verify.FrontendBridge

open Metamath.Spec.Frontend

/-- Bridge projection from verifier DB state to front-end `$d` spec state. -/
def DB.toDjvarsState (db : DB) : DjvarsState where
  isVar := db.isVar

/-- Bridge projection from verifier DB state to front-end math-symbol spec state. -/
def DB.toMathSymbolState (db : DB) : MathSymbolState where
  isSym := db.isSym

/-- Bridge projection from verifier mode config to front-end include-policy state. -/
def ModeConfig.toIncludePolicy (config : ModeConfig) : IncludePolicy where
  allowIncludeInnerScope := config.allowIncludeInnerScope
  allowTokenSplicing := config.allowTokenSplicing

/-- Bridge projection from verifier DB state to top-level `$e` policy state. -/
def DB.toTopLevelEssState (db : DB) : TopLevelEssState where
  rejectToplevelEss := db.config.rejectToplevelEss
  scopeDepth := db.scopes.size

/-- `$d` gate equivalence against the front-end admissibility predicate. -/
theorem DB.djvarsScopeViolation?_none_iff_frontendAdmissible
    (db : DB) (sym : String) :
    db.djvarsScopeViolation? sym = none ↔
      DjvarsSymbolAdmissible (DB.toDjvarsState db) sym := by
  unfold DB.djvarsScopeViolation? DjvarsSymbolAdmissible DB.toDjvarsState
  by_cases h_var : db.isVar sym
  · simp [h_var]
  · simp [h_var]

/-- Any emitted `$d` gate error implies front-end inadmissibility. -/
theorem DB.djvarsScopeViolation?_some_implies_frontendNotAdmissible
    (db : DB) (sym : String) (err : ScopeDeclError) :
    db.djvarsScopeViolation? sym = some err →
      ¬ DjvarsSymbolAdmissible (DB.toDjvarsState db) sym := by
  intro h_some h_adm
  have h_none : db.djvarsScopeViolation? sym = none :=
    (DB.djvarsScopeViolation?_none_iff_frontendAdmissible db sym).2 h_adm
  have h_contra : (some err : Option ScopeDeclError) = none := by
    rw [h_some] at h_none
    exact h_none
  cases h_contra

/-- Front-end `$d` inadmissibility produces some verifier-side gate error. -/
theorem DB.djvarsScopeViolation?_frontendNotAdmissible_implies_exists
    (db : DB) (sym : String) :
    ¬ DjvarsSymbolAdmissible (DB.toDjvarsState db) sym →
      ∃ err, db.djvarsScopeViolation? sym = some err := by
  intro h_not
  cases h_gate : db.djvarsScopeViolation? sym with
  | none =>
      have h_adm :
          DjvarsSymbolAdmissible (DB.toDjvarsState db) sym :=
        (DB.djvarsScopeViolation?_none_iff_frontendAdmissible db sym).1 h_gate
      exact False.elim (h_not h_adm)
  | some err =>
      exact ⟨err, rfl⟩

/-- Math-symbol gate equivalence against the front-end admissibility predicate. -/
theorem DB.mathSymbolViolation?_none_iff_frontendAdmissible
    (db : DB) (sym : String) :
    db.mathSymbolViolation? sym = none ↔
      MathSymbolAdmissible (DB.toMathSymbolState db) sym := by
  unfold DB.mathSymbolViolation? MathSymbolAdmissible DB.toMathSymbolState
  by_cases h_sym : db.isSym sym
  · simp [h_sym]
  · simp [h_sym]

/-- Any emitted math-symbol gate error implies front-end inadmissibility. -/
theorem DB.mathSymbolViolation?_some_implies_frontendNotAdmissible
    (db : DB) (sym : String) (err : ScopeDeclError) :
    db.mathSymbolViolation? sym = some err →
      ¬ MathSymbolAdmissible (DB.toMathSymbolState db) sym := by
  intro h_some h_adm
  have h_none : db.mathSymbolViolation? sym = none :=
    (DB.mathSymbolViolation?_none_iff_frontendAdmissible db sym).2 h_adm
  have h_contra : (some err : Option ScopeDeclError) = none := by
    rw [h_some] at h_none
    exact h_none
  cases h_contra

/-- Front-end math-symbol inadmissibility produces some verifier-side gate error. -/
theorem DB.mathSymbolViolation?_frontendNotAdmissible_implies_exists
    (db : DB) (sym : String) :
    ¬ MathSymbolAdmissible (DB.toMathSymbolState db) sym →
      ∃ err, db.mathSymbolViolation? sym = some err := by
  intro h_not
  cases h_gate : db.mathSymbolViolation? sym with
  | none =>
      have h_adm :
          MathSymbolAdmissible (DB.toMathSymbolState db) sym :=
        (DB.mathSymbolViolation?_none_iff_frontendAdmissible db sym).1 h_gate
      exact False.elim (h_not h_adm)
  | some err =>
      exact ⟨err, rfl⟩

/-- Include gate equivalence against the front-end admissibility predicate. -/
theorem includeDirectiveViolation?_none_iff_frontendAdmissible
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? config scopeDepth inStatement pos = none ↔
      IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  unfold includeDirectiveViolation? IncludeDirectiveAdmissible ModeConfig.toIncludePolicy
  by_cases h_inner : (!config.allowIncludeInnerScope && scopeDepth > 0) = true
  · simp [h_inner]
  · by_cases h_stmt : (!config.allowTokenSplicing && inStatement) = true
    · simp [h_inner, h_stmt]
    · simp [h_inner, h_stmt]

/-- Any include gate error implies front-end include inadmissibility. -/
theorem includeDirectiveViolation?_some_implies_frontendNotAdmissible
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) (err : IncludeError) :
    includeDirectiveViolation? config scopeDepth inStatement pos = some err →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  intro h_some h_adm
  have h_none : includeDirectiveViolation? config scopeDepth inStatement pos = none :=
    (includeDirectiveViolation?_none_iff_frontendAdmissible config scopeDepth inStatement pos).2 h_adm
  have h_contra : (some err : Option IncludeError) = none := by
    rw [h_some] at h_none
    exact h_none
  cases h_contra

/-- Front-end include inadmissibility produces some verifier-side include gate error. -/
theorem includeDirectiveViolation?_frontendNotAdmissible_implies_exists
    (config : ModeConfig) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement →
      ∃ err, includeDirectiveViolation? config scopeDepth inStatement pos = some err := by
  intro h_not
  cases h_gate : includeDirectiveViolation? config scopeDepth inStatement pos with
  | none =>
      have h_adm :
          IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement :=
        (includeDirectiveViolation?_none_iff_frontendAdmissible config scopeDepth inStatement pos).1 h_gate
      exact False.elim (h_not h_adm)
  | some err =>
      exact ⟨err, rfl⟩

/-- Top-level `$e` gate equivalence against the front-end admissibility predicate. -/
theorem topLevelEssViolation?_none_iff_frontendAdmissible
    (db : DB) :
    ParserState.topLevelEssViolation? db = none ↔
      TopLevelEssentialAdmissible (DB.toTopLevelEssState db) := by
  unfold ParserState.topLevelEssViolation? TopLevelEssentialAdmissible DB.toTopLevelEssState
  by_cases h_gate : (db.config.rejectToplevelEss && db.scopes.size == 0) = true
  · simp [h_gate]
  · simp [h_gate]

/-- Any top-level `$e` gate error implies front-end inadmissibility. -/
theorem topLevelEssViolation?_some_implies_frontendNotAdmissible
    (db : DB) (err : ScopeDeclError) :
    ParserState.topLevelEssViolation? db = some err →
      ¬ TopLevelEssentialAdmissible (DB.toTopLevelEssState db) := by
  intro h_some h_adm
  have h_none : ParserState.topLevelEssViolation? db = none :=
    (topLevelEssViolation?_none_iff_frontendAdmissible db).2 h_adm
  have h_contra : (some err : Option ScopeDeclError) = none := by
    rw [h_some] at h_none
    exact h_none
  cases h_contra

/-- Front-end top-level `$e` inadmissibility produces some verifier-side gate error. -/
theorem topLevelEssViolation?_frontendNotAdmissible_implies_exists
    (db : DB) :
    ¬ TopLevelEssentialAdmissible (DB.toTopLevelEssState db) →
      ∃ err, ParserState.topLevelEssViolation? db = some err := by
  intro h_not
  cases h_gate : ParserState.topLevelEssViolation? db with
  | none =>
      have h_adm :
          TopLevelEssentialAdmissible (DB.toTopLevelEssState db) :=
        (topLevelEssViolation?_none_iff_frontendAdmissible db).1 h_gate
      exact False.elim (h_not h_adm)
  | some err =>
      exact ⟨err, rfl⟩

/-- `checkBytes` top-level strict-mode code carries canonical scope evidence + gate facts. -/
theorem checkBytes_topLevelEssentialNotAllowed_implies_frontendGateFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
    (checkBytes arr config).errorEvidence? =
      some (.scopeDecl (.topLevelEssentialNotAllowed)) ∧
    TopLevelEssentialGateFacts true 0 := by
  intro h_code
  have h_ev :=
    checkBytes_parseErrorCode?_topLevelEssentialNotAllowed_guardFacts arr config h_code
  exact ⟨h_ev, rfl, rfl⟩

/-- `checkBytes` top-level strict-mode code carries canonical witness payload. -/
theorem checkBytes_topLevelEssentialNotAllowed_implies_frontendWitness
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
    (checkBytes arr config).errorEvidence? =
      some (.scopeDecl (.topLevelEssentialNotAllowed)) := by
  intro h_code
  exact (checkBytes_topLevelEssentialNotAllowed_implies_frontendGateFacts arr config h_code).1

/-- `checkBytes` top-level strict-mode code implies frontend inadmissibility,
under certified-run gate/reflection facts. -/
theorem checkBytes_topLevelEssentialNotAllowed_implies_frontendNotAdmissible
    (arr : ByteArray) (config : ModeConfig)
    (h_cert : Metamath.Verify.FrontendCertified.CheckBytesFrontendCertifiedRun arr config) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
    ¬ TopLevelEssentialAdmissible (DB.toTopLevelEssState (checkBytes arr config)) := by
  intro h_code
  rcases h_cert.topLevelEssential_gateFacts h_code with ⟨h_reject, h_scope⟩
  have h_some :
      ParserState.topLevelEssViolation? (checkBytes arr config) =
        some (.topLevelEssentialNotAllowed) := by
    have h_gate :
        ((checkBytes arr config).config.rejectToplevelEss &&
          (checkBytes arr config).scopes.size == 0) = true := by
      rw [h_reject, h_scope]
      simp
    exact (ParserState.topLevelEssViolation?_eq_some_topLevelEssentialNotAllowed_iff
      (db := checkBytes arr config)).2 h_gate
  exact topLevelEssViolation?_some_implies_frontendNotAdmissible
    (db := checkBytes arr config) (.topLevelEssentialNotAllowed) h_some

/-- `checkBytes` top-level strict-mode code has certified witness existence. -/
theorem checkBytes_topLevelEssentialNotAllowed_certifiedWitness_exists
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .topLevelEssentialNotAllowed →
    ∃ rejectToplevelEssWitness scopeDepthWitness,
      (checkBytes arr config).errorEvidence? =
        some (.scopeDecl (.topLevelEssentialNotAllowed)) ∧
      rejectToplevelEssWitness = true ∧
      scopeDepthWitness = 0 := by
  intro h_code
  have h_ev := checkBytes_topLevelEssentialNotAllowed_implies_frontendWitness arr config h_code
  exact ⟨true, 0, h_ev, rfl, rfl⟩

/-- `checkBytes` token-not-const/var code carries canonical scope evidence + gate facts. -/
theorem checkBytes_tokenNotConstantOrVariable_implies_frontendGateFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
    ∃ sym,
      (checkBytes arr config).errorEvidence? =
        some (.scopeDecl (.tokenNotConstantOrVariable sym)) ∧
      MathSymbolGateFacts false := by
  intro h_code
  rcases checkBytes_parseErrorCode?_tokenNotConstantOrVariable_guardFacts arr config h_code with
    ⟨sym, h_ev⟩
  exact ⟨sym, h_ev, rfl⟩

/-- `checkBytes` token-not-const/var code has certified witness existence. -/
theorem checkBytes_tokenNotConstantOrVariable_certifiedWitness_exists
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
    ∃ sym isSymWitness,
      (checkBytes arr config).errorEvidence? =
        some (.scopeDecl (.tokenNotConstantOrVariable sym)) ∧
      isSymWitness = false := by
  intro h_code
  rcases checkBytes_parseErrorCode?_tokenNotConstantOrVariable_guardFacts arr config h_code with
    ⟨sym, h_ev⟩
  exact ⟨sym, false, h_ev, rfl⟩

/-- `checkBytes` token-not-const/var code implies frontend inadmissibility,
under certified-run gate/reflection facts. -/
theorem checkBytes_tokenNotConstantOrVariable_implies_frontendNotAdmissible
    (arr : ByteArray) (config : ModeConfig)
    (h_cert : Metamath.Verify.FrontendCertified.CheckBytesFrontendCertifiedRun arr config) :
    (checkBytes arr config).parseErrorCode? = some .tokenNotConstantOrVariable →
    ∃ sym, ¬ MathSymbolAdmissible (DB.toMathSymbolState (checkBytes arr config)) sym := by
  intro h_code
  rcases h_cert.tokenNotConstOrVar_gateFacts h_code with ⟨sym, _h_ev, h_isSym_false⟩
  refine ⟨sym, ?_⟩
  intro h_adm
  unfold MathSymbolAdmissible DB.toMathSymbolState at h_adm
  simp [h_isSym_false] at h_adm

/-- `checkBytes` include-in-inner-scope code carries canonical include evidence + gate facts. -/
theorem checkBytes_includeInInnerScope_implies_frontendGateFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
    ∃ pos depth inStatement allowIncludeInnerScopeWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness)) := by
  intro h_code
  rcases checkBytes_parseErrorCode?_includeInInnerScope_guardFacts arr config h_code with
    ⟨pos, depth, inStatement, allowIncludeInnerScopeWitness, h_ev⟩
  exact ⟨pos, depth, inStatement, allowIncludeInnerScopeWitness, h_ev⟩

/-- `checkBytes` include-inside-statement code carries canonical include evidence + gate facts. -/
theorem checkBytes_includeInsideStatement_implies_frontendGateFacts
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
    ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness)) := by
  intro h_code
  rcases checkBytes_parseErrorCode?_includeInsideStatement_guardFacts arr config h_code with
    ⟨pos, scopeDepth, inStatementWitness, allowTokenSplicingWitness, h_ev⟩
  exact ⟨pos, scopeDepth, inStatementWitness, allowTokenSplicingWitness, h_ev⟩

/-- `checkBytes` include-in-inner-scope code has certified witness existence. -/
theorem checkBytes_includeInInnerScope_certifiedWitness_exists
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInInnerScope →
    ∃ pos depth inStatement allowIncludeInnerScopeWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.inInnerScope pos depth inStatement allowIncludeInnerScopeWitness)) := by
  intro h_code
  exact checkBytes_includeInInnerScope_implies_frontendGateFacts arr config h_code

/-- `checkBytes` include-inside-statement code has certified witness existence. -/
theorem checkBytes_includeInsideStatement_certifiedWitness_exists
    (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).parseErrorCode? = some .includeInsideStatement →
    ∃ pos scopeDepth inStatementWitness allowTokenSplicingWitness,
      (checkBytes arr config).errorEvidence? =
        some (.includeErr (.insideStatement pos scopeDepth inStatementWitness allowTokenSplicingWitness)) := by
  intro h_code
  exact checkBytes_includeInsideStatement_implies_frontendGateFacts arr config h_code

/-- Include-preprocessor in-inner-scope code implies front-end include gate facts. -/
theorem includePreprocessErrorDB_inInnerScope_implies_frontendGateFacts
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    (includePreprocessErrorDB config
      (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)).parseErrorCode? =
      some .includeInInnerScope →
      IncludeInInnerScopeGateFacts config.allowIncludeInnerScope depth := by
  intro h_code
  exact includePreprocessErrorDB_inInnerScope_guardFacts
    config pos depth inStatement h_allow h_depth h_code

/-- Include-preprocessor in-inner-scope code implies front-end include gate facts
from the pure include-gate witness. -/
theorem includePreprocessErrorDB_inInnerScope_implies_frontendGateFacts_of_gate
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config depth inStatement pos =
        some (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)) :
    (includePreprocessErrorDB config
      (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)).parseErrorCode? =
      some .includeInInnerScope →
      IncludeInInnerScopeGateFacts config.allowIncludeInnerScope depth := by
  intro h_code
  exact includePreprocessErrorDB_inInnerScope_guardFacts_of_gate
    config pos depth inStatement h_gate h_code

/-- Include-preprocessor inside-statement code implies front-end include gate facts. -/
theorem includePreprocessErrorDB_insideStatement_implies_frontendGateFacts
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    (includePreprocessErrorDB config
      (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)).parseErrorCode? =
      some .includeInsideStatement →
      IncludeInsideStatementGateFacts config.allowTokenSplicing inStatement := by
  intro h_code
  exact includePreprocessErrorDB_insideStatement_guardFacts
    config pos scopeDepth inStatement h_allow h_stmt h_code

/-- Include-preprocessor inside-statement code implies front-end include gate facts
from the pure include-gate witness. -/
theorem includePreprocessErrorDB_insideStatement_implies_frontendGateFacts_of_gate
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config scopeDepth inStatement pos =
        some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)) :
    (includePreprocessErrorDB config
      (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)).parseErrorCode? =
      some .includeInsideStatement →
      IncludeInsideStatementGateFacts config.allowTokenSplicing inStatement := by
  intro h_code
  exact includePreprocessErrorDB_insideStatement_guardFacts_of_gate
    config pos scopeDepth inStatement h_gate h_code

/-- `checkExpandedResult` in-inner-scope code implies front-end include inadmissibility. -/
theorem checkExpandedResult_inInnerScope_implies_frontendNotAdmissible
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    (checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_inInnerScope_guardFacts config pos depth inStatement h_allow h_depth h_code with
    ⟨h_allow, h_depth_ne_zero⟩
  have h_lhs_false : (!config.allowIncludeInnerScope && depth > 0) = false := h_adm.1
  have h_depth_pos : depth > 0 := Nat.pos_iff_ne_zero.mpr h_depth_ne_zero
  have h_lhs_true : (!config.allowIncludeInnerScope && depth > 0) = true := by
    simp [h_allow, h_depth_pos]
  simp [h_lhs_true] at h_lhs_false

/-- `checkExpandedResult` in-inner-scope code implies front-end include inadmissibility
from the pure include-gate witness. -/
theorem checkExpandedResult_inInnerScope_implies_frontendNotAdmissible_of_gate
    (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config depth inStatement pos =
        some (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)) :
    (checkExpandedResult config
      (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
      some .includeInInnerScope →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_inInnerScope_guardFacts_of_gate
      config pos depth inStatement h_gate h_code with ⟨h_allow, h_depth_ne_zero⟩
  have h_lhs_false : (!config.allowIncludeInnerScope && depth > 0) = false := h_adm.1
  have h_depth_pos : depth > 0 := Nat.pos_iff_ne_zero.mpr h_depth_ne_zero
  have h_lhs_true : (!config.allowIncludeInnerScope && depth > 0) = true := by
    simp [h_allow, h_depth_pos]
  simp [h_lhs_true] at h_lhs_false

/-- `checkExpandedResult` inside-statement code implies front-end include inadmissibility. -/
theorem checkExpandedResult_insideStatement_implies_frontendNotAdmissible
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    (checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_insideStatement_guardFacts config pos scopeDepth inStatement h_allow h_stmt h_code with
    ⟨h_allow, h_stmt⟩
  have h_rhs_false : (!config.allowTokenSplicing && inStatement) = false := h_adm.2
  have h_rhs_true : (!config.allowTokenSplicing && inStatement) = true := by
    simp [h_allow, h_stmt]
  simp [h_rhs_true] at h_rhs_false

/-- `checkExpandedResult` inside-statement code implies front-end include inadmissibility
from the pure include-gate witness. -/
theorem checkExpandedResult_insideStatement_implies_frontendNotAdmissible_of_gate
    (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_gate :
      includeDirectiveViolation? config scopeDepth inStatement pos =
        some (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)) :
    (checkExpandedResult config
      (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
      some .includeInsideStatement →
      ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  intro h_code h_adm
  rcases checkExpandedResult_insideStatement_guardFacts_of_gate
      config pos scopeDepth inStatement h_gate h_code with ⟨h_allow, h_stmt⟩
  have h_rhs_false : (!config.allowTokenSplicing && inStatement) = false := h_adm.2
  have h_rhs_true : (!config.allowTokenSplicing && inStatement) = true := by
    simp [h_allow, h_stmt]
  simp [h_rhs_true] at h_rhs_false

/-- IO-entry include in-inner-scope expansion error binds `check` result and front-end inadmissibility. -/
theorem check_inInnerScope_of_expandIncludes_error_implies_frontendNotAdmissible
    (fname : String) (config : ModeConfig) (pos depth : Nat) (inStatement : Bool)
    (h_expand :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16) (Std.HashSet.emptyWithCapacity 16) config =
        pure (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope)))
    (h_allow : config.allowIncludeInnerScope = false)
    (h_depth : depth ≠ 0) :
    check fname config =
      pure (checkExpandedResult config
        (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))) ∧
    ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) depth inStatement := by
  constructor
  · unfold check
    rw [h_expand]
    rfl
  · have h_code :
        (checkExpandedResult config
          (.error (.inInnerScope pos depth inStatement config.allowIncludeInnerScope))).parseErrorCode? =
          some .includeInInnerScope := by
      simp [checkExpandedResult, includePreprocessErrorDB_parseErrorCode, IncludeError.code]
    exact checkExpandedResult_inInnerScope_implies_frontendNotAdmissible
      config pos depth inStatement h_allow h_depth h_code

/-- IO-entry include inside-statement expansion error binds `check` result and front-end inadmissibility. -/
theorem check_insideStatement_of_expandIncludes_error_implies_frontendNotAdmissible
    (fname : String) (config : ModeConfig) (pos scopeDepth : Nat) (inStatement : Bool)
    (h_expand :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16) (Std.HashSet.emptyWithCapacity 16) config =
        pure (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing)))
    (h_allow : config.allowTokenSplicing = false)
    (h_stmt : inStatement = true) :
    check fname config =
      pure (checkExpandedResult config
        (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))) ∧
    ¬ IncludeDirectiveAdmissible (ModeConfig.toIncludePolicy config) scopeDepth inStatement := by
  constructor
  · unfold check
    rw [h_expand]
    rfl
  · have h_code :
        (checkExpandedResult config
          (.error (.insideStatement pos scopeDepth inStatement config.allowTokenSplicing))).parseErrorCode? =
          some .includeInsideStatement := by
      simp [checkExpandedResult, includePreprocessErrorDB_parseErrorCode, IncludeError.code]
    exact checkExpandedResult_insideStatement_implies_frontendNotAdmissible
      config pos scopeDepth inStatement h_allow h_stmt h_code

end Metamath.Verify.FrontendBridge

namespace Metamath.FrontendBridge

export Metamath.Verify.FrontendBridge
  (DB.toDjvarsState
   DB.toMathSymbolState
   DB.toTopLevelEssState
   ModeConfig.toIncludePolicy
   DB.djvarsScopeViolation?_none_iff_frontendAdmissible
   DB.djvarsScopeViolation?_some_implies_frontendNotAdmissible
   DB.djvarsScopeViolation?_frontendNotAdmissible_implies_exists
   DB.mathSymbolViolation?_none_iff_frontendAdmissible
   DB.mathSymbolViolation?_some_implies_frontendNotAdmissible
   DB.mathSymbolViolation?_frontendNotAdmissible_implies_exists
   includeDirectiveViolation?_none_iff_frontendAdmissible
   includeDirectiveViolation?_some_implies_frontendNotAdmissible
   includeDirectiveViolation?_frontendNotAdmissible_implies_exists
   topLevelEssViolation?_none_iff_frontendAdmissible
   topLevelEssViolation?_some_implies_frontendNotAdmissible
   topLevelEssViolation?_frontendNotAdmissible_implies_exists
   checkBytes_topLevelEssentialNotAllowed_implies_frontendGateFacts
   checkBytes_topLevelEssentialNotAllowed_implies_frontendWitness
   checkBytes_topLevelEssentialNotAllowed_implies_frontendNotAdmissible
   checkBytes_topLevelEssentialNotAllowed_certifiedWitness_exists
   checkBytes_tokenNotConstantOrVariable_implies_frontendGateFacts
   checkBytes_tokenNotConstantOrVariable_implies_frontendNotAdmissible
   checkBytes_tokenNotConstantOrVariable_certifiedWitness_exists
   checkBytes_includeInInnerScope_implies_frontendGateFacts
   checkBytes_includeInsideStatement_implies_frontendGateFacts
   checkBytes_includeInInnerScope_certifiedWitness_exists
   checkBytes_includeInsideStatement_certifiedWitness_exists
   includePreprocessErrorDB_inInnerScope_implies_frontendGateFacts
   includePreprocessErrorDB_inInnerScope_implies_frontendGateFacts_of_gate
   includePreprocessErrorDB_insideStatement_implies_frontendGateFacts
   includePreprocessErrorDB_insideStatement_implies_frontendGateFacts_of_gate
   checkExpandedResult_inInnerScope_implies_frontendNotAdmissible
   checkExpandedResult_inInnerScope_implies_frontendNotAdmissible_of_gate
   checkExpandedResult_insideStatement_implies_frontendNotAdmissible
   checkExpandedResult_insideStatement_implies_frontendNotAdmissible_of_gate
   check_inInnerScope_of_expandIncludes_error_implies_frontendNotAdmissible
   check_insideStatement_of_expandIncludes_error_implies_frontendNotAdmissible)

end Metamath.FrontendBridge
