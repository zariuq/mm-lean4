/-
ErrorCodeSemantics — Total evidence extraction for every ParseErrorCode constructor.

This module proves that every decoded parser error code carries a concrete,
family-specific evidence payload.  Combined with the existing semantic layer
(`parseErrorCode?_ruleSemantic_sound`, all constructors), this gives a fully certified
error-code ↔ evidence-shape correspondence.

**Main results (all sorry-free):**

1. `CodePayloadWitness`  — per-code evidence shape predicate
2. `DB.parseErrorCode?_guardFacts_total` — total DB-level evidence extraction
3. `checkBytes_parseErrorCode?_guardFacts_total` — bytes-level lift
4. `checkBytes_parseErrorCode?_fullyCertified` — payload ∧ semantic bundle
-/

import Metamath.Verify
import Metamath.VerifyDBSemanticThms
import Metamath.VerifyDBPayloadThms
import Metamath.VerifyIncludeThms
import Metamath.VerifyPackagingThms
import Metamath.VerifyProofGuardThms
import Metamath.VerifyScopeThms

set_option autoImplicit false

namespace Metamath.ErrorCodeSemantics

open Metamath.Verify

/-! ## Evidence shape specification

`CodePayloadWitness s code` states that the DB `s` carries error evidence
whose shape matches the error family and constructor for `code`.
Each branch is the *tightest* statement extractable from the evidence layer. -/

/-- Per-code evidence shape predicate, one branch per `ParseErrorCode`
constructor. -/
@[simp] def CodePayloadWitness (s : DB) : ParseErrorCode → Prop
  -- CompressedSaveError (1)
  | .cantSaveEmptyStack =>
      ∃ stackSize, s.errorEvidence? = some (.compressedSave (.cantSaveEmptyStack stackSize))
  -- DoneModeError (10)
  | .unclosedBlock => s.errorEvidence? = some (.doneMode .unclosedBlock)
  | .unclosedComment => s.errorEvidence? = some (.doneMode .unclosedComment)
  | .unclosedConst => s.errorEvidence? = some (.doneMode .unclosedConst)
  | .unclosedVar => s.errorEvidence? = some (.doneMode .unclosedVar)
  | .unclosedDjvars => s.errorEvidence? = some (.doneMode .unclosedDjvars)
  | .unclosedFloat => s.errorEvidence? = some (.doneMode .unclosedFloat)
  | .unclosedEss => s.errorEvidence? = some (.doneMode .unclosedEss)
  | .unclosedAx => s.errorEvidence? = some (.doneMode .unclosedAx)
  | .unclosedThm => s.errorEvidence? = some (.doneMode .unclosedThm)
  | .unclosedProof => s.errorEvidence? = some (.doneMode .unclosedProof)
  -- TokenFormError (5)
  | .notACommand =>
      ∃ label, s.errorEvidence? = some (.tokenForm (.notACommand label))
  | .invalidLabel =>
      ∃ label, s.errorEvidence? = some (.tokenForm (.invalidLabel label))
  | .invalidMathString =>
      ∃ tok, s.errorEvidence? = some (.tokenForm (.invalidMathString tok))
  | .unknownStatementType =>
      ∃ tok, s.errorEvidence? = some (.tokenForm (.unknownStatementType tok))
  | .nestedCommentDelimiter =>
      s.errorEvidence? = some (.tokenForm .nestedCommentDelimiter)
  -- ScopeDeclError
  | .cantPopGlobalScope => s.errorEvidence? = some (.scopeDecl .cantPopGlobalScope)
  | .constMustBeOutermost => s.errorEvidence? = some (.scopeDecl .constMustBeOutermost)
  | .duplicateSymbolOrAssert =>
      ∃ label, s.errorEvidence? = some (.scopeDecl (.duplicateSymbolOrAssert label))
  | .firstSymbolNotConstant => s.errorEvidence? = some (.scopeDecl .firstSymbolNotConstant)
  | .hypothesisSymbolsNotInFrame =>
      s.errorEvidence? = some (.scopeDecl .hypothesisSymbolsNotInFrame)
  | .outOfOrderHypothesesInFrame =>
      s.errorEvidence? = some (.scopeDecl .outOfOrderHypothesesInFrame)
  | .expectedConstantAndVariable =>
      s.errorEvidence? = some (.scopeDecl .expectedConstantAndVariable)
  | .variableAlreadyHasFloatHyp =>
      ∃ v, s.errorEvidence? = some (.scopeDecl (.variableAlreadyHasFloatHyp v))
  | .duplicateDisjointVariable =>
      ∃ sym, s.errorEvidence? = some (.scopeDecl (.duplicateDisjointVariable sym))
  | .disjointStatementTooShort =>
      ∃ actual,
        s.errorEvidence? = some (.scopeDecl (.disjointStatementTooShort actual))
  | .variableAlreadyActive =>
      ∃ name, s.errorEvidence? = some (.scopeDecl (.variableAlreadyActive name))
  | .constantStatementEmpty =>
      s.errorEvidence? = some (.scopeDecl .constantStatementEmpty)
  | .variableStatementEmpty =>
      s.errorEvidence? = some (.scopeDecl .variableStatementEmpty)
  | .tokenNotInScope =>
      ∃ sym, s.errorEvidence? = some (.scopeDecl (.tokenNotInScope sym))
  | .inactiveMathSymbol =>
      ∃ sym, s.errorEvidence? = some (.scopeDecl (.inactiveMathSymbol sym))
  | .tokenNotVariable =>
      ∃ sym, s.errorEvidence? = some (.scopeDecl (.tokenNotVariable sym))
  | .tokenNotConstantOrVariable =>
      ∃ sym, s.errorEvidence? = some (.scopeDecl (.tokenNotConstantOrVariable sym))
  | .topLevelEssentialNotAllowed =>
      s.errorEvidence? = some (.scopeDecl .topLevelEssentialNotAllowed)
  -- ProofCheckError (16)
  | .stackFormulaNoConstantHead =>
      s.errorEvidence? = some (.proofCheck .stackFormulaNoConstantHead)
  | .hypothesisNoConstantHead =>
      s.errorEvidence? = some (.proofCheck .hypothesisNoConstantHead)
  | .typeErrorInSubstitution =>
      s.errorEvidence? = some (.proofCheck .typeErrorInSubstitution)
  | .badTypecodeInSubstitution =>
      ∃ ctx, s.errorEvidence? = some (.proofCheck (.badTypecodeInSubstitution ctx))
  | .duplicateFloatVariable =>
      s.errorEvidence? = some (.proofCheck .duplicateFloatVariable)
  | .disjointVariableViolation =>
      s.errorEvidence? = some (.proofCheck .disjointVariableViolation)
  | .assertionNoConstantHead =>
      s.errorEvidence? = some (.proofCheck .assertionNoConstantHead)
  | .assertionVarsNotInFrame =>
      s.errorEvidence? = some (.proofCheck .assertionVarsNotInFrame)
  | .stackUnderflow =>
      ∃ needed haveSize, s.errorEvidence? = some (.proofCheck (.stackUnderflow needed haveSize))
  | .proofBackrefIndexOutOfRange =>
      ∃ idx heapSize,
        s.errorEvidence? = some (.proofCheck (.proofBackrefIndexOutOfRange idx heapSize))
  | .proofParseError =>
      s.errorEvidence? = some (.proofCheck .proofParseError)
  | .unknownStepQuestionRejected =>
      s.errorEvidence? = some (.proofCheck .unknownStepQuestionRejected)
  | .hypothesisNotInDatabaseScope =>
      ∃ label, s.errorEvidence? = some (.proofCheck (.hypothesisNotInDatabaseScope label))
  | .statementNotFound =>
      ∃ label, s.errorEvidence? = some (.proofCheck (.statementNotFound label))
  | .mandatoryHypothesisNotFoundInDatabase =>
      ∃ label,
        s.errorEvidence? = some (.proofCheck (.mandatoryHypothesisNotFoundInDatabase label))
  | .hypothesisNotFound =>
      ∃ label, s.errorEvidence? = some (.proofCheck (.hypothesisNotFound label))
  -- TheoremFinalityError (2)
  | .theoremMoreThanOneStackElement =>
      ∃ stackSize,
        s.errorEvidence? = some (.theoremFinality (.theoremMoreThanOneStackElement stackSize))
  | .theoremClaimMismatch =>
      ∃ claim top,
        s.errorEvidence? = some (.theoremFinality (.theoremClaimMismatch claim top))
  -- IncludeError (7)
  | .includeCycleDetected =>
      ∃ path, s.errorEvidence? = some (.includeErr (.cycleDetected path))
  | .includeDepthExceeded =>
      ∃ path, s.errorEvidence? = some (.includeErr (.depthExceeded path))
  | .includeBudgetExhausted =>
      ∃ path, s.errorEvidence? = some (.includeErr (.budgetExhausted path))
  | .includeInInnerScope =>
      ∃ pos depth inStmt witness,
        s.errorEvidence? = some (.includeErr (.inInnerScope pos depth inStmt witness))
  | .includeInsideStatement =>
      ∃ pos depth inStmt witness,
        s.errorEvidence? = some (.includeErr (.insideStatement pos depth inStmt witness))
  | .includeExtractedEmptyPath =>
      ∃ startPos endPos file,
        s.errorEvidence? = some (.includeErr (.extractedEmptyPath startPos endPos file))
  | .includeEmptyPathBeforeNormalization =>
      ∃ file, s.errorEvidence? = some (.includeErr (.emptyPathBeforeNormalization file))
  | .includePathEmptyAfterNormalization =>
      ∃ orig file,
        s.errorEvidence? = some (.includeErr (.pathEmptyAfterNormalization orig file))
  | .includeReadFailure =>
      ∃ name path err,
        s.errorEvidence? = some (.includeErr (.readFailure name path err))
  -- Internal (1)
  | .internalIllFormedDatabaseAfterParse =>
      ∃ allowDup wf dv, s.errorEvidence? = some (.internalGate allowDup wf dv)

/-! ## Total evidence extraction

Every decoded parser error code carries a concrete evidence payload
matching the `CodePayloadWitness` shape.  The proof combines:
- 19 existing `DB.parseErrorCode?_*_guardFacts` theorems (Verify.lean)
- 36 new inline proofs (DoneMode via `parseErrorCode?_sound`, others via
  `parseErrorCode?_ruleSemantic_sound` + family case analysis) -/

/-- Total evidence extraction: every decoded code has a `CodePayloadWitness`.
Covers every `ParseErrorCode` constructor. -/
theorem DB.parseErrorCode?_guardFacts_total (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code → CodePayloadWitness s code := by
  intro h
  cases code with
  -- ═══════════════════════════════════════════════════════════════
  -- DoneMode (10) — Strategy B: parseErrorCode?_sound + full case analysis
  -- ═══════════════════════════════════════════════════════════════
  | unclosedBlock =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedComment =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedConst =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedVar =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedDjvars =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedFloat =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedEss =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedAx =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedThm =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  | unclosedProof =>
    obtain ⟨_, _, _, ev, _, h_ev, h_code'⟩ := DB.parseErrorCode?_sound s _ h
    cases ev with
    | doneMode err => cases err <;> simp_all [ErrorEvidence.code, DoneModeError.code]
    | tokenForm err => cases err <;> simp_all [ErrorEvidence.code, TokenFormError.code]
    | scopeDecl err => cases err <;> simp_all [ErrorEvidence.code, ScopeDeclError.code]
    | includeErr err => cases err <;> simp_all [ErrorEvidence.code, IncludeError.code]
    | proofCheck err => cases err <;> simp_all [ErrorEvidence.code, ProofCheckError.code]
    | theoremFinality err => cases err <;> simp_all [ErrorEvidence.code, TheoremFinalityError.code]
    | compressedSave err => cases err <;> simp_all [ErrorEvidence.code, CompressedSaveError.code]
    | internalGate => simp_all [ErrorEvidence.code]
  -- ═══════════════════════════════════════════════════════════════
  -- TokenForm (5) — Strategy A: ruleSemantic → family violation
  -- ═══════════════════════════════════════════════════════════════
  | notACommand =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .notACommand h
    simp only [DB.RuleSemanticViolation, DB.TokenFormViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [TokenFormError.code]
  | invalidLabel =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .invalidLabel h
    simp only [DB.RuleSemanticViolation, DB.InvalidLabelViolation, DB.TokenFormViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [TokenFormError.code]
  | invalidMathString =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .invalidMathString h
    simp only [DB.RuleSemanticViolation, DB.TokenFormViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [TokenFormError.code]
  | unknownStatementType =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .unknownStatementType h
    simp only [DB.RuleSemanticViolation, DB.TokenFormViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [TokenFormError.code]
  | nestedCommentDelimiter =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .nestedCommentDelimiter h
    simp only [DB.RuleSemanticViolation, DB.TokenFormViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [TokenFormError.code]
  -- ═══════════════════════════════════════════════════════════════
  -- ScopeDecl (13) — 3 existing + 10 new via Strategy A
  -- ═══════════════════════════════════════════════════════════════
  | cantPopGlobalScope =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .cantPopGlobalScope h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | constMustBeOutermost =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .constMustBeOutermost h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | duplicateSymbolOrAssert =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .duplicateSymbolOrAssert h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | firstSymbolNotConstant =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .firstSymbolNotConstant h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | hypothesisSymbolsNotInFrame =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .hypothesisSymbolsNotInFrame h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | outOfOrderHypothesesInFrame =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .outOfOrderHypothesesInFrame h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | expectedConstantAndVariable =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .expectedConstantAndVariable h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | variableAlreadyHasFloatHyp =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .variableAlreadyHasFloatHyp h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | duplicateDisjointVariable =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .duplicateDisjointVariable h
    simp only [DB.RuleSemanticViolation, DB.DuplicateDisjointVariableViolation,
               DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | disjointStatementTooShort =>
    exact DB.parseErrorCode?_disjointStatementTooShort_payload_inversion s h
  | variableAlreadyActive =>
    exact DB.parseErrorCode?_variableAlreadyActive_payload_inversion s h
  | constantStatementEmpty =>
    exact DB.parseErrorCode?_constantStatementEmpty_evidence_inversion s h
  | variableStatementEmpty =>
    exact DB.parseErrorCode?_variableStatementEmpty_evidence_inversion s h
  | tokenNotInScope =>
    exact DB.parseErrorCode?_tokenNotInScope_guardFacts s h
  | inactiveMathSymbol =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .inactiveMathSymbol h
    simp only [DB.RuleSemanticViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | tokenNotVariable =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .tokenNotVariable h
    simp only [DB.RuleSemanticViolation, DB.ScopeDeclViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ScopeDeclError.code]
  | tokenNotConstantOrVariable =>
    exact DB.parseErrorCode?_tokenNotConstantOrVariable_guardFacts s h
  | topLevelEssentialNotAllowed =>
    exact DB.parseErrorCode?_topLevelEssentialNotAllowed_guardFacts s h
  -- ═══════════════════════════════════════════════════════════════
  -- ProofCheck (16) — 8 existing + 8 new via Strategy A
  -- ═══════════════════════════════════════════════════════════════
  | stackFormulaNoConstantHead =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .stackFormulaNoConstantHead h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | hypothesisNoConstantHead =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .hypothesisNoConstantHead h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | typeErrorInSubstitution =>
    exact DB.parseErrorCode?_typeErrorInSubstitution_guardFacts s h
  | badTypecodeInSubstitution =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .badTypecodeInSubstitution h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | duplicateFloatVariable =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .duplicateFloatVariable h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | disjointVariableViolation =>
    exact DB.parseErrorCode?_disjointVariableViolation_guardFacts s h
  | assertionNoConstantHead =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .assertionNoConstantHead h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | assertionVarsNotInFrame =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .assertionVarsNotInFrame h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | stackUnderflow =>
    exact DB.parseErrorCode?_stackUnderflow_guardFacts s h
  | proofBackrefIndexOutOfRange =>
    exact DB.parseErrorCode?_proofBackrefIndexOutOfRange_guardFacts s h
  | proofParseError =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .proofParseError h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | unknownStepQuestionRejected =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .unknownStepQuestionRejected h
    simp only [DB.RuleSemanticViolation, DB.ProofCheckViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [ProofCheckError.code]
  | hypothesisNotInDatabaseScope =>
    exact DB.parseErrorCode?_hypothesisNotInDatabaseScope_guardFacts s h
  | statementNotFound =>
    exact DB.parseErrorCode?_statementNotFound_guardFacts s h
  | mandatoryHypothesisNotFoundInDatabase =>
    exact DB.parseErrorCode?_mandatoryHypothesisNotFoundInDatabase_guardFacts s h
  | hypothesisNotFound =>
    exact DB.parseErrorCode?_hypothesisNotFound_guardFacts s h
  -- ═══════════════════════════════════════════════════════════════
  -- TheoremFinality (2) — both existing
  -- ═══════════════════════════════════════════════════════════════
  | theoremMoreThanOneStackElement =>
    exact DB.parseErrorCode?_theoremMoreThanOneStackElement_guardFacts s h
  | theoremClaimMismatch =>
    exact DB.parseErrorCode?_theoremClaimMismatch_guardFacts s h
  -- ═══════════════════════════════════════════════════════════════
  -- CompressedSave (1) — Strategy A
  -- ═══════════════════════════════════════════════════════════════
  | cantSaveEmptyStack =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .cantSaveEmptyStack h
    simp only [DB.RuleSemanticViolation, DB.CompressedSaveViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [CompressedSaveError.code]
  -- ═══════════════════════════════════════════════════════════════
  -- Include (7) — 6 existing + 1 new via Strategy A
  -- ═══════════════════════════════════════════════════════════════
  | includeCycleDetected =>
    exact DB.parseErrorCode?_includeCycleDetected_guardFacts s h
  | includeDepthExceeded =>
    exact DB.parseErrorCode?_includeDepthExceeded_guardFacts s h
  | includeBudgetExhausted =>
    exact DB.parseErrorCode?_includeBudgetExhausted_guardFacts s h
  | includeInInnerScope =>
    exact DB.parseErrorCode?_includeInInnerScope_guardFacts s h
  | includeInsideStatement =>
    exact DB.parseErrorCode?_includeInsideStatement_guardFacts s h
  | includeExtractedEmptyPath =>
    exact DB.parseErrorCode?_includeExtractedEmptyPath_guardFacts s h
  | includeEmptyPathBeforeNormalization =>
    exact DB.parseErrorCode?_includeEmptyPathBeforeNormalization_guardFacts s h
  | includePathEmptyAfterNormalization =>
    exact DB.parseErrorCode?_includePathEmptyAfterNormalization_guardFacts s h
  | includeReadFailure =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s .includeReadFailure h
    simp only [DB.RuleSemanticViolation, DB.IncludeReadFailureViolation,
               DB.IncludeViolation] at h_rule
    obtain ⟨err, h_ev, h_code_eq⟩ := h_rule
    cases err <;> simp_all [IncludeError.code]
  -- ═══════════════════════════════════════════════════════════════
  -- Internal (1) — Strategy C: 3-way disjunction
  -- ═══════════════════════════════════════════════════════════════
  | internalIllFormedDatabaseAfterParse =>
    have h_rule := DB.parseErrorCode?_ruleSemantic_sound s
      .internalIllFormedDatabaseAfterParse h
    simp only [DB.RuleSemanticViolation] at h_rule
    rcases h_rule with ⟨err, h_ev, h_code⟩ | ⟨err, h_ev, h_code⟩ | ⟨allowDup, wf, dv, h_ev⟩
    · cases err <;> simp_all [ScopeDeclError.code]
    · cases err <;> simp_all [IncludeError.code]
    · exact ⟨allowDup, wf, dv, h_ev⟩

/-! ## Bytes-level lifts -/

/-- Total evidence extraction lifted to `checkBytes`. -/
theorem checkBytes_parseErrorCode?_guardFacts_total
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    CodePayloadWitness (checkBytes arr config) code :=
  DB.parseErrorCode?_guardFacts_total (checkBytes arr config) code

/-- Fully certified error bundle: payload witness ∧ semantic violation.
This is the strongest per-code result: every decoded error code carries
both a concrete evidence shape AND a rule-semantic violation. -/
theorem checkBytes_parseErrorCode?_fullyCertified
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    CodePayloadWitness (checkBytes arr config) code ∧
    (checkBytes arr config).RuleSemanticViolation code :=
  fun h => ⟨checkBytes_parseErrorCode?_guardFacts_total arr config code h,
            checkBytes_parseErrorCode?_ruleSemantic_sound arr config code h⟩

end Metamath.ErrorCodeSemantics
