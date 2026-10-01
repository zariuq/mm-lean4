# Parser Error Codes

This table records the parser error taxonomy with the mapped spec clause and the rule predicate used in proofs.

Columns:
- Code: `ParseErrorCode` constructor.
- Message: `ParseErrorCode.message`.
- SpecClause: `ParseErrorCode.specClause`.
- Predicate: rule predicate used by `RuleSemanticViolation`.

| Code | Message | SpecClause | Predicate |
|---|---|---|---|
| cantSaveEmptyStack | can't save empty stack | sec4_4_5_compressedProof | CompressedSaveViolation |
| unclosedBlock | unclosed block (missing $}) | sec4_2_8_scoping | DoneModeViolation |
| unclosedComment | unclosed comment | sec4_1_2_comments | DoneModeViolation |
| unclosedConst | unclosed $c | sec4_2_3_c_v_declarations | DoneModeViolation |
| unclosedVar | unclosed $v | sec4_2_3_c_v_declarations | DoneModeViolation |
| unclosedDjvars | unclosed $d | sec4_2_4_djvars | DoneModeViolation |
| unclosedFloat | unclosed $f | sec4_2_5_f_e_hypotheses | DoneModeViolation |
| unclosedEss | unclosed $e | sec4_2_5_f_e_hypotheses | DoneModeViolation |
| unclosedAx | unclosed $a | sec4_2_6_assertions | DoneModeViolation |
| unclosedThm | unclosed $p | sec4_2_6_assertions | DoneModeViolation |
| notACommand | not a command | sec4_1_3_basicSyntax | TokenFormViolation |
| unclosedProof | unclosed $p proof | sec4_3_proofVerification | DoneModeViolation |
| cantPopGlobalScope | can't pop global scope | sec4_2_8_scoping | ScopeDeclViolation |
| constMustBeOutermost | $c must be in outermost block (spec Section 4.2.8) | sec4_2_8_scoping | ScopeDeclViolation |
| duplicateSymbolOrAssert | duplicate symbol/assert '<label>' | sec4_2_1_labels | ScopeDeclViolation |
| firstSymbolNotConstant | first symbol is not a constant | sec4_2_5_f_e_hypotheses | ScopeDeclViolation |
| hypothesisSymbolsNotInFrame | hypothesis symbols not in frame | sec4_2_7_frames | ScopeDeclViolation |
| expectedConstantAndVariable | expected a constant and a variable | sec4_2_5_f_e_hypotheses | ScopeDeclViolation |
| variableAlreadyHasFloatHyp | variable '<v>' already has $f hypothesis | sec4_2_5_f_e_hypotheses | ScopeDeclViolation |
| stackFormulaNoConstantHead | stack formula has no constant head | sec4_3_proofVerification | ProofCheckViolation |
| hypothesisNoConstantHead | hypothesis has no constant head | sec4_3_proofVerification | ProofCheckViolation |
| typeErrorInSubstitution | type error in substitution | sec4_3_substitution | ProofCheckViolation |
| badTypecodeInSubstitution | bad typecode in substitution '<ctx>' | sec4_3_substitution | ProofCheckViolation |
| duplicateFloatVariable | duplicate float variable | sec4_2_5_f_e_hypotheses | ProofCheckViolation |
| disjointVariableViolation | disjoint variable violation | sec4_3_substitution | ProofCheckViolation |
| assertionNoConstantHead | assertion has no constant head | sec4_3_proofVerification | ProofCheckViolation |
| assertionVarsNotInFrame | assertion variables not in frame | sec4_3_proofVerification | ProofCheckViolation |
| stackUnderflow | stack underflow | sec4_3_stackDiscipline | ProofCheckViolation |
| proofBackrefIndexOutOfRange | proof backref index out of range | sec4_4_5_compressedProof | ProofCheckViolation |
| invalidLabel | invalid label '<label>' | sec4_2_1_labels | InvalidLabelViolation |
| invalidMathString | invalid math string '<math>' | sec4_1_1_whitespace | TokenFormViolation |
| duplicateDisjointVariable | duplicate disjoint variable '<sym>' | sec4_2_4_djvars | DuplicateDisjointVariableViolation |
| tokenNotInScope | symbol '<sym>' not in scope | sec4_2_4_djvars | TokenNotInScopeViolation |
| tokenNotVariable | symbol '<sym>' is not a variable | sec4_2_4_djvars | ScopeDeclViolation |
| unknownStepQuestionRejected | unknown step '?' not allowed (config rejects incomplete proofs) | sec4_4_6_unknownProof | ProofCheckViolation |
| topLevelEssentialNotAllowed | top-level $e not allowed (config requires $e inside blocks) | sec4_2_8_scoping | ScopeDeclViolation |
| proofParseError | proof parse error | sec4_3_proofVerification | ProofCheckViolation |
| theoremMoreThanOneStackElement | more than one element on stack | sec4_3_stackDiscipline | TheoremFinalityViolation |
| theoremClaimMismatch | theorem does not prove what it claims | sec4_3_proofVerification | TheoremFinalityViolation |
| nestedCommentDelimiter | nested comment delimiter '$(' inside comment | sec4_1_2_comments | TokenFormViolation |
| tokenNotConstantOrVariable | symbol '<sym>' is not a constant or variable | sec4_2_2_constantsVariables | ScopeDeclViolation |
| unknownStatementType | unknown statement type '<type>' | sec4_1_3_basicSyntax | TokenFormViolation |
| internalIllFormedDatabaseAfterParse | internal error: ill-formed database after parse | impl_internalConsistency | ScopeDeclViolation ∨ IncludeViolation ∨ InternalConsistencyViolation |
| includeCycleDetected | include cycle detected: '<path>' is already being processed | sec4_1_2_includes | IncludeViolation |
| includeInInnerScope | include in inner scope (config requires outermost scope only, spec §4.1.2) | sec4_1_2_includes | IncludeViolation |
| includeInsideStatement | include inside statement (config forbids token splicing, spec §4.1.2) | sec4_1_2_includes | IncludeViolation |
| includeExtractedEmptyPath | extracted empty path from position <start> to <end> in <file> | sec4_1_2_includes | IncludeViolation |
| includeEmptyPathBeforeNormalization | extracted empty include path before normalization in <file> | sec4_1_2_includes | IncludeViolation |
| includePathEmptyAfterNormalization | include path became empty after normalizing './' prefix (original was '<path>') in <file> | sec4_1_2_includes | IncludeViolation |
| includeReadFailure | failed to read include file '<name>' (resolved to '<path>'): <error> | sec4_1_2_includes | IncludeReadFailureViolation |
| hypothesisNotInDatabaseScope | hypothesis '<label>' not in database scope | sec4_3_labelResolution | ProofCheckViolation |
| statementNotFound | statement '<label>' not found | sec4_3_labelResolution | ProofCheckViolation |
| mandatoryHypothesisNotFoundInDatabase | mandatory hypothesis '<label>' not found in database | sec4_3_labelResolution | ProofCheckViolation |
| hypothesisNotFound | hypothesis '<label>' not found | sec4_3_labelResolution | ProofCheckViolation |
| outOfOrderHypothesesInFrame | out of order hypotheses in frame | sec4_2_7_frames | ScopeDeclViolation |
| includeDepthExceeded | include depth limit exceeded (increase maxIncludeDepth in ModeConfig) | impl_resourceBound | IncludeViolation |
| disjointStatementTooShort | $d statement must contain at least two variables | sec4_2_4_djvars | DisjointStatementTooShortViolation |
| constantStatementEmpty | $c statement must declare at least one constant | sec4_2_2_constantsVariables | ConstantStatementEmptyViolation |
| variableStatementEmpty | $v statement must declare at least one variable | sec4_2_2_constantsVariables | VariableStatementEmptyViolation |
| variableAlreadyActive | variable is already active in an enclosing block | sec4_2_2_constantsVariables | VariableAlreadyActiveViolation |
| inactiveMathSymbol | symbol '<sym>' is not active here | sec4_2_2_constantsVariables | InactiveMathSymbolViolation |
| includeBudgetExhausted | include resolution budget exhausted (increase maxIncludeResolutions in ModeConfig) | impl_resourceBound | IncludeViolation |
| mandatoryHypothesisInCompressedHeader | mandatory hypothesis '<label>' repeated in compressed proof header | sec4_4_5_compressedProof | ProofCheckViolation |
| commentDelimiterInToken | '$(' or '$)' inside a comment token | sec4_1_2_comments | TokenFormViolation |
| commentIllegalByte | illegal character in comment | sec4_1_2_comments | TokenFormViolation |

## Numeric Stability and Payload Schema

- Primary machine key is `ParseErrorCode.toNat` (inverse: `ParseErrorCode.ofNat?`).
- Human-facing tag is `repr code`.
- Clause anchor is `ParseErrorCode.specClause code`.
- Core guarantee: decoded parser errors in the verifier path are evidence-backed (`errorEvidence? = some ev`).

Payload schema is type-indexed by `ErrorEvidence` in `Metamath/Verify.lean`:
- `doneMode (err : DoneModeError)`
- `tokenForm (err : TokenFormError)`
- `scopeDecl (err : ScopeDeclError)`
- `includeErr (err : IncludeError)`
- `proofCheck (err : ProofCheckError)`
- `theoremFinality (err : TheoremFinalityError)`
- `compressedSave (err : CompressedSaveError)`
- `internalGate (allowDuplicateFloat : Bool) (wellFormed : Bool) (assertDvVarsInFrame : Bool)`

For CLI output with `--show-error-code`, the verifier prints:
- `code #<Nat>` (stable numeric ID)
- `clause <SpecClause>`
- `tag <ParseErrorCode>`
- original error message
