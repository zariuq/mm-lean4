# Parser Error Codes

This table records the parser error taxonomy with the mapped spec clause and the rule predicate used in proofs.

Columns:
- Code: `ParseErrorCode` constructor.
- Message: `ParseErrorCode.message`.
- SpecClause: `ParseErrorCode.specClause`.
- Predicate: rule predicate used by `RuleSemanticViolation`.

| Code | Message | SpecClause | Predicate |
|---|---|---|---|
| cantSaveEmptyStack | can't save empty stack | sec4_3_statementTermination | DoneModeViolation |
| unclosedBlock | unclosed block (missing $}) | sec4_3_statementTermination | DoneModeViolation |
| unclosedComment | unclosed comment | sec4_1_2_comments | DoneModeViolation |
| unclosedConst | unclosed $c | sec4_3_statementTermination | DoneModeViolation |
| unclosedVar | unclosed $v | sec4_3_statementTermination | DoneModeViolation |
| unclosedDjvars | unclosed $d | sec4_2_4_djvars | DoneModeViolation |
| unclosedFloat | unclosed $f | sec4_3_statementTermination | DoneModeViolation |
| unclosedEss | unclosed $e | sec4_3_statementTermination | DoneModeViolation |
| unclosedAx | unclosed $a | sec4_3_statementTermination | DoneModeViolation |
| unclosedThm | unclosed $p | sec4_3_statementTermination | DoneModeViolation |
| notACommand | not a command | sec4_3_statementTermination | TokenFormViolation |
| unclosedProof | unclosed $p proof | sec4_3_statementTermination | DoneModeViolation |
| cantPopGlobalScope | can't pop global scope | sec4_3_statementTermination | ScopeDeclViolation |
| constMustBeOutermost | $c must be in outermost block (spec Section 4.2.8) | sec4_2_8_constOutermost | ScopeDeclViolation |
| duplicateSymbolOrAssert | duplicate symbol/assert <label> | sec4_3_statementTermination | ScopeDeclViolation |
| firstSymbolNotConstant | first symbol is not a constant | sec4_3_statementTermination | ScopeDeclViolation |
| hypothesisSymbolsNotInFrame | hypothesis symbols not in frame | sec4_3_statementTermination | ScopeDeclViolation |
| expectedConstantAndVariable | expected a constant and a variable | sec4_3_statementTermination | ScopeDeclViolation |
| variableAlreadyHasFloatHyp | variable <v> already has $f hypothesis | sec4_3_statementTermination | ScopeDeclViolation |
| stackFormulaNoConstantHead | stack formula has no constant head | sec4_3_statementTermination | ProofCheckViolation |
| hypothesisNoConstantHead | hypothesis has no constant head | sec4_3_statementTermination | ProofCheckViolation |
| typeErrorInSubstitution | type error in substitution | sec4_3_statementTermination | ProofCheckViolation |
| badTypecodeInSubstitution | bad typecode in substitution <ctx> | sec4_3_statementTermination | ProofCheckViolation |
| duplicateFloatVariable | duplicate float variable | sec4_3_statementTermination | ProofCheckViolation |
| disjointVariableViolation | disjoint variable violation | sec4_3_statementTermination | ProofCheckViolation |
| assertionNoConstantHead | assertion has no constant head | sec4_3_statementTermination | ProofCheckViolation |
| assertionVarsNotInFrame | assertion variables not in frame | sec4_3_statementTermination | ProofCheckViolation |
| stackUnderflow | stack underflow | sec4_3_statementTermination | ProofCheckViolation |
| proofBackrefIndexOutOfRange | proof backref index out of range | sec4_3_statementTermination | ProofCheckViolation |
| invalidLabel | invalid label '<label>' | sec4_2_1_labels | InvalidLabelViolation |
| invalidMathString | invalid math string '<math>' | sec4_1_1_whitespace | TokenFormViolation |
| duplicateDisjointVariable | duplicate disjoint variable <sym> | sec4_2_4_djvars | DuplicateDisjointVariableViolation |
| tokenNotInScope | <sym> not in scope | sec4_2_4_djvars | TokenNotInScopeViolation |
| tokenNotVariable | <sym> is not a variable | sec4_2_4_djvars | ScopeDeclViolation |
| unknownStepQuestionRejected | unknown step '?' not allowed (config rejects incomplete proofs) | sec4_3_statementTermination | ProofCheckViolation |
| topLevelEssentialNotAllowed | top-level $e not allowed (config requires $e inside blocks) | sec4_3_statementTermination | ScopeDeclViolation |
| proofParseError | proof parse error | sec4_3_statementTermination | ProofCheckViolation |
| theoremMoreThanOneStackElement | more than one element on stack | sec4_3_statementTermination | TheoremFinalityViolation |
| theoremClaimMismatch | theorem does not prove what it claims | sec4_3_statementTermination | TheoremFinalityViolation |
| nestedCommentDelimiter | nested comment delimiter '$(' inside comment | sec4_1_2_comments | TokenFormViolation |
| tokenNotConstantOrVariable | <sym> is not a constant or variable | sec4_3_statementTermination | ScopeDeclViolation |
| unknownStatementType | unknown statement type <type> | sec4_3_statementTermination | TokenFormViolation |
| internalIllFormedDatabaseAfterParse | internal error: ill-formed database after parse | sec4_3_statementTermination | InternalConsistencyViolation |
| includeCycleDetected | include cycle detected: '<path>' is already being processed | sec4_1_2_includes | IncludeViolation |
| includeDepthExceeded | include depth limit exceeded (increase maxIncludeDepth in ModeConfig) | impl_resourceBound | IncludeViolation |
| includeInInnerScope | include in inner scope (config requires outermost scope only, spec §4.1.2) | sec4_1_2_includes | IncludeViolation |
| includeInsideStatement | include inside statement (config forbids token splicing, spec §4.1.2) | sec4_1_2_includes | IncludeViolation |
| includeExtractedEmptyPath | extracted empty path from position <start> to <end> in <file> | sec4_1_2_includes | IncludeViolation |
| includeEmptyPathBeforeNormalization | extracted empty include path before normalization in <file> | sec4_1_2_includes | IncludeViolation |
| includePathEmptyAfterNormalization | include path became empty after normalizing './' prefix (original was '<path>') in <file> | sec4_1_2_includes | IncludeViolation |
| includeReadFailure | failed to read include file '<name>' (resolved to '<path>'): <error> | sec4_1_2_includes | IncludeReadFailureViolation |
| includeBudgetExhausted | include resolution budget exhausted (increase maxIncludeResolutions in ModeConfig) | impl_resourceBound | IncludeViolation |

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
