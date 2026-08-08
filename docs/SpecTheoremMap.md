# Specification-to-theorem map

Each row connects a clause of the Metamath specification (section 4 of the
Metamath book; `SPEC_SECTION_4.txt`) to the Lean artifacts that state it, the
theorems that enforce or certify it, and the tests that witness it.  Mode
policies that occupy a spec-licensed freedom cite the licensing sentence.

| Spec clause | Meaning | Lean statement / theorem | Witness tests |
|---|---|---|---|
| 4.1.1 tokens, whitespace | tokenization | `ParserState.feed` / `feedToken`; registry-invariance toolkit | suite core |
| 4.1.2 comments | `$( $)`, no nesting | `feedToken` comment mode; `nestedCommentDelimiter` | test03 |
| 4.1.2 includes: include-once | "Only the first reference to a given file is included; any later references … ignored (treated like white space)" | `includeFrameGate`; `includeFrameGate_skips_seen`, `includeFrameGate_admits_fresh` | test42, test46 |
| 4.1.2 includes: cycles | "A file self-reference is ignored, as is any reference to the top-level file (to avoid loops)" | `includeFrameGate_ignores_cycle` (spec-faithful modes; non-fatal warning); mirror modes realize it via literal-string suppression | test28, test44; `cli_honesty.sh` cycle gates |
| 4.1.2 includes: file identity | "A verifier may assume that file names with different strings refer to different files" (license) | `FileIdentity` in `IncludeInterpretation.lean`; `literalIncludePaths`; selection theorems per mode | `cli_honesty.sh` spelled-cycle gates; reference differential |
| 4.1.2 includes: path base | "currently unspecified if path references are relative to the process' current directory or the file's containing directory" | `PathBase` in `IncludeInterpretation.lean`; mode selection theorems | `cli_honesty.sh` CWD-lookup gate; reference differential |
| 4.1.2 includes: child completeness | included files may not end mid-statement / mid-comment / mid-include | `childFileBoundaryError?`, `popExhaustedFrame`, `ChildFileBoundaryPolicy` (strict; `spliceExceptComments` mirrors metamath.exe; `spliceAll` permissive) | test87–test95 |
| 4.1.2 includes: outermost scope, not inside statements | placement of `$[ $]` | `includeDirectiveViolation?` | test17, test40, test46, test52, test53 |
| 4.2.1 labels | label / duplicate discipline | `DB.insert` duplicate rejection; `insert_success_nonvar_fresh` | suite core |
| 4.2.2 variable activity | "A variable may not be declared a second time while it is active, but it may be declared again … after it becomes inactive"; math symbols must be active | `DB.activeVars`, activity gate in `insert`; `Metamath.VariableActivity` (ScopeStack model + `isActiveVar_iff_scopeStack_active`) | test80–test86 |
| 4.2.3 `$c`/`$v` | declaration rules | `insert` const/var arms; `constMustBeOutermost` | test47 |
| 4.2.4 `$d` | distinct-variable restrictions on active variables | djvars arm; `dvCheck`; `assertDvVarsInFrame?` with `assertDvVarsInFrame_of_assertDvVarsInFrame?` | test81; suite DV cases |
| 4.2.5 `$f`/`$e` | hypothesis forms; one active `$f` per variable | `insertHyp`, float checks; `allowDuplicateFloat` policy | test15, test16, test67 |
| 4.2.6–4.2.8 assertions, frames, scoping | mandatory frames, scoping | `trimFrame'`, `pushScope`/`popScope`; `WellScopedDBWithScopes` | suite core |
| 4.3 proof verification | a `$p` proof derives its exact stored statement from prior assertions | `Metamath.Spec` (`Provable`, `ProofValid`); `proofChecker_*_acceptance_iff_specProvable_in_parsedDB` (fixed-final-database adequacy); `checkSinglePass_assert_origin_provable` (written-proof, pre-insertion formula provability under the full active frame); `checkSinglePass_storedStatements_writtenProof` (exact trimmed `Statement.Provable`); `checkSinglePass_every_theorem_provable_from_run_axiom_events` (chronological cut eliminating prior `$p` rules over the run's own emitted chronology: `SinglePassEmission` ties the step list to the actual invocation and `SinglePassEmission.unique` makes it the only list any emission of that invocation can produce — `Metamath/RunEmission.lean`); `ExecutionChronology` (execution-indexed exactly-one origin; `CertifiedRegistryChronology` is its registry-continuity weakening). `checkSinglePass_assertions_selfCitable` is only a projection/self-citation check and is not part of the written-proof soundness chain. | full suite; set.mm |
| 4.4.4 (book App. B) compressed proofs | compressed encoding, `Z` saves | compressed decoder; `applyCompressedActions`; `CompressedInvalidBytePolicy` (`reject` spec-faithful; `ignore` mirrors metamath-knife's decoder) | test19, test30; out-of-range-saved-step |
| 4.1.4 / 4.4.6 unknown steps | "A proof may contain a `?` … a verifier may ignore any proof containing `?` but should warn the user that the proof is incomplete" | `ProofState.incomplete` → `DB.incompleteProofs` ledger; accepted-vs-verified CLI wording; `rejectUnknownSteps` in certified modes; `not_zar_prefixCertified` | test20, test30; `cli_honesty.sh` `?` gates |
| (spec-external) resource bounds | depth / resolution limits the spec does not impose | `maxIncludeDepth`, `maxIncludeResolutions`; `SpecClause.impl_resourceBound`; `includeFrameGate_depth_exhausted` | `cli_honesty.sh` budget canaries |
| (spec-external) reference agreement | mirror modes vs live metamath.exe / metamath-knife | never a Lean theorem: `scripts/reference_mode_differential.sh` attempts all 177 registered databases, compares only semantic verdicts, and fails closed on reference-process errors | reference differential receipts |

Reading order for the certified story: `IncludeInterpretation.lean` (per-mode
interpretation) → `Verify.lean` (executable and policy surface) →
`PrefixWitnessCheckBytes.lean` (chronology and origin) →
`StoredStatementSoundness.lean` (exact stored statement and trace-relative cut) →
`RunEmission.lean` (execution-indexed emission chronology: refinement +
determinism, and the run-indexed cut crown) →
`scripts/print_axioms.lean` (axiom audit).
