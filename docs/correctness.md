# Correctness Summary

This file lists the main correctness claims, theorems, and the trusted computing base.

## Claims and Theorem Anchors

### Parser -> Spec
- Parser success implies spec well-formedness and scopedness, then the proof-run theorems apply.
- Proof runs in the database a parse returns. These concern the run of proof steps, whose final
  formula has the expression of the claim; they are not `finishProof` acceptance, which compares
  formulas literally (an empty claim and `ERROR` have the same expression):
  - spec provable -> a run exists: `verify_parser_accepts_of_spec_provable` and
    `verify_impl_complete_of_checkBytes` in `Metamath/KernelCorrectness.lean`;
  - a run exists -> spec provable: `verify_parser_sound_of_impl_acceptance` and
    `verify_parser_sound_of_impl_acceptance_equiv` in `Metamath/KernelCorrectness.lean`.
- Proof runs at any well-formed database state, such as the state at a `$p` statement:
  `normalFoldSucceeds_iff_specProvable` and `anyFormatFoldSucceeds_iff_specProvable` in
  `Metamath/ParserEquivalence.lean`.
- Acceptance proper (the parser's `$p` path ending in `finishProof`, which stores exactly the claimed
  statement): `acceptedWithDummies_iff_statementProvable` in `Metamath/CheckerCompleteness.lean`, with
  `verify_impl_complete_exact` in `Metamath/CheckerCompleteness/Exact.lean` for the literal final
  stack; for source text, `statementProvable_iff_sourceAccepts` and
  `statementProvable_iff_fileAccepts` in `Metamath/SourceCompleteness.lean` (below).

### Mario Carneiro's Declarative Semantics
- `Metamath/DeclarativeSpec.lean` restricts the typing premise of Mario Carneiro's `ax` rule to the
  variables of the applied statement (the book's clause C.2.5 2(a)); his original rule is kept in
  `Metamath/Spec/DeclarativeOriginal.lean`, with `statementProvable_iff` showing that the two agree on
  trimmed axiom sets, which the translated databases are.
- At one fixed frame, operational provability is derivability by Mario's rules with every
  variable typed by the frame (`FrameDerivable`):
  - `operational_to_frameDerivable` and `frameDerivable_to_proofValid` in
    `Metamath/Spec/Equivalence.lean`.
  - Parser-specialized: `proofChecker_normal_iff_frameDerivable_in_parsedDB` in
    `Metamath/ParserEquivalence.lean` (premises discharged from parser success through
    `parser_toDatabase_wellFormed_strong` in `Metamath/KernelCorrectness.lean`).
- Soundness (accepted proof -> provable in Mario's semantics):
  - `operational_to_declarative` in `Metamath/Spec/Equivalence.lean`.
  - Stored statement at a `$p` statement: `finishProof_storedStatement_prefixProvable` in
    `Metamath/StoredStatementSoundness.lean` (provable from the pre-insertion database), and
    `check_storedStatements_writtenProof` supplies local insertion-event witnesses for stored
    assertions in a mode satisfying `IsSound` (no `?` steps, no duplicate `$f` statements).
    Actual-run membership and `$a`/`$p` classification are retained by
    `check_every_theorem_provable_from_run_axiom_events` in `Metamath/RunEmission.lean`;
    `statementProvable_of_anyFormatFoldSucceeds` in `Metamath/CheckerCompleteness.lean`.
- The Metamath book's definition, as a theorem about Mario's `Statement.Provable`:
  `Statement.provable_iff_exists_extension` in `Metamath/Spec/Derivable.lean` (Appendix C.2.5:
  a statement is provable iff it is the reduct of a provable pre-statement), and
  `Statement.provable_iff_exists_finite_extension` (finitely many dummy variables suffice).
- Completeness (provable in Mario's semantics -> a Metamath proof exists):
  - `statementProvable_iff_exists_extendedFrame` in `Metamath/Spec/Completeness.lean`: a
    stored statement is provable in Mario's statement-level semantics iff some extended frame
    of it (Metamath book §4.2.7: the frame plus optional `$f` and `$d` statements for dummy
    variables) has a proof.
  - `originalStatementProvable_iff_exists_extendedFrame`: the same for Mario's original `ax`
    rule (`Metamath/Spec/DeclarativeOriginal.lean`).
  - `exists_extendDummies_of_statementProvable`: the dummy variables extend any given
    extended frame, such as the active frame of a proof.
  - Checker form: `acceptedWithDummies_iff_statementProvable` in
    `Metamath/CheckerCompleteness.lean`: at a parser state between statements, the stored
    statement of a `$p` claim is provable in Mario's semantics iff, after declaring finitely
    many fresh dummy variables (`Verify.DB.declareDummies`: the parser's `$v`, `$f` and `$d`
    actions), the parser accepts a normal-mode proof of the claim (`ProofAccepted`: frame
    trimming, the proof steps, and `finishProof`). The declarations are database actions.
    `SourceCompleteness.acceptedWithDummies_iff_statementProvable_afterSource` states it at the
    end of an error-free read that stops between statements, in a mode without duplicate `$f`
    statements; its premises come from `afterSource_invariants`.
  - Source form: `statementProvable_iff_sourceAccepts` in `Metamath/SourceCompleteness.lean`.
    Let the parser read a source text without error, in a mode without duplicate `$f`
    statements, ending between statements with no token pending. The stored statement of a claim
    under a fresh label token is provable in Mario's semantics from the assertions read so far
    (earlier theorems with incomplete proofs among them) iff, for some admissible dummy
    declarations and normal proof (`Admissible`: fresh names, legal label and math-symbol tokens,
    proof steps that are label tokens), the parser reads the rendered text (`render`: `$v`, `$f`,
    the canonical `$d` pairs, and one `$p` statement) after the prefix without error, ends
    between statements, stores exactly the claimed statement, and records no new incomplete
    proof (`SourceAccepts`). `afterSource_declTokens`: the declarations leave the assertion
    database and the claim's trimmed frame unchanged; `sourceAccepts_toDatabaseTotal`: the
    continuation adds exactly the one assertion and keeps every earlier object. The invariants
    this needs hold at every error-free checkpoint (`afterSource_invariants`).
    `statementProvable_iff_sourceAccepts_originalRule` states the same for Mario's original `ax`
    rule. These are existence statements: they do not compute the declarations or the proof.
  - File form: `statementProvable_iff_fileAccepts`: the same for the complete file, closed by one
    `$}` for each open block and checked by `checkBytes` with its post-checks;
    `fileAccepts_verified`: a prefix without incomplete proofs gives a verified file.
  - Entry point: `check_accepts_of_statementProvable` and `statementProvable_of_check`: the same
    file through `Verify.check`, for a root file that resolves and reads as exactly those bytes.
    The rendered file raises no include request (`checkBytes_errorNotRequest` in
    `Metamath/SourceCompleteness/NoRequest.lean`), so `check` returns what `checkBytes` returns
    (`Metamath/RootFileCheck.lean`: `check_eq_checkBytes_of_ok`, `checkBytes_eq_of_check_ok`, and
    `check_assertDvVarsInFrame` for the stored-`$d` invariant through the include driver).
- At one fixed frame, completeness fails: Mario's `Provable` allows any variable, so a
  statement can be provable without a proof in its own frame.
  `Metamath/Spec/FixedFrameCounterexample.lean` gives a well-formed database in which a
  dummy variable is needed, and one in which an optional `$d` statement is needed.

### Kernel Soundness / Completeness
- Implementation soundness (a successful proof run -> spec provable):
  - `verify_impl_sound` in `Metamath/KernelCorrectness.lean`.
- Implementation completeness (spec provable -> a proof run whose final formula has the claim's
  expression): `verify_impl_complete` in `Metamath/KernelCorrectness.lean`; the literal final stack
  that `finishProof` requires is `verify_impl_complete_exact` in
  `Metamath/CheckerCompleteness/Exact.lean`.

### Parser Error Semantics
- Every parser error code is certified to agree with its recorded evidence (tag and payload
  shape) and its specification clause. This is consistency of the diagnostic, not an independent
  proof that the source violates the rule:
  - `RuleSemanticViolation` and `RuleClauseSemanticViolation` in `Metamath/Verify.lean`.
  - `checkBytes_parseErrorCode?_ruleClauseSemantic_sound` in `Metamath/Verify/Packaging.lean`.
- Per-code rule+clause theorem specialization exists for every `ParseErrorCode` constructor.

## Trusted Computing Base (TCB)

- Theorems: Lean's kernel, and the Lean core and Batteries definitions they are stated over.
- Running the compiled `mm-lean4` checker, and the `#guard` calibration tests, additionally relies
  on the Lean compiler and runtime and on the native implementations of core operations (such as
  the `String` and `ByteArray` primitives and hashing).
- The `mm-lean4` executable front end: command-line parsing and file IO.
- The host operating system and filesystem, for reading files and resolving includes (include IO
  failures are classified as environment errors, not specification violations).

## Verification Boundary

- Verified parser diagnostics and semantic theorems are anchored at `checkBytesCore` / `checkBytes`
  in `Metamath/Verify.lean`.
- The active executable path is `check`: a single-pass, include-aware driver (`runDriverLoop` over
  `stepFrame`) around the same parser. `Metamath/RunEmission.lean` and
  `Metamath/PrefixProvability/Checker.lean` prove properties of its runs. For a single root file
  that raises no include request, `Metamath/RootFileCheck.lean` proves that `check` returns what
  `checkBytes` returns on the file's bytes (`check_root_bridge`), under explicit conditions on the
  depth limit, the path resolution and the read; the stored-`$d` invariant holds for every
  error-free run (`check_assertDvVarsInFrame`).
- Source-level completeness (`Metamath/SourceCompleteness.lean`) covers `checkBytes`, and `check`
  on a root file that reads as the completed file. Completeness for continuations that use include
  directives is not proved.
- The theorems concern the parser's reading of the source. Outside the `permissive` mode the
  parser rejects comments with bytes outside the book's character set or with `$(` or `$)` inside
  a token; the `exe` mode treats vertical tab as whitespace, as metamath.exe does. In `permissive`,
  every byte and an inner `$(` are ignored as comment text until the first standalone `$)`;
  comments do not nest, and an unterminated comment is still rejected.
- Every mode deliberately permits a variable to have different `$f` types in separate scopes,
  as in test59. This differs from the book's global-type rule (§4.1.3), but does not weaken proof
  checking: each assertion retains its own frame and each application must satisfy that frame's
  typing premises. `Metamath/Tests/TypePolicy.lean` checks both permitted retyping and rejection
  of wrong-type and inactive-hypothesis proof steps. This policy is separate from allowing two
  simultaneously active `$f` declarations, controlled by `allowDuplicateFloat`.
- The legacy two-pass path (`expandIncludes` in `Metamath/Legacy/Runtime.lean`, related to
  `checkBytes` by `Metamath/Legacy/CompatThms.lean`) and the include scanner `scanIncludes` are not
  part of the active path.
- Legacy/raw `mkError` paths now carry explicit fallback evidence (`internalGate false false false`)
  to keep decoded error classification total.

## Intended Reading Order

1. `Metamath/Verify.lean` for parser semantics, error codes, and clause mapping.
2. `Metamath/ParserCorrectness*.lean` for parser-level invariants and correctness.
3. `Metamath/KernelCorrectness.lean` for implementation soundness/completeness and parser-entry wrappers.
4. `Metamath/Spec/Completeness.lean` for completeness with respect to Mario's declarative semantics.
5. `Metamath/SourceCompleteness.lean` for completeness at the level of source text and files.
