# Mm-lean4 Metamath verifier

mm-lean4 formalizes a Metamath verifier in Lean 4.
The project includes operational specification and semantic specification.
The project includes a proof.

## Layout

### Core layout

- `Metamath/Spec/`
  - `Metamath/Spec/` holds declarative and operational specifications with equivalence

- `Metamath/Verify.lean`
  - `Metamath/Verify.lean` implements the verifier

- `Metamath/KernelCorrectness.lean`
  - `Metamath/KernelCorrectness.lean` proves kernel soundness and completeness

- `Metamath/ParserCorrectness.lean`
  - `Metamath/ParserCorrectness.lean` proves parser invariants and correctness layers

- `Metamath/ParserEquivalence.lean`
  - `Metamath/ParserEquivalence.lean` is the canonical review entry point

- `Metamath/PrefixProvability/Checker.lean`
  - `Metamath/PrefixProvability/Checker.lean` certifies prefix provenance per accepted event

- `Metamath/StoredStatementSoundness.lean`
  - `Metamath/StoredStatementSoundness.lean` connects the full active proof frame
    to the exact trimmed statement and eliminates earlier `$p` rules by cut

- `Metamath/Spec/Completeness.lean`
  - `Metamath/Spec/Completeness.lean` proves that a statement is provable in Mario
    Carneiro's declarative semantics iff some extended frame of it has a Metamath proof

- `Metamath/SourceCompleteness.lean`
  - `Metamath/SourceCompleteness.lean` proves that such a statement is provable iff the
    parser accepts a proof of it in source text, after finitely many fresh dummy declarations,
    in modes without duplicate `$f` statements

- `Metamath/RunEmission.lean`
  - `Metamath/RunEmission.lean` ties the emitted chronology to the actual
    `check` invocation by refinement and determinism

- `Metamath/IncludeInterpretation.lean`
  - `Metamath/IncludeInterpretation.lean` states each mode's complete acceptance
    policy, decomposes its include and compressed-proof dimensions, and connects
    the declarations to runtime helpers

- `Metamath/ErrorCodeSemantics.lean`
  - `Metamath/ErrorCodeSemantics.lean` certifies every `ParseErrorCode` constructor

- `Metamath/DeclarativeSpec.lean`
  - `Metamath/DeclarativeSpec.lean` hosts Mario Carneiro's declarative specification; the
    typing premise of its `ax` rule ranges over the applied statement's variables, and
    `Metamath/Spec/DeclarativeOriginal.lean` proves it equivalent to his original rule on
    trimmed axiom sets, which translated databases are

### Non-core layout

- `Metamath/ParserEquivalenceExamples.lean`
  - `Metamath/ParserEquivalenceExamples.lean` provides compiling usage examples

- `Metamath/CounterexampleInsertError.lean`
  - `Metamath/CounterexampleInsertError.lean` provides a counterexample for insert-with-error behavior

- `Metamath/ParserSoundnessDemo.lean`
  - `Metamath/ParserSoundnessDemo.lean` is a development artifact

- `Metamath/DeclarativeSpecDemo.lean`
  - `Metamath/DeclarativeSpecDemo.lean` holds Mario Carneiro's by-hand translation of `demo0.mm`

- `Metamath/ZipperTest.lean`
  - `Metamath/ZipperTest.lean` is a development artifact

## Toolchain

- The toolchain pins Lean 4.33.1.
- The toolchain pins Batteries at commit `4488d40`.

## Status

- Sorries are 0.
- No project-declared axioms in active `Metamath/` Lean code; the headline
  theorems depend on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) under `#print axioms`.
- `lake build` succeeds on the pinned toolchain.
- The specification suite is 187 of 187 in the default `zar` mode.
- The fail-closed reference differential attempts all 187 registered databases
  in `knife` and `exe` mode.  Its report distinguishes semantic verdicts from
  reference-process failures; a crash is never counted as rejection or agreement.
- Direct `set.mm` verification reports 67764 objects.
- The CLI honesty and resource-bound gates are `scripts/cli_honesty.sh`.

```bash
rg -n '^\s*sorry\b|by sorry' Metamath/ --glob '*.lean'
lake env lean scripts/print_axioms.lean
MM_LEAN4=.lake/build/bin/mm-lean4 sh scripts/cli_honesty.sh
MM_LEAN4=.lake/build/bin/mm-lean4 \
  METAMATH_KNIFE="$METAMATH_KNIFE" METAMATH_EXE="$METAMATH_EXE" \
  METAMATH_TEST="$METAMATH_TEST" scripts/reference_mode_differential.sh
```

## Correctness

The development includes end-to-end correctness theorems for the verifier.
The detailed clause and theorem scopes are in `docs/SpecTheoremMap.md`.

### Main claims

- `check_storedStatements_writtenProof` (in a mode satisfying `IsSound`) connects the written
  `$p` proof to the exact trimmed statement stored by the include-aware executable.
- `check_every_theorem_provable_from_run_axiom_events`
  (`Metamath/RunEmission.lean`, in a mode satisfying `IsSound`) eliminates prior
  `$p` rules by chronological cut, leaving only `$a`-classified events — over the run's own chronology:
  `SinglePassEmission` ties the step list to the actual invocation through
  equations about the entrypoint's own IO recursion, and its determinism
  theorem (`SinglePassEmission.unique`) makes that list the only one any
  emission of the invocation can produce.
- `InsertionHistory` supplies the registry-continuity form of the
  same history; `ExecutionInsertionHistory` is its execution-indexed strengthening
  (subdatabase, exactly-one creation, and bound payloads over the emitted
  list).
- The `proofChecker_*_in_parsedDB` family is fixed-final-database adequacy and is
  not presented as source-proof acceptance.
- `checkBytes_parseErrorCode?_fullyCertified` certifies that every decoded error code agrees with
  its evidence payload.
- `parser_operational_to_frameDerivable_total` and `parser_frameDerivable_to_operational_total`
  are the parser-specialized bridge to derivability by Mario Carneiro's rules in the frame.
- `statementProvable_iff_exists_extendedFrame` (`Metamath/Spec/Completeness.lean`): a stored
  statement is provable in Mario Carneiro's declarative semantics iff some extended frame of it
  (the frame plus `$f` and `$d` statements for dummy variables, §4.2.7) has a Metamath proof.
  At one fixed frame the two differ (`Metamath/Spec/FixedFrameCounterexample.lean`).
- `statementProvable_iff_sourceAccepts` and `statementProvable_iff_fileAccepts`
  (`Metamath/SourceCompleteness.lean`): after an error-free read of source text that ends between
  statements with no token pending, in a mode without duplicate `$f` statements (not `exe` or
  `permissive`), such a statement is provable from the assertions read so far iff the parser
  accepts a proof of it written after finitely many fresh `$v`, `$f` and `$d` declarations;
  `check_accepts_of_statementProvable` and `statementProvable_of_check` state it through
  `Verify.check` on a root file without includes.

For incomplete proofs, `zar` accepts `?` but reports the database as accepted
and incomplete, never verified.  `sound` and `knife` reject `?`.

### Parser discharge

Parser success discharges WellFormedDatabaseStrong, FloatVarNoDup, and FrameVarsDisjointConsts.
`proofChecker_normal_iff_frameDerivable_in_parsedDB` composes the bridge from `checkBytes` success.

```
h_success : (checkBytes bytes).error? = none
  -> parser_construction_wf_scoped
  -> parser_toDatabase_wellFormed_strong
  -> floatVarNoDup_of_uniqueFloatVars
  -> frameVarsDisjointConsts_of_toFrame
  -> operational_to_frameDerivable, frameDerivable_to_proofValid
```

## Diagnostics

- Diagnostic taxonomy is `docs/ErrorCodes.md`.
- The specification-to-theorem map is `docs/SpecTheoremMap.md`.
- The verifier reports the first error.
- Include I/O failures are environment errors.
- Verifier modes are distinct specifications.

## Conformance boundary

- `Metamath/IncludeInterpretation.lean` declares and connects the distinct
  `zar`, `knife`, and `exe` policies.  The reference differential compares
  semantic acceptance verdicts and fails closed on reference-process crashes.
- Every mode but `permissive` follows the book's comment rules (§4.1.1–4.1.2), and `exe`
  additionally treats vertical tab as whitespace, as metamath.exe does; `permissive` ignores
  comment text up to the first standalone `$)`.  Every mode lets a variable take different `$f`
  types in separate scopes; each stored assertion keeps its own frame.
- Two operational resource bounds exist that the Metamath specification does
  not impose: `maxIncludeDepth` (default 100) and `maxIncludeResolutions`
  (default 1000000, the include-driver loop's resolution budget; duplicate
  suppressions also consume one resolution).  Exceeding either is reported
  loudly under the `impl_resourceBound` clause — an implementation resource
  outcome, not a claim that the source violated section 4.1.2.
- `--max-include-resolutions=N` overrides the resolution budget;
  `scripts/cli_honesty.sh` pins the zero/sufficient/default canaries.
- Unknown, malformed or conflicting command-line options are rejected with exit code 2.

## Boundary

- Formal theorems cover both the pure `checkBytes` lane over `ByteArray` input
  and properties derived by induction over the include-aware `check`
  implementation; `Metamath/RunEmission.lean` ties them to the invocation's
  own emitted chronology.
- The active executable frontend is single-pass and include-aware.
- `Metamath/FrontendBridge.lean` connects frontend outcomes back to the reviewed theorem chain.
- `Metamath/ParserEquivalence.lean` is the review entry module for the composed chain.

## Reproduction

```bash
ROOT="$(pwd)"
lake build
MM_LEAN4="$ROOT/.lake/build/bin/mm-lean4" sh scripts/cli_honesty.sh
(cd "$METAMATH_TEST" && \
  MM_LEAN4="$ROOT/.lake/build/bin/mm-lean4" ./run-testsuite-all ./test-mm-lean4)
```

## Quick expert checklist

- Reviewers read the theorem statements in `Metamath/SourceCompleteness.lean` and `Metamath/ParserEquivalence.lean`.
- Reviewers trace `parser_toDatabase_wellFormed_strong -> parser_frameDerivable_to_operational -> frameDerivable_to_proofValid`.
- Reviewers run `lake build` and the full test suite.

## Build

```bash
lake build
```

## Executables

- Lake executables are `mm-lean4` and `validateDB`.
- The executable build target is `lake build mm-lean4 validateDB`.
