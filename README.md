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

- `Metamath/KernelClean.lean`
  - `Metamath/KernelClean.lean` proves kernel soundness and completeness

- `Metamath/ParserCorrectness.lean`
  - `Metamath/ParserCorrectness.lean` proves parser invariants and correctness layers

- `Metamath/ParserEquivalence.lean`
  - `Metamath/ParserEquivalence.lean` is the canonical review entry point

- `Metamath/PrefixWitnessCheckBytes.lean`
  - `Metamath/PrefixWitnessCheckBytes.lean` certifies prefix provenance per accepted event

- `Metamath/StoredStatementSoundness.lean`
  - `Metamath/StoredStatementSoundness.lean` connects the full active proof frame
    to the exact trimmed statement and eliminates earlier `$p` rules by cut

- `Metamath/RunEmission.lean`
  - `Metamath/RunEmission.lean` ties the emitted chronology to the actual
    `checkSinglePass` invocation by refinement and determinism

- `Metamath/IncludeInterpretation.lean`
  - `Metamath/IncludeInterpretation.lean` states each mode's complete acceptance
    policy, decomposes its include and compressed-proof dimensions, and connects
    the declarations to runtime helpers

- `Metamath/ErrorCodeSemantics.lean`
  - `Metamath/ErrorCodeSemantics.lean` certifies every `ParseErrorCode` constructor

- `Metamath/DeclarativeSpec.lean`
  - `Metamath/DeclarativeSpec.lean` hosts Mario Carneiro's declarative specification

### Non-core layout

- `Metamath/ParserEquivalenceExamples.lean`
  - `Metamath/ParserEquivalenceExamples.lean` provides compiling usage examples

- `Metamath/CounterexampleInsertError.lean`
  - `Metamath/CounterexampleInsertError.lean` provides a counterexample for insert-with-error behavior

- `Metamath/ParserSoundnessDemo.lean`
  - `Metamath/ParserSoundnessDemo.lean` is a development artifact

- `Metamath/ZipperTest.lean`
  - `Metamath/ZipperTest.lean` is a development artifact

## Toolchain

- The toolchain pins Lean 4.31.0.
- The toolchain pins Batteries v4.31.0.

## Status

- Sorries are 0.
- No project-declared axioms in active `Metamath/` Lean code; the headline
  soundness theorems depend on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) under `#print axioms`.
- `lake build` succeeds on the pinned toolchain.
- The specification suite is 177 of 177 in the default `zar` mode.
- The fail-closed reference differential attempts all 177 registered databases
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

- `checkSinglePass_storedStatements_writtenProof` connects the written `$p`
  proof to the exact trimmed statement stored by the include-aware executable.
- `checkSinglePass_every_theorem_provable_from_run_axiom_events`
  (`Metamath/RunEmission.lean`) eliminates prior `$p` rules by chronological
  cut, leaving only `$a`-classified events — over the run's own chronology:
  `SinglePassEmission` ties the step list to the actual invocation through
  equations about the entrypoint's own IO recursion, and its determinism
  theorem (`SinglePassEmission.unique`) makes that list the only one any
  emission of the invocation can produce.
- `CertifiedRegistryChronology` supplies the registry-continuity form of the
  same history; `ExecutionChronology` is its execution-indexed strengthening
  (subdatabase, exactly-one creation, and bound payloads over the emitted
  list).
- The `proofChecker_*_in_parsedDB` family is fixed-final-database adequacy and is
  not presented as source-proof acceptance.
- `checkBytes_parseErrorCode?_fullyCertified` is the total error certification theorem.
- `parser_operational_iff_semantic_total` is the parser-specialized semantic bridge.

For incomplete proofs, `zar` accepts `?` but reports the database as accepted
and incomplete, never verified.  `sound` and `knife` reject `?`.

### Parser discharge

Parser success discharges WellFormedDatabaseStrong, FloatVarNoDup, and FrameVarsDisjointConsts.
`parser_operational_iff_semantic` composes the full bridge from `checkBytes` success.

```
h_success : (checkBytes bytes).error? = none
  -> parser_construction_wf_scoped
  -> parser_toDatabase_wellFormed_strong
  -> floatVarNoDup_of_uniqueFloatVars
  -> frameVarsDisjointConsts_of_toFrame
  -> operational_iff_semantic
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
- Two operational resource bounds exist that the Metamath specification does
  not impose: `maxIncludeDepth` (default 100) and `maxIncludeResolutions`
  (default 1000000, the include-driver loop's resolution budget; duplicate
  suppressions also consume one resolution).  Exceeding either is reported
  loudly under the `impl_resourceBound` clause — an implementation resource
  outcome, not a claim that the source violated section 4.1.2.
- `--max-include-resolutions=N` overrides the resolution budget;
  `scripts/cli_honesty.sh` pins the zero/sufficient/default canaries.

## Boundary

- Formal theorems cover both the pure `checkBytes` lane over `ByteArray` input
  and properties derived by induction over the include-aware `checkSinglePass`
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

- Reviewers read the theorem statements in `Metamath/ParserEquivalence.lean`.
- Reviewers trace `parser_toDatabase_wellFormed_strong -> parser_operational_iff_semantic -> operational_iff_semantic`.
- Reviewers run `lake build` and the full test suite.

## Build

```bash
lake build
```

## Executables

- Lake executables are `mm-lean4` and `validateDB`.
- The executable build target is `lake build mm-lean4 validateDB`.
