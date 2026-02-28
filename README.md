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

- `Metamath/ErrorCodeSemantics.lean`
  - `Metamath/ErrorCodeSemantics.lean` certifies total error code semantics for 55 codes

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

- The toolchain pins Lean 4.27.0.
- The toolchain pins Batteries v4.27.0-rc1.

## Status

- Sorries are 0.
- Axioms are 0.
- Build status is 129 jobs with 0 errors.
- The default test suite is 151 of 151.
- The small-only test suite is 141 of 141.

```bash
rg -n "sorry" Metamath/
```

## Correctness

The development includes end-to-end correctness theorems for the verifier.
The development includes a formal contract.

### Main claims

- `verify_parser_acceptance_iff_spec_provable` is the normal-mode acceptance biconditional.
- `verify_parser_acceptance_any_mode_iff_spec_provable` is the any-mode acceptance biconditional.
- `checkBytes_done_finishProofEvent_certified` is the per-event prefix provenance theorem.
- `checkBytes_parseErrorCode?_fullyCertified` is the total error certification theorem.
- `parser_operational_iff_semantic_total` is the parser-specialized semantic bridge.

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
- The verifier reports the first error.
- Include I/O failures are environment errors.
- Verifier modes are distinct specifications.

## Boundary

- Formal theorems cover `checkBytes` on expanded `ByteArray` input.
- Include expansion is a trusted preprocessing layer.
- `Metamath/ParserEquivalence.lean` is the review entry module for the composed chain.

## Reproduction

```bash
lake build
cd ../metamath-test && ./run-testsuite-all ./test-mm-lean4
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
