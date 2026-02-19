# mm-lean4 — Metamath Verifier in Lean 4

Formalization of a Metamath proof checker in Lean 4, with both operational and semantic
specifications and a correspondence proof.

## Layout (selected)

Core:
- `Metamath/Spec/` — declarative and operational specs, plus equivalence
- `Metamath/Verify.lean` — implementation of the verifier
- `Metamath/KernelClean.lean` — kernel soundness + completeness proofs
- `Metamath/ParserCorrectness.lean` — parser invariants and correctness layers
- `Metamath/ParserEquivalence.lean` — **canonical review entry point**
- `Metamath/PrefixWitnessCheckBytes.lean` — prefix provenance (per-event)
- `Metamath/ErrorCodeSemantics.lean` — total error code certification (55/55)
- `Metamath/DeclarativeSpec.lean` — Mario Carneiro's declarative specification

Non-core (excluded from default build or clearly auxiliary):
- `Metamath/ParserEquivalenceExamples.lean` — compiling usage examples showing how to call the main theorems (semantic bridge, `soundDefault` prefix provenance, `knife` prefix provenance)
- `Metamath/CounterexampleInsertError.lean` — counterexample proving insert-with-error can modify DB
- `Metamath/ParserSoundnessDemo.lean` — dev artifact (not in build)
- `Metamath/ZipperTest.lean` — dev artifact (not in build)

## Toolchain

Pinned in `lakefile.lean`:
- Lean 4.27.0
- Batteries v4.27.0‑rc1

## Status

- **Sorries**: 0
- **Axioms**: 0
- **Build**: 129 jobs, 0 errors
- **Test suite**: 151/151 (default), 141/141 (small-only)

Detailed status: `CURRENT_STATUS.md`. To verify directly: `rg -n "sorry" Metamath/`

## Correctness

End-to-end correctness theorems for the Metamath verifier, plus a formal
diagnostic contract for parser errors. 0 sorries, 0 axioms.

### Main claims (entry points for review)

1. **`verify_parser_acceptance_iff_spec_provable`** (`KernelClean.lean`) — normal-mode acceptance biconditional: raw `ByteArray` acceptance iff `Spec.Provable`.
2. **`verify_parser_acceptance_any_mode_iff_spec_provable`** (`ParserAnyModeEquivalence.lean`) — any-mode (normal + compressed + Z/saves) acceptance biconditional.
3. **`checkBytes_done_finishProofEvent_certified`** (`PrefixWitnessCheckBytes.lean`) — per-event prefix provenance: each accepted `$p` is provable in the pre-insertion DB, under `ModeConfig.prefixCertified`.
4. **`checkBytes_parseErrorCode?_fullyCertified`** (`ErrorCodeSemantics.lean`) — total error certification: every decoded error code implies payload evidence AND a spec-rule violation (55/55 codes).
5. **`parser_operational_iff_semantic_total`** (`ParserEquivalence.lean`) — parser-specialized bridge to Mario Carneiro's declarative semantics, with all structural premises discharged from `checkBytes` success.

### How parser success discharges Mario-spec assumptions

The bridge to Mario's `Semantic.Provable` requires three structural
premises: `WellFormedDatabaseStrong`, `FloatVarNoDup`, `FrameVarsDisjointConsts`.
All three are **proved** (not assumed) from `checkBytes` success:

```
h_success : (checkBytes bytes).error? = none
  -> parser_construction_wf_scoped        (KernelClean.lean)    -> WellFormedDB + WellScopedDB
  -> parser_toDatabase_wellFormed_strong   (KernelClean.lean)    -> WellFormedDatabaseStrong
  -> floatVarNoDup_of_uniqueFloatVars      (ParserEquivalence)   -> FloatVarNoDup
  -> frameVarsDisjointConsts_of_toFrame    (ParserEquivalence)   -> FrameVarsDisjointConsts
  -> operational_iff_semantic              (Spec/Equivalence)    -> Spec.Provable <-> Semantic.Provable
```

This chain is composed in `parser_operational_iff_semantic` (`ParserEquivalence.lean:335`).
No well-formedness hypothesis floats — `h_success` is the sole gateway.

### Diagnostics

Diagnostic taxonomy (codes -> messages -> clauses -> predicates): `docs/ErrorCodes.md`.
The verifier reports the first error. Include I/O failures are environment errors,
not spec violations. Different verifier modes (`exe`, `knife`, `permissive`) are
explicitly treated as different specs.

### Trust boundary

- Formal theorems cover `checkBytes` given a fully-expanded `ByteArray`.
- IO include expansion (`scanIncludes`/`expandIncludes`) is a trusted preprocessing layer.
- `Metamath/ParserEquivalence.lean` is the review entry module for the composed theorem chain.

### Reproduction

```bash
lake build                           # 129 jobs, 0 errors
cd ../metamath-test && ./run-testsuite-all ./test-mm-lean4   # 151/151
```

Optional large-db check: `lake exe validateDB ../metamath-test/core/large/set.mm`

### Quick expert-review checklist

1. Read theorem statements in `Metamath/ParserEquivalence.lean`.
2. Trace the discharge chain: `parser_toDatabase_wellFormed_strong` -> `parser_operational_iff_semantic` -> `operational_iff_semantic`.
3. Run `lake build` and the full test suite above.

## Build

```bash
lake build
```

## Executables

The Lake config defines:
- `mm-lean4` (main verifier)
- `validateDB` (database validator)

Build with:
```bash
lake build mm-lean4 validateDB
```
