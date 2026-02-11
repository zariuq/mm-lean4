# mm-lean4 — Metamath Verifier in Lean 4

Formalization of a Metamath proof checker in Lean 4, with both operational and semantic
specifications and a correspondence proof.

## Layout (selected)

- `Metamath/Spec/` — declarative and operational specs, plus equivalence
- `Metamath/Verify` — implementation of the verifier
- `Metamath/KernelClean` — kernel soundness infrastructure
- `Metamath/ParserCorrectness` — parser invariants and correctness layers

## Toolchain

Pinned in `lakefile.lean`:
- Lean 4.27.0
- Batteries v4.27.0‑rc1

## Status & review

Project status is tracked in:
- `CURRENT_STATUS.md` — latest reported status
- `BLOCKING_SORRIES.md` — remaining proof gaps (if any)

To check proof gaps directly:
```bash
rg -n "sorry" Metamath/
```

## Correctness (summary)

This project provides end‑to‑end correctness theorems for the Metamath verifier, and a
formal diagnostic contract for parser errors.

Core guarantees (with theorem anchors) are summarized in `docs/correctness.md`, including:

- Parser‑origin acceptance ⇔ spec provability (`Metamath/KernelClean.lean`):
  - `verify_parser_accepts_of_spec_provable`
  - `verify_parser_sound_of_impl_acceptance` / `_equiv`
- Kernel soundness / completeness:
  - `verify_impl_sound`
  - `verify_impl_complete`
- Parser error semantics for all codes:
  - `RuleSemanticViolation` / `RuleClauseSemanticViolation`
  - `checkBytes_parseErrorCode?_ruleClauseSemantic_sound`

Diagnostic taxonomy (codes → messages → clauses → predicates) is listed in
`docs/ErrorCodes.md`. The verifier reports the first error; include I/O failures are
classified as environment errors rather than spec violations. Different verifier modes
(`exe`, `knife`, `permissive`) are explicitly treated as different specs.

Compatibility and reproduction:

- `lake build`
- `metamath-test/run-testsuite-all` (see `metamath-test` repo)

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
