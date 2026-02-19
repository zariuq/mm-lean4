# Correctness Summary

This file lists the main correctness claims, theorems, and the trusted computing base.

## Claims and Theorem Anchors

### Parser -> Spec
- Parser success implies spec well-formedness and scopedness, then acceptance/validity theorems apply.
- Canonical parser-entry completeness (spec provable -> accepted):
  - `verify_parser_accepts_of_spec_provable` in `Metamath/KernelClean.lean`.
  - `verify_impl_complete_of_checkBytes` in `Metamath/KernelClean.lean`.
- Canonical parser-entry soundness (accepted -> spec provable):
  - `verify_parser_sound_of_impl_acceptance` in `Metamath/KernelClean.lean`.
  - `verify_parser_sound_of_impl_acceptance_equiv` in `Metamath/KernelClean.lean`.
- Parser-specialized bridge to Mario semantics (premises discharged from parser success):
  - `parser_operational_iff_semantic_total` in `Metamath/ParserEquivalence.lean`.
  - Internally uses `parser_toDatabase_wellFormed_strong` in `Metamath/KernelClean.lean`
    to satisfy `operational_iff_semantic` in `Metamath/Spec/Equivalence.lean`.

### Kernel Soundness / Completeness
- Implementation soundness (accepted proof -> spec provable):
  - `verify_impl_sound` in `Metamath/KernelClean.lean`.
- Implementation completeness (spec provable -> accepted proof exists):
  - `verify_impl_complete` in `Metamath/KernelClean.lean`.

### Parser Error Semantics
- All parser error codes have rule-level semantic witnesses and spec clause links:
  - `RuleSemanticViolation` and `RuleClauseSemanticViolation` in `Metamath/Verify.lean`.
  - `checkBytes_parseErrorCode?_ruleClauseSemantic_sound` in `Metamath/Verify.lean`.
- Per-code rule+clause theorem specialization exists for every `ParseErrorCode` constructor.

## Trusted Computing Base (TCB)

- Lean kernel and trusted libraries used by this project.
- The `mm-lean4` executable front-end (CLI parsing and file IO).
- Host filesystem and OS for include resolution (include IO failures are classified as environment errors, not spec violations).

## Verification Boundary

- Verified parser diagnostics and semantic theorems are anchored at `checkBytesCore` / `checkBytes` in `Metamath/Verify.lean`.
- Include expansion (`scanIncludes`, `expandIncludes`, `check`) is an IO preprocessing boundary that feeds bytes into the verified parser core.
- Legacy/raw `mkError` paths now carry explicit fallback evidence (`internalGate false false false`) to keep decoded error classification total.

## Intended Reading Order

1. `Metamath/Verify.lean` for parser semantics, error codes, and clause mapping.
2. `Metamath/ParserCorrectness*.lean` for parser-level invariants and correctness.
3. `Metamath/KernelClean.lean` for implementation soundness/completeness and parser-entry wrappers.
