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
