# Diagnostics Contract

This contract describes what a first error from the verifier means and what fields are stable.

## Stable Fields

For a decoded parser/verifier error code `code`:

- Numeric ID: `ParseErrorCode.toNat code`
- Tag: `repr code`
- Clause anchor: `ParseErrorCode.specClause code`
- Message: runtime message stored in `error?`

The inverse mapping for IDs is:

- `ParseErrorCode.ofNat?`
- theorem: `ParseErrorCode.ofNat?_toNat`

## Evidence Shape

Structured evidence is carried by `errorEvidence? : Option ErrorEvidence`.
The certification theorems show that a decoded error code agrees with the
recorded payload; they do not independently prove that the source violates
the corresponding rule. The payload families are:

- `doneMode (DoneModeError)`
- `tokenForm (TokenFormError)`
- `scopeDecl (ScopeDeclError)`
- `includeErr (IncludeError)`
- `proofCheck (ProofCheckError)`
- `theoremFinality (TheoremFinalityError)`
- `compressedSave (CompressedSaveError)`
- `internalGate (allowDuplicateFloat, wellFormed, assertDvVarsInFrame)`

## Boundary

- Verified parser diagnostics are anchored at `checkBytesCore` / `checkBytes`.
- The active `check` path is a single-pass, include-aware driver around the
  same parser, not an include-preprocessing pass. `scanIncludes` and the
  legacy `expandIncludes` path are not part of that active path.
- [correctness.md](correctness.md#verification-boundary) states the proof
  boundary and the assumptions of the bridge between `check` and `checkBytes`.

## CLI Surface

With `--show-error-code`, the CLI prints:

- `[code #<nat>]`
- `[clause <SpecClause>]`
- `[tag <ParseErrorCode>]`
- original message

Reference taxonomy table:

- [ErrorCodes.md](ErrorCodes.md)
