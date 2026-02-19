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

Structured evidence is carried by `errorEvidence? : Option ErrorEvidence` and is used as the semantic witness:
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
- Include expansion (`scanIncludes`, `expandIncludes`, `check`) is IO preprocessing.

## CLI Surface

With `--show-error-code`, the CLI prints:
- `[code #<nat>]`
- `[clause <SpecClause>]`
- `[tag <ParseErrorCode>]`
- original message

Reference taxonomy table:
- `docs/ErrorCodes.md`
