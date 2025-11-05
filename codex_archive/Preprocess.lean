/-
Preprocessing correctness for Metamath verification.

This module defines the preprocessor (include stripping) and states
its correctness properties. The preprocessor is kept separate from
the verified kernel per GPT-5's pragmatic verification approach.
-/

import Metamath.Spec

namespace Metamath.Preprocess

/-! ## Include Stripping

Per Metamath spec §4.1.2:
"A file may include itself... will simply be ignored"

Our preprocessor replaces all `$[...$]` directives with whitespace.
This handles self-includes correctly (they get stripped) and simplifies
the parser (no recursive file loading needed).
-/

/-- Strip all include directives from a ByteArray, replacing with spaces -/
def stripIncludes (arr : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  let mut i := 0
  while i < arr.size do
    -- Check for "$["
    if i + 1 < arr.size && arr[i]! == '$'.toUInt8 && arr[i+1]! == '['.toUInt8 then
      i := i + 2
      -- Scan until "$]"
      while i + 1 < arr.size &&
            !(arr[i]! == '$'.toUInt8 && arr[i+1]! == ']'.toUInt8) do
        i := i + 1
      -- Skip the closing "$]"
      if i + 1 < arr.size then i := i + 2
      -- Replace entire directive with single space (preserve token boundaries)
      result := result.push ' '.toUInt8
    else
      result := result.push arr[i]!
      i := i + 1
  result

/-! ## Correctness Properties

These are STATEMENTS of correctness to be proven, not proofs themselves.
They define what it means for stripIncludes to be correct.
-/

/-! ### Property 1: Whitespace Preservation

Stripping includes preserves whitespace structure (tokens remain separated).
-/

def isWhitespace (b : UInt8) : Bool :=
  b == ' '.toUInt8 || b == '\n'.toUInt8 || b == '\t'.toUInt8 || b == '\r'.toUInt8

/-- Include directives are replaced with whitespace -/
axiom stripIncludes_adds_whitespace (arr : ByteArray) (i : Nat) :
  i < (stripIncludes arr).size →
  (stripIncludes arr)[i]! == ' '.toUInt8 ∨
  (∃ j, j < arr.size ∧ arr[j]! = (stripIncludes arr)[i]!)

/-! ### Property 2: Token Equivalence

After stripping includes, the sequence of non-whitespace tokens is valid.
This is the key property: preprocessing doesn't corrupt the content.
-/

def tokens (arr : ByteArray) : List ByteArray :=
  -- Simplified: split on whitespace
  -- Real implementation would use full tokenizer
  sorry

axiom stripIncludes_preserves_tokens (arr : ByteArray) :
  -- For non-include content, tokens unchanged
  ∀ tok, tok ∈ tokens arr →
    ¬(tok[0]! == '$'.toUInt8 ∧ tok[1]! == '['.toUInt8) →
    tok ∈ tokens (stripIncludes arr)

/-! ### Property 3: Self-Include Correctness

The specific case we care about: self-includes are handled correctly.
Per spec §4.1.2, a self-include "will simply be ignored".
-/

axiom stripIncludes_removes_self_includes (arr : ByteArray) :
  -- If arr contains "$[ filename $]" where filename = arr's filename
  -- Then stripIncludes removes it
  ∀ i j, i < j → j < arr.size →
    arr[i]! == '$'.toUInt8 → arr[i+1]! == '['.toUInt8 →
    arr[j]! == '$'.toUInt8 → arr[j+1]! == ']'.toUInt8 →
    -- Result: gap [i..j+2) replaced with single space
    (stripIncludes arr).size < arr.size

/-! ### Property 4: Soundness

The BIG property: preprocessing preserves semantics.

If we verify the stripped version, then the original is also valid
(assuming no actual file inclusions, i.e., all includes stripped).
-/

axiom stripIncludes_sound (arr : ByteArray) :
  -- If the stripped version parses to database db
  ∀ db fr, Metamath.Spec.Database →
    -- (Parser produces db from stripped arr)
    -- Then the semantic validity is preserved
    (∀ l e, db l = some (fr, e) →
      Metamath.Spec.Provable db fr e) →
    -- (Same semantics for original, if no actual includes needed)
    True  -- Formalization TODO

/-! ## Discussion: What Does This Prove?

These axioms define what we WANT to prove about stripIncludes.
They are not proofs themselves - they are proof obligations.

**Status:** UNPROVEN (axioms, not theorems)

**Why axioms?** To document requirements without doing full proofs yet.
Per GPT-5's advice: "start with specs, prove later".

**Difficulty:** ⭐⭐ (Low-medium)
- Property 1-3: Straightforward induction on array structure
- Property 4: Requires connecting to parser and Spec.lean

**Value:** Medium
- Self-includes are extremely rare edge case
- Preprocessor is only 20 lines, easy to audit
- Type safety already prevents crashes/undefined behavior

**Recommendation:** Defer proving these until core kernel verified.
-/

/-! ## Future Work: Include Resolution

If we wanted to support REAL includes (not just stripping), we'd need:

1. **File I/O**: Load included files from disk
2. **Path resolution**: Handle relative/absolute paths
3. **Cycle detection**: Prevent infinite include loops
4. **Scope handling**: Include content inherits scope

This is ~200 lines of code and much harder to verify.
For now, stripIncludes is sufficient for 38/38 compliance.
-/

end Metamath.Preprocess
