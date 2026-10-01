import Metamath.Verify

/-!
# Source tokens

The lexical categories of the Metamath book (§4.1.1). A label token is a nonempty string of
letters, digits, `-`, `_` and `.`. A math symbol token is a nonempty string of the printable
characters other than `$`, which excludes the space. `ByteSlice.bytes` is the content of a token as
the parser reads it.

`KeysAreTokens` says that every object name of a database is a token of its kind, and
`FloatVarsActive` that every floating hypothesis of the active frame types an active variable,
declared at a depth no deeper than the block that contains the hypothesis.
-/

set_option autoImplicit false

/-- The bytes of a slice, in order. -/
def ByteSlice.bytes (s : ByteSlice) : List UInt8 := s.toByteArray.toList

namespace Metamath.SourceCompleteness

open Metamath.Verify

/-- A label token (Metamath book §4.1.1): letters, digits, `-`, `_` and `.`, at least one. -/
def IsLabelToken (t : String) : Prop :=
  t ≠ "" ∧ ∀ c ∈ t.toList, c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = '.'

/-- A math symbol token (Metamath book §4.1.1): printable characters other than `$`, at least one. -/
def IsMathToken (t : String) : Prop :=
  t ≠ "" ∧ ∀ c ∈ t.toList, 33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '$'

instance (t : String) : Decidable (IsLabelToken t) := by
  unfold IsLabelToken
  infer_instance

instance (t : String) : Decidable (IsMathToken t) := by
  unfold IsMathToken
  infer_instance

/-- Every object name is a token of its kind: constants and variables are math symbol tokens,
hypotheses and assertions are label tokens. -/
def KeysAreTokens (db : DB) : Prop :=
  ∀ l o, db.find? l = some o →
    match o with
    | .const _ | .var _ => IsMathToken l
    | .hyp _ _ _ | .assert _ _ _ => IsLabelToken l

/-- Every floating hypothesis of the active frame types an active variable, declared at a depth
`d` such that every block opened before depth `d` was opened before the hypothesis. Closing a block
therefore removes a floating hypothesis no later than it deactivates its variable. -/
def FloatVarsActive (db : DB) : Prop :=
  ∀ k (hk : k < db.frame.hyps.size) f nm,
    db.find? db.frame.hyps[k] = some (.hyp false f nm) →
    ∃ d, (f[1]!.value, d) ∈ db.activeVars.toList ∧
      ∀ j (hj : j < db.scopes.size), j < d → db.scopes[j].2 ≤ k

end Metamath.SourceCompleteness
