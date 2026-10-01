import Metamath.CheckerCompleteness.Declare
import Metamath.SourceCompleteness.Tokens

/-!
# Rendering dummy declarations and a proof as source text

`render s ds label f proof` is the source text that continues at the parser state `s`: for each
dummy variable in `ds`, `$v d $.` and `lbl $f tc d $.`; then one `$d` statement per pair that
`Verify.DB.declareDummies` records, computed from the float variables of the active frame of `s`;
then `label $p f $= proof $.`. Tokens are separated by single spaces, and the text ends with one.
`closeBlocks k` closes `k` blocks at the end of a file.

`Admissible s ds label f proof` requires fresh dummy declarations typed by declared constants,
tokens of the right kind throughout, and a normal proof made of label tokens, so no `?` step and
no compressed proof. At a reachable checkpoint the token conditions on the label, the claim and the
typecodes also follow from the premises of the source theorem; they are kept so that `Admissible`
alone fixes the grammar of the rendered text.
-/

set_option autoImplicit false

namespace Metamath.SourceCompleteness

open Metamath.Verify
open Metamath.CheckerCompleteness

/-- The tokens that declare the dummy variables `ds`: `$v d $.` and `lbl $f tc d $.` for each, then
`$d` for each pair that `Verify.DB.declareDummies` records. `seen` lists the float variables of the
active frame before the declarations. -/
def declTokens (seen : List String) (ds : List DummyDecl) : List String :=
  (ds.flatMap fun d => ["$v", d.var, "$.", d.lbl, "$f", d.tc, d.var, "$."]) ++
  ((dummyDJs seen (ds.map (·.var))).flatMap fun p => ["$d", p.1, p.2, "$."])

/-- The tokens of the `$p` statement `label` with claim `f` and the normal proof `proof`. -/
def thmTokens (label : String) (f : Verify.Formula) (proof : Array String) : List String :=
  label :: "$p" :: (f.toList.map (·.value) ++ "$=" :: (proof.toList ++ ["$."]))

/-- The tokens of the source text that declares the dummy variables `ds` and proves the `$p`
statement `label` with claim `f` by the normal proof `proof`. -/
def renderTokens (seen : List String) (ds : List DummyDecl) (label : String)
    (f : Verify.Formula) (proof : Array String) : List String :=
  declTokens seen ds ++ thmTokens label f proof

/-- Source text for a list of tokens: each token followed by one space. -/
def renderText (toks : List String) : ByteArray :=
  (String.join (toks.map (· ++ " "))).toUTF8

/-- Feed the tokens `toks` one at a time, each as a slice spelling it, at the positions they have in
`renderText toks` placed at `base`; stop at the first error. -/
def runTokens (s : ParserState) (base : Nat) : List String → ParserState
  | [] => s
  | t :: ts =>
      let s' := s.feedToken base t.toUTF8.toByteSlice
      if s'.db.error?.isSome then s' else runTokens s' (base + t.toUTF8.size + 1) ts

/-- The source text that continues at the parser state `s`. -/
def render (s : ParserState) (ds : List DummyDecl) (label : String) (f : Verify.Formula)
    (proof : Array String) : ByteArray :=
  renderText (renderTokens (s.db.frameFloatVars s.db.frame) ds label f proof)

/-- Source text closing `k` blocks: `$}` `k` times. -/
def closeBlocks (k : Nat) : ByteArray :=
  renderText (List.replicate k "$}")

/-- Dummy declarations and a proof that can be rendered at `s`: fresh dummy variables typed by
declared constants, tokens of the right kind throughout, and a normal proof of label tokens. -/
structure Admissible (s : ParserState) (ds : List DummyDecl) (label : String) (f : Verify.Formula)
    (proof : Array String) : Prop where
  fresh : DummyDeclsFresh s.db label ds
  var_token : ∀ d ∈ ds, IsMathToken d.var
  lbl_token : ∀ d ∈ ds, IsLabelToken d.lbl
  tc_token : ∀ d ∈ ds, IsMathToken d.tc
  label_token : IsLabelToken label
  claim_tokens : ∀ x ∈ f.toList, IsMathToken x.value
  proof_tokens : ∀ l ∈ proof.toList, IsLabelToken l

end Metamath.SourceCompleteness
