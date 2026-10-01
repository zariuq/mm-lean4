import Metamath.SourceCompleteness
import Metamath.Tests.CheckerCompletenessCalibration

/-!
# Calibration of source-level completeness

Executable checks of `Metamath.SourceCompleteness` on concrete source text, run when this file is
compiled: `#guard` evaluates each check and fails the build if it is not `true`. They are tests of
concrete parser runs, not kernel proofs of each fixture's premises. `premises`, `admissibleB` and
`continues` compute the premises, the witness condition (`Admissible`) and the conclusions
(`SourceAccepts`) of `statementProvable_iff_sourceAccepts` in the default mode; `declaredB_iff` and
`admissibleB_iff` prove that the Boolean checks decide the corresponding propositions.
-/

set_option autoImplicit false

namespace Metamath.SourceCompletenessCalibration

open Metamath.Verify Metamath.CheckerCompleteness Metamath.SourceCompleteness
open Metamath.CheckerCompletenessCalibration

def isWs (s : ParserState) : Bool :=
  match s.charp with
  | .ws => true
  | .token _ _ => false

def sameFrame (a b : Verify.Frame) : Bool := a.dj == b.dj && a.hyps == b.hyps

/-- `FormulaSymbolsDeclared`, computed. -/
def declaredB (db : DB) (f : Verify.Formula) : Bool :=
  f.toList.all fun x => match x with
    | .const c => db.isConst c
    | .var v => db.isVar v

theorem declaredB_iff (db : DB) (f : Verify.Formula) :
    declaredB db f = true ↔ Metamath.WF.FormulaSymbolsDeclared db f := by
  simp only [declaredB, List.all_eq_true, Metamath.WF.FormulaSymbolsDeclared]
  constructor <;> intro h x hx <;> have h' := h x hx <;> cases x <;> exact h'

/-- `Admissible`, computed. -/
def admissibleB (s : ParserState) (ds : List DummyDecl) (label : String) (f : Verify.Formula)
    (proof : Array String) : Bool :=
  ds.all (fun d => (s.db.find? d.var).isNone && (s.db.find? d.lbl).isNone &&
      s.db.isConst d.tc && decide (IsMathToken d.var) && decide (IsLabelToken d.lbl) &&
      decide (IsMathToken d.tc)) &&
    decide ((ds.map (·.var) ++ ds.map (·.lbl) ++ [label]).Nodup) &&
    decide (IsLabelToken label) && f.toList.all (fun x => decide (IsMathToken x.value)) &&
    proof.toList.all (fun l => decide (IsLabelToken l))

theorem admissibleB_iff (s : ParserState) (ds : List DummyDecl) (label : String)
    (f : Verify.Formula) (proof : Array String) :
    admissibleB s ds label f proof = true ↔ Admissible s ds label f proof := by
  simp only [admissibleB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨⟨⟨⟨h_ds, h_nd⟩, h_label⟩, h_claim⟩, h_proof⟩
    exact
      { fresh := ⟨fun d hd => (h_ds d hd).1.1.1.1.1, fun d hd => (h_ds d hd).1.1.1.1.2, h_nd,
          fun d hd => (h_ds d hd).1.1.1.2⟩
        var_token := fun d hd => (h_ds d hd).1.1.2
        lbl_token := fun d hd => (h_ds d hd).1.2
        tc_token := fun d hd => (h_ds d hd).2
        label_token := h_label
        claim_tokens := h_claim
        proof_tokens := h_proof }
  · intro h
    exact ⟨⟨⟨⟨fun d hd => ⟨⟨⟨⟨⟨h.fresh.var_fresh d hd, h.fresh.lbl_fresh d hd⟩,
      h.fresh.tc_const d hd⟩, h.var_token d hd⟩, h.lbl_token d hd⟩, h.tc_token d hd⟩,
      h.fresh.nodup⟩, h.label_token⟩, h.claim_tokens⟩, h.proof_tokens⟩

/-- The premises of `statementProvable_iff_sourceAccepts` at the end of `src`, in the default
mode: no duplicate `$f` statements, an error-free read ending between statements with no token
pending, a fresh label token, a claim with a constant head and declared symbols, and a trimmed
frame with a spec frame. Returns the trimmed frame. -/
def premises (src : String) (label : String) (f : Verify.Formula) : Option Verify.Frame :=
  let config : ModeConfig := {}
  let s := afterSource config src.toUTF8
  if !config.allowDuplicateFloat && s.db.error?.isNone && isStart s && isWs s &&
      (s.db.find? label).isNone && decide (IsLabelToken label) && f.hasConstHead &&
      declaredB s.db f then
    match s.db.trimFrame' f with
    | .ok frImpl => if (Kernel.toFrame s.db frImpl).isSome then some frImpl else none
    | .error _ => none
  else none

/-- The conclusions of the source theorem after the continuation `text`, with no check of the
text: no error, a clean checkpoint, `label` stored as `f` with the frame `frImpl`, and no new
incomplete proof. -/
def continues (src : String) (text : ByteArray) (label : String) (f : Verify.Formula)
    (frImpl : Verify.Frame) : Bool :=
  let e := afterSource {} (src.toUTF8 ++ text)
  e.db.error?.isNone && isStart e && isWs e &&
    (match e.db.find? label with
     | some (.assert g fr l) => g == f && sameFrame fr frImpl && l == label
     | _ => false) &&
    e.db.incompleteProofs == (after src).db.incompleteProofs

/-- The premises, the admissibility of the witness `ds`, `proof`, and the conclusions of
`statementProvable_iff_sourceAccepts` for its rendering. -/
def accepts (src : String) (ds : List DummyDecl) (label : String) (f : Verify.Formula)
    (proof : Array String) : Bool :=
  match premises src label f with
  | some frImpl => admissibleB (after src) ds label f proof &&
      continues src (render (after src) ds label f proof) label f frImpl
  | none => false

def rejects (src : String) (text : ByteArray) : Bool :=
  (afterSource {} (src.toUTF8 ++ text)).db.error?.isSome

/-! ## The pre-target checkpoint: zero declarations -/

def preTh : String := axiomBlock ++ "${\n  $v y $.\n  wy $f wff y $.\n"

#guard (premises preTh "th" claimC).isSome
#guard String.fromUTF8! (render (after preTh) [] "th" claimC #["wy", "wy", "ax"]) ==
  "th $p |- c $= wy wy ax $. "
#guard accepts preTh [] "th" claimC #["wy", "wy", "ax"]

/-! ## The premises -/

-- A label that is not a label token, a claim with an undeclared constant, an empty claim and a
-- label already in use fail the premises.
#guard (premises preTh "bad label" claimC).isNone
#guard (premises preTh "th" #[.const "|-", .const "undeclared"]).isNone
#guard (premises preTh "th" #[]).isNone
#guard (premises preTh "ax" claimC).isNone

/-! ## No active `$f` for the needed variable: one dummy -/

def noDummy : String := axiomBlock ++ "${\n"

#guard (premises noDummy "th" claimC).isSome
#guard rejects noDummy (render (after noDummy) [] "th" claimC #["wy", "wy", "ax"])
#guard String.fromUTF8! (render (after noDummy) [⟨"wff", "y", "wy"⟩] "th" claimC
  #["wy", "wy", "ax"]) == "$v y $. wy $f wff y $. th $p |- c $= wy wy ax $. "
#guard accepts noDummy [⟨"wff", "y", "wy"⟩] "th" claimC #["wy", "wy", "ax"]

/-! ## A dummy that needs a `$d` pair with a frame variable -/

#guard (premises dvSource "th2" claimC).isSome
#guard String.fromUTF8! (render (after dvSource) [⟨"wff", "u", "wu"⟩] "th2" claimC
  #["wz", "wu", "hz", "wu", "ax2"]) ==
  "$v u $. wu $f wff u $. $d u z $. th2 $p |- c $= wz wu hz wu ax2 $. "
#guard accepts dvSource [⟨"wff", "u", "wu"⟩] "th2" claimC #["wz", "wu", "hz", "wu", "ax2"]
-- Without the pair the same proof is rejected.
#guard rejects dvSource "$v u $. wu $f wff u $. th2 $p |- c $= wz wu hz wu ax2 $. ".toUTF8

/-! ## Two dummies: one unordered pair, in the order the parser stores it -/

def twoDummies : String :=
  "$c wff |- c $.\n${\n  $v x w $.\n  wx $f wff x $.\n  ww $f wff w $.\n  hx $e wff x $.\n" ++
  "  hw $e wff w $.\n  $d x w $.\n  ax2 $a |- c $.\n$}\n${\n"

#guard (premises twoDummies "th3" claimC).isSome
#guard String.fromUTF8! (render (after twoDummies) [⟨"wff", "v", "wv"⟩, ⟨"wff", "u", "wu"⟩] "th3"
  claimC #["wv", "wu", "wv", "wu", "ax2"]) ==
  "$v v $. wv $f wff v $. $v u $. wu $f wff u $. $d u v $. th3 $p |- c $= wv wu wv wu ax2 $. "
#guard accepts twoDummies [⟨"wff", "v", "wv"⟩, ⟨"wff", "u", "wu"⟩] "th3" claimC
  #["wv", "wu", "wv", "wu", "ax2"]
#guard rejects twoDummies
  "$v v $. wv $f wff v $. $v u $. wu $f wff u $. th3 $p |- c $= wv wu wv wu ax2 $. ".toUTF8

/-! ## The empty claim -/

-- The literal final check rejects an empty claim ...
#guard rejects preTh (render (after preTh) [] "th" #[] #["wy", "wy", "ax"])
-- ... which the expression-level conversion cannot tell from the claim `ERROR`.
theorem toExpr_empty : Kernel.toExpr #[] = Kernel.toExpr #[.const "ERROR"] := rfl

/-! ## Witnesses outside admissible rendering -/

#guard decide (IsLabelToken "wy") && decide (IsMathToken "|-")
#guard !decide (IsLabelToken "bad label") && !decide (IsLabelToken "")
#guard !decide (IsMathToken "a b") && !decide (IsMathToken "")
#guard !decide (IsMathToken "$.") && !decide (IsLabelToken "x$.")
#guard !decide (IsLabelToken "é") && !decide (IsLabelToken "α")
-- Illegal tokens, and dummy names that collide with an old label or with the target label.
#guard !admissibleB (after preTh) [] "th" claimC #["wy", "wy", "ax $. th4 $a |- c"]
#guard !admissibleB (after noDummy) [⟨"wff", "a b", "wy"⟩] "th" claimC #["wy", "wy", "ax"]
#guard !admissibleB (after noDummy) [⟨"wff", "y", "ax"⟩] "th" claimC #["ax"]
#guard !admissibleB (after noDummy) [⟨"wff", "y", "th"⟩] "th" claimC #["th"]
-- Rendering such strings anyway: a label with a space is rejected ...
#guard rejects preTh (render (after preTh) [] "bad label" claimC #["wy", "wy", "ax"])
-- ... and a proof item carrying commands smuggles in a further statement, the axiom `th4`.
#guard ((afterSource {} (preTh.toUTF8 ++ render (after preTh) [] "th" claimC
  #["wy", "wy", "ax $. th4 $a |- c"])).db.find? "th4").isSome

/-- No axiom proves `|- c` here. -/
def noAxioms : String := "$c wff |- c $.\n"

-- A dummy label carrying commands declares the axiom `evil` before the claim, and the claim is
-- then "proved" from it: with the raw check `continues`, the four source conditions hold for a
-- statement that is not provable from the assertions of the prefix. The witness is not admissible.
#guard match premises noAxioms "th" claimC with
  | some frImpl => continues noAxioms (render (after noAxioms)
      [⟨"wff", "y", "evil $a |- c $. wy"⟩] "th" claimC #["evil"]) "th" claimC frImpl
  | none => false
#guard !admissibleB (after noAxioms) [⟨"wff", "y", "evil $a |- c $. wy"⟩] "th" claimC #["evil"]

/-! ## A pending token is not a clean checkpoint -/

def pendingSource : String := preTh ++ "th"

#guard isStart (after pendingSource) && !isWs (after pendingSource)
#guard (premises pendingSource "th2" claimC).isNone
-- A well-formed completion still parses ...
#guard (checkBytes (pendingSource ++ " $p |- c $= wy wy ax $.\n$}\n").toUTF8).error?.isNone
-- ... but rendered text spliced onto the pending token extends it: the label read is `thth2`.
#guard !continues pendingSource (render (after pendingSource) [] "th2" claimC
  #["wy", "wy", "ax"]) "th2" claimC default
#guard ((afterSource {} (pendingSource.toUTF8 ++ render (after pendingSource) [] "th2" claimC
  #["wy", "wy", "ax"])).db.find? "thth2").isSome

/-! ## `?` is accepted as incomplete, never a witness -/

#guard !decide (IsLabelToken "?")
#guard !admissibleB (after preTh) [] "th" claimC #["?"]
#guard !accepts preTh [] "th" claimC #["?"]
#guard (afterSource {} (preTh.toUTF8 ++ render (after preTh) [] "th" claimC #["?"])).db.incompleteProofs
  == #["th"]

/-! ## End of file: the open blocks are closed -/

def fileBytes : ByteArray :=
  preTh.toUTF8 ++ render (after preTh) [] "th" claimC #["wy", "wy", "ax"]

#guard (checkBytes fileBytes).error?.isSome
#guard (after preTh).db.scopes.size == 1
#guard (checkBytes (fileBytes ++ closeBlocks 1)).error?.isNone
#guard (checkBytes (fileBytes ++ closeBlocks 1)).incompleteProofs.isEmpty
#guard match (checkBytes (fileBytes ++ closeBlocks 1)).find? "th" with
  | some (.assert g _ _) => g == claimC
  | _ => false

-- Two open blocks: one closer is not enough; two close the file, keep every earlier object, and
-- leave the block's variable inactive.
def nested : String := axiomBlock ++ "${ ${ $v y $. wy $f wff y $. "
def nestedText : ByteArray := render (after nested) [] "th" claimC #["wy", "wy", "ax"]

#guard accepts nested [] "th" claimC #["wy", "wy", "ax"]
#guard (after nested).db.scopes.size == 2
#guard (checkBytes (nested.toUTF8 ++ nestedText ++ closeBlocks 1)).error?.isSome
#guard (checkBytes (nested.toUTF8 ++ nestedText ++ closeBlocks 2)).error?.isNone
#guard (checkBytes (nested.toUTF8 ++ nestedText ++ closeBlocks 2)).incompleteProofs.isEmpty
#guard !(checkBytes (nested.toUTF8 ++ nestedText ++ closeBlocks 2)).isActiveVar "y"
#guard (after nested).db.objects.toList.all fun (name, _) =>
  ((checkBytes (nested.toUTF8 ++ nestedText ++ closeBlocks 2)).find? name).isSome

/-! ## Other shapes of claims and scopes -/

-- A continuation at top level: the dummy is declared globally and stays active.
#guard (after axiomBlock).db.scopes.size == 0
#guard accepts axiomBlock [⟨"wff", "y", "wy"⟩] "th" claimC #["wy", "wy", "ax"]
#guard (checkBytes (axiomBlock.toUTF8 ++
  render (after axiomBlock) [⟨"wff", "y", "wy"⟩] "th" claimC #["wy", "wy", "ax"])).isActiveVar "y"

-- A claim with variables and a mandatory `$d`: the trimmed frame keeps the pair, and without the
-- pair in scope the same proof fails.
def dvClaim : String :=
  "$c wff |- ( -> ) $.\n$v p q r $.\nwp $f wff p $.\nwq $f wff q $.\nwr $f wff r $.\n" ++
  "${ $d p q $. ax1 $a |- ( p -> q ) $. $}\n${ $d p q $.\n"
def dvClaimNoPair : String :=
  "$c wff |- ( -> ) $.\n$v p q r $.\nwp $f wff p $.\nwq $f wff q $.\nwr $f wff r $.\n" ++
  "${ $d p q $. ax1 $a |- ( p -> q ) $. $}\n${\n"
def claimPQ : Verify.Formula :=
  #[.const "|-", .const "(", .var "p", .const "->", .var "q", .const ")"]

#guard match premises dvClaim "th" claimPQ with
  | some fr => fr.dj == #[("p", "q")] && fr.hyps == #["wp", "wq"]
  | none => false
#guard accepts dvClaim [] "th" claimPQ #["wp", "wq", "ax1"]
#guard (premises dvClaimNoPair "th" claimPQ).isSome
#guard !accepts dvClaimNoPair [] "th" claimPQ #["wp", "wq", "ax1"]

-- A dummy next to an optional variable of the active frame gets its `$d` pair with it.
#guard String.fromUTF8! (render (after preTh) [⟨"wff", "d", "wd"⟩] "th" claimC
  #["wd", "wd", "ax"]) == "$v d $. wd $f wff d $. $d d y $. th $p |- c $= wd wd ax $. "
#guard accepts preTh [⟨"wff", "d", "wd"⟩] "th" claimC #["wd", "wd", "ax"]

-- A variable declared again after its block closed, used in the claim.
def redeclared : String :=
  "$c wff |- ( -> ) $.\n${ $v p $. wp1 $f wff p $. ax-id $a |- ( p -> p ) $. $}\n" ++
  "$v p $. wp2 $f wff p $.\n"
def claimPP : Verify.Formula :=
  #[.const "|-", .const "(", .var "p", .const "->", .var "p", .const ")"]

#guard accepts redeclared [] "th" claimPP #["wp2", "ax-id"]
-- A claim variable without an active `$f` fails the premises.
#guard (premises "$c wff |- ( -> ) $.\n$v p $.\n" "th" claimPP).isNone

/-! ## Modes

The theorem covers modes without duplicate `$f` statements: the default, `sound` and `knife`. The
shipped `exe` and `permissive` presets allow duplicate `$f` statements and lie outside it. -/

#guard !({} : ModeConfig).allowDuplicateFloat
#guard !ModeConfig.sound.allowDuplicateFloat && !ModeConfig.knife.allowDuplicateFloat
#guard ModeConfig.exe.allowDuplicateFloat && ModeConfig.permissive.allowDuplicateFloat

/-! ## Provability is relative to the assertions read so far

An earlier incomplete theorem is an assertion of the prefix. A complete proof may use it; it stays
incomplete, so the file is accepted, not verified. -/

def incompletePrefix : String := "$c |- c $.\nold $p |- c $= ? $.\n"

#guard accepts incompletePrefix [] "new" claimC #["old"]
#guard (checkBytes (incompletePrefix.toUTF8 ++
  render (after incompletePrefix) [] "new" claimC #["old"])).incompleteProofs == #["old"]

/-! ## The claim of the injection example is not provable

The prefix declares no assertion. With no axioms and no hypotheses, a derivation in Mario Carneiro's
semantics yields only a variable, whatever the `$d` relation, never the constant conclusion `|- c`.
So no statement of that claim without hypotheses is provable; `Statement.Provable` reads a statement
in its `untrim` context, which keeps its hypotheses and changes only its `$d` relation. -/

#guard !(after noAxioms).db.objects.toList.any (fun (_, o) => o matches .assert ..)

theorem empty_derivation_is_variable {axs : Metamath.Statement → Prop} (haxs : ∀ a, ¬ axs a)
    {dj : Metamath.DJ} {f : Metamath.Formula} (h : Metamath.Provable axs ⟨[], dj⟩ f) :
    ∃ v : Metamath.VR, f = Metamath.VR.vhyp v := by
  cases h with
  | hyp _ hmem => exact False.elim (List.not_mem_nil hmem)
  | var v => exact ⟨v, rfl⟩
  | ax _ hax _ _ _ => exact False.elim (haxs _ hax)

theorem constant_not_provable_without_axioms {axs : Metamath.Statement → Prop}
    (haxs : ∀ a, ¬ axs a) (dj : Metamath.DJ) :
    ¬ Metamath.Provable axs ⟨[], dj⟩ ("|-", [Metamath.Sym.const "c"]) := by
  intro h
  obtain ⟨v, hv⟩ := empty_derivation_is_variable haxs h
  have heq : [Metamath.Sym.const "c"] = [Metamath.Sym.var v] := congrArg Prod.snd hv
  cases heq

theorem constant_statement_not_provable_without_axioms {axs : Metamath.Statement → Prop}
    (haxs : ∀ a, ¬ axs a) (dj : Metamath.DJ) :
    ¬ (⟨⟨[], dj⟩, ("|-", [Metamath.Sym.const "c"])⟩ : Metamath.Statement).Provable axs :=
  constant_not_provable_without_axioms haxs _

/-! ## `Verify.check` and `checkBytes`

The source-file
label reaches the database only through include-path payloads: an empty include
directive fails under both labels, with evidence naming each label, so equality
of the two databases is false on error paths.  A complete include directive
makes the pure entrypoint report an include request, the case the bridge's
hypothesis excludes (the driver would resolve the include instead). -/

#guard (RootFileCheck.checkBytesCoreAt "a.mm" "$[ $]".toUTF8 {}).errorEvidence?
  = some (.includeErr (.emptyPathBeforeNormalization "a.mm"))
#guard (checkBytes "$[ $]".toUTF8 {}).errorEvidence?
  = some (.includeErr (.emptyPathBeforeNormalization ""))
#guard match (checkBytes "$c a $. $[ x.mm $]".toUTF8 {}).error? with
  | some ⟨.includeRequest _ p, _⟩ => p == "x.mm"
  | _ => false


end Metamath.SourceCompletenessCalibration

/-! ## No include request from a continuation without `$[`

Executable checks, not proofs. Each drops one of the three conditions of
`checkBytes_append_errorNotRequest` on the text read first (read without error, between tokens,
outside the include-directive modes), keeps the other two and a continuation without a token `$[`,
and gets an include request. The same continuations after text that meets all three raise none. -/

namespace Metamath.SourceCompleteness.NoRequestCalibration

open Metamath.Verify Metamath.CheckerCompleteness Metamath.SourceCompleteness

def isRequest : Option Interrupt → Bool
  | some ⟨.includeRequest _ _, _⟩ => true
  | _ => false

def isWs (s : ParserState) : Bool :=
  match s.charp with
  | .ws => true
  | .token _ _ => false

def isStart (s : ParserState) : Bool :=
  match s.tokp with
  | .start => true
  | _ => false

def isIncludePath (s : ParserState) : Bool :=
  match s.tokp with
  | .includePath _ _ => true
  | _ => false

-- Outside the include-directive modes dropped: `$[ ` ends without error, between tokens, in
-- `.includePath`.
#guard (afterSource {} "$[ ".toUTF8).db.error?.isNone
#guard isWs (afterSource {} "$[ ".toUTF8)
#guard isIncludePath (afterSource {} "$[ ".toUTF8)
#guard isRequest (checkBytes ("$[ ".toUTF8 ++ "x.mm $] ".toUTF8) {}).error?

-- Between tokens dropped: `$` ends without error at `.start`, with the token `$` pending.
#guard (afterSource {} "$".toUTF8).db.error?.isNone
#guard isStart (afterSource {} "$".toUTF8)
#guard !isWs (afterSource {} "$".toUTF8)
#guard isRequest (checkBytes ("$".toUTF8 ++ "[ x.mm $] ".toUTF8) {}).error?

-- Read without error dropped: `$[ x.mm $] ` ends between tokens at `.start`, with the request.
#guard isRequest (afterSource {} "$[ x.mm $] ".toUTF8).db.error?
#guard isWs (afterSource {} "$[ x.mm $] ".toUTF8)
#guard isStart (afterSource {} "$[ x.mm $] ".toUTF8)
#guard isRequest (checkBytes ("$[ x.mm $] ".toUTF8 ++ ByteArray.empty) {}).error?

-- All three hold after `$c a $. `.
#guard (afterSource {} "$c a $. ".toUTF8).db.error?.isNone
#guard isWs (afterSource {} "$c a $. ".toUTF8)
#guard isStart (afterSource {} "$c a $. ".toUTF8)
#guard !isRequest (checkBytes ("$c a $. ".toUTF8 ++ "x.mm $] ".toUTF8) {}).error?
#guard !isRequest (checkBytes ("$c a $. ".toUTF8 ++ "[ x.mm $] ".toUTF8) {}).error?
#guard !isRequest (checkBytes ("$c a $. ".toUTF8 ++ ByteArray.empty) {}).error?
#guard !isRequest (checkBytes ("$c a $. ".toUTF8 ++ renderText ["$v", "x", "$."]) {}).error?

end Metamath.SourceCompleteness.NoRequestCalibration
