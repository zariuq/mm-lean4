import Lean.Elab.Term
import Metamath.Verify

/-!
# Declarative Specification

Mario Carneiro's canonical declarative specification of Metamath proof validity.
This defines **what** a valid proof is mathematically (the "big-step" view),
as opposed to **how** the verifier checks it operationally (the "small-step" view
in `Spec/Operational.lean`).

## Metamath Specification References (Chapter 4)

| Section | Topic | Lean Type |
|---------|-------|-----------|
| §4.2.2 | Constants and Variables | `CN`, `VR`, `Sym` |
| §4.2.3 | Expressions | `Expr`, `Expr.subst` |
| §4.2.4 | Disjoint variable restrictions | `DJ`, `DJ.subst` |
| §4.2.5 | Floating ($f) and essential ($e) hypotheses | `Formula`, `VR.vhyp` |
| §4.2.6 | Assertions ($a and $p statements) | `Statement`, `Statement.WellFormed` |
| §4.2.7 | Frames (mandatory hypotheses + DV) | `Context` |
| §4.3 | Proof verification algorithm | `Provable` |

## Key Theorem

The main result (in `Spec/Equivalence.lean`) is:
```lean
theorem operational_iff_semantic {Γ : Database} {fr : Frame} {e : Expr}
    (h_wf : WellFormedDatabaseStrong Γ)
    (h_fr_nodup : FloatVarNoDup fr) :
    Provable Γ fr e ↔
    Semantic.Provable (dbToAxioms Γ) (frameToContext fr)
      (exprToFormula (varMapOfFrame fr) e)
```

This establishes both soundness and completeness: the operational verifier
accepts exactly those proofs that are valid under Mario's declarative semantics.
-/

namespace Metamath
open Lean Elab
open Verify in
partial def foo : TermElabM Unit := do
  let h ← IO.FS.Handle.mk "/home/mario/Documents/metamath/mm/iset.mm" IO.FS.Mode.read
  let rec loop (s : ParserState) (base : Nat) : IO (Except ParserState DB) := do
    let buf ← h.read 1024
    if buf.isEmpty then
      pure <| .ok <| s.done base
    else
      let s := s.feedAll base buf
      if s.db.error?.isSome then pure <| .error s
      else loop s (base + buf.size)
  match ← loop Inhabited.default 0 with
  | .ok _ => pure ()
  | .error s' => match s'.db.error? with
    | some ⟨.ax _pos l f fr, _i⟩ =>
      IO.println s!"axiom {l}: {fr} |- {f}"
    | some ⟨.thm _pos l f fr, _i⟩ =>
      IO.println s!"theorem {l}: {fr} |- {f}"
    | some ⟨.error pos msg, _⟩ =>
      IO.println s!"at {pos}: {msg}"
    | _ => pure ()

-- #eval foo

/-! ## Core Types (§4.2.2)

Per §4.2.2: "The basic Metamath language has two kinds of math symbols:
constants and variables."

The substitution distinction (§4.2.2):
- "In a Metamath proof, a constant may not be substituted with any expression."
- "A variable can be substituted with any expression."

This distinction is enforced in `Expr.subst`: constants pass through unchanged,
variables are replaced by the substitution function. -/

/-- Constant name: the string representation of a constant symbol.
    Examples: "wff", "|-", "(", "->", "0" -/
def CN := String
instance : Inhabited CN := inferInstanceAs (Inhabited String)
instance : DecidableEq CN := inferInstanceAs (DecidableEq String)

/-- Variable reference: pairs a variable with its typecode.
    - `type`: the typecode from the $f statement (e.g., "wff", "term", "set")
    - `i`: index to distinguish variables of the same type (e.g., P vs Q)

    Per §4.2.5: "A variable must have its type specified in a $f statement
    before it may be used in a $e, $a, or $p statement." -/
structure VR where (type : CN) (i : Nat)
deriving DecidableEq

/-- Math symbol: either a constant or a variable (§4.2.2).

    The key distinction: in `Expr.subst`, constants pass through unchanged
    while variables are replaced by their substitution values. -/
inductive Sym
  | const (c : CN)  -- constant: not substituted
  | var (n : VR)    -- variable: replaced by σ(n) during substitution
  deriving Inhabited, DecidableEq
open Sym

instance : Coe String Sym := ⟨const⟩
def Sym.isVar : Sym → Bool
  | const _ => false
  | var _ => true

/-! ## Expressions

Per §4.2.2: "An expression is any sequence of math symbols, possibly empty." -/

/-- Expression: a sequence of symbols (§4.2.2) -/
def Expr := List Sym
/-- Variable as a singleton expression -/
def VR.expr (v : VR) : Expr := [var v]

instance : Append Expr := inferInstanceAs (Append (List Sym))
instance : Membership Sym Expr := inferInstanceAs (Membership Sym (List Sym))
def Expr.sn (s : Sym) : Expr := [s]
instance : Coe String Expr := ⟨fun c => Expr.sn c⟩
instance : Coe VR Expr := ⟨fun v => Expr.sn (var v)⟩
def Expr.cons (c : String) : Expr → Expr := List.cons c
def Expr.mem (e : Expr) (v : VR) : Prop := var v ∈ e

scoped notation:50 a:51 " ∈' " b:51 => Expr.mem b a

/-- Variables occurring in an expression -/
def Expr.vars : Expr → List VR
  | [] => []
  | const _ :: e => vars e
  | var v :: e => v :: vars e

/-! ## Substitution (§4.2.2, §4.3)

Per §4.2.2: "A variable can be substituted with any expression. This sequence
may include other variables and may even include the variable being substituted."

Per §4.3: During proof verification, "Metamath determines what substitutions
have to be made into the variables of the assertion's mandatory hypotheses
to make them identical to the associated stack entries." -/

/-- Apply substitution to an expression: replace each variable v with σ(v).
    - Constants pass through unchanged (per §4.2.2: "a constant may not be substituted")
    - Variables are replaced by their image under σ -/
def Expr.subst (σ : VR → Expr) : Expr → Expr
  | [] => []
  | const c :: e => const c :: subst σ e  -- constant: unchanged
  | var v :: e => σ v ++ subst σ e        -- variable: replaced

theorem Expr.subst_id : (e : Expr) → Expr.subst VR.expr e = e
  | [] => rfl
  | const c :: e => congrArg (const c :: .) (subst_id e)
  | var v :: e => congrArg (var v :: .) (subst_id e)

theorem Expr.subst_append (σ) : (e₁ e₂ : Expr) → Expr.subst σ (e₁ ++ e₂) = e₁.subst σ ++ e₂.subst σ
  | [], _ => rfl
  | const c :: (e₁ : Expr), e₂ => by
    rw [subst, List.cons_append, subst, subst_append ..]; rfl
  | var v :: e, e₂ => by
    rw [List.cons_append]; simp only [Expr.subst]; rw [List.append_assoc, subst_append ..]

theorem Expr.mem_subst {σ a} : {e : Expr} → a ∈' Expr.subst σ e → ∃ b, b ∈' e ∧ a ∈' σ b
  | const _ :: _, .tail _ h => let ⟨b, h₁, h₂⟩ := mem_subst h; ⟨b, .tail _ h₁, h₂⟩
  | var v :: _, h =>
    match List.mem_append.1 h with
    | Or.inl h => ⟨v, .head _, h⟩
    | Or.inr h => let ⟨b, h₁, h₂⟩ := mem_subst h; ⟨b, .tail _ h₁, h₂⟩

def subst.trans (σ σ' : VR → Expr) (v : VR) : Expr := (σ v).subst σ'

theorem Expr.subst_tr (σ σ' : VR → Expr) : (e : Expr) →
    e.subst (subst.trans σ σ') = (e.subst σ).subst σ'
  | [] => rfl
  | const c :: e => congrArg (const c :: .) (subst_tr _ _ e)
  | var v :: e => by simp only [subst]; rw [subst_append, subst_tr _ _ e]; rfl

/-! ## Formulas (§4.2.5)

Per §4.2.5: "The expression in a $f, $e, $a, or $p statement consists of a
typecode (an active constant math symbol) followed by a sequence of zero
or more math symbols."

A Formula is a (typecode, expression) pair. Examples:
- `("wff", [P, "->", Q])` represents "wff ( P -> Q )"
- `("|-", [P])` represents "|- P" (P is provable)

Test: metamath-test/tests/unit/test12_non-constant_typecode.mm
  (typecode must be a constant, not a variable) -/

/-- Formula: a typecode paired with an expression (§4.2.5) -/
def Formula := CN × Expr

/-- Apply substitution to formula -/
def Formula.subst (σ : VR → Expr) : Formula → Formula
  | (c, e) => (c, e.subst σ)

theorem Formula.subst_id : (e : Formula) → Formula.subst VR.expr e = e
  | (c, e) => congrArg (c, .) e.subst_id

theorem Formula.subst_tr (σ σ' : VR → Expr) : (e : Formula) →
    e.subst (subst.trans σ σ') = (e.subst σ).subst σ'
  | (c, e) => congrArg (c, .) (e.subst_tr _ _)

/-- Convert a variable to its floating hypothesis formula.

    Per §4.2.5: The syntax of a $f statement is "$f typecode variable $."
    This creates a formula (typecode, [variable]).

    Example: If v has type "wff" and index 0 (representing variable P),
    then v.vhyp = ("wff", [var v]), representing "wff P".

    Test: metamath-test/tests/unit/test14_variable_without_f_hypothesis.mm
      (every variable used must have a $f hypothesis) -/
def VR.vhyp (v : VR) : Formula := (v.type, [var v])
instance : Coe VR Formula := ⟨VR.vhyp⟩

/-- Check if two expressions have no variables in common -/
def Expr.δ (a b : Expr) : Bool :=
  a.all fun
  | const _ => true
  | var a => b.all fun
    | const _ => true
    | var b => a != b

/-! ## Disjoint Variable Constraints

Per §4.2.4: "The $d statement is called a disjoint-variable restriction...
The full meaning is that if any substitution is made to its two variables
(during the course of a proof that references a $a or $p statement
associated with the $d), the two expressions that result from the
substitution must have no variables in common."

Interpretations (§4.2.4):
- `$d x y $.` means "assume x and y are distinct variables."
- `$d x ph $.` means "assume x does not occur in φ."
- `$d ph ps $.` means "assume φ and ψ have no variables in common."

Tests:
- metamath-test/tests/unit/test09_d_with_non-variables.mm
- metamath-test/tests/core/small/dv-violation-bad1.mm -/

/-- Disjoint variable relation (§4.2.4): symmetric, irreflexive -/
structure DJ where
  disj : VR → VR → Prop
  irr : ¬ disj x x
  symm : disj x y → disj y x

instance : CoeFun DJ (fun _ => VR → VR → Prop) := ⟨DJ.disj⟩
instance : LE DJ := ⟨fun dj dj' => ∀ a b, dj a b → dj' a b⟩

theorem DJ.refl (dj : DJ) : dj ≤ dj := fun _ _ => id

theorem DJ.ne (dj : DJ) {a b} (h : dj a b) : a ≠ b :=
  fun e => by cases e; exact dj.irr h

theorem DJ.ext : {dj₁ dj₂ : DJ} → (∀ a b, dj₁ a b ↔ dj₂ a b) → dj₁ = dj₂
  | ⟨dj₁, _, _⟩, ⟨dj₂, _, _⟩, h =>
    have : dj₁ = dj₂ := funext fun a => funext fun b => propext (h a b)
    by cases this; rfl

theorem DJ.le_antisymm {dj₁ dj₂ : DJ} (H₁ : dj₁ ≤ dj₂) (H₂ : dj₂ ≤ dj₁) : dj₁ = dj₂ :=
  DJ.ext fun _ _ => ⟨H₁ _ _, H₂ _ _⟩

def DJ.mk' (disj : List (VR × VR)) : DJ where
  disj := fun a b => a ≠ b ∧ ((a, b) ∈ disj ∨ (b, a) ∈ disj)
  irr := fun h => h.1 rfl
  symm := fun ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩

/-- Two expressions are disjoint under dj if all variable pairs are disjoint -/
def Expr.disjoint (dj : DJ) (e₁ e₂ : Expr) : Prop :=
  ∀ a b, a ∈' e₁ → b ∈' e₂ → dj a b

theorem Expr.disjoint.mono {dj₁ dj₂ : DJ} (h : dj₁ ≤ dj₂) {e₁ e₂}
    (H : Expr.disjoint dj₁ e₁ e₂) : Expr.disjoint dj₂ e₁ e₂ :=
  fun a b ha hb => h _ _ (H a b ha hb)

/-- Substitution respects DV constraints.

    Per §4.2.4: "if any substitution is made to [two variables in a $d],
    the two expressions that result from the substitution must have no
    variables in common. In addition, each possible pair of variables,
    one from each expression, must be in a $d statement associated with
    the statement being proved."

    `DJ.subst σ dj dj'` means: if (a, b) is in the source DV relation `dj`,
    then the substituted expressions σ(a) and σ(b) are disjoint under `dj'`. -/
def DJ.subst (σ : VR → Expr) (dj dj' : DJ) :=
  ∀ a b, dj a b → (σ a).disjoint dj' (σ b)

theorem DJ.subst.mono {σ : VR → Expr} {dj₁ dj₂ dj₁' dj₂' : DJ}
    (h : dj₂ ≤ dj₁) (h' : dj₁' ≤ dj₂') (H : dj₁.subst σ dj₁') : dj₂.subst σ dj₂' :=
  fun _ _ d => Expr.disjoint.mono h' (H _ _ (h _ _ d))

def DJ.trim (dj : DJ) (P : VR → Prop) : DJ where
  disj := fun x y => dj x y ∧ P x ∧ P y
  irr := fun x => dj.irr x.1
  symm := fun ⟨h₁, h₂, h₃⟩ => ⟨dj.symm h₁, h₃, h₂⟩

theorem DJ.trim.mono {dj₁ dj₂ : DJ} (hdj : dj₁ ≤ dj₂) {P Q : VR → Prop}
    (pq : ∀ x, P x → Q x) : dj₁.trim P ≤ dj₂.trim Q :=
  fun _ _ ⟨h, ha, hb⟩ => ⟨hdj _ _ h, pq _ ha, pq _ hb⟩

def DJ.trimmed (dj : DJ) (P : VR → Prop) : Prop :=
  ∀ a b, dj a b → P a ∧ P b

theorem DJ.trimmed.mono (dj : DJ) {P Q : VR → Prop}
    (h : ∀ x, P x → Q x) (H : dj.trimmed P) : dj.trimmed Q
  | a, b, d => let ⟨h₁, h₂⟩ := H a b d; ⟨h _ h₁, h _ h₂⟩

theorem DJ.trim_le_self (dj : DJ) (P : VR → Prop) : dj.trim P ≤ dj := fun _ _ d => d.1

theorem DJ.trim.trimmed (dj : DJ) (P : VR → Prop) : (dj.trim P).trimmed P := fun _ _ h => h.2

theorem DJ.trimmed.trim_eq {dj : DJ} {P} (h : dj.trimmed P) : dj.trim P = dj :=
  DJ.ext fun _ _ => ⟨fun h => h.1, fun h' => ⟨h', h _ _ h'⟩⟩

def DJ.untrim (dj : DJ) (P : VR → Prop) : DJ where
  disj := fun x y => x ≠ y ∧ (P x → P y → dj x y)
  irr := fun x => x.1 rfl
  symm := fun ⟨h₁, h₂⟩ => ⟨h₁.symm, fun x y => dj.symm (h₂ y x)⟩

theorem DJ.untrim.mono {dj₁ dj₂ : DJ} (hdj : dj₁ ≤ dj₂) {P Q : VR → Prop}
    (qp : ∀ x, Q x → P x) : dj₁.untrim P ≤ dj₂.untrim Q :=
  fun _ _ ⟨h₁, h₂⟩ => ⟨h₁, fun ha hb => hdj _ _ (h₂ (qp _ ha) (qp _ hb))⟩

theorem DJ.trim_le {dj₁ dj₂ : DJ} {P} : dj₁.trim P ≤ dj₂ ↔ dj₁ ≤ dj₂.untrim P where
  mp H _ _ h := ⟨dj₁.ne h, fun ha hb => H _ _ ⟨h, ha, hb⟩⟩
  mpr H _ _ := fun ⟨h, ha, hb⟩ => (H _ _ h).2 ha hb

theorem DJ.self_le_untrim (dj : DJ) (P : VR → Prop) : dj ≤ dj.untrim P :=
  DJ.trim_le.1 <| DJ.trim_le_self _ _

theorem DJ.trim_untrim (dj : DJ) (P : VR → Prop) : (dj.untrim P).trim P = dj.trim P :=
  DJ.le_antisymm (fun _ _ ⟨h, ha, hb⟩ => ⟨h.2 ha hb, ha, hb⟩)
    (DJ.trim.mono (DJ.self_le_untrim _ _) (fun _ => id))

theorem DJ.untrim_trim (dj : DJ) (P : VR → Prop) : (dj.trim P).untrim P = dj.untrim P :=
  DJ.le_antisymm (DJ.untrim.mono (DJ.trim_le_self _ _) (fun _ => id))
    fun _ _ ⟨h, H⟩ => ⟨h, fun ha hb => ⟨H ha hb, ha, hb⟩⟩

/-! ## Context (Frame)

Per §4.2.7: "A frame is a sequence of $d, $f, and $e statements (zero or more
of each) followed by one $a or $p statement... A frame groups together those
hypotheses (and $d statements) relevant to an assertion."

Properties (§4.2.7):
1. Variables in $e/$a/$p must have $f hypothesis (type specified)
2. No two $f statements for the same variable
3. $f must occur before $e using that variable

Test: metamath-test/tests/unit/test15_multiple_f_for_same_variable_bad.mm -/

/-- Context: hypotheses + DV constraints (corresponds to a frame, §4.2.7) -/
structure Context where
  hyps : List Formula
  dj : DJ

def Context.mk' (disj : List (VR × VR)) (hyps : List Formula) : Context :=
  ⟨hyps, DJ.mk' disj⟩

instance : LE Context := ⟨fun Γ Γ' => (∀ a, a ∈ Γ.hyps → a ∈ Γ'.hyps) ∧ Γ.dj ≤ Γ'.dj⟩

theorem Context.refl (Γ : Context) : Γ ≤ Γ := ⟨fun _ => id, DJ.refl _⟩

/-! ## Statement (Assertion) (§4.2.6)

Per §4.2.6: "There are two types of assertions, $a statements (axiomatic
assertions) and $p statements (provable assertions). Their syntax is:
  label $a typecode math-symbol ... math-symbol $.
  label $p typecode math-symbol ... math-symbol $= proof $."

A Statement packages together the context (frame's hypotheses + DV constraints)
with the conclusion formula. This corresponds to what §4.2.7 calls a "frame"
combined with its assertion. -/

/-- Statement: context (hypotheses + DV) paired with conclusion formula.
    Corresponds to an assertion ($a or $p) together with its frame (§4.2.6-7). -/
structure Statement where
  ctx : Context
  fmla : Formula

instance : LE Statement := ⟨fun s s' => s.ctx ≤ s'.ctx ∧ s.fmla = s'.fmla⟩

theorem Statement.refl (s : Statement) : s ≤ s := ⟨Context.refl _, rfl⟩

def Statement.vars (s : Statement) : List VR :=
  (s.fmla :: s.ctx.hyps).flatMap fun e => e.2.vars

theorem Statement.vars.mono' {s₁ s₂ : Statement}
    (H : ∀ a, a ∈ s₁.ctx.hyps → a ∈ s₂.ctx.hyps) (H₂ : s₁.fmla = s₂.fmla)
    (v) : v ∈ s₁.vars → v ∈ s₂.vars := by
  simp only [vars, List.mem_flatMap, List.mem_cons, H₂]
  exact fun ⟨a, b, c⟩ => ⟨a, b.imp_right (H _), c⟩

theorem Statement.vars.mono {s₁ s₂ : Statement} (H : s₁ ≤ s₂) : ∀ v, v ∈ s₁.vars → v ∈ s₂.vars :=
  Statement.vars.mono' H.1.1 H.2

def Statement.trim (s : Statement) : Statement :=
  ⟨⟨s.ctx.hyps, s.ctx.dj.trim fun v => v ∈ s.vars⟩, s.fmla⟩

def Statement.untrim' (s : Statement) (P : VR → Prop) : Statement :=
  ⟨⟨s.ctx.hyps, s.ctx.dj.untrim P⟩, s.fmla⟩
def Statement.untrim (s : Statement) : Statement := s.untrim' fun v => v ∈ s.vars

theorem Statement.trim_le_self (s : Statement) : s.trim ≤ s :=
  ⟨⟨fun _ => id, DJ.trim_le_self _ _⟩, rfl⟩

theorem Statement.self_le_untrim' (s : Statement) (P) : s ≤ s.untrim' P :=
  ⟨⟨fun _ => id, DJ.self_le_untrim _ _⟩, rfl⟩
theorem Statement.self_le_untrim (s : Statement) : s ≤ s.untrim := s.self_le_untrim' _

theorem Statement.trim.mono {s₁ s₂ : Statement} (h : s₁ ≤ s₂) : s₁.trim ≤ s₂.trim :=
  ⟨⟨h.1.1, DJ.trim.mono h.1.2 (Statement.vars.mono h)⟩, h.2⟩

theorem Statement.untrim'.mono {s₁ s₂ : Statement} {P Q}
    (H : ∀ x, Q x → P x) (h : s₁ ≤ s₂) : s₁.untrim' P ≤ s₂.untrim' Q :=
  ⟨⟨h.1.1, DJ.untrim.mono h.1.2 H⟩, h.2⟩
theorem Statement.untrim.mono {s₁ s₂ : Statement}
    (H : s₁.ctx.hyps = s₂.ctx.hyps) (h : s₁ ≤ s₂) : s₁.untrim ≤ s₂.untrim :=
  Statement.untrim'.mono (Statement.vars.mono' (by rw [H]; exact fun _ => id) h.2.symm) h

theorem Statement.trim_vars (s : Statement) : s.trim.vars = s.vars := rfl
theorem Statement.untrim'_vars (s : Statement) (P) : (s.untrim' P).vars = s.vars := rfl
theorem Statement.untrim_vars (s : Statement) : s.untrim.vars = s.vars := rfl

theorem Statement.trim_untrim (s : Statement) : s.untrim.trim = s.trim := by
  simp only [trim, untrim_vars]; simp only [untrim, untrim', DJ.trim_untrim]

theorem Statement.untrim_trim (s : Statement) : s.trim.untrim = s.untrim := by
  simp only [untrim, untrim', trim_vars]; simp only [trim, DJ.untrim_trim]

theorem Statement.trim_le {s₁ s₂ : Statement} (e : s₁.vars = s₂.vars) :
    s₁.trim.ctx ≤ s₂.ctx ↔ s₁.ctx ≤ s₂.untrim.ctx where
  mp := fun ⟨h₁, h₂⟩ => ⟨h₁, DJ.trim_le.1 <| by rw [← e]; exact h₂⟩
  mpr := fun ⟨h₁, h₂⟩ => ⟨h₁, DJ.trim_le.2 <| by rw [e]; exact h₂⟩

def Statement.trimmed (s : Statement) : Prop := s.ctx.dj.trimmed fun v => v ∈ s.vars

theorem Statement.trim.trimmed (s : Statement) : s.trim.trimmed := DJ.trim.trimmed _ _

theorem Statement.trimmed.trim_eq : {s : Statement} → s.trimmed → s.trim = s
  | ⟨⟨a, b⟩, c⟩, h => by simp only [trim]; rw [DJ.trimmed.trim_eq h]

/-! ## Provable (Declarative/Big-Step Semantics)

Per §4.3: "Each label in a proof must be either the label of a previous
assertion ($a or $p statement) or the label of an active hypothesis
($e or $f statement)."

This is the **declarative** specification: what makes a proof valid, without
describing the operational details of stack manipulation.

Constructors:
- `hyp`: Reference an essential hypothesis from the context
- `var`: Reference a floating hypothesis (variable typing)
- `ax`: Apply an axiom/theorem with substitution

The key constraint (§4.2.4, §4.3): when applying an axiom, the substitution
must respect all DV constraints. -/

/-- Declarative provability (§4.3): the "big-step" semantics -/
inductive Provable (axs : Statement → Prop) (Γ : Context) : Formula → Prop
  /-- Use an essential hypothesis directly -/
  | hyp (h) : h ∈ Γ.hyps → Provable axs Γ h
  /-- Use a floating hypothesis (variable typing) -/
  | var (v:VR) : v.vhyp ∈ Γ.hyps → Provable axs Γ v
  /-- Apply an axiom with substitution σ, proving all hypotheses -/
  | ax (σ) {ax} : axs ax → ax.ctx.dj.subst σ Γ.dj →
    (∀ h ∈ ax.ctx.hyps, Provable axs Γ (h.subst σ)) →
    (∀ v ∈ ax.vars, Provable axs Γ (v.type, σ v)) →
    Provable axs Γ (ax.fmla.subst σ)

theorem Provable.mono {axs₁ axs₂} (haxs : ∀ a, axs₁ a → axs₂ a)
    {Γ₁ Γ₂} (hΓ : Γ₁ ≤ Γ₂) {e} (pr : Provable axs₁ Γ₁ e) : Provable axs₂ Γ₂ e := by
  induction pr with
  | hyp e h => exact hyp e (hΓ.1 _ h)
  | var v h => exact var v (hΓ.1 _ h)
  | ax σ ha h₁ _ _ IH_h IH_v =>
    exact ax σ (haxs _ ha) (h₁.mono (DJ.refl _) hΓ.2)
      (fun h hm => IH_h h hm) (fun v vm => IH_v v vm)

def Statement.Provable' (axs : Statement → Prop) (s : Statement) : Prop :=
  Provable axs s.ctx s.fmla

theorem Statement.Provable'.mono {axs₁ axs₂} (haxs : ∀ a, axs₁ a → axs₂ a) :
    {s₁ s₂ : Statement} → s₁ ≤ s₂ → s₁.Provable' axs₁ → s₂.Provable' axs₂
  | ⟨_Γ₁, _⟩, ⟨_Γ₂, _⟩, ⟨hΓ, rfl⟩ => Provable.mono haxs hΓ

def Statement.Provable (axs : Statement → Prop) (s : Statement) : Prop :=
  s.untrim.Provable' axs

-- theorem Statement.Provable.mono {axs₁ axs₂} (haxs : ∀ a, axs₁ a → axs₂ a) :
--   {s₁ s₂ : Statement} → s₁ ≤ s₂ → s₁.Provable axs₁ → s₂.Provable axs₂
-- | s₁, s₂, h, hs, pr =>
--   Statement.Provable'.mono haxs (untrim'.mono (fun _ => id) hs) $
--   Statement.Provable'.mono (fun _ => id) _ pr

theorem Statement.Provable'.of {axs} {s : Statement} (h : s.Provable' axs) : s.Provable axs :=
  h.mono (fun _ => id) (self_le_untrim _)

theorem Statement.Provable.trim {axs} {s : Statement} : s.trim.Provable axs ↔ s.Provable axs := by
  simp only [Provable, untrim_trim]

/-- Well-formed statement (§4.2.5, §4.2.7): all variables used in the formula
    or hypotheses have floating hypotheses in the context.

    Per §4.2.5: "A variable must have its type specified in a $f statement
    before it may be used in a $e, $a, or $p statement."

    Per §4.2.7: "The set of variables contained in its $f statements must be
    identical to the set of variables contained in its $e, $a, and/or $p
    statements."

    Test: metamath-test/tests/unit/test14_variable_without_f_hypothesis.mm -/
def Statement.WellFormed (s : Statement) : Prop :=
  ∀ v ∈ s.vars, v.vhyp ∈ s.ctx.hyps

theorem Provable.ax_self (axs : Statement → Prop) {ax} (H : axs ax)
    (h_wf : ax.WellFormed) : ax.Provable' axs := by
  have := Provable.ax (Γ := ax.ctx) VR.expr H ?disj ?hyp ?var
  rw [Formula.subst_id] at this; exact this
  case disj =>
    intro a b h a' b' h₁ h₂
    match a', b', h₁, h₂ with | _, _, .head _, .head _ => ?_
    exact h
  case hyp =>
    intro h h_in
    rw [Formula.subst_id]
    exact .hyp h h_in
  case var =>
    intro v v_in
    -- VR.expr v = [var v], so (v.type, VR.expr v) = v.vhyp
    -- By h_wf: v ∈ ax.vars → v.vhyp ∈ ax.ctx.hyps
    show Provable axs ax.ctx (v.type, VR.expr v)
    exact .var v (h_wf v v_in)

/-- Substitution through a proof. With the new `var` requiring membership,
    the variable case is subsumed by the hypothesis case. -/
theorem Provable.trans' {axs Γ} (σ) {Γ' fmla} (pr : Provable axs Γ' fmla)
    (dj : Γ'.dj.subst σ Γ.dj)
    (hh : ∀ h ∈ Γ'.hyps, Provable axs Γ (h.subst σ)) :
    Provable axs Γ (fmla.subst σ) := by
  induction pr with
  | hyp f h => exact hh f h
  | var v h_in => exact hh v.vhyp h_in
  | @ax σ' a ha dj' _ _ IH_h IH_v =>
    rw [← Formula.subst_tr]
    apply ax (subst.trans σ' σ) ha
    · -- DV constraint
      intros x y xy c d hc hd
      let ⟨e, ea, ce⟩ := Expr.mem_subst hc
      let ⟨f, fb, df⟩ := Expr.mem_subst hd
      exact dj _ _ (dj' _ _ xy _ _ ea fb) _ _ ce df
    · -- Essential hypotheses
      intro h h_in
      rw [Formula.subst_tr]
      exact IH_h h h_in
    · -- Variable typing
      intro v v_in
      -- (v.type, subst.trans σ' σ v) = (v.type, (σ' v).subst σ)
      -- IH_v gives: Provable axs Γ ((v.type, σ' v).subst σ)
      -- which equals: Provable axs Γ (v.type, (σ' v).subst σ)
      exact IH_v v v_in

theorem Provable.trans'' {axs Γ σ} (s : Statement) : s.Provable' axs →
    s.ctx.dj.subst σ Γ.dj →
    (∀ h ∈ s.ctx.hyps, Provable axs Γ (h.subst σ)) →
    Provable axs Γ (s.fmla.subst σ) :=
  Provable.trans' (axs := axs) σ

def subst_of : List (VR × Expr) → VR → Expr
  | [], v => v
  | (a, e)::l, v => if a = v then e else subst_of l v

class Subst (σ : VR → Expr) (e : Expr) (e' : outParam Expr) where (out : e.subst σ = e')

instance [Subst σ e₁ e₁'] [Subst σ e₂ e₂'] : Subst σ (e₁ ++ e₂) (e₁' ++ e₂') :=
  ⟨by rw [Expr.subst_append, Subst.out, Subst.out]⟩

instance (s : String) : Subst σ s s := ⟨rfl⟩

instance (s : String) [Subst σ e e'] : Subst σ (s ++ e) (s ++ e') :=
  inferInstanceAs (Subst σ (Expr.sn _ ++ e) _)
instance (s : String) [Subst σ e e'] : Subst σ (e ++ s) (e' ++ s) :=
  inferInstanceAs (Subst σ (e ++ Expr.sn _) _)

def subst.ok (axs Γ) (σ : VR → Expr) := ∀ v, Provable axs Γ (v.type, σ v)

theorem subst.ok.nil {axs Γ} (h : ∀ v : VR, v.vhyp ∈ Γ.hyps) : subst.ok axs Γ (subst_of []) :=
  fun v => Provable.var v (h v)
theorem subst.ok.cons {axs Γ e σ} (x) (h₁ : Provable axs Γ (x.type, e))
    (h₂ : subst.ok axs Γ (subst_of σ)) : subst.ok axs Γ (subst_of ((x, e)::σ)) := by
  intro v
  simp only [subst_of]
  cases Decidable.em (x = v) with simp [h]
  | inl h => cases h; exact h₁
  | inr h => exact h₂ v

theorem Provable.thm {axs} {Γ : Context}
    {σ : VR → Expr} {dj hyps c s} (pr : Provable axs (Context.mk' dj hyps) (c, s))
    (_hv : subst.ok axs Γ σ)  -- No longer needed: variable typing now in ax constructor
    (dj : (DJ.mk' dj).subst σ Γ.dj)
    (hh : ∀ h ∈ hyps, Provable axs Γ (h.subst σ))
    {e} [inst : Subst σ s e] : Provable axs Γ (c, e) := by
  rw [← inst.out]
  -- The source context is Context.mk' dj hyps, so its hyps field is exactly `hyps`
  -- Provable.var now requires v.vhyp ∈ hyps, so all hyps are covered by hh
  refine Metamath.Provable.trans' σ pr dj ?_
  intro h h_in
  exact hh h h_in

theorem DJ_nil {σ dj'} : (DJ.mk' []).subst σ dj' | _, _, h => nomatch h
theorem DJ_cons {a b l σ dj'}
    (h₁ : (σ a).disjoint dj' (σ b))
    (h₂ : (DJ.mk' l).subst σ dj') : (DJ.mk' ((a, b) :: l)).subst σ dj'
  | _, _, ⟨_, .inl (.head _)⟩ => h₁
  | _, _, ⟨_, .inr (.head _)⟩ => fun x y hx hy => dj'.symm (h₁ y x hy hx)
  | _, _, ⟨h, .inl (.tail _ h')⟩ => h₂ _ _ ⟨h, .inl h'⟩
  | _, _, ⟨h, .inr (.tail _ h')⟩ => h₂ _ _ ⟨h, .inr h'⟩

theorem HH_nil {axs Γ σ} : ∀ h:Formula, h ∈ [] → Provable axs Γ (h.subst σ)
  | _, h => nomatch h

theorem HH_cons {axs Γ σ c f hyps}
    {e} [Subst σ f e] (h₁ : Provable axs Γ (c, e))
    (h₂ : ∀ h:Formula, h ∈ hyps → Provable axs Γ (h.subst σ)) :
    ∀ h:Formula, h ∈ (c, f)::hyps → Provable axs Γ (h.subst σ)
  | _, .head _ => by rw [← @Subst.out σ f e] at h₁; exact h₁
  | _, .tail _ h => h₂ _ h

class Typed (axs : outParam _) (c : outParam CN) (e : Expr) where
  type Γ : Provable axs Γ (c, e)

def Expr.ty (e) {axs c} [Typed axs c e] {Γ} : Provable axs Γ (c, e) := Typed.type Γ

/-!
## Demo Section (Commented Out)

The Demo section below is a by-hand translation of demo0.mm. It is commented out because
the axioms in Demo.axs don't include floating hypotheses for their variables in their
contexts, which violates Metamath's well-formedness requirement (§4.2.4):

  "A variable must have its type specified in a $f statement before it may be used"

With the corrected `Provable.var` constructor that now requires `v.vhyp ∈ Γ.hyps`,
these axioms would need to include appropriate floating hypotheses.

For example, the axiom `⟨Context.mk' [] [], ("term", pl vt vr)⟩` should be:
```
⟨Context.mk' [] [vt.vhyp, vr.vhyp], ("term", pl vt vr)⟩
```

This demonstrates the semantic gap that the fix to `Provable.var` addresses.
-/

/-
namespace Demo

def ze : Expr := "0"
instance : Subst σ ze ze := inferInstanceAs (Subst σ "0" _)

def pl (t r : Expr) : Expr := "(" ++ t ++ "+" ++ r ++ ")"
instance [Subst σ t t'] [Subst σ r r'] : Subst σ (pl t r) (pl t' r') :=
  inferInstanceAs (Subst σ (_++_) _)

def eq (t r : Expr) : Expr := t ++ "=" ++ r
instance [Subst σ t t'] [Subst σ r r'] : Subst σ (eq t r) (eq t' r') :=
  inferInstanceAs (Subst σ (_++_) _)

def im (P Q : Expr) : Expr := "(" ++ P ++ "->" ++ Q ++ ")"
instance {P Q P' Q'} [Subst σ P P'] [Subst σ Q Q'] : Subst σ (im P Q) (im P' Q') :=
  inferInstanceAs (Subst σ (_++_) _)

def al (x P : Expr) : Expr := "A." ++ x ++ P
instance {x P x' P'} [Subst σ x x'] [Subst σ P P'] : Subst σ (al x P) (al x' P') :=
  inferInstanceAs (Subst σ (_++_) _)

def vt : VR := ⟨"term", 0⟩
def vr : VR := ⟨"term", 1⟩
def vs : VR := ⟨"term", 2⟩
def vP : VR := ⟨"wff", 0⟩
def vQ : VR := ⟨"wff", 1⟩
def vx : VR := ⟨"set", 0⟩

def axs (s : Statement) : Prop := s ∈ [
  ⟨Context.mk' [] [], ("term", ze)⟩,
  ⟨Context.mk' [] [], ("term", pl vt vr)⟩,
  ⟨Context.mk' [] [], ("wff", eq vt vr)⟩,
  ⟨Context.mk' [] [], ("wff", im vP vQ)⟩,
  ⟨Context.mk' [] [], ("wff", al vx vP)⟩,
  ⟨Context.mk' [] [], ("|-", im (eq vt vr) (im (eq vt vs) (eq vr vs)))⟩,
  ⟨Context.mk' [] [], ("|-", eq (pl vt ze) vt)⟩,
  ⟨Context.mk' [] [("|-", vP), ("|-", im vP vQ)], ("|-", vQ)⟩,
  ⟨Context.mk' [(vx, vP)] [], ("|-", im vP (al vx vP))⟩
]

abbrev Provable := Metamath.Provable axs
abbrev Typed := Metamath.Typed axs

instance tze : Typed "term" ze :=
  ⟨fun _Γ => (Provable.ax_self axs (.head _) sorry).thm (subst.ok.nil sorry) DJ_nil HH_nil⟩

instance tpl {t r} [Typed "term" t] [Typed "term" r] : Typed "term" (pl t r) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vt, t), (vr, r)]) vt t := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vt, t), (vr, r)]) vr r := ⟨List.append_nil _⟩
    (Provable.ax_self axs (.tail _ <| .head _) sorry).thm
      (subst.ok.cons vt t.ty <| subst.ok.cons vr r.ty (subst.ok.nil sorry))
      DJ_nil HH_nil⟩

instance weq {t r} [Typed "term" t] [Typed "term" r] : Typed "wff" (eq t r) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vt, t), (vr, r)]) vt t := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vt, t), (vr, r)]) vr r := ⟨List.append_nil _⟩
    (Provable.ax_self axs (List.get_mem _ ⟨2, by decide⟩) sorry).thm
      (subst.ok.cons vt t.ty <| subst.ok.cons vr r.ty (subst.ok.nil sorry))
      DJ_nil HH_nil⟩

instance wim {P Q} [Typed "wff" P] [Typed "wff" Q] : Typed "wff" (im P Q) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vP, P), (vQ, Q)]) vP P := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q := ⟨List.append_nil _⟩
    (Provable.ax_self axs (List.get_mem _ ⟨3, by decide⟩) sorry).thm
      (subst.ok.cons vP P.ty <| subst.ok.cons vQ Q.ty (subst.ok.nil sorry))
      DJ_nil HH_nil⟩

instance wal {x P} [Typed "set" x] [Typed "wff" P] : Typed "wff" (al x P) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vx, x), (vP, P)]) vx x := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vx, x), (vP, P)]) vP P := ⟨List.append_nil _⟩
    (Provable.ax_self axs (List.get_mem _ ⟨4, by decide⟩) sorry).thm
      (subst.ok.cons vx x.ty <| subst.ok.cons vP P.ty (subst.ok.nil sorry))
      DJ_nil HH_nil⟩

theorem a1 {Γ t r s} [Typed "term" t] [Typed "term" r] [Typed "term" s] :
    Provable Γ ("|-", im (eq t r) (im (eq t s) (eq r s))) :=
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vt t := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vr r := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vs s := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨5, by decide⟩) sorry).thm
    (subst.ok.cons vt t.ty <| subst.ok.cons vr r.ty <| subst.ok.cons vs s.ty (subst.ok.nil sorry))
    DJ_nil HH_nil

theorem a2 {Γ t} [Typed "term" t] : Provable Γ ("|-", eq (pl t ze) t) :=
  have : Subst (subst_of [(vt, t)]) vt t := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨6, by decide⟩) sorry).thm
    (subst.ok.cons vt t.ty (subst.ok.nil sorry))
    DJ_nil HH_nil

theorem mp {Γ P Q} [Typed "wff" P] [Typed "wff" Q]
    (min : Provable Γ ("|-", P))
    (maj : Provable Γ ("|-", im P Q)) :
    Provable Γ ("|-", Q) :=
  have : Subst (subst_of [(vP, P), (vQ, Q)]) vP P := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨7, by decide⟩) sorry).thm
    (subst.ok.cons vP P.ty <| subst.ok.cons vQ Q.ty (subst.ok.nil sorry))
    DJ_nil (HH_cons min <| HH_cons maj HH_nil)

theorem ax5 {Γ x P} [Typed "set" x] [Typed "wff" P]
    (xp : x.disjoint Γ.dj P) :
    Provable Γ ("|-", im P (al x P)) :=
  have : Subst (subst_of [(vx, x), (vP, P)]) vx x := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vx, x), (vP, P)]) vP P := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨8, by decide⟩) sorry).thm
    (subst.ok.cons vx x.ty <| subst.ok.cons vP P.ty (subst.ok.nil sorry))
    (DJ_cons xp DJ_nil) HH_nil

theorem th1 {Γ t} [Typed "term" t] :
  Provable Γ ("|-", eq t t) := mp a2 (mp a2 a1)

end Demo
-/
end Metamath
