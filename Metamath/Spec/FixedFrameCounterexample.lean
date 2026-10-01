import Metamath.Spec.Completeness

/-!
# Metamath proofs in one fixed frame are incomplete for the declarative semantics

Mario Carneiro's declarative semantics judges a stored statement with unlimited
dummy variables, each disjoint from every other variable. A Metamath proof uses
the variables and `$d` statements of one extended frame. This module gives two
well-formed databases showing that both kinds of optional statements of the
Metamath book (§4.2.7) are needed:

1. **A missing dummy variable.**
   ```text
   $c |- wff c $.
   ${ $v x $.  wx $f wff x $.  ha $e wff x $.  ax-A $a |- c $. $}
   thm $p |- c $= ? $.
   ```
   `|- c` is declaratively provable (apply `ax-A` with `x := y` for a fresh
   `y`), but at the theorem's frame no proof exists: nothing of typecode `wff`
   is available (`not_specProvable_thm`). With one optional hypothesis
   `wy $f wff y $.` a proof exists (`specProvable_thm_with_dummy`).

2. **A missing `$d` statement.**
   ```text
   $c |- wff $.
   ${ $v x y $.  wx $f wff x $.  wy $f wff y $.  hx $e wff x $.  $d x y $.
      ax-B $a |- y $. $}
   ${ $v z $.  wz $f wff z $.  thm $p |- z $= ? $. $}
   ```
   `|- z` is declaratively provable (apply `ax-B` with `x := d`, `y := z` for a
   fresh `d`, disjoint from `z`), but no extended frame without `$d` statements
   has a proof (`not_specProvable_of_no_dv`); some extended frame with an optional
   `$d` statement has one (`exists_extendedFrame_with_dv`).
-/

namespace Metamath.Spec.FixedFrameCounterexample

open Metamath.Spec.Equivalence
open Metamath.Spec.StoredStatement (statementOfFrame)
open Metamath.Spec.Completeness
open Metamath.Spec.Bridge (DeclarativeVR DeclarativeFormula)

/-- `Metamath.Formula` is a `def` over `CN × Expr`. -/
local instance : DecidableEq Metamath.Formula :=
  inferInstanceAs (DecidableEq (Metamath.CN × Metamath.Expr))

def wffConstant : Constant := ⟨"wff"⟩

def turnstileConstant : Constant := ⟨"|-"⟩

/-! ## 1. A missing dummy variable -/

/-- Constants of the first database: `|-`, `wff`, `c`. -/
def counterexampleConstants : ConstSet :=
  fun s => s = "|-" ∨ s = "wff" ∨ s = "c"

def xVariable : Variable := ⟨"x"⟩

/-- The essential hypothesis `wff x`. -/
def essentialWffX : Expr := ⟨wffConstant, ["x"]⟩

/-- The conclusion `|- c`. -/
def conclusionC : Expr := ⟨turnstileConstant, ["c"]⟩

/-- The stored frame of `ax-A`: `wff x` floating, `wff x` essential. -/
def axiomFrame : Frame :=
  ⟨[.floating wffConstant xVariable, .essential essentialWffX], []⟩

/-- The frame of `thm`: the scope of `x` has closed. -/
def emptyFrame : Frame := ⟨[], []⟩

/-- The database holding exactly `ax-A`. -/
def counterexampleDatabase : Database :=
  fun l => if l = "ax-A" then some (axiomFrame, conclusionC) else none

/-- The image of `x` under the variable map of `axiomFrame`. -/
def xVR : DeclarativeVR := ⟨"wff", 0⟩

/-- A variable that no frame of the database declares. -/
def freshVR : DeclarativeVR := ⟨"wff", 37⟩

/-- The declarative formula `|- c`; it mentions no variable. -/
def target : DeclarativeFormula := ("|-", [Metamath.Sym.const "c"])

/-- `ax-A` as a declarative statement. -/
noncomputable def axiomStatement : Metamath.Statement :=
  ⟨frameToContext axiomFrame, exprToFormula (varMapOfFrame axiomFrame) conclusionC⟩

theorem database_entries {l : Label} {fr : Frame} {e : Expr}
    (hlookup : counterexampleDatabase l = some (fr, e)) :
    fr = axiomFrame ∧ e = conclusionC := by
  simp only [counterexampleDatabase] at hlookup
  split at hlookup
  · exact ⟨(congrArg Prod.fst (Option.some.inj hlookup)).symm,
      (congrArg Prod.snd (Option.some.inj hlookup)).symm⟩
  · exact nomatch hlookup

theorem varMapOfFrame_emptyFrame : varMapOfFrame emptyFrame = [] := rfl

theorem axiomStatement_fmla_eq : axiomStatement.fmla = target := by decide

theorem axiomStatement_hyps_eq :
    axiomStatement.ctx.hyps =
      [(("wff" : Metamath.CN), [Metamath.Sym.var xVR]),
       (("wff" : Metamath.CN), [Metamath.Sym.var xVR])] := by rfl

theorem axiomStatement_vars_eq : axiomStatement.vars = [xVR, xVR] := by decide

theorem axiomFrame_vars_eq : axiomFrame.vars = [xVariable] := by decide

theorem axiomStatement_dj_eq : axiomStatement.ctx.dj = Metamath.DJ.mk' [] := rfl

theorem axiomStatement_dj_not {a b : DeclarativeVR} : ¬ axiomStatement.ctx.dj a b := by
  rw [axiomStatement_dj_eq]
  rintro ⟨-, h | h⟩ <;> exact nomatch h

theorem axiomStatement_mem : dbToAxioms counterexampleDatabase axiomStatement :=
  ⟨"ax-A", axiomFrame, conclusionC, by simp [counterexampleDatabase], rfl, rfl⟩

/-- The substitution sending every variable to the fresh variable. -/
def freshSubstitution : DeclarativeVR → Metamath.Expr :=
  fun _ => [Metamath.Sym.var freshVR]

/-- `|- c` is declaratively provable in the frame of `thm`. -/
theorem declarative_provable_target :
    Metamath.Provable (dbToAxioms counterexampleDatabase) (frameToContext emptyFrame) target := by
  have h :=
    Metamath.Provable.ax (axs := dbToAxioms counterexampleDatabase)
      (Γ := frameToContext emptyFrame) (σ := freshSubstitution)
      (ax := axiomStatement) axiomStatement_mem
      (fun _ _ hab => (axiomStatement_dj_not hab).elim)
      (by
        intro hyp hmem
        rw [axiomStatement_hyps_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var freshVR
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var freshVR
        exact nomatch hmem)
      (by
        intro v hmem
        rw [axiomStatement_vars_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var freshVR
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var freshVR
        exact nomatch hmem)
  have hfmla : axiomStatement.fmla.subst freshSubstitution = target := by
    rw [axiomStatement_fmla_eq]
    rfl
  exact hfmla ▸ h

theorem exprToFormula_conclusionC_emptyFrame :
    exprToFormula (varMapOfFrame emptyFrame) conclusionC = target := by decide

/-- The stored statement of `thm` is declaratively provable. -/
theorem statementProvable_thm :
    (statementOfFrame emptyFrame conclusionC).Provable (dbToAxioms counterexampleDatabase) := by
  apply Metamath.Statement.Provable'.of
  change Metamath.Provable _ (frameToContext emptyFrame)
    (exprToFormula (varMapOfFrame emptyFrame) conclusionC)
  rw [exprToFormula_conclusionC_emptyFrame]
  exact declarative_provable_target

/-- Every conclusion of an assertion of the database has typecode `|-`. -/
theorem axiom_conclusion_turnstile {ax : Metamath.Statement}
    (hax : dbToAxioms counterexampleDatabase ax) (σ : DeclarativeVR → Metamath.Expr) :
    (ax.fmla.subst σ).1 = "|-" := by
  obtain ⟨_, _, _, hlookup, -, hfmla⟩ := hax
  obtain ⟨rfl, rfl⟩ := database_entries hlookup
  rw [hfmla]
  rfl

/-- In the frame of `thm`, nothing of typecode `wff` is derivable. -/
theorem no_frameDerivable_wff {e : Metamath.Expr} :
    ¬ FrameDerivable counterexampleDatabase emptyFrame ("wff", e) := by
  intro h
  generalize hf : ((("wff" : Metamath.CN), e) : DeclarativeFormula) = f at h
  cases h with
  | hyp g hmem => exact nomatch hmem
  | var v hsupp =>
      obtain ⟨_, hfind⟩ := hsupp
      rw [varMapOfFrame_emptyFrame] at hfind
      simp [findVar] at hfind
  | ax σ hax _ _ _ =>
      have h1 := congrArg Prod.fst hf
      rw [axiom_conclusion_turnstile hax σ] at h1
      have h2 : ("wff" : Metamath.CN) = "|-" := h1
      exact absurd h2 (by decide)

/-- In the frame of `thm`, `|- c` is not derivable. -/
theorem not_frameDerivable_target :
    ¬ FrameDerivable counterexampleDatabase emptyFrame target := by
  intro h
  generalize hf : target = f at h
  cases h with
  | hyp g hmem => exact nomatch hmem
  | var v _ =>
      have h1 := congrArg Prod.snd hf
      simp only [target, Metamath.VR.vhyp] at h1
      injection h1 with h2 _
      exact Metamath.Sym.noConfusion h2
  | @ax σ ax hax _ hhyps _ =>
      obtain ⟨_, _, _, hlookup, hctx, -⟩ := hax
      obtain ⟨rfl, rfl⟩ := database_entries hlookup
      have hbase : (("wff" : Metamath.CN), [Metamath.Sym.var xVR]) ∈
          (frameToContext axiomFrame).hyps := by
        rw [show (frameToContext axiomFrame).hyps = _ from axiomStatement_hyps_eq]
        exact List.Mem.head _
      have hin : (("wff" : Metamath.CN), [Metamath.Sym.var xVR]) ∈ ax.ctx.hyps := by
        rw [hctx]
        exact hbase
      exact no_frameDerivable_wff (hhyps _ hin)

theorem wellFormed_counterexampleDatabase :
    WellFormedDatabaseStrong counterexampleDatabase counterexampleConstants := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro l fr e hlookup
    obtain ⟨rfl, rfl⟩ := database_entries hlookup
    constructor
    · intro s hs
      simp only [conclusionC] at hs
      rcases List.mem_singleton.mp hs with rfl
      exact Or.inr (Or.inr (Or.inr rfl))
    · intro h hmem
      simp only [axiomFrame, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · trivial
      · intro s hs
        simp only [essentialWffX] at hs
        rcases List.mem_singleton.mp hs with rfl
        exact Or.inl (by rw [axiomFrame_vars_eq]; exact List.Mem.head _)
  · intro l fr e hlookup
    obtain ⟨rfl, -⟩ := database_entries hlookup
    intro v hv
    rw [axiomFrame_vars_eq] at hv
    rcases List.mem_singleton.mp hv with rfl
    rintro (h | h | h) <;> exact absurd h (by decide)
  · intro l fr e hlookup
    obtain ⟨rfl, -⟩ := database_entries hlookup
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro c c' v hc hc'
      simp only [axiomFrame, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
      rcases hc with hc | hc <;> rcases hc' with hc' | hc'
      · injection hc with hc1 _
        injection hc' with hc1' _
        rw [hc1, hc1']
      · exact nomatch hc'
      · exact nomatch hc
      · exact nomatch hc
    · unfold FloatVarNoDup
      decide
    · intro v w hvw
      exact nomatch hvw
    · intro v hvv
      exact nomatch hvv

theorem emptyFrame_wellFormed : FrameWellFormed emptyFrame ∧ DVWellFormed emptyFrame := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro c c' v hc
    exact nomatch hc
  · unfold FloatVarNoDup
    decide
  · intro v w hvw
    exact nomatch hvw
  · intro v hvv
    exact nomatch hvv

theorem emptyFrame_varsDisjointConsts :
    FrameVarsDisjointConsts counterexampleConstants emptyFrame :=
  fun _ hv => nomatch hv

/-- **No proof in the fixed frame.** `thm` has no Metamath proof in its own
frame, although its stored statement is declaratively provable. -/
theorem not_specProvable_thm : ¬ Spec.Provable counterexampleDatabase emptyFrame conclusionC := by
  intro h
  have hsupp := operational_to_frameDerivable wellFormed_counterexampleDatabase
    emptyFrame_varsDisjointConsts h
  rw [exprToFormula_conclusionC_emptyFrame] at hsupp
  exact not_frameDerivable_target hsupp

/-- At one fixed frame, declarative derivability does not imply frame
derivability, even for a well-formed database, a well-formed frame and a
conclusion without variables. -/
theorem declarative_not_conservative_at_fixed_frame :
    ¬ ∀ (Γ : Database) (consts : ConstSet) (fr : Frame) (fmla : DeclarativeFormula),
        WellFormedDatabaseStrong Γ consts → FrameWellFormed fr → DVWellFormed fr →
        fmla.2.vars = [] →
        Metamath.Provable (dbToAxioms Γ) (frameToContext fr) fmla →
        FrameDerivable Γ fr fmla := by
  intro h
  exact not_frameDerivable_target
    (h counterexampleDatabase counterexampleConstants emptyFrame target
      wellFormed_counterexampleDatabase emptyFrame_wellFormed.1 emptyFrame_wellFormed.2
      rfl declarative_provable_target)

def dummyVariable : Variable := ⟨"y"⟩

/-- The frame of `thm` extended by the optional hypothesis `wff y`. -/
def dummyFrame : Frame := ⟨[.floating wffConstant dummyVariable], []⟩

/-- The image of `y` under the variable map of `dummyFrame`. -/
def dummyVR : DeclarativeVR := ⟨"wff", 0⟩

theorem findVar_dummyFrame : findVar (varMapOfFrame dummyFrame) dummyVR = some dummyVariable := by
  decide

theorem frameDerivable_target_with_dummy :
    FrameDerivable counterexampleDatabase dummyFrame target := by
  have h :=
    Derivable.ax (axs := dbToAxioms counterexampleDatabase) (T := FrameDeclared dummyFrame)
      (Γ := frameToContext dummyFrame)
      (σ := fun _ => [Metamath.Sym.var dummyVR]) (ax := axiomStatement)
      axiomStatement_mem
      (fun _ _ hab => (axiomStatement_dj_not hab).elim)
      (by
        intro hyp hmem
        rw [axiomStatement_hyps_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Derivable.var dummyVR ⟨dummyVariable, findVar_dummyFrame⟩
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Derivable.var dummyVR ⟨dummyVariable, findVar_dummyFrame⟩
        exact nomatch hmem)
      (by
        intro v hmem
        rw [axiomStatement_vars_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Derivable.var dummyVR ⟨dummyVariable, findVar_dummyFrame⟩
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Derivable.var dummyVR ⟨dummyVariable, findVar_dummyFrame⟩
        exact nomatch hmem)
  have hfmla : axiomStatement.fmla.subst (fun _ => [Metamath.Sym.var dummyVR]) = target := by
    rw [axiomStatement_fmla_eq]
    rfl
  exact hfmla ▸ h

theorem dummyFrame_extendedFrame :
    ExtendedFrame counterexampleConstants emptyFrame dummyFrame where
  wellFormed := by
    refine ⟨?_, ?_⟩
    · intro c c' v hc hc'
      simp only [dummyFrame, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
      injection hc with hc1 _
      injection hc' with hc1' _
      rw [hc1, hc1']
    · unfold FloatVarNoDup
      decide
  hyps_mem := fun _ hh => nomatch hh
  optional_hyp := by
    intro h hh _
    simp only [dummyFrame, List.mem_cons, List.not_mem_nil, or_false] at hh
    subst hh
    refine ⟨wffConstant, dummyVariable, rfl, ?_, ?_⟩
    · intro hv
      exact nomatch hv
    · rintro (h | h | h) <;> exact absurd h (by decide)
  dv_mem := fun _ hp => nomatch hp
  optional_dv := fun _ hp => nomatch hp

/-- **A proof with one dummy variable.** In the extended frame with the
optional hypothesis `wff y`, `thm` has a Metamath proof. -/
theorem specProvable_thm_with_dummy :
    Spec.Provable counterexampleDatabase dummyFrame conclusionC := by
  apply frameDerivable_to_proofValid wellFormed_counterexampleDatabase
    dummyFrame_extendedFrame.wellFormed.2
    (dummyFrame_extendedFrame.varsDisjointConsts emptyFrame_varsDisjointConsts)
  have hfmla : exprToFormula (varMapOfFrame dummyFrame) conclusionC = target := by decide
  rw [hfmla]
  exact frameDerivable_target_with_dummy

theorem counterexampleConstants_finite :
    ∃ L : List String, ∀ s, counterexampleConstants s → s ∈ L :=
  ⟨["|-", "wff", "c"], by
    rintro s (rfl | rfl | rfl) <;> simp⟩

theorem thm_exprsInScope :
    FrameExprsInScope counterexampleConstants emptyFrame conclusionC := by
  refine ⟨?_, fun _ hh => nomatch hh⟩
  intro s hs
  simp only [conclusionC] at hs
  rcases List.mem_singleton.mp hs with rfl
  exact Or.inr (Or.inr (Or.inr rfl))

/-- The completeness theorem applies to `thm`: its premises hold, and both
sides are true. -/
example :
    ∃ fr', ExtendedFrame counterexampleConstants emptyFrame fr' ∧
      Spec.Provable counterexampleDatabase fr' conclusionC :=
  (statementProvable_iff_exists_extendedFrame wellFormed_counterexampleDatabase
    counterexampleConstants_finite emptyFrame_wellFormed.1 emptyFrame_varsDisjointConsts
    thm_exprsInScope).mp statementProvable_thm

/-! ## 2. A missing `$d` statement -/

/-- Constants of the second database: `|-`, `wff`. -/
def dvConstants : ConstSet := fun s => s = "|-" ∨ s = "wff"

def yVariable : Variable := ⟨"y"⟩

def zVariable : Variable := ⟨"z"⟩

/-- The stored frame of `ax-B`: `wff x`, `wff y`, `wff x` essential, `$d x y`. -/
def dvAxiomFrame : Frame :=
  ⟨[.floating wffConstant xVariable, .floating wffConstant yVariable,
    .essential essentialWffX], [(xVariable, yVariable)]⟩

/-- The conclusion `|- y` of `ax-B`. -/
def conclusionY : Expr := ⟨turnstileConstant, ["y"]⟩

/-- The database holding exactly `ax-B`. -/
def dvDatabase : Database :=
  fun l => if l = "ax-B" then some (dvAxiomFrame, conclusionY) else none

/-- The frame of `thm`: `wff z`. -/
def thmFrame : Frame := ⟨[.floating wffConstant zVariable], []⟩

/-- The conclusion `|- z` of `thm`. -/
def conclusionZ : Expr := ⟨turnstileConstant, ["z"]⟩

/-- The images of `x` and `y` under the variable map of `dvAxiomFrame`. -/
def xB : DeclarativeVR := ⟨"wff", 0⟩

def yB : DeclarativeVR := ⟨"wff", 1⟩

/-- The image of `z` under the variable map of `thmFrame`. -/
def zVR : DeclarativeVR := ⟨"wff", 0⟩

/-- A variable fresh for `thm`. -/
def dVR : DeclarativeVR := ⟨"wff", 7⟩

/-- The declarative formulas `|- y` over `ax-B` and `|- z` over `thm`. -/
def yTarget : DeclarativeFormula := ("|-", [Metamath.Sym.var yB])

def zTarget : DeclarativeFormula := ("|-", [Metamath.Sym.var zVR])

/-- `ax-B` as a declarative statement. -/
noncomputable def dvAxiomStatement : Metamath.Statement :=
  ⟨frameToContext dvAxiomFrame, exprToFormula (varMapOfFrame dvAxiomFrame) conclusionY⟩

theorem dvDatabase_entries {l : Label} {fr : Frame} {e : Expr}
    (hlookup : dvDatabase l = some (fr, e)) : fr = dvAxiomFrame ∧ e = conclusionY := by
  simp only [dvDatabase] at hlookup
  split at hlookup
  · exact ⟨(congrArg Prod.fst (Option.some.inj hlookup)).symm,
      (congrArg Prod.snd (Option.some.inj hlookup)).symm⟩
  · exact nomatch hlookup

theorem dvAxiomStatement_mem : dbToAxioms dvDatabase dvAxiomStatement :=
  ⟨"ax-B", dvAxiomFrame, conclusionY, by simp [dvDatabase], rfl, rfl⟩

theorem dvAxiomStatement_hyps_eq :
    dvAxiomStatement.ctx.hyps =
      [(("wff" : Metamath.CN), [Metamath.Sym.var xB]),
       (("wff" : Metamath.CN), [Metamath.Sym.var yB]),
       (("wff" : Metamath.CN), [Metamath.Sym.var xB])] := by rfl

theorem dvAxiomStatement_fmla_eq : dvAxiomStatement.fmla = yTarget := by decide

theorem dvAxiomStatement_vars_eq : dvAxiomStatement.vars = [yB, xB, yB, xB] := by decide

theorem dvAxiomStatement_dj_eq : dvAxiomStatement.ctx.dj = Metamath.DJ.mk' [(xB, yB)] := by
  rfl

theorem dvAxiomFrame_vars_eq : dvAxiomFrame.vars = [xVariable, yVariable] := by decide

theorem thmFrame_vars_eq : thmFrame.vars = [zVariable] := by decide

theorem statementOfFrame_thm_vars :
    (statementOfFrame thmFrame conclusionZ).vars = [zVR, zVR] := by decide

theorem statementOfFrame_thm_fmla : (statementOfFrame thmFrame conclusionZ).fmla = zTarget := by
  decide

/-- `ax-B` instantiated with `x := d` for a fresh `d`, and `y := z`. -/
def dvSubstitution : DeclarativeVR → Metamath.Expr :=
  fun v => if v = xB then [Metamath.Sym.var dVR] else [Metamath.Sym.var zVR]

/-- The stored statement of `thm` is declaratively provable: the fresh `d` is
disjoint from `z` in its `untrim` context. -/
theorem dv_statementProvable_thm :
    (statementOfFrame thmFrame conclusionZ).Provable (dbToAxioms dvDatabase) := by
  change Metamath.Provable (dbToAxioms dvDatabase)
    (statementOfFrame thmFrame conclusionZ).untrim.ctx
    (statementOfFrame thmFrame conclusionZ).fmla
  rw [statementOfFrame_thm_fmla]
  have h :=
    Metamath.Provable.ax (axs := dbToAxioms dvDatabase)
      (Γ := (statementOfFrame thmFrame conclusionZ).untrim.ctx) (σ := dvSubstitution)
      (ax := dvAxiomStatement) dvAxiomStatement_mem
      (by
        rw [dvAxiomStatement_dj_eq]
        intro a b hab
        -- the only pair is `x, y`, sent to `d` and `z`
        have hpair : (a = xB ∧ b = yB) ∨ (a = yB ∧ b = xB) := by
          obtain ⟨_, h | h⟩ := hab
          · left
            simpa using h
          · right
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
            exact ⟨h.2, h.1⟩
        have hdz : ((statementOfFrame thmFrame conclusionZ).untrim.ctx.dj) dVR zVR := by
          refine ⟨by decide, fun hd _ => ?_⟩
          rw [statementOfFrame_thm_vars] at hd
          exact absurd hd (by decide)
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · intro a' b' ha' hb'
          have ha'' : a' = dVR := by simpa [dvSubstitution, Metamath.Expr.mem] using ha'
          have hb'' : b' = zVR := by
            simpa [dvSubstitution, xB, yB, Metamath.Expr.mem] using hb'
          subst ha'' hb''
          exact hdz
        · intro a' b' ha' hb'
          have ha'' : a' = zVR := by
            simpa [dvSubstitution, xB, yB, Metamath.Expr.mem] using ha'
          have hb'' : b' = dVR := by simpa [dvSubstitution, Metamath.Expr.mem] using hb'
          subst ha'' hb''
          exact (statementOfFrame thmFrame conclusionZ).untrim.ctx.dj.symm hdz)
      (by
        intro hyp hmem
        rw [dvAxiomStatement_hyps_eq] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var dVR
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var zVR
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Metamath.Provable.var dVR
        exact nomatch hmem)
      (by
        intro v hmem
        rw [dvAxiomStatement_vars_eq] at hmem
        have hv : v = xB ∨ v = yB := by
          rcases List.mem_cons.mp hmem with h | hmem
          · exact Or.inr h
          rcases List.mem_cons.mp hmem with h | hmem
          · exact Or.inl h
          rcases List.mem_cons.mp hmem with h | hmem
          · exact Or.inr h
          rcases List.mem_cons.mp hmem with h | hmem
          · exact Or.inl h
          exact nomatch hmem
        rcases hv with rfl | rfl
        · exact Metamath.Provable.var dVR
        · exact Metamath.Provable.var zVR)
  have hfmla : dvAxiomStatement.fmla.subst dvSubstitution = zTarget := by
    rw [dvAxiomStatement_fmla_eq]
    rfl
  exact hfmla ▸ h

theorem wellFormed_dvDatabase : WellFormedDatabaseStrong dvDatabase dvConstants := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro l fr e hlookup
    obtain ⟨rfl, rfl⟩ := dvDatabase_entries hlookup
    constructor
    · intro s hs
      simp only [conclusionY] at hs
      rcases List.mem_singleton.mp hs with rfl
      exact Or.inl (by rw [dvAxiomFrame_vars_eq]; decide)
    · intro h hmem
      simp only [dvAxiomFrame, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · trivial
      · trivial
      · intro s hs
        simp only [essentialWffX] at hs
        rcases List.mem_singleton.mp hs with rfl
        exact Or.inl (by rw [dvAxiomFrame_vars_eq]; decide)
  · intro l fr e hlookup
    obtain ⟨rfl, -⟩ := dvDatabase_entries hlookup
    intro v hv
    rw [dvAxiomFrame_vars_eq] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> rintro (h | h) <;> exact absurd h (by decide)
  · intro l fr e hlookup
    obtain ⟨rfl, -⟩ := dvDatabase_entries hlookup
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have hconst : ∀ c v, Hyp.floating c v ∈ dvAxiomFrame.hyps → c = wffConstant := by
        intro c v h
        simp [dvAxiomFrame] at h
        rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
      intro c c' v hc hc'
      rw [hconst c v hc, hconst c' v hc']
    · unfold FloatVarNoDup
      decide
    · intro v w hvw
      simp only [dvAxiomFrame, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hvw
      obtain ⟨rfl, rfl⟩ := hvw
      rw [dvAxiomFrame_vars_eq]
      decide
    · intro v hvv
      simp only [dvAxiomFrame, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hvv
      obtain ⟨rfl, h⟩ := hvv
      exact absurd h (by decide)

theorem thmFrame_wellFormed : FrameWellFormed thmFrame := by
  refine ⟨?_, ?_⟩
  · intro c c' v hc hc'
    simp only [thmFrame, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    injection hc with hc1 _
    injection hc' with hc1' _
    rw [hc1, hc1']
  · unfold FloatVarNoDup
    decide

theorem thmFrame_varsDisjointConsts : FrameVarsDisjointConsts dvConstants thmFrame := by
  intro v hv
  rw [thmFrame_vars_eq] at hv
  rcases List.mem_singleton.mp hv with rfl
  rintro (h | h) <;> exact absurd h (by decide)

theorem dvConstants_finite : ∃ L : List String, ∀ s, dvConstants s → s ∈ L :=
  ⟨["|-", "wff"], by rintro s (rfl | rfl) <;> simp⟩

/-- Every conclusion of an assertion of the database has typecode `|-`. -/
theorem dv_axiom_conclusion_turnstile {ax : Metamath.Statement}
    (hax : dbToAxioms dvDatabase ax) (σ : DeclarativeVR → Metamath.Expr) :
    (ax.fmla.subst σ).1 = "|-" := by
  obtain ⟨_, _, _, hlookup, -, hfmla⟩ := hax
  obtain ⟨rfl, rfl⟩ := dvDatabase_entries hlookup
  rw [hfmla]
  rfl

/-- Every hypothesis of an extended frame of `thmFrame` is floating. -/
theorem floating_of_extendedFrame {fr' : Frame} (hext : ExtendedFrame dvConstants thmFrame fr')
    {h : Hyp} (hh : h ∈ fr'.hyps) : ∃ c w, h = .floating c w := by
  by_cases hin : h ∈ thmFrame.hyps
  · simp only [thmFrame, List.mem_cons, List.not_mem_nil, or_false] at hin
    exact ⟨_, _, hin⟩
  · obtain ⟨c, w, heq, _, _⟩ := hext.optional_hyp h hh hin
    exact ⟨c, w, heq⟩

/-- In an extended frame of `thmFrame`, a derivable formula of typecode `wff`
is a single variable. -/
theorem wff_is_variable {fr' : Frame} (hext : ExtendedFrame dvConstants thmFrame fr')
    {e : Metamath.Expr} (h : FrameDerivable dvDatabase fr' ("wff", e)) :
    ∃ a, e = [Metamath.Sym.var a] := by
  generalize hf : ((("wff" : Metamath.CN), e) : DeclarativeFormula) = f at h
  cases h with
  | hyp g hmem =>
      obtain ⟨h₀, hh₀, rfl⟩ := hyps_correspondence hmem
      obtain ⟨c, w, rfl⟩ := floating_of_extendedFrame hext hh₀
      have h2 := congrArg Prod.snd hf
      simp only [hypToDeclarativeFormula] at h2
      exact ⟨_, h2⟩
  | var v _ =>
      exact ⟨v, congrArg Prod.snd hf⟩
  | ax σ hax _ _ _ =>
      have h1 := congrArg Prod.fst hf
      rw [dv_axiom_conclusion_turnstile hax σ] at h1
      have h2 : ("wff" : Metamath.CN) = "|-" := h1
      exact absurd h2 (by decide)

/-- **The optional `$d` statements are needed.** No extended frame of
`thmFrame` without `$d` statements has a proof of `|- z`: every proof must
apply `ax-B` to two variables, which `$d x y` requires to be disjoint. -/
theorem not_specProvable_of_no_dv {fr' : Frame} (hext : ExtendedFrame dvConstants thmFrame fr')
    (hdv : fr'.dv = []) : ¬ Spec.Provable dvDatabase fr' conclusionZ := by
  intro hprov
  have hsupp := operational_to_frameDerivable wellFormed_dvDatabase
    (hext.varsDisjointConsts thmFrame_varsDisjointConsts) hprov
  -- The conclusion is `|- z'` for the image `z'` of `z` in `fr'`.
  have hz : Hyp.floating wffConstant zVariable ∈ fr'.hyps := hext.hyps_mem _ (List.Mem.head _)
  obtain ⟨z', hz', hz'type⟩ := findVR_of_float_typed hext.wellFormed.1 hz
  have hz'' : findVR (varMapOfFrame fr') ⟨"z"⟩ = some z' := hz'
  have hconcl : exprToFormula (varMapOfFrame fr') conclusionZ =
      (("|-" : Metamath.CN), [Metamath.Sym.var z']) := by
    simp [exprToFormula, exprToDeclarativeExpr, conclusionZ, turnstileConstant,
      toDeclarativeSym, hz'']
    rfl
  rw [hconcl] at hsupp
  generalize hf : ((("|-" : Metamath.CN), [Metamath.Sym.var z']) : DeclarativeFormula) = f
    at hsupp
  cases hsupp with
  | hyp g hmem =>
      -- a hypothesis `c w` with `c = |-` would give `w` two typecodes
      obtain ⟨h₀, hh₀, rfl⟩ := hyps_correspondence hmem
      obtain ⟨c, w, rfl⟩ := floating_of_extendedFrame hext hh₀
      obtain ⟨wVR, hwVR⟩ := findVR_of_float hh₀
      simp only [hypToDeclarativeFormula, hwVR, Prod.mk.injEq, List.cons.injEq,
        Metamath.Sym.var.injEq, and_true] at hf
      obtain ⟨hc, rfl⟩ := hf
      obtain ⟨c', hc', hc'type⟩ := mem_varMapOfFrame_sound_typed (findVR_mem_of_some hwVR)
      have hcc' : c' = c := hext.wellFormed.1 c' c w hc' hh₀
      subst hcc'
      rw [hz'type] at hc'type
      rw [← hc'type] at hc
      exact absurd hc (by decide)
  | var v _ =>
      simp only [Metamath.VR.vhyp, Prod.mk.injEq, List.cons.injEq, Metamath.Sym.var.injEq,
        and_true] at hf
      obtain ⟨htype, rfl⟩ := hf
      rw [hz'type] at htype
      exact absurd htype (by decide)
  | ax σ hax hdj hhyps _ =>
      obtain ⟨_, _, _, hlookup, hctx, -⟩ := hax
      obtain ⟨rfl, rfl⟩ := dvDatabase_entries hlookup
      have hmemx : (("wff" : Metamath.CN), [Metamath.Sym.var xB]) ∈
          (frameToContext dvAxiomFrame).hyps := by
        rw [show (frameToContext dvAxiomFrame).hyps = _ from dvAxiomStatement_hyps_eq]
        exact List.Mem.head _
      have hmemy : (("wff" : Metamath.CN), [Metamath.Sym.var yB]) ∈
          (frameToContext dvAxiomFrame).hyps := by
        rw [show (frameToContext dvAxiomFrame).hyps = _ from dvAxiomStatement_hyps_eq]
        exact List.Mem.tail _ (List.Mem.head _)
      have hsubst : ∀ v : DeclarativeVR,
          Metamath.Formula.subst σ (("wff" : Metamath.CN), [Metamath.Sym.var v]) =
            (("wff" : Metamath.CN), σ v) := fun v => by
        change (("wff" : Metamath.CN), List.append (σ v) []) = _
        exact congrArg (Prod.mk _) (List.append_nil (σ v))
      have hx := hhyps _ (hctx.symm ▸ hmemx)
      have hy := hhyps _ (hctx.symm ▸ hmemy)
      rw [hsubst] at hx hy
      obtain ⟨a, ha⟩ := wff_is_variable hext hx
      obtain ⟨b, hb⟩ := wff_is_variable hext hy
      have hxy : dvAxiomStatement.ctx.dj xB yB := by
        rw [dvAxiomStatement_dj_eq]
        exact ⟨by decide, Or.inl (List.Mem.head _)⟩
      have hab := hdj xB yB (hctx ▸ hxy) a b (by rw [ha]; exact List.Mem.head _)
        (by rw [hb]; exact List.Mem.head _)
      obtain ⟨_, hor⟩ := hab
      simp only [hdv, List.filterMap_nil, List.not_mem_nil, or_self] at hor

/-- **An extended frame with a `$d` statement proves `thm`.** The completeness
theorem gives an extended frame with a proof of `|- z`; by
`not_specProvable_of_no_dv`, it has an optional `$d` statement. -/
theorem exists_extendedFrame_with_dv :
    ∃ fr', ExtendedFrame dvConstants thmFrame fr' ∧ Spec.Provable dvDatabase fr' conclusionZ ∧
      fr'.dv ≠ [] := by
  obtain ⟨fr', hext, hprov⟩ :=
    exists_extendedFrame_of_statementProvable wellFormed_dvDatabase dvConstants_finite
      thmFrame_wellFormed thmFrame_varsDisjointConsts dv_statementProvable_thm
  exact ⟨fr', hext, hprov, fun hdv => not_specProvable_of_no_dv hext hdv hprov⟩

end Metamath.Spec.FixedFrameCounterexample
