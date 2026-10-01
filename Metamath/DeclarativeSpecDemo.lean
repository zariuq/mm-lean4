import Metamath.DeclarativeSpec

/-!
# Mario Carneiro's `Demo` section

A by-hand translation of `demo0.mm` into the declarative specification, with its proofs of
`|- t = t`. This is the `Demo` section of mm-lean4 (github.com/digama0/mm-lean4, commit `6778ca0`,
`Metamath/Translate.lean`), unchanged except for the type ascription `: List Statement` on the
axiom list, which Lean 4.33 needs to elaborate the membership.
-/

namespace Metamath

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

def axs (s : Statement) : Prop := s ∈ ([
  ⟨Context.mk' [] [], ("term", ze)⟩,
  ⟨Context.mk' [] [], ("term", pl vt vr)⟩,
  ⟨Context.mk' [] [], ("wff", eq vt vr)⟩,
  ⟨Context.mk' [] [], ("wff", im vP vQ)⟩,
  ⟨Context.mk' [] [], ("wff", al vx vP)⟩,
  ⟨Context.mk' [] [], ("|-", im (eq vt vr) (im (eq vt vs) (eq vr vs)))⟩,
  ⟨Context.mk' [] [], ("|-", eq (pl vt ze) vt)⟩,
  ⟨Context.mk' [] [("|-", vP), ("|-", im vP vQ)], ("|-", vQ)⟩,
  ⟨Context.mk' [(vx, vP)] [], ("|-", im vP (al vx vP))⟩
] : List Statement)

abbrev Provable := Metamath.Provable axs
abbrev Typed := Metamath.Typed axs

instance tze : Typed "term" ze :=
  ⟨fun _Γ => (Provable.ax_self axs (.head _)).thm subst.ok.nil DJ_nil HH_nil⟩

instance tpl {t r} [Typed "term" t] [Typed "term" r] : Typed "term" (pl t r) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vt, t), (vr, r)]) vt t := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vt, t), (vr, r)]) vr r := ⟨List.append_nil _⟩
    (Provable.ax_self axs (.tail _ <| .head _)).thm
      (subst.ok.cons vt t.ty <| subst.ok.cons vr r.ty subst.ok.nil)
      DJ_nil HH_nil⟩

instance weq {t r} [Typed "term" t] [Typed "term" r] : Typed "wff" (eq t r) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vt, t), (vr, r)]) vt t := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vt, t), (vr, r)]) vr r := ⟨List.append_nil _⟩
    (Provable.ax_self axs (List.get_mem _ ⟨2, by decide⟩)).thm
      (subst.ok.cons vt t.ty <| subst.ok.cons vr r.ty subst.ok.nil)
      DJ_nil HH_nil⟩

instance wim {P Q} [Typed "wff" P] [Typed "wff" Q] : Typed "wff" (im P Q) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vP, P), (vQ, Q)]) vP P := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q := ⟨List.append_nil _⟩
    (Provable.ax_self axs (List.get_mem _ ⟨3, by decide⟩)).thm
      (subst.ok.cons vP P.ty <| subst.ok.cons vQ Q.ty subst.ok.nil)
      DJ_nil HH_nil⟩

instance wal {x P} [Typed "set" x] [Typed "wff" P] : Typed "wff" (al x P) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vx, x), (vP, P)]) vx x := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vx, x), (vP, P)]) vP P := ⟨List.append_nil _⟩
    (Provable.ax_self axs (List.get_mem _ ⟨4, by decide⟩)).thm
      (subst.ok.cons vx x.ty <| subst.ok.cons vP P.ty subst.ok.nil)
      DJ_nil HH_nil⟩

theorem a1 {Γ t r s} [Typed "term" t] [Typed "term" r] [Typed "term" s] :
    Provable Γ ("|-", im (eq t r) (im (eq t s) (eq r s))) :=
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vt t := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vr r := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vs s := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨5, by decide⟩)).thm
    (subst.ok.cons vt t.ty <| subst.ok.cons vr r.ty <| subst.ok.cons vs s.ty subst.ok.nil)
    DJ_nil HH_nil

theorem a2 {Γ t} [Typed "term" t] : Provable Γ ("|-", eq (pl t ze) t) :=
  have : Subst (subst_of [(vt, t)]) vt t := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨6, by decide⟩)).thm
    (subst.ok.cons vt t.ty subst.ok.nil)
    DJ_nil HH_nil

theorem mp {Γ P Q} [Typed "wff" P] [Typed "wff" Q]
    (min : Provable Γ ("|-", P))
    (maj : Provable Γ ("|-", im P Q)) :
    Provable Γ ("|-", Q) :=
  have : Subst (subst_of [(vP, P), (vQ, Q)]) vP P := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨7, by decide⟩)).thm
    (subst.ok.cons vP P.ty <| subst.ok.cons vQ Q.ty subst.ok.nil)
    DJ_nil (HH_cons min <| HH_cons maj HH_nil)

theorem ax5 {Γ x P} [Typed "set" x] [Typed "wff" P]
    (xp : x.disjoint Γ.dj P) :
    Provable Γ ("|-", im P (al x P)) :=
  have : Subst (subst_of [(vx, x), (vP, P)]) vx x := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vx, x), (vP, P)]) vP P := ⟨List.append_nil _⟩
  (Provable.ax_self axs (List.get_mem _ ⟨8, by decide⟩)).thm
    (subst.ok.cons vx x.ty <| subst.ok.cons vP P.ty subst.ok.nil)
    (DJ_cons xp DJ_nil) HH_nil

theorem th1 {Γ t} [Typed "term" t] :
  Provable Γ ("|-", eq t t) := mp a2 (mp a2 a1)

end Demo

end Metamath
