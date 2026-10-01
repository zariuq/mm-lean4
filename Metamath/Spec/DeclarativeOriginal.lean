import Metamath.Spec.Derivable

/-!
# Mario Carneiro's original `ax` rule

In `Metamath.Provable`, the `ax` rule has two premises: the substituted
hypotheses of the referenced assertion, and a typing premise for each of its
variables `ax.vars`. Mario Carneiro's original rule has a single premise ranging
over the hypotheses and every variable (mm-lean4, github.com/digama0/mm-lean4, commit
`6778ca0`, `Metamath/Translate.lean`). This module states the original rule
verbatim (`Provable`) and proves the two equivalent when every assertion is
trimmed, i.e. its disjoint-variable relation only mentions its own variables
(`provable_iff`). Every assertion of `dbToAxioms Γ` is trimmed
(`Metamath.Spec.Equivalence.dbToAxioms_trimmed`).
-/

namespace Metamath.Spec.DeclarativeOriginal

/-- Mario Carneiro's original declarative provability. -/
inductive Provable (axs : Metamath.Statement → Prop) (Γ : Metamath.Context) :
    Metamath.Formula → Prop
  | hyp (h) : h ∈ Γ.hyps → Provable axs Γ h
  | var (v : Metamath.VR) : Provable axs Γ v
  | ax (σ) {ax} : axs ax → ax.ctx.dj.subst σ Γ.dj →
    (∀ h, h ∈ ax.ctx.hyps ∨ (∃ v : Metamath.VR, h = v) → Provable axs Γ (h.subst σ)) →
    Provable axs Γ (ax.fmla.subst σ)

/-- Original provability of a statement: provability in its `untrim` context. -/
def StatementProvable (axs : Metamath.Statement → Prop) (s : Metamath.Statement) : Prop :=
  Provable axs s.untrim.ctx s.fmla

/-- The original rule derives only what `Metamath.Provable` derives. -/
theorem provable_of {axs : Metamath.Statement → Prop} {Γ : Metamath.Context}
    {f : Metamath.Formula} (h : Provable axs Γ f) : Metamath.Provable axs Γ f := by
  induction h with
  | hyp f hf => exact .hyp f hf
  | var v => exact .var v
  | @ax σ ax hax hdj _ ih =>
      refine .ax σ hax hdj (fun h hh => ih h (Or.inl hh)) (fun v _ => ?_)
      have hv := ih (Metamath.VR.vhyp v) (Or.inr ⟨v, rfl⟩)
      rwa [Metamath.VR.vhyp_subst] at hv

/-- For trimmed assertions, the original rule derives everything
`Metamath.Provable` derives: outside the variables of the referenced assertion,
the substitution is replaced by the identity. -/
theorem of_provable {axs : Metamath.Statement → Prop}
    (htrim : ∀ a, axs a → a.trimmed) {Γ : Metamath.Context} {f : Metamath.Formula}
    (h : Metamath.Provable axs Γ f) : Provable axs Γ f := by
  induction h with
  | hyp f hf => exact .hyp f hf
  | var v => exact .var v
  | @ax σ ax hax hdj _ _ ih_h ih_v =>
      let τ : Metamath.VR → Metamath.Expr :=
        fun v => if v ∈ ax.vars then σ v else Metamath.VR.expr v
      have hτ : ∀ v ∈ ax.vars, τ v = σ v := fun _ hv => if_pos hv
      have hfmla : ax.fmla.subst τ = ax.fmla.subst σ :=
        Metamath.Formula.subst_congr fun v hv => hτ v (ax.mem_vars_of_fmla hv)
      rw [← hfmla]
      refine .ax τ hax ?_ ?_
      · intro x y hxy
        obtain ⟨hx, hy⟩ := htrim ax hax x y hxy
        rw [hτ x hx, hτ y hy]
        exact hdj x y hxy
      · rintro h (hh | ⟨v, rfl⟩)
        · rw [Metamath.Formula.subst_congr (f := h) fun v hv =>
            hτ v (ax.mem_vars_of_hyp hh hv)]
          exact ih_h h hh
        · rw [Metamath.VR.vhyp_subst]
          by_cases hv : v ∈ ax.vars
          · rw [hτ v hv]
            exact ih_v v hv
          · have hid : τ v = Metamath.VR.expr v := if_neg hv
            rw [hid]
            exact .var v

/-- For trimmed assertions, the original rule and `Metamath.Provable` agree. -/
theorem provable_iff {axs : Metamath.Statement → Prop}
    (htrim : ∀ a, axs a → a.trimmed) {Γ : Metamath.Context} {f : Metamath.Formula} :
    Provable axs Γ f ↔ Metamath.Provable axs Γ f :=
  ⟨provable_of, of_provable htrim⟩

theorem statementProvable_iff {axs : Metamath.Statement → Prop}
    (htrim : ∀ a, axs a → a.trimmed) {s : Metamath.Statement} :
    StatementProvable axs s ↔ s.Provable axs :=
  provable_iff htrim

end Metamath.Spec.DeclarativeOriginal
