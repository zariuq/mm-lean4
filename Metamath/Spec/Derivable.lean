import Metamath.DeclarativeSpec

/-!
# Pre-statements and their closure (Metamath book, Appendix C)

The Metamath book (Megill and Wheeler, Appendix C.2.4–C.2.5) defines provability in two layers.

| Book | Lean |
|---|---|
| pre-statement ⟨D, T, H, A⟩ | a context `⟨H, D⟩`, a set `T : VR → Prop` of variables with variable-type hypotheses, and a formula `A` |
| closure of ⟨D, T, H, ·⟩ | `Derivable axs T ⟨H, D⟩` |
| a pre-statement is provable if A is in its closure | `Derivable axs T ⟨H, D⟩ A` |
| the reduct of a pre-statement | its hypotheses and the `$d` pairs among the variables of H ∪ {A} |
| a statement is provable if it is the reduct of a provable pre-statement | `Statement.provable_iff_exists_extension` (reduct `s.trim`) |

`Derivable` is Mario Carneiro's `Provable` with one change: a variable leaf `v` requires `T v`.
`Provable` is the case where every variable has a variable-type hypothesis
(`provable_iff_derivable`), and `Statement.Provable`, which reads a statement in its `untrim`
context, is provability of the largest pre-statement whose reduct is that statement. The book's
definition, "the reduct of some provable pre-statement", is therefore a theorem about Mario's
definition (`Statement.provable_iff_exists_extension`): a statement `s` is provable iff some
provable pre-statement has the reduct `s.trim`, which is `s` itself when `s.trimmed`. Any one derivation uses finitely many
variables (`Derivable.exists_finite_vars`), so finitely many dummy variables suffice
(`Statement.provable_iff_exists_finite_extension`); the book notes that no bound works for all
statements.

The book's axiomatic statements are reducts: their `$d` pairs only mention their own variables.
Here this is the hypothesis `∀ a, axs a → a.trimmed`. Hypotheses of the form `(c, [v])` may occur
both in the hypothesis list and as members of `T`; the book's closure contains `T ∪ H`, so the
duplication does not change it.
-/

namespace Metamath

/-- The closure of the pre-statement with context `Γ` (hypotheses and `$d` pairs) and variables
`T` (Metamath book C.2.5), over the axiomatic statements `axs`. `T` is the set of variables with a
variable-type hypothesis. -/
inductive Derivable (axs : Statement → Prop) (T : VR → Prop) (Γ : Context) : Formula → Prop
  /-- Use a hypothesis -/
  | hyp (h) : h ∈ Γ.hyps → Derivable axs T Γ h
  /-- Use a variable-type hypothesis -/
  | var (v : VR) : T v → Derivable axs T Γ v
  /-- Apply an axiomatic statement with substitution `σ` -/
  | ax (σ) {ax} : axs ax → ax.ctx.dj.subst σ Γ.dj →
    (∀ h ∈ ax.ctx.hyps, Derivable axs T Γ (h.subst σ)) →
    (∀ v ∈ ax.vars, Derivable axs T Γ (v.type, σ v)) →
    Derivable axs T Γ (ax.fmla.subst σ)

theorem Derivable.mono {axs₁ axs₂ : Statement → Prop} (haxs : ∀ a, axs₁ a → axs₂ a)
    {T₁ T₂ : VR → Prop} (hT : ∀ v, T₁ v → T₂ v) {Γ₁ Γ₂ : Context} (hΓ : Γ₁ ≤ Γ₂) {f : Formula}
    (pr : Derivable axs₁ T₁ Γ₁ f) : Derivable axs₂ T₂ Γ₂ f := by
  induction pr with
  | hyp h hh => exact .hyp h (hΓ.1 _ hh)
  | var v hv => exact .var v (hT v hv)
  | ax σ ha hdj _ _ ih_h ih_v =>
      exact .ax σ (haxs _ ha) (hdj.mono (DJ.refl _) hΓ.2) ih_h ih_v

/-- Mario's `Provable` is derivability when every variable has a variable-type hypothesis. -/
theorem provable_iff_derivable {axs : Statement → Prop} {Γ : Context} {f : Formula} :
    Provable axs Γ f ↔ Derivable axs (fun _ => True) Γ f := by
  constructor
  · intro h
    induction h with
    | hyp h hh => exact .hyp h hh
    | var v => exact .var v trivial
    | ax σ ha hdj _ _ ih_h ih_v => exact .ax σ ha hdj ih_h ih_v
  · intro h
    induction h with
    | hyp h hh => exact .hyp h hh
    | var v _ => exact .var v
    | ax σ ha hdj _ _ ih_h ih_v => exact .ax σ ha hdj ih_h ih_v

/-! ## Variables -/

theorem Expr.mem_vars_iff {v : VR} {e : Expr} : v ∈ e.vars ↔ v ∈' e := by
  change v ∈ e.vars ↔ Sym.var v ∈ e
  induction e with
  | nil =>
      change v ∈ ([] : List VR) ↔ Sym.var v ∈ ([] : List Sym)
      simp
  | cons s e ih =>
      cases s with
      | const c =>
          simp only [Expr.vars]
          constructor
          · intro h
            exact List.Mem.tail _ (ih.mp h)
          · intro h
            cases h with
            | tail _ h => exact ih.mpr h
      | var w =>
          simp only [Expr.vars, List.mem_cons]
          constructor
          · rintro (rfl | h)
            · exact Or.inl rfl
            · exact Or.inr (ih.mp h)
          · intro h
            rcases h with h | h
            · cases h
              exact Or.inl rfl
            · exact Or.inr (ih.mpr h)

theorem Statement.mem_vars_of_fmla (s : Statement) {v : VR} (h : v ∈' s.fmla.2) : v ∈ s.vars :=
  List.mem_flatMap.mpr ⟨s.fmla, List.Mem.head _, Expr.mem_vars_iff.mpr h⟩

theorem Statement.mem_vars_of_hyp (s : Statement) {f : Formula} (hf : f ∈ s.ctx.hyps) {v : VR}
    (h : v ∈' f.2) : v ∈ s.vars :=
  List.mem_flatMap.mpr ⟨f, List.Mem.tail _ hf, Expr.mem_vars_iff.mpr h⟩

theorem Formula.subst_fst (σ : VR → Expr) (f : Formula) : (f.subst σ).1 = f.1 := by
  cases f
  rfl

theorem Formula.subst_snd (σ : VR → Expr) (f : Formula) : (f.subst σ).2 = f.2.subst σ := by
  cases f
  rfl

theorem VR.vhyp_subst (σ : VR → Expr) (v : VR) : (VR.vhyp v).subst σ = (v.type, σ v) := by
  change (v.type, List.append (σ v) []) = (v.type, σ v)
  exact congrArg (Prod.mk v.type) (List.append_nil (σ v))

/-- A substitution only matters on the variables of the expression. -/
theorem Expr.subst_congr {σ σ' : VR → Expr} :
    ∀ {e : Expr}, (∀ v, v ∈' e → σ v = σ' v) → e.subst σ = e.subst σ'
  | [], _ => rfl
  | .const c :: e, h =>
      congrArg (Sym.const c :: ·) (Expr.subst_congr fun v hv => h v (List.Mem.tail _ hv))
  | .var w :: e, h => by
      change σ w ++ Expr.subst σ e = σ' w ++ Expr.subst σ' e
      rw [h w (List.Mem.head _), Expr.subst_congr fun v hv => h v (List.Mem.tail _ hv)]

theorem Formula.subst_congr {σ σ' : VR → Expr} {f : Formula} (h : ∀ v, v ∈' f.2 → σ v = σ' v) :
    f.subst σ = f.subst σ' := by
  obtain ⟨c, e⟩ := f
  exact congrArg (fun x => ((c, x) : Formula)) (Expr.subst_congr h)

/-- The variables of a derived formula have variable-type hypotheses, when those of the hypotheses
do (the book's condition V(H ∪ {A}) ⊆ V(T)). -/
theorem Derivable.vars_mem {axs : Statement → Prop} {T : VR → Prop} {Γ : Context}
    (hH : ∀ h ∈ Γ.hyps, ∀ v, v ∈' h.2 → T v) {f : Formula} (pr : Derivable axs T Γ f) :
    ∀ v, v ∈' f.2 → T v := by
  induction pr with
  | hyp h hh => exact hH h hh
  | var w hw =>
      intro v hv
      have : v = w := Sym.var.inj (List.mem_singleton.mp hv)
      exact this ▸ hw
  | @ax σ ax _ _ _ _ _ ih_v =>
      intro v hv
      rw [Formula.subst_snd] at hv
      obtain ⟨b, hb, hvb⟩ := Expr.mem_subst hv
      exact ih_v b (ax.mem_vars_of_fmla hb) v hvb

/-! ## Substitution -/

/-- Substitution through a derivation (Mario's `Provable.trans'`, restricted to the variables of
`T`): only the `$d` pairs among variables of `T` are consulted, because an axiomatic statement's
`$d` pairs mention its own variables, whose images are derived formulas. -/
theorem Derivable.subst {axs : Statement → Prop} (htrim : ∀ a, axs a → a.trimmed)
    {T T' : VR → Prop} {Γ Γ' : Context} (hH : ∀ h ∈ Γ.hyps, ∀ v, v ∈' h.2 → T v)
    (σ : VR → Expr) {f : Formula} (pr : Derivable axs T Γ f)
    (dj : (Γ.dj.trim T).subst σ Γ'.dj)
    (hh : ∀ h ∈ Γ.hyps, Derivable axs T' Γ' (h.subst σ))
    (hv : ∀ v, T v → Derivable axs T' Γ' (v.type, σ v)) :
    Derivable axs T' Γ' (f.subst σ) := by
  induction pr with
  | hyp h hmem => exact hh h hmem
  | var v hT =>
      rw [VR.vhyp_subst]
      exact hv v hT
  | @ax σ' a ha dj' _ hvars ih_h ih_v =>
      rw [← Formula.subst_tr]
      refine .ax (subst.trans σ' σ) ha ?_ ?_ ?_
      · intro x y hxy c d hc hd
        obtain ⟨e, he, hce⟩ := Expr.mem_subst hc
        obtain ⟨g, hg, hdg⟩ := Expr.mem_subst hd
        obtain ⟨hx, hy⟩ := htrim a ha x y hxy
        have hTe : T e := (hvars x hx).vars_mem hH e he
        have hTg : T g := (hvars y hy).vars_mem hH g hg
        exact dj e g ⟨dj' x y hxy e g he hg, hTe, hTg⟩ c d hce hdg
      · intro h hmem
        rw [Formula.subst_tr]
        exact ih_h h hmem
      · intro v hmem
        exact ih_v v hmem

/-- Only the `$d` pairs among variables of `T` matter. -/
theorem Derivable.trim_dj {axs : Statement → Prop} (htrim : ∀ a, axs a → a.trimmed)
    {T : VR → Prop} {Γ : Context} (hH : ∀ h ∈ Γ.hyps, ∀ v, v ∈' h.2 → T v) {f : Formula}
    (pr : Derivable axs T Γ f) : Derivable axs T ⟨Γ.hyps, Γ.dj.trim T⟩ f := by
  have h := pr.subst htrim hH VR.expr (Γ' := ⟨Γ.hyps, Γ.dj.trim T⟩) (T' := T)
    (fun a b hab c d hc hd => by
      have hca : c = a := Sym.var.inj (List.mem_singleton.mp hc)
      have hdb : d = b := Sym.var.inj (List.mem_singleton.mp hd)
      subst hca hdb
      exact hab)
    (fun h hmem => by
      rw [Formula.subst_id]
      exact .hyp h hmem)
    (fun v hv => .var v hv)
  rwa [Formula.subst_id] at h

/-- Substitution of a variable for each variable. -/
def renameSubst (ρ : VR → VR) : VR → Expr := fun v => [Sym.var (ρ v)]

/-- Renaming the variables of a derivation: variables of `T` go to variables of `T'`, and `$d`
pairs among variables of `T` go to `$d` pairs. -/
theorem Derivable.rename {axs : Statement → Prop} (htrim : ∀ a, axs a → a.trimmed)
    {T T' : VR → Prop} {Γ Γ' : Context} (hH : ∀ h ∈ Γ.hyps, ∀ v, v ∈' h.2 → T v)
    {ρ : VR → VR} (htype : ∀ v, (ρ v).type = v.type) (hT : ∀ v, T v → T' (ρ v))
    (hhyps : ∀ h ∈ Γ.hyps, h.subst (renameSubst ρ) ∈ Γ'.hyps)
    (hdj : ∀ a b, T a → T b → Γ.dj a b → Γ'.dj (ρ a) (ρ b)) {f : Formula}
    (pr : Derivable axs T Γ f) : Derivable axs T' Γ' (f.subst (renameSubst ρ)) :=
  pr.subst htrim hH (renameSubst ρ)
    (fun a b hab c d hc hd => by
      have hca : c = ρ a := Sym.var.inj (List.mem_singleton.mp hc)
      have hdb : d = ρ b := Sym.var.inj (List.mem_singleton.mp hd)
      subst hca hdb
      exact hdj a b hab.2.1 hab.2.2 hab.1)
    (fun h hmem => .hyp _ (hhyps h hmem))
    (fun v hv => by
      have h := Derivable.var (axs := axs) (Γ := Γ') (ρ v) (hT v hv)
      change Derivable axs T' Γ' ((ρ v).type, [Sym.var (ρ v)]) at h
      rw [htype v] at h
      exact h)

/-! ## Finitely many variables -/

/-- Finitely many branches, each needing some finite list, share one finite list. -/
theorem exists_common_list {α : Type _} (items : List α)
    (property : α → List VR → Prop) (bound : VR → Prop)
    (hmono : ∀ item {smaller larger : List VR},
      property item smaller → (∀ v ∈ smaller, v ∈ larger) → property item larger)
    (hexists : ∀ item ∈ items, ∃ V, property item V ∧ ∀ v ∈ V, bound v) :
    ∃ V, (∀ item ∈ items, property item V) ∧ ∀ v ∈ V, bound v := by
  induction items with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · intro _ hmem
        exact nomatch hmem
      · intro _ hv
        exact nomatch hv
  | cons head tail ih =>
      obtain ⟨V₁, hp₁, hb₁⟩ := hexists head (List.Mem.head tail)
      obtain ⟨V₂, hp₂, hb₂⟩ := ih (fun item hmem => hexists item (List.Mem.tail head hmem))
      refine ⟨V₁ ++ V₂, ?_, ?_⟩
      · intro item hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · exact hmono _ hp₁ (fun v hv => List.mem_append_left V₂ hv)
        · exact hmono item (hp₂ item htail) (fun v hv => List.mem_append_right V₁ hv)
      · intro v hv
        rcases List.mem_append.mp hv with h | h
        · exact hb₁ v h
        · exact hb₂ v h

/-- A derivation uses finitely many variables. -/
theorem Derivable.exists_finite_vars {axs : Statement → Prop} {T : VR → Prop} {Γ : Context}
    {f : Formula} (pr : Derivable axs T Γ f) :
    ∃ V : List VR, (∀ v ∈ V, T v) ∧ Derivable axs (· ∈ V) Γ f := by
  induction pr with
  | hyp h hh =>
      refine ⟨[], ?_, Derivable.hyp h hh⟩
      intro _ hv
      exact nomatch hv
  | var v hv =>
      refine ⟨[v], ?_, Derivable.var v (List.Mem.head _)⟩
      intro w hw
      rw [List.mem_singleton.mp hw]
      exact hv
  | @ax σ ax ha hdj _ _ ih_h ih_v =>
      have hmono : ∀ (g : Formula) {smaller larger : List VR},
          Derivable axs (· ∈ smaller) Γ g → (∀ v ∈ smaller, v ∈ larger) →
          Derivable axs (· ∈ larger) Γ g :=
        fun _ _ _ hd hsub => hd.mono (fun _ h => h) hsub (Context.refl _)
      obtain ⟨V₁, hp₁, hb₁⟩ := exists_common_list ax.ctx.hyps
        (fun h V => Derivable axs (· ∈ V) Γ (h.subst σ)) T
        (fun h _ _ hd hsub => hmono _ hd hsub)
        (fun h hmem => (ih_h h hmem).imp fun _ hV => ⟨hV.2, hV.1⟩)
      obtain ⟨V₂, hp₂, hb₂⟩ := exists_common_list ax.vars
        (fun v V => Derivable axs (· ∈ V) Γ (v.type, σ v)) T
        (fun v _ _ hd hsub => hmono _ hd hsub)
        (fun v hmem => (ih_v v hmem).imp fun _ hV => ⟨hV.2, hV.1⟩)
      refine ⟨V₁ ++ V₂, ?_, ?_⟩
      · intro v hv
        rcases List.mem_append.mp hv with h | h
        · exact hb₁ v h
        · exact hb₂ v h
      · exact .ax σ ha hdj
          (fun h hmem => hmono _ (hp₁ h hmem) (fun v hv => List.mem_append_left V₂ hv))
          (fun v hmem => hmono _ (hp₂ v hmem) (fun w hw => List.mem_append_right V₁ hw))

/-- Typecodes the axiomatic statements use in premises: heads of their hypotheses and types of their
variables. -/
def PremiseTypecode (axs : Statement → Prop) (t : CN) : Prop :=
  ∃ ax, axs ax ∧ ((∃ h ∈ ax.ctx.hyps, h.1 = t) ∨ ∃ v ∈ ax.vars, v.type = t)

/-- A derivation only needs variables whose typecode is the conclusion's or a premise typecode. -/
theorem Derivable.restrict_typecodes {axs : Statement → Prop} {T : VR → Prop} {Γ : Context}
    {f : Formula} (pr : Derivable axs T Γ f) :
    Derivable axs (fun v => T v ∧ (v.type = f.1 ∨ PremiseTypecode axs v.type)) Γ f := by
  induction pr with
  | hyp h hh => exact .hyp h hh
  | var v hv => exact .var v ⟨hv, Or.inl rfl⟩
  | @ax σ ax ha hdj _ _ ih_h ih_v =>
      refine .ax σ ha hdj (fun h hmem => ?_) (fun v hmem => ?_)
      · refine (ih_h h hmem).mono (fun _ h => h) (fun w ⟨hw, htw⟩ => ⟨hw, Or.inr ?_⟩) (Context.refl _)
        rcases htw with heq | hp
        · exact ⟨ax, ha, Or.inl ⟨h, hmem, by rw [heq, Formula.subst_fst]⟩⟩
        · exact hp
      · refine (ih_v v hmem).mono (fun _ h => h) (fun w ⟨hw, htw⟩ => ⟨hw, Or.inr ?_⟩) (Context.refl _)
        rcases htw with heq | hp
        · exact ⟨ax, ha, Or.inr ⟨v, hmem, heq.symm⟩⟩
        · exact hp

/-! ## Statements -/

/-- **Metamath book C.2.5, as a theorem about Mario's `Statement.Provable`.** A statement is
provable iff it is the reduct of a provable pre-statement: some set `T` of typed variables
containing its own, and some `$d` relation `D` agreeing with its own on its variables, whose
closure contains its assertion. -/
theorem Statement.provable_iff_exists_extension {axs : Statement → Prop} {s : Statement} :
    s.Provable axs ↔ ∃ (T : VR → Prop) (D : DJ), (∀ v ∈ s.vars, T v) ∧
      (∀ a b, a ∈ s.vars → b ∈ s.vars → (D a b ↔ s.ctx.dj a b)) ∧
      Derivable axs T ⟨s.ctx.hyps, D⟩ s.fmla := by
  constructor
  · intro h
    refine ⟨fun _ => True, s.untrim.ctx.dj, fun _ _ => trivial, ?_, provable_iff_derivable.mp h⟩
    intro a b ha hb
    constructor
    · intro hab
      exact hab.2 ha hb
    · intro hab
      exact ⟨s.ctx.dj.ne hab, fun _ _ => hab⟩
  · rintro ⟨T, D, _, hD, hder⟩
    have hle : (⟨s.ctx.hyps, D⟩ : Context) ≤ s.untrim.ctx := by
      refine ⟨fun _ h => h, ?_⟩
      intro a b hab
      exact ⟨D.ne hab, fun ha hb => (hD a b ha hb).mp hab⟩
    exact provable_iff_derivable.mpr (hder.mono (fun _ h => h) (fun _ _ => (trivial : True)) hle)

/-- The pre-statement of `s` with dummy variables `V`: the hypotheses of `s`, its `$d` pairs among
its own variables, and every pair with a dummy distinct. Its reduct is `s` when `s` is trimmed. -/
def Statement.withDummies (s : Statement) (V : List VR) : Statement :=
  ⟨⟨s.ctx.hyps, s.untrim.ctx.dj.trim (· ∈ s.vars ++ V)⟩, s.fmla⟩

/-- A provable statement is provable with finitely many dummy variables `V`, each typed by its
assertion's typecode or by a typecode the axiomatic statements use in premises. The axiomatic
statements are reducts. -/
theorem Statement.exists_finite_extension {axs : Statement → Prop}
    (htrim : ∀ a, axs a → a.trimmed) {s : Statement} (h : s.Provable axs) :
    ∃ V : List VR, (∀ v ∈ V, v.type = s.fmla.1 ∨ PremiseTypecode axs v.type) ∧
      Derivable axs (· ∈ s.vars ++ V) (s.withDummies V).ctx s.fmla := by
  obtain ⟨V, hV, hder⟩ := (provable_iff_derivable.mp h).restrict_typecodes.exists_finite_vars
  refine ⟨V, fun v hv => (hV v hv).2, ?_⟩
  have hmono : Derivable axs (· ∈ s.vars ++ V) s.untrim.ctx s.fmla :=
    hder.mono (fun _ h => h) (fun _ h => List.mem_append_right _ h) (Context.refl _)
  exact Derivable.trim_dj (Γ := s.untrim.ctx) htrim
    (fun _ hh _ hv => List.mem_append_left V (s.mem_vars_of_hyp hh hv)) hmono

/-- Finitely many dummy variables suffice: a statement is provable iff some finite list `V` of
dummy variables makes its pre-statement provable. The axiomatic statements are reducts. -/
theorem Statement.provable_iff_exists_finite_extension {axs : Statement → Prop}
    (htrim : ∀ a, axs a → a.trimmed) {s : Statement} :
    s.Provable axs ↔ ∃ V : List VR, Derivable axs (· ∈ s.vars ++ V) (s.withDummies V).ctx s.fmla := by
  constructor
  · intro h
    obtain ⟨V, _, hV⟩ := Statement.exists_finite_extension htrim h
    exact ⟨V, hV⟩
  · rintro ⟨V, hV⟩
    have hle : (s.withDummies V).ctx ≤ s.untrim.ctx :=
      ⟨fun _ h => h, DJ.trim_le_self s.untrim.ctx.dj _⟩
    exact provable_iff_derivable.mpr (hV.mono (fun _ h => h) (fun _ _ => (trivial : True)) hle)

end Metamath
