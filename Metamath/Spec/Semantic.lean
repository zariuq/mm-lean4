/-
Semantic layer for Metamath specification - Mario Carneiro's canonical foundation.

This file re-exports Mario Carneiro's Translate.lean types as the canonical
semantic specification of Metamath provability.

**Why Mario's layer?**
- Proven lemmas for substitution, DJ, trim/untrim
- Clean declarative "big-step" semantics
- Expert-written, production-tested formalization
- Textbook-style mathematical definitions

**Relationship to Operational layer**:
- Semantic (this file): WHAT it means for an assertion to be provable
- Operational (Operational.lean): HOW the verifier checks proofs
- Bridge (Equivalence.lean): Proves they're equivalent

Per Mario Carneiro's Translate.lean formalization.
-/

import Metamath.Translate

namespace Metamath.Spec.Semantic

-- Re-export Mario's core types
export Metamath (CN VR Sym Expr Formula DJ Context Statement)

-- Re-export Mario's Provable as the canonical semantic spec
export Metamath (Provable)

/-! ## Mario's Type System

**Core types**:
- `VR where (type : CN) (i : Nat)` - Indexed variables
- `Sym = const String | var VR` - Symbols (inductive)
- `Expr = List Sym` - Expressions
- `Formula = CN × Expr` - Typed formulas

**Contexts and Statements**:
- `DJ` - Disjoint variable structure (with irr, symm axioms)
- `Context where (hyps : List Formula) (dj : DJ)` - Proof context
- `Statement where (ctx : Context) (fmla : Formula)` - Full statement

**Provability** (3 constructors):
```lean
inductive Provable (axs : Statement → Prop) (Γ : Context) : Formula → Prop
  | hyp (h) : h ∈ Γ.hyps → Provable axs Γ h
  | var (v:VR) : v.vhyp ∈ Γ.hyps → Provable axs Γ v
  | ax (σ) {ax} : axs ax → ax.ctx.dj.subst σ Γ.dj →
      (∀ h ∈ ax.ctx.hyps, Provable axs Γ (h.subst σ)) →
      (∀ v ∈ ax.vars, Provable axs Γ (v.type, σ v)) →
      Provable axs Γ (ax.fmla.subst σ)
```

**Note on var constructor**: Per Metamath spec §4.2.4, a variable must have its
floating hypothesis ($f statement) in scope before use. The `v.vhyp ∈ Γ.hyps`
requirement enforces this - you cannot use an undeclared variable.

**Key lemmas available**:
- `Expr.subst_id` - Identity substitution
- `Expr.subst_append` - Substitution distributes over append
- `Expr.subst_tr` - Substitution composition
- `DJ.trim`, `DJ.untrim` - DJ scoping operations
- `Provable.mono` - Monotonicity
- `Provable.trans'` - Transitivity

-/

end Metamath.Spec.Semantic
