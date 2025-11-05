# Bridge Overview: Implementation ↔ Specification

**Date:** 2025-10-13
**Project:** Metamath Verifier Soundness Proof

---

## One-Page Summary

This document explains how the **implementation verifier** (Verify.lean) connects to the **mathematical specification** (Spec.lean) through a **bridge layer** (Bridge/Basics.lean, Kernel.lean).

```
┌─────────────────────────────────────────────────────────────┐
│                    SPEC.LEAN                                │
│  Mathematical semantics: Provable, applySubst, DV           │
│  Pure, total functions over Expr, Frame, Subst              │
└─────────────────────────────────────────────────────────────┘
                           ▲
                           │
                     toExpr, toFrame
                     TypedSubst witness
                           │
┌─────────────────────────────────────────────────────────────┐
│                 BRIDGE (Kernel.lean)                        │
│  • Conversion functions: toExpr, toFrame, toSubstTyped      │
│  • Witness predicates: FloatBindWitness, TypedSubst         │
│  • Bridge theorems: checkHyp_produces_typed_coverage        │
│  • Simulation invariant: ProofStateInv                      │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│              VERIFY.LEAN                                    │
│  Implementation: checkHyp, stepNormal, stepAssert           │
│  Partial functions over Formula, ProofState, HashMap        │
│  Returns Except (error or ok)                               │
└─────────────────────────────────────────────────────────────┘
```

---

## Key Design Principles

### 1. **Fail-Fast Option Returns**

Instead of dependent types, we use `Option` to encode partiality:

**BAD (dependent types):**
```lean
def toExpr (f : Formula) (h : isValidFormula f) : Expr
```
Problems: Proof obligations everywhere, tight coupling

**GOOD (Option returns):**
```lean
def toExpr (f : Formula) : Option Expr
```
Benefits: Total function, composes cleanly, natural error propagation

This follows the "Lean verified compiler" lesson: **prefer `nth`/`find?` over `nth_le` with proof parameters**.

---

### 2. **Witness-Carrying Predicates**

Instead of "phantom values" (arbitrary default on error), we use **explicit witnesses**:

**BAD (phantom values):**
```lean
def toSubst (σ : HashMap String Formula) : Spec.Subst :=
  fun v => match σ[v.v]? with
  | some f => toExpr f |>.getD ⟨⟨"wff"⟩, ["wff"]⟩  -- PHANTOM!
  | none => ⟨⟨v.v⟩, [v.v]⟩
```
Problems: Untyped result, no guarantee "wff" is valid

**GOOD (witness-carrying):**
```lean
structure TypedSubst (fr : Spec.Frame) where
  σ : Spec.Subst
  typed : ∀ c v, (c, v) ∈ fr.floatingHyps → (σ v).typecode = c
```
Benefits: Type correctness is **proven**, no silent corruption

---

### 3. **Boolean Folds → ∀-Facts**

Implementation uses boolean scans (e.g., DV checks). Bridge converts to spec ∀-facts:

**Implementation (Verify.lean):**
```lean
def checkDV (dj : Array (String × String)) (σ : HashMap String Formula) : Bool :=
  dj.foldl (fun acc (v1, v2) => acc && distinctVars σ[v1] σ[v2]) true
```

**Bridge theorem (KernelExtras.lean):**
```lean
theorem foldl_and_eq_true : (xs.foldl (fun acc x => acc && p x) true = true) ↔ ∀ x ∈ xs, p x
```

**Spec (Spec.lean):**
```lean
structure Frame where
  dj : List (Variable × Variable)
  hyps : List Hyp

def dvOK (fr : Frame) (σ : Subst) : Prop :=
  ∀ (v1, v2) ∈ fr.dj, disjoint (varsInExpr vars (σ v1)) (varsInExpr vars (σ v2))
```

**Result:** Boolean scan correctness implies ∀-quantified DV condition.

---

## Core Bridge Components

### A. Conversion Functions

#### `toExpr : Formula → Option Expr` (Kernel.lean:~670)

Converts implementation formulas to spec expressions.

**Properties:**
- Fails if Formula has invalid structure
- Preserves substitution: see `subst_sound` theorem

**Usage:** Every formula on the stack must `toExpr` successfully to relate to spec.

---

#### `toFrame : DB → Verify.Frame → Option Spec.Frame` (Kernel.lean:~1300)

Converts implementation frames to spec frames.

**Properties:**
- Converts hypothesis list
- Converts DV constraints
- Fails if any hypothesis doesn't convert

**Usage:** Frame correspondence is key to proving `Provable`.

---

#### `toSubstTyped : Frame → HashMap String Formula → Option (TypedSubst Frame)` (Bridge/Basics.lean:~200)

**Fail-fast** conversion that checks typing:

```lean
def toSubstTyped (fr : Spec.Frame) (σ_impl : HashMap String Formula) : Option (TypedSubst fr) :=
  if h : ∀ (c, v) ∈ fr.floatingHyps,
         ∃ f ∈ σ_impl.values, toExpr f = some e ∧ e.typecode = c
  then some ⟨σ, h⟩
  else none
```

**Key property:** If `toSubstTyped` returns `some`, the substitution is **provably well-typed**.

---

### B. Witness Predicates

#### `FloatBindWitness` (Kernel.lean:~1495)

Proves that a binding from `checkHyp` is valid:

```lean
def FloatBindWitness (db : DB) (v : String) (val : Formula) (c : Constant) : Prop :=
  toExprOpt val = some e ∧ e.typecode = c ∧ (val[0]! == c.c) = true
```

**Why the `==` check?** Bridges boolean head-constant check to spec typing.

---

#### `HypProp` (Kernel.lean:~1510)

Loop invariant for `checkHyp` induction:

```lean
def HypProp (i : Nat) (subst : HashMap String Formula) : Prop :=
  ∀ v val, subst[v]? = some val →
    ∃ j < i, (hyps[j] is floating with constant c) ∧ FloatBindWitness db v val c
```

**Purpose:** Tracks origin of every binding - which hypothesis it came from.

---

### C. Key Bridge Theorems

These are the "hinge" theorems connecting implementation to spec.

---

#### 1. **`checkHyp_stack_split`** (Kernel.lean:~2295)

```lean
theorem checkHyp_stack_split
    (h_checkHyp : db.checkHyp hyps stack off 0 ∅ = .ok σ)
    (h_stack : stack.toList.mapM toExpr = some stack_spec) :
  ∃ remaining needed, stack_spec = remaining ++ needed.reverse ∧ needed.length = hyps.size
```

**What it proves:** Stack has correct **shape** - top |hyps| elements match hypotheses in reverse order (RPN discipline).

**Why it matters:** Spec's `useAxiom` requires this exact suffix structure.

---

#### 2. **`checkHyp_images_convert`** (Kernel.lean:~2407)

```lean
theorem checkHyp_images_convert
    (h_checkHyp : db.checkHyp hyps stack off 0 ∅ = .ok σ) :
  ∀ fv ∈ σ.values, ∃ e, toExpr fv = some e
```

**What it proves:** Every value in the substitution **converts to spec**.

**Why it matters:** Can't have phantom formulas - everything is valid.

---

#### 3. **`checkHyp_domain_covers`** (Kernel.lean:~2418)

```lean
theorem checkHyp_domain_covers
    (h_checkHyp : db.checkHyp hyps stack off 0 ∅ = .ok σ)
    (h_frame : toFrame db fr = some fr_spec) :
  ∀ v ∈ fr_spec.floatingHyps.map (·.2), σ.contains v
```

**What it proves:** Substitution **covers all variables** in frame's floating hypotheses.

**Why it matters:** No missing bindings - frame is fully instantiated.

---

#### 4. **`checkHyp_produces_typed_coverage`** (KEY THEOREM - Kernel.lean:~2445)

```lean
theorem checkHyp_produces_typed_coverage
    (h_checkHyp : db.checkHyp hyps stack off 0 ∅ = .ok σ)
    (h_stack : stack.toList.mapM toExpr = some stack_spec)
    (h_frame : toFrame db fr = some fr_spec) :
  ∀ (c, v) ∈ fr_spec.floatingHyps,
    ∃ e, σ[v]? = some f ∧ toExpr f = some e ∧ e.typecode = c
```

**What it proves:** **Every float is typed correctly** - the holy grail!

**Why it matters:** This is the **foundation for TypedSubst** - proves that `toSubstTyped` will succeed.

**Proof chain:**
- `checkHyp_preserves_HypProp` → every binding has `FloatBindWitness`
- `FloatBindWitness` → `e.typecode = c` (typing witness!)
- Combine with `domain_covers` → **full typed coverage**

---

#### 5. **`checkHyp_produces_TypedSubst`** (Phase 3 - Bridge/Basics.lean or Kernel.lean)

```lean
theorem checkHyp_produces_TypedSubst
    (h_checkHyp : db.checkHyp hyps stack off 0 ∅ = .ok σ)
    (h_stack : stack.toList.mapM toExpr = some stack_spec)
    (h_frame : toFrame db fr = some fr_spec) :
  ∃ σ_typed, toSubstTyped fr_spec σ = some σ_typed
```

**What it proves:** `checkHyp` success → `TypedSubst` construction succeeds.

**Why it matters:** One-line path from implementation to **honest typed substitutions**.

**Proof:** Direct from `checkHyp_produces_typed_coverage` + `toSubstTyped` definition.

---

### D. Simulation Invariant

#### `ProofStateInv` (Kernel.lean:~2950)

Relates implementation `ProofState` to spec `(Frame, List Expr)`:

```lean
structure ProofStateInv (db : DB) (pr : ProofState) (fr_spec : Spec.Frame) (stack_spec : List Spec.Expr) where
  state_ok : viewState db pr = some (fr_spec, stack_spec)
  stack_len_ok : stack_spec.length = pr.stack.size
```

**Purpose:** Simulation relation for proving `stepNormal` correctness.

**Key property:** Preserved by every `stepNormal` step (`stepNormal_preserves_inv`, Kernel.lean:~3008).

---

## The Complete Proof Chain

Here's how everything connects to prove soundness:

```
verify_impl_sound                           [Main theorem]
    ↓ (fold over proof steps)
fold_maintains_inv_and_provable             [Induction on steps]
    ↓ (each step)
stepNormal_preserves_inv                    [Single step simulation]
    ↓ (assertion case)
stepNormal_impl_correct                     [Step → Spec correspondence]
    ↓ (checkHyp validation)
checkHyp_produces_TypedSubst                [Phase 3 KEY THEOREM]
    ↓ (typed coverage)
checkHyp_produces_typed_coverage            [Phase 2 KEY THEOREM]
    ↓ (properties of checkHyp)
checkHyp_preserves_HypProp                  [Loop invariant]
    ↓ (base invariant)
FloatBindWitness                            [Typing witness per binding]
```

**Result:** Implementation success → Spec-level `Provable`! 🎉

---

## Key Insights from Lean Compiler Report

### ✅ DO: Use Option/Find? for Partiality
- **Lesson:** Dependent proofs (`nth_le`) create tight coupling and proof brittleness.
- **Application:** All conversions return `Option`, never panic or use partial functions.

### ✅ DO: Total Functions + Explicit Failure
- **Lesson:** Prefer total functions that return error codes over partial functions.
- **Application:** `toExpr`, `toFrame`, `toSubstTyped` are all total functions returning `Option`.

### ✅ DO: Witnesses Over Phantoms
- **Lesson:** Carry proof witnesses explicitly instead of using arbitrary defaults.
- **Application:** `TypedSubst` carries `typed` witness; `FloatBindWitness` carries type equality.

### ✅ DO: Boolean Scans → Logical Facts
- **Lesson:** Bridge boolean checks to logical properties via fold lemmas.
- **Application:** `foldl_and_eq_true` converts DV boolean to `∀` fact.

---

## Design Rationale: Why This Structure?

### Q: Why not just axiomatize `toSubst` correctness?

**A:** Axioms hide bugs. By **constructing** `TypedSubst` with witnesses, we:
1. Prove type safety (no phantom values)
2. Make conversion failures explicit (Option return)
3. Get **checkable** properties (no "trust me")

---

### Q: Why separate Spec from Verify?

**A:** Clean semantics. Spec is **what Metamath means** (math). Verify is **how we check it** (code). Bridge proves **they agree**.

---

### Q: Why not use dependent types everywhere?

**A:** Proof brittleness. Dependent indices create tight coupling. Lean prefers:
- `List.get? : List α → Nat → Option α` (total, returns Option)
- NOT `List.get : (l : List α) → (i : Nat) → (h : i < l.length) → α` (partial, proof parameter)

**Our approach:** Use `Option` + existence proofs. More flexible, easier to refactor.

---

### Q: How does this relate to TransWeave/OT?

**Bridge as commuting diagram:** The bridge theorems are commutativity proofs:

```
checkHyp(impl) ──────toSubstTyped──────→ TypedSubst(spec)
     │                                        │
     │                                        │
  success                                 proof of
     │                                    well-typed
     │                                        │
     ▼                                        ▼
  OK(σ)  ───────checkHyp_produces────→  ∃ typed witness
```

Implementation operations **commute** with spec operations via conversion functions. The bridge lemmas prove this commutativity.

---

## Files and Line Numbers

| Component | File | Lines | Description |
|-----------|------|-------|-------------|
| **Spec** | Metamath/Spec.lean | ~300 | Math semantics |
| **Verify** | Metamath/Verify.lean | ~800 | Implementation |
| **Bridge** | Metamath/Bridge/Basics.lean | ~250 | TypedSubst |
| **Kernel** | Metamath/Kernel.lean | ~3800 | Bridge theorems + soundness |
| **Extras** | Metamath/KernelExtras.lean | ~100 | Fold lemmas |

---

## Summary: What Makes This Bridge Bulletproof

1. **Fail-fast conversions** - No silent failures or phantom values
2. **Witness-carrying types** - Type safety is proven, not assumed
3. **Boolean → Logical** - Implementation checks proven equivalent to spec facts
4. **Simulation invariant** - Clear correspondence at every step
5. **Theorem chain** - Each bridge lemma builds on previous ones
6. **Total functions** - No partiality, all paths explicit

**Result:** If the verifier says "ok", we **prove** (not assert) that the spec says "Provable". No handwaving, no gaps.

---

**Maintained by:** Zar
**Review:** Update when bridge structure changes
**See also:** TCB.md (axioms), BUILD_REPRO.md (how to build)
