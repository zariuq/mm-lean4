# Phase 3 Integration Requirements - Complete Analysis

**Date:** 2025-10-13
**Purpose:** Comprehensive analysis of all type system changes, helper lemmas, witnesses, and infrastructure needed for Phase 3 integration
**Status:** Planning Document - To inform Phase 2 work

---

## Executive Summary

Phase 3 (Integration + Bridge) is the critical phase where:
1. The thin Bridge module connects Spec ↔ Kernel
2. TypedSubst replaces the "phantom wff" toSubst
3. All remaining sorries are eliminated
4. The full verification pipeline is proven sound

**Key insight:** We need to build the right witness-carrying infrastructure NOW in Phase 2, so Phase 3 can smoothly integrate everything without major refactoring.

---

## Table of Contents

1. [Bridge Module Structure](#bridge-module-structure)
2. [Type System Requirements](#type-system-requirements)
3. [Witness-Carrying Patterns](#witness-carrying-patterns)
4. [Helper Lemma Infrastructure](#helper-lemma-infrastructure)
5. [Integration Points](#integration-points)
6. [Remaining Sorries Analysis](#remaining-sorries-analysis)
7. [Phase 2 → Phase 3 Dependencies](#phase-2-phase-3-dependencies)

---

## Bridge Module Structure

### Current State

**Exists in Codex's archive:** `codex_archive/Bridge/Basics.lean`

**Key definitions (all thin, definition-only):**
```lean
namespace Metamath.Bridge

/-- Floating hypotheses extraction -/
def floats (fr : Spec.Frame) : List (Spec.Constant × Spec.Variable)

/-- Essential hypotheses extraction -/
def essentials (fr : Spec.Frame) : List Spec.Expr

/-- Witness-carrying typed substitution -/
structure TypedSubst (fr : Spec.Frame) where
  σ : Spec.Subst
  typed : ∀ {c v}, Spec.Hyp.floating c v ∈ fr.mand → (σ v).typecode = c

/-- Needed hypothesis images -/
def needOf (vars : List Spec.Variable) (σ : Spec.Subst) : Spec.Hyp → Spec.Expr
def needed (vars : List Spec.Variable) (fr : Spec.Frame) (σ : Spec.Subst) : List Spec.Expr
```

**Supporting lemmas (thin proofs, ~100 lines):**
- `floating_mem_floats`: Every floating hyp appears in floats list
- `floats_mem_floating`: Reverse direction
- `floats_map_snd`: Variable projection agrees with filterMap

### What Phase 3 Needs

1. **Module hierarchy:**
   ```
   Metamath/Spec.lean           -- Already exists
   Metamath/Bridge/Basics.lean  -- NEW: Thin definitions
   Metamath/Bridge.lean         -- NEW: Root import
   Metamath/Verify.lean         -- Already exists (checkHyp impl)
   Metamath/Kernel.lean         -- Update imports
   ```

2. **Import changes in Kernel.lean:**
   ```lean
   import Metamath.Spec
   import Metamath.Bridge      -- NEW!
   import Metamath.Verify
   ```

3. **lakefile.lean update:**
   ```lean
   lean_lib Metamath where
     roots := #[`Metamath.Spec, `Metamath.Bridge, `Metamath.Verify, `Metamath.Kernel]
   ```

**Key principle:** Bridge contains ZERO complex proofs. All verification stays in Kernel.lean.

---

## Type System Requirements

### 1. TypedSubst - The Central Type

**What it replaces:**
```lean
-- OLD (current Kernel.lean:1299-1308)
def toSubst (σ_impl : HashMap String Formula) : Option Spec.Subst :=
  some (fun v =>
    match σ_impl[v.v.drop 1]? with
    | some f =>
        match toExpr f with
        | some e => e
        | none => ⟨⟨"wff"⟩, [v.v]⟩  -- ❌ PHANTOM WFF BUG!
    | none => ⟨⟨"wff"⟩, [v.v]⟩)
```

**What Phase 3 needs:**
```lean
-- NEW (using Bridge.TypedSubst)
def toSubstTyped (σ_impl : HashMap String Formula) (fr : Spec.Frame)
    : Option (Bridge.TypedSubst fr) :=
  -- Uses checkHyp_produces_typed_coverage to build witness
  -- NO fallbacks - either fully typed or None
  ...
```

**Type system implications:**
- TypedSubst is **frame-specific** (parametrized by `fr : Spec.Frame`)
- Carries **witness** that all floating hypotheses have correct typecodes
- **Witness type:** `∀ {c v}, Spec.Hyp.floating c v ∈ fr.mand → (σ v).typecode = c`

### 2. Frame Conversion Types

**Current:** `toFrame` returns `Option Spec.Frame` (lines 1330-1341)

**Phase 3 requirement:** Need witness that conversion succeeds for WF databases

```lean
-- Helper type for frame conversion witness
structure FrameConv (db : Verify.DB) (fr_impl : Verify.Frame) where
  fr_spec : Spec.Frame
  converts : toFrame db fr_impl = some fr_spec
```

**Why:** Simplifies proofs by bundling the conversion witness with the result.

### 3. Stack Conversion Types

**Current:** Stack conversion via `stack.toList.mapM toExpr`

**Phase 3 requirement:** Witness that stack elements have consistent structure

```lean
-- Helper for stack conversion
structure StackConv (stack_impl : Array Verify.Formula) where
  stack_spec : List Spec.Expr
  converts : stack_impl.toList.mapM toExpr = some stack_spec

  -- Optional: Length preservation witness
  length_eq : stack_spec.length = stack_impl.size
```

**Benefit:** Avoids repeating mapM proofs; witness carries the conversion.

### 4. Substitution Domain Types

**What Phase 3 needs:** Track which variables are covered by a substitution

```lean
-- Domain coverage witness
def SubstCovers (σ_impl : HashMap String Formula) (vars : List String) : Prop :=
  ∀ v ∈ vars, σ_impl.contains v = true

-- Combined: Coverage + Conversion
structure TypedCoverage (σ_impl : HashMap String Formula) (fr : Spec.Frame) where
  covers : ∀ v, (∃ c, Spec.Hyp.floating c v ∈ fr.mand) → σ_impl.contains v.v = true
  converts : ∀ v val, σ_impl[v]? = some val → ∃ e, toExpr val = some e
  typed : ∀ c v val e, Spec.Hyp.floating c v ∈ fr.mand →
                        σ_impl[v.v]? = some val →
                        toExpr val = some e →
                        e.typecode = c
```

**This is exactly what `checkHyp_produces_typed_coverage` gives us!**

---

## Witness-Carrying Patterns

### Pattern 1: FloatBindWitness (Already in Kernel.lean!)

**Location:** Lines 1392-1402

**Purpose:** Carries evidence that a floating hypothesis binding is well-typed

**Structure:**
```lean
def FloatBindWitness (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (j : Nat) (v : String) (val : Formula) : Prop :=
  ∃ (hj : j < hyps.size) (k : Fin stack.size) (f : Formula) (lbl : String),
    off.1 + j = k.val ∧
    db.find? (hyps[j]) = some (.hyp false f lbl) ∧
    f[1]!.value = v ∧
    val = stack[k]! ∧
    (f[0]! == val[0]!) = true  -- ⭐ KEY: Typecode equality witness
```

**Why it matters:** The last conjunct `(f[0]! == val[0]!) = true` is the witness that proves `toExpr val` will succeed with the correct typecode!

**Phase 3 usage:** This feeds directly into TypedSubst construction.

### Pattern 2: HypProp Loop Invariant (Already in Kernel.lean!)

**Location:** Lines 1410-1412

**Purpose:** Tracks that all bindings in a substitution come from processed floating hypotheses

**Structure:**
```lean
def HypProp (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (n : Nat) (σ : HashMap String Formula) : Prop :=
  ∀ v val, σ[v]? = some val →
    ∃ j, j < n ∧ FloatBindWitness db hyps stack off j v val
```

**Why it matters:** This invariant connects the imperative checkHyp loop to the declarative TypedSubst witness.

**Phase 3 usage:** `checkHyp_preserves_HypProp` + `HypProp` → `TypedSubst` construction.

### Pattern 3: WF Database Invariant (Already in Kernel.lean!)

**Location:** Lines 1785-1818

**Purpose:** Tracks well-formedness properties of the database

**Structure:**
```lean
structure WF (db : Verify.DB) : Prop where
  toExpr_ok : ∀ label f, db.find? label = some (.assert f _ _) ∨ ... →
                          ∃ e, toExpr f = some e
  toFrame_ok_for_assert : ∀ label fr, db.find? label = some (.assert _ fr _) →
                                        ∃ fr_spec, toFrame db fr = some fr_spec
  -- ... more properties
```

**Why it matters:** WF is threaded through ALL verification theorems. It's the top-level invariant.

**Phase 3 usage:** WF ensures conversions succeed, enabling all bridge theorems.

### Pattern 4: ProofStateInv (Already in Kernel.lean!)

**Location:** Lines 2932-2935

**Purpose:** Connects implementation proof state to specification

**Structure:**
```lean
structure ProofStateInv (db : Verify.DB) (pr : Verify.ProofState)
    (fr_spec : Spec.Frame) (stack_spec : List Spec.Expr) : Prop where
  state_ok : viewState db pr = some (fr_spec, stack_spec)
  stack_len_ok : pr.stack.size = stack_spec.length
```

**Why it matters:** This is the simulation invariant! Preservation of ProofStateInv = simulation proof.

**Phase 3 usage:** Main verification theorem shows ProofStateInv preservation.

---

## Helper Lemma Infrastructure

### Category A: List/Array Operations (Need ~15 lemmas)

**What exists:**
- `list_mapM_Option_length` (added in Phase 2, line 1614)

**What Phase 3 needs:**

1. **mapM index preservation:**
   ```lean
   theorem mapM_index_some {α β} (f : α → Option β) (xs : List α) (ys : List β)
       (h : xs.mapM f = some ys) (i : Nat) (hi : i < xs.length) :
       ∃ y, f (xs.get ⟨i, hi⟩) = some y ∧
            ys.get ⟨i, by ...⟩ = y
   ```
   **Location in Codex:** KernelExtras.lean:126-165
   **Usage:** checkHyp_images_convert proof (extracting converted bindings)
   **Estimated lines:** ~40

2. **mapM membership:**
   ```lean
   theorem mapM_mem {α β} (f : α → Option β) (xs : List α) (ys : List β)
       (h : xs.mapM f = some ys) (y : β) :
       y ∈ ys → ∃ x ∈ xs, f x = some y
   ```
   **Location in Codex:** KernelExtras.lean:167-200
   **Usage:** Reverse lookups in converted stacks
   **Estimated lines:** ~30

3. **Array/List drop/take lemmas:**
   ```lean
   theorem Array.getElem_toList (xs : Array α) (i : Nat) (h : i < xs.size) :
       xs.toList.get ⟨i, by ...⟩ = xs[i]

   theorem List.drop_eq_getElem_cons (l : List α) (i : Nat) (h : i < l.length) :
       l.drop i = l.get ⟨i, h⟩ :: l.drop (i + 1)
   ```
   **Usage:** checkHyp_domain_covers, stack manipulation proofs
   **Estimated lines:** ~20 each

**Status:** Some may exist in Mathlib; need to check/import/adapt.

### Category B: HashMap Operations (Need ~5 lemmas)

**What exists (as axioms in Phase 1):**
- `HashMap.getElem?_insert_self` (line 1381)
- `HashMap.getElem?_insert_of_ne` (line 1386)

**What Phase 3 needs:**

1. **contains_eq_isSome:**
   ```lean
   theorem HashMap.contains_eq_isSome_getElem? (m : HashMap α β) (a : α) :
       m.contains a = m[a]?.isSome
   ```
   **Location in Codex:** Used in checkHyp_images_convert
   **Status:** May exist in Std.HashMap
   **Estimated lines:** ~5-10

2. **contains_insert_self:**
   ```lean
   theorem HashMap.contains_insert_self (m : HashMap α β) (a : α) (b : β) :
       (m.insert a b).contains a = true
   ```
   **Location in Codex:** KernelExtras.lean:198-201
   **Usage:** checkHyp_domain_covers monotonicity
   **Estimated lines:** ~5

3. **contains_mono_insert:**
   ```lean
   theorem HashMap.contains_mono_insert (m : HashMap α β) (a k : α) (b : β) :
       m.contains a = true → (m.insert k b).contains a = true
   ```
   **Location in Codex:** KernelExtras.lean:203-224
   **Usage:** checkHyp_domain_covers
   **Estimated lines:** ~20

**Recommendation:** Import from Std or prove once as utilities.

### Category C: checkHyp Auxiliary Lemmas (Need ~3 lemmas)

**What Phase 2/3 needs:**

1. **checkHyp_contains_mono:**
   ```lean
   theorem checkHyp_contains_mono {i : Nat} {subst σ : HashMap String Formula}
       (hi : i ≤ hyps.size)
       (hrun : DB.checkHyp db hyps stack off i subst = .ok σ) :
       ∀ v, subst.contains v = true → σ.contains v = true
   ```
   **Location in Codex:** Verify/Proofs.lean:259-379
   **Purpose:** Monotonicity of domain during checkHyp
   **Usage:** Needed for checkHyp_domain_covers
   **Estimated lines:** ~120 (strong induction like checkHyp_preserves_HypProp)

2. **checkHyp_domain_aux:**
   ```lean
   theorem checkHyp_domain_aux {i : Nat} {subst σ : HashMap String Formula}
       (hi : i ≤ hyps.size)
       (hrun : DB.checkHyp db hyps stack off i subst = .ok σ) :
       ∀ label ∈ hyps.toList.drop i,
         ∀ f, db.find? label = some (.hyp false f _) →
           σ.contains (f[1]!.value) = true
   ```
   **Location in Codex:** Verify/Proofs.lean:381-519
   **Purpose:** Auxiliary for domain coverage (handles induction on i)
   **Usage:** Needed for checkHyp_domain_covers_theorem
   **Estimated lines:** ~140 (strong induction with list manipulation)

3. **checkHyp_binding_witness:**
   ```lean
   theorem checkHyp_binding_witness (db : DB) (hyps : Array String)
       (stack : Array Formula) (off : ...) (σ : HashMap String Formula) :
       DB.checkHyp db hyps stack off 0 ∅ = .ok σ →
       ∀ v val, σ[v]? = some val →
         ∃ j f lbl (hlt : off.1 + j < stack.size),
           j < hyps.size ∧
           db.find? hyps[j] = some (.hyp false f lbl) ∧
           f[1]!.value = v ∧
           val = stack[off.1 + j]'hlt ∧
           f[0]! == val[0]! = true
   ```
   **Location in Codex:** Verify/Proofs.lean:678-712
   **Purpose:** Extract the FloatBindWitness for any binding
   **Usage:** Bridge between HypProp and TypedSubst
   **Estimated lines:** ~35

**Note:** These are the "missing pieces" from Phase 2!

### Category D: Conversion Lemmas (Need ~8 lemmas)

**What Phase 3 needs for toSubst → TypedSubst transition:**

1. **toExpr_typecode_from_head:**
   ```lean
   theorem toExpr_typecode_from_head (f val : Formula) (e : Spec.Expr) :
       f[0]! == val[0]! = true →
       toExpr val = some e →
       e.typecode = f[0]!.value
   ```
   **Purpose:** Key bridge: typecode equality → converted typecode match
   **Usage:** Building TypedSubst witness from FloatBindWitness
   **Estimated lines:** ~15-20

2. **toSubstTyped_total:**
   ```lean
   theorem toSubstTyped_total (σ_impl : HashMap String Formula) (fr : Spec.Frame)
       (hcover : ∀ c v, Spec.Hyp.floating c v ∈ fr.mand →
                         ∃ f e, σ_impl[v.v]? = some f ∧
                                toExpr f = some e ∧
                                e.typecode = c) :
       ∃ σ_typed : Bridge.TypedSubst fr, toSubstTyped σ_impl fr = some σ_typed
   ```
   **Purpose:** If coverage holds, TypedSubst construction succeeds
   **Usage:** Final bridge from checkHyp to TypedSubst
   **Estimated lines:** ~30-40

3. **toFrame_preserves_floats:**
   ```lean
   theorem toFrame_preserves_floats (db : DB) (fr_impl : Verify.Frame)
       (fr_spec : Spec.Frame) :
       toFrame db fr_impl = some fr_spec →
       ∀ c v, Spec.Hyp.floating c v ∈ fr_spec.mand ↔
              ∃ label ∈ fr_impl.hyps.toList, convertHyp db label = some (.floating c v)
   ```
   **Purpose:** Frame conversion preserves floating hypothesis structure
   **Usage:** Connecting checkHyp's hyps array to Spec.Frame
   **Estimated lines:** ~40-50

**Total for conversions:** ~150 lines

---

## Integration Points

### Integration Point 1: checkHyp → TypedSubst

**Current gap:** checkHyp produces `HashMap String Formula`, but we need `TypedSubst fr`

**Bridge needed:**
```lean
theorem checkHyp_produces_TypedSubst
    (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (σ : HashMap String Formula) (fr_spec : Spec.Frame)
    (h_check : DB.checkHyp db hyps stack off 0 ∅ = .ok σ)
    (h_frame : toFrame db ⟨hyps, #[]⟩ = some fr_spec)
    (h_stack : ∃ stack_spec, stack.toList.mapM toExpr = some stack_spec) :
    ∃ σ_typed : Bridge.TypedSubst fr_spec,
      toSubstTyped σ fr_spec = some σ_typed ∧
      σ_typed.σ = (fun v => match σ[v.v]? with | some f => ... | none => ...) :=
  by
    -- Use checkHyp_produces_typed_coverage
    -- Build TypedSubst witness using toSubstTyped_total
    ...
```

**Dependencies:**
- checkHyp_produces_typed_coverage (Phase 1, currently axiom line 1557)
- toSubstTyped definition
- toSubstTyped_total lemma

**Status:** checkHyp_produces_typed_coverage is axiomat ized; needs proof.

### Integration Point 2: stepAssert Uses TypedSubst

**Current code (lines 1900-1929):** Uses `toSubst` with fallback

**Phase 3 change:**
```lean
-- OLD:
match toSubst σ_impl with
| some σ_spec => ... -- use σ_spec
| none => fallback

-- NEW:
match toSubstTyped σ_impl fr_callee with
| some σ_typed => ... -- use σ_typed.σ (guaranteed well-typed!)
| none => error -- Should never happen due to checkHyp_produces_TypedSubst
```

**Proof obligation:** Show that checkHyp success implies toSubstTyped success.

**Helper needed:**
```lean
theorem checkHyp_ensures_toSubstTyped_succeeds
    (h_check : DB.checkHyp ... = .ok σ)
    (h_frame : toFrame db fr_impl = some fr_spec) :
    ∃ σ_typed, toSubstTyped σ fr_spec = some σ_typed
```

**Estimated lines:** ~20-30 (direct application of checkHyp_produces_TypedSubst)

### Integration Point 3: verify_impl_sound Main Theorem

**Current status (lines 2594-2620):** Stated with TODO comments

**Phase 3 completion:** Prove the theorem using:
1. ProofStateInv preservation (stepNormal_preserves_inv)
2. fold induction over proof steps
3. WF propagation through the proof

**Structure:**
```lean
theorem verify_impl_sound (db : Verify.DB) (fr_impl : Verify.Frame)
    (proof : Array String) (target : Verify.Formula) (WFdb : WF db) :
    Verify.DB.verify db fr_impl proof target = true →
    ∃ Γ fr_spec e_spec,
      toDatabase db = some Γ ∧
      toFrame db fr_impl = some fr_spec ∧
      toExpr target = some e_spec ∧
      Spec.Provable Γ fr_spec e_spec := by
  intro h_verify
  -- Unfold verify: runs fold over proof
  -- Base case: ProofStateInv holds for initial state
  -- Inductive case: stepNormal_preserves_inv
  -- Final case: extract Provable from final state
  ...
```

**Dependencies:**
- stepNormal_impl_correct (currently axiomatized, line 2068)
- ProofStateInv preservation
- All view functions (viewState, viewStack, etc.)

**Estimated lines:** ~200-300

---

## Remaining Sorries Analysis

### Category 1: Helper Lemmas (~15 sorries, ~200 lines total)

| Line | Description | Difficulty | Dependency |
|------|-------------|------------|------------|
| 316 | Provability monotonicity | Medium | Spec.Provable properties |
| 400 | Variable in substitution | Easy | varsInExpr unfold |
| 637 | Provability inversion | Hard | Spec.Provable structure |
| 2745 | viewStack correctness | Easy | Array.toList + mapM |
| 2757 | viewStack dropLast | Easy | List operations |
| 3120 | mapM index preservation | Medium | List induction |
| 3124 | list_mapM_length | Easy | Already proven! (line 1614) |
| 3392 | Constant disjointness | Easy | String properties |
| 3400 | toSubst definition | Easy | HashMap unfold |

**Priority:** Category 1 sorries should be filled first (foundation for others).

### Category 2: WF Propagation (~10 sorries, ~150 lines total)

| Line | Description | Difficulty | Phase |
|------|-------------|------------|-------|
| 880 | List distinctness | Easy | 2-3 |
| 897 | Same | Easy | 2-3 |
| 932 | Proof adapt for vars | Medium | 3 |

**Note:** These track WF invariant preservation through database operations.

### Category 3: checkHyp Bridge (~2 sorries, ~120 lines total)

| Line | Description | Difficulty | Phase |
|------|-------------|------------|-------|
| 1906 | checkHyp floats ≈ matchFloats | Hard | 3 |
| 1929 | checkHyp essentials ≈ checkEssentials | Hard | 3 |

**These are the spec-level simulation theorems!** Critical for final soundness.

### Category 4: Stack/Substitution Correctness (~8 sorries, ~100 lines)

| Line | Description | Difficulty | Phase |
|------|-------------|------------|-------|
| 1034 | Stack underflow case | Medium | 3 |
| 1115 | Substitution agreement | Medium | 3 |
| 3359 | For-loop analysis | Easy | 3 |
| 3449 | Final verification | Hard | 3 |

**Note:** These complete the stepAssert proof.

---

## Phase 2 → Phase 3 Dependencies

### What Phase 2 MUST deliver for Phase 3:

1. **✅ checkHyp_preserves_HypProp** (master theorem)
   - Status: Structure adapted (line 1481), needs debugging
   - Why critical: Feeds into ALL other checkHyp theorems
   - Phase 3 blocker: Yes - without this, can't prove checkHyp_produces_typed_coverage

2. **⚠️ checkHyp_images_convert** (theorem 2)
   - Status: Axiomatized (line 1519)
   - Dependencies: mapM_index_some, checkHyp_preserves_HypProp
   - Why critical: Proves all bindings convert to Spec.Expr
   - Phase 3 blocker: Yes - needed for TypedSubst construction

3. **⚠️ checkHyp_domain_covers** (theorem 3)
   - Status: Axiomatized (line 1537)
   - Dependencies: checkHyp_contains_mono, checkHyp_domain_aux
   - Why critical: Proves all floating variables are covered
   - Phase 3 blocker: Yes - needed for TypedSubst construction

4. **⚠️ checkHyp_produces_typed_coverage** (combined)
   - Status: Axiomatized (line 1557)
   - Dependencies: checkHyp_images_convert + checkHyp_domain_covers
   - Why critical: THE KEY THEOREM for TypedSubst
   - Phase 3 blocker: **ABSOLUTE BLOCKER** - This is the bridge!

### What Phase 2 can defer to Phase 3:

1. **TypedSubst structure definition**
   - Can be added in Phase 3 Bridge module
   - Not needed for Phase 2 proofs

2. **toSubstTyped implementation**
   - Can be written in Phase 3
   - checkHyp theorems don't depend on it

3. **Bridge helper lemmas** (floats, essentials, etc.)
   - Can be added in Phase 3
   - checkHyp theorems are independent

4. **Integration theorems** (checkHyp_produces_TypedSubst, etc.)
   - Phase 3 work
   - Build on top of Phase 2 theorems

### Recommended Phase 2 Scope:

**MUST HAVE:**
- ✅ checkHyp_stack_split (done!)
- ⏰ checkHyp_preserves_HypProp (debug and complete)
- ⏰ Helper infrastructure (mapM lemmas, HashMap lemmas, checkHyp_contains_mono, checkHyp_domain_aux)
- ⏰ checkHyp_images_convert (prove using helpers)
- ⏰ checkHyp_domain_covers (prove using helpers)
- ⏰ checkHyp_produces_typed_coverage (combine 2 and 3)

**NICE TO HAVE (can defer):**
- toSubstTyped definition (Phase 3)
- Bridge module structure (Phase 3)
- Integration theorems (Phase 3)

---

## Witness-Carrying Design Patterns (For Phase 2 Work)

### Pattern: Always carry the "success witness"

**Bad:**
```lean
theorem foo (h : convert x = some y) : ... := by
  have h2 : some_property y := sorry  -- Need to re-derive from h!
```

**Good:**
```lean
structure ConvResult (x : Input) where
  y : Output
  converts : convert x = some y
  property : some_property y  -- Witness bundled!

theorem foo (c : ConvResult x) : ... := by
  have h2 : some_property c.y := c.property  -- Direct access!
```

**Application to Phase 2:** When proving checkHyp theorems, bundle witnesses together.

### Pattern: Existential for complex witnesses

**Why FloatBindWitness uses existential (line 1392):**
```lean
def FloatBindWitness (...) : Prop :=
  ∃ (hj : j < hyps.size) (k : Fin stack.size) ...,
    ...
```

**Reason:** Lean 4 Prop-valued structures can't have data fields. Existential quantification provides the witness without creating a data structure.

**When to use:** Whenever you need to carry index bounds or other "proof-relevant" data in a Prop.

### Pattern: Thread invariants through recursion

**checkHyp_preserves_HypProp pattern:**
```lean
theorem checkHyp_preserves_HypProp (hi : i ≤ hyps.size) (hprop : HypProp i subst) ... :
    HypProp hyps.size σ := by
  -- Strong induction on (hyps.size - i)
  have main : ∀ k, hyps.size - i = k → ... := by
    intro k
    induction k with
    | zero => ... -- Base: i = hyps.size
    | succ k ih => ... -- Step: use ih with i+1
  exact main (hyps.size - i) rfl
```

**Why this works:** Lean's termination checker sees `hyps.size - i` decreasing.

**Application:** Use this pattern for all auxiliary recursive lemmas (checkHyp_contains_mono, checkHyp_domain_aux).

---

## Summary: What Phase 2 Must Build

### High Priority (Blockers for Phase 3):

1. **checkHyp_preserves_HypProp proof** (~130 lines)
   - Current: Structure adapted, type mismatches
   - Action: Debug and complete

2. **Helper lemma infrastructure** (~200 lines)
   - mapM_index_some
   - checkHyp_contains_mono
   - checkHyp_domain_aux
   - HashMap utilities

3. **checkHyp_images_convert proof** (~60 lines)
   - Dependencies: helpers above + checkHyp_preserves_HypProp

4. **checkHyp_domain_covers proof** (~60 lines)
   - Dependencies: helpers above + checkHyp_preserves_HypProp

5. **checkHyp_produces_typed_coverage proof** (~30 lines)
   - Dependencies: theorems 2 and 3 above
   - **THIS IS THE CRITICAL PATH TO PHASE 3!**

**Total Phase 2 remaining:** ~480 lines

### Can Defer to Phase 3:

- Bridge module creation
- TypedSubst definition
- toSubstTyped implementation
- Integration theorems
- Remaining sorries (categories 1-4)
- Main verification theorem

**Total Phase 3:** ~1000 lines (but builds cleanly on Phase 2 foundation)

---

## Conclusion

**Key insight:** Phase 2 should focus on **proving the checkHyp theorem stack completely**. This creates a solid foundation with NO axioms remaining for the checkHyp→TypedSubst pipeline.

Phase 3 can then:
1. Add the thin Bridge module (definitions only)
2. Implement toSubstTyped using the proven checkHyp theorems
3. Integrate everything with the main verification proof
4. Clean up remaining sorries

**The witness-carrying patterns we need are ALREADY in place:**
- FloatBindWitness ✅
- HypProp ✅
- WF ✅
- ProofStateInv ✅

**What we need to complete is the PROOFS that connect them!**

---

**Date:** 2025-10-13
**Next action:** Resume Phase 2 with full context of Phase 3 requirements
**Priority:** Debug checkHyp_preserves_HypProp, then add helper infrastructure
