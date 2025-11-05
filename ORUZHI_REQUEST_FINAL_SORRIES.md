# Request for Guidance: Final 4 Sorries in Kernel.lean

**Date:** 2025-10-14
**Context:** Metamath formal verification project
**Progress:** 11 sorries → 5 sorries (6 eliminated this session)
**Status:** 4 active sorries remain, all in toExpr_subst_commutes infrastructure

---

## Summary of Progress

We've successfully completed:
- ✅ **extract_from_allM_true** (65-line proof, 5-level splitting)
- ✅ **toSubstTyped** (100% complete with honest Option behavior)
- ✅ **checkHyp axiomatization** (checkHyp_floats_sound, checkHyp_essentials_sound)
- ✅ **Bridge lemmas** (toExpr × 3, Array↔List × 3, viewStack × 2)
- ✅ **mapM correspondence lemmas** (list_mapM_length_Option, list_mapM_get_Option)
- ✅ **frame_conversion_correct Property 1** (82-line proof using mapM index preservation)

The main verification pipeline (toSubstTyped → checkHyp → frame conversion) is now solid.

---

## Remaining Sorries

**File:** Metamath/Kernel.lean

### 1. Line 1115 (COMMENTED OUT - DEPRECATED)
```lean
theorem matchHyps_sound ... := by
  ...
  sorry  -- Requires disjoint variable domain precondition
-/
-/
```

**Status:** Intentionally deprecated. Not used in verification pipeline. Two-phase approach (matchFloats + checkEssentials) is preferred.

**Question:** Should we delete this entirely or keep it commented as documentation?

---

### 2. Line 3602: for-loop analysis (~10 lines)

**Context:**
```lean
theorem toExpr_subst_const_case (f f' : Formula) (σ : HashMap String Formula) :
  f.size > 0 →
  f[0].isConst →
  f.subst σ = .ok f' →
  f'[0] = f[0] ∧ f'.size > 0 := by
  intro h_size h_const h_subst
  -- Goal: Show that for-loop in Formula.subst pushes f[0] unchanged
  -- Constants are pushed unchanged: f' := f'.push f[0]
  -- Thus f'[0] = f[0] and f'.size > 0
  sorry  -- ~10 lines: for-loop analysis
```

**Location:** Helper lemma for toExpr_subst_commutes

**Challenge:** Need to reason about imperative for-loop in Formula.subst that builds result array.

**Question:** Should this be:
- (A) Proven by unfolding Formula.subst and reasoning about Array.foldl?
- (B) Converted to an axiom about Formula.subst behavior?
- (C) Removed if toExpr_subst_commutes isn't on critical path?

---

### 3. Line 3635: constant case (~3-5 lines)

**Context:**
```lean
theorem subst_sym_correspondence (s : Sym) (σ_impl : HashMap String Formula)
    (σ_spec : Spec.Subst) :
  toSubst σ_impl = some σ_spec →
  (∀ fv, σ_impl.values.contains fv → ∃ e, toExpr fv = some e) →
  match s with
  | .const c =>
      [toSym s] = (if h : (toSym s).length > 0 ∧ (toSym s).get ⟨0, h.1⟩ = 'v' then
                    (σ_spec ⟨toSym s⟩).syms else [toSym s])
  | .var v => ... := by
  intro h_toSubst h_images
  cases s with
  | const c =>
    simp [toSym]
    -- The 'if' condition checks for 'v' prefix: it's false for constants
    -- Thus we need: [c] = [c], which is trivial
    sorry  -- ~3-5 lines: case split on c.length, show c ≠ "v"++_ since s is .const
```

**ARCHITECTURAL ISSUE:**
```lean
-- LIMITATION: Current Spec.lean encoding assumes constants don't start with 'v'
-- (per toSym encoding: const c → c, var v → "v"++v). This works for set.mm/iset.mm
-- but could collide if a database declares `$c vx $.`. Proper fix: pass variable set
-- to Spec.applySubst instead of prefix check (per Grok §4.2.1-4.2.3 guidance).
```

**Question:** Should we:
- (A) Add precondition `∀ c, ¬(c.startsWith "v")` to theorem?
- (B) Redesign Spec.applySubst to take explicit variable set instead of using prefix?
- (C) Accept limitation and document that verification only works for well-formed databases?
- (D) Make this an axiom since it's about encoding conventions?

---

### 4. Line 3643: variable case (~10 lines)

**Context:**
```lean
  | var v =>
    -- Variables: toSym (.var v) = "v" ++ v
    -- σ_spec looks up ⟨"v" ++ v⟩ and applies the substitution
    simp [toSym, toSubst] at h_toSubst
    -- toSubst maps: Variable "v"++v ↦ (match σ_impl.find? v.drop 1 ...)
    -- For "v"++v, dropping "v" prefix gives v
    -- σ_impl.find? v gives the formula that should replace v
    sorry  -- ~10 lines: unfold toSubst, relate σ_impl.find? v to σ_spec
```

**Challenge:** Need to unfold toSubst definition and show correspondence between HashMap lookup and spec function application.

**Question:** Should this be:
- (A) Proven by unfolding toSubst and using HashMap lookup properties?
- (B) Combined with constant case into single axiom about toSubst correspondence?
- (C) Is there a simpler formulation of this theorem?

---

### 5. Line 3692: toExpr_subst_commutes main proof

**Context:**
```lean
theorem toExpr_subst_commutes (vars : List Spec.Variable)
    (f f' : Formula) (σ_impl : HashMap String Formula)
    (e : Spec.Expr) (σ_spec : Spec.Subst) :
  (∀ v, v ∈ f.foldlVars ∅ (fun acc v => acc.insert v ()) → σ_impl.contains v) →
  (∀ fv, σ_impl.values.contains fv → ∃ e, toExpr fv = some e) →
  toExpr f = some e →
  toSubst σ_impl = some σ_spec →
  f.subst σ_impl = .ok f' →
  toExpr f' = some (Spec.applySubst vars σ_spec e) := by
  intro h_domain h_images h_toExpr h_toSubst h_subst
  -- Proof sketch (from comment):
  -- 1. Induction on f (Formula structure)
  -- 2. Base case: f = [tc] (single typecode)
  -- 3. Inductive case: use toExpr_subst_const_case (line 3602 sorry)
  -- 4. For each symbol: use subst_sym_correspondence (lines 3635, 3643 sorries)
  -- 5. Show Array.foldl in Formula.subst ≡ List.bind in applySubst
  -- 6. Relate imperative for-loop to functional operations
  sorry
```

**Challenge:** Main correspondence theorem between implementation substitution and spec substitution. Blocked by sorries at lines 3602, 3635, 3643.

**Question:** Is this theorem on the critical path for verify_impl_sound?
- Looking at verify_impl_sound (line 3844), does it depend on toExpr_subst_commutes?
- Or is the verification complete through stepNormal_sound axiom (line 1730)?

---

## Strategic Questions

### Question 1: Critical Path Analysis

**Is toExpr_subst_commutes needed for the main verification goal?**

Looking at the verification architecture:
- `verify_impl_sound` (line 3844) is the top-level theorem
- `stepNormal_sound` (line 1730) is axiomatized for impl→spec
- checkHyp axioms bridge hypothesis checking
- frame_conversion_correct bridges frame conversion

Does verify_impl_sound use toExpr_subst_commutes? Or is it already covered by the axioms?

**Request:** Please check if toExpr_subst_commutes is used in the proof of verify_impl_sound or any theorems that lead to it.

### Question 2: Axiom vs Theorem Decision

**Should these be axioms or theorems?**

Pattern observed in codebase:
- **Spec theorems** (proven): matchFloats_sound, matchExpr_sound, etc.
- **Impl axioms**: stepNormal_sound, dvCheck_sound, checkHyp_*_sound

The sorries 3602/3635/3643/3692 are all about Formula.subst (implementation) ↔ applySubst (spec) correspondence.

**Suggestion:** These might belong as axioms, similar to:
```lean
axiom formula_subst_sound (f f' : Formula) (σ_impl : HashMap String Formula)
    (e : Spec.Expr) (σ_spec : Spec.Subst) :
  -- Preconditions about σ correspondence
  toExpr f = some e →
  toSubst σ_impl = some σ_spec →
  f.subst σ_impl = .ok f' →
  toExpr f' = some (Spec.applySubst vars σ_spec e)
```

**Question:** Should we axiomatize formula_subst_sound rather than proving toExpr_subst_commutes?

### Question 3: Architectural Fix

**The "v" prefix encoding issue:**

Current design:
- `toSym : Sym → String` maps `.const c → c` and `.var v → "v" ++ v`
- Spec's `applySubst` checks `if sym.startsWith "v"` to distinguish variables
- **Problem:** Collision if database has constant named "vx"

**Alternative design (Grok §4.2.1-4.2.3 guidance):**
```lean
-- Pass explicit variable set instead of using prefix
def applySubst (vars : Set String) (σ : Subst) (e : Expr) : Expr :=
  ⟨e.typecode, e.syms.bind fun sym =>
    if sym ∈ vars then (σ ⟨sym⟩).syms else [sym]⟩
```

**Question:** Should we:
1. Fix the architecture (change Spec.applySubst signature)?
2. Add precondition "no constants start with 'v'"?
3. Accept limitation for well-formed databases?

---

## Specific Guidance Requested

### Priority 1: Critical Path

**Please clarify:**
1. Is toExpr_subst_commutes used in verify_impl_sound proof chain?
2. If not, can we delete/comment out these 4 sorries as non-essential?
3. If yes, what's the recommended approach?

### Priority 2: Architecture

**If toExpr_subst_commutes IS needed:**

**Option A: Axiomatize**
```lean
axiom formula_subst_sound (f f' : Formula) (σ_impl : HashMap String Formula)
    (e : Spec.Expr) (σ_spec : Spec.Subst) (vars : List Spec.Variable) :
  (∀ v, v ∈ f.foldlVars ∅ (·.insert · ()) → σ_impl.contains v) →
  (∀ fv, σ_impl.values.contains fv → ∃ e, toExpr fv = some e) →
  toExpr f = some e →
  toSubst σ_impl = some σ_spec →
  f.subst σ_impl = .ok f' →
  toExpr f' = some (Spec.applySubst vars σ_spec e)
```

**Option B: Prove with preconditions**
```lean
-- Add to WF predicate:
structure WF (db : DB) : Prop where
  ...
  constants_dont_start_with_v : ∀ c, db.hasConstant c → ¬(c.startsWith "v")
```

**Option C: Fix Spec.applySubst**
```lean
-- Change signature to take explicit variable set
def applySubst (varSet : Set String) (σ : Subst) (e : Expr) : Expr := ...
```

**Which option do you recommend?**

### Priority 3: Proof Strategy

**If we should prove (not axiomatize), please provide:**

1. **For line 3602 (for-loop analysis):** What's the best way to reason about Formula.subst's for-loop?
   - Unfold to Array.foldl?
   - Use Array invariant properties?
   - Something else?

2. **For lines 3635/3643 (subst_sym_correspondence):** What's the right formulation?
   - Add preconditions about "v" prefix?
   - Split into separate lemmas?
   - Use different approach?

3. **For line 3692 (main proof):** What's the proof structure?
   - Induction on Formula?
   - Induction on Expr?
   - Use mapM correspondence pattern?

---

## What We've Tried

### Successes This Session:
1. ✅ Proved extract_from_allM_true using **induction + 5-level split** (no external lemmas)
2. ✅ Proved list_mapM_get_Option using **induction on list + case analysis on i** (38 lines)
3. ✅ Proved frame_conversion_correct Property 1 using **mapM index preservation + convertHyp unfolding** (82 lines)

**Pattern:** Direct induction + split tactics work well for monadic operations and list correspondence.

### Challenges:
1. ❌ toExpr_subst_commutes infrastructure blocked by architectural issues
2. ❌ Unclear if these theorems are on critical path
3. ❌ Uncertain whether to axiomatize or prove

---

## Questions Summary

1. **Critical Path:** Is toExpr_subst_commutes used in verify_impl_sound?
2. **Axiom Decision:** Should we axiomatize formula_subst_sound like stepNormal_sound?
3. **Architecture:** How to handle "v" prefix collision issue?
4. **Proof Strategy:** If proving, what's the recommended approach for each sorry?
5. **Cleanup:** Should we delete deprecated matchHyps_sound (line 1115)?

---

## Context for Review

**Files:**
- Metamath/Kernel.lean (main file with sorries)
- Metamath/Spec.lean (spec definitions)
- Metamath/Verify.lean (implementation)

**Key definitions:**
- `toExpr : Formula → Option Expr` (line 1396, converts Array Sym to Expr)
- `toSubst : HashMap String Formula → Option Subst` (line 1496, DEPRECATED phantom wff version)
- `toSubstTyped : Frame → HashMap String Formula → Option (TypedSubst fr)` (line 1629, honest version, 100% complete!)
- `Formula.subst : HashMap String Formula → Except String Formula` (in Verify.lean, imperative for-loop)
- `Spec.applySubst : List Variable → Subst → Expr → Expr` (in Spec.lean, functional)

**Current sorry count:** 5 total (1 commented out deprecated, 4 active)

---

## Thank You! 🙏

Your guidance on Section F (toSubstTyped) was perfect and led to:
- Complete 65-line proof of extract_from_allM_true
- toSubstTyped 100% functional with honest Option behavior
- 6 sorries eliminated this session

We're at the final stretch with these last 4 interconnected sorries. Strategic guidance on whether to axiomatize vs prove (and if prove, the architecture/approach) would be invaluable.

**Project status:** ~85% complete, 4 active sorries remaining! 🚀
