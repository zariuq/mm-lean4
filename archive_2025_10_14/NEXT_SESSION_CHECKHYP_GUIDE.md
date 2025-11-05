# Next Session Guide: CheckHyp Integration

**Priority:** HIGH - Core soundness path
**Estimated Time:** 4-8 hours
**Prerequisites:** matchFloats_sound already proven ✅

---

## Overview

Connect the implementation's `checkHyp` function to the spec-level `matchFloats` and `checkEssentials` functions. This is a critical step in the verification pipeline.

---

## Current Issues

### 1. Theorem Statement Type Errors

**checkHyp_floats_sound (Line 1677):**
```lean
-- BROKEN:
floats_spec.map (fun (tc, v) => σ_spec v) =
  (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e)
--  ^^^^ List Expr        ^^^^ Prop (type mismatch!)
```

**Should be:**
```lean
floats_spec.map (fun (tc, v) => σ_spec v) = stack_spec
-- where stack_spec is converted from stack[off..off+hyps.size]
```

**Similar issue in checkHyp_essentials_sound (Line 1699-1700)**

---

## Required Infrastructure

### Bridge Functions (Need to verify these exist)

1. **toExpr**: `Formula → Option Expr`
   - Converts implementation Formula to spec Expr
   - Location: Search for `def toExpr`

2. **toSubst**: `HashMap String Formula → Option Subst`
   - Converts implementation substitution to spec substitution
   - Location: Search for `def toSubst`

3. **toFrame**: `Verify.Frame → Option Spec.Frame`
   - Converts implementation Frame to spec Frame
   - Location: Search for `def toFrame`

### Helper Lemmas Needed

1. **Array/List Correspondence:**
   - `Array.toList` properties
   - `Array.extract` correspondence
   - Index preservation lemmas

2. **Conversion Lemmas:**
   - `toExpr` preserves structure
   - `toSubst` preserves mapping
   - Composition properties

3. **allM Lemmas** (from Session 6):
   - `allM_mapM_some`: Connect allM to mapM
   - These should already exist!

---

## Strategy for checkHyp_floats_sound

### Step 1: Fix Theorem Statement (30 min)

```lean
theorem checkHyp_floats_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : Nat)
    (subst_impl : Std.HashMap String Metamath.Verify.Formula) :
  -- Precondition: hyps are all floating hypotheses
  (∀ i < hyps.size,
    ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with
    | .hyp false f _ => True  -- floating
    | _ => False) →
  -- Precondition: checkHyp succeeds
  checkHyp db hyps stack off 0 subst_impl = some subst_impl' →
  -- Then there exists a spec-level correspondence
  ∃ (floats_spec : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (stack_spec : List Metamath.Spec.Expr)
    (σ_spec : Metamath.Spec.Subst),
    -- Conversions succeed
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e ∧ stack_spec[i] = e) ∧
    toSubst subst_impl' = some σ_spec ∧
    -- matchFloats would succeed with same result
    matchFloats floats_spec stack_spec = some σ_spec ∧
    -- And matchFloats_sound applies
    floats_spec.map (fun (tc, v) => σ_spec v) = stack_spec := by
  sorry
```

### Step 2: Proof Outline (2-3 hours)

1. **Extract floats_spec from hyps:**
   - For each hyp in hyps, look up in db
   - Extract (typecode, variable) pairs
   - Build List (Constant × Variable)

2. **Extract stack_spec from stack:**
   - For each i < hyps.size, convert stack[off + i] using toExpr
   - Build List Expr

3. **Show checkHyp ≈ matchFloats:**
   - checkHyp for floats iterates through hyps
   - Binds each variable to corresponding stack entry
   - This is exactly what matchFloats does!

4. **Apply matchFloats_sound:**
   - We already proved this! ✅
   - Just need to connect implementation to spec

### Step 3: Key Lemmas to Prove (1-2 hours)

```lean
-- checkHyp on floats builds substitution equivalently to matchFloats
lemma checkHyp_floats_equiv_matchFloats :
  ∀ floats stack subst_impl subst_impl',
    checkHyp_floats_only floats stack = some subst_impl' →
    ∃ floats_spec stack_spec σ_spec,
      convertFloats floats = some floats_spec ∧
      convertStack stack = some stack_spec ∧
      toSubst subst_impl' = some σ_spec ∧
      matchFloats floats_spec stack_spec = some σ_spec
```

---

## Strategy for checkHyp_essentials_sound

### Step 1: Fix Theorem Statement (30 min)

```lean
theorem checkHyp_essentials_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : Nat)
    (subst_impl : Std.HashMap String Metamath.Verify.Formula)
    (vars : List Metamath.Spec.Variable) :
  -- Precondition: hyps are all essential hypotheses
  (∀ i < hyps.size,
    ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with
    | .hyp true f _ => True  -- essential
    | _ => False) →
  -- Precondition: checkHyp succeeds (checking mode, no new bindings)
  checkHyp db hyps stack off 0 subst_impl = some subst_impl →
  -- Then checkEssentials succeeds
  ∃ (essentials_spec : List Metamath.Spec.Expr)
    (stack_spec : List Metamath.Spec.Expr)
    (σ_spec : Metamath.Spec.Subst),
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e ∧ stack_spec[i] = e) ∧
    toSubst subst_impl = some σ_spec ∧
    checkEssentials vars σ_spec essentials_spec stack_spec = true := by
  sorry
```

### Step 2: Proof Outline (2-3 hours)

1. **Extract essentials_spec:** Convert essential hypothesis expressions

2. **Extract stack_spec:** Convert stack entries

3. **Show checkHyp checking ≈ checkEssentials:**
   - checkHyp for essentials checks: `f.subst σ == stack[i]`
   - checkEssentials checks: `applySubst σ e_hyp == stack_spec[i]`
   - These are equivalent operations!

4. **Use equality decidability:**
   - Both use boolean equality
   - Just need to show conversion preserves equality

---

## Quick Wins First Approach

### Option A: Start with Simpler Bridge Lemmas

Before tackling checkHyp theorems, prove:

1. **toExpr preserves equality** (30 min):
   ```lean
   lemma toExpr_preserves_eq (f1 f2 : Formula) (e1 e2 : Expr) :
     toExpr f1 = some e1 → toExpr f2 = some e2 →
     (f1 == f2) = true ↔ e1 = e2
   ```

2. **toSubst preserves lookup** (1 hour):
   ```lean
   lemma toSubst_lookup (σ_impl : HashMap String Formula) (σ_spec : Subst) (v : Variable) :
     toSubst σ_impl = some σ_spec →
     ∃ f e, σ_impl[v.v] = some f ∧ toExpr f = some e ∧ σ_spec v = e
   ```

3. **Array slice conversion** (1 hour):
   ```lean
   lemma array_slice_toList (arr : Array α) (off len : Nat) :
     (arr.extract off (off + len)).toList = (arr.toList).drop off |>.take len
   ```

These build foundation for main theorems.

---

## Dependencies to Check

### Search for existing definitions:
```bash
grep -n "def toExpr" Metamath/Kernel.lean
grep -n "def toSubst" Metamath/Kernel.lean
grep -n "def checkHyp" Metamath/Verify.lean
grep -n "def matchFloats" Metamath/Kernel.lean  # Should be ~line 1139
grep -n "def checkEssentials" Metamath/Kernel.lean  # Should be ~line 1158
```

### Search for existing lemmas:
```bash
grep -n "allM_mapM_some" Metamath/Kernel.lean
grep -n "toExpr.*preserves" Metamath/Kernel.lean
```

---

## Success Criteria

### Minimum (2 hours):
- ✅ Fix theorem statements so they type-check
- ✅ Outline proof strategy with sorry placeholders
- ✅ Identify all needed bridge lemmas

### Good (4-6 hours):
- ✅ Above +
- ✅ Prove 2-3 key bridge lemmas
- ✅ Partial proof of checkHyp_floats_sound

### Excellent (6-8 hours):
- ✅ Above +
- ✅ Complete checkHyp_floats_sound proof
- ✅ Significant progress on checkHyp_essentials_sound
- ✅ Eliminate 1-2 sorries

---

## Potential Blockers

1. **Missing Bridge Functions:**
   - If toExpr/toSubst don't exist or are incomplete
   - Solution: Define them or use axioms temporarily

2. **checkHyp Implementation Unknown:**
   - Need to read Verify.lean to understand implementation
   - Solution: Study implementation before proving

3. **Complex Type Conversions:**
   - Array vs List, HashMap vs Function
   - Solution: Build up lemma library gradually

---

## Recommended Session Plan

### Phase 1: Investigation (30-60 min)
1. Search for existing definitions (toExpr, toSubst, checkHyp)
2. Read checkHyp implementation in Verify.lean
3. Check what bridge lemmas already exist
4. Update theorem statements to type-check

### Phase 2: Foundation (2-3 hours)
1. Prove toExpr preservation lemmas
2. Prove toSubst correspondence lemmas
3. Prove Array/List slice lemmas

### Phase 3: Main Theorems (2-4 hours)
1. Start with checkHyp_floats_sound
2. Use matchFloats_sound (already proven!)
3. Connect implementation to spec step-by-step

### Phase 4: Polish (1 hour)
1. Document remaining gaps
2. Create clear sorry comments
3. Update progress tracking

---

## Resources Available

- ✅ **matchFloats_sound**: Already proven! Can be used directly
- ✅ **checkEssentials definition**: Already exists (~line 1158)
- ✅ **Nodup patterns**: Proven to work well
- ✅ **Helper lemmas**: 5 lemmas from Oruži ready to use
- ✅ **Session 6 work**: allM lemmas should be available

---

## Expected Outcome

**Optimistic:** Eliminate 1-2 sorries (lines 1691 or 1714)
**Realistic:** Fix theorem statements, prove 2-3 bridge lemmas, outline main proofs
**Minimum:** Clear understanding of what's needed and type-correct theorem statements

---

## Bottom Line

CheckHyp integration is **HIGH VALUE** work that directly advances core soundness. The infrastructure (matchFloats_sound, helper lemmas) is in place. Main challenge is connecting implementation types to spec types through bridge lemmas.

**Start with:** Fix theorem statements → Prove simple bridge lemmas → Build up to main theorems

**Key insight:** We can leverage our proven matchFloats_sound theorem - the hard proof work is already done! Just need to show the implementation corresponds to it.

Good luck! 🚀🐢✨
