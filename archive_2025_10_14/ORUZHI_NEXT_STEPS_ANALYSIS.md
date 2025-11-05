# Analysis: Implementing Oruži's Section F Guidance

**Date:** 2025-10-14 (Continued)
**Context:** Applied Oruži's Solutions A, B, E - now ready for next steps
**Goal:** Complete toSubstTyped and checkHyp integration using Oruži's Section F pattern

---

## What We've Found

### 1. ✅ Bridge Module Infrastructure EXISTS

**Location:** `Metamath/Bridge/Basics.lean` (~250 lines)

**Key Components:**
```lean
-- Core type for well-typed substitutions
structure TypedSubst (fr : Spec.Frame) where
  σ : Spec.Subst
  typed : ∀ {c v}, Hyp.floating c v ∈ fr.mand → (σ v).typecode = c

-- Helper functions
def floats (fr : Spec.Frame) : List (Constant × Variable)
def essentials (fr : Spec.Frame) : List Expr
def needed (vars : List Variable) (fr : Spec.Frame) (σ : Subst) : List Expr
def needOf (vars : List Variable) (σ : Subst) (h : Hyp) : Expr

-- Simple lemmas (ALL PROVEN ✅)
theorem floats_complete ...
theorem floats_sound ...
theorem essentials_complete ...
theorem essentials_sound ...
theorem needed_length ...
```

**Status:** ✅ Complete! All simple lemmas proven.

### 2. ✅ Bridge Functions (toExpr, toSubst) EXIST

**Location:** `Metamath/Kernel.lean` lines 1394-1418

```lean
-- Convert implementation Formula to spec Expr
def toExpr (f : Verify.Formula) : Option Spec.Expr :=
  if h : f.size > 0 then
    let typecode : Spec.Constant := ⟨f[0].value⟩
    let syms := f.toList.tail.map toSym
    some ⟨typecode, syms⟩
  else none

-- Convert HashMap substitution to spec function (with phantom wff fallback)
def toSubst (σ_impl : HashMap String Verify.Formula) : Option Spec.Subst :=
  some (fun v : Spec.Variable =>
    match σ_impl[v.v.drop 1]? with  -- Drop "v" prefix
    | some f =>
        match toExpr f with
        | some e => e
        | none => ⟨⟨"wff"⟩, [v.v]⟩  -- Fallback: phantom identity
    | none => ⟨⟨"wff"⟩, [v.v]⟩)       -- Fallback: phantom identity
```

**Key Issue:** toSubst has phantom wff fallback! This is what TypedSubst fixes.

### 3. ✅ checkHyp Implementation FOUND

**Location:** `Metamath/Verify.lean` lines 401-418

```lean
variable (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) in
def checkHyp (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(...)
    if let some (.hyp ess f _) := db.find? hyps[i] then
      if f[0]! == val[0]! then  -- Check typecode match
        if ess then
          -- Essential hypothesis: check f[subst] == val
          if (← f.subst subst) == val then
            checkHyp (i+1) subst  -- No change to subst
          else throw "type error in substitution"
        else
          -- Floating hypothesis: bind f[1]! (variable name) to val
          checkHyp (i+1) (subst.insert f[1]!.value val)
      else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
    else unreachable!
  else pure subst
```

**Key Properties:**
- Recursively processes hypotheses from index i to hyps.size
- For floating hyps: `subst.insert f[1]!.value val` (binds variable to expression)
- For essential hyps: checks `f.subst subst == val` (no new bindings)
- Returns final HashMap or error

---

## What We DON'T Have Yet

### ❌ toSubstTyped - Not Implemented

**Expected location:** Kernel.lean (not found!)

**What it should do:**
```lean
-- This is what Oruži's Section F describes
def toSubstTyped (floats : List (Constant × Variable))
    (σ_impl : HashMap String Verify.Formula) : Option TypedSubst :=
  match float_list.allM (checkFloat σ_impl) with
  | some true =>
      -- Build TypedSubst with witness
      some ⟨σ_fn, proof_of_typing⟩
  | _ => none
```

**Oruži's Pattern (Section F):**
```lean
match hAll : float_list.allM (checkFloat σ_impl) with
| some true =>
  let σ_fn : Spec.Subst := fun v => ...
  exact some ⟨σ_fn, by
    intro c v h_float
    have h_in : (c, v) ∈ float_list := ...
    rcases extract_from_allM_true float_list σ_impl hAll c v h_in with
      ⟨f, e, hlook, hconv, htc⟩
    dsimp [σ_fn]
    simp [hlook, hconv, htc]
  ⟩
| _ => none
```

---

## Comparison: Current vs Needed Architecture

### Current Architecture (Kernel.lean lines 1408-1417)
```lean
def toSubst (σ_impl : HashMap String Formula) : Option Subst :=
  some (fun v =>
    match σ_impl[v.v.drop 1]? with
    | some f => match toExpr f with
                | some e => e
                | none => ⟨⟨"wff"⟩, [v.v]⟩  -- PHANTOM!
    | none => ⟨⟨"wff"⟩, [v.v]⟩)              -- PHANTOM!
```

**Problem:** Always returns `some`, uses phantom wff on errors!

### Target Architecture (with Bridge/TypedSubst)
```lean
def toSubstTyped (fr : Spec.Frame) (σ_impl : HashMap String Formula)
    : Option (TypedSubst fr) :=
  let floats := Bridge.floats fr
  match floats.allM (checkFloat σ_impl) with
  | some true =>
      -- Can prove typing witness!
      some ⟨σ_fn, proof_that_types_match⟩
  | _ => none  -- Honest failure!
```

**Benefits:**
- No phantom values!
- Honest Option behavior
- Type safety guaranteed by witness

---

## Bridge Lemmas We Need (From Oruži's Guidance)

### 1. toExpr Properties

```lean
-- Equality preservation (Q3 from AI_REQUEST_QUICK.md)
lemma toExpr_eq_iff :
  toExpr f1 = some e1 → toExpr f2 = some e2 →
  (f1 == f2) ↔ e1 = e2 := by sorry

-- Typecode preservation
lemma toExpr_typecode :
  toExpr f = some e → e.typecode = ⟨f[0].value⟩ := by sorry

-- Success conditions
lemma toExpr_success :
  toExpr f = some e ↔ f.size > 0 := by sorry
```

### 2. toSubst Properties (Q4 from AI_REQUEST_QUICK.md)

```lean
-- Lookup correspondence (BUT: toSubst is phantom!)
-- Better: prove properties of toSubstTyped when we build it

-- What we can prove about current toSubst:
lemma toSubst_phantom_behavior :
  toSubst σ_impl = some σ_spec →
  ∀ v, ∃ e, σ_spec v = e ∧
    (∃ f, σ_impl[v.v.drop 1]? = some f ∧ toExpr f = some e) ∨
    e = ⟨⟨"wff"⟩, [v.v]⟩  -- Fallback case
  := by sorry
```

### 3. checkHyp ≈ matchFloats Correspondence (Q2, Q3 from AI_REQUEST_QUICK.md)

```lean
-- This is what checkHyp_floats_sound should prove!
theorem checkHyp_produces_matchFloats
    (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : Nat) (subst_init subst_result : HashMap String Formula) :
  (∀ i < hyps.size, ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with | .hyp false f _ => True | _ => False) →
  checkHyp db hyps stack off 0 subst_init = Except.ok subst_result →
  ∃ (floats_spec : List (Constant × Variable))
    (stack_spec : List Expr)
    (σ_spec : Subst),
    -- Conversions succeed
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e ∧
      stack_spec[i]? = some e) ∧
    toSubst subst_result = some σ_spec ∧
    -- Spec-level correspondence
    matchFloats floats_spec stack_spec = some σ_spec ∧
    floats_spec.map (fun (tc, v) => σ_spec v) = stack_spec := by
  sorry
```

**Note:** This is EXACTLY the corrected checkHyp_floats_sound statement (lines 1652-1683)!

### 4. Array ↔ List Correspondences (Q5 from AI_REQUEST_QUICK.md)

```lean
-- Indexed access correspondence
lemma Array.get_toList :
  ∀ i h, arr.toList[i] = arr[i] := by sorry

-- Quantifier equivalences
lemma Array.forall_iff_toList :
  (∀ i < arr.size, P arr[i]) ↔ (∀ x ∈ arr.toList, P x) := by sorry

-- Extract/slice correspondence
lemma Array.extract_eq_drop_take :
  (arr.extract off len).toList = arr.toList.drop off |>.take len := by sorry
```

---

## Next Steps (Priority Order)

### Phase 1: Understand Current State (15 min)

1. ✅ **DONE:** Found all key functions
2. ✅ **DONE:** Found Bridge module infrastructure
3. ✅ **DONE:** Understood checkHyp implementation
4. **NEXT:** Check if Kernel.lean imports Bridge

```bash
grep -n "import.*Bridge" Metamath/Kernel.lean
```

### Phase 2: Apply Oruži's Section F Pattern (1-2 hours)

**Goal:** Implement toSubstTyped using allM pattern

**Steps:**
1. Define `checkFloat` helper function
2. Define `extract_from_allM_true` lemma
3. Implement `toSubstTyped` using Oruži's match pattern
4. Prove typing witness using extracted facts

**Expected difficulty:** Medium (need to understand allM in Lean 4.20)

### Phase 3: Prove Bridge Lemmas (2-3 hours)

**Priority order (from Oruži's guidance):**
1. toExpr_typecode (easy, direct)
2. toExpr_success (easy, if-then-else)
3. Array.get_toList (medium, Batteries lemma)
4. Array.forall_iff_toList (medium, induction on indices)
5. toExpr_eq_iff (harder, BEq reasoning)

### Phase 4: Complete checkHyp Theorems (3-4 hours)

**Using corrected statements from lines 1652-1715:**
1. Prove checkHyp iteration corresponds to matchFloats recursion
2. Extract floats_spec from db lookups
3. Convert stack using toExpr
4. Show substitutions correspond
5. Apply matchFloats_sound (already proven!)

---

## Key Insights from Code Analysis

### 1. checkHyp is Tail-Recursive

```lean
def checkHyp (i : Nat) (subst : HashMap) : Except String HashMap := do
  if h : i < hyps.size then
    ...
    checkHyp (i+1) (updated_subst)
  else pure subst
```

**Implications:**
- Can prove by strong induction on `hyps.size - i`
- Base case: `i >= hyps.size` returns subst unchanged
- Inductive case: processes hyps[i], recurses on i+1

### 2. Floating Hypothesis Format

From checkHyp line 415:
```lean
checkHyp (i+1) (subst.insert f[1]!.value val)
```

**Key fact:** f[1]! is the variable name for floating hyps!
- f[0]! = typecode (checked against val[0]!)
- f[1]! = variable name (inserted into HashMap)

### 3. TypedSubst Eliminates Phantom Behavior

**Old toSubst:**
- Always returns `some σ`
- Uses `⟨⟨"wff"⟩, [v.v]⟩` fallback on missing variables
- LIES about success!

**New toSubstTyped:**
- Returns `Option (TypedSubst fr)`
- Can only be constructed if all floats have correct types
- Honest about failures!

---

## Oruži's Section F Pattern - Complete Reference

```lean
-- Helper: check a single float
def checkFloat (σ_impl : HashMap String Formula)
    (float : Constant × Variable) : Option Bool :=
  let (tc, v) := float
  match σ_impl[v.v]? with  -- Look up variable
  | some f =>
      match toExpr f with   -- Convert to expr
      | some e =>
          -- Check typecode matches
          if e.typecode = tc then some true else some false
      | none => none
  | none => none

-- Helper: extraction lemma
lemma extract_from_allM_true (floats : List (Constant × Variable))
    (σ_impl : HashMap String Formula)
    (hAll : floats.allM (checkFloat σ_impl) = some true)
    (c : Constant) (v : Variable)
    (h_in : (c, v) ∈ floats) :
    ∃ (f : Formula) (e : Expr),
      σ_impl[v.v]? = some f ∧
      toExpr f = some e ∧
      e.typecode = c := by
  sorry  -- TODO: prove using allM properties

-- Main function using Oruži's pattern
def toSubstTyped (fr : Spec.Frame) (σ_impl : HashMap String Formula)
    : Option (TypedSubst fr) :=
  let float_list := Bridge.floats fr
  match hAll : float_list.allM (checkFloat σ_impl) with
  | some true =>
      let σ_fn : Spec.Subst := fun v =>
        match σ_impl[v.v]? with
        | some f => (toExpr f).getD ⟨⟨"wff"⟩, [v.v]⟩
        | none => ⟨⟨"wff"⟩, [v.v]⟩
      some ⟨σ_fn, by
        intro c v h_float
        -- Use floats_sound to convert h_float to membership
        have h_in : (c, v) ∈ float_list := Bridge.floats_complete fr c v h_float
        -- Extract proof from allM
        rcases extract_from_allM_true float_list σ_impl hAll c v h_in with
          ⟨f, e, hlook, hconv, htc⟩
        -- Show σ_fn v = e and e.typecode = c
        dsimp [σ_fn]
        simp [hlook, hconv]
        exact htc
      ⟩
  | _ => none
```

---

## Strategic Questions (From AI_REQUEST_QUICK.md Q8)

### Q: What order to tackle?

**Oruži's implicit guidance (from Section F):**
```
1. Build infrastructure (toSubstTyped, checkFloat, extract lemma)
2. Prove simple bridge lemmas (toExpr properties)
3. Complete checkHyp theorems using infrastructure
```

**Our assessment:**
```
Phase 1: Import Bridge into Kernel ✅ (5 min)
Phase 2: Implement toSubstTyped ⏰ (1-2 hours, Section F pattern)
Phase 3: Prove toExpr lemmas ⏰ (1 hour, simple)
Phase 4: Complete checkHyp_floats_sound ⏰ (2-3 hours, uses above)
Phase 5: Complete checkHyp_essentials_sound ⏰ (1-2 hours, similar)
```

**Total estimate:** 5-8 hours for significant progress

---

## Files Ready to Modify

### ✅ Bridge Module (Already Complete!)
- `Metamath/Bridge/Basics.lean` - TypedSubst + helpers
- All simple lemmas proven

### ⏰ Kernel.lean Updates Needed
- Import Bridge module
- Implement toSubstTyped (using Section F pattern)
- Prove extract_from_allM_true lemma
- Prove toExpr bridge lemmas
- Complete checkHyp_floats_sound proof
- Complete checkHyp_essentials_sound proof

### 📝 Documentation
- This file! (tracking Oruži's guidance application)
- ORUZHI_SOLUTIONS_APPLIED.md (already created)

---

## Success Metrics

### Minimum Success ✅
- ✅ Found all key functions (toExpr, toSubst, checkHyp)
- ✅ Understood Bridge module infrastructure
- ✅ Documented next steps clearly

### Good Success (Next Session Target)
- ⏰ Implement toSubstTyped using Section F
- ⏰ Import Bridge into Kernel
- ⏰ Prove 2-3 simple bridge lemmas
- ⏰ Reduce sorry count by 1-2

### Excellent Success (Full Implementation)
- ⏰ Complete toSubstTyped with witness
- ⏰ Complete all toExpr lemmas
- ⏰ Complete checkHyp_floats_sound
- ⏰ Complete checkHyp_essentials_sound
- ⏰ Reduce sorry count to 7-9

---

## Key References

**Oruži's Guidance:**
- Section A: vars_apply_subset (localized dsimp) ✅ APPLIED
- Section B: matchFloats_sound with Nodup ✅ ALREADY COMPLETE
- Section C: `by simp` for if-then-else ✅ NOTED
- Section D: Avoiding "simp made no progress" ✅ APPLIED
- Section E: checkHyp type error fixes ✅ APPLIED
- **Section F: toSubstTyped with allM** ⏰ READY TO APPLY
- Section H: Hypothesis shaping ✅ NOTED
- Section I: allM pattern ✅ READY TO USE

**Our Proven Theorems:**
- matchFloats_sound (lines 1172-1226) ✅
- vars_apply_subset (lines 429-457) ✅
- matchSyms_sound (lines 884-969) ✅
- matchExpr_sound (lines 972-993) ✅
- identity_subst_syms (lines 350-364) ✅
- proofValid_monotone (lines 688-704) ✅

**Helper Lemmas:**
- List.mem_flatMap_iff (line 297) ✅
- mem_varsInExpr_of_mem_syms (line 305) ✅
- mem_varsInExpr_of_mem_sigma (line 314) ✅
- List.nodup_tail (line 323) ✅
- not_mem_of_nodup_cons (line 328) ✅

---

## Immediate Next Action

**Check if Kernel.lean imports Bridge:**
```bash
grep -n "import.*Bridge" Metamath/Kernel.lean
```

**If not imported:**
- Add `import Metamath.Bridge` to Kernel.lean
- Verify it builds

**Then implement Section F:**
- Define checkFloat
- Define extract_from_allM_true
- Implement toSubstTyped using Oruži's pattern

---

**Status:** ✅ Analysis complete! Ready to implement Section F.

**Next milestone:** toSubstTyped implementation with honest Option behavior

**Thank you Oruži for the clear roadmap!** 🚀
