# Expert AI Request: CheckHyp Integration & Bridge Lemmas

**Request Date:** 2025-10-14
**Project:** Metamath Proof Verifier Formal Verification in Lean 4.20.0-rc2
**Context:** 11 sorries remaining (down from 19), seeking expert guidance to complete
**Priority:** CheckHyp integration theorems (HIGH VALUE - core soundness path)

---

## Executive Summary

We're formalizing the soundness of a Metamath proof verifier in Lean 4. We've successfully eliminated 8 sorries using AI expert guidance (thank you!), and now need help with the remaining 11 sorries, particularly the CheckHyp integration theorems which connect our implementation to our already-proven spec-level lemmas.

**Key Success:** We've already proven `matchFloats_sound` - the hard work is done! Now we need to show the implementation corresponds to it.

---

## Project Context

### What We're Verifying

A Metamath proof verifier has two representations:
- **Implementation** (`Metamath.Verify`): Imperative code using Arrays, HashMaps, indices
- **Specification** (`Metamath.Spec`): Mathematical semantics using Lists, Functions, direct values

**Goal:** Prove that if the implementation succeeds, the specification has a valid proof derivation.

### What We've Proven So Far ✅

**Category B - Spec-Level Lemmas (ALL COMPLETE):**
- `vars_apply_subset`: Variables in substitution result
- `matchFloats_sound`: Floating hypothesis matching produces correct substitution
- `matchSyms_sound`: Symbol list matching soundness
- `matchExpr_sound`: Expression matching soundness
- `identity_subst_syms`: Identity substitution properties
- `proofValid_monotone`: Proof validity monotonicity

**Infrastructure:**
- 5 helper lemmas for nodup, membership, flatMap
- Validated proof patterns (nodup preconditions, witness-based approaches)

---

## MAIN REQUEST: CheckHyp Integration Theorems

### Problem Overview

We need to connect the implementation's `checkHyp` function (which processes both floating and essential hypotheses) to our proven spec-level functions `matchFloats` and `checkEssentials`.

**Current Challenge:** The theorem statements have TYPE ERRORS and need fixing + proving.

---

## Question 1: checkHyp_floats_sound - Fix & Proof Strategy

### Current (BROKEN) Theorem Statement

```lean
theorem checkHyp_floats_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : Nat)
    (subst_impl : Std.HashMap String Metamath.Verify.Formula) :
  -- If checkHyp succeeds on floating hypotheses
  (∀ i < hyps.size,
    ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with
    | .hyp false f _ => True  -- floating
    | _ => False) →
  -- BROKEN: Type mismatch!
  ∃ (floats_spec : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (σ_spec : Metamath.Spec.Subst),
    toSubst subst_impl = some σ_spec ∧
    floats_spec.map (fun (tc, v) => σ_spec v) =
      (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e) := by
  --  ^^^^ List Expr (Type)        ^^^^ Prop (Type mismatch!)
  sorry
```

**THE PROBLEM:** Right side is a `Prop`, left side is a `List Expr`. They can't be equal!

### What We Have Available

**Bridge Functions** (need to verify if these exist/are complete):
```lean
-- Convert implementation Formula to spec Expr
def toExpr : Metamath.Verify.Formula → Option Metamath.Spec.Expr := ...

-- Convert implementation HashMap to spec Subst
def toSubst : Std.HashMap String Metamath.Verify.Formula → Option Metamath.Spec.Subst := ...
```

**Already Proven Spec Lemma** (THIS IS KEY!):
```lean
theorem matchFloats_sound (floats : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (stack : List Metamath.Spec.Expr) (σ : Metamath.Spec.Subst)
    (h_nodup : List.Nodup (floats.map Prod.snd)) :
  matchFloats floats stack = some σ →
  floats.map (fun (tc, v) => σ v) = stack := by
  -- PROVEN! ✅ This is the hard work already done!
```

**Implementation Function** (need to understand):
```lean
-- From Metamath/Verify.lean (approximately)
def checkHyp (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : Nat) (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) :=
  if i >= hyps.size then pure subst
  else
    match db.find? hyps[i] with
    | some (.hyp false f _) =>  -- floating hypothesis
        -- Bind variable to stack expression
        let v := extract_variable f
        checkHyp db hyps stack off (i+1) (subst.insert v stack[off + i])
    | some (.hyp true f _) =>   -- essential hypothesis
        -- Check that f.subst == stack[off + i]
        if f.subst subst == stack[off + i] then
          checkHyp db hyps stack off (i+1) subst  -- no change to subst
        else
          throw "essential hypothesis doesn't match"
    | _ => throw "invalid hypothesis"
```

### QUESTION 1A: Correct Theorem Statement

**What should the correct theorem statement be?**

Our attempt:
```lean
theorem checkHyp_floats_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : Nat)
    (subst_impl : Std.HashMap String Metamath.Verify.Formula)
    (subst_impl' : Std.HashMap String Metamath.Verify.Formula) :
  -- Precondition: all hyps are floating
  (∀ i < hyps.size,
    ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with
    | .hyp false f _ => True
    | _ => False) →
  -- Precondition: checkHyp succeeds
  checkHyp db hyps stack off 0 subst_impl = Except.ok subst_impl' →
  -- Then there exists a spec correspondence
  ∃ (floats_spec : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (stack_spec : List Metamath.Spec.Expr)
    (σ_spec : Metamath.Spec.Subst),
    -- Stack converts successfully
    stack_spec.length = hyps.size ∧
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e ∧ stack_spec[i]? = some e) ∧
    -- Subst converts successfully
    toSubst subst_impl' = some σ_spec ∧
    -- matchFloats would succeed
    matchFloats floats_spec stack_spec = some σ_spec ∧
    -- And our proven lemma applies!
    floats_spec.map (fun (tc, v) => σ_spec v) = stack_spec := by
  sorry
```

**Questions:**
1. Is this theorem statement correct and complete?
2. What preconditions are we missing?
3. Should we relate `floats_spec` to `hyps` more explicitly?
4. Do we need a precondition about `subst_impl` being initial/empty?

### QUESTION 1B: Proof Strategy

**What's the best approach to prove this?**

Our ideas:
1. **Extract floats_spec**: For each `hyps[i]`, look up in `db`, extract `(typecode, variable)` pair
2. **Extract stack_spec**: Convert `stack[off..off+hyps.size]` using `toExpr`
3. **Induction on checkHyp**: Show it builds same substitution as matchFloats
4. **Apply matchFloats_sound**: Use our already-proven theorem!

**Specific questions:**
1. Should we prove by induction on `hyps.size` or on the `checkHyp` recursion?
2. Do we need a separate lemma relating checkHyp's iteration to matchFloats' recursion?
3. How do we handle the HashMap vs Function difference?
4. What's the right way to show `toSubst (checkHyp's result) = matchFloats' result`?

### QUESTION 1C: Key Bridge Lemmas Needed

**What lemmas should we prove first to make the main theorem easier?**

Our guesses:
```lean
-- 1. toExpr preserves equality
lemma toExpr_eq_iff (f1 f2 : Formula) (e1 e2 : Expr) :
  toExpr f1 = some e1 → toExpr f2 = some e2 →
  (f1 == f2) = true ↔ e1 = e2

-- 2. toSubst preserves lookups
lemma toSubst_lookup (σ_impl : HashMap String Formula) (σ_spec : Subst) :
  toSubst σ_impl = some σ_spec →
  ∀ v : Variable, ∃ f e,
    σ_impl[v.v]? = some f ∧
    toExpr f = some e ∧
    σ_spec v = e

-- 3. checkHyp for floats only ≈ matchFloats
lemma checkHyp_floats_equiv_matchFloats :
  ∀ (floats_impl : ...) (floats_spec : ...) (stack_impl : ...) (stack_spec : ...),
    convert_hyps_to_floats floats_impl = some floats_spec →
    convert_stack stack_impl = some stack_spec →
    checkHyp_floats_only floats_impl stack_impl = Except.ok subst_impl' →
    ∃ σ_spec,
      toSubst subst_impl' = some σ_spec ∧
      matchFloats floats_spec stack_spec = some σ_spec
```

**Questions:**
1. Are these the right helper lemmas?
2. What other lemmas would make the proof smoother?
3. Should we prove these in a specific order?
4. Are there standard Lean 4 tactics/patterns for HashMap↔Function correspondences?

---

## Question 2: checkHyp_essentials_sound - Similar Issues

### Current (BROKEN) Theorem Statement

```lean
theorem checkHyp_essentials_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : Nat)
    (subst_impl : Std.HashMap String Metamath.Verify.Formula) :
  (∀ i < hyps.size,
    ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with
    | .hyp true f _ => True  -- essential
    | _ => False) →
  ∃ (vars : List Metamath.Spec.Variable)
    (essentials_spec : List Metamath.Spec.Expr)
    (stack_spec : List Metamath.Spec.Expr)
    (σ_spec : Metamath.Spec.Subst),
    toSubst subst_impl = some σ_spec ∧
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e) ∧
    checkEssentials vars σ_spec essentials_spec stack_spec = true := by
  sorry
```

**Spec Function Available:**
```lean
def checkEssentials (vars : List Variable) (σ : Subst)
    (essentials : List Expr) (stack : List Expr) : Bool :=
  match essentials, stack with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | e_hyp :: es, e_stack :: ss =>
      (applySubst vars σ e_hyp == e_stack) && checkEssentials vars σ es ss
```

### QUESTION 2A: Correct Statement & Proof Strategy

**Similar questions as Q1:**
1. What should the correct theorem statement be?
2. What preconditions are needed?
3. How to relate checkHyp's checking mode (no new bindings) to checkEssentials?
4. How to prove the correspondence?

**Key difference from floats:**
- Floats: **builds** substitution (HashMap.insert)
- Essentials: **checks** against existing substitution (no insert)

---

## Question 3: Array/List Bridge Lemmas

### Context

Implementation uses Arrays, spec uses Lists. Need correspondence lemmas.

### Specific Questions

```lean
-- Q3A: Array slice to List correspondence
lemma array_slice_correspondence (arr : Array α) (off len : Nat) :
  (arr.extract off (off + len)).toList =
    arr.toList.drop off |>.take len := ?

-- Q3B: Indexed access correspondence
lemma array_list_getElem (arr : Array α) (i : Nat) (h : i < arr.size) :
  arr[i] = arr.toList[i]'(by simp [h]) := ?

-- Q3C: Converting Array hypotheses to List
-- Need pattern for: ∀ i < arr.size, P arr[i]  →  ∀ x ∈ arr.toList, P x
```

**Questions:**
1. Do these lemmas already exist in Lean 4.20 Batteries?
2. What's the idiomatic way to prove Array↔List correspondences?
3. Are there higher-level lemmas that would make our proofs easier?

---

## Question 4: HashMap/Function Bridge Lemmas

### Context

Implementation uses `HashMap String Formula`, spec uses `Variable → Expr` functions.

### Specific Questions

```lean
-- Q4A: Lookup correspondence
-- If toSubst succeeds, lookups correspond
lemma toSubst_lookup_correspondence
    (σ_impl : HashMap String Formula)
    (σ_spec : Subst) :
  toSubst σ_impl = some σ_spec →
  ∀ (v : Variable),
    ∃ (f : Formula) (e : Expr),
      σ_impl[v.v]? = some f ∧
      toExpr f = some e ∧
      σ_spec v = e := ?

-- Q4B: Insert correspondence
-- If we insert into HashMap, does toSubst still work?
lemma toSubst_insert_correspondence
    (σ_impl : HashMap String Formula)
    (σ_spec : Subst)
    (v : String) (f : Formula) :
  toSubst σ_impl = some σ_spec →
  toExpr f = some e →
  ∃ σ_spec',
    toSubst (σ_impl.insert v f) = some σ_spec' ∧
    σ_spec' = (fun w => if w.v = v then e else σ_spec w) := ?

-- Q4C: Iteration over HashMap
-- Pattern for proving properties about HashMap operations
```

**Questions:**
1. What's the standard approach for HashMap↔Function correspondences in Lean?
2. Are there libraries/patterns for this?
3. How to handle partiality (HashMap lookup returns Option)?

---

## Question 5: Implementation Details We Need Help With

### Q5A: Understanding checkHyp Implementation

We need to understand the ACTUAL implementation of `checkHyp` in `Metamath/Verify.lean`.

**Questions:**
1. Does checkHyp iterate with a loop or recursion?
2. How does it distinguish floating vs essential hypotheses?
3. What exactly goes into the HashMap for floating hypotheses?
4. How does it check essential hypotheses (what equality test)?

**Why we need this:** Can't prove correspondence without understanding implementation!

### Q5B: toExpr and toSubst Definitions

We need the actual definitions (or at least specifications).

**Questions:**
1. What does `toExpr : Formula → Option Expr` do exactly?
2. What does `toSubst : HashMap String Formula → Option Subst` do?
3. When do these conversion functions return `none` vs `some`?
4. What well-formedness conditions do they require?

**Example of what we need:**
```lean
-- Is toExpr defined like this?
def toExpr (f : Formula) : Option Expr :=
  if h : f.size > 0 then
    some { typecode := f[0].as_const?,
           syms := f.toList.tail.map symbol_to_string }
  else
    none

-- Is toSubst defined like this?
def toSubst (σ_impl : HashMap String Formula) : Option Subst :=
  -- Check all values convert successfully?
  if (σ_impl.values.all (fun f => toExpr f |>.isSome)) then
    some (fun v =>
      match σ_impl[v.v]?, toExpr ... with
      | some f, some e => e
      | _, _ => default_expr)
  else
    none
```

---

## Question 6: Proof Tactics & Patterns

### Q6A: Best Tactics for This Kind of Proof

**What tactics/patterns work well for:**
1. Induction on imperative recursion/loops?
2. Relating HashMap operations to function updates?
3. Array/List correspondence proofs?
4. Existential introduction from computation?

### Q6B: Common Pitfalls

**What should we watch out for:**
1. Off-by-one errors in Array indexing?
2. Partiality issues (Options everywhere)?
3. Type class inference problems?
4. Performance issues with large proofs?

### Q6C: Lean 4.20 Specific Advice

**Are there Lean 4.20-specific patterns we should use?**
1. New tactics available in 4.20?
2. Changes from Lean 4.8 or earlier?
3. Batteries library we should leverage?

---

## Question 7: Overall Strategy Guidance

### Q7A: What Order to Tackle These?

We have 11 sorries remaining:
1. checkHyp_floats_sound (line 1691) - HIGH PRIORITY
2. checkHyp_essentials_sound (line 1714) - HIGH PRIORITY
3-11. Various implementation bridge lemmas (lines 2505, 2517, 2880, 2884, 3119, 3152, 3160, 3209)

**Question:** What's the best order to tackle these for maximum progress?

Options:
- **A.** Fix checkHyp theorem statements first, then prove bridge lemmas, then complete proofs
- **B.** Prove all bridge lemmas first, then tackle checkHyp theorems
- **C.** Interleave: prove bridge lemmas as needed for checkHyp proofs
- **D.** Something else?

### Q7B: Time Estimates

**Realistic time estimates for each part?**
1. Fixing theorem statements: ?
2. Proving basic bridge lemmas (toExpr properties): ?
3. Proving HashMap correspondence lemmas: ?
4. Proving Array/List lemmas: ?
5. checkHyp_floats_sound main proof: ?
6. checkHyp_essentials_sound main proof: ?

### Q7C: Should We Simplify?

**Alternative approaches:**
1. Should we use `axiom` for some bridge lemmas and focus on main theorems?
2. Should we refactor implementation to make verification easier?
3. Should we add preconditions to make proofs simpler?
4. Are there design patterns that would help?

---

## Question 8: Specific Code Review & Suggestions

### Current File Structure

```
Metamath/Kernel.lean (~3400 lines)
  - Lines 1-700: Spec definitions, substitution lemmas ✅
  - Lines 700-1200: Match functions (matchSyms, matchExpr, matchFloats) ✅
  - Lines 1200-1700: Soundness theorems (matchFloats_sound proven!) ✅
  - Lines 1700-2400: Bridge infrastructure (partially complete)
  - Lines 2400+: Implementation bridge lemmas (8 sorries remaining)
```

**Questions:**
1. Should we split this into multiple files?
2. Is the structure logical?
3. Any organizational improvements?

### Code Quality Questions

1. Are our theorem statements idiomatic Lean 4?
2. Are we using the right proof patterns?
3. Could we simplify any statements?
4. Are we missing obvious lemmas from the library?

---

## What Would Help Most

### High Priority

1. **✅ Corrected theorem statements** for checkHyp_floats_sound and checkHyp_essentials_sound
2. **✅ List of bridge lemmas** we should prove first (with statements)
3. **✅ Proof outline** for checkHyp_floats_sound showing how to apply matchFloats_sound
4. **✅ Tactics/patterns** for HashMap↔Function and Array↔List correspondences

### Medium Priority

5. **Example proofs** of 1-2 simple bridge lemmas as patterns
6. **Time estimates** for realistic planning
7. **Implementation guidance** - what details we need from Verify.lean
8. **Strategic advice** on ordering and approach

### Bonus

9. **Code review** of our existing proofs (are they idiomatic?)
10. **Performance tips** for large formal verification projects
11. **Common pitfalls** to avoid

---

## Context Files

### What We Can Provide

1. **Full Metamath/Kernel.lean** (~3400 lines with our current proofs)
2. **Metamath/Spec.lean** (~200 lines with definitions)
3. **Metamath/Verify.lean** (implementation - need to extract relevant parts)
4. **Success documentation** showing what worked (patterns, lemmas)
5. **Our helper lemmas** that are working well

### What We've Tried

- ✅ Nodup precondition pattern (worked great!)
- ✅ Witness-based approaches for existentials (worked!)
- ✅ Simple induction patterns (worked!)
- ❌ Direct approach to checkHyp theorems (type errors)
- ❌ Attempting full proofs without bridge lemmas (got stuck)

---

## Success Metrics

### Minimum Success

- ✅ Type-correct theorem statements
- ✅ Clear proof strategy
- ✅ List of needed bridge lemmas

### Good Success

- ✅ Above plus
- ✅ 2-3 bridge lemmas proven
- ✅ Partial proof of checkHyp_floats_sound

### Excellent Success

- ✅ Above plus
- ✅ Complete proof of checkHyp_floats_sound
- ✅ Significant progress on checkHyp_essentials_sound
- ✅ 1-2 sorries eliminated

---

## Additional Context

### What Makes This Hard

1. **Two representations**: Implementation vs Specification
2. **Different data structures**: HashMap vs Function, Array vs List
3. **Partiality everywhere**: Lots of Options and Excepts
4. **Complex recursion**: checkHyp has non-trivial control flow
5. **Type conversions**: toExpr, toSubst need careful handling

### Why We're Confident This Can Work

1. ✅ We've already proven the hard spec-level lemma (matchFloats_sound)!
2. ✅ We have working patterns (nodup, witness-based)
3. ✅ We have helper lemma infrastructure
4. ✅ Previous AI guidance worked exceptionally well
5. ✅ We're 70-75% complete overall

### What We're Asking For

**Not:** "Please write the proofs for us"

**But:**
- **Correct theorem statements** (fix the type errors!)
- **Proof strategies** (what approach to take)
- **Bridge lemma lists** (what to prove first)
- **Lean 4 patterns** (idioms for HashMap/Array correspondences)
- **Strategic guidance** (best order to tackle things)

---

## Example of Response Format We'd Love

### For checkHyp_floats_sound:

**1. Corrected Statement:**
```lean
theorem checkHyp_floats_sound ... :=
  -- Fixed version here
```

**2. Proof Strategy:**
- Step 1: ...
- Step 2: ...
- Step 3: ...

**3. Bridge Lemmas Needed:**
```lean
lemma bridge_1 : ... :=
lemma bridge_2 : ... :=
```

**4. Proof Outline:**
```lean
theorem checkHyp_floats_sound ... := by
  intro ...
  -- Extract floats_spec: ...
  -- Convert stack: ...
  -- Show checkHyp ≈ matchFloats by ...
  -- Apply matchFloats_sound: ...
  sorry  -- Specific remaining gap: ...
```

---

## Thank You!

We're incredibly grateful for AI expert help! The previous guidance (Problems 1 & 3 from Oruži) was **exactly right** and led to successful proofs. We're hoping for similar high-quality strategic guidance for these final theorems.

**Project goal:** Complete formal verification of Metamath proof checker soundness

**Current state:** 70-75% complete, 11 sorries remaining, clear path forward

**What we need:** Expert guidance on checkHyp integration and bridge lemmas

**Impact:** This is open-source formal verification that could benefit the broader proof assistant community!

---

**Total Sorries Remaining: 11**
- **2 HIGH PRIORITY:** checkHyp integration (this request)
- **8 MEDIUM:** Implementation bridge lemmas
- **1 COMMENTED OUT:** Deprecated theorem (can ignore)

Let's finish this! 🚀🐢✨
