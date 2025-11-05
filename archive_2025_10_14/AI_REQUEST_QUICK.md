# Quick AI Expert Request: Fix checkHyp Theorem Type Errors

**Project:** Metamath verifier soundness in Lean 4.20.0-rc2
**Status:** 11/19 sorries remaining, need help with 2 HIGH PRIORITY theorems
**Key:** We already proved `matchFloats_sound` - just need to connect implementation to it!

---

## THE PROBLEM: Type Errors in Theorem Statements

### checkHyp_floats_sound (Line 1691) - BROKEN ❌

```lean
theorem checkHyp_floats_sound ... :
  ... →
  ∃ (floats_spec : List (Constant × Variable)) (σ_spec : Subst),
    toSubst subst_impl = some σ_spec ∧
    floats_spec.map (fun (tc, v) => σ_spec v) =
      (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e) := by
  --  ^^^^^^^^^^^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  --  List Expr (Type)           Prop (TYPE MISMATCH!)
  sorry
```

**ERROR:** Can't equate `List Expr` with `Prop`!

### What We Have Already Proven ✅

```lean
theorem matchFloats_sound (floats : List (Constant × Variable))
    (stack : List Expr) (σ : Subst)
    (h_nodup : List.Nodup (floats.map Prod.snd)) :
  matchFloats floats stack = some σ →
  floats.map (fun (tc, v) => σ v) = stack := by
  -- PROVEN! This is the hard work done ✅
```

---

## 8 FOCUSED QUESTIONS

### Q1: Fix the Type Error - What's the Correct Statement?

Should it be:
```lean
theorem checkHyp_floats_sound
    (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : Nat) (subst_impl subst_impl' : HashMap String Formula) :
  (∀ i < hyps.size, ∃ obj, db.find? hyps[i] = some obj ∧ obj is floating) →
  checkHyp db hyps stack off 0 subst_impl = Except.ok subst_impl' →
  ∃ (floats_spec : List (Constant × Variable))
    (stack_spec : List Expr)
    (σ_spec : Subst),
    -- Convert stack successfully
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e ∧ stack_spec[i]? = some e) ∧
    -- Convert subst successfully
    toSubst subst_impl' = some σ_spec ∧
    -- matchFloats succeeds with same result
    matchFloats floats_spec stack_spec = some σ_spec ∧
    -- Apply our proven theorem!
    floats_spec.map (fun (tc, v) => σ_spec v) = stack_spec := by
  sorry
```

**Is this correct? What are we missing?**

### Q2: Proof Strategy

How to prove? Our idea:
1. Extract `floats_spec` from `hyps` (look up each in db)
2. Convert `stack[off..off+hyps.size]` to `stack_spec` using `toExpr`
3. Show `checkHyp` builds same substitution as `matchFloats`
4. Apply `matchFloats_sound` (already proven!)

**Is this the right approach? Better strategy?**

### Q3: Bridge Lemmas Needed

What helper lemmas should we prove first?

```lean
-- toExpr preserves equality?
lemma toExpr_eq_iff : toExpr f1 = some e1 → toExpr f2 = some e2 →
  (f1 == f2) ↔ e1 = e2

-- toSubst preserves lookups?
lemma toSubst_lookup : toSubst σ_impl = some σ_spec →
  ∀ v, ∃ f e, σ_impl[v.v]? = some f ∧ toExpr f = some e ∧ σ_spec v = e

-- checkHyp iteration ≈ matchFloats recursion?
lemma checkHyp_equiv_matchFloats : ...
```

**Are these the right lemmas? What else?**

### Q4: HashMap to Function Correspondence

How to relate `HashMap String Formula` to `Variable → Expr` functions?

**Pattern we need:**
- checkHyp does `σ.insert v f` for floating hypotheses
- matchFloats builds `fun w => if w = v then e else σ w`
- How to show these correspond through `toSubst`?

**What's the idiomatic Lean 4 approach?**

### Q5: Array to List Correspondence

How to handle `Array` in implementation vs `List` in spec?

**Patterns we need:**
- `∀ i < arr.size, P arr[i]` → `∀ x ∈ arr.toList, P x`
- `arr.extract off len` → `arr.toList.drop off |>.take len`
- Indexed access correspondence

**Do these lemmas exist in Batteries? How to prove?**

### Q6: checkHyp_essentials_sound - Similar Issue

```lean
theorem checkHyp_essentials_sound ... :
  ... →
  ∃ (essentials_spec stack_spec : List Expr) (σ_spec : Subst),
    toSubst subst_impl = some σ_spec ∧
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e) ∧  -- Fix this?
    checkEssentials vars σ_spec essentials_spec stack_spec = true := by
  sorry
```

**Same type error? What's the fix?**

**Key difference:** Essential hyps CHECK (no new bindings) vs floats BUILD substitution

### Q7: Implementation Details Needed

To prove correspondence, we need to know:
1. How does `checkHyp` actually iterate? (recursion? loop?)
2. What exactly does it store in HashMap for floats?
3. How does it check essential hypotheses?

**Can you infer reasonable implementation or do we need to provide Verify.lean?**

### Q8: Best Order to Tackle

We have:
- 2 checkHyp theorems (this request)
- 8 other implementation bridge lemmas

**What order:**
- A) Fix statements → prove bridge lemmas → complete proofs
- B) Prove bridge lemmas first → then tackle main theorems
- C) Interleave as needed
- D) Something else?

---

## What We Need Most

### Priority 1: ⭐
✅ **Corrected theorem statements** (fix type errors!)
✅ **Proof strategy** (step-by-step approach)
✅ **Bridge lemma list** (what to prove first)

### Priority 2:
✅ Patterns for HashMap↔Function correspondences
✅ Patterns for Array↔List correspondences
✅ Example proof of 1-2 bridge lemmas

### Priority 3:
✅ Time estimates (realistic planning)
✅ Strategic advice (best order)
✅ Lean 4.20 idioms and tactics

---

## Context

**What we've proven:** vars_apply_subset, matchFloats_sound, matchSyms_sound, matchExpr_sound, proofValid_monotone + 5 helper lemmas ✅

**Patterns that worked:** Nodup preconditions, witness-based approaches, simple induction ✅

**Current blocker:** Type errors in checkHyp theorem statements

**Project status:** 70-75% complete, 11 sorries remaining, clear path forward with your help!

---

## Example Response Format

```lean
-- Q1 Answer: Corrected statement
theorem checkHyp_floats_sound ... :=
  -- [corrected version]

-- Q2 Answer: Proof strategy
-- Step 1: Extract floats_spec by...
-- Step 2: Convert stack using...
-- Step 3: Show correspondence by...
-- Step 4: Apply matchFloats_sound

-- Q3 Answer: Bridge lemmas needed
lemma bridge_1 : ... := by ...
lemma bridge_2 : ... := by ...
```

---

**Previous AI guidance worked perfectly!** (Eliminated 8 sorries)

**Now we need:** Fix type errors + connection strategy to leverage our proven matchFloats_sound

**Impact:** Open-source formal verification completing Metamath soundness proof

Thank you! 🚀
