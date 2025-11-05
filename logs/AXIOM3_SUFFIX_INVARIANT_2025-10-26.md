# AXIOM 3: Suffix Invariant Proof Strategy
**Date**: October 26, 2025
**Source**: GPT-5 Pro (Oruži)
**Goal**: Eliminate AXIOM 3 using well-founded induction with suffix invariant

---

## The Problem: Why Prefix Invariant Failed

### Original Approach (Failed)
```lean
ImplInv σ i := ∀ j, j < i → ImplMatchesAt σ j
```

**Issue**: Growing this from `i` to `i+1` requires proving index `i` matches **while threading the substitution** - exactly where we got stuck.

### Key Insight: Use Suffix Invariant

```lean
ImplInvFrom σ i := ∀ j, i ≤ j → j < hyps.size → ImplMatchesAt σ j
```

**Why this works**:
- Prove "everything from `i` to end matches"
- Well-founded induction on `k = hyps.size - i`
- At each step, only need to discharge **local check at i**, then IH handles rest
- At the end, convert suffix (`ImplInvFrom σ 0`) to prefix (`ImplInv σ hyps.size`)

---

## The checkHyp Implementation (Verify.lean:401-418)

```lean
def checkHyp (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(proof)
    if let some (.hyp ess f _) := db.find? hyps[i] then
      if f[0]! == val[0]! then        -- Typecode check
        if ess then                    -- Essential hypothesis
          if (← f.subst subst) == val then
            checkHyp (i+1) subst       -- Recurse, σ unchanged
          else throw "type error"
        else                           -- Float hypothesis
          checkHyp (i+1) (subst.insert f[1]!.value val)  -- σ extended
      else throw "bad typecode"
    else unreachable!
  else pure subst                      -- Base: i ≥ hyps.size
```

**Recursion pattern**:
- Base: `i ≥ hyps.size` → return `subst` unchanged
- Float: insert `v ↦ val`, recurse with `i+1`
- Essential: check `f.subst σ == val`, recurse with same σ
- Always: `i → i+1` (measure decreases)

---

## Proof Structure: Well-Founded Induction

### Measure
```lean
k = hyps.size - i    -- Strictly decreases: i < hyps.size implies (size - (i+1)) < (size - i)
```

### Induction Setup
```lean
revert σ_out
generalize hk : hyps.size - i = k
induction k generalizing i σ_in with
| zero => ...    -- Base case: i ≥ hyps.size
| succ k ih => ...  -- Step case: process index i, apply IH to i+1
```

### Base Case (`k = 0`, i.e., `i ≥ hyps.size`)
- checkHyp returns `pure σ_in`
- So `σ_out = σ_in`
- Suffix property vacuous (no `j` satisfies `i ≤ j < hyps.size`)

### Step Case (`k = k' + 1`, i.e., `i < hyps.size`)
1. **Expose the step**: `simp [checkHyp, hi]` unfolds one iteration
2. **Case split on hypothesis type**: `cases db.find? hyps[i]!`
3. **Branch on essential/float**:
   - **Essential**: Extract `f.subst σ_in = ok expected = val`, recurse with same σ
   - **Float**: Extract `v`, recurse with `σ_in.insert v val`
4. **Apply IH**: Get suffix property for `i+1` to `hyps.size`
5. **Build suffix for i**: Show `ImplMatchesAt σ_out i`, then IH covers `i+1...size`

---

## Required Helper Lemmas (3 total)

### HashMap Operations (2 lemmas)

```lean
@[simp] axiom HashMap.find?_insert_self
  {α β} [BEq α] [Hashable α] (m : Std.HashMap α β) (a : α) (b : β) :
  (m.insert a b)[a]? = some b

@[simp] axiom HashMap.find?_insert_ne
  {α β} [BEq α] [Hashable α] (m : Std.HashMap α β) {a a' : α} (b : β) :
  a' ≠ a → (m.insert a b)[a']? = m[a']?
```

**Purpose**: Track bindings through float insertions
- `insert_self`: The just-inserted binding is present
- `insert_ne`: Other bindings unchanged
- **Character**: Library-level HashMap facts (not domain logic)

### Formula Substitution Extensionality

```lean
def Verify.Formula.vars (f : Verify.Formula) : List String :=
  (List.range f.size).filterMap (fun i =>
    match f[i]! with | .var v => some v | _ => none)

axiom Formula_subst_agree_on_vars
  (f : Verify.Formula) (σ₁ σ₂ : Std.HashMap String Verify.Formula) :
  (∀ v, v ∈ f.vars → σ₁[v]? = σ₂[v]?) →
  f.subst σ₁ = f.subst σ₂
```

**Purpose**: For essential case, show `f.subst σ_out = f.subst σ_in` when later floats don't touch vars in `f`
- **Character**: Library-level Formula.subst property (not checkHyp semantics)

**TODO**: These can be proven (~20 lines each) by induction on formulas/arrays

---

## Tactic Recipe (GPT-5 Pro's Pattern)

### Setup
```lean
revert σ_out
generalize hk : hyps.size - i = k
induction k generalizing i σ_in with
```

### Base Case
```lean
| zero =>
    intro σ_out hrun
    have hi : ¬ i < hyps.size := ...  -- From k = 0
    simp [Verify.DB.checkHyp, hi] at hrun
    cases hrun  -- σ_out = σ_in
    intro j hij hjlt
    exact (False.elim ...)  -- Impossible: j ≥ i but j < hyps.size
```

### Step Case
```lean
| succ k ih =>
    intro σ_out hrun
    have hi : i < hyps.size := ...  -- Contradict succ otherwise
    simp [Verify.DB.checkHyp, hi] at hrun
    cases h : db.find? hyps[i]! with ...
    -- Extract obj, split on .hyp ess f _
```

### Float Branch
```lean
-- Extract v and recursive call
obtain hrec : checkHyp ... (i+1) (σ_in.insert v val) = ok σ_out := ...
-- Apply IH with updated measure
have IH := ih (by omega) hrec
-- Build suffix property
intro j hij hjlt
by_cases hji : j = i
· -- j = i: Use HashMap.find?_insert_self
  subst hji
  simpa [ImplMatchesAt, hfind, HashMap.find?_insert_self]
· -- j > i: Use IH
  have : i+1 ≤ j := Nat.succ_le_of_lt (lt_of_le_of_ne hij hji)
  exact IH j this hjlt
```

### Essential Branch
```lean
-- Extract expected and recursive call
obtain ⟨expected, hsubst, heq, hrec⟩ := ...
-- Apply IH with same σ
have IH := ih (by omega) hrec
-- Build suffix property
intro j hij hjlt
by_cases hji : j = i
· -- j = i: Use Formula_subst_agree_on_vars
  have : f.subst σ_out = ok expected := by
    apply Formula_subst_agree_on_vars
    -- Show σ_out agrees with σ_in on vars of f
    ...
  simpa [ImplMatchesAt, hfind, this, heq]
· -- j > i: Use IH
  exact IH j (Nat.succ_le_of_lt ...) hjlt
```

---

## Conversion: Suffix → Prefix

```lean
theorem checkHyp_builds_impl_inv ... := by
  intro h_ok
  have hSuf : ImplInvFrom db hyps stack off σ_impl 0 :=
    checkHyp_builds_impl_inv_from ... h_ok
  -- Reshape: "all from 0" = "all below size"
  intro j hj
  exact hSuf j (Nat.zero_le _) hj
```

**Why this works**: `ImplInvFrom σ 0` means `∀ j, 0 ≤ j → j < size → ...`, which is exactly `ImplInv σ size`.

---

## Axiom Count Analysis

### Current State
- 6 axioms total (including AXIOM 3)

### After Implementation
- Remove: AXIOM 3 (now a theorem)
- Add: 3 helper axioms (HashMap × 2, Formula.subst × 1)
- **Net: 6 → 8 axioms**

### Character Difference
**Before**:
- AXIOM 3: Domain axiom (checkHyp operational semantics)

**After**:
- 3 helpers: Library axioms (HashMap, Formula operations)
- AXIOM 3: **Theorem** (proven using helpers + induction)

**Trust boundary shift**: From trusting checkHyp behavior → trusting library operations

### Future Optimization
Each helper is ~20 lines to prove:
- `HashMap.find?_insert_self`: Unfold insert, case on equality
- `HashMap.find?_insert_ne`: Unfold insert, case on inequality
- `Formula_subst_agree_on_vars`: Induction on formula structure

**Final goal**: 5 axioms (eliminate all 3 helpers)

---

## Learning Points

### 1. Suffix Invariant Technique
**When to use**: Proving properties of recursive functions with accumulating state
**Why it works**: Aligns with natural recursion direction (forward through indices)
**Alternative names**: "Tail invariant", "Forward invariant"

### 2. Well-Founded Induction Setup
```lean
generalize hk : measure = k
induction k generalizing ...
```
**Key**: Generalize the measure, induct on it, keep original parameters flexible

### 3. HashMap Reasoning Pattern
- Use `@[simp]` lemmas for insert/lookup
- Monotonicity: `insert` doesn't change other keys
- Extensionality: Agreement on relevant keys → equal results

### 4. Case Analysis on do-Notation
```lean
simp [...] at hrun
obtain ⟨var1, var2, ..., hrec⟩ := ...
```
**Instead of**: Manually unfolding `bind`/`>>=`

---

## Implementation Checklist

- [x] Create logs directory
- [ ] Add 3 helper lemmas to KernelExtras.lean
- [ ] Add `ImplInvFrom` definition
- [ ] Add `checkHyp_builds_impl_inv_from` (suffix proof)
- [ ] Add `checkHyp_builds_impl_inv` wrapper (suffix→prefix)
- [ ] Update `impl_to_spec_at` with GPT-5 skeleton
- [ ] Build and test
- [ ] Document remaining admits/sorries
- [ ] Create final status report

---

## References

- **Original request**: See conversation with user about structural induction
- **GPT-5 Pro's response**: Full message saved in logs/gpt5_axiom3_response.txt
- **Pattern**: Similar to Hoare logic invariant proofs for while loops

---

**Next Steps**: Implement Phase 2 (add helper lemmas) → Phase 3 (suffix proof) → Phase 4 (bridge) → Phase 5 (build) → Phase 6 (document).
