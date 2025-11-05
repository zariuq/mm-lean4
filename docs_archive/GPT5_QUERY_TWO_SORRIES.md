# Query for GPT-5: Fill Two Sorries in Key-Based Witness Extraction

**Context:** We're proving soundness of Metamath proof checker in Lean 4. We've successfully refactored from a values-based HashMap approach to a strictly stronger key-based approach, eliminating the need for TRUSTED HashMap.values reasoning. Two straightforward sorries remain in the witness extraction proof.

---

## The Proof Context

**File:** `Metamath/Kernel.lean`
**Lines:** 2449-2474 (inside `checkHyp_correct_strong`, base case of strong induction)

### What We're Proving

**Main Goal:** For every binding `σ[v] = f` in the substitution, prove that `f` converts to a spec expression.

**Key-Based Approach (Stronger):**
```lean
∀ (v : String) (f : Metamath.Verify.Formula), σ'[v]? = some f → (∃ e, toExprOpt f = some e)
```

This eliminates HashMap.values entirely - we quantify over keys (lookups) instead of the values collection!

---

## Available Context (In Scope)

From the proof state at the sorries:

```lean
-- Fixed parameters (from theorem signature):
db : Metamath.Verify.DB
hyps : Array String
stack : Array Metamath.Verify.Formula
off : { off : Nat // off + hyps.size = stack.size }
stack_spec : List Metamath.Spec.Expr
hStack : stack.toList.mapM toExprOpt = some stack_spec  -- ⭐ KEY FACT

-- Base case specific:
i : Nat
σ : Std.HashMap String Metamath.Verify.Formula
hi : i ≤ hyps.size
hn : 0 = hyps.size - i  -- so i = hyps.size
hprop : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) i σ
σ' : Std.HashMap String Metamath.Verify.Formula
hrun : Metamath.Verify.DB.checkHyp db hyps stack off i σ = .ok σ'
h_eq : i = hyps.size
h_σ : σ = σ'  -- (from injecting hrun)

-- Witness extraction (from Step 1-2):
v : String
f : Metamath.Verify.Formula
hv_lookup : σ[v]? = some f  -- ⭐ This is the key we're looking up!
j : Nat
hj_lt : j < i
hwitness : FloatBindWitness (db := db) (hyps := hyps) (stack := stack) (off := off) j v f
hj : j < hyps.size
k : Fin stack.size  -- ⭐ THE KEY WITNESS: stack index where f came from!
f' : Metamath.Verify.Formula
lbl : String
h_off : off.1 + j = k.val
h_find : db.find? (hyps[j]) = some (.hyp false f' lbl)
h_var : f'[1]!.value = v
h_val_eq : f = stack[k]!  -- ⭐ KEY FACT: f equals stack[k]!
h_head : (f'[0]! == f[0]!) = true
```

---

## Relevant Definitions

### FloatBindWitness
```lean
def FloatBindWitness
    (db : Metamath.Verify.DB) (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (j : Nat) (v : String) (val : Metamath.Verify.Formula) : Prop :=
  ∃ (hj : j < hyps.size) (k : Fin stack.size) (f : Metamath.Verify.Formula) (lbl : String),
    off.1 + j = k.val ∧
    db.find? (hyps[j]) = some (.hyp false f lbl) ∧
    f[1]!.value = v ∧
    val = stack[k]! ∧   -- ⭐ This gives us the stack index!
    (f[0]! == val[0]!) = true
```

**Key Insight:** FloatBindWitness records the stack index `k` where each binding value came from!

### HypProp (Loop Invariant)
```lean
def HypProp (n : Nat) (σ : Std.HashMap String Metamath.Verify.Formula) : Prop :=
  ∀ v val, σ[v]? = some val →
    ∃ j, j < n ∧ FloatBindWitness (db := db) (hyps := hyps) (stack := stack) (off := off) j v val
```

**Key Insight:** Every binding in σ comes from a FloatBindWitness, which records the stack index!

---

## The Two Sorries

### **Sorry #1** (Lines 2462-2466): Array Membership

**Goal Type:**
```lean
⊢ stack[k] ∈ stack.toList
```

**Context:**
- `stack : Array Metamath.Verify.Formula`
- `k : Fin stack.size`

**What We Need:** Prove that `Array.get` (notation `stack[k]`) produces a member of `stack.toList`.

**Expected Approach:** This is a standard Array property. In Lean 4:
- `Array.toList` is defined as `Array.data` (converts Array to List)
- `Array.get` with `Fin stack.size` is in-bounds by construction
- Should be provable using `Array.getElem_mem_data` or similar from Std library

**Helper Lemma in KernelExtras (exists but has sorry):**
```lean
theorem Array.mem_toList_get {α} (a : Array α) (k : Fin a.size) : a[k] ∈ a.toList := by sorry
```

**Question:** Can you prove `stack[k] ∈ stack.toList` using Lean 4 standard library lemmas? Ideally from `Std.Data.Array.*` or core Lean.

---

### **Sorry #2** (Lines 2469-2473): mapM Witness Extraction

**Goal Type:**
```lean
⊢ ∃ e, toExprOpt stack[k]! = some e
```

**Context:**
- `stack : Array Metamath.Verify.Formula`
- `k : Fin stack.size`
- `hStack : stack.toList.mapM toExprOpt = some stack_spec` -- ⭐ mapM succeeds!
- `h_mem : stack[k] ∈ stack.toList` -- ⭐ (from Sorry #1)
- `toExprOpt : Metamath.Verify.Formula → Option Metamath.Spec.Expr`

**What We Need:** If `mapM f` succeeds on a list, then `f` succeeds on each element in that list.

**Key Insight:**
- `List.mapM f xs = some ys` means every element of `xs` converts successfully via `f`
- Since `stack[k] ∈ stack.toList`, and `stack.toList.mapM toExprOpt = some stack_spec`, we know `toExprOpt stack[k]` succeeds!

**Helper Lemma in KernelExtras (exists but has sorry):**
```lean
theorem List.mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b := by sorry
```

**Question:** Can you prove this using Lean 4's `List.mapM` definition? Key steps:
1. `List.mapM` is defined recursively: `mapM f (x::xs) = do let y ← f x; let ys ← mapM f xs; return y::ys`
2. If `mapM f xs = some ys`, then for all `x ∈ xs`, we have `∃ b, f x = some b`
3. This should be provable by induction on the list

---

## Current Proof Structure

```lean
· -- All values convert: key-based approach (no HashMap.values reasoning needed!)
  intro v f hv_lookup
  -- Each binding σ[v] = f comes from a FloatBindWitness (via HypProp)

  -- Step 1: Use HypProp to get FloatBindWitness
  obtain ⟨j, hj_lt, hwitness⟩ := hprop v f hv_lookup

  -- Step 2: Extract stack index from FloatBindWitness
  unfold FloatBindWitness at hwitness
  obtain ⟨hj, k, f', lbl, h_off, h_find, h_var, h_val_eq, h_head⟩ := hwitness

  -- Step 3: f = stack[k], so stack[k] ∈ stack.toList
  rw [h_val_eq]
  have h_mem : stack[k] ∈ stack.toList := by
    sorry  -- ⭐ SORRY #1: Prove stack[k] ∈ stack.toList

  -- Step 4: Apply mapM_some_of_mem to get conversion witness
  have : ∃ e, toExprOpt stack[k]! = some e := by
    sorry  -- ⭐ SORRY #2: Use h_mem + hStack to get witness
  exact this
```

---

## What We're Asking

**Please provide Lean 4 proofs for both sorries:**

1. **Prove `stack[k] ∈ stack.toList`** using standard library lemmas
2. **Prove `∃ e, toExprOpt stack[k]! = some e`** using:
   - `hStack : stack.toList.mapM toExprOpt = some stack_spec`
   - `h_mem : stack[k] ∈ stack.toList`
   - Properties of `List.mapM`

**Constraints:**
- Use Lean 4.20.0-rc2 syntax
- Prefer standard library lemmas over custom axioms
- If you need helper lemmas, state them clearly
- The proofs should be straightforward (these are standard list/array properties)

**Bonus:** If you can also prove the helper lemmas in `KernelExtras.lean` (Array.mem_toList_get and List.mapM_some_of_mem), that would eliminate the need for sorry in those files too!

---

## Why This Matters

This completes the **key-based refactor** which:
1. ✅ **Eliminates TRUSTED HashMap.values property** - No longer needed!
2. ✅ **Strictly stronger** - Key-based reasoning is more direct
3. ✅ **Uses existing witnesses** - FloatBindWitness already has stack indices

These two sorries are the last pieces to make the base case proof complete!

---

**File to modify:** `Metamath/Kernel.lean`, lines 2462-2466 and 2469-2473
**Helper lemmas file:** `Metamath/KernelExtras.lean`, lines 29-30 and 21-23

Thank you! 🎯
