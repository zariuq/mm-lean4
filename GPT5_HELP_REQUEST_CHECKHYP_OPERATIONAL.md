# GPT-5 Pro Help Request: Eliminate checkHyp_operational_semantics Axiom

**Date:** 2025-11-01
**Context:** Metamath verifier in Lean 4
**Status:** AXIOM 2 fully proven, but using one operational semantics axiom

## What We've Accomplished ✅

We successfully eliminated AXIOM 2 by:
1. Building Phase 5 infrastructure (Theorems A-D, 195 lines proven)
2. Proving `checkHyp_ensures_floats_typed` (82 lines, no sorries)
3. Using a simpler operational axiom: `checkHyp_operational_semantics`

**Location:** `Metamath/KernelClean.lean`, lines 902-1008

## The Remaining Axiom

```lean
axiom checkHyp_operational_semantics
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ_impl : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ_impl →
    FloatsProcessed db hyps hyps.size σ_impl
```

**What it says:** If checkHyp succeeds starting from index 0 with empty substitution, then the result satisfies `FloatsProcessed` (all floating hypotheses are validated).

## The checkHyp Implementation

**Location:** `Metamath/Verify.lean`, lines 401-418

```lean
variable (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) in
def checkHyp (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(...)
    if let some (.hyp ess f _) := db.find? hyps[i] then
      if f[0]! == val[0]! then
        if ess then
          if (← f.subst subst) == val then
            checkHyp (i+1) subst  -- Essential: σ unchanged
          else throw "type error in substitution"
        else
          checkHyp (i+1) (subst.insert f[1]!.value val)  -- Float: insert
      else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
    else unreachable!
  else pure subst  -- Base case: return σ
```

**Key structure:**
- Recursively processes hypotheses from index `i` to `hyps.size`
- For floats: validates typecode (`f[0]! == val[0]!`), inserts binding, recurses
- For essentials: validates match, recurses with same σ
- Base case (`i ≥ hyps.size`): returns σ unchanged

## Phase 5 Infrastructure (Already Proven!)

**Definitions:**
```lean
def FloatReq (db : DB) (hyps : Array String) (σ : HashMap String Formula) (j : Nat) : Prop :=
  j < hyps.size →
  match db.find? hyps[j]! with
  | some (.hyp false f _) =>
      f.size = 2 →
      match f[0]!, f[1]! with
      | .const c, .var v =>
          ∃ val, σ[v]? = some val ∧ val.size > 0 ∧ (toExpr val).typecode = ⟨c⟩
      | _, _ => True
  | _ => True

def FloatsProcessed (db : DB) (hyps : Array String) (n : Nat) (σ : HashMap String Formula) : Prop :=
  ∀ j, j < n → FloatReq db hyps σ j
```

**Proven Theorems:**
- **Theorem A** (`FloatReq_of_insert_self`): Current float satisfied after inserting its binding
- **Theorem B** (`FloatReq_preserve_of_insert_ne`): Earlier floats preserved when inserting at different key
- **Theorem C** (`FloatsProcessed_preserve_insert`): All floats j<n preserved by insertion
- **Theorem D** (`FloatsProcessed_succ_of_insert`): Extend invariant from n to n+1

All 4 theorems are **fully proven** with no sorries (195 lines total).

## The Problem

To prove `checkHyp_operational_semantics`, we need to show:
```
checkHyp 0 ∅ = ok σ_impl → FloatsProcessed db hyps hyps.size σ_impl
```

**Proof strategy:**
```lean
lemma checkHyp_invariant (i : Nat) (σ_start σ_impl : HashMap String Formula)
    (h_start : FloatsProcessed db hyps i σ_start)
    (h_success : checkHyp db hyps stack off i σ_start = ok σ_impl) :
    FloatsProcessed db hyps hyps.size σ_impl := by
  -- Induction on (hyps.size - i)
  -- Base case (i ≥ hyps.size): checkHyp returns σ_start, so σ_impl = σ_start
  -- Step case (i < hyps.size):
  --   - checkHyp processes hyps[i] and recurses to i+1
  --   - For float: use Theorem D to extend FloatsProcessed from i to i+1
  --   - For essential: FloatsProcessed i preserved
  --   - Apply IH to get FloatsProcessed hyps.size
```

**The blocker:** We cannot unfold checkHyp's definition because:
1. It's defined in a different module (`Verify.lean`)
2. It uses monadic recursion with `do` notation and `Except`
3. It's defined in a `variable` section with specific parameters

## What We've Tried

1. **Induction on (hyps.size - i):** Set up correctly, but can't proceed without unfolding checkHyp
2. **Reasoning about Except monad:** Too complex without equation lemmas
3. **Axiomatizing equation lemmas:** Still adds axioms (just different ones)

## The Question for GPT-5 Pro

**How do we eliminate the `checkHyp_operational_semantics` axiom in Lean 4?**

Specifically:
1. Can we access Lean 4's auto-generated equation lemmas for `checkHyp`?
2. Should we add equation lemmas as axioms (e.g., `checkHyp_base`, `checkHyp_step`)?
3. Should we move this proof to `Verify.lean` where `checkHyp` is defined?
4. Is there a way to reason about monadic recursion without unfolding?
5. Can we use Lean 4's `termination_by` or well-founded recursion tactics?

**What we need:**
- Concrete Lean 4 code showing how to either:
  - Access/use checkHyp's equation lemmas
  - Prove the invariant lemma using strong induction
  - Work with the Except monad in proofs
  - OR: Justification that `checkHyp_operational_semantics` is a reasonable axiom to keep

## Context Files

**Key files:**
- `Metamath/Verify.lean`: checkHyp definition (lines 401-418)
- `Metamath/KernelClean.lean`: Phase 5 infrastructure and axiom (lines 664-1008)
- Phase 5 theorems A-D are already proven (no sorries)

## What Success Looks Like

**Ideal:** Replace `axiom checkHyp_operational_semantics` with `theorem checkHyp_operational_semantics` and fill in the proof.

**Acceptable:**
- Theorem with minimal axioms (e.g., just equation lemmas that are obviously true)
- Clear explanation of why it's not feasible and `checkHyp_operational_semantics` is reasonable
- Concrete steps to move the proof to Verify.lean if that's the only way

## Additional Info

**Lean version:** 4.20.0-rc2
**Project:** Metamath verifier with proven correctness
**Goal:** Eliminate all axioms or reduce to minimal, obviously-sound ones

The infrastructure (Theorems A-D) provides **exactly** the right tools to handle each recursive case. We just need to connect them to checkHyp's actual execution.

---

**Bottom line:** We've proven 277 lines of verification infrastructure and AXIOM 2. We're stuck on this last operational semantics connection. How do we finish it?
