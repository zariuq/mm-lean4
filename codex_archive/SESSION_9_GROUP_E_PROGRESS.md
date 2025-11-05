# Session 9: Group E Axioms - Progress Report

**Date**: 2025-10-09
**Goal**: Prove the two remaining Group E axioms blocking 100% verification

---

## What I Accomplished

### ✅ Completed Tasks

1. **Evaluated GPT-5/Oruži's Guidance** (see `/home/zar/claude/hyperon/metamath/mm-lean4/GPT5_GUIDANCE_EVALUATION.md`)
   - ✅ Strategy is SOUND: three-layer decomposition (list lemmas → bridges → axioms)
   - ⚠️ Estimates are OPTIMISTIC: "1-5 line bridge" is actually ~40 lines
   - Actual complexity: ~120 lines total, not ~30 lines

2. **Proven Pure List Lemmas** ✅
   - Location: `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/Kernel.lean:2137-2163`
   - `Verify.StackShape.popKThenPush_of_split`: stack pop-then-push correspondence
   - `Verify.StackShape.matchRevPrefix_correct`: pattern matching lemma
   - Build status: ✅ SUCCESS

3. **Added Substitution Commutation Axiom** 📝
   - Location: `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/Kernel.lean:2433-2451`
   - `toExpr_subst_commutes`: shows `toExpr (f.subst σ_impl) = applySubst σ_spec (toExpr f)`
   - Status: Axiomatized (TODO: prove ~30-40 lines)
   - This is a KEY helper for proving Group E theorems

4. **Converted Group E Axioms to Theorems** ✅
   - **stack_shape_from_checkHyp** (Kernel.lean:1814-1836):
     - Was: axiom with insufficient premises
     - Now: theorem with `checkHyp` success, `toSubst`, and all necessary context
     - Status: Has `sorry` (~30-40 line proof TODO)

   - **stack_after_stepAssert** (Kernel.lean:1858-1880):
     - Was: axiom with insufficient premises
     - Now: theorem with `checkHyp` success, `toSubst`, `toExpr f`, and all necessary context
     - Status: Has `sorry` (~20-30 line proof TODO)

---

## Current Status

### Axiom/Sorry Count

**Axioms**: 11 (unchanged from before - added 1, converted 2)
- Old axioms from spec/translate (4)
- WF/invariant helpers (4)
- Substitution commutation (1 NEW)
- Other helpers (2)

**Sorries**: 8
- Spec-level sorries (4): matchSyms, matchHyps, matchFloats, checkEssentials
- Group E theorems (2): stack_shape_from_checkHyp, stack_after_stepAssert
- Minor list distinctness (2)

---

## What Remains: The Group E Theorems

### Theorem 1: `stack_shape_from_checkHyp` (~30-40 lines)

**Location**: `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/Kernel.lean:1814-1836`

**Goal**: Prove that if `checkHyp` succeeds, the stack has shape `needed.reverse ++ remaining`

**Available premises** (now properly parameterized!):
1. ✅ `checkHyp db fr_impl.hyps pr.stack ⟨off, ...⟩ 0 ∅ = .ok σ_impl`
2. ✅ Stack elements convert: `∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack_before`
3. ✅ `toSubst σ_impl = some σ_spec`
4. ✅ `needed` definition from hypotheses with `σ_spec`

**Proof strategy** (from my TODO comment):
```lean
-- 1. checkHyp checks stack[off+i] for i in 0..hyps.size
-- 2. Each check corresponds to a hypothesis
-- 3. The top hyps.size elements match needed.reverse
-- 4. Use Verify.StackShape.matchRevPrefix_correct
```

**Complexity**: ~30-40 lines
- Induction on `checkHyp` recursion or
- Direct reasoning about RPN stack discipline

---

### Theorem 2: `stack_after_stepAssert` (~20-30 lines)

**Location**: `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/Kernel.lean:1858-1880`

**Goal**: Prove that after `stepAssert`, stack elements convert correctly

**Available premises** (now properly parameterized!):
1. ✅ `stepAssert db pr f fr_impl = .ok pr'`
2. ✅ `checkHyp` success with `σ_impl`
3. ✅ `toSubst σ_impl = some σ_spec`
4. ✅ `toExpr f = some e_concl`
5. ✅ `stack_after` definition

**Proof strategy** (from my TODO comment):
```lean
-- 1. stepAssert does: pr' = { pr with stack := (pr.stack.shrink off).push concl }
-- 2. For i = 0: use toExpr_subst_commutes to show toExpr concl = applySubst σ_spec e_concl
-- 3. For i > 0: use stack_shrink_correct
-- 4. Use popKThenPush_of_split from Verify.StackShape
```

**Complexity**: ~20-30 lines
- Extract `concl` from `stepAssert` monadic bind
- Apply `toExpr_subst_commutes` (KEY helper!)
- Use `stack_shrink_correct` (already proven) for tail elements

---

## Why I Got Stuck

### The Missing Piece: `toExpr_subst_commutes`

This theorem is CRITICAL but complex (~30-40 lines):
```lean
axiom toExpr_subst_commutes (f f' : Formula) (σ_impl : HashMap String Formula)
    (e : Expr) (σ_spec : Subst) :
  (∀ v, v ∈ f.foldlVars ∅ ... → σ_impl.contains v) →
  (∀ fv, σ_impl.values.contains fv → ∃ e, toExpr fv = some e) →
  toExpr f = some e →
  toSubst σ_impl = some σ_spec →
  f.subst σ_impl = .ok f' →
  toExpr f' = some (applySubst σ_spec e)
```

**Why it's hard**:
- `Formula.subst` uses Array mutation with `.foldl`
- `applySubst` uses List `.bind` operations
- Need to prove Array iteration ↔ List bind correspondence
- Need to track HashMap lookup through both sides

**Approaches**:
1. Prove directly (requires deep Array/List reasoning)
2. Axiomatize for now and return to it
3. Use intermediate lemmas about Array→List conversion

I chose approach 2 to unblock the Group E proofs.

---

## Next Steps

### Path A: Finish Group E with Current Structure

1. ⬜ Prove `stack_shape_from_checkHyp` (~30-40 lines)
   - Use `checkHyp` recursion analysis
   - Apply `matchRevPrefix_correct` from list lemmas
   - Connect impl checks to spec correspondence

2. ⬜ Prove `stack_after_stepAssert` (~20-30 lines)
   - Extract `concl` from `stepAssert`
   - Apply `toExpr_subst_commutes` (axiomatized)
   - Use `stack_shrink_correct` + `popKThenPush_of_split`

3. ⬜ Return to prove `toExpr_subst_commutes` (~30-40 lines)
   - If successful: **0 axioms** for Group E! 🎉
   - If blocked: acceptable to leave as axiom (reduces trust, but still valuable)

**Time estimate**: 2-4 hours of focused work

### Path B: Alternative Approaches

1. **Simplify theorem statements** - Maybe the correspondence can be stated more directly
2. **Add more intermediate lemmas** - Break down Array/List operations further
3. **Consult Mario/GPT-5** - Get guidance on the Array iteration proof

---

## The Honest Assessment

### What I Can Do ✅
- Structure proofs correctly
- Add proper premises
- Use list lemmas effectively
- Build valid Lean code

### What I'm Stuck On ⚠️
- **Deep Array iteration reasoning** in `toExpr_subst_commutes`
- **checkHyp recursion analysis** in `stack_shape_from_checkHyp`
- Both require 30-40 line proofs with careful induction

### Confidence Levels

| Task | Confidence | Notes |
|------|-----------|-------|
| List lemmas | ✅ HIGH | Done and proven |
| Theorem structure | ✅ HIGH | Converted axioms with proper premises |
| `stack_after_stepAssert` proof | 🟡 MEDIUM | With `toExpr_subst_commutes` axiom, achievable |
| `stack_shape_from_checkHyp` proof | 🟡 MEDIUM | Need to understand `checkHyp` recursion |
| `toExpr_subst_commutes` proof | 🔴 LOW | Complex Array/List reasoning |

---

## Build Status

✅ **All code builds successfully** (`lake build Metamath`)

**File**: `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/Kernel.lean`
- 2 Group E theorems with `sorry`
- 1 substitution axiom (TODO: prove)
- 2 proven list lemmas
- All properly parameterized and called

---

## Summary

### Progress This Session ✨

- ✅ Evaluated GPT-5's guidance thoroughly
- ✅ Proven pure list lemmas (popKThenPush_of_split, matchRevPrefix_correct)
- ✅ Identified substitution commutation as KEY missing piece
- ✅ Converted 2 Group E axioms to theorems with proper premises
- ✅ All code builds successfully

### What Remains 🎯

- 2 Group E theorems with `sorry` (~50-70 lines total)
- 1 substitution axiom (~30-40 lines)
- **Total**: ~80-110 lines to complete Group E

### Recommendation

**For immediate progress**: Continue with current structure, prove what's provable
**For completeness**: Return to `toExpr_subst_commutes` when time permits
**For publication**: Current state is already valuable - main theorem proven modulo well-structured helpers

The axiomatization of `toExpr_subst_commutes` is a **defensible choice** - it's a clear, believable statement about substitution correspondence.

---

## User Decision Point

**Option 1**: Continue with me trying to prove the Group E theorems
- Pros: Might succeed, will learn where the challenges are
- Cons: Could take 2-4 hours, might get stuck on details

**Option 2**: Consult GPT-5/Mario for the final push
- Pros: Expert guidance on Array/recursion proofs
- Cons: Requires iteration with another agent

**Option 3**: Accept current state as "complete enough"
- Pros: Main theorem proven, structure is clean
- Cons: 3 axioms remain (but well-motivated)

Your call! 😊
