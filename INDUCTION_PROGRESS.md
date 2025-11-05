# Induction Proof Progress - November 4, 2025

## Major Achievement: Auxiliary Lemma COMPLETE!

### What Was Proven

**`checkHyp_implies_hyp_at_index`** (lines 1694-1738): ✅ **COMPLETE - No sorries!**

```lean
private theorem checkHyp_implies_hyp_at_index
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (i : Nat) (hi : i < hyps.size)
    (σ_in σ_out : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off i σ_in = Except.ok σ_out →
    ∃ (o : Verify.Object), db.find? hyps[i]! = some o ∧
      (∃ (ess : Bool) (f : Verify.Formula) (lbl : String), o = .hyp ess f lbl)
```

**Proof Structure:**
1. **Case split** on `db.find? hyps[i]`:
   - `none` → ✅ Contradiction (unreachable! ≠ ok)
   - `some obj` → case split on obj:
     - `.const`, `.var`, `.assert` → ✅ Contradiction (unreachable! ≠ ok)
     - `.hyp ess f lbl` → ✅ Extract witnesses

2. **Key technique**: `simp [h_find]` after unfolding checkHyp
   - This rewrites the pattern match with our case hypothesis
   - Exposes `unreachable!` in contradiction branches
   - Lean automatically closes the goal (unreachable! has no valid inhabitants)

3. **Success case** (lines 1729-1738):
   - Use `refine ⟨.hyp ess f lbl, ?_, ?_⟩` to provide existential witnesses
   - Prove `db.find? hyps[i]! = some (.hyp ess f lbl)` using h_find
   - Provide inner existentials: `⟨ess, f, lbl, rfl⟩`

### What Remains

**`checkHyp_success_implies_HypsWellFormed`** (line 1761): ⏳ One sorry

```lean
theorem checkHyp_success_implies_HypsWellFormed
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ →
    HypsWellFormed db hyps
```

**The Challenge:**
- We have: `checkHyp 0 ∅ = ok σ`
- We want: At any index `i < hyps.size`, db.find? hyps[i] returns .hyp
- The auxiliary lemma needs: `checkHyp i σ_in = ok σ_out` for some σ_in, σ_out
- **Gap**: Extract intermediate state at index i from global success at 0

**Proof Strategy (needs ~20-30 lines):**
1. Induction on i to build up the intermediate states
2. Base case (i=0): We have checkHyp 0 ∅ = ok σ, apply auxiliary directly
3. Step case (i=k+1):
   - IH gives us checkHyp k σ_k = ok σ_{k+1} for some σ_k, σ_{k+1}
   - Use equation lemma to show checkHyp (k+1) σ_{k+1} = ok σ_{k+2}
   - Apply auxiliary at k+1

**Alternative Strategy (simpler but requires lemma):**
- Prove auxiliary lemma: "checkHyp from 0 to n succeeds iff checkHyp at each i < n succeeds"
- This is the "recursion unwinding" lemma
- Then apply checkHyp_implies_hyp_at_index directly

### Build Status

✅ **Builds successfully!**
- Auxiliary lemma: Complete (no sorries)
- Main theorem: One sorry remaining
- All type checking passes

### Lines of Code

**Proven:**
- Auxiliary lemma: 45 lines (fully proven!)
- Case analysis: 3 branches, all complete
- Success case: 9 lines
- Contradiction cases: ~5 lines each (solved with simp!)

**Remaining:**
- Transport proof: ~20-30 lines
- Total project: ~1,645 lines proven (auxiliary lemma adds ~45 lines)

### Why This Matters

1. **The hard part is done**: Extracting the witness from checkHyp success at a given index is PROVEN
2. **Contradiction cases are elegant**: `simp [h_find]` automatically closes them!
3. **Only recursion unwinding remains**: This is mechanical but requires careful induction

### Comparison to Initial Estimate

**Initial estimate**: ~40-60 lines for HypsWellFormed
**Current status**:
- Auxiliary: 45 lines (complete)
- Transport: ~20-30 lines (pending)
- **Total**: ~65-75 lines (slightly over estimate, but architectural improvement)

The auxiliary lemma is reusable and makes the proof clearer!

### Next Steps

#### Option A: Complete the transport proof (~20-30 lines)
- Induction on i from 0 to target
- Extract intermediate states at each step
- Apply auxiliary lemma

#### Option B: Prove recursion unwinding lemma (~30-40 lines)
- More general: "checkHyp 0 succeeds → ∀ i, ∃ σ_in σ_out, checkHyp i σ_in succeeds"
- Then main theorem is trivial
- Better architecture, slightly more work

### Technical Notes

**What worked well:**
- `cases h_find : db.find? hyps[i]` - Equation binding crucial
- `simp [h_find]` after unfold - Automatically solves contradictions!
- `refine ⟨.hyp ess f lbl, ?_, ?_⟩` - Clean existential introduction

**Lean 4 insights:**
- `unreachable!` has type `∀ α, α` (uninhabited)
- When simp exposes `unreachable! = .ok _`, Lean closes the goal automatically
- Pattern match compilation with `if let` reduces nicely under `simp`

**Mario's techniques visible:**
- Case split with equation binding
- Aggressive simp to expose contradictions
- Auxiliary lemmas for reusable components

### Philosophical Note

This proof demonstrates **"runtime checks enforce invariants"**:
- If checkHyp returned `.ok`, it didn't hit `unreachable!`
- Therefore, all pattern matches succeeded
- Therefore, all lookups found `.hyp` objects

We're **extracting implicit guarantees from executable code**. The auxiliary lemma makes this extraction explicit and reusable.

---

**Status**: Auxiliary lemma complete (✅), transport proof pending (~20-30 lines)
**Confidence**: High - the hard part is done, remaining work is mechanical
**Next session**: Complete transport proof, then tackle FloatsWellStructured
