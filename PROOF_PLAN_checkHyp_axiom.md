# Proof Plan: Eliminate checkHyp_ensures_floats_typed Axiom

## Current Status

**File:** `Metamath/KernelClean.lean`, line 806
**Type:** `axiom` (unproven assumption)
**Impact:** Blocks ALL Phase 6 step soundness proofs
**Effort Estimate:** 8-12 hours

## What the Axiom Claims

```lean
axiom checkHyp_ensures_floats_typed :
  checkHyp db hyps stack off 0 ∅ = .ok σ_impl →
  (∀ i < hyps.size,
    if hyps[i] maps to float hyp (c, v) in db
    then σ_impl[v] exists and has correct type c)
```

**In plain English:** If `checkHyp` succeeds starting from empty substitution, then every floating hypothesis variable is bound in the result with a value of the correct type.

## Why It's True

The `checkHyp` function (Verify.lean:401-418) loops through hypotheses:
- For **floating hyps** (`ess = false`): Inserts binding `subst[v] := val`
- For **essential hyps** (`ess = true`): Validates using existing `subst`
- Type checking: Ensures `f[0]! == val[0]!` (typecode match)

So by construction, every float variable gets bound with a correctly-typed value.

## Proof Strategy (from Archive)

The file `codex_archive/Verify/Proofs.lean` contains a **COMPLETE PROVEN** lemma:

```lean
lemma checkHyp_preserves_HypProp
    {i : Nat} {subst σ : Std.HashMap String Formula}
    (hi : i ≤ hyps.size)
    (hprop : HypProp i subst)
    (hrun : checkHyp i subst = .ok σ) :
    HypProp hyps.size σ
```

Where `HypProp n σ` means: "Every binding in σ came from a float hyp at index < n"

**Proof technique:** Strong induction on `k = hyps.size - i`
- Base case (k=0): i = hyps.size, done
- Inductive case: Process hyp[i], recurse on i+1

## Implementation Plan

### Option 1: Extend HypProp (Recommended)

**Step 1:** Define enriched invariant in KernelClean.lean

```lean
private def HypPropTyped (n : Nat) (σ : HashMap String Formula) : Prop :=
  ∀ v val, σ[v]? = some val →
    ∃ (j : Nat) (c : String),
      j < n ∧
      match db.find? hyps[j] with
      | some (.hyp false f _) =>
          f.size = 2 ∧
          match f[0]!, f[1]! with
          | .const c', .var v' =>
              v' = v ∧ c' = c ∧
              val.size > 0 ∧ (toExpr val).typecode = ⟨c⟩
          | _, _ => False
      | _ => False
```

**Step 2:** Prove preservation by adapting archive proof

```lean
lemma checkHyp_preserves_HypPropTyped
    {i : Nat} {subst σ : HashMap String Formula}
    (hi : i ≤ hyps.size)
    (hprop : HypPropTyped i subst)
    (hrun : checkHyp i subst = .ok σ) :
    HypPropTyped hyps.size σ := by
  -- Copy structure from checkHyp_preserves_HypProp
  -- Add typing checks at each float hypothesis case
  sorry
```

**Step 3:** Prove main axiom from lemma

```lean
theorem checkHyp_ensures_floats_typed ... := by
  have h := checkHyp_preserves_HypPropTyped
    (hi := Nat.le_refl _)
    (hprop := by intro v val h; simp at h) -- empty map satisfies invariant
    (hrun := h_ok)
  -- h gives us: HypPropTyped hyps.size σ_impl
  -- Massage into required form
  sorry
```

### Option 2: Direct Proof (Alternative)

Copy the entire `checkHyp_preserves_HypProp` proof, inline the typing checks.

**Pros:** Self-contained, no dependencies
**Cons:** More code duplication (~150 lines)

## Execution Steps

### Phase 1: Setup (1-2 hours)
1. ✅ Study checkHyp implementation (Verify.lean:401-418)
2. ✅ Study archive proof (codex_archive/Verify/Proofs.lean:115-270)
3. ⏳ Define HypPropTyped invariant
4. ⏳ Prove HypPropTyped.mono (monotonicity lemma)
5. ⏳ Prove empty substitution satisfies invariant

### Phase 2: Main Induction (4-6 hours)
6. ⏳ Set up strong induction structure
7. ⏳ Prove base case (i = hyps.size)
8. ⏳ Prove inductive step:
   - Handle essential hypothesis case
   - Handle floating hypothesis case (KEY: add typing check)
   - Apply IH on i+1

### Phase 3: Finalization (2-3 hours)
9. ⏳ Convert lemma to axiom form
10. ⏳ Replace axiom with theorem
11. ⏳ Verify build passes
12. ⏳ Check that downstream proofs now work

## Success Criteria

- [ ] `checkHyp_ensures_floats_typed` changes from `axiom` to `theorem`
- [ ] Proof is ~150-200 lines (similar to archive proof)
- [ ] Build passes with no new errors
- [ ] Can mark todo as COMPLETE

## Dependencies

**Required:**
- `checkHyp` definition (Verify.lean:401) - ✅ exists
- Strong induction pattern - ✅ exists in archive
- HashMap reasoning - ✅ standard library

**Optional:**
- Could extract `FloatBindWitness` from archive if useful
- Could factor out common lemmas with archive proof

## Risk Assessment

**LOW RISK** because:
- ✅ Proven reference code exists
- ✅ Property is true by construction
- ✅ No research needed, just translation work
- ✅ Clear 3-phase execution plan

## Estimated Timeline

- **Optimistic:** 6-8 hours (if proof adapts cleanly)
- **Realistic:** 8-12 hours (with debugging)
- **Pessimistic:** 12-16 hours (if type reasoning is tricky)

## Next Action

**START:** Define `HypPropTyped` invariant in KernelClean.lean and prove basic properties.
