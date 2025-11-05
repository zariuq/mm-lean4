# Group E Proof Attempt

**Reality Check:** These axioms are embedded INSIDE the proof of `stepNormal_impl_correct` (lines 1814 and 1847) and depend on many variables from the enclosing scope (`σ_spec`, `e_concl`, `stack_before`, `fr_callee`, etc.).

To truly prove them, I need to either:
1. Extract them as standalone theorems (requires adding ~15 parameters each)
2. Replace the `axiom` keywords with actual proof tactics inline

Let me attempt option 2 for the simpler one:

---

## Attempt: stack_after_stepAssert

**What it needs to prove:**
Given:
- `stepAssert db pr f fr_impl = .ok pr'` (line 436 does: `pr' = { pr with stack := (pr.stack.shrink off).push concl }`)
- `stack_after = applySubst σ_spec e_concl :: stack_before.drop fr_callee.mand.length`

Prove:
- `∀ i < pr'.stack.size, ∃ e, toExpr pr'.stack[i] = some e ∧ e ∈ stack_after`

**Key facts available:**
- `stack_before = needed.reverse ++ remaining` (from stack_shape_from_checkHyp - but that's also an axiom!)
- `concl` comes from `f.subst σ_impl`
- `off = pr.stack.size - fr_impl.hyps.size`

**Proof sketch:**
```lean
theorem stack_after_stepAssert ... := by
  intro pr pr' stack_after h_step h_stack_after

  -- Unfold stepAssert to see pr'.stack = (pr.stack.shrink off).push concl
  unfold Metamath.Verify.stepAssert at h_step
  cases fr_impl with | mk dj hyps =>
  simp at h_step
  split at h_step
  · -- Case: hyps.size ≤ pr.stack.size
    -- Extract concl from the do-bind
    cases h_subst : checkHyp db hyps pr.stack ⟨_, _⟩ 0 ∅ with
    | error e => simp [h_subst] at h_step
    | ok σ_impl =>
      simp [h_subst] at h_step
      -- Continue through DV check...
      sorry -- Need to extract concl and show pr'.stack = (pr.stack.shrink off).push concl

      -- Then use:
      -- 1. stack_shrink_correct to show first `off` elements convert
      -- 2. Show concl converts to applySubst σ_spec e_concl
      -- 3. Use stack_push_correspondence to combine

  · -- Case: stack underflow - contradiction
    simp at h_step
```

**Blockers:**
1. Need to extract `concl` from the monadic bind chain in stepAssert
2. Need `f.subst σ_impl = .ok concl → toExpr concl = some (applySubst σ_spec e_concl)`
   - This requires proving the substitution homomorphism!
3. Still depends on `stack_shape_from_checkHyp` (the other axiom)

---

## Attempt: stack_shape_from_checkHyp

**What it needs to prove:**
Given:
- `fr_impl.hyps.size ≤ pr.stack.size`
- `∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack_before`
- `needed = fr_callee.mand.map (...)`

Prove:
- `∃ remaining, stack_before = needed.reverse ++ remaining`

**This requires:**
Mario/Chad said: "Zipped view lemma: mapM toExpr + BEq→Eq → elementwise equality"

```lean
theorem stack_shape_from_checkHyp ... := by
  intro pr stack_before needed h_stack_size h_stack_before h_needed_def

  -- Key insight: checkHyp succeeded (we're inside stepAssert success case)
  -- This means the top |hyps| elements of pr.stack match the hypotheses

  -- Step 1: Extract that mapM toExpr on pr.stack succeeds
  sorry -- Need: pr.stack.toList.mapM toExpr = some stack_before

  -- Step 2: Show top |hyps| elements convert to needed.reverse
  sorry -- Need: checkHyp success → top elements match hypotheses

  -- Step 3: Remaining elements form the "rest"
  sorry -- Pure list: if xs = ys ++ zs and |ys| = k, then drop k xs = zs (modulo reverse)
```

**Blockers:**
1. Need to connect checkHyp success to element-wise matching
2. Need to understand checkHyp's recursion over hypotheses
3. This is the ~100+ line proof Mario/Chad mentioned

---

## Honest Assessment

These axioms require:
1. **Substitution homomorphism**: `f.subst σ_impl` converts to `applySubst σ_spec`
2. **checkHyp inversion**: Understanding what checkHyp success means for the stack
3. **They're interdependent**: stack_after needs stack_shape!

**Time estimate:** 2-4 hours of focused work per axiom (Mario/Chad were right!)

**Current status:** I can outline the strategy but hitting the implementation details requires:
- Proving substitution properties
- Deep checkHyp analysis
- Careful array↔list reasoning

This is beyond a quick inline fix.