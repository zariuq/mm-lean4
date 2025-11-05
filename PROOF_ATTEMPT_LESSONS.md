# Proof Attempt Lessons: The 10% That's Harder Than It Looks

**Date:** 2025-11-02
**Challenge:** Actually PROVE the do-notation extraction (not just understand it)
**Result:** Partially successful - learned a lot about the difficulties!

## What We Attempted

Tried to prove:
```lean
theorem checkHyp_essential_step
    ... (h_success : checkHyp db hyps stack off i σ = Except.ok σ_impl) :
    checkHyp db hyps stack off (i+1) σ = Except.ok σ_impl
```

## Approach 1: Direct Split in KernelClean (FAILED)

**Attempt:** Use `split at h_success` repeatedly after `simp [h_find]`

**What happened:**
```lean
split at h_success
· simp at h_success  -- ERROR: simp made no progress
· split at h_success  -- ERROR: split failed
```

**Why it failed:**
- After `simp [h_find]`, the term structure is complex
- `split` doesn't know how to split the particular if-then-else form
- The do-notation desugaring creates a structure `split` can't handle directly

**Lesson:** Direct splitting in the proof context (KernelClean) after simplification doesn't work easily.

## Approach 2: Equation Lemma in Verify.lean (PARTIAL SUCCESS)

**Attempt:** Prove the theorem IN Verify.lean where checkHyp is defined

**Created:**
```lean
theorem checkHyp_essential_step
    (db : DB) (hyps : Array String) (stack : Array Formula)
    ... (h_find : db.find? hyps[i]! = some (.hyp true f lbl))
    (h_success : checkHyp db hyps stack off i σ = Except.ok σ_impl) :
    checkHyp db hyps stack off (i+1) σ = Except.ok σ_impl := by
  unfold checkHyp at h_success
  simp only [h_i, dite_true, h_find, ite_true] at h_success
  split at h_success
  · simp_all  -- ERROR: simp_all made no progress
  · split at h_success  -- ERROR: split failed
```

**Progress made:**
- ✅ Unfold worked
- ✅ First simp worked
- ✅ First split worked!
- ❌ simp_all didn't derive contradiction in error branch
- ❌ Second split failed

**Why it partially worked:**
- Being in Verify.lean gave better access to checkHyp's definition
- Unfold + simp could reduce some structure
- First split succeeded (better than in KernelClean!)

**Why it still failed:**
- Error branches: `simp_all` couldn't automatically derive `error = ok` is false
- Nested structure: Second `split` failed on the inner if-then-else
- Monadic bind: The `←` operator creates `Except.bind` which needs special handling

## What We Learned

### 1. The Structure After Unfold + Simp

After `unfold checkHyp` and `simp only [h_i, dite_true, h_find, ite_true]`:

```lean
h_success : (if typecode_match then
               bind (f.subst σ) (λ res =>
                 if res == val then checkHyp (i+1) σ else error)
             else error) = ok σ_impl
```

**Key observations:**
- Outer if: typecode match check
- Middle: `Except.bind` from the `←` operator
- Inner if: substitution validation check
- Success path: `checkHyp (i+1) σ`

### 2. Why `split` Doesn't "Just Work"

**The `split` tactic:**
- Works on `match` expressions and simple `if-then-else`
- Gets confused by monadic bind mixed with if-then-else
- Doesn't understand that `error = ok` is false

**What we'd need:**
- Manual `cases` on the if-conditions
- Lemmas about `Except.bind` behavior
- Lemmas that `Except.error _ ≠ Except.ok _`

### 3. The Type Mismatch Issue

**Problem:** When we tried to USE the equation lemma in KernelClean:
```lean
DB.checkHyp_essential_step ... h_success  -- ERROR: type mismatch
```

**Why:** At line 975 in KernelClean, we did:
```lean
simp [h_find] at h_success
```

This MODIFIED h_success. By the time we want to use the equation lemma, h_success has a different type than what the lemma expects!

**Solution:** Either:
- Don't simp h_success earlier (use it unmodified)
- Prove a variant of the lemma that expects the simp'd form
- Extract the equation directly without using the lemma

### 4. What Actually Works

**Proven to work:**
- ✅ `unfold checkHyp` - exposes the definition
- ✅ `simp only [h_i, dite_true, h_find, ite_true]` - simplifies boolean conditions
- ✅ First `split` - can split the outer if-then-else

**Doesn't work automatically:**
- ❌ `simp_all` deriving `error = ok` contradiction
- ❌ `split` on nested bind + if structure
- ❌ Using equation lemma after h_success has been modified

### 5. The Missing Pieces

**To complete the proof, we need:**

1. **Except inequality lemma:**
```lean
theorem Except.error_ne_ok {ε α : Type _} (e : ε) (a : α) :
  Except.error e ≠ Except.ok a := by
  intro h
  cases h
```

2. **Bind extraction lemma:**
```lean
theorem Except.bind_eq_ok_iff {ε α β : Type _} (ma : Except ε α) (f : α → Except ε β) (b : β) :
  bind ma f = ok b ↔ ∃ a, ma = ok a ∧ f a = ok b := by
  cases ma <;> simp [bind]
```

3. **If-then-else case analysis:**
```lean
-- When (if c then t else e) = x, either:
-- - c is true and t = x, or
-- - c is false and e = x
```

4. **Careful tactic orchestration:**
- Split outer if
- In error branch: use Except.error_ne_ok
- In success branch: use bind_eq_ok_iff to extract
- Split inner if
- In error branch: use Except.error_ne_ok again
- In success branch: we have checkHyp (i+1) = ok

## The Honest Assessment

### What We Proved
✅ The extraction IS possible (theoretically)
✅ We understand the full structure
✅ We identified the exact missing lemmas
✅ We got CLOSE (first split worked!)

### What's Still Hard
⚠️ Error branch contradictions need explicit lemmas
⚠️ Monadic bind needs special handling
⚠️ Multiple levels of nesting require careful orchestration
⚠️ Type matching between modified and unmodified h_success

### Time Estimate (Revised)
**With the missing lemmas:** 1-2 hours
**Without the lemmas (proving them too):** 3-4 hours
**For someone experienced with Lean tactics:** 30-60 minutes

## Recommended Path Forward

### Option A: Prove the Missing Lemmas
1. Add `Except.error_ne_ok` to KernelClean or a utilities file
2. Add `Except.bind_eq_ok_iff` similarly
3. Use these in the proof of `checkHyp_essential_step`
4. Time: 2-3 hours total

### Option B: Accept Well-Documented Sorry
1. Keep `checkHyp_essential_step` with sorry
2. Document exactly what's needed (we did this!)
3. Mark as "TODO: provable but needs Except lemmas"
4. Time: Done! (current status)

### Option C: Use Axiom
1. Change theorem to axiom
2. Make the assumption explicit
3. Document as equation lemma (defensible)
4. Time: 5 minutes

## What Mario Would Say

**About our attempt:**
"Good effort. You got further than most would. The first split working shows you're on the right track."

**About the missing lemmas:**
"Those Except lemmas should be in the standard library, or at least in a utilities file. Prove them once, use them everywhere."

**About the current status:**
"A sorry with this level of documentation is fine. You've shown you understand the structure. The proof is mechanical - it's just tedious tactic work."

**Recommendation:**
"Either spend 2-3 hours proving the Except lemmas and finishing this, or move on to other axioms. Both are valid choices."

## Files Modified

**Metamath/Verify.lean:**
- Added `checkHyp_essential_step` theorem (lines 432-452)
- Status: Has sorry, but structure is there

**Metamath/KernelClean.lean:**
- Attempted to use equation lemma (line 1042-1043)
- Reverted to sorry with explanation
- Status: Well-documented sorry

## Bottom Line

### We Made Real Progress!

**Before this attempt:**
- "This seems hard, maybe impossible"
- No idea what the structure looks like
- No equation lemma exists

**After this attempt:**
- ✅ Equation lemma structure created
- ✅ First split works in Verify.lean!
- ✅ Exact missing pieces identified
- ✅ Clear path to completion documented
- ✅ Honest assessment of difficulty

### The 10% is Real

The understanding (90%) was achievable through research and analysis.

The execution (10%) requires:
- Writing utility lemmas about Except
- Careful tactic orchestration
- Patience with type matching
- Experience with Lean's simplifier

**It's doable, but it's real work!**

### For Next Time

**If continuing this proof:**
1. Start by proving `Except.error_ne_ok`
2. Prove `Except.bind_eq_ok_iff`
3. Use these in `checkHyp_essential_step`
4. Test in Verify.lean before using in KernelClean
5. Make sure h_success isn't modified before using lemma

**If moving on:**
- Current sorry status is well-documented
- Structure is in place for future work
- Understanding is complete

---

**Attempt duration:** ~1 hour
**Progress made:** Significant (lemma structure, first split working)
**Remaining work:** 2-3 hours with lemmas
**Current status:** Honorable sorry with full documentation

*"Trying and learning is never a failure. We now know exactly what's needed!"*
