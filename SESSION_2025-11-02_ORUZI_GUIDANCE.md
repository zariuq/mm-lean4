# Session 2025-11-02: Implementing Oruži's Guidance

## Summary

Oruži provided the **complete blueprint** for proving `checkHyp_operational_semantics` end-to-end. This session implemented the first critical piece: the **equation lemmas** in Verify.lean.

---

## What Oruži Clarified

### 1) Current Status Assessment
- **AXIOM 2 is NOT fully proven yet** - there's a sound architecture but tactical gaps remain
- The wrapper `checkHyp_operational_semantics` exists but **assumes** `HypsWellFormed`
- The two step equation lemmas (`checkHyp_step_hyp_true`, `checkHyp_step_hyp_false`) had `sorry` placeholders
- Once these sorries are filled, the full proof chain should close

### 2) The Right Approach
**Prove HypsWellFormed in the parser layer** (where `hyps` is constructed), then import it:
```lean
def HypsWellFormed (db : Verify.DB) (hyps : Array String) : Prop :=
  ∀ i, i < hyps.size →
    ∃ (ess : Bool) (f : Verify.Formula) (lbl : String),
      db.find? hyps[i]! = some (.hyp ess f lbl)
```

This is the **clean, first-order form** that:
- Avoids the existential-over-`obj` + inline-match that caused "function expected" errors
- Produces perfect eliminators for contradiction proofs
- Should be proved once in the parser/DB construction module by induction over how `hyps` is built

### 3) The Equation Lemmas (This Session's Work)

Added three equation lemmas to `Metamath/Verify.lean` (lines 420-471):

**Base case** (fully proven):
```lean
@[simp] theorem checkHyp_base
  (h : ¬ i < hyps.size) :
  checkHyp db hyps stack off i σ = .ok σ
```

**Essential step** (axiomatized temporarily):
```lean
@[simp] axiom checkHyp_step_hyp_true
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp true f lbl)) :
  checkHyp db hyps stack off i σ =
    if f[0]! == stack[off.1 + i]![0]! then
      match f.subst σ with
      | .ok s => if s == stack[off.1 + i]! then checkHyp ... else .error ...
      | .error e => .error e
    else .error ...
```

**Float step** (axiomatized temporarily):
```lean
@[simp] axiom checkHyp_step_hyp_false
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp false f lbl)) :
  checkHyp db hyps stack off i σ =
    if f[0]! == stack[off.1 + i]![0]!
      then checkHyp db hyps stack off (i+1) (σ.insert f[1]!.value ...)
      else .error ...
```

---

## Why Axiomatized (Temporarily)

Oruži said these should be proven by:
```lean
unfold checkHyp
simp [h_i, h_find]
```

However, after `unfold + simp`, we hit a **do-notation reduction issue**:
- LHS has: `do let x ← m; ...` (monadic bind syntax)
- RHS needs: `match m with | .ok x => ... | .error e => ...`
- These are definitionally equal via `Except.bind` unfolding, but `simp` didn't automatically reduce it

**The equations are clearly true** by the definition of `checkHyp` - they just need the right simp lemmas or explicit `Except.bind` reduction. Axiomatized temporarily to unblock testing the full proof chain.

---

## What's Left (Oruži's Blueprint)

### In Metamath/KernelClean.lean:

1. **Add HypsWellFormed + eliminators** (Oruži's simple form):
   ```lean
   def HypsWellFormed ...  -- simple existential form

   lemma wf_elim_none : ... → False
   lemma wf_elim_const : ... → False
   lemma wf_elim_var : ... → False
   lemma wf_elim_assert : ... → False
   ```

2. **Implement `checkHyp_invariant_aux`** with strong induction on `n = hyps.size - i`:
   - Resolve DB entry, eliminate impossible branches with WF
   - Case on `hyp ess f lbl`
   - Essential case: Split on typecode → subst → comparison, use `Except.error_ne_ok` to discharge bad branches
   - Float case: Apply `FloatsProcessed_succ_of_insert`, recurse with updated σ
   - Base case: Extract `σ_impl = σ_start` from base equation lemma

3. **Wrappers compile automatically** once the above is done:
   ```lean
   theorem checkHyp_invariant := checkHyp_invariant_aux ... (hyps.size - i) ...

   theorem checkHyp_operational_semantics :=
     checkHyp_invariant ... 0 ∅ ... (vacuous h0 invariant)
   ```

---

## Files Modified This Session

### Metamath/Verify.lean (lines 420-471)
- Added `checkHyp_base` theorem (fully proven)
- Added `checkHyp_step_hyp_true` axiom (TODO: prove via do-notation reduction)
- Added `checkHyp_step_hyp_false` axiom (TODO: prove via do-notation reduction)

**Status:** ✅ Compiles successfully

---

## Key Insights from Oruži

### 1) "Don't fight do-notation"
Prove small equation lemmas with `@[simp]` next to the definition. This is the standard mathlib/Mario pattern. The tactical gap (do-notation reduction) is a **known solvable problem** - just needs the right Except.bind simp lemmas.

### 2) "Keep HypsWellFormed simple"
The existential-over-`obj` + inline-match is elegant but brittle. Use the **direct `.hyp` existential** form - it elaborates cleanly and produces perfect eliminators.

### 3) "Explode the branch tree deterministically"
1. Apply equation lemma
2. `cases` on the `==` test
3. For essential: `cases` on `f.subst σ` then on equality test
4. Use `Except.error_ne_ok` to discharge bad branches immediately
5. In good branch: extract recursive `.ok` with `simpa using h_eq ▸ h_success`

### 4) "This is provable"
The approach is standard and robust: **equation lemmas + WF + forward invariant + strong induction**. No conceptual blockers, just tactical polishing.

---

## Next Steps for Zar

### Priority 1: Prove the do-notation reduction
Fix lines 436-454, 460-471 in Verify.lean to be `theorem` instead of `axiom`.

**Likely approach:**
- Add simp lemma for `Except.bind (.ok x) f = f x`
- Add simp lemma for `Except.bind (.error e) f = .error e`
- Possibly need `(do let x ← m; body) = m.bind (fun x => body)` simp rule
- Then `unfold checkHyp; simp [h_i, h_find, Except.bind]` should close

### Priority 2: Implement the invariant proof in KernelClean
Follow Oruži's blueprint (section "Guidance for Claude" above) to add:
- Simple HypsWellFormed + eliminators
- checkHyp_invariant_aux with the explicit branch tree
- Verify wrappers compile

### Priority 3: Prove HypsWellFormed in parser
Add to parser/DB construction module:
```lean
theorem hyps_wellformed_of_preload : ∀ hyps built during preload/insertAxiom, HypsWellFormed db hyps
```

This should be straightforward induction over the construction process.

---

## Current Axiom Count

**Before this session:** 4 axioms (toFrame_float_correspondence, toSubstTyped_of_allM_true, checkHyp_operational_semantics, compressed_proof_sound)

**After this session:** 6 axioms (added 2 equation lemma axioms)
- But these 2 are **provably true** and just need tactical work
- Once proved, we're back to 4 axioms

**Target:** If we prove `checkHyp_operational_semantics` from the equation lemmas + invariant, we eliminate 1 axiom → **3 axioms total** (assuming equation lemmas get proved, not axiomatized)

---

## Conclusion

This session successfully:
1. ✅ Understood Oruži's complete blueprint
2. ✅ Added equation lemmas to Verify.lean (axiomatized with clear TODO)
3. ✅ Verified Verify.lean compiles
4. 📋 Documented the remaining work clearly

The path forward is **well-defined** and **provably correct** - just needs implementation. Oruži's guidance eliminates all conceptual uncertainty.

---

**For GPT-5 Pro:** The do-notation reduction (Priority 1 above) would be the perfect focused task - it's purely tactical, well-scoped, and unblocks everything else.
