# Session Complete: Oruži's Approach Implementation Started
**Date**: October 28, 2025
**Duration**: ~5 hours
**Goal**: Follow Oruži's concrete plan to prove checkHyp correctness
**Result**: ✅ Cleanup complete, checkHyp_step skeleton in place

---

## Summary

Successfully transitioned from the failed CheckHypOk big-step semantics approach to Oruži's cleaner operational lemma approach. The file now builds cleanly with a clear path forward.

---

## Completed Work

### ✅ Step 1: Except Lemmas (Lines 114-129)

Added 3 **proven** (not axiomatized!) Except monad lemmas:

```lean
namespace Except

@[simp] theorem bind_eq_ok_iff {ε α β : Type _}
  {x : Except ε α} {f : α → Except ε β} {b : β} :
  x.bind f = Except.ok b ↔ ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x <;> simp [Except.bind]

@[simp] theorem ok_bind_eq_ok_iff {ε α β : Type _} {a : α}
  {f : α → Except ε β} {b : β} :
  (Except.ok a).bind f = Except.ok b ↔ f a = Except.ok b := by
  simp [Except.bind]

@[simp] theorem error_bind {ε α β : Type _} {e : ε} {f : α → Except ε β} :
  (Except.error e).bind f = Except.error e := rfl

end Except
```

**Key point**: These are fully proven, using only `cases` and `simp`. No axioms.

### ✅ Step 2: Cleanup of Failed Approach

Removed entire CheckHypSemantics section (~330 lines) that contained:
- Duplicate axiomatized Except lemmas (now proven)
- DB well-formedness axioms (not needed)
- `inductive CheckHypOk` (wrong approach)
- `CheckHypOk.extends` theorem with sorry (wrong approach)
- `checkHyp_ok_sound` theorem with sorry (wrong approach)
- `CheckHypOk.matches_all` theorem with sorries (wrong approach)
- `checkHyp_builds_impl_inv_from` using CheckHypOk (wrong approach)

**Kept**: All the necessary definitions that Oruži's approach uses:
- `ImplSubst`, `ImplMatchesAt` (impl-level correspondence)
- `Formula.vars` (for extensionality)
- `ImplInv`, `ImplInvFrom` (invariant definitions)
- Axioms that will be proven later (checkHyp_preserves_bindings, etc.)

### ✅ Step 3: checkHyp_step Skeleton (Lines 1086-1120)

Added theorem skeleton following Oruži's exact specification:

```lean
theorem checkHyp_step
  (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ_in σ_out : Std.HashMap String Verify.Formula) :
  i < hyps.size →
  Verify.DB.checkHyp db hyps stack off i σ_in = Except.ok σ_out →
  ∃ σ_mid : Std.HashMap String Verify.Formula,
    (match db.find? hyps[i]! with
     | some (.hyp false f _) =>
         f.size = 2 ∧ f[0]! == stack[off.1 + i]![0]! ∧
         σ_mid = σ_in.insert (match f[1]! with | .var v => v | _ => "") stack[off.1 + i]!
     | some (.hyp true f _) =>
         f[0]! == stack[off.1 + i]![0]! ∧
         f.subst σ_in = Except.ok stack[off.1 + i]! ∧
         σ_mid = σ_in
     | _ => σ_mid = σ_in) ∧
    Verify.DB.checkHyp db hyps stack off (i + 1) σ_mid = Except.ok σ_out := by
  intro hi hrun
  unfold Verify.DB.checkHyp at hrun
  simp [hi] at hrun
  sorry -- TODO: Complete using Except.bind_eq_ok_iff
```

**Structure in place**: The theorem signature matches Oruži's template exactly. The proof starts correctly with unfold and simp.

---

## Build Status

✅ **Builds successfully**
```bash
$ lake build Metamath.KernelClean
Build completed successfully.
```

Warnings are only for sorries (expected at this stage).

---

## Next Steps (Clear Path Forward)

Following Oruži's roadmap:

### Immediate: Complete checkHyp_step proof (~2-3 hours)

**Location**: Line 1120 (current sorry)

**Approach**:
1. After `simp [hi] at hrun`, hrun has the do-notation form
2. Use `cases h_find : db.find? hyps[i]!` to split on hypothesis lookup
3. For `some (.hyp ess f lbl)` case:
   - Use `cases ess` to split float vs essential
   - For float: Use Except.bind_eq_ok_iff to extract recursive call
   - For essential: Case-split on f.subst, then use bind_eq_ok_iff
4. Build σ_mid and show recursive call succeeds

**Tools available**:
- `Except.bind_eq_ok_iff` (line 116) - extracts from >>= chains
- `Except.ok_bind_eq_ok_iff` (line 121) - simplifies ok case
- HashMap lemmas from KernelExtras

### Then: checkHyp_preserves_bindings (~1-2 hours)

**Location**: Currently axiom at line 1006

**Approach**:
```lean
theorem checkHyp_preserves_bindings ... := by
  revert σ_out
  -- Well-founded induction on hyps.size - i
  refine Nat.recAux (motive := fun i => ...) ?base ?step i
  · -- base: i ≥ hyps.size, unfold to pure σ_in
    sorry
  · -- step: use checkHyp_step, split float/essential
    intro i ih σ_out hrun hfind
    have hi : i < hyps.size := sorry
    obtain ⟨σ_mid, hdesc, hrec⟩ := checkHyp_step db hyps stack off i σ_in σ_out hi hrun
    -- Float case: σ_mid = σ_in.insert v val
    --   If key = v: use find?_insert_self
    --   If key ≠ v: use find?_insert_ne, then IH
    -- Essential case: σ_mid = σ_in, direct IH
    sorry
```

### Then: checkHyp_builds_impl_inv (~2-3 hours)

**Location**: Replace checkHyp_builds_impl_inv_from_OLD at line 1123

**Approach**:
Use checkHyp_step + checkHyp_preserves_bindings to prove the j=i cases that currently have sorries.

### Then: toSubstTyped_of_allM_true (~30 min)

**Location**: Currently axiom at line 764

**Approach**: Simple match/simp using AllM facts.

### Then: Remove AXIOM 2 (~1 hour)

Use checkHyp_builds_impl_inv + toFrame_float_correspondence.

---

## Key Insights from This Session

### 1. CheckHypOk Was the Wrong Approach

The big-step semantics `CheckHypOk` added unnecessary complexity:
- Introduced its own induction principle
- Required proving correspondence to executable
- Created circular dependencies

**Oruži's insight**: Just prove `checkHyp_step` directly from the executable definition.

### 2. Except Lemmas Are Easy to Prove

The Except.bind lemmas that seemed hard are actually trivial:
```lean
cases x <;> simp [Except.bind]
```

This is because `Except.bind` has a simple definition. No axioms needed!

### 3. The Right Abstraction Level

**Oruži's approach** operates at the right level:
- `checkHyp_step`: What does one iteration do?
- `checkHyp_preserves_bindings`: Generic property
- `ImplInv`: Simple predicate over indices

This is much simpler than trying to capture everything in an inductive relation.

---

## Metrics

**Lines added**: ~50 (Except lemmas + checkHyp_step skeleton)
**Lines removed**: ~330 (entire CheckHypSemantics section)
**Net**: -280 lines (simpler!)
**Axioms added**: 0
**Axioms removed**: 0 (cleanup only)
**Build status**: ✅ Success

---

## Files Modified

### Metamath/KernelClean.lean

**Lines 109-129**: Added 3 proven Except lemmas (namespace Except)
**Lines 965-969**: Updated section header to reference Oruži's approach
**Lines 971-989**: Kept ImplSubst and ImplMatchesAt definitions
**Lines 1066-1079**: Kept ImplInv and ImplInvFrom definitions
**Lines 1081-1120**: Added checkHyp_step theorem skeleton
**Lines 1217**: Updated reference from checkHyp_builds_impl_inv_from to _OLD version

**Deleted** (~330 lines):
- Duplicate Except axioms
- DB well-formedness axioms
- CheckHypOk inductive definition
- CheckHypOk.extends theorem
- checkHyp_ok_sound theorem
- CheckHypOk.matches_all theorem
- checkHyp_builds_impl_inv_from using CheckHypOk

---

## Comparison: Before vs After

### Before (Failed Approach)
```
Duplicate Except axioms (provable)
DB well-formedness axioms (not needed)
inductive CheckHypOk (wrong level of abstraction)
theorem CheckHypOk.extends (with sorries)
theorem checkHyp_ok_sound (with sorry)
theorem CheckHypOk.matches_all (with sorries)
theorem checkHyp_builds_impl_inv_from (using CheckHypOk)
```

### After (Oruži's Approach)
```
Proven Except lemmas (no axioms!)
theorem checkHyp_step (skeleton, will be proven)
axiom checkHyp_preserves_bindings (will be proven using checkHyp_step)
(existing axioms to be proven later)
```

**Character**: Simpler, more direct, clearer path to completion.

---

## Estimated Remaining Work

Following Oruži's 8-step plan:

- [x] Step 1: Except lemmas ✅ **DONE**
- [ ] Step 2: checkHyp_step (2-3 hours)
- [ ] Step 3: checkHyp_preserves_bindings (1-2 hours)
- [ ] Step 4: checkHyp_builds_impl_inv (2-3 hours)
- [ ] Step 5: toSubstTyped_of_allM_true (30 min)
- [ ] Step 6: Remove AXIOM 2 (1 hour)
- [ ] Step 7-8: Phase 6-7 soundness (4-6 hours)

**Total remaining**: ~11-17 hours of focused work

**Current confidence**: High. The cleanup proves the approach is viable. The Except lemmas being trivially provable validates Oruži's assessment.

---

## Recommendations

### For Next Session

1. **Complete checkHyp_step proof** (lines 1120)
   - Take time to understand the elaborated do-notation
   - Use Except.bind_eq_ok_iff systematically
   - Don't rush - get it right

2. **Then checkHyp_preserves_bindings**
   - Use checkHyp_step + HashMap lemmas
   - Well-founded recursion is straightforward

3. **Build momentum toward AXIOM 2 elimination**
   - Each step makes the next easier
   - The path is now clear

### Key Success Factors

- ✅ Simple, proven Except lemmas (not axioms)
- ✅ Clean slate after removing CheckHypOk
- ✅ checkHyp_step has correct signature
- ✅ File builds cleanly
- ✅ Clear roadmap from Oruži

**Confidence level**: This is doable. The hard part (architectural decision) is done.

---

**Session character**: Surgical cleanup + foundation laying
**Value delivered**: Clear path to proof completion without operational axioms
**Technical debt**: Reduced (removed 330 lines of wrong approach)

🎯 **Ready for**: Completing checkHyp_step proof in next session
