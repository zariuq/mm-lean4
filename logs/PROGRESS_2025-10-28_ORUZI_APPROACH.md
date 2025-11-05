# Progress: Implementing Oruži's Approach
**Date**: October 28, 2025
**Goal**: Follow Oruži's concrete plan to prove checkHyp correctness without operational axioms

---

## Current Status

### ✅ Step 1 Complete: Except Lemmas (Lines 109-129)

Added 3 **proven** (not axiomatized) Except lemmas to make do-notation tractable:

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

**Status**: ✅ Build successful
**Lines**: 109-129 in KernelClean.lean

---

## ⚠️ Cleanup Needed

### Remove CheckHypSemantics Section (Lines 971-1299)

This section contains my earlier failed attempt using CheckHypOk big-step semantics. It includes:
- Axiomatized (duplicate) versions of the Except lemmas we just proved
- DB well-formedness axioms
- CheckHypOk inductive relation
- checkHyp_ok_sound with sorry

**Action**: Delete lines 971-1299 entirely. This removes:
- `axiom except_bind_eq_ok_iff` (duplicate - we have theorem at line 116)
- `axiom except_pure_eq_ok_iff` (duplicate - not needed)
- `axiom db_hyps_found` (not needed for Oruži's approach)
- `axiom db_hyps_are_hyps` (not needed)
- `inductive CheckHypOk` (wrong approach)
- `theorem checkHyp_ok_sound` with sorry (wrong approach)
- `end CheckHypSemantics`

---

## Next Steps (Oruži's Checklist)

### Step 2: Prove checkHyp_step

**Location**: After line 1215 (where `axiom checkHyp_preserves_bindings` currently is)

**Template** (from Oruži):
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
  -- Split on db.find? using the Except lemmas from lines 116-127
  -- With those lemmas, the proof is ~30 lines of case splits
  sorry -- TODO: Fill using Except.bind_eq_ok_iff
```

**Estimated effort**: 2-3 hours with the Except lemmas in place

### Step 3: Prove checkHyp_preserves_bindings

**Location**: Replace axiom at line 1209

**Uses**: checkHyp_step + HashMap lemmas (find?_insert_self, find?_insert_ne)

**Template**:
```lean
theorem checkHyp_preserves_bindings
  (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ_in σ_out : Std.HashMap String Verify.Formula)
  (key : String) (val : Verify.Formula) :
  Verify.DB.checkHyp db hyps stack off i σ_in = Except.ok σ_out →
  σ_in[key]? = some val →
  σ_out[key]? = some val := by
  revert σ_out
  -- Well-founded induction on hyps.size - i
  sorry -- TODO: Use checkHyp_step in IH, split float/essential cases
```

**Estimated effort**: 1-2 hours

### Step 4: Finish checkHyp_builds_impl_inv

**Location**: Lines 1305-1445 (currently has sorries)

**Uses**: checkHyp_step + checkHyp_preserves_bindings

For j=i case:
- Float: Use checkHyp_step to get σ_mid = σ_in.insert v val
  - Then use find?_insert_self + checkHyp_preserves_bindings
- Essential: Use checkHyp_step to get f.subst σ_in = ok expected

**Estimated effort**: 2-3 hours

### Step 5: Prove toSubstTyped_of_allM_true

**Location**: Replace axiom at line 764

**Uses**: AllM.allM_true_iff_forall (already proven)

**Template**:
```lean
theorem toSubstTyped_of_allM_true
    (fr : Spec.Frame) (σ_impl : Std.HashMap String Verify.Formula)
    (hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true) :
  ∃ σ_typed : Bridge.TypedSubst fr, toSubstTyped fr σ_impl = some σ_typed := by
  unfold toSubstTyped
  simp [hAll]  -- The match reduces directly
```

**Estimated effort**: 30 minutes

### Step 6: Remove AXIOM 2 (checkHyp_ensures_floats_typed)

**Location**: Line 806

**Action**: Delete axiom, re-prove checkHyp_validates_floats using:
- checkHyp_builds_impl_inv (gives ImplMatchesAt at each index)
- toFrame_float_correspondence (already proven)
- AllM.allM_true_iff_forall

**Estimated effort**: 1 hour

---

## Summary

**Completed**:
- ✅ 3 Except lemmas (proven, 20 lines)

**Cleanup needed**:
- ⚠️ Remove CheckHypSemantics section (delete lines 971-1299)

**Remaining work** (Oruži's sequence):
1. Prove checkHyp_step (~2-3 hours)
2. Prove checkHyp_preserves_bindings (~1-2 hours)
3. Finish checkHyp_builds_impl_inv (~2-3 hours)
4. Prove toSubstTyped_of_allM_true (~30 min)
5. Remove AXIOM 2 (~1 hour)

**Total estimated**: 7-10 hours of focused work

**Key insight**: We don't need CheckHypOk at all! The existing ImplInv/ImplMatchesAt structure + checkHyp_step is the right approach.

---

**Build Status**: ✅ Currently builds (with warnings for sorries)
**Next action**: Remove lines 971-1299, then implement checkHyp_step
