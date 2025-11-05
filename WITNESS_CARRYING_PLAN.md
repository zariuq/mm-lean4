# Witness-Carrying Implementation Plan

**Date:** 2025-10-14
**Approach:** Solution A (Proof-driven, no new axioms)
**Goal:** Complete witness-carrying `TypedSubst` architecture per Oruží/GPT-5 guidance

---

## Overview

Implement the witness-carrying substitution pattern where `TypedSubst` bundles the substitution with proof that it respects typing constraints. This eliminates downstream re-checking and shrinks the TCB with zero runtime cost (proofs erase).

## Success Criteria

- ✅ `allM_option_true_iff` proven as **theorem** (not axiom)
- ✅ `vars_apply_subset` compiles without dependent elimination errors
- ✅ `matchFloats_sound` proven with `Nodup` precondition
- ✅ `toSubstTyped` returns witness-carrying `TypedSubst`
- ✅ `verify_impl_sound` compiles without "sorry in fold" error
- ✅ Full project builds: `lake build` succeeds
- ✅ Zero active sorries in critical path
- ✅ Executable runs

---

## Phase 1: Core Infrastructure (KernelExtras)
**Duration:** 30-45 min
**Status:** READY TO START

Add the reusable `allM` extraction lemma as a **theorem**:

```lean
namespace List

/-- For Option monad: `allM p = some true` iff `p x = some true` for all x.
    This is the key extraction lemma for witness-based verification. -/
theorem allM_option_true_iff {α}
    (xs : List α) (p : α → Option Bool) :
    xs.allM p = some true ↔ (∀ x ∈ xs, p x = some true) := by
  induction xs with
  | nil => simp [allM]
  | cons x xs ih =>
    simp [allM, Option.bind, Bool.and_eq_true, ih]
    constructor
    · intro ⟨hx, hall⟩
      intro y hy
      cases hy
      · exact hx
      · exact hall y (by assumption)
    · intro hall
      constructor
      · exact hall x (List.mem_cons_self _ _)
      · intro y hy
        exact hall y (List.mem_cons_of_mem _ hy)

end List
```

**Deliverable:** KernelExtras.lean compiles with new theorem

---

## Phase 2: Fix `vars_apply_subset`
**Duration:** 20-30 min
**Status:** PENDING Phase 1

**Problem:** Line 420 has dependent elimination failure with `rcases`

**Solution:** Add `mem_flatMap` helper, use targeted unfolds, avoid `unfold ... at *`

```lean
-- Helper lemma
lemma mem_flatMap_iff {α β} (xs : List α) (f : α → List β) (b : β) :
  b ∈ xs.flatMap f ↔ ∃ a ∈ xs, b ∈ f a := by
  simpa [List.flatMap, List.bind, List.join, List.mem_bind, List.mem_join]

theorem vars_apply_subset ... := by
  intro v hv
  unfold Spec.varsInExpr at hv  -- Only where needed, NOT at *
  obtain ⟨s, hsIn, hvEq⟩ := List.mem_filterMap.mp hv
  unfold Spec.applySubst at hsIn  -- Targeted
  obtain ⟨s', hs'mem, hsInBranch⟩ := (mem_flatMap_iff e.syms _ s).mp hsIn
  by_cases hvar' : Spec.Variable.mk s' ∈ vars
  · right  -- variable branch
    refine ⟨⟨s'⟩, ?memInE, ?vIn⟩
    · unfold Spec.varsInExpr
      simp [List.filterMap, hs'mem, hvar']
    · unfold Spec.varsInExpr
      have : s ∈ (σ ⟨s'⟩).syms := by simpa [hvar'] using hsInBranch
      cases hvEq
      simp [List.filterMap, this]
  · left  -- constant branch
    have : s = s' := by simpa [hvar'] using hsInBranch
    subst this
    unfold Spec.varsInExpr
    simp [List.filterMap, hs'mem, hvar']
```

**Key insight:** Use `obtain` instead of `rcases`, apply `mem_flatMap_iff` explicitly

**Deliverable:** vars_apply_subset compiles without errors

---

## Phase 3: Complete `matchFloats_sound`
**Duration:** 30-45 min
**Status:** PENDING Phase 2

**Problem:** Line 1239 needs proof that tail variables are distinct

**Solution:** Add `Nodup` precondition, use `map_congr_left` pattern

```lean
theorem matchFloats_sound
    (floats : List (Spec.Constant × Spec.Variable))
    (stack : List Spec.Expr) (σ : Spec.Subst)
    (hNoDup : (floats.map Prod.snd).Nodup) :
  matchFloats floats stack = some σ →
  floats.map (fun (_, v) => σ v) = stack := by
  intro h
  induction floats generalizing stack σ with
  | nil => ...
  | cons ⟨tc, v⟩ fs ih =>
    cases stack with
    | nil => cases h
    | cons e es =>
      unfold matchFloats at h
      split at h
      · simp [List.map]
        constructor
        · simp [if_pos rfl]  -- head
        · -- tail: extract Nodup properties
          have hNoDupTail := (List.nodup_cons.mp hNoDup).2
          have hvNotIn := (List.nodup_cons.mp hNoDup).1
          -- Use map_congr_left to show pointwise equality
          have : ∀ p ∈ fs, (if p.snd = v then e else σ_rest p.snd) = σ_rest p.snd := by
            intro ⟨tc', v'⟩ hp
            by_cases heq : v' = v
            · exfalso
              rw [heq] at hp
              exact hvNotIn (List.mem_map_of_mem Prod.snd hp)
            · simp [heq]
          rw [List.map_congr_left this]
          exact ih es σ_rest hNoDupTail h
      · cases h
```

**Key insight:** Extract `v ∉ tail` from Nodup, use contradiction on impossible case

**Deliverable:** matchFloats_sound proven completely

---

## Phase 4: Implement `toSubstTyped` with Witness
**Duration:** 45-60 min
**Status:** PENDING Phase 1, 3

**Problem:** Need to construct `TypedSubst` with proof witness from `allM` success

**Solution:** Use Phase 1's `allM_option_true_iff` + `floats_complete`

```lean
def toSubstTyped (fr : Spec.Frame)
    (σ_impl : Std.HashMap String Verify.Formula) : Option (TypedSubst fr) := do
  let xs := floats fr
  let ok ← xs.allM (fun (c, v) => do
    let f ← σ_impl[v.v]?
    let e ← toExprOpt f
    pure (decide ((toExpr e).typecode = c)))

  if h : ok then
    let σ : Spec.Subst := fun v =>
      match σ_impl[v.v]? with
      | some f => toExpr f
      | none => ⟨⟨v.v⟩, [v.v]⟩

    have hOk : xs.allM ... = some true := by
      cases ok; simp [h] at *; simp [h]

    some ⟨σ, by
      intro c v hvFloat
      have hx := floats_complete fr c v hvFloat
      have hall := (List.allM_option_true_iff xs _).mp hOk
      have helem := hall (c, v) hx
      -- Unwrap do-block to extract: σ_impl[v.v]? = some f ∧ toExprOpt f = some e ∧ e.typecode = c
      simp [σ, Option.bind] at helem
      cases hσ : σ_impl[v.v]?
      · simp [hσ] at helem
      · simp [hσ] at helem
        cases he : toExprOpt f
        · simp [he] at helem
        · simp [he, decide_eq_true_eq] at helem
          exact helem
    ⟩
  else
    none
```

**Key insight:** Transform `ok : Bool` to `hOk : ok = true` to feed into allM theorem

**Deliverable:** toSubstTyped returns witness-carrying TypedSubst

---

## Phase 5: Stabilize `verify_impl_sound`
**Duration:** 15-30 min
**Status:** PENDING Phase 4

**Problem:** Line 3277 shows "sorry in fold" - initial state became sorry during rewrites

**Solution:** Protect initial state with `set`, avoid `simp [*]`

```lean
theorem verify_impl_sound ... := by
  intro ⟨pr_final, h_fold, h_size, h_top⟩

  -- Name and protect the initial state
  set pr0 : Verify.ProofState := ⟨#[], #[], db.frame⟩ with hpr0
  have h_init_size : pr0.stack.size = 0 := by simp [pr0]

  obtain ⟨Γ, h_Γ⟩ := WFdb.db_converts
  obtain ⟨fr, h_fr⟩ := WFdb.current_frame_converts

  -- Convert array fold to list fold (controlled rewrite)
  rw [array_foldlM_toList] at h_fold
  simp only [hpr0] at h_fold  -- Targeted simplification, NOT simp [*]

  have h_init_inv : ProofStateInv db pr0 fr [] := by
    constructor
    · unfold viewState
      unfold viewStack
      simp [pr0, h_fr]
    · simp [pr0]

  -- Apply fold lemma
  obtain ⟨frS', stkS', h_inv_final, h_prov⟩ :=
    fold_maintains_inv_and_provable db WFdb Γ h_Γ pr0 fr [] proof.toList pr_final
      h_init_inv h_fold

  -- Continue...
```

**Key insight:** Never `simp [*]` when `*` includes `set` equalities like `hpr0`

**Deliverable:** verify_impl_sound compiles without sorry errors

---

## Phase 6: Fix Line 3291 Parse Error
**Duration:** 10 min
**Status:** PENDING Phase 5

**Problem:** "unexpected token ','" at line 3291

**Current (likely):**
```lean
unfold viewState, viewStack  -- Comma syntax might fail
```

**Fix:**
```lean
unfold viewState
unfold viewStack
```

**Deliverable:** Parse error eliminated

---

## Phase 7: Integration Testing
**Duration:** 30-45 min
**Status:** PENDING All Above

**Build sequence:**
1. `lake build Metamath.KernelExtras`
2. `lake build Metamath.Bridge`
3. `lake build Metamath.Kernel`
4. `lake build` (full project)
5. Test executable (if test files available)

**Deliverable:** Green build, executable runs

---

## Risk Mitigation

- **Tactic failures:** Mark temporary `sorry` with `-- TODO: fix tactic` to keep moving
- **Type mismatches:** `allM` lemma signature may need minor tweaks for exact monad setup
- **Build dependencies:** May need iteration if Bridge depends on Kernel changes

---

## Why This Approach

1. **Theoretically sound:** Mario/Oruží-approved witness-carrying pattern
2. **No new axioms:** Proves all lemmas as theorems
3. **Composable:** `TypedSubst` reusable throughout kernel
4. **Runtime zero-cost:** Proofs in `Prop` erase at compile time
5. **Clear TCB:** Witnesses localize correctness obligations to constructors

---

## Estimated Total Time

**3.5 - 4.5 hours** focused implementation

---

## Current Status

- **Active sorries:** 0 in main path (per session history)
- **Compilation errors:** ~200 (mostly in early sections, not blocking main theorem)
- **Main theorem:** verify_impl_sound at line 3821 (90% complete, needs initial state fix)
- **File parses to:** Line 3277 (out of ~4000)

---

## Notes from Oruží

> "The witness‑carrying version is runtime zero‑cost (proofs erase) and eliminates recurring obligations by turning them into one‑time constructors. This is exactly the Mario‑approved architecture."

> "Prove the allM extraction once; it's the reusable pattern for every witness in checkHyp/toSubstTyped."

> "Avoid `unfold … at *` - unfold only on the goal or the specific hypothesis you need. This prevents the brittle flatMap/filterMap pattern matching failures."
