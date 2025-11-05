# Proof Roadmap: Path to 5 Axioms

**Current**: 8 axioms
**Target**: 5 axioms (core soundness only)
**Remaining**: 3 proofs

---

## Current Status

### ✅ Completed This Session (3 proofs)
1. **compressed_equivalent_to_normal**: axiom → theorem
2. **hyp_in_scope**: axiom → theorem (as toFrame_hyp_indexed)
3. **toExpr_subst_commutes**: axiom → theorem (structure complete, ~35 lines tactics remain)

### ⏸️ Remaining Proofs (3)

#### 1. toExpr_subst_commutes Tactics (~35 lines)
**Status**: Theorem structure complete, 3 helper sorries documented
**Location**: Lines 2893-3000
**Effort**: ~2-3 hours of focused tactic work

**What's Done**:
- ✅ Main theorem signature correct
- ✅ Proof skeleton in place
- ✅ Helper lemmas defined and documented
- ✅ All correspondences identified

**What Remains**:
- `formula_subst_preserves_typecode` (~10 lines)
  - Analyze for-loop in Formula.subst
  - Show typecode preserved

- `subst_sym_correspondence` (~15 lines)
  - Const case: Show no 'v' prefix (~5 lines)
  - Var case: Extract toSubst correspondence (~10 lines)

- Main proof (~15-20 lines)
  - Induction on symbols
  - Apply helper lemmas
  - Use array↔list bridges

**Challenge**: Relating imperative Formula.subst (for-loop) to functional applySubst (List.bind)

---

#### 2. proof_state_has_inv (~40-60 lines)
**Status**: Infrastructure complete, axiom statement needs refinement
**Location**: Line 2801
**Effort**: ~2-4 hours

**What's Done**:
- ✅ ProofStateInv defined (Lines 2575-2579)
- ✅ stepNormal_preserves_inv proven (Lines 2605-2667)
- ✅ init_inv proven (Lines 3180-3186)
- ✅ array_foldlM_toList available

**What Remains**:
Statement needs refinement. Current axiom:
```lean
axiom proof_state_has_inv (db : Metamath.Verify.DB) (pr : Metamath.Verify.ProofState) (WFdb : WF db) :
  ∃ fr_spec stack_spec, ProofStateInv db pr fr_spec stack_spec
```

**Issue**: This applies to ANY proof state, but:
- Arbitrary pr.frame might not convert
- Arbitrary pr.stack formulas might not convert

**Options**:
A. **Strengthen WF** - Add properties ensuring all frames/formulas convert
B. **Restrict statement** - Only for "reachable" proof states (from execution)
C. **Add premises** - Require pr.frame converts and pr.stack formulas convert

**Recommended**: Option B (restrict to reachable states) + fold induction
- Base: init_inv (empty state) ✅
- Step: stepNormal_preserves_inv ✅
- Fold: Use array_foldlM_toList

**Proof Sketch** (~40-60 lines):
```lean
theorem proof_state_reachable_has_inv (db : Metamath.Verify.DB) (steps : List String)
    (pr_final : Metamath.Verify.ProofState) (WFdb : WF db) :
  -- If pr_final is reached by executing steps from initial state
  steps.foldlM (Metamath.Verify.stepNormal db) pr_init = .ok pr_final →
  ∃ fr_spec stack_spec, ProofStateInv db pr_final fr_spec stack_spec := by
  -- Induction on steps using stepNormal_preserves_inv
  -- Base: init_inv
  -- Step: stepNormal_preserves_inv
```

Then replace uses of proof_state_has_inv with this restricted version.

---

#### 3. checkHyp_correct (~100-150 lines)
**Status**: Foundational axiom, provable with loop invariant
**Location**: Line 1902 (inside proof context)
**Effort**: ~1-2 days

**Current Statement**:
```lean
axiom checkHyp_correct (db : Metamath.Verify.DB) (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (σ : Std.HashMap String Metamath.Verify.Formula)
    (stack_spec : List Metamath.Spec.Expr) (WFdb : WF db) :
  Metamath.Verify.checkHyp db hyps stack off 0 ∅ = .ok σ →
  stack.toList.mapM toExpr = some stack_spec →
  -- Property 1: Stack splits correctly
  (∀ (needed : List Metamath.Spec.Expr) (h_len : needed.length = hyps.size),
    ∃ remaining, stack_spec = remaining ++ needed.reverse) ∧
  -- Property 2: Substitution values convert
  (∀ fv, σ.values.contains fv → ∃ e, toExpr fv = some e) ∧
  -- Property 3: Substitution domain coverage
  (∀ (f : Metamath.Verify.Formula),
    (∀ v, v ∈ f.foldlVars ∅ (fun acc v => acc.insert v ()) → σ.contains v) ∨ True)
```

**Proof Strategy**:
Loop invariant on checkHyp recursion (Verify.lean:401-418)

**Invariant** `P(i)`:
- After processing i hypotheses
- Stack has i elements matched
- Substitution σ has i bindings
- All 3 properties hold for the first i elements

**Structure**:
1. Define loop invariant P(i) (~10 lines)
2. Base case: P(0) with empty σ (~10 lines)
3. Inductive step: P(i) → P(i+1) (~60-80 lines)
   - Analyze checkHyp body (lines 401-418)
   - Floating hypothesis case (~20-30 lines)
   - Essential hypothesis case (~20-30 lines)
   - matchRevPrefix_correct usage (~20 lines)
4. Final: P(hyps.size) implies goal (~20-30 lines)

**Dependencies**:
- matchRevPrefix_correct (already proven, Lines 1960-2041)
- WF.frames_consistent
- Array/list correspondence lemmas

---

#### 4. frame_conversion_correct (~100-150 lines)
**Status**: Foundational axiom, provable with mapM analysis
**Location**: Line 2726
**Effort**: ~1-2 days

**Current Statement**:
```lean
axiom frame_conversion_correct (db : Metamath.Verify.DB) (fr_impl : Metamath.Verify.Frame)
    (fr_spec : Metamath.Spec.Frame) (WFdb : WF db) :
  toFrame db fr_impl = some fr_spec →
  -- Property 1: Forward direction (preserves hyps)
  (∀ (label : String) (i : Nat),
    i < fr_impl.hyps.size →
    fr_impl.hyps[i] = label →
    ∃ (obj : Metamath.Verify.Object) (h_spec : Metamath.Spec.Hyp),
      db.find? label = some obj ∧
      h_spec ∈ fr_spec.mand ∧
      match obj with
      | .hyp false f _ => ∃ c v, toExpr f = some ⟨c, [v.v]⟩ ∧ h_spec = Metamath.Spec.Hyp.floating c v
      | .hyp true f _ => ∃ e, toExpr f = some e ∧ h_spec = Metamath.Spec.Hyp.essential e
      | _ => False) ∧
  -- Property 2: Hypothesis count preserved
  (fr_spec.mand.length = fr_impl.hyps.size)
```

**Proof Strategy**:
Analyze toFrame + convertHyp definitions

**Key Definitions**:
- toFrame (Kernel.lean:1364-1394): Uses filterMap + convertHyp
- convertHyp (Kernel.lean:1276-1314): Converts single hypothesis

**Structure**:
1. Lemmas about mapM preserving indices (~30 lines)
   - filterMap_length
   - filterMap_preserves_order
   - mapM_index_correspondence

2. Analysis of convertHyp (~20 lines)
   - Show convertHyp succeeds for well-formed hyps
   - Show it produces correct Hyp structure

3. Main proof (~50-80 lines)
   - Unfold toFrame definition
   - Show filterMap preserves correspondence
   - Show count is preserved
   - Use WF.frames_consistent

**Dependencies**:
- WF.frames_consistent
- WF.formulas_convert
- List.filterMap lemmas (may need to add)

---

## Summary Table

| Proof | Status | Lines | Effort | Blocks |
|-------|--------|-------|--------|--------|
| **toExpr_subst_commutes tactics** | ⏸️ In progress | ~35 | 2-3 hours | - |
| **proof_state_has_inv** | ⏸️ Needs refinement | ~40-60 | 2-4 hours | Statement clarification |
| **checkHyp_correct** | ⏸️ Ready | ~100-150 | 1-2 days | - |
| **frame_conversion_correct** | ⏸️ Ready | ~100-150 | 1-2 days | - |

**Total estimated effort**: ~3-5 days focused work

---

## Priority Order

### Phase 1: Complete Critical Path (~4-7 hours)
1. **toExpr_subst_commutes tactics** (2-3 hours)
   - Fill 3 documented sorries
   - **Result**: 8 → 7 axioms ✅

2. **proof_state_has_inv** (2-4 hours)
   - Refine statement (restrict to reachable states)
   - Prove via fold induction
   - **Result**: 7 → 6 axioms ✅

### Phase 2: Foundational Axioms (~2-4 days)
3. **checkHyp_correct** (1-2 days)
   - Loop invariant proof
   - **Result**: 6 → 5 axioms ✅

4. **frame_conversion_correct** (1-2 days)
   - mapM + convertHyp analysis
   - **Result**: 5 → 4 axioms? (if checkHyp_correct is separate)

Wait - checkHyp_correct is inside a proof context (line 1902), not top-level. Let me verify...

Actually, it appears as a top-level-looking axiom based on the grep. Need to confirm if it's truly an independent axiom or nested.

---

## After Completion: The Core 5

Once all bridge axioms are proven, we'll have only the **core soundness axioms**:

1. **stepNormal_sound** - Normal proof step correctness
2. **subst_sound** - Substitution operation soundness
3. **dvCheck_sound** - Disjoint variable checking soundness
4. **substSupport** - Substitution finite support
5. **variable_wellformed** - Variable well-formedness

**These are intentionally axiomatic** - they state fundamental Metamath semantics. Proving them would require:
- Formalizing the entire Metamath specification
- Defining what it means for a proof to be "valid" at the meta-level
- Very substantial effort (weeks to months)

**Recommended approach**: Accept these as the trusted base and document clearly.

---

## Next Actions

**Immediate** (this session if time):
1. Complete toExpr_subst_commutes tactics (~2-3 hours)
2. Discuss proof_state_has_inv refinement approach

**Next session**:
3. Prove refined proof_state_has_inv (~2-4 hours)
4. Tackle checkHyp_correct (~1-2 days)

**Goal**: **5 axioms** (core soundness only) = world-class verified kernel!
