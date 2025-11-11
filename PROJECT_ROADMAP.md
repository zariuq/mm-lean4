# Metamath Verifier: Project Roadmap to Full Verification

**Last Updated:** 2025-11-09
**Status:** 12 axioms remaining, clear path to zero axioms
**Target:** Fully verified Metamath proof checker with zero axioms/sorries in trusted core

---

## Executive Summary

The Metamath verifier project has reached a critical milestone:
- ✅ **Architecture complete:** Clean spec/impl/proof separation
- ✅ **Infrastructure proven:** Array/List lemmas, mapM theorems
- ✅ **Recent wins:** `mapM_get_some` and `getElem!_idxOf` fully proven
- 🎯 **Path forward:** 40-50 hours to zero axioms in core kernel
- 🎯 **Full verification:** 70-90 hours with parser proofs

**Current State:**
- **12 axioms** (7 high-priority, 5 medium/low priority)
- **53 sorries** (23 critical, 30 in parser infrastructure)
- **Next target:** 3 substitution loop axioms (highest impact)

---

## Table of Contents

1. [The Critical Path: 5-Step Plan](#critical-path)
2. [Detailed Work Breakdown](#work-breakdown)
3. [Dependency Graph](#dependencies)
4. [Proof Strategies](#strategies)
5. [Success Metrics & Milestones](#milestones)
6. [Risk Assessment](#risks)
7. [Long-Term Vision](#vision)

---

## <a name="critical-path"></a>The Critical Path: 5-Step Plan to Zero Axioms

### Step 1: Substitution Loop Axioms (HIGHEST PRIORITY) 🔥

**Target Axioms (3):**
- `Verify.Formula.subst_eq_foldlM` (KernelClean.lean:306)
- `Verify.Formula.subst_ok_flatMap_tail` (KernelClean.lean:331)
- `Verify.Formula.subst_preserves_head` (KernelClean.lean:358)

**What They Do:**
These axioms describe the operational behavior of Formula.subst, which substitutes variables in formulas by iterating over the symbol list. They bridge the implementation (for-in loop) to the specification (list operations).

**Why They Block Progress:**
- Required for `applySubst_correspondence` (Phase 6)
- Blocks all step soundness proofs (float/essential/assert steps)
- Without these, cannot prove substitution correctness

**Proof Strategy:**

1. **Prove `subst_eq_foldlM`:**
   ```lean
   -- Current axiom:
   axiom subst_eq_foldlM :
     Formula.subst σ f = f.toList.foldlM (subst_step σ) #[]

   -- Proof approach:
   -- 1. Unfold Formula.subst definition (for-in loop)
   -- 2. Research Lean 4's for-in desugaring for Array
   -- 3. Show for-in desugars to foldlM with same step function
   -- 4. Use definitional equality
   ```

2. **Prove `subst_ok_flatMap_tail`:**
   ```lean
   -- Current axiom:
   axiom subst_ok_flatMap_tail :
     ∀ c rest σ out,
       Formula.subst σ #[.const c] ++ rest = out →
       out[1:].toList = (rest.toList.flatMap (λ s => ...))

   -- Proof approach:
   -- 1. Use subst_eq_foldlM to express subst as foldlM
   -- 2. Separate first step (c) from rest
   -- 3. Show foldlM on tail equals flatMap (list induction)
   -- 4. Use existing head_push_stable lemma
   ```

3. **Prove `subst_preserves_head`:**
   ```lean
   -- Current axiom:
   axiom subst_preserves_head :
     ∀ c rest σ out,
       Formula.subst σ (#[.const c] ++ rest) = out →
       out[0]! = .const c

   -- Proof approach:
   -- 1. Use subst_eq_foldlM
   -- 2. Analyze first foldlM step: #[] → #[.const c]
   -- 3. Show subsequent steps only append to tail
   -- 4. Use head_append_many_stable lemma (already proven)
   ```

**Resources Needed:**
- Lean 4 documentation on for-in desugaring
- Example: How `for x in xs` with `ExceptT` desugars
- Consult Lean Zulip: "for-in desugaring with ExceptT and arrays"

**Estimated Effort:** 8-12 hours
- Research for-in desugaring: 2-3 hours
- Prove subst_eq_foldlM: 2-3 hours
- Prove tail/head lemmas: 4-6 hours

**Success Criteria:**
- All 3 axioms replaced with theorems
- Phase 6 step soundness proofs unblocked
- Build succeeds with no new errors

**Files to Modify:**
- `Metamath/Verify.lean`: Add helper lemmas about subst behavior
- `Metamath/KernelClean.lean`: Replace axioms with proofs

---

### Step 2: checkHyp Operational Semantics (HIGH PRIORITY) 🔥

**Target Axiom (1):**
- `checkHyp_operational_semantics` (KernelClean.lean:1336)

**What It Does:**
Proves that when `checkHyp` succeeds, it produces a substitution σ with the `FloatsProcessed` property (all float hypotheses correctly typed and present in σ).

**Why It Blocks Progress:**
- Core to Phase 5 (checkHyp soundness)
- Required for `checkHyp_ensures_floats_typed`
- Blocks Phase 6 (step soundness) which depends on Phase 5

**Current Statement:**
```lean
axiom checkHyp_operational_semantics :
  ∀ db dv σ_impl hyps i σ_typed,
    checkHyp db dv σ_impl hyps i = .ok σ_typed →
    FloatsProcessed db.frames.back! σ_typed hyps[0:i]
```

**Proof Strategy:**

Strong induction on `i` (the number of hypotheses processed):

1. **Base case (i = 0):**
   ```lean
   -- When i=0, hyps[0:0] = [], σ_typed = σ_impl (unchanged)
   -- FloatsProcessed ∅ [] holds trivially
   -- No floats to process, condition vacuous
   ```

2. **Inductive step (i → i+1):**
   ```lean
   -- Assume: FloatsProcessed σ hyps[0:i]
   -- Show: FloatsProcessed σ' hyps[0:i+1]

   -- Case 1: hyps[i] is essential hypothesis (ess = true)
   --   checkHyp leaves σ unchanged: σ' = σ
   --   hyps[i+1] contains same floats as hyps[i]
   --   FloatsProcessed preserved (no new floats)

   -- Case 2: hyps[i] is float hypothesis (ess = false)
   --   checkHyp extends σ with new binding
   --   Use Theorem D (FloatsProcessed extends by one float)
   --   Show new binding matches hyps[i] float structure
   ```

3. **Key lemmas to use:**
   - `checkHyp_float_step`: When processing float hyp, σ gets extended
   - `checkHyp_essential_step`: When processing essential hyp, σ unchanged
   - Theorem D (already proven): FloatsProcessed can be extended one float at a time
   - `toFrame_float_correspondence`: Connects spec floats to impl floats

**Resources Needed:**
- Existing Phase 5 infrastructure (FloatsProcessed definition, Theorems A-D)
- `checkHyp` implementation in Verify.lean (lines ~540-600)
- Understanding of recursion pattern in checkHyp

**Estimated Effort:** 12-16 hours
- Understand checkHyp recursion: 3-4 hours
- Prove base case: 1-2 hours
- Prove inductive step: 6-8 hours
- Handle edge cases: 2-3 hours

**Success Criteria:**
- Axiom replaced with proven theorem
- Phase 5 complete
- `checkHyp_ensures_floats_typed` proof closes without axiom

**Files to Modify:**
- `Metamath/KernelClean.lean`: Replace axiom, add induction proof
- May need helper lemmas about checkHyp steps

---

### Step 3: toFrame Float Correspondence (MEDIUM PRIORITY) 🟡

**Target Axiom (1):**
- `toFrame_float_correspondence` (KernelClean.lean:554)

**What It Does:**
Establishes bijection between specification-level float hypotheses and implementation-level float list.

**Why It's Needed:**
- Required for checkHyp soundness
- Connects abstract spec to concrete impl
- Enables reasoning about float hypothesis coverage

**Current Statement:**
```lean
axiom toFrame_float_correspondence :
  ∀ frame : Impl.Frame, v : Impl.VarName,
    (∃ c, ⟨c, v⟩ ∈ frame.toFrame.floats) ↔
    (∃ fh : FloatHyp, fh ∈ frame.floats ∧ fh.var = v)
```

**Proof Strategy:**

1. **Forward direction (spec → impl):**
   ```lean
   -- Assume: ⟨c, v⟩ ∈ frame.toFrame.floats
   -- toFrame.floats defined as: frame.floats.filterMap toExprOpt
   -- Use List.mem_filterMap:
   --   ∃ fh ∈ frame.floats, toExprOpt fh = some ⟨c, v⟩
   -- Need: toExprOpt injectivity to extract fh.var = v
   ```

2. **Backward direction (impl → spec):**
   ```lean
   -- Assume: ∃ fh ∈ frame.floats, fh.var = v
   -- Show: toExprOpt fh = some ⟨c, v⟩ for some c
   -- Use: frame.floats structure (validated by parser)
   -- Each fh has form [.const c, .var v]
   -- toExprOpt maps this to some ⟨c, v⟩
   ```

3. **Key lemma needed:**
   ```lean
   theorem toExprOpt_injective_on_var :
     ∀ fh1 fh2,
       toExprOpt fh1 = some ⟨c1, v⟩ →
       toExprOpt fh2 = some ⟨c2, v⟩ →
       fh1.var = fh2.var

   -- Proof: Analyze toExprOpt definition
   -- It extracts variable from fh[1] position
   ```

**Resources Needed:**
- `toExprOpt` definition (Verify.lean)
- `List.filterMap` lemmas from Batteries
- Parser invariants about float structure

**Estimated Effort:** 6-8 hours
- Prove toExprOpt properties: 3-4 hours
- Prove bijection: 3-4 hours

**Success Criteria:**
- Axiom replaced with theorem
- checkHyp soundness proofs can use bijection
- No new parser axioms introduced

**Files to Modify:**
- `Metamath/KernelClean.lean`: Add toExprOpt lemmas, prove bijection

---

### Step 4: toSubstTyped Witness (MEDIUM PRIORITY) 🟡

**Target Axiom (1):**
- `toSubstTyped_of_allM_true` (KernelClean.lean:809)

**What It Does:**
When `allM` validation succeeds, proves that `toSubstTyped` produces a properly typed substitution.

**Why It's Axiomatized:**
Let-binding vs direct definition causes definitional equality issue. The function defined in the match branch doesn't syntactically match the external definition.

**Current Situation:**
```lean
-- External definition
def σ_fn : VarName → Option Expr := ...

-- In match branch
match allM validate σ_impl with
| some true =>
    -- Want to use: toSubstTyped σ_fn
    -- But have: toSubstTyped (fun v => ...)
    -- These aren't definitionally equal!
```

**Proof Strategy:**

1. **Refactor approach:**
   ```lean
   -- Extract σ_fn definition outside the match
   let σ_fn : VarName → Option Expr := fun v =>
     match σ_impl.find? v with
     | some expr => some expr
     | none => none

   -- Now match uses the same σ_fn
   match allM validate σ_impl with
   | some true => toSubstTyped σ_fn  -- Now definitionally equal!
   | _ => ...
   ```

2. **Proof technique if refactoring not sufficient:**
   ```lean
   -- Use function extensionality
   theorem toSubstTyped_of_allM_true :
     allM validate σ_impl = some true →
     toSubstTyped (fun v => σ_impl.find? v) = toSubstTyped σ_fn := by
     intro h
     congr 1  -- Reduce to function equality
     funext v  -- Function extensionality
     rfl  -- Definitions equal at each point
   ```

**Resources Needed:**
- Understanding of Lean 4's definitional equality
- `funext` tactic for function extensionality
- May need to consult Lean Zulip about match-expr equality

**Estimated Effort:** 4-6 hours
- Try refactoring approach: 2-3 hours
- Prove with funext if needed: 2-3 hours

**Success Criteria:**
- Axiom replaced with theorem or eliminated by refactoring
- No change in external behavior
- checkHyp_produces_TypedSubst continues to work

**Files to Modify:**
- `Metamath/KernelClean.lean`: Refactor or add funext proof

---

### Step 5: Spec-Level Proof Combinators (LOWER PRIORITY) 🟢

**Target Axioms (2):**
- `ProofValidSeq.toProvable` (Spec.lean:236)
- `ProofValid.toSeq_from_nil` (Spec.lean:252)

**What They Do:**
These axioms convert between different representations of valid proofs:
- `toProvable`: Proof sequence → Provable statement
- `toSeq_from_nil`: Single proof step → Proof sequence

**Why Lower Priority:**
- Not on critical path for main soundness
- Part of specification infrastructure, not kernel
- Can be proven later without blocking other work

**Proof Strategy for toProvable:**

```lean
axiom ProofValidSeq.toProvable :
  ∀ (pf : ProofValidSeq Γ hyps [] [thm]),
    Provable Γ thm

-- Proof by structural induction:
theorem ProofValidSeq.toProvable :
  ∀ (pf : ProofValidSeq Γ hyps [] [thm]),
    Provable Γ thm := by
  intro pf
  induction pf with
  | base =>
      -- Base case: Empty sequence
      -- Contradiction: cannot have [thm] from []
  | cons step pf_rest ih =>
      -- Inductive case: step extends pf_rest
      -- By IH: Provable Γ (result of pf_rest)
      -- step is ProofValid: applies valid rule
      -- Compose: Provable preserved by valid rules
      apply ProofValid.preserves_provable step ih
```

**Proof Strategy for toSeq_from_nil:**

```lean
axiom ProofValid.toSeq_from_nil :
  ∀ (step : ProofValid Γ hyps st [res]),
    ProofValidSeq Γ hyps [] [res]

-- Proof: Construct sequence with single step
theorem ProofValid.toSeq_from_nil :
  ∀ (step : ProofValid Γ hyps st [res]),
    ProofValidSeq Γ hyps [] [res] := by
  intro step
  -- Use ProofValidSeq.cons to build sequence
  apply ProofValidSeq.cons step
  -- Base: need ProofValidSeq from [] to st
  exact ProofValidSeq.base_from_state st
```

**Resources Needed:**
- Understanding of ProofValidSeq inductive structure
- Provable definition and composition properties
- May need helper lemmas about proof composition

**Estimated Effort:** 6-8 hours
- Understand proof sequence structure: 2-3 hours
- Prove toProvable: 2-3 hours
- Prove toSeq_from_nil: 2 hours

**Success Criteria:**
- Both axioms replaced with theorems
- fold_maintains_provable proof closes
- No impact on kernel verification

**Files to Modify:**
- `Metamath/Spec.lean`: Replace axioms with proofs

---

## <a name="work-breakdown"></a>Detailed Work Breakdown

### By Priority Level

#### 🔥 Critical (Blocks Core Verification)

| Item | Type | Effort | Dependencies | Unblocks |
|------|------|--------|--------------|----------|
| 3 Substitution axioms | Axioms → Theorems | 8-12h | for-in docs | Phase 6 |
| checkHyp operational | Axiom → Theorem | 12-16h | Phase 5 infra | Phase 5 closure |
| toFrame correspondence | Axiom → Theorem | 6-8h | toExprOpt lemmas | checkHyp soundness |

**Total Critical Path:** 26-36 hours

#### 🟡 Medium (Improves Completeness)

| Item | Type | Effort | Dependencies | Unblocks |
|------|------|--------|--------------|----------|
| toSubstTyped witness | Axiom → Theorem | 4-6h | funext | Clean Phase 5 |
| Spec combinators (2) | Axioms → Theorems | 6-8h | Structural induction | fold soundness |
| KernelClean sorries (8) | Sorries → Proofs | 10-15h | Phase 5/6 | Step soundness |

**Total Medium Priority:** 20-29 hours

#### 🟢 Lower (Can Defer)

| Item | Type | Effort | Dependencies | Unblocks |
|------|------|--------|--------------|----------|
| Parser invariants (3) | Axioms → Theorems | 20-30h | ParserProofs | Eliminates assumptions |
| ParserProofs sorries (30) | Sorries → Proofs | 30-40h | Parser analysis | Parser correctness |
| Compressed proof | Axiom → Theorem | 8-12h | Phase 7 | Production readiness |

**Total Lower Priority:** 58-82 hours

### Cumulative Effort Estimates

- **Core kernel verification:** 46-65 hours (Critical + Medium)
- **With parser correctness:** 104-147 hours (All items)
- **Minimal viable (Critical only):** 26-36 hours

---

## <a name="dependencies"></a>Dependency Graph

### Visual Representation

```
┌─────────────────────────────────────────────────────────┐
│                    MAIN SOUNDNESS                        │
│              verifier_sound : VerifyResult               │
└──────────────────────┬──────────────────────────────────┘
                       │
                       │ depends on
                       ▼
         ┌─────────────────────────────┐
         │      Phase 7: Fold Sound     │
         │  Uses: array_foldlM_preserves│
         │  Uses: ProofValidSeq.toProvable│
         └──────────────┬───────────────┘
                        │
                        │ depends on
                        ▼
         ┌─────────────────────────────┐
         │   Phase 6: Step Soundness    │
         │ BLOCKED BY 3 AXIOMS:         │
         │  • subst_eq_foldlM          │🔥
         │  • subst_ok_flatMap_tail    │🔥
         │  • subst_preserves_head     │🔥
         └──────────────┬───────────────┘
                        │
                        │ depends on
                        ▼
         ┌─────────────────────────────┐
         │  Phase 5: checkHyp Sound     │
         │ BLOCKED BY 2 AXIOMS:         │
         │  • checkHyp_operational_sem │🔥
         │  • toFrame_float_corresp    │🔥
         └──────────────┬───────────────┘
                        │
                        │ uses
                        ▼
         ┌─────────────────────────────┐
         │ Phase 4: Array/List Infra    │
         │  ✅ mapM_get_some            │
         │  ✅ getElem!_idxOf           │
         │  ✅ head_stable lemmas       │
         └─────────────────────────────┘

PARALLEL TRACK (not blocking):

┌─────────────────────────────────┐
│   Parser Correctness Proofs      │
│ • 30 sorries in ParserProofs     │🟢
│ • 3 axioms in ParserInvariants   │🟢
│   Proves: float structure valid  │
└─────────────────────────────────┘
```

### Critical Path Analysis

**Shortest path to main soundness theorem:**
1. Prove 3 substitution axioms → Unblocks Phase 6
2. Prove checkHyp operational → Completes Phase 5
3. Prove toFrame correspondence → Enables checkHyp soundness
4. Complete Phase 6 sorries (8) → Step soundness proven
5. Prove spec combinators (2) → Phase 7 closes
6. Main soundness theorem proven! ✅

**Estimated time:** 26-36 hours (critical) + 20-29 hours (medium sorries) = **46-65 hours**

---

## <a name="strategies"></a>Detailed Proof Strategies

### Strategy 1: for-in Loop Desugaring

**Challenge:** Lean 4's `for x in xs` syntax desugars to complex ForIn typeclass instances. Need to show equivalence to `foldlM`.

**Approach:**

1. **Research phase:**
   - Read Lean 4 source: `Init/Control/ForIn.lean`
   - Find examples with `ExceptT` monad
   - Ask on Lean Zulip: "for-in desugaring with Array and ExceptT"

2. **Proof technique:**
   ```lean
   -- Formula.subst is defined as:
   def Formula.subst (σ : Subst) (f : Formula) : Except Error Formula := do
     let mut out := #[]
     for s in f do
       match s with
       | .const c => out := out.push (.const c)
       | .var v =>
           match σ.find? v with
           | some e => out := out ++ e
           | none => throw error
     return out

   -- Show this equals:
   -- f.toList.foldlM (step σ) #[]

   -- Proof steps:
   -- 1. Unfold for-in to ForIn.forIn
   -- 2. Show ForIn instance for Array/ExceptT desugars to foldlM
   -- 3. Match step functions
   ```

3. **Key insight:**
   The `for x in xs` with mutable `out` is syntactic sugar for:
   ```lean
   ForIn.forIn xs #[] (fun s acc =>
     match s with
     | .const c => .yield (acc.push (.const c))
     | .var v => ...)
   ```
   which for `ExceptT` should desugar to `foldlM`.

### Strategy 2: Strong Induction on Recursion

**Challenge:** checkHyp is tail-recursive with index `i` ranging over hypotheses. Need to prove property holds after processing `i` hypotheses.

**Pattern:**

```lean
theorem by_strong_induction (P : Nat → Prop)
    (base : P 0)
    (step : ∀ k, P k → P (k+1)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ k ih => exact step k ih
```

**Application to checkHyp:**

```lean
theorem checkHyp_operational_semantics :
    ∀ i, checkHyp ... i = .ok σ → FloatsProcessed σ hyps[0:i] := by
  intro i
  induction i with
  | zero =>
      -- Base: i=0, hyps[0:0] = []
      -- FloatsProcessed σ [] holds vacuously
      simp [FloatsProcessed]
  | succ k ih =>
      -- Inductive: assume P(k), prove P(k+1)
      intro h_ok
      -- Case split on hyps[k]
      cases h_k : hyps[k].essential with
      | true =>
          -- Essential hyp: σ unchanged
          -- FloatsProcessed preserved
          exact FloatsProcessed.of_essential ih h_k
      | false =>
          -- Float hyp: σ extended
          -- Use Theorem D to extend property
          exact FloatsProcessed.extend ih h_k (checkHyp_float_extends h_ok)
```

### Strategy 3: Structural Induction on Inductive Types

**Challenge:** ProofValidSeq is inductively defined. Need to prove properties by structural induction.

**Pattern:**

```lean
inductive ProofValidSeq : Context → Hyps → Stack → Stack → Type where
  | base : ProofValidSeq Γ hyps st st
  | cons : ProofValid Γ hyps st [res] →
           ProofValidSeq Γ hyps [res] final →
           ProofValidSeq Γ hyps st final
```

**Proof technique:**

```lean
theorem property_of_seq (pf : ProofValidSeq Γ hyps [] [thm]) : ... := by
  induction pf with
  | base =>
      -- Base case: st=st, but we have []=[thm]
      -- Contradiction in this case
  | cons step pf_rest ih =>
      -- step : ProofValid Γ hyps st [res]
      -- pf_rest : ProofValidSeq Γ hyps [res] [thm]
      -- ih : property_of_seq pf_rest
      -- Show: property holds for cons step pf_rest
      -- Use: composition of step + ih
```

---

## <a name="milestones"></a>Success Metrics & Milestones

### Milestone 1: Substitution Axioms Eliminated (2 weeks)

**Target Date:** 2025-11-23

**Deliverables:**
- ✅ `subst_eq_foldlM` proven
- ✅ `subst_ok_flatMap_tail` proven
- ✅ `subst_preserves_head` proven
- ✅ Phase 6 step soundness proofs unblocked
- ✅ Build succeeds with 9 axioms (down from 12)

**Success Criteria:**
- All 3 axioms replaced with `theorem` declarations
- No new axioms introduced
- Existing proofs continue to work
- Documentation updated in how-to-lean.md

**Validation:**
```bash
# Check axiom count
rg "^axiom " Metamath/*.lean | wc -l  # Should be 9

# Verify build
lake build
```

---

### Milestone 2: Phase 5 Complete (4 weeks)

**Target Date:** 2025-12-07

**Deliverables:**
- ✅ `checkHyp_operational_semantics` proven
- ✅ `toFrame_float_correspondence` proven
- ✅ `checkHyp_ensures_floats_typed` proof closes
- ✅ Phase 5 infrastructure complete
- ✅ Build succeeds with 7 axioms

**Success Criteria:**
- checkHyp soundness fully proven
- No remaining Phase 5 sorries
- Ready to tackle Phase 6 step soundness

**Validation:**
```bash
# Verify Phase 5 complete
rg "sorry" Metamath/KernelClean.lean | grep -i "phase 5"  # Should be empty
```

---

### Milestone 3: Core Kernel Zero Axioms (6 weeks)

**Target Date:** 2025-12-21

**Deliverables:**
- ✅ All high-priority axioms eliminated
- ✅ `toSubstTyped_of_allM_true` proven
- ✅ Spec combinators proven
- ✅ Phase 6 step soundness complete
- ✅ Build succeeds with 3 axioms (parser only)

**Success Criteria:**
- Kernel soundness proof relies on zero axioms
- Only parser invariant axioms remain (can be assumed)
- Main soundness theorem pathway clear

**Validation:**
```bash
# Check kernel has zero axioms
rg "^axiom " Metamath/KernelClean.lean  # Should be empty
rg "^axiom " Metamath/Spec.lean  # Should be empty
```

---

### Milestone 4: Full Verification (8-12 weeks)

**Target Date:** 2026-01-18 to 2026-02-15

**Deliverables:**
- ✅ Parser invariant axioms proven
- ✅ All 30 ParserProofs sorries completed
- ✅ Compressed proof support (optional)
- ✅ Documentation complete
- ✅ Build succeeds with ZERO axioms, ZERO sorries

**Success Criteria:**
- Complete formal verification
- No axioms anywhere in codebase
- No sorries in trusted core
- Ready for publication

**Validation:**
```bash
# Ultimate check: zero axioms, zero sorries in core
rg "^axiom " Metamath/*.lean  # Should be empty
rg "sorry" Metamath/{Spec,Verify,KernelClean,ArrayListExt}.lean  # Empty
```

---

## <a name="risks"></a>Risk Assessment

### High-Risk Items

#### Risk 1: for-in Desugaring Complexity

**Issue:** Lean 4's for-in desugaring with ExceptT and mutable variables may be complex.

**Mitigation:**
- Research early (first task in Step 1)
- Consult Lean Zulip community
- May need to refactor Formula.subst to use explicit foldlM

**Fallback Plan:**
- Rewrite Formula.subst using foldlM directly
- Update all call sites (low risk, mechanical change)
- This eliminates need to prove desugaring equivalence

**Probability:** Medium (30%)
**Impact:** Low (adds 4-6 hours if needed)

---

#### Risk 2: checkHyp Induction Complexity

**Issue:** Strong induction on checkHyp may have subtle edge cases or dependent type issues.

**Mitigation:**
- Phase 5 infrastructure already exists (FloatsProcessed, Theorem D)
- Break into smaller lemmas (per-step properties)
- Use how-to-lean.md patterns for dependent types

**Fallback Plan:**
- If full induction too complex, prove restricted version
- Add well-formedness preconditions
- Document assumptions clearly

**Probability:** Medium (40%)
**Impact:** Medium (adds 8-12 hours)

---

### Medium-Risk Items

#### Risk 3: Parser Proof Volume

**Issue:** 30 sorries in ParserProofs.lean is a lot of work.

**Mitigation:**
- These are NOT on critical path for core soundness
- Can use parser invariant axioms initially
- Defer to Milestone 4 (long-term goal)

**Status:** Not a blocker, lower priority

---

#### Risk 4: HashMap Lemma Dependencies

**Issue:** 2 sorries in KernelExtras.lean blocked on Batteries library.

**Mitigation:**
- These are standard HashMap properties
- Can be assumed as axioms (well-understood properties)
- When Batteries adds HashMap theory, can be proven

**Status:** Acceptable to leave as axioms temporarily

---

### Risk Monitoring

**Weekly Check-ins:**
- Count axioms remaining
- Track sorries in critical path
- Document blockers in progress log

**Monthly Reviews:**
- Assess milestone progress
- Adjust timeline if needed
- Update roadmap with lessons learned

---

## <a name="vision"></a>Long-Term Vision

### Phase A: Core Verification (Months 1-2)
**Goal:** Zero axioms in kernel (KernelClean.lean, Spec.lean)

- Complete Steps 1-4 of critical path
- Prove main soundness theorem
- Document verification approach
- Publish technical report

**Deliverable:** "Formally Verified Metamath Proof Checker (Core)"

---

### Phase B: Full Verification (Months 3-4)
**Goal:** Zero axioms project-wide (including parser)

- Complete parser correctness proofs
- Prove all parser invariants
- Add compressed proof support
- Comprehensive test suite

**Deliverable:** "Fully Verified Metamath Proof Checker"

---

### Phase C: Publication & Adoption (Months 5-6)
**Goal:** Disseminate results, enable adoption

- **Academic paper:**
  - Journal of Formalized Reasoning
  - "A Fully Verified Metamath Proof Checker in Lean 4"
  - Emphasis on architecture and proof techniques

- **Engineering artifact:**
  - Extract verified checker to executable
  - Performance benchmarks on set.mm
  - Integration with existing Metamath ecosystem

- **Educational materials:**
  - Tutorial: "How to Verify a Proof Checker"
  - Case study: Verification architecture patterns
  - Expand how-to-lean.md into comprehensive guide

**Deliverable:** Published paper + production-ready tool

---

### Phase D: Extensions (Months 7+)
**Goal:** Leverage verified foundation for advanced features

**Possible extensions:**
1. **Proof transformation verified:**
   - Proof compression/decompression
   - Proof minimization
   - Proof repair

2. **Database optimization verified:**
   - Verified indexing structures
   - Verified proof search
   - Verified proof caching

3. **Interactive tools:**
   - Verified proof assistant frontend
   - Verified proof visualization
   - Verified proof explanation

4. **Cross-system verification:**
   - Metamath → Lean translation verified
   - Metamath → Coq translation verified
   - Metamath → Isabelle translation verified

---

## Conclusion

The Metamath verifier project is **remarkably well-positioned** for success:

✅ **Strong foundation:**
- Clean architecture with clear phase structure
- Proven infrastructure (Array/List lemmas, mapM theorems)
- Recent momentum (getElem!_idxOf, mapM_get_some completed)

✅ **Clear path forward:**
- Only 12 axioms remaining (most provable)
- Well-defined proof strategies for each axiom
- Critical path: 26-36 hours to unblock main soundness

✅ **Manageable scope:**
- Core verification: 46-65 hours (1-2 months part-time)
- Full verification: 104-147 hours (3-4 months part-time)
- Milestones defined with clear success criteria

✅ **Strong technical approach:**
- Witness-carrying code eliminates partial functions
- Simulation relation connects impl↔spec cleanly
- Phase structure makes proof organization clear

**Next Actions:**

1. **This week:** Begin Step 1 (substitution axioms)
2. **Next 2 weeks:** Complete Step 1, start Step 2
3. **Next month:** Complete Steps 1-2 (Phase 5/6 unblocked)
4. **Next 2 months:** Achieve core verification (zero kernel axioms)

**The project is on track to achieve full formal verification in Q1 2026.**

---

*Roadmap prepared 2025-11-09*
*For questions or updates, see VERIFICATION_STATUS_2025-11-09.md*
*For technical techniques, see how-to-lean.md*

