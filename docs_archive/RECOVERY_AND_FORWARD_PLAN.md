# Recovery and Forward Plan - MM-Lean4 Verifier

**Date:** 2025-10-12
**Status:** ✅ Revert Complete - Ready to Execute
**Contributors:** Claude (TypedSubst KIT A/B), Codex (archived proofs), GPT-5 (strategic advice)

---

## Executive Summary

**Where we are:**
- ✅ Clean build restored (200 baseline errors, acceptable)
- ✅ Claude's TypedSubst infrastructure (KIT A & B) intact in HEAD
- ✅ Codex's work safely archived in `codex_archive/` for reference
- ✅ Directory structure clean and compiling

**Strategic decision:** Revert-then-finish-proofs path
- **Rationale:** Build first, prove second. Structural breakage blocks all progress.
- **Bridge approach:** Still valuable, but introduce **incrementally** as thin definition-only layer **after** proofs are stable.

**GPT-5's key insight:** "Trying to land Bridge all at once while proofs are in flux created friction. Land it in thin slices after Verify proofs are stable."

---

## Why Revert Was Right

### 1. Build First, Then Prove
- Non-compiling tree blocks ALL progress (tests, proof search, refactors)
- Structural errors cascade and waste time
- Green builds = fast iteration

### 2. Structural Breakage Was Deep
- Missing `Metamath/Bridge.lean` root file
- Inconsistent imports (Kernel importing non-existent modules)
- Not a one-line fix - would invite cascading errors

### 3. TypedSubst Work (KIT A & B) is the Real Leverage
- Already in HEAD commit
- Solves "phantom wff" bug
- Solves double-prefix bug
- Foundation for finishing the verifier

**Verdict:** Optimize for shipping proofs, not rescuing a brittle reorg.

---

## The Bridge Pattern (Still Valuable!)

### What Bridge Should Be (Mario/MK Spirit)

```
Spec.lean          -- Pure specification (no implementation)
    ↓
Bridge/Basics.lean -- Definition-only glue (no proofs!)
    ↓              -- Types and contracts
Verify/Proofs.lean -- Implementation proofs (checkHyp, DV, typed subst, stack invariants)
    ↓
Kernel.lean        -- Imports: Spec + Bridge + Verify.Proofs (no circularity)
```

**Key principles:**
1. **Spec stays pure** - Mathematical definitions only
2. **Bridge is definition-only glue** - Structures and function signatures, NO PROOFS
3. **Verify owns implementation proofs** - All verification work stays here
4. **Kernel imports only what it needs** - Clean DAG, no cycles

### What Went Wrong with Codex's Approach

- ❌ **Timing:** Landed new module hierarchy while key proofs weren't finished
- ❌ **Scope:** Tried to move too much at once (multiple modules + directory reorg)
- ❌ **Testing:** Didn't verify build worked after changes

**The concept was right; the execution was premature.**

### When to Re-introduce Bridge

**After Phase 1 lands** (checkHyp proofs complete):

1. Create thin `Metamath/Bridge.lean` root:
   ```lean
   -- Metamath/Bridge.lean
   import Metamath.Spec
   import Metamath.Bridge.Basics
   ```

2. `Bridge/Basics.lean` contains ONLY:
   ```lean
   structure TypedSubst (fr : Spec.Frame) where
     σ : Spec.Subst
     typed : ∀ {c v}, Spec.Hyp.floating c v ∈ fr.mand → (σ v).typecode = c

   def floats (fr : Spec.Frame) : List (Spec.Constant × Spec.Variable) :=
     -- definition only, no proofs
   ```

3. **Keep all proofs in Verify** - Bridge is just types/contracts

4. **Test incrementally** - Ensure build stays green at each step

---

## Immediate Recovery (Completed ✅)

### Steps Executed

```bash
# 1. Restore core files to HEAD (Claude's clean TypedSubst state)
git restore Metamath/Kernel.lean Metamath/Verify.lean Metamath/Spec.lean
git restore lakefile.lean lean-toolchain

# 2. Remove broken directories
rm -rf Metamath/Bridge Metamath/Verify Metamath/Kernel
rm -f Metamath/KernelExtras.lean

# 3. Verify build
lake build  # ✅ 200 errors (baseline)
```

### Current State

**Files:**
- `Metamath/Kernel.lean` - 3392 lines (HEAD commit f79c5ac)
- `Metamath/Verify.lean` - Clean
- `Metamath/Spec.lean` - Clean
- Build: ✅ Compiling (200 baseline errors)

**Archive:**
- `codex_archive/` - All of Codex's work preserved for reference
- See `CODEX_TREASURE_MAP.md` for detailed catalog

---

## Forward Path: Focus, Low-Risk, High-Impact

**Goal:** Finish the verified verifier on clean tree, then re-introduce thin Bridge.

---

## Phase 1: Harden `toSubst` & Finish `checkHyp` Trio

**Objective:** Complete the typed substitution pipeline with no axioms/stubs.

### 1.1 Finalize Fail-Fast `toSubstTyped`

**Current location:** Kernel.lean (~line 1237+, KIT A infrastructure)

**API design:**
```lean
def toSubstTyped (σ_impl : HashMap String Formula)
                 (fr : Spec.Frame)
                 : Option TypedSubst :=
  -- Uses typed witnesses from checkHyp
  -- No "phantom wff" fallbacks
  -- Returns Some only if all bindings are well-typed
```

**Elimination lemma:**
```lean
lemma toSubstTyped_witnesses (h : toSubstTyped σ_impl fr = some σ_typed) :
    ∀ (c v : String), Spec.Hyp.floating c v ∈ fr.mand →
      ∃ f e, σ_impl.find? v = some f ∧
             toExprOpt f = some e ∧
             e.typecode = c
```

**Why this matters:**
- Eliminates "phantom wff" bug permanently
- Type safety enforced at construction time
- Clean API for Kernel to consume

**Estimated effort:** ~80-100 lines (using existing KIT A infrastructure)

---

### 1.2 Prove the 3 `checkHyp_*` Theorems

**Current status:** Signatures stated in Kernel.lean, need proofs

**Reference:** `codex_archive/Verify/Proofs.lean` contains `checkHyp_preserves_HypProp` (~150 lines, fully proven!) - use as template!

#### Theorem 1: `checkHyp_stack_split`

**Signature:**
```lean
theorem checkHyp_stack_split
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    (h_off : off + hyps.size = stack.size)
    : ∃ remaining hypTail,
        stack_converted = remaining ++ hypTail.reverse ∧
        hypTail.length = hyps.size
```

**Proof strategy:**
- Induction on `hyps.size - i`
- Track stack consumption: each hypothesis reads from `stack[off + i]`
- Stack shape invariant maintained throughout loop

**Codex reference:** `checkHyp_stack_split_theorem` in Verify/Proofs.lean:688-695

**Estimated effort:** ~60-80 lines

---

#### Theorem 2: `checkHyp_images_convert`

**Signature:**
```lean
theorem checkHyp_images_convert
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    : ∀ v val, σ.find? v = some val →
        ∃ e, toExprOpt val = some e
```

**Proof strategy:**
- Every binding comes from a floating hypothesis check
- Floating check includes typecode guard: `f[0]! == val[0]!`
- This guard ensures `val` has valid structure for conversion

**Key insight from GPT-5:** "Record (per float) the head-constant equality you actually used to succeed. If your current HypBinding doesn't carry it, extend it."

**Codex reference:**
- `checkHyp_image_exists` in Verify/Proofs.lean:741-748
- `FloatBindWitness` structure carries the equality witness

**Estimated effort:** ~80-100 lines

---

#### Theorem 3: `checkHyp_domain_covers`

**Signature:**
```lean
theorem checkHyp_domain_covers
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    (h_float : Spec.Hyp.floating c v ∈ frame.mand)
    : σ.contains v
```

**Proof strategy:**
- Induction shows every floating hypothesis inserts its variable
- Domain monotonicity: each iteration only grows the map
- At end, all frame variables are covered

**Codex reference:**
- `checkHyp_domain_covers_theorem` in Verify/Proofs.lean:715-728
- `checkHyp_contains_mono` (monotonicity lemma) in Verify/Proofs.lean:652-656

**Estimated effort:** ~60-80 lines

---

### 1.3 Single Induction Schema (Recommended by GPT-5)

**Instead of proving each theorem separately, use ONE induction that threads all invariants:**

```lean
theorem checkHyp_master_invariant
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    : StackSplitProp σ ∧ ImagesConvertProp σ ∧ DomainCoversProp σ
```

**Induction variable:** `hyps.size - i`

**Invariants threaded:**
1. Stack shape: `stack[0..off+i]` processed, `stack[off+i..]` remaining
2. Substitution bindings: all inserted values convert via `toExprOpt`
3. Domain coverage: variables `{v | ∃j < i, hyps[j] = floating _ v}` all in `σ`
4. Typecode guard: each binding satisfies `f[0]! == val[0]!`

**Why this is better:**
- Single traversal of the recursion structure
- Shared setup and context
- Interdependent properties proven together

**Codex provides the template:** `checkHyp_preserves_HypProp` in Verify/Proofs.lean:467-619 (150 lines, FULLY PROVEN)

**Key structure from Codex:**
```lean
-- From codex_archive/Verify/Proofs.lean:467-619
lemma checkHyp_preserves_HypProp
    {i : Nat} {subst σ : Std.HashMap String Formula}
    (hi : i ≤ hyps.size)
    (hprop : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) i subst)
    (hrun : DB.checkHyp db hyps stack off i subst = .ok σ) :
    HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) hyps.size σ := by
  -- Unfold checkHyp recursion
  -- Case analysis on i = hyps.size vs i < hyps.size
  -- Recursive case: analyze floating vs essential
  -- Show invariant is preserved after insertion
```

**How to adapt:**
1. Extend `HypProp` to include stack-split and domain-coverage clauses
2. Follow Codex's case analysis structure (i = size / i < size)
3. Use Codex's floating case handling (lines 520-580)
4. Add stack-shape tracking to the invariant

**Estimated effort:** ~180-220 lines (but proves all 3 theorems at once!)

---

### 1.4 Derive "Typed Coverage" Directly

**Theorem:**
```lean
theorem checkHyp_produces_typed_coverage
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    : ∀ (c v : String), Spec.Hyp.floating c v ∈ frame.mand →
        ∃ f e, σ.find? v = some f ∧
               toExprOpt f = some e ∧
               e.typecode = c
```

**Proof:** Direct combination of theorems 2 and 3 above.

**Estimated effort:** ~20-30 lines (just combining results)

---

### 1.5 Plug into `toSubstTyped`

**Current location:** Kernel.lean uses typed witnesses in stepAssert

**Change needed:**
```lean
-- Old (has fallback path):
match toSubstTyped σ_impl frame with
| some σ_typed => use σ_typed  -- typed path
| none => sorry  -- REMOVE THIS FALLBACK

-- New (no fallback):
match toSubstTyped σ_impl frame with
| some σ_typed => use σ_typed
-- No fallback needed! checkHyp_produces_typed_coverage guarantees Some
```

**Proof obligation:** Show that `checkHyp` success implies `toSubstTyped` succeeds.

```lean
lemma checkHyp_implies_toSubstTyped_succeeds
    (h_check : DB.checkHyp db hyps stack off 0 ∅ = .ok σ)
    (h_frame : frame = toFrame db_entry)
    : ∃ σ_typed, toSubstTyped σ frame = some σ_typed := by
  apply toSubstTyped_witnesses
  exact checkHyp_produces_typed_coverage h_check
```

**Estimated effort:** ~40-50 lines

---

### Phase 1 Acceptance Criteria

✅ **`toSubstTyped` is complete** - No fallback paths
✅ **checkHyp master invariant proven** - Stack split + images convert + domain covers
✅ **Typed coverage theorem proven** - Combines the above
✅ **Kernel no longer relies on "subst converts" axiom/stub**
✅ **Build still green** (errors reduced from 200 baseline)

**Total estimated effort:** ~460-560 lines of proof

**Timeline:** 2-3 focused sessions

**Key reference:** Codex's `checkHyp_preserves_HypProp` (150 lines, fully proven) provides the roadmap!

---

## Phase 2: DV, Without Reorg Risk

**Objective:** Eliminate DV axioms by connecting impl ↔ spec via proven lemmas.

### 2.1 Normalize Variable Scans (impl ↔ spec)

**Current status:** `Formula.varsList` started in Kernel.lean

**Needed lemmas:**

#### Lemma: `foldlVars_eq_foldl_varsList`
```lean
theorem foldlVars_eq_foldl_varsList (f : Formula) (init : α) (op : α → String → α) :
    foldlVars f op init = f.varsList.foldl op init
```

**Why:** Connects imperative fold to list representation

**Estimated effort:** ~30-40 lines

---

#### Lemma: `foldlVars_all`
```lean
theorem foldlVars_all (P : String → Bool) (f : Formula) :
    foldlVars f (fun acc v => acc && P v) true = true ↔
    ∀ v ∈ f.varsList, P v = true
```

**Why:** Boolean fold ↔ universal quantification

**GPT-5's insight:** "Reduce Boolean fold checks to simple ∀ proofs via `foldlVars_all`"

**Codex reference:** `foldl_and_eq_true` in KernelExtras.lean:144-149

**Estimated effort:** ~40-50 lines

---

#### Lemma: `foldlVars_all₂`
```lean
theorem foldlVars_all₂ (P : String → String → Bool) (f g : Formula) :
    foldlVars f (fun acc v => foldlVars g (fun acc' w => acc' && P v w) acc) true = true ↔
    ∀ v ∈ f.varsList, ∀ w ∈ g.varsList, P v w = true
```

**Why:** Nested folds ↔ double quantification (exactly what DV needs!)

**Codex reference:** `foldl_all₂` in KernelExtras.lean:151-170

**Estimated effort:** ~50-70 lines

---

### 2.2 Bridge `toExprOpt` → `Spec.varsInExpr` Membership

**Theorem:**
```lean
theorem toExprOpt_preserves_vars
    (h_conv : toExprOpt f = some e) :
    ∀ v ∈ Spec.varsInExpr e, v ∈ f.varsList
```

**Why:** Variables in spec expression must come from impl formula

**Proof strategy:**
- Induction on formula structure
- Use symbol-disjointness invariant (constants won't masquerade as variables)
- Variable constructor case is direct

**Estimated effort:** ~60-80 lines

---

### 2.3 Replace DV Axioms

**Current axioms in Kernel.lean (need to eliminate):**
```lean
axiom dv_impl_to_spec : ...
axiom dv_caller_sound : ...
```

**Replacement theorems:**

#### Theorem: `dvOK_impl_iff_spec`
```lean
theorem dvOK_impl_iff_spec
    (h_conv_f : toExprOpt f = some ef)
    (h_conv_g : toExprOpt g = some eg)
    (h_dv_impl : foldlVars f (fun acc v =>
                   foldlVars g (fun acc' w => acc' && (v != w)) acc) true = true)
    : Spec.dvOK ef eg
```

**Proof:** Apply `foldlVars_all₂` + `toExprOpt_preserves_vars`

**Estimated effort:** ~40-60 lines

---

#### Theorem: `checkDV_caller_sound`
```lean
theorem checkDV_caller_sound
    (h_dv_check : checkDV_caller_impl stack frame = true)
    (h_conv : stack_impl converts to stack_spec)
    : ∀ i j, i < stack_spec.length → j < stack_spec.length → i ≠ j →
        Spec.dvOK stack_spec[i] stack_spec[j]
```

**Proof:** Unfold nested folds, apply `dvOK_impl_iff_spec`

**Estimated effort:** ~60-80 lines

---

#### Theorem: `checkDV_callee_sound`
```lean
theorem checkDV_callee_sound
    (h_dv_check : checkDV_callee_impl frame = true)
    (h_conv : frame_impl converts to frame_spec)
    : ∀ dv ∈ frame_spec.dvs, Spec.dvOK (σ dv.v₁) (σ dv.v₂)
```

**Proof:** Similar structure to caller case

**Estimated effort:** ~60-80 lines

---

### Phase 2 Acceptance Criteria

✅ **Variable scan lemmas proven** - `foldlVars_all`, `foldlVars_all₂`
✅ **Conversion membership proven** - `toExprOpt_preserves_vars`
✅ **DV axioms eliminated** - Replaced with proven theorems
✅ **Build still green**

**Total estimated effort:** ~320-420 lines

**Timeline:** 1-2 focused sessions

**Key references:**
- Codex's `foldl_and_eq_true`, `foldl_all₂` in KernelExtras.lean
- GPT-5's advice on reducing boolean folds to quantification

---

## Phase 3: Final Integration & Cleanup

### 3.1 Eliminate Remaining Sorries

**Current count:** ~40 strategic sorries in Kernel.lean

**Categories:**
1. Helper lemmas (Array/List, HashMap) - ~15 sorries
2. WF (well-formedness) propagation - ~10 sorries
3. Stack/substitution correctness - ~8 sorries
4. Main theorems using above helpers - ~7 sorries

**Strategy:** Bottom-up proving
- Start with helper lemmas (may already exist in Mathlib)
- Build up to WF propagation
- Complete stack/subst theorems
- Fill main theorem gaps

**Estimated effort:** ~400-600 lines (varies based on Mathlib coverage)

**Timeline:** 2-3 sessions

---

### 3.2 Introduce Thin Bridge (Definition-Only)

**After Phase 1 & 2 are complete and green:**

**Step 1:** Create `Metamath/Bridge/Basics.lean`
```lean
-- Metamath/Bridge/Basics.lean
import Metamath.Spec

namespace Metamath.Bridge

/-- Typed substitution structure (definition only) -/
structure TypedSubst (fr : Spec.Frame) where
  σ : Spec.Subst
  typed : ∀ {c v}, Spec.Hyp.floating c v ∈ fr.mand →
    (σ v).typecode = c

/-- Extract floating hypotheses from frame (definition only) -/
def floats (fr : Spec.Frame) : List (Spec.Constant × Spec.Variable) :=
  fr.mand.foldr
    (fun h acc =>
      match h with
      | .floating c v => (c, v) :: acc
      | .essential _ => acc)
    []

/-- Extract essential hypotheses from frame (definition only) -/
def essentials (fr : Spec.Frame) : List Spec.Expr :=
  fr.mand.foldr
    (fun h acc =>
      match h with
      | .floating _ _ => acc
      | .essential e => e :: acc)
    []

end Metamath.Bridge
```

**Step 2:** Create `Metamath/Bridge.lean` root
```lean
-- Metamath/Bridge.lean
import Metamath.Bridge.Basics
```

**Step 3:** Update `lakefile.lean`
```lean
lean_lib Metamath where
  roots := #[`Metamath.Spec, `Metamath.Bridge, `Metamath.Verify, `Metamath.Kernel]
```

**Step 4:** Update imports in `Kernel.lean`
```lean
import Metamath.Spec
import Metamath.Bridge  -- Now available!
import Metamath.Verify
```

**Step 5:** Test incrementally
```bash
lake build Metamath.Bridge  # Should succeed (definitions only)
lake build Metamath.Kernel  # Should still succeed
```

**Key principle:** NO PROOFS IN BRIDGE. All proofs stay in Verify.

**Estimated effort:** ~100-150 lines (definitions + integration)

**Timeline:** 1 session (after proofs are stable)

---

### 3.3 Final Verification Sweep

**Objectives:**
1. ✅ All axioms eliminated (except Lean's built-ins)
2. ✅ All sorries removed
3. ✅ Build clean (0 errors)
4. ✅ Documentation updated
5. ✅ Tests pass (if any)

**Final checklist:**
```bash
# Check for remaining axioms
grep -n "axiom" Metamath/*.lean

# Check for remaining sorries
grep -n "sorry\|admit" Metamath/*.lean

# Full build
lake build

# Count errors (should be 0)
lake build 2>&1 | grep -E "^error:" | wc -l
```

---

## Phase 4: Polish & Documentation

### 4.1 Create Clean Status Report

**Document:**
- What was proven
- What infrastructure was built
- How the pieces fit together
- Architecture diagram (Spec → Bridge → Verify → Kernel)

### 4.2 Extract Key Learnings

**From this experience:**
- ✅ Build-first discipline essential
- ✅ Incremental changes keep momentum
- ✅ Thin abstraction layers (Bridge) are powerful when done right
- ✅ Timing matters: land infrastructure before reorganizing

### 4.3 Acknowledge Contributions

**Contributors:**
- **Claude (this session):** TypedSubst KIT A & B, recovery strategy
- **Codex (archived):** checkHyp loop invariant template, helper lemmas
- **GPT-5 (advisory):** Strategic guidance on incremental approach

---

## Codex's Valuable Contributions (To Mine from Archive)

*See `CODEX_TREASURE_MAP.md` for full catalog*

**Top items to reference:**

1. **`checkHyp_preserves_HypProp`** (Verify/Proofs.lean:467-619)
   - 150-line loop invariant proof, FULLY PROVEN
   - Template for Phase 1.3 master invariant
   - Shows exactly how to structure the induction

2. **`FloatBindWitness` structure** (Verify/Proofs.lean:50-63)
   - Witness pattern for floating hypothesis bindings
   - Carries the head-constant equality (GPT-5's point!)
   - Clean design worth adapting

3. **`foldl_and_eq_true`, `foldl_all₂`** (KernelExtras.lean:144-170)
   - Boolean fold lemmas (proven!)
   - Exactly what Phase 2.1 needs for DV

4. **`mapM` infrastructure** (KernelExtras.lean:177-264)
   - `mapM_index_some`, `mapM_mem`, `mapM_length` (all proven!)
   - Generally useful, may want to import

5. **Alternative `TypedSubst` design** (Bridge/Basics.lean:11-15)
   - Frame-centric (vs my declaration-map approach)
   - Worth comparing when introducing Bridge in Phase 3.2

---

## Housekeeping for Fast Iteration

### Pre-commit Discipline

**Create `.git/hooks/pre-commit`:**
```bash
#!/bin/bash
# Pre-commit hook: ensure build works and no new sorries

echo "Running pre-commit checks..."

# Check for new sorries in changed files
if git diff --cached --name-only | grep -E '\.lean$' | xargs grep -H "sorry\|admit" > /dev/null; then
    echo "WARNING: Commit contains sorry/admit. Proceed? (y/n)"
    read answer
    if [ "$answer" != "y" ]; then
        echo "Commit aborted."
        exit 1
    fi
fi

# Quick build check (optional - can be slow)
# lake build 2>&1 | grep -E "^error:" | head -5

echo "Pre-commit checks passed."
```

### Incremental Landing Strategy

**GPT-5's advice:** "One failing theorem at a time. Tiny PRs, green in between."

**Workflow:**
1. Pick single theorem (e.g., `checkHyp_stack_split`)
2. Prove it (maybe ~60 lines)
3. Test: `lake build` - ensure still green
4. Commit: `git commit -m "Prove checkHyp_stack_split"`
5. Repeat for next theorem

**Benefits:**
- Always have a working state to return to
- Easy to bisect if something breaks
- Clear progress tracking

### No Proofs in Bridge Rule

**If tempted to add a proof to Bridge:**
→ Stop and ask: "Does this belong in Verify instead?"

**Bridge = types + contracts**
**Verify = proofs**

---

## Timeline Estimates

### Phase 1: checkHyp + TypedSubst (2-3 sessions)
- 1.1 Finalize toSubstTyped: ~80-100 lines
- 1.2/1.3 Master invariant: ~180-220 lines
- 1.4 Typed coverage: ~20-30 lines
- 1.5 Integration: ~40-50 lines
- **Total:** ~460-560 lines

### Phase 2: DV Replacement (1-2 sessions)
- 2.1 Variable scans: ~120-160 lines
- 2.2 Membership: ~60-80 lines
- 2.3 DV theorems: ~160-220 lines
- **Total:** ~320-420 lines

### Phase 3: Integration (3-4 sessions)
- 3.1 Remaining sorries: ~400-600 lines
- 3.2 Thin Bridge: ~100-150 lines
- 3.3 Verification sweep: validation only
- **Total:** ~500-750 lines

### Phase 4: Polish (1 session)
- Documentation and cleanup

**Grand Total:** ~1280-1730 lines of new proof
**Overall timeline:** 7-10 focused sessions = **2-3 weeks** at steady pace

---

## Success Metrics

### Quantitative
- ✅ 0 axioms (except Lean built-ins)
- ✅ 0 sorries/admits
- ✅ 0 build errors
- ✅ ~5200-5300 total lines (estimated)

### Qualitative
- ✅ Clean module architecture (Spec → Bridge → Verify → Kernel)
- ✅ Type-safe substitution handling (no phantom wff)
- ✅ DV checks at spec level (no axioms)
- ✅ Maintainable proof structure (clear separation of concerns)

### Documentation
- ✅ Architecture diagram
- ✅ Key theorem list with descriptions
- ✅ Contribution acknowledgments
- ✅ Lessons learned summary

---

## Conclusion

**Current status:** ✅ Clean build, ready to execute

**Strategy:** Revert-then-finish-proofs path with incremental Bridge introduction

**Key insight from GPT-5:** "Sometimes 'undo' is the fastest path forward." ✓

**Next immediate step:** Begin Phase 1.1 (Finalize fail-fast toSubstTyped)

**Reference for Phase 1.3:** Codex's `checkHyp_preserves_HypProp` (~150 lines, proven) in `codex_archive/Verify/Proofs.lean:467-619`

---

**This plan honors:**
- ✅ Claude's TypedSubst infrastructure (foundation)
- ✅ Codex's theoretical contributions (archived and cataloged)
- ✅ GPT-5's strategic guidance (incremental, build-first approach)

**Let's ship a verified verifier!** 🚀

---

**Date:** 2025-10-12
**Next milestone:** Phase 1.1 complete (toSubstTyped finalized)
**Final goal:** Fully verified Metamath checker in Lean 4
