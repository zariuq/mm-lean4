# Final Roadmap: Optimal Transport to Fully Verified mm-lean4

**Date:** 2025-10-08
**Source:** GPT-5 Pro feedback + preprocessing verification plan
**Goal:** Complete end-to-end formal verification

---

## Current Status ✅

- **Spec kernel:** Proven sound (stepNormal_sound, verify_sound)
- **Bridge:** stepNormal_impl_correct complete structure with 22 axioms
- **Infrastructure:** WF invariant, projections, two-phase correspondence

**Gap:** 22 routine axioms + verify_impl_sound fold

---

## Phase 1: Eliminate 22 Axioms (1-2 Weeks)

### Proving Order (GPT-5 Optimal)

**A. Array/List Bridge (Priority 1 - Fast Wins)**
```lean
1. array_list_push : (arr.push x).toList = arr.toList ++ [x]
2. array_push_size : (arr.push x).size = arr.size + 1
3. array_push_get : (arr.push x)[i] = if i < arr.size then arr[i] else x
4. array_list_get : arr.get? i = arr.toList.get? i
```
**Why first:** May exist in std; unlocks stack correspondence
**Effort:** 1-2 hours (or 0 if in std!)

**B. Determinism (Priority 2 - Trivial)**
```lean
5. toExpr_unique : toExpr f = some e1 → toExpr f = some e2 → e1 = e2
6. toFrame_unique : toFrame db fr = some fr1 → toFrame db fr = some fr2 → fr1 = fr2
```
**Why second:** One-liners, simplify many sorries
**Effort:** <1 hour

**C. Proof-State Invariants (Priority 3 - Unlocks Hypothesis)**
```lean
7. proof_state_has_inv : ProofStateInv db pr
8. build_spec_stack : Build List from array using pr_inv.stack_converts
9. stack_push_correspondence : Pushing preserves correspondence
```
**Why third:** Closes all hypothesis-case stack sorries
**Effort:** 2-3 hours

**D. Frame Preservation (Priority 4 - Closes Hypothesis)**
```lean
10. toFrame_preserves_hyps : Hypotheses match between impl and spec
11. hyp_in_scope : Well-formed proofs reference in-scope hypotheses (derived from 10)
```
**Why fourth:** Completes hypothesis case
**Effort:** 3-4 hours

**E. stepAssert/checkHyp Group (Priority 5 - Closes Assertion)**
```lean
12. extract_checkHyp_success
13-14. checkHyp_floats_sound, checkHyp_essentials_sound
15. subst_converts
16. dv_impl_matches_spec
17. db_lookup_commutes
18. checkHyp_gives_needed_list
19. stack_shape_from_checkHyp
20. stack_after_stepAssert
```
**Why last:** Largest chunk, but just unfolding stepAssert/checkHyp
**Effort:** 8-12 hours

**Result:** stepNormal_impl_correct fully proved (0 axioms)

---

## Phase 2: verify_impl_sound (Step 5) - 1 Session

```lean
theorem verify_impl_sound :
  WF db →
  Verify.verify db label f proof = .ok →
  Spec.Provable (toDatabase db) (toFrame db) (toExpr f) := by
  intro WFdb h_verify
  -- Induction on proof steps
  induction proof with
  | nil => sorry
  | cons step rest ih =>
      -- Use stepNormal_impl_correct at each step
      have h_step := stepNormal_impl_correct db pr step WFdb
      -- Carry WF invariant (per-constructor preservation)
      have WFdb' := insertStep_preserves_WF db step WFdb
      -- Compose with spec-level verify_sound
      apply Spec.verify_sound
      sorry
```

**Approach:**
- Fold stepNormal_impl_correct over proof array
- Maintain WF invariant throughout
- Compose with spec-level theorems (already proven)

**Effort:** 1 session (4-6 hours)

---

## Phase 3: Preprocessing Verification - 1-2 Sessions

### The Trust Boundary Problem

**Currently trusted (per SPEC_ALIGNMENT.md):**
- Lexer (whitespace, comments, tokens)
- File I/O and include resolution
- Scoping rules ($c, $v, $f blocks)
- Syntactic well-formedness

**Goal:** Make trust boundary explicit and minimal

### Solution: checkPreprocessInvariants

**Define a post-parse checker:**
```lean
def checkPreprocessInvariants (db : Verify.DB) : Bool :=
  -- 1. $c only at outermost scope
  checkConstantsOuterScope db &&

  -- 2. Variables: only in $v, unique $f per variable, no conflicts
  checkVariableDeclarations db &&

  -- 3. Includes: outermost only, not mid-statement (strict spec)
  checkIncludePolicy db &&

  -- 4. Balanced delimiters, complete statements
  checkSyntacticWellFormedness db &&

  -- 5. Labels unique & well-formed
  checkLabelUniqueness db &&

  -- 6. $d pairs are variables only
  checkDVPairsValid db
```

**Bridge to WF:**
```lean
theorem preprocess_ok_implies_WF :
  checkPreprocessInvariants db = true → WF db := by
  intro h_check
  unfold checkPreprocessInvariants at h_check
  -- Split conjunctions
  have ⟨h_const, h_vars, h_incl, h_syntax, h_labels, h_dv⟩ := h_check
  -- Build WF from components
  constructor
  · -- labels_unique: from checkLabelUniqueness
    exact labels_unique_from_check h_labels
  · -- frames_consistent: from checkVariableDeclarations
    exact frames_consistent_from_check h_vars
  · -- formulas_convert: from checkSyntacticWellFormedness
    exact formulas_convert_from_check h_syntax
  · -- current_frame_converts, db_converts: from checkVariableDeclarations
    sorry
  · -- toFrame_correct: from checkVariableDeclarations + checkSyntacticWellFormedness
    sorry
  · -- dv_correct: from checkDVPairsValid
    exact dv_correct_from_check h_dv
```

**Implementation Details:**

Each `check*` function mirrors your existing test suite:
```lean
def checkConstantsOuterScope (db : Verify.DB) : Bool :=
  db.constants.all (fun c =>
    -- Check c was declared at outermost scope
    -- Extract from your Test 1-10 logic
    true)

def checkVariableDeclarations (db : Verify.DB) : Bool :=
  db.variables.all (fun v =>
    -- Unique $f per variable
    -- No conflicts across blocks
    -- Extract from your Test 11-20 logic
    true)

-- ... similar for other checks
```

**Top-Level Soundness Claim:**
```lean
theorem mm_file_sound :
  parse_ok file ∧
  checkPreprocessInvariants db ∧
  Verify.verify db label f proof = .ok →
  Spec.Provable (toDatabase db) (toFrame db db.frame) (toExpr f) := by
  intro ⟨h_parse, h_preprocess, h_verify⟩
  have WFdb := preprocess_ok_implies_WF h_preprocess
  exact verify_impl_sound WFdb h_verify
```

**What This Achieves:**
1. **Explicit trust boundary:** Only lexer + file I/O are trusted
2. **Testable invariants:** checkPreprocessInvariants is executable
3. **Validated entry point:** DB must pass checks before kernel sees it
4. **Minimal TCB:** Everything after checkPreprocessInvariants is verified

**Effort:**
- Implement 6 check functions: 4-6 hours (extract from tests)
- Prove preprocess_ok_implies_WF: 4-6 hours (routine)
- Total: 1-2 sessions

---

## Phase 4: Build Gates & CI - 1 Hour

### Scoped Strict Mode
```lean
-- lakefile.lean
@[default_target]
lean_lib MetamathProofs where
  roots := #[`Metamath.Spec, `Metamath.Kernel]
  moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]

@[default_target]
lean_lib Metamath where
  roots := #[`Metamath.Verify]
  -- No strict mode for Verify.lean yet (defer cleanup)
```

### Axiom Audit
```lean
-- Metamath/Witness.lean
#print axioms stepNormal_impl_correct
-- Should print: (empty) after Phase 1

#print axioms verify_impl_sound
-- Should print: (empty) after Phase 2

#print axioms mm_file_sound
-- Should print: (empty) after Phase 3
-- Or only std library axioms (propext, quot.sound, etc.)
```

**CI Check:**
```bash
# .github/workflows/verify.yml
- name: Check axioms
  run: |
    lean Metamath/Witness.lean | grep "axioms:"
    # Fail if non-std axioms found
```

---

## Timeline Summary

| Phase | Description | Effort | Calendar |
|-------|-------------|--------|----------|
| Phase 1 | Prove 22 axioms | 28-41 hours | 1-2 weeks |
| Phase 2 | verify_impl_sound | 4-6 hours | 1 session |
| Phase 3 | Preprocessing | 8-12 hours | 1-2 sessions |
| Phase 4 | Build gates | 1 hour | 1 session |
| **Total** | **Complete verification** | **~2-3 weeks** | **2-3 weeks** |

**Parallelizable:**
- Phase 1 axioms are independent (can prove in any order)
- Phase 3 can start before Phase 1 completes

---

## Final Result

**What you'll have:**
```lean
theorem mm_file_sound :
  parse_ok file ∧
  checkPreprocessInvariants db ∧
  Verify.verify db label f proof = .ok →
  Spec.Provable (toDatabase db) (toFrame db db.frame) (toExpr f)
```

**Interpreted as:**
- **parse_ok:** File is valid Metamath syntax (lexer trusted)
- **checkPreprocessInvariants:** Scoping, declarations, includes are valid
- **verify_ok:** Kernel verification succeeds
- **⇒ Provable:** Database + frame + formula form a valid proof

**Trusted Computing Base (TCB):**
1. Lean 4 type checker
2. Lean 4 standard library
3. Lexer (whitespace, comments, tokenization)
4. File I/O (reading .mm files)

**Verified:**
- Metamath specification (Spec.lean)
- Metamath implementation (Verify.lean)
- Bridge between them (Kernel.lean)
- Preprocessing invariants (checkPreprocessInvariants)

**Performance:**
- All proofs erased at runtime (Prop/proof terms)
- Implementation unchanged (two-phase matching already matches)
- No runtime penalty

---

## Key Insights from GPT-5

1. **Prove axioms in right order:** Array/List → Determinism → Invariants → Frame → stepAssert
   - Minimizes backtracking
   - Each stage unlocks next

2. **Preprocessing as explicit gate:** checkPreprocessInvariants + preprocess_ok_implies_WF
   - Makes trust boundary explicit
   - Matches existing test suite
   - Executable and testable

3. **Scoped strict mode:** Turn on for proofs now, defer Verify.lean cleanup
   - Incremental progress
   - No blocking on legacy code

4. **Axiom audit in CI:** #print axioms catches regressions
   - Simple guard against hidden sorry/axiom
   - Standard practice

---

## Concrete Next Actions

**This session (1-2 hours):**
1. Prove array_list_push, array_push_size, array_push_get (or find in std)
2. Prove toExpr_unique, toFrame_unique (one-liners)

**Next session (4-6 hours):**
3. Prove proof_state_has_inv, build_spec_stack, stack_push_correspondence
4. Hypothesis case turns green ✅

**Following sessions:**
5. Prove toFrame_preserves_hyps, hyp_in_scope
6. Prove stepAssert/checkHyp group (largest chunk)
7. Implement verify_impl_sound (Step 5)
8. Implement checkPreprocessInvariants + bridge
9. Set up build gates + axiom audit

**Result:** Fully verified mm-lean4 with explicit trust boundary! 🎉

---

**Status:** Ready to execute. All conceptual work done; remaining work is mechanical.
