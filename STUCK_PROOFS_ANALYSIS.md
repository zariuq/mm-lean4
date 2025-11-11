# Incomplete Proofs in KernelClean.lean - Complete Analysis

## Summary

**File:** `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/KernelClean.lean`

**Total Stuck Proofs:** 15 locations (3 ADMIT, 12 SORRY)

### Breakdown by Type

| Type  | Count | Lines |
|-------|-------|-------|
| ADMIT | 3     | 328, 370, 401 |
| SORRY | 12    | 861, 886, 987, 1008, 1016, 1020, 1100, 2022, 2074, 2136, 2142, 2338 |

---

## Critical Induction Proofs (ADMIT - Must Complete)

### 1. **Line 328** - `subst_preserves_head_of_const0`

**Category:** Formula.subst induction with fold

**Signature:**
```lean
theorem subst_preserves_head_of_const0
    {σ : Std.HashMap String Verify.Formula}
    {f g : Verify.Formula}
    (hf : 0 < f.size)
    (hhead : ∃ c, f[0]! = Verify.Sym.const c)
    (h_sub : f.subst σ = Except.ok g) :
  ∃ (hg : 0 < g.size), g[0]'hg = f[0]'hf
```

**What it proves:** When substituting into a formula with a constant head, the head is preserved after the fold operation

**Proof sketch:**
- Rewrite `f.subst σ` as `f.toList.foldlM (Formula.substStep σ) #[]`
- Split `f.toList = s₀ :: tail` where `s₀ = const c`
- First fold step: `substStep σ #[] (const c) = ok #[const c]`
- Remaining steps preserve head via `head_push_stable` and `head_append_many_stable`
- Induction on tail

**Blocking:** List induction pattern matching
**Helpers:** `head_push_stable`, `head_append_many_stable`, `subst_eq_foldlM`
**Complexity:** Medium (~50-100 lines)

---

### 2. **Line 370** - `subst_ok_flatMap_tail`

**Category:** Formula.subst / flatMap correspondence

**Signature:**
```lean
theorem subst_ok_flatMap_tail
  {σ : Std.HashMap String Formula} {f g : Formula}
  (hsub : f.subst σ = .ok g) :
  g.toList.tail = (f.toList.tail).flatMap (fun s =>
    match s with
    | .const _ => [s]
    | .var v   =>
      match σ[v]? with
      | none    => []
      | some e  => e.toList.drop 1)
```

**What it proves:** When `f.subst σ = ok g`, the tail of `g` equals the `flatMap` of the tail of `f` under the substition step specification

**Proof sketch:**
- Use `subst_eq_foldlM` to convert to functional fold
- List induction on `f.toList`
- Each `substStep` call must match the `flatMap` specification:
  - Constants: produce `[s]`
  - Variables: produce `e.toList.drop 1` or `[]`

**Blocking:** Case analysis on `substStep` behavior
**Pattern:** List induction with `foldlM` equation lemma
**Complexity:** Medium (~50-100 lines)

---

### 3. **Line 401** - `subst_preserves_head` (precondition)

**Category:** Parser invariant / well-formedness

**Location in code:**
```lean
theorem subst_preserves_head ... := by
  ...
  have hconst : ∃ c, f[0]! = Verify.Sym.const c := by
    -- Should come from ParserInvariants
    admit
```

**What it proves:** The first symbol of any well-formed formula is a constant (Metamath convention)

**Why it's blocked:**
- Needs lemma from `ParserInvariants.lean`
- Can be threaded from call-site (`assert_step_ok`)
- Metamath well-formedness property: typecode is always first

**Dependency:** `ParserInvariants.lean` must provide this
**Complexity:** Low (~10-20 lines, depends on parser lemma)

---

## Bridge Layer & Witness Extraction (SORRY)

### 4. **Line 861** - `toSubstTyped_of_allM_true`

**Category:** Monadic allM to TypedSubst witness extraction

**Signature:**
```lean
theorem toSubstTyped_of_allM_true
    (fr : Spec.Frame) (σ_impl : Std.HashMap String Verify.Formula)
    (hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true) :
  ∃ σ_typed : Bridge.TypedSubst fr, toSubstTyped fr σ_impl = some σ_typed
```

**What it proves:** When `allM` verifies all floats exist in the substitution, the `TypedSubst` witness can be constructed

**Blocker:** Function pattern mismatch
- `hAll` lambda: `fun (c, v) => ...` (direct tuple destructuring)
- `toSubstTyped` lambda: `fun x => ... x.fst x.snd` (pair access)
- Extensionally equal but Lean's pattern matching is tricky

**Technique:** Unfold `toSubstTyped`, use `Function.ext`, or careful matching
**Complexity:** Medium (~30-50 lines)

---

### 5. **Line 886** - `const_not_in_vars`

**Category:** Metamath convention axiom

**Signature:**
```lean
theorem const_not_in_vars (c : String) (vars : List Spec.Variable) :
    ¬(Spec.Variable.mk (toSym (Verify.Sym.const c)) ∈ vars)
```

**What it proves:** Constants never appear in variable lists (disjoint namespaces)

**Status:** Metamath naming convention axiom (non-blocking)
**Usage:** `flatMap_toSym_correspondence` const case
**Complexity:** Low (~10-20 lines, can keep as axiom)

---

### 6. **Line 987** - `flatMap_toSym_correspondence` (variable case)

**Category:** Monadic fold case analysis

**Location in code:**
```lean
-- In context of induction on syms (lines 926-989)
induction syms with
| cons s tail ih =>
    cases s with
    | var v =>
        cases h_lookup : σ_impl[v]? with
        | some f_v =>
            -- When v ∈ vars
            sorry  -- Need expansion of toExpr on both sides
```

**What it proves:** When `v ∈ vars` and `σ_impl[v]? = some f_v`, the LHS `(f_v.toList.drop 1).map toSym` equals RHS `(σ_spec v).syms`

**Technique:**
- Use hypothesis `h_toExpr_match : toExpr f_v = σ_spec v`
- Unfold `σ_spec v` and compare symbol lists
- Induction hypothesis handles tail

**Blocking:** Matching expansions of `toExpr`
**Complexity:** Medium (~40-60 lines)

---

### 7-9. **Lines 1008, 1016, 1020** - `flatMap_toSym_correspondence_ATTEMPT`

**Category:** Edge cases in list induction

**Context:** Commented proof showing edge cases (lines 990-1021)

Three separate `sorry` cases in same induction:

**Line 1008 (const case):**
```lean
-- Need: toSym(const c) ∉ vars
sorry
```

**Line 1016 (none case):**
```lean
-- If σ_impl[v]? = none and v ∈ vars: contradiction with h_match
-- If σ_impl[v]? = none and v ∉ vars: LHS=[], RHS=[v] mismatch
sorry
```

**Line 1020 (some case):**
```lean
-- If σ_impl[v]? = some and v ∈ vars: use h_match
-- If σ_impl[v]? = some and v ∉ vars: contradiction
sorry
```

**Status:** Proof structure documented but edge cases incomplete
**Dependency:** Line 886 (`const_not_in_vars`)
**Complexity:** Low-Medium (already have structure)

---

### 10. **Line 1100** - `subst_correspondence` (frame condition)

**Category:** Frame well-formedness assumption

**Location in code:**
```lean
have h_vars_in_syms : ∀ v, Verify.Sym.var v ∈ f_impl.toList.tail 
                             → Spec.Variable.mk v ∈ vars := by
  sorry  -- Need frame well-formedness condition
```

**What it proves:** All variables in formula tail are in the frame's variable list

**Why blocked:** Frame construction invariant (parser/validation responsibility)

**Status:** Reasonable assumption; should come from database construction lemmas
**Complexity:** Low-Medium (~20-30 lines)

---

## Main Theorem & Array Induction (SORRY)

### 11. **Line 2022** - `verify_impl_sound` (ProofValid witness)

**Category:** Array induction over proof steps

**Location in code:**
```lean
unfold Spec.Provable
refine ⟨[], [toExpr e_final], ?_, rfl⟩
sorry  -- TODO: Array induction using stepNormal_sound at each step
```

**What it proves:** The proof array's `foldlM` maintains `Provable` - constructs `ProofValid` witness

**Goal:** Given:
```
proof.foldlM (fun pr step => Verify.DB.stepNormal db pr step) pr_init = Except.ok pr_final
```

Construct:
```
∃ steps finalStack, ProofValid Γ fr finalStack steps ∧ finalStack = [toExpr e_final]
```

**Pattern:** Array induction (see `Lean Curriculum/02_FoldInduction.lean`)
**Technique:** 
- Induction on proof array length
- Each element becomes a `ProofStep`
- Use `stepNormal_sound` at each step

**Complexity:** High (~80-120 lines, architectural framework)

---

### 12. **Line 2074** - `verify_impl_sound` (DB frame validity)

**Category:** Database construction assumption

**Location in code:**
```lean
have h_frame : ∃ fr, toFrame db db.frame = some fr := by
  sorry  -- AXIOM 4: well-formed db → valid frame
```

**What it proves:** Converting DB frame to spec frame always succeeds (well-formedness)

**Status:** 
- AXIOM 4 candidate - database construction responsibility
- Could be proven from DB construction invariants
- May keep as axiom (non-blocking)

**Complexity:** Low-Medium (~15-25 lines)

---

## Phase 8: Compressed Proofs (Heap-based)

### 13-14. **Lines 2136, 2142** - `stepProof_equiv_stepNormal` (error cases)

**Category:** Error equivalence between implementations

**Location:**
```lean
theorem stepProof_equiv_stepNormal ... := by
  cases obj with
  | const _ =>
      simp [h_find]
      sorry  -- Error equivalence for const case
  | var _ =>
      simp [h_find]
      sorry  -- Error equivalence for var case
```

**What it proves:** When object is const/var, both `stepProof` and `stepNormal` error equivalently

**Problem:** Both throw errors but messages differ

**Solutions:**
- (a) Prove error messages are equivalent
- (b) Change theorem to use `Result.isError` instead
- (c) Adjust error handling in implementations

**Complexity:** Low-Medium (~15-25 lines each)

---

### 15. **Line 2338** - `verify_compressed_sound`

**Category:** Phase 8.3 completion

**Signature:**
```lean
theorem verify_compressed_sound ... := by
  sorry  -- TODO: Complete after Phase 8.3
```

**What it proves:** Compressed proof execution equivalent to normal proof execution

**Dependencies:**
- `compressed_proof_sound` (Phase 8.3)
- Conversion between heap indices and labels

**Strategy:**
1. Use `compressed_proof_sound` to get equivalent normal proof
2. Apply `verify_impl_sound` to the normal proof
3. Conclude with `Provable`

**Status:** Depends on Phase 8.3
**Complexity:** Medium (straightforward application once 8.3 complete)

---

## Completion Priority & Strategy

### Tier 1 (Critical Path)

1. **Line 401** - Parser invariant (10-20 lines)
   - Prerequisite for lines 328, 370

2. **Line 328** - Head preservation (50-100 lines)
   - Prerequisite for multiple bridge proofs

3. **Line 370** - Tail/flatMap correspondence (50-100 lines)
   - Core substitution correspondence

### Tier 2 (Bridge Layer)

4. **Line 861** - TypedSubst witness (30-50 lines)
5. **Line 987** - Variable case in flatMap (40-60 lines)
6. **Line 1100** - Frame well-formedness (20-30 lines)

### Tier 3 (Main Theorem)

7. **Line 2022** - Array induction (80-120 lines)
8. **Line 2074** - DB frame validity (15-25 lines, may keep as axiom)

### Tier 4 (Phase 8 - Lower Priority)

9. **Lines 2136, 2142** - Error equivalence (15-25 lines each)
10. **Line 2338** - Compressed proofs (depends on 8.3)

### Axioms (May Keep)

- **Line 886** - `const_not_in_vars` (Metamath convention)

---

## Files with Related Infrastructure

- `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/KernelExtras.lean` - Helper lemmas (axioms about HashMap, filterMap)
- `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/ArrayListExt.lean` - Array/List correspondence lemmas
- `/home/zar/claude/hyperon/metamath/mm-lean4/Lean Curriculum/02_FoldInduction.lean` - Pattern for array induction
- `/home/zar/claude/hyperon/metamath/mm-lean4/Metamath/ParserInvariants.lean` - Well-formedness lemmas (needed for line 401)

---

## Key Lemmas Already Available

These can be used directly in stuck proofs:

- `subst_eq_foldlM` - Converts `Formula.subst` to functional fold
- `head_push_stable`, `head_append_many_stable` - Head preservation under fold
- `toExprOpt_some_iff_toExpr` - Equivalence between `toExprOpt` and `toExpr`
- `filterMap_fusion` - List fusion for `toFrame_floats_eq`
- `allM` - Monadic predicate for witness extraction

