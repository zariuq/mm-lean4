# GPT-5 Pro Tasks: Complete checkHyp_ensures_floats_typed Proof

## Context

Claude Code successfully converted `checkHyp_ensures_floats_typed` from an **axiom** to a **theorem** with proof structure. However, hit a Lean 4 parser compatibility issue with complex nested match expressions.

**Current Status:**
- ✅ Theorem structure complete
- ✅ Helper axiom `floatsProcessed_preservation` defined
- ⚠️ `FloatsProcessed` definition simplified to `True` (parser workaround)
- ⚠️ Theorem proof body is `sorry` (waiting on FloatsProcessed)

**Files:**
- `Metamath/KernelClean.lean` lines 745-793

---

## Task 1: Fix FloatsProcessed Definition (HIGH PRIORITY)

**Problem:** Lean 4.20.0-rc2 rejects this syntax:

```lean
def FloatsProcessed
    (db : Verify.DB) (hyps : Array String)
    (n : Nat) (σ : Std.HashMap String Verify.Formula) : Prop :=
  ∀ j, j < hyps.size → j < n →
    match db.find? hyps[j]! with
    | some (.hyp false f _) =>
        f.size = 2 →
        match f[0]!, f[1]! with
        | .const c, .var v =>
            ∃ val, σ[v]? = some val ∧
                   val.size > 0 ∧
                   (toExpr val).typecode = ⟨c⟩
        | _, _ => True
    | _ => True
```

**Error:** Line 766:23: "function expected at `j < n →`", "term has type Prop"

**What Claude Tried:**
- ✅ Removing dependent types from `∀` binder: `∀ j, j < hyps.size →` instead of `∀ j (hj : j < hyps.size)`
- ✅ Adding parentheses: `∀ j, j < hyps.size → (j < n → ...)`
- ✅ Removing `private` modifier
- ❌ Still fails with same error

**Questions for GPT-5:**
1. Is this a known Lean 4.20.0-rc2 limitation with nested match in `∀` body?
2. Can you provide a syntax that works in this Lean version?
3. Should we:
   - Extract match arms into separate helper predicates?
   - Use a different formulation (e.g., `List.all₂`)?
   - Factor the definition differently?

**Success Criteria:**
- `FloatsProcessed` compiles with full definition (not `True`)
- Captures: "every float variable up to index n is bound with correct type"
- No new axioms introduced

---

## Task 2: Prove floatsProcessed_preservation (MEDIUM PRIORITY)

**Current State:** Axiom (line 769-774)

```lean
axiom floatsProcessed_preservation
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ_impl : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ_impl →
    FloatsProcessed db hyps hyps.size σ_impl
```

**Goal:** Convert to `theorem` with proof

**Approach:** Strong induction on `k = hyps.size - i`
- Base case (k=0): `i = hyps.size`, no more hyps, `FloatsProcessed hyps.size σ` holds
- Inductive step: Process hyp at index `i`, recurse on `i+1`
  - If float: Show `insert` maintains invariant + adds new binding
  - If essential: Show σ unchanged, invariant preserved

**Reference Code:** `codex_archive/Verify/Proofs.lean` lines 115-270
- Has proven `checkHyp_preserves_HypProp` using this exact pattern
- Can adapt structure, add typing information

**Challenges:**
- Need to reason about `Verify.DB.checkHyp` recursion (lines 401-418 in `Metamath/Verify.lean`)
- Need `HashMap.insert` preservation lemmas
- Need to connect `f[0]! == val[0]!` check to `(toExpr val).typecode`

**Success Criteria:**
- `floatsProcessed_preservation` is a `theorem`, not `axiom`
- Proof ~150-200 lines (similar to archive)
- Uses only standard Lean 4 tactics

---

## Task 3: Complete checkHyp_ensures_floats_typed Proof (LOW PRIORITY)

**Current State:** Theorem with `sorry` (line 792-793)

**Dependencies:** Requires Task 1 + Task 2 complete

**What's Already Done:**
- Theorem statement is correct
- Calls `floatsProcessed_preservation` to get invariant
- Has case-split logic sketched (lines 796-832, currently removed)

**What's Needed:**
Once `FloatsProcessed` is properly defined, uncomment the proof body:

```lean
theorem checkHyp_ensures_floats_typed ... := by
  intro h_ok i hi
  have h_floats := floatsProcessed_preservation db hyps stack off σ_impl h_ok
  have h_at_i := h_floats i hi (...)
  cases hobj : db.find? hyps[i]! with
  | none => trivial
  | some obj =>
      cases obj with
      | hyp ess f lbl =>
          cases ess
          | true => trivial
          | false =>  -- Float case
              intro h_size
              cases hf0 : f[0]! ; cases hf1 : f[1]!
              -- Extract from h_at_i that σ_impl[v]? = some val
              -- Show val has correct size and typecode
```

**Success Criteria:**
- No `sorry` in theorem body
- Uses `FloatsProcessed` invariant cleanly
- Build passes

---

## Task 4: Document the Architecture (BONUS)

Once complete, update these files:

**EXEC_SUMMARY_2025-11-01.md:**
- Change "AXIOM 2: checkHyp_ensures_floats_typed" → "✅ THEOREM 2: checkHyp_ensures_floats_typed PROVEN"
- Update axiom count: 4 total → 3 total (or 2 if floatsProcessed also proven)
- Update completion percentage: 65-70% → 75-80%

**Metamath/KernelClean.lean header:**
- Update sorry count in comment block (currently says "13 total")
- Document the proof technique used

---

## Priority Order

1. **Task 1** (CRITICAL): Fix FloatsProcessed syntax - blocks everything
2. **Task 2** (HIGH): Prove floatsProcessed_preservation - core theorem work  
3. **Task 3** (MEDIUM): Complete main theorem proof - cleanup
4. **Task 4** (LOW): Documentation - polish

---

## Notes for GPT-5

**Environment:**
- Lean 4.20.0-rc2
- Batteries package available
- Standard library only (no mathlib)

**Constraints:**
- Work with our Lean version, not archive version
- No sections with `variable` (parser issues discovered)
- Explicit parameters everywhere
- Avoid `private` on lemmas (causes issues)

**Known Working Patterns:**
- `def HypPropTyped ... : Prop := ∀ v val, σ[v]? = some val → ∃ j c, ...` (backward invariant works!)
- Strong induction via `have main : ∀ k, ... := by induction k`
- HashMap reasoning with `[v]?` syntax

**Known Broken Patterns:**
- `∀ j (hj : j < n), ...` with dependent type in binder
- `∀ j, j < n → match ... ` (our current blocker!)
- `private lemma` (should be just `lemma`)
- Section variables with implicit parameters `{m n : Nat}`

---

**Estimated Effort:**
- Task 1: 1-2 hours (syntax puzzle)
- Task 2: 4-6 hours (main proof work)
- Task 3: 1 hour (cleanup)
- Task 4: 30 minutes (documentation)

**Total: 6-10 hours** to eliminate this axiom completely.
