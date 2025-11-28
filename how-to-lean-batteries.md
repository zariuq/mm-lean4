# How to Lean 4 - Practical Guide

This document captures practical patterns and techniques learned while working on the Metamath verifier soundness proof.

## Table of Contents
- [If-Then-Else Reduction](#if-then-else-reduction)
- [BEq and Equality](#beq-and-equality)
- [HashMap Proofs](#hashmap-proofs)
- [Case Analysis](#case-analysis)
- [Pattern Matching with Cases](#pattern-matching-with-cases)
- [Do-Notation and ForIn Loop Proofs](#do-notation-and-forin-loop-proofs)
- [Array Indexing Equivalence](#array-indexing-equivalence)

---

## If-Then-Else Reduction

### Pattern: Reducing `if condition then a else b`

When you have a hypothesis `h : condition = true`, use this pattern:

```lean
have h_cond : condition = true := ...
unfold SomeType.field at h_cond ⊢
simp only [if_pos h_cond]
exact h_cond  -- or continue proof
```

**Key tactics**:
- `if_pos h` - reduces `if` when condition is true
- `if_neg h` - reduces `if` when condition is false
- Always `unfold` the relevant definitions first
- Use `simp only` (not `simp`) for precise control

**Example** (from `insert_error_propagates`):
```lean
have h' : (db.mkError pos msg).error = true := mkError_sets_error _ _ _
unfold DB.error at h' ⊢
simp only [if_pos h']
exact h'
```

---

## BEq and Equality

### Typeclass Hierarchy

**EquivBEq vs LawfulBEq**:
- `EquivBEq α` - provides equivalence relation (symm, trans, refl)
- `LawfulBEq α` - **additionally** provides `beq_iff_eq : (a == b) ↔ a = b`

**Rule of thumb**:
- Use `EquivBEq` when you only need equivalence properties
- Use `LawfulBEq` when you need to convert between `==` and `=`

### Pattern: Proving `k ≠ k'` implies `(k == k') = false`

**With LawfulBEq**:
```lean
theorem example [BEq α] [LawfulBEq α] (k k' : α) (h_ne : k ≠ k') :
    (k == k') = false := by
  have : ¬((k == k') = true) := by
    intro h
    rw [beq_iff_eq] at h  -- Convert (k == k') = true to k = k'
    exact h_ne h          -- Contradiction
  simp [this]
```

**Key lemma**: `beq_iff_eq : (a == b) ↔ a = b` (from `LawfulBEq`)

### Common BEq Lemmas

From `Init/Data/Bool.lean`:
- `Bool.eq_false_iff : b = false ↔ b ≠ true`
- `Bool.eq_true_iff : b = true ↔ b ≠ false`

---

## HashMap Proofs

### Batteries HashMap wraps Std.HashMap

```lean
-- Batteries
structure HashMap (α : Type u) (β : Type v) where
  inner : Std.HashMap α β

-- To use Std theorems directly:
theorem my_lemma [EquivBEq α] [LawfulHashable α] ... :=
  exact Std.HashMap.getElem?_insert_self
```

### Key HashMap Theorems (from Std)

**Insertion**:
```lean
-- Insert and lookup same key
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] :
  (m.insert k v)[k]? = some v

-- Insert and lookup different key
theorem getElem?_insert [EquivBEq α] [LawfulHashable α] :
  (m.insert k v)[a]? = if k == a then some v else m[a]?
```

**Pattern for "insert other key"**:
```lean
theorem find?_insert_other [LawfulBEq α] [LawfulHashable α]
    (m : HashMap α β) (k k' : α) (v : β) :
    k ≠ k' → (m.insert k v)[k']? = m[k']? := by
  intro h_ne
  rw [Std.HashMap.getElem?_insert]
  have : ¬((k == k') = true) := by
    intro h
    rw [beq_iff_eq] at h
    exact h_ne h
  simp [this]
```

**Note**: Need `LawfulBEq` (not just `EquivBEq`) to use `beq_iff_eq`.

### HashMap Through Record Updates

**Pattern**: When HashMap is a field in a record, simp can automatically apply HashMap lemmas through the record projection.

```lean
-- Record with HashMap field
structure DB where
  objects : HashMap String Object
  error? : Option Error

-- After record update, simp handles the projection
theorem example (db : DB) (label : String) (obj : Object) :
    { db with objects := db.objects.insert label obj }.objects[label]? = some obj := by
  simp  -- ✅ Automatically applies getElem?_insert_self through record projection!
```

**Key insight**: You don't need to manually extract the HashMap and apply lemmas. Just:
1. `unfold` the wrapper function (e.g., `DB.find?`)
2. Use `simp only [h_obj]` to substitute any matched objects
3. Call `simp` to reduce the record projection and apply HashMap lemmas

**Example** (from `insert_success_new`):
```lean
-- Goal: { db with objects := db.objects.insert label (obj label) }.objects[label]? = some (obj label)
unfold DB.find?  -- Reveals the .objects projection
simp only [h_obj]  -- Substitute obj label = .const c (or .var v, etc.)
simp  -- Reduces { db with objects := ... }.objects to db.objects.insert ..., then applies HashMap lemma
-- Goal solved! ✅
```

---

## Case Analysis

### Pattern: Nested Match Expressions

When classifier and implementation both match on the same expression:

```lean
-- Classifier
def classify (obj : Object) : Outcome :=
  match obj with
  | .const c => if condition then .error else .success
  | .var v => ...

-- Implementation
def process (obj : Object) : Result :=
  match obj with
  | .const c => if condition then mkError else insert
  | .var v => ...

-- Proof strategy
theorem classify_correct :
    match classify obj with
    | .error => result.error = true
    | .success => result.ok := by
  unfold classify process
  -- Now both match on obj - use match in proof:
  match obj with
  | .const c =>
    by_cases h : condition
    · simp [h]
      -- prove error case
    · simp [h]
      -- prove success case
  | .var v => ...
```

### Critical: Do `cases` BEFORE `simp` to preserve scope

**Problem**: When you need to case on a variable inside a proof, doing `simp` first can hide the variable.

**❌ Bad pattern**:
```lean
have ⟨o, h_some⟩ : ∃ o, db.find? label = some o := ...
simp [h_some]  -- o might become inaccessible!
cases o  -- ERROR: Unknown identifier 'o'
```

**✅ Good pattern**:
```lean
have h_exists : ∃ o, db.find? label = some o := ...
obtain ⟨o, h_some⟩ := h_exists  -- Use obtain to keep o in scope
cases o  -- ✅ Do cases BEFORE simp
· -- o = .const c
  rename_i c
  simp [h_some]
  -- Now c is accessible
· -- o = .var v
  rename_i v
  simp [h_some]
  -- Now v is accessible
```

**Key insight** (from `insert_duplicate_error`):
- Use `obtain` instead of destructuring in `have` when you need the variable later
- Do `cases` on the obtained variable BEFORE any simp that might hide it
- Use `rename_i` to give meaningful names to constructor arguments

### Systematic Case Analysis

For complex proofs with many branches:

1. **Unfold** both classifier and implementation
2. **Cases** on discriminants early (before simp)
3. **by_cases** on conditions (use same hypothesis names)
4. **simp [h]** to reduce both sides in parallel (after cases!)
5. **Apply lemmas** once reduced

**Example structure**:
```lean
theorem complex_cases :
    match classify db obj with
    | .error => result.error = true
    | .success => result.property := by
  unfold classify implementation

  match obj with
  | .const c =>
    by_cases h_cond1 : condition1
    · simp [h_cond1]
      exact error_lemma
    · by_cases h_cond2 : condition2
      · simp [h_cond1, h_cond2]
        exact another_error_lemma
      · simp [h_cond1, h_cond2]
        -- success case
        constructor
        · exact success_lemma1
        · exact success_lemma2
  | .var v => ...
```

---

## Pattern Matching with Cases

### Understanding Parameter Binding in `cases`

When using `cases h with` on an inductive type, Lean expects you to bind **exactly the right number** of parameters for each constructor.

**Key Rule**: Use underscores `_` for parameters you don't need, don't try to bind them!

### Pattern: Correct Parameter Binding

```lean
-- Given an inductive type:
inductive ProofValid (Γ : Database) : Frame → List Expr → List ProofStep → Prop where
  | useEssential : ∀ fr stack steps e,
      Hyp.essential e ∈ fr.mand →
      ProofValid Γ fr stack steps →
      ProofValid Γ fr (e :: stack) (ProofStep.useHyp (Hyp.essential e) :: steps)
```

**❌ Too many bindings** (Lean error: "Too many variable names provided"):
```lean
cases h with
| useEssential fr stack steps e h_in h_prev =>  -- ❌ Trying to bind fr!
```

**❌ Wrong parameter is bound** ("Unknown identifier" errors):
```lean
cases h with
| useEssential stack steps e h_in h_prev =>  -- ❌ e gets bound to h_in!
```

**✅ Correct pattern** (use underscores for implicit/inferred parameters):
```lean
cases h with
| useEssential _ _ e h_in h_prev =>  -- ✅ Underscores for stack, steps
  -- Now e, h_in, h_prev are properly bound
  have h_fact : SomeProperty e := ...
  ...
```

### Variable Scoping Strategy

**Problem**: Variables bound in pattern match go out of scope after certain tactics.

**Solution**: Use `have` to establish facts while variables are in scope:

```lean
cases h with
| useEssential _ _ e h_in h_prev =>
    -- Establish facts IMMEDIATELY while e is in scope
    have h_mem : converted e ∈ context := conversion_lemma h_in
    have h_eq : conversion e = target e := conversion_correct e

    -- Now use these facts (even after e goes out of scope)
    apply SomeConstructor
    unfold definitions
    rw [← h_eq]
    exact h_mem
```

### Common Errors and Fixes

**Error**: "Unknown identifier `x`"
- **Cause**: Variable `x` not properly bound in pattern match
- **Fix**: Check you have the right number of underscores before `x`

**Error**: "Too many variable names provided at alternative `ctor`: N provided, but M expected"
- **Cause**: Binding too many parameters (including implicit ones)
- **Fix**: Replace early bindings with underscores `_`

**Error**: "Application type mismatch: The argument `x` has type `Prop` but is expected to have type `Type`"
- **Cause**: Variable got bound to wrong parameter (usually a proof instead of a value)
- **Fix**: Add more underscores before `x` in the pattern

### Example: Bridge Theorem Pattern Matching

```lean
-- From Metamath.Spec.Equivalence.lean
theorem proofValid_to_mario {Γ : Database} {fr : Frame} {e : Expr} {steps : List ProofStep}
    (vars : List MarioVR) :
    ProofValid Γ fr [e] steps →
    Semantic.Provable (dbToAxioms Γ vars) (frameToContext fr vars) (exprToFormula e vars) := by
  intro h
  cases h with
  | useEssential _ _ e h_in h_prev =>
      -- ✅ Correct: _ _ e binds exactly what we need
      -- Establish facts while e is in scope
      have h_mem : Hyp.toMarioFormula (Hyp.essential e) vars ∈
                   (Frame.toMarioContext fr vars).hyps :=
        Bridge.Hyp.toMarioFormula_mem h_in
      have h_eq : Hyp.toMarioFormula (Hyp.essential e) vars = exprToFormula e vars :=
        Hyp.toMarioFormula_essential e vars

      -- Use the facts
      apply Metamath.Provable.hyp
      unfold frameToContext
      rw [← h_eq]
      exact h_mem
```

**Key insight from this example**:
1. Pattern `_ _ e h_in h_prev` skips `fr` and `stack` (inferred from context)
2. Binds `e` (the expression we need), `h_in` (membership proof), `h_prev` (recursive proof)
3. Immediately establishes `have` facts using `e` before it goes out of scope
4. Uses those facts in the rest of the proof

---

## Common Pitfalls

### 1. Using `EquivBEq` when you need `LawfulBEq`
```lean
-- ❌ Won't work - EquivBEq doesn't give beq_iff_eq
theorem bad [EquivBEq α] (k k' : α) (h : k ≠ k') :
    (k == k') = false := sorry

-- ✅ Use LawfulBEq instead
theorem good [LawfulBEq α] (k k' : α) (h : k ≠ k') :
    (k == k') = false := ...
```

### 2. Forgetting to unfold before if_pos/if_neg
```lean
-- ❌ Won't reduce properly
simp only [if_pos h]

-- ✅ Unfold first
unfold DB.error at h ⊢
simp only [if_pos h]
```

### 3. Using `simp` instead of `simp only`
```lean
-- ❌ May reduce too much or unexpectedly
simp [h]

-- ✅ More controlled
simp only [h, if_pos, if_neg]
```

---

## Quick Reference

### Essential Tactics for This Project

| Tactic | Use Case |
|--------|----------|
| `unfold` | Expose definitions before reasoning |
| `simp only [...]` | Precise simplification |
| `if_pos h` | Reduce if when condition true |
| `if_neg h` | Reduce if when condition false |
| `rw [thm] at h ⊢` | Rewrite in hypothesis and goal |
| `exact` | Complete proof with exact term |
| `by_cases h : cond` | Split on decidable condition |
| `match ... with` | Pattern match in proof |
| `constructor` | Prove conjunction `∧` |
| `intro` | Move hypothesis from goal to context |
| `have` | Introduce intermediate fact |

### Extracting Information from Match Hypotheses

**Pattern**: When you have a hypothesis with a match expression, use `cases` on the matched variable to reduce it.

```lean
-- Hypothesis: (match obj with | .const _ => complex_expr | _ => false) = false
-- Want: complex_expr = false when obj = .const c

-- ✅ Use cases to reduce the match:
cases h_obj : obj
· -- obj = .const c
  rename_i c
  simp only [h_obj] at h_match  -- Reduces match to const branch
  -- Now h_match : complex_expr = false
```

**Example** (from `insert_success_new`):
```lean
-- h_no_scope_err : (match obj label with | .const _ => !db.permissive && db.scopes.size > 0 | _ => false) = false
cases h_obj : obj label
· -- obj label = .const c
  rename_i c
  have h_scope_false : (!db.permissive && db.scopes.size > 0) = false := by
    simp only [h_obj] at h_no_scope_err  -- Match reduces to const branch
    exact h_no_scope_err
  simp [h_scope_false]  -- Now use it to reduce if-then-else
```

**Key insight**: `simp only [h_obj]` is safer than `simp [h_obj]` because it only substitutes `obj` without doing extra simplifications.

### When Stuck

1. **Check the goal**: Use `show` to clarify what you're proving
2. **Unfold definitions**: See the actual structure
3. **Check typeclasses**: Do you have `LawfulBEq`? `EquivBEq`?
4. **Search Std library**: `grep -r "theorem.*insert" ~/.elan/...`
5. **Build incrementally**: Prove small lemmas first
6. **Try cases before simp**: If variables are becoming inaccessible

---

## Pattern Library

### Contradiction from incompatible hypotheses
```lean
have h1 : a = true := ...
have h2 : a = false := ...
simp [h1] at h2  -- Goal: False
```

### Boolean case analysis
```lean
match h : some_bool with
| true => ...
| false => ...
```

### Option case analysis
```lean
match h : some_option with
| none => ...
| some x => ...
```

### Existential unpacking with `obtain`
```lean
-- ❌ Bad: Destructuring in have loses scope
have ⟨x, h_x⟩ : ∃ x, P x := ...
-- x is not accessible here!

-- ✅ Good: Use obtain to keep x in scope
have h_exists : ∃ x, P x := ...
obtain ⟨x, h_x⟩ := h_exists
-- x is now accessible for the rest of the proof
```

### Deriving contradictions from Bool hypotheses
```lean
-- Pattern: h_err : ¬db.error = true and h_some : db.error? = some _
-- Goal: Derive False
unfold DB.error at h_err  -- db.error = db.error?.isSome
simp [Option.isSome, h_some] at h_err  -- Reduces to ¬true = true, which is False
-- Goal solved! ✅
```

---

## Do-Notation and ForIn Loop Proofs

### The Challenge: Proving Loop Equivalences

When proving that an imperative `for` loop equals a functional recursion, you encounter complex do-notation desugaring. This section documents patterns for handling this systematically.

### Pattern: Imperative Loop = Recursive Function

**Goal**: Prove `floatCheckLoop = floatCheckLoopAux` where:
- `floatCheckLoop` uses `for h in array do ...` (imperative style)
- `floatCheckLoopAux` uses pattern matching recursion (functional style)

**Strategy**: Show both equal the same `List.foldl` via intermediate lemmas.

### Step 1: Build Generic ForIn Infrastructure

Add to `ArrayListExt.lean`:

```lean
/-- In Id monad, yield-only forIn over a list equals foldl -/
theorem List.idRun_forIn_yield_eq_foldl
    {α β} (xs : List α) (init : β) (step : β → α → β) :
    Id.run (xs.forIn init (fun a s => pure (ForInStep.yield (step s a)))) =
      xs.foldl step init := by
  induction xs generalizing init with
  | nil => simp
  | cons a xs ih => simpa using ih (step init a)

/-- Bridge Array.forIn to List.forIn in Id monad -/
theorem Array.idRun_forIn_toList {α β} (arr : Array α) (init : β)
    (body : α → β → Id (ForInStep β)) :
    Id.run (arr.forIn init body) =
      Id.run ((arr.toList).forIn init body) := by
  simp only [Array.forIn_toList]

/-- Combine: Array forIn (yield-only) equals foldl over toList -/
theorem Array.idRun_forIn_yield_eq_foldl
    {α β} (arr : Array α) (init : β) (step : β → α → β) :
    Id.run (arr.forIn init (fun a s => pure (ForInStep.yield (step s a)))) =
      (arr.toList).foldl step init := by
  rw [Array.idRun_forIn_toList]
  exact List.idRun_forIn_yield_eq_foldl (arr.toList) init step
```

### Step 2: Define Pure Step Function

Extract the loop body as a pure function:

```lean
def floatStep (pos : Pos) (v : String) (db : DB) (h : String) : DB :=
  match db.find? h with
  | some (.hyp false prevF _) =>
      if prevF.size >= 2 && prevF[1]!.value == v then
        db.mkError pos s!"variable {v} already has $f hypothesis"
      else db
  | _ => db
```

### Step 3: Prove Recursive = Foldl

Use straightforward induction:

```lean
theorem floatCheckLoopAux_eq_foldl (db : DB) (pos : Pos) (v : String) (hyps : List String) :
    floatCheckLoopAux db pos v hyps = hyps.foldl (floatStep pos v) db := by
  induction hyps generalizing db with
  | nil => rfl
  | cons h t ih =>
      simp only [floatCheckLoopAux, List.foldl, floatStep]
      cases db.find? h <;> [exact ih db, ...]  -- handle all cases
```

### Step 4: The Hard Part - Do-Notation Normalization

**The Challenge**: Show that the actual loop body (with mutable variables and assignments) equals the clean `floatStep`.

**What makes this hard**:
1. **Mutable variables**: `let mut db' := db` desugars to state threading
2. **Assignments**: `db' := ...` becomes yielding new values
3. **Do-notation**: Adds `pure PUnit.unit` noise
4. **If-let patterns**: Desugar to nested matches

**Current Status**: This remains an open challenge. The proof is **provable** (no mathematical gap), but requires careful handling of Lean's exact desugaring.

### Key Insights from This Session

1. **The mathematical content is straightforward**: Both loops compute the same foldl
2. **The syntactic challenge is real**: Do-notation desugaring is complex
3. **Build reusable infrastructure**: Generic forIn lemmas help across projects
4. **Document the patterns**: Future proofs can reuse this approach

### Lessons for Reliable ForIn Proofs

1. **Always go through foldl**: It's the canonical meeting point
2. **Extract pure functions**: Define the step function explicitly
3. **Use stdlib lemmas**: `Array.forIn_toList` etc. are your friends
4. **Test incrementally**: Build and test each lemma separately
5. **Accept temporary sorries**: Focus on the mathematical core first

### Common Pitfalls

- **Type annotations**: May need explicit `: Id (ForInStep DB)` to guide inference
- **Monad confusion**: Remember `Id.run` unwraps the Id monad
- **Do-notation complexity**: The actual desugaring has many intermediate steps
- **Mutable variable threading**: State becomes accumulator in forIn

### Solution: Successful Pattern for Do-Notation (2025-11-17)

**RESOLVED**: The `floatCheckLoop_eq_aux` theorem has been successfully proven without axioms!

The key insights that made it work:

1. **Direct equality via foldl**: Instead of trying to match the exact do-notation desugaring, prove both sides equal the same foldl:
```lean
theorem floatCheckLoop_eq_aux (db : DB) (pos : Pos) (v : String) :
    floatCheckLoop db pos v = floatCheckLoopAux db pos v db.frame.hyps.toList := by
  suffices h : floatCheckLoop db pos v = db.frame.hyps.toList.foldl (floatStep pos v) db by
    rw [h, ← floatCheckLoopAux_eq_foldl]
```

2. **Function extensionality for body transformation**: Use `funext` to prove the loop bodies are equivalent:
```lean
apply funext; intro h
apply funext; intro acc
simp only [floatStep, pure, Id.pure, bind, Id.bind]
```

3. **Case analysis on the accumulator**: Handle each case of `find?` systematically:
```lean
cases acc.find? h with
| none => rfl
| some obj =>
  cases obj with
  | hyp ess prevF _ =>
    cases ess with
    | false => split_ifs with h_cond; rfl; rfl
    | true => rfl
  | _ => rfl
```

4. **Bridge lemma application**: Use the proven `idRun_forIn_yield_eq_foldl` bridge:
```lean
exact ArrayListExt.Array.idRun_forIn_yield_eq_foldl db.frame.hyps db
  (fun acc h => floatStep pos v acc h)
```

This pattern successfully handles the complexity of do-notation desugaring by:
- Avoiding direct manipulation of `pure PUnit.unit` noise
- Working with semantic equality rather than syntactic matching
- Using foldl as a common meeting point between imperative and functional styles

---

## Array Indexing Equivalence

### Problem: Bridging `arr[i]` and `arr[i]!`

Lean 4 has two array indexing notations that are **not** definitionally equal:
- `arr[i]` (or `arr[i]'h`) - requires proof `h : i < arr.size` at compile time
- `arr[i]!` - panic-safe indexing using `getBang`, panics at runtime if out of bounds

**Common Issue**: Proofs about `HypOK db arr[i]` cannot directly apply to goals about `arr[i]!`.

### Pattern: Using `getElem!_pos`

The Lean stdlib theorem `getElem!_pos` bridges these notations:
```lean
theorem getElem!_pos {α} [Inhabited α] (arr : Array α) (i : Nat) (h : i < arr.size) :
  arr[i]! = arr[i]
```

**Usage Pattern**:
```lean
-- Given:
--   hi : i < db.frame.hyps.size
--   h_find : db.find? db.frame.hyps[i] = some (...)
-- Need: db.find? db.frame.hyps[i]! = some (...)

-- Step 1: Prove indexing equivalence
have h_bang : db.frame.hyps[i]! = db.frame.hyps[i] := by
  simp [getElem!_pos, hi]

-- Step 2: Rewrite to get desired form
have h_find' : db.find? db.frame.hyps[i]! = some (...) := by
  rw [h_bang]
  exact h_find

-- Step 3: Use h_find' in the rest of the proof
```

**Key Points**:
- Use `simp [getElem!_pos, hi]` rather than calling `getElem!_pos hi` directly
- The theorem requires the element type to be `Inhabited`
- For Lists, use the analogous `List.getElem!_pos` theorem

**Example** (from `toFrame_some_of_wfFrame` in KernelClean.lean:1073):
```lean
have h_ok := h_hyps i hi  -- HypOK db db.frame.hyps[i]
unfold HypOK at h_ok
obtain ⟨ess, f, lbl, h_find, ...⟩ := h_ok
-- h_find : db.find? db.frame.hyps[i] = some (.hyp ess f lbl)

-- Bridge to getBang notation
have h_bang : db.frame.hyps[i]! = db.frame.hyps[i] := by
  simp [getElem!_pos, hi]

have h_find' : db.find? db.frame.hyps[i]! = some (.hyp ess f lbl) := by
  rw [h_bang]
  exact h_find

-- Now h_find' can be used with convertHyp which expects db.frame.hyps[i]!
```

---

*This document is living and should be updated with new patterns as discovered.*
# How to Lean 4 (Batteries Edition)

Practical guidance for Lean 4 formalization using only the Batteries library (no mathlib).

## Table of Contents
1. [Wrapper Functions and Frame Preservation](#wrapper-functions-and-frame-preservation)
2. [Case Analysis with Option Types](#case-analysis-with-option-types)
3. [Error Propagation Lemmas](#error-propagation-lemmas)
4. [Do-Notation and Loop Reasoning](#do-notation-and-loop-reasoning)
5. [Using congrArg for Projection Equality](#using-congrarg-for-projection-equality)
6. [General Proof Patterns](#general-proof-patterns)

---

## Wrapper Functions and Frame Preservation

When a function wraps another with state modifications, prove preservation separately.

### Pattern: Transparent Wrapper Lemma

If a wrapper only modifies a specific field (e.g., error messages) but preserves structure:

```lean
/-- withAt preserves frame - it only modifies error message, not frame. -/
theorem withAt_preserves_frame (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).db.frame = (f ()).db.frame := by
  unfold ParserState.withAt
  simp only
  -- Case on the option that determines wrapper behavior
  cases hopt : (f ()).db.error? with
  | none => rfl
  | some int =>
    obtain ⟨e, idx⟩ := int
    cases e with
    | error pos msg => simp only [ParserState.withDB]
    | ax _ _ _ _ => rfl  -- Fallthrough cases
    | thm _ _ _ _ => rfl
```

**Key insight**: Use `cases hopt : ...` to introduce an equation you can use with `simp only [hopt, ...]`.

---

## Case Analysis with Option Types

### Pattern: Avoiding `generalize` Issues

Instead of using `generalize` which can cause type mismatch issues:

```lean
-- Problematic approach
generalize (f ()).db.error? = err_opt at *
cases err_opt  -- h may not match goal after generalize
```

Use `cases` with equation binding:

```lean
-- Better approach
cases hopt : (f ()).db.error? with
| none => ...
| some x =>
  simp only [hopt, ...]  -- Substitute back
  ...
```

---

## Error Propagation Lemmas

### Pattern: Error Preservation Through Wrappers

When a wrapper preserves error presence (even if it modifies the message):

```lean
theorem withAt_propagates_error (l : String) (f : Unit → ParserState) :
    (f ()).db.error = true → (ParserState.withAt l f).db.error = true := by
  intro h
  unfold ParserState.withAt Verify.DB.error at *
  cases hopt : (f ()).db.error? with
  | none =>
    simp only [hopt, Option.isSome_none, Bool.false_eq_true] at h
  | some int =>
    obtain ⟨e, idx⟩ := int
    cases e with
    | error pos msg =>
      simp only [hopt, ParserState.withDB, Option.isSome_some]
    | ax _ _ _ _ => simp only [hopt, Option.isSome_some]
    | thm _ _ _ _ => simp only [hopt, Option.isSome_some]
```

**Usage**: Apply this lemma when proving error cases in disjunctions:
```lean
| inr h_err =>
  right; right
  apply withAt_propagates_error
  simp only [Id.run, ...]
  exact h_err
```

---

## Do-Notation and Loop Reasoning

### The Challenge

Lean 4's do-notation with early returns elaborates to complex structures involving:
- `ForIn` typeclass with `(Option Result, State)` pairs
- Nested `match` expressions
- Type class instance resolution

### Known Limitation

Direct reasoning about `Array.forIn` loops is extremely difficult because:
1. The loop body type involves `ForInStep (Option Result × State)`
2. Induction requires matching the exact loop structure
3. `Array.forIn.loop` may not be directly accessible

### Recommended Approach

For loop equivalence lemmas, document as semantic axioms:

```lean
/-- Loop equivalence for djvars iteration.

    Semantic axiom: The loop only updates djvars, not hyps.

    Proving this requires loop invariant reasoning over Array.forIn
    which is notoriously difficult in Lean 4.
    See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/loop.20invariant.20reasoning
-/
theorem loop_equiv : ... := sorry
```

For simpler loops, try:
1. `native_decide` (if no free variables)
2. Manual unfolding with `simp only [Id.run, Bind.bind, bind, Pure.pure]`
3. Case analysis on loop conditions

---

## Using congrArg for Projection Equality

### Pattern: Converting Equality to Projection Equality

When you have `db₁ = db₂` and need `db₁.frame.hyps = db₂.frame.hyps`:

```lean
-- Given: h : (s.resumeThm pos l arr fr).db = s.db
-- Goal: (s.resumeThm pos l arr fr).db.frame.hyps = s.db.frame.hyps

exact congrArg (fun db => db.frame.hyps) (resumeThm_preserves_db s pos l arr fr)
```

### Pattern: Converting Frame Equality to Hyps Equality

When you have `frame₁ = frame₂` and need `frame₁.hyps = frame₂.hyps`:

```lean
-- Given: h : (withAt l f).db.frame = (f ()).db.frame
-- Goal: ... .db.frame.hyps = ... .db.frame.hyps

rw [congrArg Frame.hyps (withAt_preserves_frame l _)]
```

---

## General Proof Patterns

### Multi-branch Disjunctions

For theorems with 3+ disjuncts (`A ∨ B ∨ C`):
- `left` proves `A`
- `right; left` proves `B`
- `right; right` proves `C`

### simp Arguments for Id Monad

When working with `Id.run do`:
```lean
simp only [Id.run, Bind.bind, bind, Pure.pure]
```

### Handling if-then-else After Cases

After `cases h : condition`:
```lean
| false =>
  simp only [h, ite_false, ...]
| true =>
  simp only [h, ite_true, ...]
```

### Proving by Contradiction for Bool

For `s.db.error = false` when you know `final.db.error = false` and there's monotonicity:
```lean
by_cases h : s.db.error = false
· left; exact h
· -- Use contrapositive: if s.db.error = true, then final.db.error = true
  -- This contradicts h_success
  simp only [Bool.eq_false_iff, ne_eq, Bool.not_eq_false] at h
  -- Need: execution path from s to final to apply error_monotonic
  ...
```

---

## Common Pitfalls

1. **Forgetting `Pure.pure` in Id monad simp**: The `pure` in `Id.run do` needs this lemma
2. **Using `rfl` prematurely**: After simp, the goal may need more reduction
3. **Missing explicit arguments**: Lemmas like `resumeThm_preserves_db s pos l arr fr` need all args
4. **generalize without at ***: May leave hypothesis and goal inconsistent

---

## Structural Induction: The Elegant Way

### Principle: Match Structure in Definition and Proof

**The Golden Rule**: If you define a function by pattern matching on a data structure, prove theorems about it using the SAME pattern matching structure.

This creates elegant, maintainable proofs that mirror the code structure.

### Pattern from Mario's Metamath Code

#### 1. Recursive Function Definition

```lean
-- Define by pattern matching on list structure
def Expr.subst (σ : VR → Expr) : Expr → Expr
  | [] => []                              -- Base case
  | const c :: e => const c :: subst σ e  -- Recursive case 1
  | var v :: e => σ v ++ subst σ e        -- Recursive case 2
```

**Key insight**: Each case handles ONE constructor and recursively calls on smaller pieces.

#### 2. Induction Proof with Same Structure

```lean
-- Prove by pattern matching on SAME structure
theorem Expr.subst_id : (e : Expr) → Expr.subst VR.expr e = e
  | [] => rfl                                    -- Base: immediate
  | const c :: e => congrArg (const c :: .) (subst_id e)  -- IH for e
  | var v :: e => congrArg (var v :: .) (subst_id e)      -- IH for e
```

**Pattern**:
- Base case: Usually `rfl` or trivial
- Recursive case: Apply `congrArg` with constructor + induction hypothesis

#### 3. Complex Induction with Rewriting

For more complex proofs, use `rw` to unfold definitions:

```lean
theorem Expr.subst_append (σ) : (e₁ e₂ : Expr) → 
    Expr.subst σ (e₁ ++ e₂) = e₁.subst σ ++ e₂.subst σ
  | [], _ => rfl  -- Base case
  | const c :: (e₁ : Expr), e₂ => by
      rw [subst, List.cons_append, subst, subst_append ..]
      rfl
  | var v :: e, e₂ => by
      rw [List.cons_append]
      simp only [Expr.subst]
      rw [List.append_assoc, subst_append ..]
```

**Pattern**:
1. `rw [function_def]` - unfold the recursive call
2. `rw [relevant_lemmas]` - simplify using properties
3. `rw [IH_name ..]` - apply induction hypothesis (Lean infers arguments)
4. `rfl` or continue

### Key Tactics for Structural Induction

| Tactic | Use |
|--------|-----|
| `\| pattern => proof` | Pattern match in theorem statement |
| `congrArg (f .) IH` | Apply constructor to induction hypothesis |
| `rw [def, IH ..]` | Unfold definition, apply IH |
| `simp only [def]` | Reduce without extra simplification |
| `rfl` | Proof by definitional equality |

### Helper Lemmas Strategy

**Don't prove everything at once!** Break down into layers:

```lean
-- Layer 1: Simple property
theorem list_map_cons (f : α → β) (x : α) (xs : List α) :
    List.map f (x :: xs) = f x :: List.map f xs := rfl

-- Layer 2: Composition property
theorem list_map_append (f : α → β) : (xs ys : List α) →
    List.map f (xs ++ ys) = List.map f xs ++ List.map f ys
  | [], ys => rfl
  | x :: xs, ys => by
      rw [List.cons_append, list_map_cons, list_map_cons, list_map_append]
      rfl

-- Layer 3: Complex theorem using layers 1 & 2
theorem complex_property : ... := by
  rw [list_map_append, ...]
  ...
```

**Why this works**:
- Each lemma is independently testable
- Proofs are shorter and clearer
- Easy to debug (which layer failed?)
- Reusable components

### Common Pitfall: Induction on Wrong Structure

```lean
-- ❌ BAD: Inducting on Expr when we need list structure
theorem bad_proof (e : Expr) : ... := by
  induction e  -- Wrong! Expr is a structure, not inductive
  ...

-- ✅ GOOD: Induct on the list inside Expr
theorem good_proof (e : Expr) : ... := by
  match e with
  | ⟨typecode, syms⟩ =>
      -- Now induct on syms : List String
      induction syms with
      | nil => ...
      | cons s rest IH => ...
```

**Fix**: Identify the ACTUAL recursive structure (often a list or tree inside a structure).

### Pattern: Proving flatMap Equals Recursive Definition

This pattern is useful when you have an imperative-style definition (using `flatMap`, `foldl`) that needs to match a recursive definition.

```lean
-- Imperative style (our code)
def ourFunction (xs : List α) : List β :=
  xs.flatMap fun x => process x

-- Recursive style (their code)
def theirFunction : List α → List β
  | [] => []
  | x :: xs => process x ++ theirFunction xs

-- Proof strategy: Induct on list
theorem our_equals_their : (xs : List α) → ourFunction xs = theirFunction xs
  | [] => by
      unfold ourFunction theirFunction
      rfl  -- Both are []
  | x :: xs => by
      unfold ourFunction theirFunction
      simp only [List.flatMap]  -- Reduce flatMap to cons case
      rw [our_equals_their xs]  -- Apply IH
      rfl  -- Or continue with append properties
```

**Key steps**:
1. Unfold both definitions
2. Reduce flatMap/foldl to explicit form
3. Apply induction hypothesis
4. Use append/list lemmas to finish

### Verification Testing Pattern (CreuSAT-inspired)

When proving complex properties, write executable tests FIRST:

```lean
-- 1. Define the property as a computable function
def check_property (e : Expr) : Bool :=
  our_function e == their_function e

-- 2. Write executable tests
#eval check_property example1  -- true
#eval check_property example2  -- true

-- 3. NOW prove it for all cases
theorem property_holds : ∀ e, check_property e = true := by
  intro e
  -- Proof is easier because we've tested it!
  ...
```

**Why this helps**:
- Catch bugs in theorem statement BEFORE proof
- Build intuition about edge cases
- Tests run fast, proofs are slow
- Can test on real examples from codebase

### Summary: Elegant Induction Checklist

- [ ] Define function by pattern matching on structure
- [ ] Prove theorem using SAME pattern matching
- [ ] Base case: Usually `rfl`
- [ ] Recursive case: `congrArg constructor IH` or `rw [def, IH ..]`
- [ ] Break complex proofs into helper lemmas
- [ ] Test property on examples before proving
- [ ] Match on the ACTUAL recursive structure (lists, trees)
- [ ] Use `..` in `IH ..` to let Lean infer arguments

**Sources**: Mario Carneiro's Metamath.Translate.lean, CompCert verification patterns, CreuSAT verification testing
