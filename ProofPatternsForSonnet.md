# Proof Patterns Guide for Sonnet 4.5

This guide provides systematic patterns for completing the proofs in the Metamath verifier.

## 🎯 Priority Order for Completing Proofs

### Phase 1: Eliminate HashMap Axioms (High Impact)
1. **Use `HashMapLemmas.lean`** - Replace axioms in `ParserCorrectness.lean`:
   ```lean
   -- REPLACE: axiom HashMap.find?_insert_eq
   -- WITH: theorem from HashMapLemmas.HashMap.find?_insert_self
   ```

2. **Pattern**: Most HashMap proofs follow:
   ```lean
   intro h_no_error h_not_found
   unfold DB.insert DB.find?
   simp [HashMap.find?_insert_self, HashMap.find?_insert_other]
   ```

### Phase 2: Parser Loop Properties (Critical Path)
Located in `ParserCorrectness.lean`, lines 89-164.

#### Pattern for `insert_respects_error` (line 90):
```lean
theorem insert_respects_error ... := by
  intro h
  unfold DB.insert
  -- Split on obj type
  cases obj label with
  | const _ =>
    simp [h]
    split <;> simp [h]  -- Handles scope check
  | var _ =>
    simp [h]
  | hyp _ _ _ =>
    simp [h]
  | assert _ _ _ =>
    simp [h]
```

#### Pattern for `parser_stops_on_error` (line 119):
```lean
-- Use ParserLoopInduction.feed_stops_on_error
-- Key insight: Once error occurs, feed returns immediately (Verify.lean:777-779)
theorem parser_stops_on_error ... := by
  intro ⟨step, h_step_in, intermediate_db, h_step_err⟩
  -- Use induction on the list tail after the error
  induction parsing_steps with
  | nil => simp at h_step_in
  | cons hd tl ih =>
    sorry -- Apply feed_stops_on_error from ParserLoopInduction
```

### Phase 3: checkHyp Recursion (Complex but Systematic)

Located in `KernelClean.lean`, line 1442.

#### Pattern for `checkHyp_operational_semantics`:
```lean
theorem checkHyp_operational_semantics ... := by
  intro h_success
  -- Strong induction on hyps.size
  induction hyps.size using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi
    -- Case split on hyps[i]
    match h_find : db.find? hyps[i] with
    | none => contradiction  -- Can't happen if checkHyp succeeded
    | some (.hyp false f lbl) =>
      -- Float case: use FloatReq_of_insert_self
      apply FloatReq_of_insert_self
      sorry -- Fill in arguments
    | some (.hyp true f lbl) =>
      -- Essential case: recurse with same σ
      sorry
    | some _ => contradiction
```

## 🔧 Common Proof Techniques

### 1. Error State Reasoning
```lean
-- When proving error is preserved:
by_cases h : db.error = true
· simp [h]  -- Error case: operation returns immediately
· -- No error case: do actual proof
```

### 2. HashMap/Find Reasoning
```lean
-- After insert, we can find:
have h1 := HashMap.find?_insert_self m k v
-- Other keys unaffected:
have h2 := HashMap.find?_insert_other m k k' v h_ne
```

### 3. Formula Structure
```lean
-- Floats have size 2:
have h_sz : f.size = 2 := by sorry
-- Extract components:
have ⟨c, v, h0, h1⟩ : ∃ c v, f[0]! = .const c ∧ f[1]! = .var v := by
  use (match f[0]! with | .const c => c | _ => ""),
      (match f[1]! with | .var v => v | _ => "")
  sorry
```

### 4. Frame/Hypothesis Iteration
```lean
-- Pattern for iterating through hyps:
for h in db.frame.hyps do
  match db.find? h with
  | some (.hyp false f _) => -- Float
  | some (.hyp true f _) => -- Essential
  | _ => continue
```

## 📊 Statistics & Impact

Current sorry count by file:
- `KernelClean.lean`: ~15 sorries (HIGH IMPACT - main soundness theorem)
- `ParserCorrectness.lean`: 10 sorries (CRITICAL - parser correctness)
- `HashMapLemmas.lean`: 4 sorries (FOUNDATIONAL - eliminates axioms)
- `ParserLoopInduction.lean`: 6 sorries (ENABLING - unblocks parser proofs)

**Recommended attack order**:
1. Complete HashMap lemmas (unblocks many proofs)
2. Prove `parser_stops_on_error` (critical for soundness)
3. Complete `checkHyp_operational_semantics` (enables float validation)
4. Fill remaining mechanical proofs

## 🚀 Quick Wins for Sonnet

These proofs are mechanical and can be completed quickly:

1. **`mkError_creates_error`** (ParserCorrectness.lean:167)
   ```lean
   unfold DB.mkError DB.error
   simp
   ```

2. **`error_short_circuit`** (ParserCorrectness.lean:138)
   ```lean
   intro h
   simp [h]
   ```

3. **`insert_findable`** (ParserCorrectness.lean:151)
   ```lean
   intro h_no_err h_not_found
   unfold DB.insert DB.find?
   -- Use HashMap lemmas
   sorry
   ```

## 🎓 Key Insights for Success

1. **Error handling is "sticky but not global"**: Operations that CHECK error respect it, but some operations (withFrame, withHyps) can modify errored DBs.

2. **Parser stops on first error**: This is THE KEY property that makes everything sound. Even if there are temporary inconsistencies, they're never used.

3. **Float uniqueness is checked during insertHyp**: Lines 303-307 in Verify.lean contain the critical check.

4. **HashMap is the foundation**: Most DB operations reduce to HashMap operations. Complete these first.

5. **Well-formedness is compositional**: Build from WellFormedFormula → WellFormedFrame → WellFormedDB.

## 🔍 Debugging Tips

When stuck on a proof:
1. Add `trace` messages to see the goal state
2. Use `#print` to see definitions
3. Try `simp?` to see what simp rules apply
4. Use `apply?` to find applicable theorems
5. Check if there's a similar proven theorem nearby

## 📚 References

Key files to study:
- `Verify.lean`: Lines 277-310 (insert), 401-418 (checkHyp), 762-790 (feed)
- `WellFormedness.lean`: All definitions are proven requirements
- `ParserBasics.lean`: Simple proofs to use as templates
- `KernelClean.lean`: Lines 1300-1450 (float validation architecture)