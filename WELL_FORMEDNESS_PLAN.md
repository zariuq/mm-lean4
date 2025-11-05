# Plan: Obtaining Well-Formedness Conditions for assert_step_ok

## Current Situation

In `assert_step_ok` (lines 2052-2056), we need to prove:
```lean
have ⟨σ_typed, h_typed⟩ : ∃ (σ_typed : Bridge.TypedSubst fr_assert),
  toSubstTyped fr_assert σ_impl = some σ_typed := by sorry
```

To eliminate this sorry, we need to call `checkHyp_produces_TypedSubst` (lines 1660-1675):
```lean
theorem checkHyp_produces_TypedSubst
  (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (WF : HypsWellFormed db hyps)              -- ← NEED THIS
  (FWS : FloatsWellStructured db hyps stack off)  -- ← AND THIS
  (σ_impl : Std.HashMap String Verify.Formula)
  (fr_spec : Spec.Frame) :
  Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ_impl →
  toFrame db (Verify.Frame.mk #[] hyps) = some fr_spec →
  ∃ (σ_typed : Bridge.TypedSubst fr_spec),
    toSubstTyped fr_spec σ_impl = some σ_typed
```

## What We Have Available

In `assert_step_ok`, we have:
- `inv : ProofStateInv db pr Γ fr_spec stack_spec` - gives us `db_ok`, `frame_ok`, `stack_ok`
- `h_chk : Verify.DB.checkHyp db fr_impl.hyps pr.stack ⟨off, h_off⟩ 0 ∅ = .ok σ_impl`
- `h_fr_assert : toFrame db fr_impl = some fr_assert`
- `db : Verify.DB`, `pr : Verify.ProofState` - the implementation state

## What We Need

Two well-formedness predicates (defined lines 1147-1214):

### 1. HypsWellFormed (line 1147)
```lean
def HypsWellFormed (db : Verify.DB) (hyps : Array String) : Prop :=
  ∀ (i : Nat) (hi : i < hyps.size),
    ∃ (o : Verify.Object), db.find? hyps[i]! = some o ∧ IsHyp o
```

**Meaning**: Every label in `hyps` points to a `.hyp` object (not `.const`, `.var`, or `.assert`)

### 2. FloatsWellStructured (line 1199)
```lean
def FloatsWellStructured (db : Verify.DB) (hyps : Array String)
    (stack : Array Verify.Formula) (off : {off : Nat // off + hyps.size = stack.size}) : Prop :=
  ∀ (i : Nat) (hi : i < hyps.size) (f : Verify.Formula) (lbl : String),
    db.find? hyps[i]! = some (.hyp false f lbl) →
    ∃ (c v : String),
      f.size = 2 ∧
      f[0]! = Verify.Sym.const c ∧
      f[1]! = Verify.Sym.var v ∧
      stack[off.val + i]!.size > 0 ∧
      (toExpr stack[off.val + i]!).typecode = ⟨c⟩ ∧
      (∀ j, j < i → ...) -- No duplicate float variables
```

**Meaning**: Floating hypotheses have the expected structure (`$f c v`) and the stack has matching formulas with correct typecodes

## Three Approaches to Get These Conditions

### Approach 1: Add to ProofStateInv (CLEANEST)

**Idea**: The invariant already tracks that the implementation state relates to spec state. We should ALSO track that the database and frame are well-formed.

**Change**: Extend `ProofStateInv` structure (line 527):
```lean
structure ProofStateInv (db : Verify.DB) (pr_impl : Verify.ProofState)
    (Γ : Spec.Database) (fr_spec : Spec.Frame) (stack_spec : List Spec.Expr) : Prop where
  db_ok : toDatabase db = some Γ
  frame_ok : toFrame db pr_impl.frame = some fr_spec
  stack_ok : viewStack pr_impl.stack = stack_spec
  -- NEW:
  frame_wf : HypsWellFormed db pr_impl.frame.hyps  -- ← Frame hyps are valid
```

**Problem**: We need `FloatsWellStructured` which depends on the CURRENT STACK, not just the frame. For assertions, we need to check `FloatsWellStructured db fr_impl.hyps pr.stack off`, not the current frame's hyps.

**Refined approach**: Add DB-level well-formedness:
```lean
structure ProofStateInv ... where
  ...
  db_wf : DBWellFormed db  -- ← All frames in DB have well-formed hyps
```

Where `DBWellFormed` is:
```lean
def DBWellFormed (db : Verify.DB) : Prop :=
  ∀ label obj, db.find? label = some obj →
    match obj with
    | .assert f fr _ => HypsWellFormed db fr.hyps
    | .hyp _ _ _ => True  -- Hyps are trivially well-formed
    | _ => True
```

**Then in assert_step_ok**: Extract `HypsWellFormed db fr_impl.hyps` from `db_wf` and `h_find`.

**For FloatsWellStructured**: This is harder - it depends on the runtime stack. We'd need to prove it holds at the moment we call `stepAssert`.

### Approach 2: Axiomatize (PRAGMATIC)

**Idea**: These are "obviously true" properties of valid Metamath databases. Real databases satisfy them by construction (the parser validates structure).

**Change**: Add axioms at call site in `assert_step_ok`:
```lean
-- Assume well-formedness (these follow from DB validity in practice)
axiom wf_hyps : HypsWellFormed db fr_impl.hyps
axiom wf_floats : FloatsWellStructured db fr_impl.hyps pr.stack ⟨off, h_off⟩

-- Now call checkHyp_produces_TypedSubst with the axioms
have ⟨σ_typed, h_typed⟩ :=
  checkHyp_produces_TypedSubst db fr_impl.hyps pr.stack ⟨off, h_off⟩
    wf_hyps wf_floats σ_impl fr_assert h_chk h_fr_assert
```

**Pros**:
- Immediate solution
- These ARE true for valid databases
- Parser proofs (ParserInvariants.lean) could eventually eliminate these axioms

**Cons**:
- Adds 2 axioms to the kernel soundness proof
- Less satisfying than proving from invariants

### Approach 3: Prove from checkHyp Success (CLEVER)

**Idea**: The fact that `checkHyp` SUCCEEDED already implies these conditions hold! If the database were malformed, `checkHyp` would have thrown an error.

**Theorems to prove**:
```lean
theorem checkHyp_success_implies_wf
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ_impl : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ_impl →
    HypsWellFormed db hyps := by
  -- If checkHyp succeeded, it must have looked up each hyps[i]
  -- and found a .hyp object (otherwise it would have hit unreachable!)
  sorry

theorem checkHyp_success_implies_floats_structured
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ_impl : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ_impl →
    FloatsWellStructured db hyps stack off := by
  -- If checkHyp succeeded on float i, it checked f[0]! == val[0]!
  -- which implies f.size ≥ 1, val.size ≥ 1, and typecodes match
  sorry
```

**Pros**:
- No axioms needed
- Exploits the fact that runtime checks enforce well-formedness
- Very satisfying philosophically

**Cons**:
- Requires proving properties of `checkHyp`'s implementation
- Medium complexity (30-50 lines per theorem)
- Needs to reason about the recursive structure of `checkHyp`

## Recommendation

**Immediate (Today)**: Use **Approach 2** (axiomatize) to unblock progress
- This is honest: these properties DO hold for valid databases
- Gets us to a working proof quickly
- Clearly marks what needs to be eliminated

**Short-term (Next Session)**: Pursue **Approach 3** (prove from checkHyp success)
- Most elegant solution
- Eliminates the axioms
- Relatively tractable (~50-100 LoC total)

**Long-term (Future)**: Connect to **Approach 1** via parser proofs
- ParserInvariants.lean already has structure for this
- Parser validation → DBWellFormed → HypsWellFormed
- Most complete but non-critical for kernel soundness

## Implementation Steps (Approach 2 - Immediate)

1. **Add axioms in assert_step_ok** (lines ~2053):
```lean
-- Well-formedness axioms (TODO: eliminate via checkHyp_success_implies_*)
axiom assert_hyps_wf : HypsWellFormed db fr_impl.hyps
axiom assert_floats_wf : FloatsWellStructured db fr_impl.hyps pr.stack ⟨off, h_off⟩
```

2. **Call checkHyp_produces_TypedSubst** (replace line 2056 sorry):
```lean
have ⟨σ_typed, h_typed⟩ : ∃ (σ_typed : Bridge.TypedSubst fr_assert),
    toSubstTyped fr_assert σ_impl = some σ_typed := by
  -- Build the frame for checkHyp_produces_TypedSubst
  have h_fr_mk : toFrame db (Verify.Frame.mk #[] fr_impl.hyps) = some fr_assert := by
    -- fr_impl = Verify.Frame.mk dv hyps
    -- Need: toFrame db (Frame.mk #[] hyps) = toFrame db (Frame.mk dv hyps)
    -- This should be true since toFrame only looks at hyps, not dv
    sorry  -- TODO: prove toFrame ignores dv field
  exact checkHyp_produces_TypedSubst db fr_impl.hyps pr.stack ⟨off, h_off⟩
    assert_hyps_wf assert_floats_wf σ_impl fr_assert h_chk h_fr_mk
```

3. **Document axioms** at the top of the file in the axiom status section

## Elimination Path (Approach 3 - Future)

The axioms can be eliminated by proving:

**File**: `Metamath/KernelClean.lean` (add after line 1675)

```lean
/-- When checkHyp succeeds, all hypothesis lookups must have succeeded,
    implying all labels point to .hyp objects. -/
theorem checkHyp_success_implies_HypsWellFormed
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ →
    HypsWellFormed db hyps := by
  intro h_ok
  unfold HypsWellFormed IsHyp
  intro i hi
  -- Proof by strong induction on checkHyp's recursion
  -- Key: if checkHyp reached index i, it must have successfully looked up hyps[i]
  -- and matched on `.hyp ess f lbl` (otherwise would have hit unreachable!)
  sorry

/-- When checkHyp succeeds, all float checks must have passed,
    implying floating hypotheses have the expected structure. -/
theorem checkHyp_success_implies_FloatsWellStructured
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ →
    FloatsWellStructured db hyps stack off := by
  intro h_ok
  unfold FloatsWellStructured
  intro i hi f lbl h_find
  -- Proof by induction on checkHyp's recursion
  -- Key: if checkHyp succeeded at float i, it checked f[0]! == stack[off+i][0]!
  -- This implies both have size ≥ 1 and the first elements match (typecode check)
  sorry
```

**Proof strategy**:
- Use strong induction on the recursion depth
- At each step, checkHyp either:
  - Finds a .hyp object and processes it (proving WF for that index)
  - Or throws an error (contradicts success hypothesis)
- The typecode check `f[0]! == val[0]!` implies both arrays have size ≥ 1
- The successful update `subst.insert f[1]!.value val` implies f has size ≥ 2

## Summary

**Today**: Add 2 axioms (Approach 2) to unblock `assert_step_ok` completion
**Tomorrow**: Prove the checkHyp implications (Approach 3) to eliminate the axioms
**Future**: Connect to parser validation (Approach 1) for completeness

The axioms are honest about what properties valid Metamath databases have, and there's a clear path to eliminating them.
