# Weak Formulations Audit - Mario Would Facepalm! 🤦

**Discovery**: Multiple places use unnecessarily WEAK "membership" formulations when STRONG "ordered conversion" is available.

---

## The Pattern

**WEAK** (what we're doing):
```lean
∀ i < arr.size, ∃ e, toExpr arr[i] = some e ∧ e ∈ list
```
Says: "each array element converts to SOMETHING in the list" (membership only)

**STRONG** (what we should use):
```lean
arr.toList.mapM toExpr = some list
```
Says: "array converts to list IN ORDER" (determines the list uniquely!)

---

## Found Issues

### 1. **ProofStateInv Has TWO Definitions!**

**GOOD version** (line 2252 - 4 parameters):
```lean
structure ProofStateInv (db) (pr) (fr_spec : Frame) (stack_spec : List Expr) : Prop where
  state_ok : viewState db pr = some (fr_spec, stack_spec)
  stack_len_ok : pr.stack.size = stack_spec.length
```
Uses `viewState` which does `viewStack` which does `stk.toList.mapM toExpr` ✅

**WEAK version** (line 2427 - 2 parameters):
```lean
structure ProofStateInv (db) (pr) : Prop where
  frame_converts : ∃ fr_spec, toFrame db pr.frame = some fr_spec
  stack_converts : ∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e
```
Uses indexed membership ❌

**Problem**: Both coexist (different arities), but we use the WEAK one!

---

### 2. **proof_state_has_inv Axiom Returns WEAK Version**

```lean
axiom proof_state_has_inv (db) (pr) (WFdb : WF db) :
  ProofStateInv db pr  -- Returns the 2-param WEAK version!
```

**Should be**:
```lean
axiom proof_state_has_inv (db) (pr) (WFdb : WF db) :
  ∃ fr_spec stack_spec, ProofStateInv db pr fr_spec stack_spec  -- 4-param STRONG version!
```

---

### 3. **build_spec_stack Axiom Is UNNECESSARY**

```lean
axiom build_spec_stack (db) (pr) (pr_inv : ProofStateInv db pr) :
  ∃ stack : List Expr,
    (∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack)
```

**This is already in the strong ProofStateInv!**

If `pr_inv : ProofStateInv db pr fr_spec stack_spec`, then:
- `pr_inv.state_ok : viewState db pr = some (fr_spec, stack_spec)`
- `viewState` unpacks to `viewStack db pr.stack = some stack_spec`
- `viewStack` does `pr.stack.toList.mapM toExpr`

**So `stack_spec` IS the ordered conversion! No axiom needed!**

---

### 4. **Group E Theorems Use Weak Premises**

**Current** (line 1820):
```lean
(∀ i < pr.stack.size, ∃ e, toExpr pr.stack[i] = some e ∧ e ∈ stack_before) →
```

**Should be**:
```lean
pr.stack.toList.mapM toExpr = some stack_before →
```

We already FIXED this conceptually by using `array_mapM_succeeds` to extract the ordered list, but the formulation still uses the weak version as input!

---

### 5. **Other Weak Formulations**

Found at lines: 1333, 1338, 1537, 1540, 2453, 2456, 2530

All use pattern: `∃ e, toExpr arr[i] = some e ∧ e ∈ list`

---

## The Fix

### Phase 1: Unify ProofStateInv

1. **Delete the weak 2-param version** (line 2427-2429)
2. **Keep only the strong 4-param version** (line 2252-2255)
3. **Update proof_state_has_inv** to return the strong version:
   ```lean
   axiom proof_state_has_inv (db) (pr) (WFdb : WF db) :
     ∃ fr_spec stack_spec, ProofStateInv db pr fr_spec stack_spec
   ```

### Phase 2: Delete build_spec_stack

The axiom becomes a trivial extraction:
```lean
theorem build_spec_stack (db) (pr)
    (pr_inv : ProofStateInv db pr fr_spec stack_spec) :
  viewStack db pr.stack = some stack_spec := by
  exact pr_inv.state_ok.2  -- Just extract from viewState
```

Or even simpler - just use `stack_spec` directly from the invariant!

### Phase 3: Strengthen All Theorems

Replace weak formulations:
```lean
-- OLD:
(∀ i < arr.size, ∃ e, toExpr arr[i] = some e ∧ e ∈ list) →

-- NEW:
arr.toList.mapM toExpr = some list →
```

---

## Impact

### Axioms Eliminated: **1** (build_spec_stack)

### Formulations Strengthened: **8+**
- proof_state_has_inv return type
- stack_shape_from_checkHyp premise
- stack_after_stepAssert premise
- stack_push_correspondence
- stack_shrink_correct
- And more...

### Conceptual Clarity: **HUGE**

Using `mapM` everywhere makes it crystal clear:
- Array operations correspond to List operations IN ORDER
- No confusion about membership vs. ordering
- Direct connection to viewStack/viewState

---

## Why This Happened

I was thinking:
> "Indexed facts give membership, need Choice to extract list"

But actually:
> "Indexed facts DETERMINE the ordered list via mapM - just extract it!"

The `array_mapM_succeeds` lemma I proved (line 2141) does exactly this!

---

## Mario's Reaction

```
🤦 "You had the strong property all along!
    ProofStateInv.state_ok gives you viewState
    which gives you viewStack
    which gives you mapM
    which gives you THE ORDERED LIST!

    And you added an AXIOM to 'extract' what you already had?!"
```

---

## Next Steps

1. **Immediate**: Delete weak ProofStateInv, update proof_state_has_inv
2. **Quick win**: Convert build_spec_stack axiom → trivial theorem
3. **Systematic**: Replace all weak formulations with mapM
4. **Result**: -1 axiom, +clarity, +strength

**Time estimate**: 1-2 hours for complete cleanup

---

## The Lesson

**Always ask**: "Do my indexed facts determine more than just membership?"

If `∀ i, f(arr[i])` gives you something, chances are `arr.mapM f` gives you the ORDERED VERSION!

Don't weaken to membership when you can have order! 🎯
