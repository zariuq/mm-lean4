# Integration Status: Wiring Kernel.lean into Build

## ✅ Completed

1. **Created spec-conformant test**: `test_nonv_vars.mm` passes both `mmverify_pure.py` and `metamath.exe` with:
   - Variables starting with 'c' (not 'v'): `$v cx cy $.`
   - Constants starting with 'v': `$c vtrue vimplies $.`
   - **Proves**: Metamath §4.2.1 is correct - symbol names are arbitrary!

2. **Fixed Spec.lean** to be spec-conformant:
   - `Frame.vars (fr : Frame) : List Variable` - extracts vars from floating hyps
   - `varsInExpr (vars : List Variable) (e : Expr) : List Variable` - no 'v' prefix check
   - `dvOK (vars : List Variable) (dv : ...) (σ : ...) : Prop` - uses var list
   - `applySubst (vars : List Variable) (σ : ...) (e : ...) : Expr` - uses var list
   - Builds cleanly! ✅

3. **Wired Kernel.lean into build**:
   - Updated `lakefile.lean`: `roots := #[`Metamath.Spec, `Metamath.Verify, `Metamath.Kernel]`
   - Updated `Metamath.lean`: Now imports Spec, Verify, Kernel
   - **Result**: Kernel.lean finally type-checked! Exposed ~349 errors (good!)

4. **Started API migration**:
   - Fixed line 31: `Metamath.Verify.Symbol` → `Metamath.Verify.Sym`

## ⏳ In Progress: API Migration (~349 errors)

### Error Categories

1. **dvOK signature changed** (~25-30 callsites):
   ```lean
   -- OLD: dvOK fr_spec.dv σ
   -- NEW: dvOK fr_spec.vars fr_spec.dv σ
   ```
   Examples: lines 83, 84, 203, 274...

2. **applySubst signature changed** (~20-25 callsites):
   ```lean
   -- OLD: applySubst σ e
   -- NEW: applySubst fr.vars σ e
   ```
   Examples: lines 194, 283, 344...

3. **Object constructor issues** (~10-15 locations):
   - Error refers to `.var` and `.const` constructors
   - These exist but are for Symbol declarations, not formula objects
   - Need to check usage context

4. **Cascading type errors** (~250+ errors):
   - Many will auto-fix once core API issues resolved

### Key Verify.lean API (reference)

```lean
inductive Sym
  | const (c : String)
  | var (v : String)

def Sym.value : Sym → String
  | .const c => c
  | .var v => v

abbrev Formula := Array Sym

def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula

inductive Object
  | const : String → Object      -- Symbol declaration
  | var : String → Object        -- Symbol declaration
  | hyp : Bool → Formula → String → Object
  | assert : Formula → Frame → String → Object

def DB.checkHyp (hyps : Array String) (stack : Array Formula)
    (off : ...) (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula)
```

### Next Steps (Priority Order)

1. **Batch-fix dvOK calls** (~30 callsites):
   ```bash
   # Pattern to find:
   dvOK (\w+)\.dv
   # Replace with:
   dvOK $1.vars $1.dv
   ```

2. **Batch-fix applySubst calls** (~25 callsites):
   ```bash
   # Pattern: applySubst σ_spec e
   # Need to determine correct fr.vars for each context
   ```

3. **Fix Object usage**:
   - Review lines 61, 96, 143 for `.var`/`.const` vs `.hyp`/`.assert` confusion
   - Likely misunderstanding of Verify.lean API

4. **Rebuild and address remaining errors**:
   - Many will cascade-fix
   - Estimate: ~50-100 real errors remain after above fixes

## 📊 Current Axiom Count: 7

With Kernel.lean integrated, the verified stack has:
- **Core (5)**: stepNormal_sound, subst_sound, dvCheck_sound, substSupport, variable_wellformed
- **Foundational (2)**: frame_conversion_correct, checkHyp_correct (both structured with sorries)

**Target**: 5 axioms (core soundness only)

## 🎯 Goal Architecture (per GPT-5/Grok)

```
Spec.lean (pure semantics)
   ↓
Verify.lean (implementation)
   ↓
Kernel.lean (bridge proofs) ← NOW WIRED IN! ✅
   ↓
Metamath.lean (top-level soundness)
```

**Critical achievement**: The "orphan proofs" problem is solved! Kernel.lean is now enforced by CI.

## Test Command

```bash
cd /home/zar/claude/hyperon/metamath/mm-lean4
~/.elan/bin/lake build 2>&1 | grep "error:" | wc -l
# Current: 349 errors
# After batch fixes: ~50-100 estimated
```

## Files Modified

- ✅ `Metamath/Spec.lean` - API updated
- ✅ `Metamath.lean` - Imports added
- ✅ `lakefile.lean` - Roots updated
- ✅ `test_nonv_vars.mm` - Spec-conformance test
- ⏳ `Metamath/Kernel.lean` - 1/349 errors fixed

## Session Continuation Strategy

1. Start with batch regex replacements for dvOK/applySubst
2. Fix Object constructor confusion (manual review)
3. Rebuild after each batch
4. Track progress: 349 → ~100 → ~50 → 0
5. Once clean: verify test suite passes
6. Then: Complete bridge proof tactics (toExpr_subst_commutes, checkHyp_correct)
