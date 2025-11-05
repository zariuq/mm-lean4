# API Migration Guide: Spec.lean Conformance

## Summary

Spec.lean now passes variable sets explicitly (spec §4.2.1: "symbol names are arbitrary").

## Required Changes

### 1. dvOK Signature Change

**OLD API**:
```lean
def dvOK (dv : List (Variable × Variable)) (σ : Subst) : Prop
```

**NEW API**:
```lean
def dvOK (vars : List Variable) (dv : List (Variable × Variable)) (σ : Subst) : Prop
```

**Migration Pattern**:
```lean
-- Before:
dvOK fr_spec.dv σ

-- After:
dvOK fr_spec.vars fr_spec.dv σ
```

**Special Cases**:
```lean
-- Empty DV list:
dvOK [] σ  →  dvOK [] [] σ  -- or dvOK vars [] σ if vars known

-- Single constraint:
dvOK [(v, w)] σ  →  dvOK vars [(v, w)] σ
```

### 2. applySubst Signature Change

**OLD API**:
```lean
def applySubst (σ : Subst) (e : Expr) : Expr
```

**NEW API**:
```lean
def applySubst (vars : List Variable) (σ : Subst) (e : Expr) : Expr
```

**Migration Pattern**:
```lean
-- Before:
applySubst σ_spec e

-- After:
applySubst fr.vars σ_spec e

-- In ProofValid.useAxiom (line 172 in Spec.lean):
applySubst fr'.vars σ e  -- use callee's vars for result
```

### 3. varsInExpr Signature Change

**OLD API**:
```lean
def varsInExpr (e : Expr) : List Variable  -- checks 'v' prefix
```

**NEW API**:
```lean
def varsInExpr (vars : List Variable) (e : Expr) : List Variable
```

**Migration**:
```lean
-- Before:
varsInExpr e

-- After:
varsInExpr fr.vars e
```

### 4. Frame.vars Helper

**NEW**:
```lean
def Frame.vars (fr : Frame) : List Variable :=
  fr.mand.filterMap fun h => match h with
    | Hyp.floating _ v => some v
    | Hyp.essential _ => none
```

Use `fr.vars` to get variable set from any Frame.

## Systematic Fix Procedure

### Step 1: Fix dvOK in axiom/theorem statements (lines 83-84, 203)

```bash
# Line 83:
- Metamath.Spec.dvOK fr_spec.dv σ ∧
+ Metamath.Spec.dvOK fr_spec.vars fr_spec.dv σ ∧

# Line 84:
- Metamath.Spec.dvOK fr'.dv σ
+ Metamath.Spec.dvOK fr'.vars fr'.dv σ

# Line 203:
- Metamath.Spec.dvOK fr_spec.dv σ_spec
+ Metamath.Spec.dvOK fr_spec.vars fr_spec.dv σ_spec
```

### Step 2: Fix dvOK lemmas (lines 272-599)

These are algebra lemmas about dvOK. Add `vars` parameter uniformly:

```lean
-- Line 274:
theorem no_dv_ok :
-  Metamath.Spec.dvOK [] σ := by
+  Metamath.Spec.dvOK vars [] σ := by
  unfold Metamath.Spec.dvOK
  intro v w h
  simp at h

-- Line 464:
theorem dv_sym :
-  Metamath.Spec.dvOK [(v, w)] σ → Metamath.Spec.dvOK [(w, v)] σ := by
+  Metamath.Spec.dvOK vars [(v, w)] σ → Metamath.Spec.dvOK vars [(w, v)] σ := by
```

### Step 3: Fix applySubst calls (lines 194, 283, 344+)

Need to determine correct vars for each context. Common patterns:

```lean
-- In toExpr_subst_commutes axiom (line 194):
- Metamath.Spec.applySubst σ_spec (toExpr e)
+ Metamath.Spec.applySubst vars σ_spec (toExpr e)
  -- Need to thread vars through theorem statement

-- In lemmas:
- applySubst σ e
+ applySubst vars σ e  -- Add vars parameter to lemma
```

### Step 4: Fix varsInExpr calls

Add `vars` parameter to all ~10-15 callsites.

## Affected Files

- `Metamath/Kernel.lean` (~349 errors, ~80 real fixes needed)
- `Metamath/Spec.lean` ✅ Already fixed
- `Metamath.lean` ✅ Already imports Kernel

## Testing Strategy

After each batch:
```bash
~/.elan/bin/lake build 2>&1 | grep "error:" | wc -l
```

Target progression:
- Start: 349 errors
- After dvOK fixes: ~250 errors
- After applySubst fixes: ~150 errors
- After cascading fixes: ~50 errors
- After manual review: 0 errors ✅

## Common Pitfalls

1. **Empty variable list**: Some lemmas use `dvOK [] σ` - needs `dvOK [] [] σ` or `dvOK vars [] σ`
2. **Context vars**: In nested frames, use `fr'.vars` for callee, `fr.vars` for caller
3. **Lemma generality**: Some dvOK lemmas should quantify over `vars` - add as parameter
4. **Cascading types**: Many errors auto-fix after core API matches

## Quick Reference: Verify.lean Types

```lean
inductive Sym
  | const (c : String)
  | var (v : String)

def Sym.value : Sym → String

abbrev Formula := Array Sym

inductive Object
  | const : String → Object      -- NOT formula symbols!
  | var : String → Object        -- NOT formula symbols!
  | hyp : Bool → Formula → String → Object
  | assert : Formula → Frame → String → Object
```

**Key**: `Object.const`/`Object.var` are for *symbol declarations* ($c/$v), NOT formula symbols!
