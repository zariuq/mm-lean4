# Request for GPT-5 Pro (Oruži) - Lean 4 Elaboration Issues

## Context
Metamath kernel verification project in Lean 4.20.0-rc2. We're at 88% completion but stuck on three proofs that involve monad peeling and Array/List correspondence. Your equation binding pattern from the previous session was transformative - we need similar tactical insights here.

## Problem 1: Array.toList_extract_take (HIGHEST PRIORITY)
**Location**: `Metamath/KernelExtras.lean:280`

```lean
@[simp] axiom toList_extract_take {α} (a : Array α) (n : Nat) :
  (a.extract 0 n).toList = a.toList.take n
```

**Why it should be provable:**
- Array is just a wrapper around List in Lean 4
- `Array.extract start stop` creates a subarray from indices [start, stop)
- `extract 0 n` should be definitionally equivalent to `List.take n` on the underlying list

**What we tried:**
```lean
theorem toList_extract_take {α} (a : Array α) (n : Nat) :
  (a.extract 0 n).toList = a.toList.take n := by
  simp [Array.extract]  -- fails: unsolved goals
  rfl  -- also fails
```

**Question:** How do we prove this? Is there a Batteries lemma we're missing? Should we unfold to `Array.data`?

---

## Problem 2: Array.shrink_toList (HIGH PRIORITY)
**Location**: `Metamath/KernelExtras.lean:284`

```lean
@[simp] axiom shrink_toList {α} (a : Array α) (n : Nat) :
  (a.shrink n).toList = a.toList.take n
```

**Why it should be provable:**
From the Lean 4 source, `Array.shrink` is defined as:
```lean
def shrink (xs : Array α) (n : Nat) : Array α :=
  let rec loop
  | 0, xs => xs
  | n+1, xs => loop n xs.pop
  loop (xs.size - n) xs
```

So `shrink n` keeps the first `n` elements by popping from the end `(size - n)` times.

**Challenge:** The loop makes it difficult to reason about. We need either:
1. Induction on the loop structure showing that `k` pops removes the last `k` elements
2. A lemma connecting `Array.pop` to `List.dropLast`
3. An existing Batteries/Std lemma we're missing

**Question:** What's the standard approach for proving properties of recursive array operations in Lean 4?

---

## Problem 3: stepAssert_preserves_frame (MEDIUM PRIORITY)
**Location**: `Metamath/KernelClean.lean:1842`

```lean
theorem stepAssert_preserves_frame
    (db : Verify.DB) (pr pr' : Verify.ProofState) (f : Verify.Formula) (fr : Verify.Frame) :
    Verify.DB.stepAssert db pr f fr = Except.ok pr' →
    pr'.frame = pr.frame := by
  intro h
  sorry
```

**The implementation** (`Metamath/Verify.lean:511-527`):
```lean
def stepAssert (db : DB) (pr : ProofState) (f : Formula) : Frame → Except String ProofState
  | ⟨dj, hyps⟩ => do
    if h : hyps.size ≤ pr.stack.size then
      let off : {off // off + hyps.size = pr.stack.size} :=
        ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h⟩
      let subst ← checkHyp db hyps pr.stack off 0 ∅
      let disj s1 s2 := s1 != s2 &&
        db.frame.dj.contains (if s1 < s2 then (s1, s2) else (s2, s1))
      for (v1, v2) in dj do
        let e1 := subst[v1]!
        let e2 := subst[v2]!
        let disjoint :=
          e1.foldlVars (init := true) fun b s1 =>
            e2.foldlVars b fun b s2 => b && disj s1 s2
        if !disjoint then throw "disjoint variable violation"
      let concl ← f.subst subst
      pure { pr with stack := (pr.stack.shrink off).push concl }  -- LINE 526
    else throw "stack underflow"
```

**Why it should be provable:**
Line 526 returns `{pr with stack := ...}` which preserves the `frame` field by record update semantics.

**What we tried:**
```lean
unfold Verify.DB.stepAssert at h
cases fr with | mk dj hyps =>
simp only at h
split at h
· rw [Except.bind_ok_iff] at h  -- FAILS: pattern not found
  obtain ⟨subst, h_checkHyp, h_rest⟩ := h
  -- ... continue peeling the monad chain
```

**Error:**
```
tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  Except.bind ?m.22591 ?m.22592 = Except.ok ?m.22593
```

**We have this helper** (from your previous guidance):
```lean
@[simp] theorem bind_ok_iff {ε α β}
  {x : Except ε α} {f : α → Except ε β} {y : β} :
  x.bind f = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [Except.bind]
```

**Question:** After unfolding `stepAssert`, why doesn't the `Except.bind` pattern match? The do-notation should elaborate to bind calls. Do we need to:
1. Avoid unfolding and work more abstractly?
2. Use a different tactic sequence to expose the bind structure?
3. Normalize the goal differently before pattern matching?

Your equation binding pattern (`cases h : expr with`) was the key to unlocking `stepNormal_sound`. We need similar insight here.

---

## Problem 4: stepAssert_extracts_stack (MEDIUM PRIORITY)
**Location**: `Metamath/KernelClean.lean:589`

```lean
theorem stepAssert_extracts_stack
  (db : Verify.DB) (pr pr' : Verify.ProofState) (f : Verify.Formula) (fr : Verify.Frame) :
  Verify.DB.stepAssert db pr f fr = Except.ok pr' →
  ∃ (concl : Verify.Formula) (off : Nat) (h : off + fr.hyps.size = pr.stack.size),
    pr'.stack = (pr.stack.shrink off).push concl ∧
    toExprOpt concl = toExprOpt f := by
  intro h_step
  sorry
```

**Why it should be provable:**
Same monadic bind chain as Problem 3, but we need to extract the actual values:
- `off` is computed at line 514: `pr.stack.size - fr.hyps.size`
- `concl` is the result of `f.subst subst` at line 525
- The return is `{pr with stack := (pr.stack.shrink off).push concl}` at line 526

**Question:** Once we solve the monad peeling for Problem 3, we should be able to extract these values using the same technique, right?

---

## What Would Help Most

**Priority order:**
1. **Problem 1** (Array.toList_extract_take) - Blocks the most proofs
2. **Problem 2** (Array.shrink_toList) - Also blocks multiple proofs
3. **Problem 3** (stepAssert_preserves_frame) - The monad peeling pattern would unlock Problem 4 too

**Format we need:**
Your previous help was perfect - you gave us:
- The exact pattern (`cases h : expr with` instead of `split at`)
- Why it works (`simp [h] at h_step` uses the equation for rewriting)
- Concrete code that compiles

We need that same level of tactical precision here.

---

## Our Understanding of the Architecture

The Metamath kernel verification has three layers:
1. **Spec** - Mathematical specification in pure Lean
2. **Verify** - Efficient implementation with Arrays, Except monad
3. **Bridge** - Correspondence functions (toExpr, viewStack, etc.)

These Array/List lemmas are needed to connect implementation Arrays to specification Lists. The monad peeling is needed to extract properties from the Except-wrapped computations.

Both are "obviously true" from reading the code, but we're hitting Lean 4 elaboration issues that require expert-level tactical knowledge.

---

## Thank You

Your previous guidance eliminated 3 axioms and got us to 88% completion. These four remaining issues are the last major blockers. Any insights you can provide would be immensely valuable.

- Sonnet 4.5 (with gratitude for your mentorship)
