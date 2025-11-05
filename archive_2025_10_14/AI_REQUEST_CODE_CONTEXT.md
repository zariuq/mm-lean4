# Code Context for AI Expert Review

This document contains the relevant code snippets for the checkHyp integration questions.

---

## 1. Our Already-Proven Theorem (THE KEY!) ✅

```lean
-- Location: Metamath/Kernel.lean lines 1168-1226
/-- Soundness of matchFloats: if matching succeeds, σ binds each variable correctly. -/
theorem matchFloats_sound (floats : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (stack : List Metamath.Spec.Expr) (σ : Metamath.Spec.Subst)
    (h_nodup : List.Nodup (floats.map Prod.snd)) :
  matchFloats floats stack = some σ →
  floats.map (fun (tc, v) => σ v) = stack := by
  intro h_match
  revert h_nodup
  induction floats generalizing stack σ with
  | nil =>
      intro h_nodup
      cases stack with
      | nil => simp [matchFloats] at h_match; simp
      | cons s ss => simp [matchFloats] at h_match
  | cons hd fs ih =>
      intro h_nodup
      obtain ⟨tc, v⟩ := hd
      rw [List.map_cons] at h_nodup
      have ⟨h_v_notin, h_nodup_tail⟩ := List.nodup_cons.mp h_nodup
      cases stack with
      | nil => simp [matchFloats] at h_match
      | cons e es =>
          simp [matchFloats] at h_match
          split at h_match
          · contradiction
          · next h_tc =>
              split at h_match
              · contradiction
              · next σ_rest h_match_rest =>
                  have ih_applied := ih es σ_rest h_match_rest h_nodup_tail
                  simp at h_match
                  rw [← h_match]
                  simp [List.map]
                  congr 1
                  rw [← ih_applied]
                  apply List.map_congr_left
                  intro ⟨tc', v'⟩ h_mem
                  have h_ne : v' ≠ v := by
                    intro h_eq
                    have : v' ∈ fs.map Prod.snd := by
                      rw [List.mem_map]
                      exact ⟨(tc', v'), h_mem, rfl⟩
                    exact h_v_notin (h_eq ▸ this)
                  simp [h_ne]
```

**THIS IS PROVEN AND WORKS!** We want to apply this in checkHyp_floats_sound.

---

## 2. Spec-Level Definitions We Use

```lean
-- Metamath/Spec.lean

-- Expression: typecode + symbols
structure Expr where
  typecode : Constant
  syms : List Sym
  deriving Repr, DecidableEq

-- Substitution: function from Variables to Expressions
abbrev Subst := Variable → Expr

-- Apply substitution to expression
def applySubst (vars : List Variable) (σ : Subst) (e : Expr) : Expr :=
  { typecode := e.typecode
    syms := e.syms.flatMap fun s =>
      let v := Variable.mk s
      if v ∈ vars then (σ v).syms else [s] }

-- matchFloats: bind floating hypotheses, build substitution
def matchFloats (floats : List (Constant × Variable))
    (stack : List Expr) : Option Subst :=
  match floats, stack with
  | [], [] => some (fun v => ⟨⟨"wff"⟩, [v.v]⟩)  -- Identity
  | [], _ :: _ => none
  | _ :: _, [] => none
  | (tc, v) :: fs, e :: es =>
      if e.typecode ≠ tc then none
      else
        match matchFloats fs es with
        | none => none
        | some σ => some (fun w => if w = v then e else σ w)

-- checkEssentials: verify essential hypotheses against stack
def checkEssentials (vars : List Variable) (σ : Subst)
    (essentials : List Expr) (stack : List Expr) : Bool :=
  match essentials, stack with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | e_hyp :: es, e_stack :: ss =>
      (applySubst vars σ e_hyp == e_stack) && checkEssentials vars σ es ss
```

---

## 3. Implementation-Level Types (Metamath/Verify.lean)

```lean
-- Implementation Formula: Array of symbols
abbrev Formula := Array Sym

-- Symbol: either constant or variable
inductive Sym where
  | const : String → Sym
  | var : String → Sym

-- Database: stores hypotheses and assertions
structure DB where
  -- ... (HashMap of labels to objects)

-- Object: hypothesis or assertion
inductive Object where
  | hyp : Bool → Formula → ... → Object  -- Bool: true=essential, false=floating
  | assert : Formula → Frame → ... → Object
```

---

## 4. Bridge Functions (Need Definitions!)

```lean
-- These should exist somewhere in Kernel.lean, need to find/verify:

-- Convert implementation Formula to spec Expr
def toExpr : Metamath.Verify.Formula → Option Metamath.Spec.Expr :=
  -- Need actual definition!
  sorry

-- Convert implementation HashMap substitution to spec function
def toSubst : Std.HashMap String Metamath.Verify.Formula → Option Metamath.Spec.Subst :=
  -- Need actual definition!
  sorry

-- Convert implementation Frame to spec Frame
def toFrame : Metamath.Verify.Frame → Option Metamath.Spec.Frame :=
  -- Need actual definition!
  sorry
```

**QUESTION:** Are these defined? Where? What do they do exactly?

---

## 5. Current (BROKEN) Theorem Statements

### checkHyp_floats_sound (Line 1691)

```lean
/-- Implementation's checkHyp for floats corresponds to spec matchFloats -/
theorem checkHyp_floats_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : Nat)
    (subst_impl : Std.HashMap String Metamath.Verify.Formula) :
  -- If checkHyp succeeds on floating hypotheses
  (∀ i < hyps.size,
    ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with
    | .hyp false f _ => True  -- floating
    | _ => False) →
  -- Then there exists a spec-level matchFloats result
  ∃ (floats_spec : List (Metamath.Spec.Constant × Metamath.Spec.Variable))
    (σ_spec : Metamath.Spec.Subst),
    toSubst subst_impl = some σ_spec ∧
    floats_spec.map (fun (tc, v) => σ_spec v) =
      (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e) := by
  --  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  --  TYPE ERROR: List Expr ≠ Prop
  sorry
```

### checkHyp_essentials_sound (Line 1714)

```lean
/-- Implementation's checkHyp for essentials corresponds to spec checkEssentials -/
theorem checkHyp_essentials_sound
    (db : Metamath.Verify.DB)
    (hyps : Array String)
    (stack : Array Metamath.Verify.Formula)
    (off : Nat)
    (subst_impl : Std.HashMap String Metamath.Verify.Formula) :
  -- If checkHyp succeeds on essential hypotheses
  (∀ i < hyps.size,
    ∃ obj, db.find? hyps[i] = some obj ∧
    match obj with
    | .hyp true f _ => True  -- essential
    | _ => False) →
  -- Then there exists a spec-level checkEssentials result
  ∃ (vars : List Metamath.Spec.Variable)
    (essentials_spec : List Metamath.Spec.Expr)
    (stack_spec : List Metamath.Spec.Expr)
    (σ_spec : Metamath.Spec.Subst),
    toSubst subst_impl = some σ_spec ∧
    (∀ i < hyps.size, ∃ e, toExpr stack[off + i] = some e) ∧
    checkEssentials vars σ_spec essentials_spec stack_spec = true := by
  sorry
```

---

## 6. Helper Lemmas We Have Available ✅

```lean
-- Lines 296-333 in Kernel.lean

/-- FlatMap membership iff -/
@[simp] lemma List.mem_flatMap_iff {α β} (xs : List α) (f : α → List β) (b : β) :
  b ∈ xs.flatMap f ↔ ∃ a ∈ xs, b ∈ f a := by simpa [List.mem_flatMap]

/-- Membership in varsInExpr from symbol membership -/
lemma mem_varsInExpr_of_mem_syms
  {vars : List Metamath.Spec.Variable} {e : Metamath.Spec.Expr} {s}
  (hvar : Metamath.Spec.Variable.mk s ∈ vars)
  (hsyms : s ∈ e.syms) :
  Metamath.Spec.Variable.mk s ∈ Metamath.Spec.varsInExpr vars e := by
  unfold Metamath.Spec.varsInExpr
  exact (List.mem_filterMap.mpr ⟨s, hsyms, by simp [hvar]⟩)

/-- Membership in varsInExpr from substitution result -/
lemma mem_varsInExpr_of_mem_sigma
  {vars : List Metamath.Spec.Variable} {σ}
  {v : Metamath.Spec.Variable} {s}
  (hvar : Metamath.Spec.Variable.mk s ∈ vars)
  (hsyms : s ∈ (σ v).syms) :
  Metamath.Spec.Variable.mk s ∈ Metamath.Spec.varsInExpr vars (σ v) := by
  unfold Metamath.Spec.varsInExpr
  exact (List.mem_filterMap.mpr ⟨s, hsyms, by simp [hvar]⟩)

/-- Tail of nodup list is nodup -/
lemma List.nodup_tail {α} {h : α} {t : List α} :
  List.Nodup (h :: t) → List.Nodup t := by
  simpa [List.nodup_cons] using (List.nodup_cons.mp)

/-- Element in tail is not equal to head -/
lemma not_mem_of_nodup_cons {α} {h x : α} {t : List α} :
  List.Nodup (h :: t) → x ∈ t → x ≠ h := by
  intro hN hx heq
  have ⟨h_notin, _⟩ : h ∉ t ∧ List.Nodup t := List.nodup_cons.mp hN
  exact h_notin (heq ▸ hx)
```

---

## 7. What We Need to Understand About checkHyp

The implementation function `checkHyp` (approximately):

```lean
-- Metamath/Verify.lean (our understanding)
def checkHyp (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : Nat) (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) :=
  if i >= hyps.size then
    pure subst  -- Done
  else
    match db.find? hyps[i] with
    | some (.hyp false f _) =>  -- Floating hypothesis
        -- Extract variable name from f
        let var_name := extract_var_from_formula f
        -- Bind variable to stack expression
        let subst' := subst.insert var_name stack[off + i]
        checkHyp db hyps stack off (i+1) subst'
    | some (.hyp true f _) =>   -- Essential hypothesis
        -- Check that f.subst(subst) equals stack[off + i]
        match f.subst subst with
        | some f_inst =>
            if f_inst == stack[off + i] then
              checkHyp db hyps stack off (i+1) subst  -- No change to subst
            else
              throw "essential hypothesis doesn't match"
        | none => throw "substitution failed"
    | _ => throw "invalid hypothesis"
```

**QUESTIONS:**
1. Is this roughly correct?
2. How exactly does it extract the variable from a floating hypothesis?
3. What does `f.subst` do exactly?
4. Is there actual recursion or a loop?

---

## 8. Proof Patterns That Worked For Us

### Pattern 1: Nodup Precondition (Used 4 times!)

```lean
theorem matchSyms_sound ... (h_nodup : List.Nodup hyp_syms) : ... := by
  intro h_match
  revert h_nodup  -- Key: revert before induction!
  induction hyp_syms ... with
  | case h hs ih =>
      intro h_nodup
      have ⟨h_notin, h_nodup_tail⟩ := List.nodup_cons.mp h_nodup
      -- Use h_notin for contradictions
      -- Pass h_nodup_tail to IH
      ...
```

### Pattern 2: Witness-Based Approach

```lean
theorem vars_apply_subset ... := by
  -- Extract witness from flatMap
  have ⟨s', hs'e, hs_in⟩ := List.mem_flatMap_iff ... |>.mp ...
  -- Choose producing element as witness
  by_cases h_var : Variable.mk s' ∈ vars
  · right; use Variable.mk s'; ...
  · left; ...
```

### Pattern 3: Simple Induction

```lean
theorem identity_subst_syms ... := by
  induction syms with
  | nil => simp [List.flatMap]
  | cons s ss ih =>
      simp [List.flatMap]
      split
      · -- Variable case
        ...
      · -- Constant case
        simp [ih]
```

**These patterns worked great for us!**

---

## Summary of What We Need

1. **Corrected theorem statements** for checkHyp_floats_sound and checkHyp_essentials_sound
2. **Definitions or specifications** of toExpr, toSubst, toFrame
3. **Bridge lemmas** we should prove first (with statements)
4. **Proof strategy** showing how to apply matchFloats_sound
5. **Patterns** for HashMap↔Function and Array↔List correspondences

With these, we can complete the remaining sorries!

---

**Note:** Full file is ~3400 lines. Can provide complete file if needed, but tried to extract relevant parts here.
