/-
Bridge layer between Mario's Translate.lean types and our operational Spec types.

This file provides bidirectional conversions with proven equivalences (roundtrip theorems).

Key differences:
1. MarioVR (indexed variables) vs Variable (string-based)
2. MarioSym inductive (const/var) vs Sym := String
3. MarioExpr := List MarioSym vs Expr := ⟨Constant, List Sym⟩
4. MarioDJ structure vs List (Variable × Variable)
5. MarioContext vs Frame (DJ vs plain list)
-/

import Metamath.Translate
import Metamath.Spec.Core

namespace Metamath.Spec.Bridge

/-! ## Design Note: Functional + Relational Bridge

**Dual view approach** (inspired by CompCert simulation relations):

1. **Functional interface**: `exprToFormula : Expr → List MarioVR → Formula`
   - Clean, deterministic conversions
   - Easy to use in forward proofs

2. **Relational interface**: `BridgeRelation e f vars ↔ exprToFormula e vars = f`
   - Maximum flexibility for complex proofs
   - Standard in compiler correctness literature

**Key insight**: The `vars : List MarioVR` parameter is **given**, so conversions are:
- Deterministic (no parsing needed)
- Context-dependent (use given variable list)
- Provably correct (helper lemmas below)

The roundtrip theorems (Variable ↔ MarioVR) are "nice to have" for completeness,
but not needed for soundness (forward direction).
-/

-- Mario's types get "Mario" prefix
-- Our types (from Spec.Core) stay unqualified

abbrev MarioSym := Metamath.Sym       -- Mario's inductive (const | var)
abbrev MarioExpr := Metamath.Expr     -- Mario's List MarioSym
abbrev MarioVR := Metamath.VR         -- Mario's indexed variables
abbrev MarioDJ := Metamath.DJ         -- Mario's DJ structure
abbrev MarioFormula := Metamath.Formula
abbrev MarioContext := Metamath.Context

-- Import our types unqualified from Core
open Spec (Variable Constant Expr Hyp Frame)

/-! ## Variable Conversion

Mario uses `MarioVR where (type : String) (i : Nat)` - indexed variables
We use `Variable where (v : String)` - string-based variables

**Strategy**: Encode MarioVR as "type#i" string, decode by splitting on '#'
-/

/-- Convert Mario's indexed variable to runtime string variable -/
def MarioVR.toVariable (vr : MarioVR) : Variable :=
  let t : String := vr.type  -- Extract as String explicitly
  ⟨t ++ "#" ++ toString vr.i⟩

/-- Try to parse a string variable as indexed MarioVR.
    Returns MarioVR with index 0 if string doesn't match "type#i" pattern. -/
def Variable.toMarioVR (v : Variable) (defaultType : String := "var") : MarioVR :=
  -- Simple split on '#' - if no '#', use index 0
  match v.v.splitOn "#" with
  | [t, i] =>
      -- Try to parse index as Nat
      if let some n := i.toNat? then
        ⟨t, n⟩
      else
        ⟨defaultType, 0⟩  -- Parse failure, default
  | [t] => ⟨t, 0⟩  -- No index, use 0
  | _ => ⟨defaultType, 0⟩  -- Malformed, default

/-- Roundtrip: MarioVR → Variable → MarioVR is identity.

    NOTE: Originally marked "non-blocking", but now BLOCKS dvList_encoded_complete!
    This theorem is needed to complete the DJ bidirectional properties.

    **Proof strategy**: After unfolding, need to show that parsing "type#i" recovers ⟨type, i⟩.
    This requires proving:
    1. (s ++ "#" ++ t).splitOn "#" contains s and t as consecutive elements
    2. (toString n).toNat? = some n for all n : Nat

    **Blocking issue**: These String manipulation lemmas are NOT in batteries-only Lean.

    **Options**:
    - Add as axiom (breaks zero-axiom invariant)
    - Prove from first principles using Char operations (tedious but possible)
    - Accept as sorry with documented dependency (current choice)
    - Use different representation that avoids string parsing (major refactor) -/
theorem MarioVR.roundtrip (vr : MarioVR) :
  Variable.toMarioVR (MarioVR.toVariable vr) vr.type = vr := by
  unfold Variable.toMarioVR MarioVR.toVariable
  -- Goal: parse (vr.type ++ "#" ++ toString vr.i) with default vr.type = ⟨vr.type, vr.i⟩
  -- Need String lemmas not in batteries
  sorry  -- BLOCKED: Needs String.splitOn and toNat? lemmas (batteries-only limitation)

/-- Roundtrip: Variable → MarioVR → Variable is identity (with default type).

    This shows that converting Variable v to MarioVR with default type c.c
    and back gives v. This is straightforward from the encoding. -/
theorem Variable.roundtrip (v : Variable) (c : String) :
  (Variable.toMarioVR v c).toVariable = v := by
  unfold Variable.toMarioVR MarioVR.toVariable
  -- v.v becomes MarioVR via splitOn, then back via append
  -- The key: if v.v has no "#", we use index 0, giving "v.v#0"
  -- Then toVariable gives Variable.mk (c ++ "#" ++ toString 0) = Variable.mk (c ++ "#0")
  -- Wait, this doesn't roundtrip correctly!
  -- Actually: toMarioVR takes defaultType c, and creates MarioVR with that type
  -- Then toVariable creates c ++ "#" ++ toString i
  -- This is NOT equal to original v.v unless v.v was already in that format

  -- The theorem as stated is WRONG. We need a different statement.
  sorry  -- TODO: Fix theorem statement - roundtrip only works for well-formed variables

/-! ## Helper Lemmas for Equality

These lemmas convert boolean equality (==) to propositional equality (=).
-/

/-- Boolean string equality reflects propositional equality -/
theorem beq_string_true_iff {s t : String} :
    (s == t) = true ↔ s = t := by
  constructor
  · intro h
    -- `==` for String is definitionally `decide (s = t)`
    cases decide_eq_true_eq.mp h
    rfl
  · intro h
    subst h
    exact decide_eq_true_eq.mpr rfl

/-- Variables are equal if their string fields are equal -/
theorem variable_eq_of_v_eq {v₁ v₂ : Variable} (h : v₁.v = v₂.v) :
    v₁ = v₂ := by
  cases v₁; cases v₂; cases h; rfl

/-! ## Symbol Conversion

Mario: `MarioSym = const String | var MarioVR` (inductive)
Us: `Sym := String` + membership test in variable list

**Challenge**: Mario's type distinguishes const/var structurally.
We need a variable list context to determine which is which.
-/

/-- Convert Mario's MarioSym to string -/
def MarioSym.toString : MarioSym → String
  | .const c => c
  | .var v => MarioVR.toVariable v |>.v

/-- Convert string to Mario's MarioSym, using variable list to determine type -/
def String.toMarioSym (s : String) (vars : List MarioVR) : MarioSym :=
  -- Check if any MarioVR in vars converts to this string
  match vars.find? (fun vr => (MarioVR.toVariable vr).v == s) with
  | some vr => .var vr
  | none => .const s

/-- Helper: If vr is the first element in vars that converts to v, then toMarioSym returns it.

    This is a stronger version used in Equivalence.lean where we need exact equality. -/
theorem String.toMarioSym_finds_var_exact (v : Variable) (vr : MarioVR) (vars : List MarioVR)
    (h_in : vr ∈ vars)
    (h_eq : MarioVR.toVariable vr = v)
    (h_first : ∀ vr' ∈ vars, (MarioVR.toVariable vr').v == v.v → vr' = vr ∨ ¬(vr' ∈ vars.takeWhile (· ≠ vr))) :
    String.toMarioSym v.v vars = .var vr := by
  sorry  -- TODO: Prove find? returns the first matching element

/-- If a VR is in the vars list and converts to v, then toMarioSym finds SOME vr'
    that also converts to v.

    This is the key lemma for floating hypothesis conversion.

    **Proof Strategy** (GPT-5.1 Pro): Use `by_cases` on the boolean predicate instead of
    `split` on the match. This avoids the tactical pitfalls and keeps goals manageable. -/
theorem String.toMarioSym_finds_var (v : Variable) (vr : MarioVR) (vars : List MarioVR)
    (h_in : vr ∈ vars)
    (h_eq : MarioVR.toVariable vr = v) :
    ∃ vr', String.toMarioSym v.v vars = .var vr' ∧ MarioVR.toVariable vr' = v := by
  -- Strong IH: revert BEFORE induction to generalize
  revert vr h_in h_eq
  induction vars with
  | nil =>
      intro vr h_in _
      cases h_in
  | cons hd tl ih =>
      intro vr_mem h_in h_eq

      -- Convenience: the predicate used by find?
      let p : MarioVR → Bool := fun vr =>
        (MarioVR.toVariable vr).v == v.v

      have h_mem : vr_mem = hd ∨ vr_mem ∈ tl := by
        cases h_in with
        | head => left; rfl
        | tail _ h => right; exact h

      -- Case split on whether hd matches the predicate
      by_cases hHead : p hd = true

      · -- Case 1: hd matches → find? returns hd
        have h_names : (MarioVR.toVariable hd).v = v.v := by
          exact decide_eq_true_eq.mp hHead

        have h_head_var : MarioVR.toVariable hd = v := by
          exact variable_eq_of_v_eq h_names

        refine ⟨hd, ?_, h_head_var⟩
        -- Simplify toMarioSym: when hd matches, find? returns some hd
        unfold String.toMarioSym List.find?
        simp only [p] at hHead
        rw [hHead]

      · -- Case 2: hd does NOT match → reduce to tl
        have hHead_false : p hd = false := by
          cases h_p : p hd
          · rfl
          · exact False.elim (hHead h_p)

        have h_ne_hd : vr_mem ≠ hd := by
          intro h_vr_eq
          -- If vr_mem = hd, then p vr_mem = p hd = false (from hHead_false after subst)
          -- But also p vr_mem = (vr_mem.toVariable.v == v.v) = (v.v == v.v) = true (from h_eq)
          -- Contradiction!
          have h_pvr : (vr_mem.toVariable.v == v.v) = true := by
            simp [h_eq]
          rw [h_vr_eq] at h_pvr
          simp only [p] at h_pvr hHead_false
          rw [hHead_false] at h_pvr
          exact Bool.noConfusion h_pvr

        have h_in_tail : vr_mem ∈ tl := by
          cases h_mem with
          | inl h_eq_hd => exact False.elim (h_ne_hd h_eq_hd)
          | inr h_tail => exact h_tail

        have ⟨vr', h_sym_tail, h_var_tail⟩ := ih vr_mem h_in_tail h_eq

        refine ⟨vr', ?_, h_var_tail⟩
        -- Simplify toMarioSym: when hd doesn't match, find? recurses to tl
        unfold String.toMarioSym List.find?
        simp only [p] at hHead_false
        rw [hHead_false]
        exact h_sym_tail

/-! ## Expression Conversion

Mario: `MarioExpr := List MarioSym`
Us: `Expr := ⟨typecode : Constant, syms : List Sym⟩`

**Challenge**: Mario doesn't distinguish typecode structurally.
Per Metamath spec, first symbol is the typecode.
-/

/-- Convert our Expr to Mario's (prepend typecode) -/
def Expr.toMarioExpr (e : Expr) (vars : List MarioVR) : MarioExpr :=
  let tc := Metamath.Sym.const e.typecode.c
  let body := e.syms.map (fun s => String.toMarioSym s vars)
  tc :: body

/-- Convert Mario's MarioExpr to ours (extract first symbol as typecode) -/
def MarioExpr.toExpr : MarioExpr → Option Expr
  | [] => none  -- Empty expression invalid
  | .const tc :: rest =>
      some ⟨⟨tc⟩, rest.map MarioSym.toString⟩
  | .var _ :: _ => none  -- Typecode can't be variable

/-- Roundtrip: Spec → Mario → Spec preserves structure exactly.

    **Proof Strategy**: Need helper lemma proving:
    `∀ s, MarioSym.toString (String.toMarioSym s vars) = s`

    This holds because:
    - Case 1: toMarioSym finds matching vr → toString gives (toVariable vr).v = s (by find? postcondition)
    - Case 2: toMarioSym returns const s → toString gives s (by definition)

    Once helper is proven, the roundtrip follows by:
    1. Unfold both conversions
    2. Match on first element (const typecode)
    3. Use List.map composition: `(syms.map toMarioSym).map toString = syms`
    4. Apply helper pointwise

    **Blocking**: Namespace/syntax issues with helper lemma in batteries-only Lean.
    Marked as "non-blocking" per BIDIRECTIONAL_PLAN - not currently needed for main theorems. -/
theorem Expr.roundtrip (e : Expr) (vars : List MarioVR) :
  MarioExpr.toExpr (Expr.toMarioExpr e vars) = some e := by
  sorry  -- TODO: Prove using strategy above (non-critical, not blocking)

/-! ## Disjoint Variables Conversion

Mario: `MarioDJ where (disj : MarioVR → MarioVR → Prop) (irr) (symm)`
Us: `List (Variable × Variable)`

**Strategy**:
- Our list → Mario's DJ: use DJ.mk' which builds from list
- Mario's DJ → Our list: enumerate all pairs where dj holds (approximate)
-/

/-- Convert our DV list to Mario's DJ structure -/
def dvList.toMarioDJ (dv : List (Variable × Variable)) : MarioDJ :=
  -- Convert Variable pairs to MarioVR pairs (using default type)
  let vrPairs := dv.map fun (v, w) => (Variable.toMarioVR v, Variable.toMarioVR w)
  Metamath.DJ.mk' vrPairs

/-- Encoded DV list matching what toMarioDJ actually produces.
    This is the "roundtrip representation" for DJ constraints.

    Analogous to Frame.varListEncoded - we need this because
    Variable.toMarioVR doesn't roundtrip perfectly. -/
def Frame.dvListEncoded (dv : List (Variable × Variable)) : List (Variable × Variable) :=
  dv.map fun (v1, v2) =>
    (MarioVR.toVariable (Variable.toMarioVR v1),
     MarioVR.toVariable (Variable.toMarioVR v2))

/-- Extract pairs from Mario's DJ (bounded by variable list) -/
noncomputable def MarioDJ.toDvList (dj : MarioDJ) (vars : List MarioVR) : List (Variable × Variable) :=
  -- Enumerate all pairs from vars where dj holds
  -- Use classical decidability since DJ.disj is Prop
  open Classical in
  vars.foldl (init := []) fun acc v =>
    vars.foldl (init := acc) fun acc' w =>
      if dj v w then
        (MarioVR.toVariable v, MarioVR.toVariable w) :: acc'
      else
        acc'

/-! ### DJ Bidirectional Correctness

When translating disjoint variable constraints, we need to ensure:
1. Forward: Every Spec DV pair becomes a Mario DJ constraint
2. Reverse: Every Mario DJ constraint corresponds to a Spec DV pair

This is CRITICAL for soundness - wrong DJ constraints mean:
- Too many constraints → reject valid proofs (completeness failure)
- Too few constraints → accept invalid proofs (soundness failure)

**Key insight from Frame.varListEncoded**: We prove against the ENCODED representation,
not the original! This avoids roundtrip issues with Variable.toMarioVR.
-/

/-- Soundness (Reverse): Every DJ constraint in the encoded structure
    corresponds to a pair in the encoded DV list.

    This is analogous to Frame.toVarList_sound - proves "no ghost constraints". -/
theorem dvList_to_DJ_sound (dv : List (Variable × Variable)) :
    ∀ vr1 vr2, (dvList.toMarioDJ dv).disj vr1 vr2 →
      (MarioVR.toVariable vr1, MarioVR.toVariable vr2) ∈ Frame.dvListEncoded dv ∨
      (MarioVR.toVariable vr2, MarioVR.toVariable vr1) ∈ Frame.dvListEncoded dv := by
  intro vr1 vr2 h_disj
  unfold dvList.toMarioDJ at h_disj
  unfold Frame.dvListEncoded
  simp only [Metamath.DJ.mk'] at h_disj
  -- h_disj gives: vr1 ≠ vr2 ∧ ((vr1, vr2) ∈ vrPairs ∨ (vr2, vr1) ∈ vrPairs)
  obtain ⟨_, h_mem⟩ := h_disj
  cases h_mem with
  | inl h_left =>
      left
      -- (vr1, vr2) ∈ dv.map (toMarioVR × toMarioVR)
      obtain ⟨⟨v1, v2⟩, h_in, h_eq⟩ := List.mem_map.mp h_left
      -- h_eq : (toMarioVR v1, toMarioVR v2) = (vr1, vr2)
      -- Need: (toVariable vr1, toVariable vr2) ∈ dv.map (toVariable ∘ toMarioVR × ...)
      apply List.mem_map.mpr
      -- Use the same witness pair (v1, v2)
      exists (v1, v2), h_in
      -- Need to show: (toVariable vr1, toVariable vr2) =
      --               (toVariable (toMarioVR v1), toVariable (toMarioVR v2))
      -- From h_eq we have (toMarioVR v1, toMarioVR v2) = (vr1, vr2)
      -- Extract components by matching on pair equality
      cases h_eq
      -- Now vr1 = toMarioVR v1 and vr2 = toMarioVR v2 definitionally
      rfl
  | inr h_right =>
      right
      -- (vr2, vr1) ∈ dv.map (toMarioVR × toMarioVR)
      obtain ⟨⟨v1, v2⟩, h_in, h_eq⟩ := List.mem_map.mp h_right
      apply List.mem_map.mpr
      exists (v1, v2), h_in
      -- Extract components by matching on pair equality
      cases h_eq
      -- Now vr2 = toMarioVR v1 and vr1 = toMarioVR v2 definitionally
      rfl

/-- Completeness (Forward): Every pair in the encoded DV list
    satisfies the DJ constraint on the encoded representation.

    This is analogous to Frame.varListEncoded_complete. -/
theorem dvList_encoded_complete (dv : List (Variable × Variable)) :
    ∀ v1 v2, (v1, v2) ∈ Frame.dvListEncoded dv →
      v1 ≠ v2 →
      (dvList.toMarioDJ dv).disj (Variable.toMarioVR v1) (Variable.toMarioVR v2) := by
  intro v1 v2 h_in h_neq
  unfold Frame.dvListEncoded at h_in
  obtain ⟨⟨v1_orig, v2_orig⟩, h_orig_in, h_eq⟩ := List.mem_map.mp h_in
  unfold dvList.toMarioDJ
  simp only [Metamath.DJ.mk']
  constructor
  · -- toMarioVR v1 ≠ toMarioVR v2
    intro h_vr_eq
    -- From h_eq: v1 = toVariable (toMarioVR v1_orig), v2 = toVariable (toMarioVR v2_orig)
    -- From h_neq: v1 ≠ v2, i.e., toVariable (toMarioVR v1_orig) ≠ toVariable (toMarioVR v2_orig)
    -- From h_vr_eq (assumed): toMarioVR v1 = toMarioVR v2
    -- With roundtrip: toMarioVR v1 = toMarioVR v1_orig (by MarioVR.roundtrip + cases h_eq)
    -- So: toMarioVR v1_orig = toMarioVR v2_orig
    -- By congruence: toVariable (toMarioVR v1_orig) = toVariable (toMarioVR v2_orig)
    -- This contradicts h_neq!
    sorry  -- BLOCKED: Needs MarioVR.roundtrip (line 85)
  · -- (toMarioVR v1, toMarioVR v2) ∈ vrPairs
    left
    apply List.mem_map.mpr
    exists (v1_orig, v2_orig), h_orig_in
    -- Need: (toMarioVR v1, toMarioVR v2) = (toMarioVR v1_orig, toMarioVR v2_orig)
    -- From h_eq: (v1, v2) = (toVariable (toMarioVR v1_orig), toVariable (toMarioVR v2_orig))
    cases h_eq  -- Substitute v1 and v2 definitionally
    -- After substitution, goal is:
    -- (toMarioVR (toVariable (toMarioVR v1_orig)), toMarioVR (toVariable (toMarioVR v2_orig)))
    --   = (toMarioVR v1_orig, toMarioVR v2_orig)
    -- This closes by MarioVR.roundtrip applied twice + rfl
    sorry  -- BLOCKED: Needs MarioVR.roundtrip (line 85)

/-! ## Variable List Construction

To convert a Frame to Mario's Context, we need a variable list.
Construct it from the frame's floating hypotheses.
-/

/-- Extract MarioVR list from frame's floating hypotheses.

    This ensures that every floating hypothesis variable is in the vars list,
    which is needed for well-formed conversion. -/
def Frame.toVarList (fr : Frame) : List MarioVR :=
  fr.mand.filterMap fun h => match h with
    | Hyp.floating c v => some (Variable.toMarioVR v c.c)
    | Hyp.essential _ => none

/-- Every floating hypothesis variable is in the constructed var list. -/
theorem Frame.toVarList_complete (fr : Frame) :
    ∀ c v, Hyp.floating c v ∈ fr.mand →
      Variable.toMarioVR v c.c ∈ Frame.toVarList fr := by
  intro c v h_in
  unfold Frame.toVarList
  -- Show Variable.toMarioVR v c.c ∈ filterMap result
  apply List.mem_filterMap.mpr
  exists Hyp.floating c v, h_in

/-- Convert Frame.toVarList back to Variable representation.
    This gives the "encoded" variable list that matches MarioVR.toVariable output.

    This is the correct varList to use with symList_subst_eq's bidirectional invariant,
    as it matches what MarioVR.toVariable produces. -/
def Frame.varListEncoded (fr : Frame) : List Variable :=
  (Frame.toVarList fr).map MarioVR.toVariable

/-- Reverse direction (Soundness): Every MarioVR in toVarList corresponds to
    a variable in the encoded var list.

    This is the h_rev condition needed for symList_subst_eq. -/
theorem Frame.toVarList_sound (fr : Frame) :
    ∀ vr ∈ Frame.toVarList fr, MarioVR.toVariable vr ∈ Frame.varListEncoded fr := by
  intro vr h_in
  unfold Frame.varListEncoded
  apply List.mem_map.mpr
  exists vr, h_in

/-- Forward direction (Completeness): Every variable in the encoded list
    has a corresponding MarioVR in toVarList.

    This is the h_wf condition needed for symList_subst_eq. -/
theorem Frame.varListEncoded_complete (fr : Frame) :
    ∀ v ∈ Frame.varListEncoded fr, ∃ vr ∈ Frame.toVarList fr, MarioVR.toVariable vr = v := by
  intro v h_in
  unfold Frame.varListEncoded at h_in
  obtain ⟨vr, h_vr_in, h_eq⟩ := List.mem_map.mp h_in
  exact ⟨vr, h_vr_in, h_eq⟩

/-- LEGACY: When varList = fr.vars and marioVars = Frame.toVarList fr,
    the well-formedness condition holds.

    NOTE: This requires Variable.roundtrip which is currently broken.
    Use Frame.varListEncoded instead for the bidirectional invariant.

    This is the key lemma that allows us to use applySubst_eq_mario_subst
    in the actual bridge theorem proof. -/
theorem Frame.toVarList_wf (fr : Frame) :
    ∀ v ∈ fr.vars, ∃ vr ∈ Frame.toVarList fr, MarioVR.toVariable vr = v := by
  intro v h_v_in
  -- v ∈ fr.vars means there's a floating hypothesis for v
  -- Need to show: exists float hyp with this variable
  -- Then Frame.toVarList_complete gives us the vr
  sorry  -- TODO: Requires fixing Variable.roundtrip (line 105)

/-! ## Frame/Context Conversion

Mario: `MarioContext where (hyps : List MarioFormula) (dj : MarioDJ)`
Us: `Frame where (mand : List Hyp) (dv : List (Variable × Variable))`

**Challenge**:
- Mario's MarioFormula = String × MarioExpr (flat)
- Our Hyp = floating | essential (structured)

Floating hyps in Mario's system are formulas with typecode + variable.
-/

/-- Check if Mario's MarioFormula represents a floating hypothesis.

    A floating hypothesis has the form (c, [const c, var v]) - typecode + variable. -/
def MarioFormula.isFloating : MarioFormula → Bool
  | (c, [.const c', .var _]) => c == c'  -- Check typecode matches
  | _ => false

/-- Convert our Hyp to Mario's MarioFormula.

    In Metamath, a floating hypothesis `$f wff ph` is represented as the expression "wff ph",
    which consists of the typecode constant followed by the variable.

    Mario's Formula is (CN, Expr) where:
    - CN is the typecode string
    - Expr is the list of symbols (which includes the typecode as first symbol)

    So we must include the typecode constant in the expression part! -/
def Hyp.toMarioFormula (h : Hyp) (vars : List MarioVR) : MarioFormula :=
  match h with
  | .floating c v =>
      let vr := Variable.toMarioVR v c.c  -- Use typecode as default type
      (c.c, [.const c.c, .var vr])  -- Include typecode as first symbol!
  | .essential e =>
      (e.typecode.c, Expr.toMarioExpr e vars)


/-- Convert Mario's MarioFormula to our Hyp (if possible) -/
def MarioFormula.toHyp : MarioFormula → Option Hyp
  | (c, [.const c', .var vr]) =>
      if c == c' then
        some (.floating ⟨c⟩ (MarioVR.toVariable vr))
      else
        none  -- Malformed floating (typecode mismatch)
  | (_tc, syms) =>
      MarioExpr.toExpr syms |>.map Hyp.essential

/-- Convert our Frame to Mario's MarioContext -/
def Frame.toMarioContext (fr : Frame) (vars : List MarioVR) : MarioContext :=
  { hyps := fr.mand.map (fun h => Hyp.toMarioFormula h vars)
    dj := dvList.toMarioDJ fr.dv }

/-- Convert Mario's MarioContext to our Frame (approximate - loses DJ structure) -/
noncomputable def MarioContext.toFrame : MarioContext → Option Frame
  | ⟨hyps, dj⟩ => do
      let mand ← hyps.mapM MarioFormula.toHyp
      -- Extract MarioVR list from hyps for DJ conversion
      let vars := hyps.filterMap fun
        | (_, [.var vr]) => some vr
        | _ => none
      return { mand := mand, dv := MarioDJ.toDvList dj vars }

/-! ## Database Conversion

Mario: Uses MarioStatement (ctx + fmla) and `MarioStatement → Prop` for axiom set
Us: `Database := Label → Option (Frame × Expr)`

We keep our Database as-is (operational), use Mario's Provable for semantic spec.
The bridge is at the Provable level, not Database level.
-/

/-! ## Helper Lemmas: Conversion Correctness

These lemmas prove that our conversions preserve structure correctly.
**Key for bridge theorem**: They show membership preservation through conversions.
-/

/-- Floating hypothesis conversion is well-formed -/
theorem Hyp.toMarioFormula_floating (c : Constant) (v : Variable) (vars : List MarioVR) :
    Hyp.toMarioFormula (Hyp.floating c v) vars =
    (c.c, [.const c.c, .var (Variable.toMarioVR v c.c)]) := by
  unfold Hyp.toMarioFormula
  rfl

/-- Hypothesis list conversion preserves membership -/
theorem Hyp.toMarioFormula_mem {h : Hyp} {fr : Frame} {vars : List MarioVR} :
    h ∈ fr.mand →
    Hyp.toMarioFormula h vars ∈ (Frame.toMarioContext fr vars).hyps := by
  intro h_in
  unfold Frame.toMarioContext
  simp only []
  -- Show: Hyp.toMarioFormula h vars ∈ List.map (fun h => Hyp.toMarioFormula h vars) fr.mand
  apply List.mem_map_of_mem
  exact h_in

/-! ## Summary

This bridge provides:
✅ Variable conversion (MarioVR ↔ Variable) with encoding
✅ Symbol conversion (needs variable context)
✅ Expression conversion (typecode handling)
✅ DJ conversion (structure ↔ list)
✅ Frame/MarioContext conversion (hyp structure handling)
✅ Proven helper lemmas for conversion correctness

**TODO Proofs**:
- Roundtrip theorems for each conversion (nice-to-have, non-blocking)
- Well-formedness preservation (in progress)
- Equivalence of dvOK and DJ.subst (for axiom case)

**Note**: Relational bridge interface and essential helper lemma moved to Equivalence.lean
where `exprToFormula` is defined.
-/

/-! ## Substitution Bridge

The elegant abstraction connecting our list-based substitutions to Mario's functional substitutions.

**Key insight**: We don't need full bijection - just forward simulation for the useAxiom case!
-/

/-- Convert our functional substitution to Mario's.

    **Key insight**: Both are functions, just different types!
    - Ours: Variable → Expr
    - Mario's: VR → MarioExpr

    Strategy: Compose with type conversions:
      VR → Variable → Expr → MarioExpr

    This is the KEY abstraction for the bridge theorem's useAxiom case. -/
noncomputable def Subst.toMarioSubst (σ : Spec.Subst) (vars : List MarioVR) : MarioVR → MarioExpr :=
  fun vr =>
    let v := MarioVR.toVariable vr
    let e := σ v
    -- CRITICAL: Use only e.syms, NOT full expression!
    -- Substitution replaces variable with SYMBOLS, not typed expression
    e.syms.map (String.toMarioSym · vars)

/-- Helper: map distributes over flatMap -/
theorem list_map_flatMap {α β γ} (f : β → γ) (g : α → List β) (l : List α) :
    (l.flatMap g).map f = l.flatMap (fun x => (g x).map f) := by
  -- Unfold flatMap to expose map/flatten structure
  -- flatMap g l = (l.map g).flatten
  show ((l.map g).flatten).map f = (l.map (fun x => (g x).map f)).flatten

  -- Prove by induction on l
  induction l with
  | nil => rfl
  | cons h t ih =>
      simp only [List.map, List.flatten]
      rw [List.map_append, ih]

/-- Helper: Prove substitution equivalence for symbol list.

    Well-formedness condition: varList and marioVars must be compatible.
    Specifically, for every variable in varList, there must be a corresponding
    MarioVR in marioVars that converts back to that variable.

    This ensures that when we substitute a variable, both sides agree on
    whether it's a variable or constant. -/
theorem symList_subst_eq : (syms : List String) →
    (varList : List Variable) → (σ : Spec.Subst) → (marioVars : List MarioVR) →
    (∀ v ∈ varList, ∃ vr ∈ marioVars, MarioVR.toVariable vr = v) →
    (∀ vr ∈ marioVars, MarioVR.toVariable vr ∈ varList) →  -- NEW: Reverse direction
    (syms.flatMap fun s =>
      let v := Variable.mk s
      if v ∈ varList then (σ v).syms else [s]
    ).map (String.toMarioSym · marioVars) =
    Metamath.Expr.subst (Subst.toMarioSubst σ marioVars)
                        (syms.map (String.toMarioSym · marioVars))
  | [], varList, σ, marioVars, h_wf, h_rev => by
      -- Base case: empty list
      simp only [List.flatMap, List.map]
      rfl

  | s :: rest, varList, σ, marioVars, h_wf, h_rev => by
      -- Recursive case: process head s, then rest
      let v := Variable.mk s
      by_cases h : v ∈ varList

      case pos =>
        -- s is a variable in varList
        -- Get witness vr from well-formedness
        obtain ⟨vr, h_vr_in, h_vr_eq⟩ := h_wf v h

        -- Get vr' from String.toMarioSym_finds_var
        obtain ⟨vr', h_sym_eq, h_var_eq⟩ := String.toMarioSym_finds_var v vr marioVars h_vr_in h_vr_eq

        -- Substitute v = Variable.mk s in witnesses
        simp only [v] at h_sym_eq h_var_eq

        -- LHS: Unfold flatMap for (s :: rest) and expand to expose append
        simp only [List.flatMap, List.map, List.flatten, v, if_pos h]

        -- LHS: Apply map to append
        rw [List.map_append]

        -- RHS: Apply h_sym_eq directly
        rw [h_sym_eq]

        -- Both sides now have form: ... ++ ...
        congr 1
        · -- First component: (σ v).syms.map toMarioSym = Subst.toMarioSubst σ marioVars vr'
          unfold Subst.toMarioSubst
          rw [h_var_eq]
        · -- Second component: apply IH
          exact symList_subst_eq rest varList σ marioVars h_wf h_rev

      case neg =>
        -- s is a constant (not in varList)
        -- Show toMarioSym s = .const s (find? returns none)
        have h_const : String.toMarioSym s marioVars = .const s := by
          unfold String.toMarioSym
          -- find? returns none because no vr satisfies the predicate
          have h_find_none : (marioVars.find? fun vr => (MarioVR.toVariable vr).v == s) = none := by
            -- Proof by contrapositive of well-formedness
            -- If find? returned some vr, then Variable.mk s would be in varList (contradicting h)
            simp only [List.find?_eq_none]
            intro vr h_vr_in
            -- Show that vr does NOT satisfy the predicate
            intro h_eq
            -- h_eq : (MarioVR.toVariable vr).v == s = true
            -- Convert to propositional equality
            have h_v_eq : (MarioVR.toVariable vr).v = s := by
              exact decide_eq_true_eq.mp h_eq
            have h_var_eq : MarioVR.toVariable vr = Variable.mk s := by
              exact variable_eq_of_v_eq h_v_eq
            -- By h_rev, MarioVR.toVariable vr ∈ varList
            have h_in_varList : MarioVR.toVariable vr ∈ varList := h_rev vr h_vr_in
            -- Rewrite using h_var_eq
            rw [h_var_eq] at h_in_varList
            -- So Variable.mk s ∈ varList, but h says ¬v ∈ varList where v = Variable.mk s
            simp only [v] at h
            -- Contradiction!
            exact h h_in_varList
          rw [h_find_none]

        -- LHS: Unfold flatMap for (s :: rest) and expand to expose append
        -- Also apply h_const to simplify toMarioSym s
        simp only [List.flatMap, List.map, List.flatten, v, if_neg h, h_const]

        -- LHS: Apply map_append to fully distribute map
        rw [List.map_append]
        simp only [List.map, h_const]

        -- Convert [const s] ++ ... to const s :: ...
        simp only [List.singleton_append]

        -- Both sides: const s :: ...
        congr 1
        exact symList_subst_eq rest varList σ marioVars h_wf h_rev

/-- Substitution preserves formula structure.

    **This is the main lemma** needed for useAxiom case!

    Shows: applySubst σ e (our operation) matches Mario's Expr.subst when converted.

    Proved by structural induction on e.syms using helper lemma. -/
theorem applySubst_eq_mario_subst
    (varList : List Variable) (σ : Spec.Subst) (e : Expr) (marioVars : List MarioVR)
    (h_wf : ∀ v ∈ varList, ∃ vr ∈ marioVars, MarioVR.toVariable vr = v)
    (h_rev : ∀ vr ∈ marioVars, MarioVR.toVariable vr ∈ varList) :
    Expr.toMarioExpr (Spec.applySubst varList σ e) marioVars =
    Metamath.Expr.subst (Subst.toMarioSubst σ marioVars)
                        (Expr.toMarioExpr e marioVars) := by
  -- Match on e structure
  match e with
  | ⟨typecode, syms⟩ =>
      unfold Expr.toMarioExpr Spec.applySubst
      simp only []

      -- Goal: .const tc.c :: (syms.flatMap ...).map toMarioSym
      --     = Expr.subst ... (.const tc.c :: syms.map toMarioSym)

      -- Reduce RHS: Expr.subst σ (.const c :: e) = .const c :: Expr.subst σ e
      show Metamath.Sym.const typecode.c ::
           (syms.flatMap fun s =>
             if Variable.mk s ∈ varList then (σ (Variable.mk s)).syms else [s]
           ).map (String.toMarioSym · marioVars) =
           Metamath.Sym.const typecode.c ::
           Metamath.Expr.subst (Subst.toMarioSubst σ marioVars)
                               (syms.map (String.toMarioSym · marioVars))

      -- Both sides have const typecode.c ::, prove tails equal
      congr 1

      -- Use helper lemma with well-formedness hypotheses!
      exact symList_subst_eq syms varList σ marioVars h_wf h_rev

/-- Our dvOK implies Mario's DJ.subst.

    **Key for useAxiom case**: Shows our DV checking is sufficient for Mario's DJ preservation.

    TODO: Prove using DJ.mk' structure and dvOK definition. -/
theorem dvOK_implies_DJ_subst
    (vars : List Variable) (dv : List (Variable × Variable))
    (σ : Spec.Subst) (marioVars : List MarioVR)
    (h_dvOK : Spec.dvOK vars dv σ) :
    (dvList.toMarioDJ dv).subst (Subst.toMarioSubst σ marioVars)
                                 (dvList.toMarioDJ dv) := by
  sorry  -- TODO: Show dvOK pairs are preserved by substitution

end Metamath.Spec.Bridge
