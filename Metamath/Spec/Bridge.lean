/-
Bridge layer between Mario's DeclarativeSpec.lean types and our operational Spec types.

This file provides bidirectional conversions with proven equivalences (roundtrip theorems).

Key differences:
1. MarioVR (indexed variables) vs Variable (string-based)
2. MarioSym inductive (const/var) vs Sym := String
3. MarioExpr := List MarioSym vs Expr := ⟨Constant, List Sym⟩
4. MarioDJ structure vs List (Variable × Variable)
5. MarioContext vs Frame (DJ vs plain list)
-/

import Metamath.DeclarativeSpec
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

-- CharCodec namespace was archived - discovered simpler index-0 encoding approach

/-! ## Variable Conversion

Mario uses `MarioVR where (type : String) (i : Nat)` - indexed variables
We use `Variable where (v : String)` - string-based variables

**Key Insight**: Original Metamath variables ALL map to index 0!
The index is only used by Mario for fresh variable generation during substitution.

**Strategy**:
- Variable.toMarioVR: Injective encoding using index 0
- MarioVR.toVariable: Simple projection (type field only, ignore index)
- This avoids the '#' collision problem entirely!
-/

/-- Convert our Variable to Mario's indexed MarioVR.

    All original Metamath variables get index 0.
    Mario uses non-zero indices only for fresh variables he generates.

    This encoding is INJECTIVE: different variables → different VRs. -/
def Variable.toMarioVR (v : Variable) : MarioVR :=
  ⟨v.v, 0⟩

/-- Convert Mario's indexed variable to our Variable.

    We simply project the type field, ignoring the index.
    This is used for display/debugging and in bidirectional conversions. -/
def MarioVR.toVariable (vr : MarioVR) : Variable :=
  ⟨vr.type⟩

/-- Injectivity: Different variables map to different VRs.

    This is the key property we need - no roundtrip required!
    Proof is trivial since we just wrap the string with index 0. -/
theorem Variable.toMarioVR_injective :
    ∀ v1 v2, Variable.toMarioVR v1 = Variable.toMarioVR v2 → v1 = v2 := by
  intro v1 v2 h
  unfold Variable.toMarioVR at h
  -- From ⟨v1.v, 0⟩ = ⟨v2.v, 0⟩ we get v1.v = v2.v
  cases v1; cases v2
  cases h
  -- Now v1.v = v2.v definitionally, so Variable.mk v1.v = Variable.mk v2.v
  rfl

/-- Partial roundtrip: For index-0 VRs, converting to Variable and back recovers the VR.

    This holds for all original Metamath variables (which all have index 0).
    For fresh variables (index > 0), the index is lost, but that's OK -
    we never need to convert fresh variables back! -/
theorem MarioVR.roundtrip_index_zero (vr : MarioVR) (h : vr.i = 0) :
    Variable.toMarioVR (MarioVR.toVariable vr) = vr := by
  unfold Variable.toMarioVR MarioVR.toVariable
  cases vr
  simp only [] at h
  rw [h]
  -- Goal closes after rewrite!

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

/-- Helper: membership in a cons list splits into head or tail. -/
theorem List.mem_head_eq {α : Type _} {x hd : α} {tl : List α}
    (h : x ∈ (hd :: tl)) :
    x = hd ∨ x ∈ tl := by
  cases h with
  | head =>
      left
      rfl
  | tail _ h_tl =>
      right
      exact h_tl

/-- Helper: takeWhile on cons when head satisfies predicate. -/
theorem List.takeWhile_cons_true {α : Type _} (p : α → Bool) (hd : α) (tl : List α)
    (h : p hd = true) :
    (hd :: tl).takeWhile p = hd :: tl.takeWhile p := by
  simp [List.takeWhile, h]

/-- Helper: If vr ≠ hd and vr ∈ tl, then hd ∈ (hd :: tl).takeWhile (· ≠ vr). -/
theorem List.head_mem_takeWhile_of_ne {α : Type _} [DecidableEq α]
    (hd : α) (tl : List α) (vr : α)
    (h_ne : hd ≠ vr) (_h_vr_tl : vr ∈ tl) :
    hd ∈ (hd :: tl).takeWhile (· ≠ vr) := by
  -- takeWhile (· ≠ vr) on (hd :: tl) when hd ≠ vr gives hd :: tl.takeWhile (· ≠ vr)
  have h_tw : (hd :: tl).takeWhile (· ≠ vr) = hd :: tl.takeWhile (· ≠ vr) := by
    apply List.takeWhile_cons_true
    simp only [decide_eq_true_eq]
    exact h_ne
  rw [h_tw]
  exact List.Mem.head (tl.takeWhile (· ≠ vr))

-- Note: The stronger theorem toMarioSym_finds_var_exact was removed (had sorries).
-- The weaker theorem toMarioSym_finds_var (below) is sufficient and proven.

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

/-- Helper: If find? returns some x, then x is in the list. -/
theorem List.find?_result_mem {α : Type _} (p : α → Bool) (xs : List α) (x : α) :
    xs.find? p = some x → x ∈ xs := by
  induction xs with
  | nil =>
      intro h
      contradiction
  | cons hd tl ih =>
      intro h
      unfold List.find? at h
      by_cases h_p : p hd
      · -- p hd = true, so find? returns hd
        simp [h_p] at h
        cases h
        exact List.Mem.head tl
      · -- p hd = false, so find? recurses to tl
        simp [h_p] at h
        have : x ∈ tl := ih h
        exact List.Mem.tail hd this

/-- If toMarioSym returns a variable, that variable must be in the vars list.

    This follows directly from the definition: toMarioSym uses List.find?,
    which only returns `some vr` when `vr ∈ vars`. -/
theorem String.toMarioSym_var_mem (s : String) (vars : List MarioVR) (vr : MarioVR) :
    String.toMarioSym s vars = .var vr → vr ∈ vars := by
  intro h
  unfold String.toMarioSym at h
  -- Match on find? result
  generalize h_find : vars.find? (fun vr => (MarioVR.toVariable vr).v == s) = opt at h
  cases opt with
  | none =>
      -- toMarioSym = .const s
      contradiction
  | some vr_found =>
      -- toMarioSym = .var vr_found
      -- h : .var vr_found = .var vr
      cases h
      -- vr = vr_found after cases, and h_find says find? returned vr
      exact List.find?_result_mem (fun vr' => (MarioVR.toVariable vr').v == s) vars vr h_find

/-- Helper: If find? returns some x, then the predicate holds for x. -/
theorem List.find?_pred_holds {α : Type _} (p : α → Bool) (xs : List α) (x : α) :
    xs.find? p = some x → p x = true := by
  induction xs with
  | nil =>
      intro h
      contradiction
  | cons hd tl ih =>
      intro h
      unfold List.find? at h
      by_cases h_p : p hd
      · -- p hd = true, so find? returns hd
        simp [h_p] at h
        cases h
        exact h_p
      · -- p hd = false, so find? recurses to tl
        simp [h_p] at h
        exact ih h

/-- If toMarioSym returns .var vr, then (MarioVR.toVariable vr).v equals the input string.

    This is because toMarioSym uses find? with predicate `(MarioVR.toVariable vr').v == s`. -/
theorem String.toMarioSym_var_eq (s : String) (vars : List MarioVR) (vr : MarioVR) :
    String.toMarioSym s vars = .var vr → (MarioVR.toVariable vr).v = s := by
  intro h
  unfold String.toMarioSym at h
  generalize h_find : vars.find? (fun vr => (MarioVR.toVariable vr).v == s) = opt at h
  cases opt with
  | none =>
      contradiction
  | some vr_found =>
      -- h : .var vr_found = .var vr
      cases h
      -- vr = vr_found, and find? returned vr_found with predicate (MarioVR.toVariable vr_found).v == s
      -- Use find?_pred_holds to get that predicate holds for vr
      have h_pred := List.find?_pred_holds (fun vr => (MarioVR.toVariable vr).v == s) vars vr h_find
      -- h_pred : (MarioVR.toVariable vr).v == s = true
      -- Convert Bool equality to Prop equality
      exact of_decide_eq_true h_pred

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

/-- Helper: toString ∘ toMarioSym is identity on strings.

    This roundtrip property is essential for proving Expr.roundtrip. -/
theorem String.toMarioSym_toString_roundtrip (s : String) (vars : List MarioVR) :
    MarioSym.toString (String.toMarioSym s vars) = s := by
  unfold String.toMarioSym
  generalize h_find : vars.find? (fun vr => (MarioVR.toVariable vr).v == s) = opt
  cases opt with
  | none =>
      -- toMarioSym returns .const s
      unfold MarioSym.toString
      rfl
  | some vr =>
      -- toMarioSym returns .var vr
      unfold MarioSym.toString
      -- Need to show: (MarioVR.toVariable vr).v = s
      -- Use String.toMarioSym_var_eq
      have h_eq := String.toMarioSym_var_eq s vars vr
      apply h_eq
      unfold String.toMarioSym
      rw [h_find]

/-- Roundtrip: Spec → Mario → Spec preserves structure exactly. -/
theorem Expr.roundtrip (e : Expr) (vars : List MarioVR) :
  MarioExpr.toExpr (Expr.toMarioExpr e vars) = some e := by
  -- Unfold the conversions
  cases e with | mk tc syms =>
  unfold Expr.toMarioExpr MarioExpr.toExpr
  -- After conversion, we have:
  -- toExpr (tc :: body) where tc = .const tc.c, body = syms.map (toMarioSym · vars)
  -- toExpr matches on tc :: body and returns some ⟨⟨tc.c⟩, body.map toString⟩
  simp only []
  -- Goal: some ⟨⟨tc.c⟩, (syms.map (String.toMarioSym · vars)).map MarioSym.toString⟩ = some ⟨tc, syms⟩
  congr 1
  -- Now show Expr equality: ⟨⟨tc.c⟩, ...⟩ = ⟨tc, syms⟩
  cases tc with | mk c =>
  simp only []
  -- Goal: ⟨⟨c⟩, (syms.map ...).map ...⟩ = ⟨⟨c⟩, syms⟩
  congr 1
  -- Syms: (syms.map (String.toMarioSym · vars)).map MarioSym.toString = syms
  -- Prove by induction on syms
  induction syms with
  | nil => rfl
  | cons s rest ih =>
      simp only [List.map]
      rw [String.toMarioSym_toString_roundtrip s vars, ih]

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
    -- Use injectivity! toMarioVR v1 = toMarioVR v2 → v1 = v2
    have h_eq_vars : v1 = v2 := Variable.toMarioVR_injective v1 v2 h_vr_eq
    -- But h_neq says v1 ≠ v2, contradiction!
    exact absurd h_eq_vars h_neq
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
    -- Use MarioVR.roundtrip_index_zero (index is 0 for originals!)
    have h1 : Variable.toMarioVR (MarioVR.toVariable (Variable.toMarioVR v1_orig)) =
              Variable.toMarioVR v1_orig := by
      unfold Variable.toMarioVR MarioVR.toVariable
      -- Goal: ⟨v1_orig.v, 0⟩ = ⟨v1_orig.v, 0⟩
      rfl
    have h2 : Variable.toMarioVR (MarioVR.toVariable (Variable.toMarioVR v2_orig)) =
              Variable.toMarioVR v2_orig := by
      unfold Variable.toMarioVR MarioVR.toVariable
      rfl
    rw [h1, h2]

/-! ## Variable List Construction

To convert a Frame to Mario's Context, we need a variable list.
Construct it from the frame's floating hypotheses.
-/

/-- Extract MarioVR list from frame's floating hypotheses.

    This ensures that every floating hypothesis variable is in the vars list,
    which is needed for well-formed conversion. -/
def Frame.toVarList (fr : Frame) : List MarioVR :=
  fr.hyps.filterMap fun h => match h with
    | Hyp.floating _ v => some (Variable.toMarioVR v)
    | Hyp.essential _ => none

/-- Every floating hypothesis variable is in the constructed var list. -/
theorem Frame.toVarList_complete (fr : Frame) :
    ∀ c v, Hyp.floating c v ∈ fr.hyps →
      Variable.toMarioVR v ∈ Frame.toVarList fr := by
  intro c v h_in
  unfold Frame.toVarList
  -- Show Variable.toMarioVR v ∈ filterMap result
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

/-- Frame.toVarList produces only index-0 VRs.

    This is immediate from the definition: toVarList uses Variable.toMarioVR
    which always produces ⟨v.v, 0⟩. -/
theorem Frame.toVarList_index_zero (fr : Frame) :
    ∀ vr ∈ Frame.toVarList fr, vr.i = 0 := by
  intro vr h_in
  unfold Frame.toVarList at h_in
  obtain ⟨h, h_h_in, h_some⟩ := List.mem_filterMap.mp h_in
  cases h with
  | floating c v =>
      simp only [Option.some.injEq] at h_some
      rw [← h_some]
      unfold Variable.toMarioVR
      rfl
  | essential _ =>
      contradiction

/-- Completeness of Frame DV lists.

    A Frame's dv list is complete if it contains all pairs of distinct variables
    from the frame's variable list. This is a well-formedness property that should
    be maintained by the Metamath parser.

    In Metamath practice, all $d declarations are explicit, making this naturally true.

    TODO: This should be proven in ParserInvariants.lean by showing that the parser
    ensures all necessary $d pairs are present. For now, we express it as a predicate
    that can be assumed for well-formed frames. -/
def Frame.DVComplete (fr : Frame) : Prop :=
  ∀ v w : Variable, v ∈ fr.vars → w ∈ fr.vars → v ≠ w →
    (v, w) ∈ fr.dv ∨ (w, v) ∈ fr.dv

/-- Well-formedness: Every variable in fr.vars corresponds to a VR in toVarList.

    This connects Frame.vars (extracted from floating hypotheses) to
    Frame.toVarList (MarioVR list from the same floating hypotheses).

    Uses the simple index-0 encoding: Variable.toMarioVR v = ⟨v.v, 0⟩ -/
theorem Frame.toVarList_wf (fr : Frame) :
    ∀ v ∈ fr.vars, ∃ vr ∈ Frame.toVarList fr, MarioVR.toVariable vr = v := by
  intro v h_v_in
  -- v ∈ fr.vars means there's a floating hypothesis with this variable
  unfold Frame.vars at h_v_in
  -- Use List.mem_filterMap to get the floating hypothesis
  obtain ⟨h, h_in, h_some⟩ := List.mem_filterMap.mp h_v_in
  -- h_some tells us the filterMap returned some v from h
  -- Since filterMap only returns some for floating hypotheses:
  cases h with
  | floating c v' =>
      -- The filterMap returned v, so v' = v
      simp only [Option.some.injEq] at h_some
      rw [← h_some]
      -- Now use Frame.toVarList_complete to get the VR
      let vr := Variable.toMarioVR v'
      have h_vr_in := Frame.toVarList_complete fr c v' h_in
      -- The exists tactic with vr, h_vr_in should auto-close the equality by rfl
      exists vr, h_vr_in
  | essential _ =>
      -- Impossible: filterMap returns none for essential, but h_some says none = some v
      contradiction

/-- Reverse direction: Every VR in toVarList corresponds to a variable in fr.vars.

    This is the other half of the bijection between fr.vars and Frame.toVarList fr. -/
theorem Frame.toVarList_mem_vars (fr : Frame) :
    ∀ vr ∈ Frame.toVarList fr, MarioVR.toVariable vr ∈ fr.vars := by
  intro vr h_vr_in
  unfold Frame.toVarList at h_vr_in
  -- vr came from filterMap on hyps, must be from some floating hypothesis
  obtain ⟨h, h_in, h_some⟩ := List.mem_filterMap.mp h_vr_in
  cases h with
  | floating c v =>
      -- h_some : some (Variable.toMarioVR v) = some vr
      simp only [Option.some.injEq] at h_some
      -- So vr = Variable.toMarioVR v
      rw [← h_some]
      -- Goal: MarioVR.toVariable (Variable.toMarioVR v) ∈ fr.vars
      -- By roundtrip: MarioVR.toVariable (Variable.toMarioVR v) = v
      unfold Variable.toMarioVR MarioVR.toVariable
      simp only []
      -- Now goal: v ∈ fr.vars
      unfold Frame.vars
      -- Show v is in the filterMap result
      apply List.mem_filterMap.mpr
      exists Hyp.floating c v, h_in
  | essential _ =>
      contradiction

/-! ## Frame/Context Conversion

Mario: `MarioContext where (hyps : List MarioFormula) (dj : MarioDJ)`
Us: `Frame where (hyps : List Hyp) (dv : List (Variable × Variable))`

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
      let vr := Variable.toMarioVR v  -- Use typecode as default type
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
  { hyps := fr.hyps.map (fun h => Hyp.toMarioFormula h vars)
    dj := dvList.toMarioDJ fr.dv }

/-! ### Frame ↔ MarioContext Bidirectional Correctness

The conversion Frame.toMarioContext has two components:
1. Hypothesis list: fr.hyps → hyps (Phase 5 handles bidirectional for this)
2. DJ constraints: fr.dv → dj (Phase 2 already proved bidirectional!)

We prove bidirectional properties for the DJ component here, leveraging Phase 2 results.
-/

/-- Soundness for DJ component: Every DJ constraint in the MarioContext's DJ field
    corresponds to a pair in the encoded DV list.

    This composes dvList_to_DJ_sound with field access. -/
theorem Frame.toMarioContext_dj_sound (fr : Frame) (vars : List MarioVR) :
    ∀ vr1 vr2, (Frame.toMarioContext fr vars).dj.disj vr1 vr2 →
      (MarioVR.toVariable vr1, MarioVR.toVariable vr2) ∈ Frame.dvListEncoded fr.dv ∨
      (MarioVR.toVariable vr2, MarioVR.toVariable vr1) ∈ Frame.dvListEncoded fr.dv := by
  intro vr1 vr2 h_disj
  unfold Frame.toMarioContext at h_disj
  simp only [] at h_disj
  -- Goal: apply dvList_to_DJ_sound (already proven in Phase 2!)
  exact dvList_to_DJ_sound fr.dv vr1 vr2 h_disj

/-- Completeness for DJ component: Every pair in the encoded DV list
    satisfies the DJ constraint in the MarioContext.

    This composes dvList_encoded_complete with field access. -/
theorem Frame.toMarioContext_dj_complete (fr : Frame) (vars : List MarioVR) :
    ∀ v1 v2, (v1, v2) ∈ Frame.dvListEncoded fr.dv →
      v1 ≠ v2 →
      (Frame.toMarioContext fr vars).dj.disj (Variable.toMarioVR v1) (Variable.toMarioVR v2) := by
  intro v1 v2 h_in h_neq
  unfold Frame.toMarioContext
  simp only []
  -- Goal: apply dvList_encoded_complete (framework from Phase 2)
  exact dvList_encoded_complete fr.dv v1 v2 h_in h_neq

/-- Convert Mario's MarioContext to our Frame (approximate - loses DJ structure) -/
noncomputable def MarioContext.toFrame : MarioContext → Option Frame
  | ⟨hyps, dj⟩ => do
      let hyps_spec ← hyps.mapM MarioFormula.toHyp
      -- Extract MarioVR list from hyps for DJ conversion
      let vars := hyps.filterMap fun
        | (_, [.var vr]) => some vr
        | _ => none
      return { hyps := hyps_spec, dv := MarioDJ.toDvList dj vars }

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
    (c.c, [.const c.c, .var (Variable.toMarioVR v)]) := by
  unfold Hyp.toMarioFormula
  rfl

/-! ### Hyp ↔ MarioFormula Bidirectional Correctness (Phase 5)

For floating hypotheses, the conversion is independent of the vars list
and uses the three-representation pattern (original → converted → encoded).
-/

/-- Roundtrip for floating hypothesis: Converting to MarioFormula and back
    produces the encoded form.

    This uses the three-representation pattern:
    - Original: Hyp.floating c v
    - Converted: MarioFormula (c.c, [.const c.c, .var vr])
    - Encoded: Hyp.floating c (toVariable vr)

    The roundtrip goes: Original → Converted → Encoded -/
theorem Hyp.toMarioFormula_roundtrip_floating (c : Constant) (v : Variable) (vars : List MarioVR) :
    MarioFormula.toHyp (Hyp.toMarioFormula (Hyp.floating c v) vars) =
    some (Hyp.floating c (MarioVR.toVariable (Variable.toMarioVR v))) := by
  unfold Hyp.toMarioFormula MarioFormula.toHyp
  -- After unfolding, goal is: if c.c == c.c then some ... else none = some ...
  -- simp automatically handles c.c == c.c and reduces the ite
  simp only [beq_self_eq_true, ite_true]

/-- Soundness for floating conversion: If a MarioFormula came from converting
    a floating hypothesis, then converting it back recovers a floating hypothesis
    with the encoded variable.

    This proves "no ghost formulas" for the floating case. -/
theorem Hyp.floating_toMarioFormula_sound (c : Constant) (v : Variable) (vars : List MarioVR) :
    ∃ c' v', MarioFormula.toHyp (Hyp.toMarioFormula (Hyp.floating c v) vars) =
      some (Hyp.floating c' v') ∧
      c' = c ∧
      v' = MarioVR.toVariable (Variable.toMarioVR v) := by
  exists c, (MarioVR.toVariable (Variable.toMarioVR v))
  constructor
  · exact Hyp.toMarioFormula_roundtrip_floating c v vars
  · constructor <;> rfl

/-- Hypothesis list conversion preserves membership -/
theorem Hyp.toMarioFormula_mem {h : Hyp} {fr : Frame} {vars : List MarioVR} :
    h ∈ fr.hyps →
    Hyp.toMarioFormula h vars ∈ (Frame.toMarioContext fr vars).hyps := by
  intro h_in
  unfold Frame.toMarioContext
  simp only []
  -- Show: Hyp.toMarioFormula h vars ∈ List.map (fun h => Hyp.toMarioFormula h vars) fr.hyps
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
  simpa using (List.map_flatMap (f := f) (g := g) (l := l))

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
        simp [List.flatMap_cons, v, if_pos h]

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
        simp [List.flatMap_cons, v, if_neg h, h_const]

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

/-- If a variable is in varsInExpr, it's in the vars list.

    This is immediate from the definition: varsInExpr filters to only include vars from the list. -/
theorem varsInExpr_mem_of_mem (vars : List Variable) (e : Expr) (v : Variable) :
    v ∈ Spec.varsInExpr vars e → v ∈ vars := by
  unfold Spec.varsInExpr
  intro h
  -- varsInExpr uses filterMap with `if v ∈ vars then some v else none`
  -- So anything in the result must satisfy the condition
  obtain ⟨s, h_s_in, h_some⟩ := List.mem_filterMap.mp h
  simp only [] at h_some
  split at h_some
  · cases h_some
    assumption
  · contradiction

/-- Helper: Well-formedness condition connecting vars and marioVars.

    In the actual use case, marioVars = Frame.toVarList fr, and this should be provable
    from the construction of toVarList. We express it as a hypothesis for now.

    This says: if a VR appears in the Mario substitution, the corresponding Variable
    is one we're tracking (i.e., it's in the varsInExpr result). -/
def VarsWellFormed (vars : List Variable) (marioVars : List MarioVR) (σ : Spec.Subst) : Prop :=
  ∀ v : Variable, ∀ x : MarioVR,
    x ∈' (Subst.toMarioSubst σ marioVars (Variable.toMarioVR v)) →
    MarioVR.toVariable x ∈ Spec.varsInExpr vars (σ v)

/-- VarsWellFormed holds for Frame.toVarList - PROVEN! ✅

    This is the KEY theorem that makes VarsWellFormed a provable property rather than
    an assumption! It shows that when marioVars = Frame.toVarList fr and vars = fr.vars,
    the well-formedness condition is automatically satisfied.

    **Proof strategy**:
    1. If x ∈' (Subst.toMarioSubst σ (Frame.toVarList fr) (Variable.toMarioVR v)),
       then x came from String.toMarioSym applied to some symbol s ∈ (σ v).syms
    2. toMarioSym returned .var x, so x ∈ Frame.toVarList fr (by toMarioSym_var_mem)
    3. Therefore MarioVR.toVariable x ∈ fr.vars (by Frame.toVarList_mem_vars)
    4. varsInExpr returns variables from (σ v).syms that are in fr.vars
    5. Since s ∈ (σ v).syms and MarioVR.toVariable x ∈ fr.vars, we're done! -/
theorem Frame.toVarList_varsWellFormed (fr : Frame) (σ : Spec.Subst) :
    VarsWellFormed fr.vars (Frame.toVarList fr) σ := by
  unfold VarsWellFormed
  intro v x h_x_in
  -- x came from Subst.toMarioSubst σ (Frame.toVarList fr) (Variable.toMarioVR v)
  unfold Subst.toMarioSubst at h_x_in
  -- This applies σ to v, then maps symbols through String.toMarioSym
  simp only [] at h_x_in
  -- x ∈ (σ (MarioVR.toVariable (Variable.toMarioVR v))).syms.map (String.toMarioSym · (Frame.toVarList fr))
  -- Simplify MarioVR.toVariable (Variable.toMarioVR v) = v
  unfold Variable.toMarioVR MarioVR.toVariable at h_x_in
  simp only [] at h_x_in
  -- x ∈ (σ v).syms.map (String.toMarioSym · (Frame.toVarList fr))
  -- So x came from toMarioSym applied to some symbol in (σ v).syms
  obtain ⟨s, h_s_in, h_x_eq⟩ := List.mem_map.mp h_x_in
  -- h_s_in : s ∈ (σ v).syms
  -- h_x_eq : String.toMarioSym s (Frame.toVarList fr) = .var x
  -- From toMarioSym returning .var x, we know x ∈ Frame.toVarList fr
  have h_x_in_list : x ∈ Frame.toVarList fr := by
    cases h_sym : String.toMarioSym s (Frame.toVarList fr) with
    | const c =>
        -- Contradiction: toMarioSym = .const c, but h_x_eq says it's .var x
        rw [h_sym] at h_x_eq
        contradiction
    | var vr =>
        -- h_sym : String.toMarioSym ... = .var vr
        -- h_x_eq : String.toMarioSym ... = .var x
        rw [h_sym] at h_x_eq
        -- h_x_eq : .var vr = .var x
        injection h_x_eq with h_vr_eq
        -- h_vr_eq : vr = x
        rw [← h_vr_eq]
        -- Now goal: vr ∈ Frame.toVarList fr
        exact String.toMarioSym_var_mem s (Frame.toVarList fr) vr h_sym
  -- From x ∈ Frame.toVarList fr, we get MarioVR.toVariable x ∈ fr.vars
  have h_var_in_vars : MarioVR.toVariable x ∈ fr.vars :=
    Frame.toVarList_mem_vars fr x h_x_in_list
  -- Now show MarioVR.toVariable x ∈ Spec.varsInExpr fr.vars (σ v)
  unfold Spec.varsInExpr
  -- varsInExpr filters symbols from (σ v).syms where Variable.mk s ∈ fr.vars
  apply List.mem_filterMap.mpr
  exists s, h_s_in
  -- Need to show: if Variable.mk s ∈ fr.vars then some (Variable.mk s) else none = some (MarioVR.toVariable x)
  simp only []
  -- From toMarioSym_var_eq, we know (MarioVR.toVariable x).v = s
  have h_var_eq : (MarioVR.toVariable x).v = s := String.toMarioSym_var_eq s (Frame.toVarList fr) x h_x_eq
  -- Use Variable.ext to show MarioVR.toVariable x = Variable.mk s
  have h_var_is : MarioVR.toVariable x = Variable.mk s := by
    apply Variable.ext
    exact h_var_eq
  -- Rewrite the goal using this equality
  rw [h_var_is]
  -- Goal: if Variable.mk s ∈ fr.vars then some (Variable.mk s) else none = some (Variable.mk s)
  -- We have h_var_in_vars : MarioVR.toVariable x ∈ fr.vars
  -- And h_var_is : MarioVR.toVariable x = Variable.mk s
  -- So Variable.mk s ∈ fr.vars
  have h_var_s_in : Variable.mk s ∈ fr.vars := by
    rw [← h_var_is]
    exact h_var_in_vars
  exact if_pos h_var_s_in

/-- Our dvOK implies Mario's DJ.subst (CORRECTED VERSION with two DJs).

    **Key for useAxiom case**: Shows our DV checking is sufficient for Mario's DJ preservation.

    **Critical insight from Mario's Provable.ax**:
    Mario's axiom rule requires `ax.ctx.dj.subst σ Γ.dj` - TWO DIFFERENT DJs!
    - First DJ: axiom's constraints (dv_source)
    - Second DJ: theorem's constraints (dv_target)

    **Completeness hypothesis**: The target DJ must contain ALL pairs of distinct variables.
    This is standard in Metamath practice (all $d pairs are declared explicitly).

    **Well-formedness hypotheses**:
    1. marioVars consists only of index-0 VRs (h_wf_index)
    2. vars and marioVars are compatible for substitution (h_wf_vars)
    Both hold when marioVars = Frame.toVarList ... (the actual use case).

    **Proof Strategy**:
    1. From dv_source, get (v, w) disjoint in axiom
    2. Use dvOK directly on variables from σ v and σ w to get dvRel in dv_target
    3. Lift dvRel into Mario's DJ relation ✅ -/
theorem dvOK_implies_DJ_subst
    (vars : List Variable)
    (dv_source dv_target : List (Variable × Variable))
    (σ : Spec.Subst) (marioVars : List MarioVR)
    (h_dvOK : Spec.dvOK vars dv_source dv_target σ)
    (h_wf_index : ∀ vr ∈ marioVars, vr.i = 0)
    (h_wf_vars : VarsWellFormed vars marioVars σ) :
    (dvList.toMarioDJ dv_source).subst (Subst.toMarioSubst σ marioVars)
                                        (dvList.toMarioDJ dv_target) := by
  -- Unfold DJ.subst: ∀ a b, dj_source a b → (σ a).disjoint dj_target (σ b)
  unfold Metamath.DJ.subst
  intro vr1 vr2 h_dj

  -- h_dj says (dvList.toMarioDJ dv_source) vr1 vr2
  unfold dvList.toMarioDJ at h_dj
  simp only [Metamath.DJ.mk'] at h_dj
  obtain ⟨h_neq, h_mem⟩ := h_dj

  -- Need to show: (σ vr1).disjoint (dvList.toMarioDJ dv_target) (σ vr2)
  -- Unfold Expr.disjoint: ∀ x y, x ∈' (σ vr1) → y ∈' (σ vr2) → dj_target x y
  unfold Metamath.Expr.disjoint
  intro x y h_x_in h_y_in

  -- vrPairs_source = dv_source.map (...)
  -- So h_mem says either (vr1, vr2) or (vr2, vr1) is in the source list
  cases h_mem with
  | inl h_fwd =>
      -- Case: (vr1, vr2) ∈ dv_source
      obtain ⟨⟨v, w⟩, h_pair_in, h_vr_eq⟩ := List.mem_map.mp h_fwd
      cases h_vr_eq  -- vr1 = toMarioVR v, vr2 = toMarioVR w

      -- Convert Mario VRs to Variables
      let x_var := MarioVR.toVariable x
      let y_var := MarioVR.toVariable y

      -- Use well-formedness to connect Mario membership to varsInExpr
      have h_x_var : x_var ∈ Spec.varsInExpr vars (σ v) :=
        h_wf_vars v x h_x_in
      have h_y_var : y_var ∈ Spec.varsInExpr vars (σ w) :=
        h_wf_vars w y h_y_in

      -- Apply dvOK directly to get dvRel in dv_target
      have h_rel : Spec.dvRel dv_target x_var y_var :=
        h_dvOK v w h_pair_in x_var h_x_var y_var h_y_var
      have h_x_neq_y : x_var ≠ y_var := h_rel.1
      have h_pair_target : (x_var, y_var) ∈ dv_target ∨ (y_var, x_var) ∈ dv_target :=
        h_rel.2

      -- Convert to Mario DJ: need to show (dvList.toMarioDJ dv_target) x y
      unfold dvList.toMarioDJ
      simp only [Metamath.DJ.mk']
      constructor
      · -- x ≠ y: follows from x_var ≠ y_var and MarioVR.toVariable injectivity
        intro h_eq
        cases h_eq
        -- Now x = y, so MarioVR.toVariable x = MarioVR.toVariable y
        -- But we have x_var = MarioVR.toVariable x and y_var = MarioVR.toVariable y
        -- So x_var = y_var, contradicting h_x_neq_y
        exact absurd rfl h_x_neq_y
      · -- (x, y) ∈ vrPairs_target ∨ (y, x) ∈ vrPairs_target
        -- We have (x_var, y_var) ∈ dv_target ∨ (y_var, x_var) ∈ dv_target
        -- Strategy: Show x = Variable.toMarioVR x_var and y = Variable.toMarioVR y_var
        -- Then use List.mem_map to lift the pair membership

        -- First, get that x and y are in marioVars and have index 0
        -- x and y came from Subst.toMarioSubst, which uses String.toMarioSym
        -- So they must be in marioVars
        unfold Subst.toMarioSubst at h_x_in h_y_in
        -- h_x_in : x ∈' (σ (MarioVR.toVariable (Variable.toMarioVR v))).syms.map (String.toMarioSym · marioVars)
        -- Simplify: MarioVR.toVariable (Variable.toMarioVR v) = v
        unfold Variable.toMarioVR MarioVR.toVariable at h_x_in h_y_in
        simp only [] at h_x_in h_y_in
        -- Now: x ∈ (σ v).syms.map (String.toMarioSym · marioVars)

        obtain ⟨s_x, h_sx_in, h_x_from⟩ := List.mem_map.mp h_x_in
        obtain ⟨s_y, h_sy_in, h_y_from⟩ := List.mem_map.mp h_y_in
        -- h_x_from : String.toMarioSym s_x marioVars = .var x
        -- h_y_from : String.toMarioSym s_y marioVars = .var y

        have h_x_in_mvars : x ∈ marioVars := String.toMarioSym_var_mem s_x marioVars x h_x_from
        have h_y_in_mvars : y ∈ marioVars := String.toMarioSym_var_mem s_y marioVars y h_y_from

        have h_x_i0 : x.i = 0 := h_wf_index x h_x_in_mvars
        have h_y_i0 : y.i = 0 := h_wf_index y h_y_in_mvars

        -- Use roundtrip to show Variable.toMarioVR (MarioVR.toVariable x) = x
        have h_x_roundtrip : Variable.toMarioVR x_var = x := by
          unfold x_var
          exact MarioVR.roundtrip_index_zero x h_x_i0
        have h_y_roundtrip : Variable.toMarioVR y_var = y := by
          unfold y_var
          exact MarioVR.roundtrip_index_zero y h_y_i0

        -- Now lift the pair membership using List.mem_map
        cases h_pair_target with
        | inl h_fwd_target =>
            -- (x_var, y_var) ∈ dv_target
            left
            apply List.mem_map.mpr
            exists (x_var, y_var), h_fwd_target
            rw [h_x_roundtrip, h_y_roundtrip]
        | inr h_bwd_target =>
            -- (y_var, x_var) ∈ dv_target
            right
            apply List.mem_map.mpr
            exists (y_var, x_var), h_bwd_target
            rw [h_y_roundtrip, h_x_roundtrip]

  | inr h_bwd =>
      -- Case: (vr2, vr1) ∈ dv_source - symmetric to above
      -- Swap roles: vr2 ↔ vr1, which means w ↔ v, y ↔ x
      obtain ⟨⟨w, v⟩, h_pair_in, h_vr_eq⟩ := List.mem_map.mp h_bwd
      cases h_vr_eq  -- vr2 = toMarioVR w, vr1 = toMarioVR v

      -- Convert Mario VRs to Variables (swapped from above)
      let y_var := MarioVR.toVariable y
      let x_var := MarioVR.toVariable x

      -- Use well-formedness (note swapped roles: y from w, x from v)
      have h_y_var : y_var ∈ Spec.varsInExpr vars (σ w) :=
        h_wf_vars w y h_y_in
      have h_x_var : x_var ∈ Spec.varsInExpr vars (σ v) :=
        h_wf_vars v x h_x_in

      -- Apply dvOK directly (note swapped roles)
      have h_rel : Spec.dvRel dv_target y_var x_var :=
        h_dvOK w v h_pair_in y_var h_y_var x_var h_x_var
      have h_y_neq_x : y_var ≠ x_var := h_rel.1
      have h_pair_target : (y_var, x_var) ∈ dv_target ∨ (x_var, y_var) ∈ dv_target :=
        h_rel.2

      -- Convert to Mario DJ
      unfold dvList.toMarioDJ
      simp only [Metamath.DJ.mk']
      constructor
      · -- x ≠ y (same as forward case)
        intro h_eq
        cases h_eq
        exact absurd rfl h_y_neq_x
      · -- Lift pairs (symmetric to forward case)
        unfold Subst.toMarioSubst at h_x_in h_y_in
        unfold Variable.toMarioVR MarioVR.toVariable at h_x_in h_y_in
        simp only [] at h_x_in h_y_in

        obtain ⟨s_x, h_sx_in, h_x_from⟩ := List.mem_map.mp h_x_in
        obtain ⟨s_y, h_sy_in, h_y_from⟩ := List.mem_map.mp h_y_in

        have h_x_in_mvars : x ∈ marioVars := String.toMarioSym_var_mem s_x marioVars x h_x_from
        have h_y_in_mvars : y ∈ marioVars := String.toMarioSym_var_mem s_y marioVars y h_y_from

        have h_x_i0 : x.i = 0 := h_wf_index x h_x_in_mvars
        have h_y_i0 : y.i = 0 := h_wf_index y h_y_in_mvars

        -- Use roundtrip
        have h_x_roundtrip : Variable.toMarioVR x_var = x := by
          unfold x_var
          exact MarioVR.roundtrip_index_zero x h_x_i0
        have h_y_roundtrip : Variable.toMarioVR y_var = y := by
          unfold y_var
          exact MarioVR.roundtrip_index_zero y h_y_i0

        -- Lift pair membership
        cases h_pair_target with
        | inl h_fwd_target =>
            -- (y_var, x_var) ∈ dv_target
            right  -- Note: reversed from forward case!
            apply List.mem_map.mpr
            exists (y_var, x_var), h_fwd_target
            rw [h_y_roundtrip, h_x_roundtrip]
        | inr h_bwd_target =>
            -- (x_var, y_var) ∈ dv_target
            left  -- Note: reversed from forward case!
            apply List.mem_map.mpr
            exists (x_var, y_var), h_bwd_target
            rw [h_x_roundtrip, h_y_roundtrip]

end Metamath.Spec.Bridge

