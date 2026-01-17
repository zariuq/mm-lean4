/-
# Metamath.ParserOperations

Proofs that parser operations can be modeled as structure-preserving operations.

This connects the parser implementation (Verify.lean) to the correctness infrastructure.

## Strategy

For each parser operation (insertHyp, insertAssert, etc.), we prove that **given**
the parser has validated inputs correctly, **then** the operation maintains WellFormedDB.

The validation conditions become hypotheses that the parser must prove when calling these operations.

This bridges parser implementation → StructurePreservingOp → WellFormedDB.
-/

import Metamath.Verify
import Metamath.ParserCorrectness
import Metamath.WellFormedness
import Metamath.DBCaseAnalysis

namespace Metamath
namespace ParserOps

open Verify
open WF
open ParserCorrectness
open Std (HashSet)

/-! ## Core Lemmas

These establish the key properties needed to model parser operations as StructurePreservingOps.
-/

/-- Constructing a StructurePreservingOp for insertHyp's insert operation.
    Given parser validation, the insert of a hyp object preserves structure. -/
theorem insertHyp_insert_is_structure_preserving
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    -- Parser validation: formula is well-formed
    (h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f))
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun _ => .hyp ess f l)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: prove the object is well-formed
    cases ess with
    | false => exact h_validates.1 rfl
    | true => exact h_validates.2 rfl
  · -- h_obj_var_names_match: trivial for hyp (not a var)
    intro lbl v h_eq
    -- h_eq : (fun _ => Object.hyp ess f l) lbl = Object.var v
    -- But .hyp ≠ .var, so this is a contradiction
    cases h_eq
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-! ## Main Theorems

These show that parser operations maintain WellFormedDB by composing structure-preserving operations.
-/

/-- insertHyp maintains WellFormedDB when parser has validated inputs -/
theorem insertHyp_maintains_wf_with_validation
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser provides these guarantees:
    (h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f))
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- And insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess f l)).error? = none)
    -- Then insertHyp maintains WF:
    -- (Note: we're proving for just the insert part, not the full insertHyp with withHyps)
    : WellFormedDB (db.insert pos l (fun _ => .hyp ess f l)) := by
  -- Use the StructurePreservingOp we just constructed
  have h_struct := insertHyp_insert_is_structure_preserving db pos l ess f
    h_validates h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-- Constructing a StructurePreservingOp for insertAxiom's insert operation.
    Given parser validation, the insert of an assert object preserves structure. -/
theorem insertAxiom_insert_is_structure_preserving
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    -- Parser validation: formula and frame are well-formed, and the label is not in the frame
    (h_validates : WellFormedFormula fmla ∧ WellFormedFrame db fr ∧
      (∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l))
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun _ => .assert fmla fr l)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: prove the object is well-formed
    exact ⟨h_validates.1, h_validates.2.1, h_validates.2.2⟩
  · -- h_obj_var_names_match: trivial for assert (not a var)
    intro lbl v h_eq
    cases h_eq
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-- insertAxiom maintains WellFormedDB when parser has validated inputs -/
theorem insertAxiom_maintains_wf_with_validation
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser provides these guarantees:
    (h_validates : WellFormedFormula fmla ∧ WellFormedFrame db fr ∧
      (∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l))
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- And insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .assert fmla fr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .assert fmla fr l)) := by
  -- Use the StructurePreservingOp we just constructed
  have h_struct := insertAxiom_insert_is_structure_preserving db pos l fmla fr
    h_validates h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-- Constructing a StructurePreservingOp for insertConst operation.
    Constants have trivial validation (True). -/
theorem insertConst_is_structure_preserving
    (db : DB) (pos : Pos) (l : String)
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun _ => .const l)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: trivial for const
    trivial
  · -- h_obj_var_names_match: trivial for const (not a var)
    intro lbl v h_eq
    cases h_eq
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-- insertConst maintains WellFormedDB -/
theorem insertConst_maintains_wf
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun _ => .const l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .const l)) := by
  have h_struct := insertConst_is_structure_preserving db pos l
    h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-- Constructing a StructurePreservingOp for insertVar operation.
    Variables must satisfy the label=name invariant. -/
theorem insertVar_is_structure_preserving
    (db : DB) (pos : Pos) (l : String)
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun lbl => .var lbl)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: var requires v = label, which holds when obj lbl = .var lbl
    rfl
  · -- h_obj_var_names_match: for vars with (fun lbl => .var lbl), this is automatic
    intro lbl v h_eq
    -- h_eq : (fun lbl => Object.var lbl) lbl = Object.var v
    -- So lbl = v, which is exactly what we need!
    simp only at h_eq
    cases h_eq
    rfl
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-- insertVar maintains WellFormedDB -/
theorem insertVar_maintains_wf
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun lbl => .var lbl)).error? = none) :
    WellFormedDB (db.insert pos l (fun lbl => .var lbl)) := by
  have h_struct := insertVar_is_structure_preserving db pos l
    h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-! ## Parser Provides Witnesses

These theorems show that the parser's validation checks ensure the witnesses
required by the structure-preserving theorems above.
-/

/-- Parser's validation checks for floats ensure WellFormedFloat.

The parser checks (Verify.lean:607-612):
1. arr.size > 0 && !arr[0]!.isVar  (line 607-608)
2. arr.size == 2 && arr[1]!.isVar  (line 611-612)

These checks ensure WellFormedFloat: arr.size = 2 ∧ arr[0] is const ∧ arr[1] is var
-/
theorem parser_float_checks_imply_wellformed
    (arr : Array Sym)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : arr.size = 2 ∧ arr[1]!.isVar) :
    WellFormedFloat arr := by
  -- Extract the individual checks
  have h_size := h_second.1
  have h_not_var_0 := h_first.2
  have h_is_var_1 := h_second.2

  -- Prove WellFormedFloat: arr.size = 2 ∧ ∃ c v, arr[0]! = .const c ∧ arr[1]! = .var v
  constructor
  · -- Size = 2
    exact h_size
  · -- Existential witnesses
    -- The check !arr[0]!.isVar means arr[0]! = .const c for some c
    -- The check arr[1]!.isVar means arr[1]! = .var v for some v
    have ⟨c, h_const⟩ : ∃ c, arr[0]! = Sym.const c := by
      cases h : arr[0]! with
      | const c => exact ⟨c, rfl⟩
      | var _ =>
          exfalso
          rw [h] at h_not_var_0
          simp only [Sym.isVar] at h_not_var_0
          -- h_not_var_0 : (!true) = true
          -- ATP SUCCESS: simp can close this directly!
          simp at h_not_var_0

    have ⟨v, h_var⟩ : ∃ v, arr[1]! = Sym.var v := by
      cases h : arr[1]! with
      | var v => exact ⟨v, rfl⟩
      | const _ =>
          exfalso
          rw [h] at h_is_var_1
          simp only [Sym.isVar] at h_is_var_1
          -- h_is_var_1 : false = true
          -- ATP SUCCESS: simp can close this directly too!
          simp at h_is_var_1

    exact ⟨c, v, h_const, h_var⟩

/-- Parser's validation checks for essential formulas ensure WellFormedFormula.

The parser checks (Verify.lean:607-608):
1. arr.size > 0 && !arr[0]!.isVar  (line 607-608)

These checks ensure WellFormedFormula: arr.size > 0 ∧ arr[0] is const
-/
theorem parser_essential_checks_imply_wellformed
    (arr : Array Sym)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar) :
    WellFormedFormula arr := by
  -- Prove WellFormedFormula: arr.size > 0 ∧ ∃ c, arr[0]! = .const c
  constructor
  · -- Size > 0
    exact h_first.1
  · -- Existential witness for const
    have h_not_var_0 := h_first.2
    cases h : arr[0]! with
    | const c => exact ⟨c, rfl⟩
    | var _ =>
        exfalso
        rw [h] at h_not_var_0
        simp only [Sym.isVar] at h_not_var_0
        -- ATP SUCCESS: simp closes this too!
        simp at h_not_var_0

/-! ## Convenience Theorems

These wire the parser witness theorems directly into the structure-preserving theorems,
eliminating the abstract validation hypotheses.
-/

/-- insertHyp maintains WellFormedDB when given parser's concrete boolean checks.
    This is the convenient form that directly uses parser implementation details. -/
theorem insertHyp_maintains_wf_from_parser_checks
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser boolean checks (directly from Verify.lean:607-612):
    (h_first : f.size > 0 ∧ !f[0]!.isVar)
    (h_second : f.size = 2 ∧ f[1]!.isVar)
    -- Freshness (same as before):
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- And insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess f l)).error? = none)
    -- For float hypothesis (ess = false):
    (h_is_float : ess = false) :
    WellFormedDB (db.insert pos l (fun _ => .hyp ess f l)) := by
  -- Convert parser boolean checks to WellFormedFloat using our witness theorem
  have h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f) := by
    constructor
    · intro _
      -- Use the witness theorem we just proved!
      exact parser_float_checks_imply_wellformed f h_first h_second
    · intro h_ess_true
      -- Contradiction: we know ess = false
      rw [h_is_float] at h_ess_true
      cases h_ess_true
  -- Apply the existing theorem with the validation witness
  exact insertHyp_maintains_wf_with_validation db pos l ess f
    h_wf h_no_err_before h_validates h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Unified convenience theorem for insertHyp that handles both float and essential formulas.
    This directly uses parser's concrete boolean checks for both cases. -/
theorem insertHyp_maintains_wf_unified
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser boolean checks (Verify.lean:607-612):
    (h_first : f.size > 0 ∧ !f[0]!.isVar)
    (h_second : ess = false → (f.size = 2 ∧ f[1]!.isVar))
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Success:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess f l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .hyp ess f l)) := by
  -- Derive validation witness by case analysis on ess
  have h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f) := by
    constructor
    · intro h_ess_false
      -- Float case: use parser_float_checks_imply_wellformed
      have h_second' := h_second h_ess_false
      exact parser_float_checks_imply_wellformed f h_first h_second'
    · intro _
      -- Essential case: use parser_essential_checks_imply_wellformed
      exact parser_essential_checks_imply_wellformed f h_first
  -- Apply the existing theorem
  exact insertHyp_maintains_wf_with_validation db pos l ess f
    h_wf h_no_err_before h_validates h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Convenience theorem for insertConst - trivial since constants need no validation.
    This is just an alias for the existing theorem since no parser checks are needed. -/
theorem insertConst_maintains_wf_from_parser
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun _ => .const l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .const l)) :=
  -- No parser validation needed - constants are trivially well-formed
  insertConst_maintains_wf db pos l h_wf h_no_err_before h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Convenience theorem for insertVar - trivial since the label=name invariant is automatic.
    This is just an alias for the existing theorem since no parser checks are needed. -/
theorem insertVar_maintains_wf_from_parser
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun lbl => .var lbl)).error? = none) :
    WellFormedDB (db.insert pos l (fun lbl => .var lbl)) :=
  -- No parser validation needed - var name matches label by construction
  insertVar_maintains_wf db pos l h_wf h_no_err_before h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Convenience theorem for insertAxiom using parser's concrete checks.
    The formula validation uses parser checks; frame well-formedness is assumed for now. -/
theorem insertAxiom_maintains_wf_from_parser
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser check for formula (same as essential hypothesis):
    (h_fmla_check : fmla.size > 0 ∧ !fmla[0]!.isVar)
    -- Frame well-formedness (from trimFrame' operation):
    (h_frame_wf : WellFormedFrame db fr)
    -- Label not present in the trimmed frame:
    (h_fresh_in_frame : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l)
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Success:
    (h_insert_ok : (db.insert pos l (fun _ => .assert fmla fr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .assert fmla fr l)) := by
  -- Derive validation witness
  have h_validates : WellFormedFormula fmla ∧ WellFormedFrame db fr ∧
      (∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l) := by
    refine ⟨parser_essential_checks_imply_wellformed fmla h_fmla_check, h_frame_wf, h_fresh_in_frame⟩
  -- Apply the existing theorem
  exact insertAxiom_maintains_wf_with_validation db pos l fmla fr
    h_wf h_no_err_before h_validates h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-! ## Parser Execution

These theorems connect the convenience theorems to the actual parser execution in feedTokens.
-/

/-- The insert part of insertHyp maintains WellFormedDB.
    This is the core theorem connecting parser checks to DB well-formedness. -/
theorem insertHyp_insert_part_maintains_wf
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    -- Parser checks:
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : ess = false → (arr.size = 2 ∧ arr[1]!.isVar))
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess arr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .hyp ess arr l)) := by
  -- Direct application of our unified convenience theorem!
  exact insertHyp_maintains_wf_unified db pos l ess arr
    h_wf h_no_err h_first h_second
    h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- The insert part of insertAxiom maintains WellFormedDB.
    This is the core theorem for axiom/theorem declarations. -/
theorem insertAxiom_insert_part_maintains_wf
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    -- Parser checks:
    (h_first : fmla.size > 0 ∧ !fmla[0]!.isVar)
    -- Frame well-formedness (from trimFrame'):
    (h_frame_wf : WellFormedFrame db fr)
    -- Label not present in the trimmed frame:
    (h_fresh_in_frame : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l)
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .assert fmla fr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .assert fmla fr l)) := by
  -- Direct application of our axiom convenience theorem!
  exact insertAxiom_maintains_wf_from_parser db pos l fmla fr
    h_wf h_no_err h_first h_frame_wf h_fresh_in_frame
    h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-! ## feedTokens Correctness

This section proves that feedTokens maintains WellFormedDB for each token kind.
This is the key composition theorem connecting individual operations to parser execution.
-/

/-! ## Frame Operation Lemmas

These lemmas prove that frame operations (withHyps) preserve WellFormedDB.
-/

/-- Array.push lemmas used by withHyps proofs. -/
theorem getElem_push_lt {α : Type u} (arr : Array α) (x : α) (i : Nat)
    (h : i < arr.size) (h' : i < (arr.push x).size := by simp [Array.size_push, h]) :
    (arr.push x)[i] = arr[i] := by
  rcases arr with ⟨lst⟩
  simp [Array.push, List.getElem_append_left h]

theorem getElem_push_eq {α : Type u} (arr : Array α) (x : α)
    (h : arr.size < (arr.push x).size := by simp [Array.size_push]) :
    (arr.push x)[arr.size] = x := by
  rcases arr with ⟨lst⟩
  simp [Array.push, List.getElem_append_right (Nat.le_refl lst.length)]

/-- withHyps with push preserves WellFormedDB when adding a HypOK label and a fresh float binder. -/
theorem withHyps_push_preserves_wf
    (db : DB) (l : String)
    (h_wf : WellFormedDB db)
    (h_hypok : HypOK db l)
    -- Additional hypothesis: float variable freshness
    (h_fresh_float : ∀ (k : Nat) (hk : k < db.frame.hyps.size) (fi f_l : Formula) (lbli lbl_l : String),
      db.find? db.frame.hyps[k] = some (.hyp false fi lbli) →
      db.find? l = some (.hyp false f_l lbl_l) →
      fi.size ≥ 2 → f_l.size ≥ 2 →
      let vi := match fi[1]! with | .var v => v | _ => ""
      let vl := match f_l[1]! with | .var v => v | _ => ""
      vi ≠ vl) :
    WellFormedDB (db.withHyps (·.push l)) := by
  unfold WellFormedDB WellFormedFrame
  constructor
  · -- WellFormedFrame for new frame
    constructor
    · -- HypOK for all indices in pushed array
      intro i hi
      dsimp [DB.withHyps, DB.withFrame] at hi ⊢
      by_cases h_old : i < db.frame.hyps.size
      · -- Old hyp: use HypOK from original frame
        have hi' : i < (db.frame.hyps.push l).size := by
          exact hi
        have h_label : (db.frame.hyps.push l)[i]'hi' = db.frame.hyps[i]'h_old := by
          exact getElem_push_lt db.frame.hyps l i h_old hi'
        have h_old_ok : HypOK db (db.frame.hyps[i]'h_old) := h_wf.1.1 i h_old
        have h_old_ok' : HypOK (db.withHyps (·.push l)) (db.frame.hyps[i]'h_old) := by
          simpa [HypOK, DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_old_ok
        simpa [h_label] using h_old_ok'
      · -- New hyp: i = size
        have hi' : i < db.frame.hyps.size + 1 := by
          simpa [Array.size_push] using hi
        have h_le : i ≤ db.frame.hyps.size := Nat.le_of_lt_succ hi'
        have h_ge : db.frame.hyps.size ≤ i := Nat.le_of_not_lt h_old
        have h_eq : i = db.frame.hyps.size := Nat.le_antisymm h_le h_ge
        subst h_eq
        have hi'' : db.frame.hyps.size < (db.frame.hyps.push l).size := by
          exact hi
        have h_label : (db.frame.hyps.push l)[db.frame.hyps.size]'hi'' = l := by
          exact getElem_push_eq db.frame.hyps l hi''
        have h_new_ok : HypOK (db.withHyps (·.push l)) l := by
          simpa [HypOK, DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_hypok
        simpa [h_label] using h_new_ok
    · -- UniqueFloatVars
      unfold UniqueFloatVars
      intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sizei h_sizej
      dsimp [DB.withHyps, DB.withFrame] at hi hj h_fi h_fj ⊢
      have h_fi' :
          db.find? (db.frame.hyps.push l)[i] = some (.hyp false fi lbli) := by
        simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_fi
      have h_fj' :
          db.find? (db.frame.hyps.push l)[j] = some (.hyp false fj lblj) := by
        simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_fj
      by_cases hi_old : i < db.frame.hyps.size
      · by_cases hj_old : j < db.frame.hyps.size
        · -- Both old indices: reuse UniqueFloatVars
          have hi' : i < (db.frame.hyps.push l).size := by
            exact hi
          have hj' : j < (db.frame.hyps.push l).size := by
            exact hj
          have hi_label : (db.frame.hyps.push l)[i] = db.frame.hyps[i] := by
            exact getElem_push_lt db.frame.hyps l i hi_old hi'
          have hj_label : (db.frame.hyps.push l)[j] = db.frame.hyps[j] := by
            exact getElem_push_lt db.frame.hyps l j hj_old hj'
          have h_fi_old : db.find? db.frame.hyps[i] = some (.hyp false fi lbli) := by
            simpa [hi_label] using h_fi'
          have h_fj_old : db.find? db.frame.hyps[j] = some (.hyp false fj lblj) := by
            simpa [hj_label] using h_fj'
          exact h_wf.1.2 i j hi_old hj_old h_ne fi fj lbli lblj h_fi_old h_fj_old h_sizei h_sizej
        · -- i old, j new
          have hj' : j < db.frame.hyps.size + 1 := by
            simpa [Array.size_push] using hj
          have hj_le : j ≤ db.frame.hyps.size := Nat.le_of_lt_succ hj'
          have hj_ge : db.frame.hyps.size ≤ j := Nat.le_of_not_lt hj_old
          have hj_eq : j = db.frame.hyps.size := Nat.le_antisymm hj_le hj_ge
          subst hj_eq
          have hi' : i < (db.frame.hyps.push l).size := by
            exact hi
          have hi_label : (db.frame.hyps.push l)[i] = db.frame.hyps[i] := by
            exact getElem_push_lt db.frame.hyps l i hi_old hi'
          have h_fi_old : db.find? db.frame.hyps[i] = some (.hyp false fi lbli) := by
            simpa [hi_label] using h_fi'
          have hj'' : db.frame.hyps.size < (db.frame.hyps.push l).size := by
            exact hj
          have hj_label : (db.frame.hyps.push l)[db.frame.hyps.size] = l := by
            exact getElem_push_eq db.frame.hyps l hj''
          have h_fj_new : db.find? l = some (.hyp false fj lblj) := by
            simpa [hj_label] using h_fj'
          exact h_fresh_float i hi_old fi fj lbli lblj h_fi_old h_fj_new h_sizei h_sizej
      · -- i new
        have hi' : i < db.frame.hyps.size + 1 := by
          simpa [Array.size_push] using hi
        have hi_le : i ≤ db.frame.hyps.size := Nat.le_of_lt_succ hi'
        have hi_ge : db.frame.hyps.size ≤ i := Nat.le_of_not_lt hi_old
        have hi_eq : i = db.frame.hyps.size := Nat.le_antisymm hi_le hi_ge
        subst hi_eq
        by_cases hj_old : j < db.frame.hyps.size
        · -- i new, j old
          have hi' : db.frame.hyps.size < (db.frame.hyps.push l).size := by
            exact hi
          have hi_label : (db.frame.hyps.push l)[db.frame.hyps.size] = l := by
            exact getElem_push_eq db.frame.hyps l hi'
          have h_fi_new : db.find? l = some (.hyp false fi lbli) := by
            simpa [hi_label] using h_fi'
          have hj' : j < (db.frame.hyps.push l).size := by
            exact hj
          have hj_label : (db.frame.hyps.push l)[j] = db.frame.hyps[j] := by
            exact getElem_push_lt db.frame.hyps l j hj_old hj'
          have h_fj_old : db.find? db.frame.hyps[j] = some (.hyp false fj lblj) := by
            simpa [hj_label] using h_fj'
          have h_ne_vars :=
            h_fresh_float j hj_old fj fi lblj lbli h_fj_old h_fi_new h_sizej h_sizei
          exact h_ne_vars.symm
        · -- both new: contradiction with i ≠ j
          have hj' : j < db.frame.hyps.size + 1 := by
            simpa [Array.size_push] using hj
          have hj_le : j ≤ db.frame.hyps.size := Nat.le_of_lt_succ hj'
          have hj_ge : db.frame.hyps.size ≤ j := Nat.le_of_not_lt hj_old
          have hj_eq : j = db.frame.hyps.size := Nat.le_antisymm hj_le hj_ge
          have h_eq : db.frame.hyps.size = j := by
            simp [hj_eq]
          exact (h_ne h_eq).elim
  · -- Object well-formedness: withHyps doesn't change find?
    intro lbl obj h_find
    have h_find' : db.find? lbl = some obj := by
      simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_find
    exact h_wf.2 lbl obj h_find'

theorem floatVarOccursInFrame_false_implies
    (db : DB) (v : String)
    (h_false : db.floatVarOccursInFrame v = false)
    (k : Nat) (hk : k < db.frame.hyps.size)
    (fi : Formula) (lbli : String)
    (h_find : db.find? db.frame.hyps[k] = some (.hyp false fi lbli))
    (h_size : fi.size ≥ 2) :
    let vi := match fi[1]! with | .var v' => v' | _ => ""
    vi ≠ v := by
  let pred := fun lbl =>
    match db.find? lbl with
    | some (.hyp false prevF _) =>
        prevF.size >= 2 &&
          (match prevF[1]! with | .var v' => v' | _ => "") == v
    | _ => false
  have h_any : (db.frame.hyps.toList.any pred) = false := by
    change db.floatVarOccursInFrame v = false
    exact h_false
  have h_all : ∀ a ∈ db.frame.hyps.toList, pred a = false := by
    intro a h_mem
    have h_not_true : ¬ pred a = true := (List.any_eq_false).1 h_any a h_mem
    cases h_pred : pred a with
    | true =>
        exact (h_not_true (by simp [h_pred])).elim
    | false => rfl
  have h_mem : db.frame.hyps[k]! ∈ db.frame.hyps.toList := by
    simpa using (Array.getElem!_mem_toList db.frame.hyps k hk)
  have h_pred_false : pred (db.frame.hyps[k]!) = false := h_all _ h_mem
  have h_find' : db.find? (db.frame.hyps[k]!) = some (.hyp false fi lbli) := by
    have h_eq : db.frame.hyps[k]! = db.frame.hyps[k]'hk := by
      simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := k) (h := hk))
    simpa [h_eq] using h_find
  have h_pred_false' :
      (fi.size >= 2 && (match fi[1]! with | .var v' => v' | _ => "") == v) = false := by
    simpa [pred, h_find'] using h_pred_false
  dsimp
  have h_beq_false :
      ((match fi[1]! with | .var v' => v' | _ => "") == v) = false := by
    simpa [h_size] using h_pred_false'
  intro h_eq
  have h_beq_true :
      ((match fi[1]! with | .var v' => v' | _ => "") == v) = true := by
    exact (beq_iff_eq).2 h_eq
  have h_false : False := by
    simp [h_beq_true] at h_beq_false
  exact h_false

-- Helper: withHyps preserves error? field
theorem withHyps_preserves_error? (db : DB) (f : Array String → Array String) :
    (db.withHyps f).error? = db.error? := by
  unfold DB.withHyps DB.withFrame
  rfl

-- Helper: Relationship between error and error?
theorem error_iff_error?_isSome (db : DB) :
    db.error = true ↔ db.error? ≠ none := by
  unfold DB.error
  cases db.error? with
  | none => simp
  | some _ => simp

theorem bool_not_eq_true_iff_eq_false {b : Bool} : (!b = true) ↔ b = false := by
  cases b <;> simp

-- Helper: If insert succeeds, input must have had no error
theorem insert_success_implies_no_error
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_success : (db.insert pos l obj).error? = none) :
    db.error? = none := by
  -- insert checks: if db.error then db else ...
  -- If db.error = true, then insert returns db unchanged
  -- So if insert result has error? = none, then db.error? must be none
  cases h_db : db.error? with
  | none => rfl
  | some e =>
    -- db.error? = some e, so db.error = true
    have h_error_true : db.error = true := by
      rw [error_iff_error?_isSome]
      rw [h_db]
      simp
    -- insert preserves error when db.error = true
    have h_insert_error : (db.insert pos l obj).error = true := by
      unfold DB.insert
      split
      · -- const case
        split
        · -- error set
          unfold DB.mkError DB.error
          simp
        · -- no const error, check db.error
          simp [h_error_true]
      · -- non-const case
        simp [h_error_true]
    -- h_insert_error means (db.insert pos l obj).error? ≠ none
    rw [error_iff_error?_isSome] at h_insert_error
    -- But h_success says it equals none, contradiction
    exact absurd h_success h_insert_error

-- NOTE: Check-phase preservation lemma would go here
-- Would prove: If the head/shape/dup checks succeed (error? = none), then db is unchanged
-- For now, we document this as a blocker for insertHyp_full_maintains_wf

-- Helper lemma: Extract success conditions from insertHyp
theorem insertHyp_success_conditions
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_success : (db.insertHyp pos l ess f).error? = none) :
    ∃ (db_after_check : DB),
      -- Step 1: Head/shape/float checks passed (if applicable)
      (db_after_check = DB.insertHypChecks db pos ess f) ∧
      db_after_check.error? = none ∧
      -- Step 2: Insert succeeded
      (db_after_check.insert pos l (.hyp ess f)).error? = none := by
  -- insertHyp does: head/shape checks, float-dup check, then insert, then withHyps
  -- If final result has no error, all steps succeeded
  let db_after_check := DB.insertHypChecks db pos ess f
  have h_def' :
      DB.insertHypChecks db pos ess f = db_after_check := by
    rfl

  -- Show the check phase has no error
  have h_check_ok : db_after_check.error? = none := by
    cases h_err_opt : db_after_check.error? with
    | none => rfl
    | some _ =>
        have h_err_true : db_after_check.error = true := by
          exact (error_iff_error?_isSome db_after_check).2 (by simp [h_err_opt])
        have h_success' := h_success
        simp [DB.insertHyp, h_def', h_err_true] at h_success'
        have : False := by
          simp [h_err_opt] at h_success'
        exact False.elim this

  have h_check_err : db_after_check.error = false := by
    simp [DB.error, h_check_ok]

  -- With checks ok, insert must also be error-free
  have h_insert_ok :
      (db_after_check.insert pos l (.hyp ess f)).error? = none := by
    by_cases h_err : (db_after_check.insert pos l (.hyp ess f)).error
    · have h_err_some : (db_after_check.insert pos l (.hyp ess f)).error? ≠ none :=
        (error_iff_error?_isSome (db_after_check.insert pos l (.hyp ess f))).1 h_err
      have h_success' := h_success
      simp [DB.insertHyp, h_def', h_check_err, h_err] at h_success'
      exact False.elim (h_err_some h_success')
    · cases h_err_opt : (db_after_check.insert pos l (.hyp ess f)).error? with
      | none => rfl
      | some _ =>
          have h_err_true : (db_after_check.insert pos l (.hyp ess f)).error = true := by
            exact (error_iff_error?_isSome (db_after_check.insert pos l (.hyp ess f))).2
              (by simp [h_err_opt])
          have : False := by
            simp [h_err] at h_err_true
          exact False.elim this

  exact ⟨db_after_check, rfl, h_check_ok, h_insert_ok⟩

theorem insertHypChecks_eq_db_of_no_error
    (db : DB) (pos : Pos) (ess : Bool) (f : Formula)
    (h_no_err : (DB.insertHypChecks db pos ess f).error? = none) :
    DB.insertHypChecks db pos ess f = db := by
  unfold DB.insertHypChecks at h_no_err ⊢
  cases h_head : f.hasConstHead with
  | false =>
      have h_no_err' :
          (db.mkError pos "first symbol is not a constant").error? = none := by
        simp [h_head] at h_no_err
        exact h_no_err
      have : False := by
        simp [DB.mkError] at h_no_err'
      exact False.elim this
  | true =>
      cases h_db_err : db.error with
      | true =>
          have h_no_err' : db.error? = none := by
            simp [h_head, h_db_err] at h_no_err
            exact h_no_err
          have h_err_some : db.error? ≠ none := (error_iff_error?_isSome db).1 h_db_err
          exact False.elim (h_err_some h_no_err')
      | false =>
          cases h_ess : ess with
          | true =>
              simp [h_db_err]
          | false =>
              cases h_shape : f.isFloatShape with
              | true =>
                  by_cases h_size : f.size ≥ 2
                  · cases h_dup : db.floatVarOccursInFrame f[1]!.value with
                    | true =>
                      have h_no_err' :
                          (db.mkError pos
                            (toString "variable " ++ toString f[1]!.value ++
                              toString " already has $f hypothesis")).error? = none := by
                          simp [h_head, h_db_err, h_ess, h_shape, h_size, h_dup] at h_no_err
                          exact h_no_err
                      have : False := by
                        simp [DB.mkError] at h_no_err'
                      exact False.elim this
                    | false =>
                        simp [h_db_err, h_size, h_dup]
                  · simp [h_db_err, h_size]
              | false =>
                  have h_no_err' :
                      (db.mkError pos "expected a constant and a variable").error? = none := by
                    simp [h_head, h_db_err, h_ess, h_shape] at h_no_err
                    exact h_no_err
                  have : False := by
                    simp [DB.mkError] at h_no_err'
                  exact False.elim this

-- First, we need a helper: insertHyp (full) maintains WellFormedDB
-- This is what we need from Phase A!
theorem insertHyp_full_maintains_wf
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_wf : WellFormedDB db)
    (_h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : ess = false → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertHyp pos l ess arr).error? = none) :
    WellFormedDB (db.insertHyp pos l ess arr) := by
  -- Step 1: Extract success conditions from insertHyp
  obtain ⟨db_after_check, h_def_check, h_check_ok, h_insert_ok⟩ :=
    insertHyp_success_conditions db pos l ess arr h_success

  -- h_def_check: db_after_check = [head/shape/dup checks]
  -- h_check_ok: db_after_check.error? = none
  -- h_insert_ok: (db_after_check.insert pos l (.hyp ess arr)).error? = none

  -- Step 2: Check phase preserves the underlying db when it succeeds.
  have h_checks_no_err : (DB.insertHypChecks db pos ess arr).error? = none := by
    simpa [h_def_check] using h_check_ok

  have h_check_eq_db : db_after_check = db := by
    have h_eq := insertHypChecks_eq_db_of_no_error db pos ess arr h_checks_no_err
    simpa [h_def_check] using h_eq

  have h_wf_after_check : WellFormedDB db_after_check := by
    simpa [h_check_eq_db] using h_wf

  -- Step 3: db_after_check has the same freshness properties as db
  have h_no_err_after_check : db_after_check.error? = none := h_check_ok

  have h_fresh_db_after_check : db_after_check.find? l = none := by
    simpa [h_check_eq_db] using h_fresh_db

  have h_fresh_label_after_check :
      ∀ (i : Nat) (hi : i < db_after_check.frame.hyps.size),
        db_after_check.frame.hyps[i]'hi ≠ l := by
    simpa [h_check_eq_db] using h_fresh_label

  have h_fresh_in_asserts_after_check :
      ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db_after_check.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l := by
    intro lbl fmla fr_assert name h_find i hi
    have h_find' : db.find? lbl = some (.assert fmla fr_assert name) := by
      simpa [h_check_eq_db] using h_find
    exact h_fresh_in_asserts lbl fmla fr_assert name h_find' i hi

  have h_dup_false :
      ess = false → db_after_check.floatVarOccursInFrame arr[1]!.value = false := by
    intro h_ess
    have h_size_eq : arr.size = 2 := (h_second h_ess).1
    have h_var1 : arr[1]!.isVar = true := by
      simpa using (h_second h_ess).2
    have h_notvar0 : arr[0]!.isVar = false := by
      cases h_var0 : arr[0]!.isVar with
      | false => rfl
      | true =>
          have : False := by
            simpa [h_var0] using h_first.2
          exact False.elim this
    have h_head : Formula.hasConstHead arr = true := by
      unfold Formula.hasConstHead
      have h_pos : 0 < arr.size := by
        exact h_first.1
      cases h0 : arr[0]! with
      | const _ =>
          simp [h_pos]
      | var _ =>
          have : False := by
            simp [Sym.isVar, h0] at h_notvar0
          exact False.elim this
    have h_shape : Formula.isFloatShape arr = true := by
      unfold Formula.isFloatShape
      cases h0 : arr[0]! with
      | const _ =>
          cases h1 : arr[1]! with
          | var _ =>
              simp [h_size_eq]
          | const _ =>
              have : False := by
                simp [Sym.isVar, h1] at h_var1
              exact False.elim this
      | var _ =>
          have : False := by
            simp [Sym.isVar, h0] at h_notvar0
          exact False.elim this
    have h_size_ge : arr.size >= 2 := by
      simp [h_size_eq]
    cases h_dup' : db_after_check.floatVarOccursInFrame arr[1]!.value with
    | true =>
        have h_dup_db : db.floatVarOccursInFrame arr[1]!.value = true := by
          simp [h_check_eq_db] at h_dup'
          exact h_dup'
        have h_db_no_err : db.error? = none := by
          simp [h_check_eq_db] at h_check_ok
          exact h_check_ok
        have h_db_err : db.error = false := by
          simp [DB.error, h_db_no_err]
        have h_no_err' :
            (db.mkError pos
              (toString "variable " ++ toString arr[1]!.value ++
                toString " already has $f hypothesis")).error? = none := by
          simpa [DB.insertHypChecks, h_head, h_db_err, h_ess, h_shape, h_size_ge, h_dup_db] using h_checks_no_err
        have : False := by
          simp [DB.mkError] at h_no_err'
        exact False.elim this
    | false =>
        simp

  -- Step 4: Apply insertHyp_insert_part_maintains_wf for the insert step
  have h_wf_after_insert :
      WellFormedDB (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)) := by
    exact insertHyp_insert_part_maintains_wf db_after_check pos l ess arr
      h_wf_after_check h_no_err_after_check
      h_first h_second
      h_fresh_db_after_check h_fresh_label_after_check h_fresh_in_asserts_after_check
      h_insert_ok

  -- Step 5: Apply withHyps_push to get final result
  -- Goal: WellFormedDB ((db_after_check.insert pos l (fun _ => .hyp ess arr l)).withHyps (·.push l))

  -- Shared insert-success side conditions
  have h_not_var_dup :
      ¬(∃ v, (fun _ => Object.hyp ess arr l) l = Object.var v ∧
        db_after_check.find? l = some (Object.var v)) := by
    intro ⟨v, h_obj, _⟩
    cases h_obj

  have h_var_labels_match_names :
      ∀ lbl v, db_after_check.find? lbl = some (Object.var v) → v = lbl := by
    intro lbl v h_find
    exact h_wf_after_check.2 lbl (Object.var v) h_find

  have h_obj_var_names_match :
      ∀ lbl v, (fun _ => Object.hyp ess arr l) lbl = Object.var v → v = lbl := by
    intro lbl v h_obj
    cases h_obj

  have h_find_l_after_insert :
      (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).find? l =
        some (Object.hyp ess arr l) := by
    apply insert_success_find?_self
    · exact h_check_ok
    · exact h_insert_ok
    · exact h_not_var_dup
    · exact h_var_labels_match_names
    · exact h_obj_var_names_match

  -- First, prove HypOK for l in the database after insert
  have h_hypok_after_insert :
      HypOK (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)) l := by
    -- After insert, l maps to .hyp ess arr l
    -- Need to show this satisfies HypOK
    unfold HypOK
    -- Exists ess, arr, l such that find? returns .hyp ess arr l
    refine ⟨ess, arr, l, ?_, ?_⟩
    · -- Prove find? l = some (.hyp ess arr l)
      exact h_find_l_after_insert
    · -- And condition: if float then WellFormedFloat, if ess then WellFormedFormula
      refine ⟨?_, ?_⟩
      · -- If float (ess = false), prove WellFormedFloat arr
        intro h_float
        unfold WellFormedFloat
        -- From h_second: ess = false → arr.size = 2 ∧ arr[1]!.isVar
        have ⟨h_size, h_var⟩ := h_second h_float
        -- From h_first: arr.size > 0 ∧ !arr[0]!.isVar
        constructor
        · exact h_size
        · -- Need to extract const and var from arr
          -- arr[0]! is const (from h_first.2: !arr[0]!.isVar)
          have ⟨c, h_c⟩ : ∃ c, arr[0]! = Sym.const c := by
            cases h_arr0 : arr[0]! with
            | const c => exact ⟨c, rfl⟩
            | var _ =>
              simp only [h_arr0, Sym.isVar] at h_first
              simp at h_first
          -- arr[1]! is var (from h_var: arr[1]!.isVar)
          have ⟨v, h_v⟩ : ∃ v, arr[1]! = Sym.var v := by
            cases h_arr1 : arr[1]! with
            | var v => exact ⟨v, rfl⟩
            | const _ =>
              simp only [h_arr1, Sym.isVar] at h_var
              simp at h_var
          exact ⟨c, v, h_c, h_v⟩
      · -- If essential (ess = true), prove WellFormedFormula arr
        intro h_ess
        unfold WellFormedFormula
        constructor
        · exact h_first.1
        · -- arr[0]! is not a var (from h_first.2: !arr[0]!.isVar), so it's a const
          have ⟨c, h_c⟩ : ∃ c, arr[0]! = Sym.const c := by
            cases h_arr0 : arr[0]! with
            | const c => exact ⟨c, rfl⟩
            | var _ =>
              simp only [h_arr0, Sym.isVar] at h_first
              simp at h_first
          exact ⟨c, h_c⟩

  -- Fresh-float witness for the push step (derived from the duplicate check)
  have h_fresh_float_after_insert :
      ∀ (k : Nat)
        (hk : k < (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).frame.hyps.size)
        (fi f_l : Formula) (lbli lbl_l : String),
        (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).find?
            (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).frame.hyps[k] =
          some (Object.hyp false fi lbli) →
        (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).find? l =
          some (Object.hyp false f_l lbl_l) →
        fi.size ≥ 2 → f_l.size ≥ 2 →
        let vi := match fi[1]! with | .var v => v | _ => ""
        let vl := match f_l[1]! with | .var v => v | _ => ""
        vi ≠ vl := by
    intro k hk fi f_l lbli lbl_l h_find_k h_find_l h_sizei _h_sizel
    cases h_ess : ess with
    | true =>
        -- ess = true: h_find_l is impossible
        have h_find_l_after_insert' :
            (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).find? l =
              some (Object.hyp true arr l) := by
          simpa [h_ess] using h_find_l_after_insert
        have h_eq : some (Object.hyp false f_l lbl_l) = some (Object.hyp true arr l) := by
          exact h_find_l.symm.trans h_find_l_after_insert'
        cases h_eq
    | false =>
        -- ess = false: use floatVarOccursInFrame check
        have h_find_l' :
            (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).find? l =
              some (Object.hyp false arr l) := by
          simpa [h_ess] using h_find_l_after_insert
        have h_eq_obj : Object.hyp false f_l lbl_l = Object.hyp false arr l := by
          exact Option.some.inj (h_find_l.symm.trans h_find_l')
        cases h_eq_obj
        have hk_pre : k < db_after_check.frame.hyps.size := by
          simpa [insert_frame_unchanged] using hk
        have h_label_ne : db_after_check.frame.hyps[k] ≠ l :=
          h_fresh_label_after_check k hk_pre
        have h_find_k' :
            (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).find?
                db_after_check.frame.hyps[k] =
              some (Object.hyp false fi lbli) := by
          simpa [insert_frame_unchanged] using h_find_k
        have h_find_k_pre :
            db_after_check.find? db_after_check.frame.hyps[k] =
              some (Object.hyp false fi lbli) := by
          have h_find_k_ne :
              (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).find?
                  db_after_check.frame.hyps[k] =
                db_after_check.find? db_after_check.frame.hyps[k] := by
            exact insert_success_find?_ne db_after_check pos l (db_after_check.frame.hyps[k])
              (fun _ => Object.hyp ess arr l) h_label_ne h_check_ok h_insert_ok
              h_not_var_dup h_var_labels_match_names h_obj_var_names_match
          simpa [h_find_k_ne] using h_find_k'
        have h_vi_ne :
            let vi := match fi[1]! with | .var v => v | _ => ""
            vi ≠ arr[1]!.value := by
          exact floatVarOccursInFrame_false_implies db_after_check (arr[1]!.value)
            (h_dup_false h_ess) k hk_pre fi lbli h_find_k_pre h_sizei
        cases h_sym : arr[1]! with
        | var v_sym =>
            simpa [h_sym] using h_vi_ne
        | const _ =>
            have h_var : arr[1]!.isVar = true := by
              simpa using (h_second h_ess).2
            simp [h_sym, Sym.isVar] at h_var

  -- Now apply withHyps_push_preserves_wf
  -- Goal: WellFormedDB (db.insertHyp pos l ess arr)
  -- insertHyp = [checks] then insert then withHyps push
  -- We know from h_def_check that db_after_check is the post-check db

  have h_final :
      WellFormedDB ((db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).withHyps (·.push l)) :=
    withHyps_push_preserves_wf
      (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)) l
      h_wf_after_insert
      h_hypok_after_insert
      h_fresh_float_after_insert

  -- h_final proves: WellFormedDB ((db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).withHyps (·.push l))
  -- Goal is: WellFormedDB (db.insertHyp pos l ess arr)
  --
  -- Key insight: insertHyp uses `.hyp ess arr` as the object constructor,
  -- while we proved using `fun _ => .hyp ess arr l`.
  --
  -- When insert calls these at label `l`:
  -- - `.hyp ess arr` applied to `l` gives `.hyp ess arr l` (fourth constructor arg)
  -- - `fun _ => .hyp ess arr l` applied to `l` gives `.hyp ess arr l` (ignores arg)
  --
  -- We handle this by rewriting insertHyp with h_def_check and a small insert equality lemma.
  have h_check_err : db_after_check.error = false := by
    cases h_err : db_after_check.error with
    | true =>
        have h_err_some : db_after_check.error? ≠ none := (error_iff_error?_isSome db_after_check).1 h_err
        exact False.elim (h_err_some h_check_ok)
    | false =>
        rfl

  have h_insert_eq :
      db_after_check.insert pos l (Object.hyp ess arr) =
        db_after_check.insert pos l (fun _ => Object.hyp ess arr l) := by
    have h_obj : (Object.hyp ess arr) l = (fun _ => Object.hyp ess arr l) l := by rfl
    unfold DB.insert
    repeat (rw [h_obj])
  have h_insert_err :
      (db_after_check.insert pos l (Object.hyp ess arr)).error = false := by
    simp [DB.error, h_insert_ok]

  have h_insertHyp_eq :
      db.insertHyp pos l ess arr =
        (db_after_check.insert pos l (Object.hyp ess arr)).withHyps (·.push l) := by
    have h_def_check' := h_def_check.symm
    simp [DB.insertHyp, h_def_check', h_check_err, h_insert_err]

  have h_insertHyp_eq' :
      db.insertHyp pos l ess arr =
        (db_after_check.insert pos l (fun _ => Object.hyp ess arr l)).withHyps (·.push l) := by
    simpa [h_insert_eq] using h_insertHyp_eq

  simpa [h_insertHyp_eq'] using h_final

-- Subsequence: arr2 is a subsequence of arr1 if every element in arr2 exists in arr1
-- (preserving the string value, though not necessarily the position)
def IsSubsequence (arr1 arr2 : Array String) : Prop :=
  ∀ (i : Nat) (hi : i < arr2.size), ∃ (j : Nat) (hj : j < arr1.size), arr2[i]'hi = arr1[j]'hj

-- STRONGER version: Injective subsequence
-- arr2 is an injective subsequence of arr1 if there exists an injective index mapping
def IsInjectiveSubsequence (arr1 arr2 : Array String) : Prop :=
  ∃ (f : (i : Nat) → (hi : i < arr2.size) → {j : Nat // j < arr1.size}),
    (∀ (i : Nat) (hi : i < arr2.size), arr2[i]'hi = arr1[(f i hi).val]'(f i hi).property) ∧
    (∀ (i j : Nat) (hi : i < arr2.size) (hj : j < arr2.size), i ≠ j → (f i hi).val ≠ (f j hj).val)

-- Extraction lemma: trimFrame' success iff trimFrame returned (true, fr)
@[simp]
theorem trimFrame'_ok_iff {db : DB} {fmla : Formula} {fr : Frame} :
    db.trimFrame' fmla = .ok fr ↔ db.trimFrame fmla = (true, fr) := by
  unfold DB.trimFrame'
  obtain ⟨ok, fr'⟩ := db.trimFrame fmla
  -- Pattern: if ok then .ok fr' else .error msg
  -- Need to show: (.ok fr' if ok, .error msg otherwise) = .ok fr ↔ (ok, fr') = (true, fr)
  cases ok <;> simp
  · -- ok = true: pure fr' = .ok fr ↔ fr' = fr
    -- Need: Except.ok injectivity
    constructor
    · intro h
      cases h
      rfl
    · intro h
      rw [h]
      rfl

theorem trimFrameHypsPairsList_mem {db : DB} {vars : HashSet String} {ls : List String}
    {p : Nat × String} :
    p ∈ _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls →
      ∃ h : p.1 < ls.length, ls[p.1] = p.2 := by
  intro h_mem
  rcases List.mem_map.1 h_mem with ⟨q, hq, rfl⟩
  rcases List.mem_filter.1 hq with ⟨hq_zip, _⟩
  have hq_get : ls[q.2]? = some q.1 := (List.mem_zipIdx_iff_getElem?).1 hq_zip
  rcases (List.getElem?_eq_some_iff).1 hq_get with ⟨h_lt, h_eq⟩
  exact ⟨h_lt, h_eq⟩

theorem trimFrameHypsPairsList_nodup (db : DB) (vars : HashSet String) (ls : List String) :
    (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst |>.Nodup := by
  have h_sub :
      List.Sublist
        (((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map Prod.snd)
        ((List.zipIdx ls 0).map Prod.snd) := by
    exact List.Sublist.map _ (List.filter_sublist)
  have h_nodup : ((List.zipIdx ls 0).map Prod.snd).Nodup := by
    have h_eq : ((List.zipIdx ls 0).map Prod.snd) = List.range' 0 ls.length := by
      simp [List.zipIdx_map_snd]
    rw [h_eq]
    exact List.nodup_range' (s := 0) (n := ls.length)
  have h_nodup' :
      (((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map Prod.snd).Nodup :=
    List.Nodup.sublist h_sub h_nodup
  have h_eq :
      (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst =
        ((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map Prod.snd := by
    simp [_root_.Metamath.Verify.DB.trimFrameHypsPairsList, List.map_map]
  rw [h_eq]
  exact h_nodup'

theorem trimFrameHyps_subsequence (db : DB) (vars : HashSet String) (hyps : Array String) :
    IsInjectiveSubsequence hyps (_root_.Metamath.Verify.DB.trimFrameHyps db vars hyps) := by
  classical
  let pairs := _root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps
  have h_pairs_list :
      pairs.toList = _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
    simp [_root_.Metamath.Verify.DB.trimFrameHypsPairs, pairs]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hi_pairs : i < pairs.size := by
      have hi' := hi
      simp [_root_.Metamath.Verify.DB.trimFrameHyps, Array.size_map] at hi'
      exact hi'
    have hi_list : i < pairs.toList.length := by
      have hi' := hi_pairs
      simp at hi'
      exact hi'
    have h_mem : pairs[i]'hi_pairs ∈ pairs.toList := by
      have h_mem' : pairs.toList[i] ∈ pairs.toList := List.getElem_mem (by simpa using hi_list)
      have h_eq : pairs.toList[i] = pairs[i]'hi_pairs := by
        exact (Array.getElem_toList (xs := pairs) (i := i) hi_pairs)
      rw [h_eq] at h_mem'
      exact h_mem'
    have h_mem' : pairs[i]'hi_pairs ∈ _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
      rw [h_pairs_list] at h_mem
      exact h_mem
    have h_exists :=
      trimFrameHypsPairsList_mem (db := db) (vars := vars) (ls := hyps.toList) h_mem'
    have h_lt : (pairs[i]'hi_pairs).1 < hyps.toList.length := Classical.choose h_exists
    have h_lt' : (pairs[i]'hi_pairs).1 < hyps.size := by
      have h := h_lt
      simp [Array.length_toList] at h
      exact h
    exact ⟨(pairs[i]'hi_pairs).1, h_lt'⟩
  · intro i hi
    have hi_pairs : i < pairs.size := by
      have hi' := hi
      simp [_root_.Metamath.Verify.DB.trimFrameHyps, Array.size_map] at hi'
      exact hi'
    have hi_list : i < pairs.toList.length := by
      have hi' := hi_pairs
      simp at hi'
      exact hi'
    have h_mem : pairs[i]'hi_pairs ∈ pairs.toList := by
      have h_mem' : pairs.toList[i] ∈ pairs.toList := List.getElem_mem (by simpa using hi_list)
      have h_eq : pairs.toList[i] = pairs[i]'hi_pairs := by
        exact (Array.getElem_toList (xs := pairs) (i := i) hi_pairs)
      rw [h_eq] at h_mem'
      exact h_mem'
    have h_mem' : pairs[i]'hi_pairs ∈ _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
      rw [h_pairs_list] at h_mem
      exact h_mem
    have h_exists :=
      trimFrameHypsPairsList_mem (db := db) (vars := vars) (ls := hyps.toList) h_mem'
    have h_lt : (pairs[i]'hi_pairs).1 < hyps.toList.length := Classical.choose h_exists
    have h_eq :
        hyps.toList[(pairs[i]'hi_pairs).1] = (pairs[i]'hi_pairs).2 :=
      Classical.choose_spec h_exists
    have h_arr2 : (_root_.Metamath.Verify.DB.trimFrameHyps db vars hyps)[i] = (pairs[i]'hi_pairs).2 := by
      have hi_map : i < (Array.map (fun p => p.2) pairs).size := by
        simpa [Array.size_map] using hi_pairs
      simp [_root_.Metamath.Verify.DB.trimFrameHyps, pairs]
    have h_lt' : (pairs[i]'hi_pairs).1 < hyps.size := by
      have h := h_lt
      simp [Array.length_toList] at h
      exact h
    have h_arr1 : hyps[(pairs[i]'hi_pairs).1]'h_lt' =
        (pairs[i]'hi_pairs).2 := by
      have h_toList :
          hyps.toList[(pairs[i]'hi_pairs).1] =
            hyps[(pairs[i]'hi_pairs).1]'h_lt' := by
        exact
          (Array.getElem_toList (xs := hyps) (i := (pairs[i]'hi_pairs).1)
            h_lt')
      have h := h_eq
      simp [h_toList] at h
      exact h
    exact h_arr2.trans h_arr1.symm
  · intro i j hi hj h_ne
    have hi_pairs : i < pairs.size := by
      have hi' := hi
      simp [_root_.Metamath.Verify.DB.trimFrameHyps, Array.size_map] at hi'
      exact hi'
    have hj_pairs : j < pairs.size := by
      have hj' := hj
      simp [_root_.Metamath.Verify.DB.trimFrameHyps, Array.size_map] at hj'
      exact hj'
    have h_nodup :
        (pairs.toList.map Prod.fst).Nodup := by
      have h := (trimFrameHypsPairsList_nodup (db := db) (vars := vars) (ls := hyps.toList))
      simp at h
      exact h
    have hi_list : i < (pairs.toList.map Prod.fst).length := by
      simpa [Array.length_toList, List.length_map] using hi_pairs
    have hj_list : j < (pairs.toList.map Prod.fst).length := by
      simpa [Array.length_toList, List.length_map] using hj_pairs
    intro h_eq
    have h_idx_i : (pairs.toList.map Prod.fst)[i] = (pairs[i]'hi_pairs).1 := by
      have h_eq_list : pairs.toList[i] = pairs[i]'hi_pairs := by
        exact (Array.getElem_toList (xs := pairs) (i := i) hi_pairs)
      have h_len : i < (List.map Prod.fst pairs.toList).length := by
        simpa [Array.length_toList, List.length_map] using hi_pairs
      have h := (List.getElem_map (f := Prod.fst) (l := pairs.toList) (i := i) (h := h_len))
      rw [h_eq_list] at h
      exact h
    have h_idx_j : (pairs.toList.map Prod.fst)[j] = (pairs[j]'hj_pairs).1 := by
      have h_eq_list : pairs.toList[j] = pairs[j]'hj_pairs := by
        exact (Array.getElem_toList (xs := pairs) (i := j) hj_pairs)
      have h_len : j < (List.map Prod.fst pairs.toList).length := by
        simpa [Array.length_toList, List.length_map] using hj_pairs
      have h := (List.getElem_map (f := Prod.fst) (l := pairs.toList) (i := j) (h := h_len))
      rw [h_eq_list] at h
      exact h
    have h_eq_list : (pairs.toList.map Prod.fst)[i] = (pairs.toList.map Prod.fst)[j] := by
      calc
        (pairs.toList.map Prod.fst)[i] = (pairs[i]'hi_pairs).1 := h_idx_i
        _ = (pairs[j]'hj_pairs).1 := h_eq
        _ = (pairs.toList.map Prod.fst)[j] := h_idx_j.symm
    have h_get :
        (pairs.toList.map Prod.fst)[i]? = (pairs.toList.map Prod.fst)[j]? := by
      have h_i :
          (pairs.toList.map Prod.fst)[i]? = some ((pairs.toList.map Prod.fst)[i]) :=
        List.getElem?_eq_getElem (l := pairs.toList.map Prod.fst) (i := i) hi_list
      have h_j :
          (pairs.toList.map Prod.fst)[j]? = some ((pairs.toList.map Prod.fst)[j]) :=
        List.getElem?_eq_getElem (l := pairs.toList.map Prod.fst) (i := j) hj_list
      calc
        (pairs.toList.map Prod.fst)[i]? = some ((pairs.toList.map Prod.fst)[i]) := h_i
        _ = some ((pairs.toList.map Prod.fst)[j]) := by simp [h_eq_list]
        _ = (pairs.toList.map Prod.fst)[j]? := h_j.symm
    have h_eq_ij := List.getElem?_inj (i := i) (j := j) (h₀ := hi_list) h_nodup h_get
    exact (h_ne h_eq_ij).elim

-- trimFrame produces an INJECTIVE subsequence of the input frame's hypotheses
theorem trimFrame_produces_subsequence {db : DB} {fmla : Formula} {ok : Bool} {fr : Frame}
    (h : db.trimFrame fmla = (ok, fr)) : IsInjectiveSubsequence db.frame.hyps fr.hyps := by
  cases h
  -- Unfold trimFrame; the returned frame hyps are trimFrameHyps for the computed vars.
  simp
  exact trimFrameHyps_subsequence (db := db) (vars := _) (hyps := db.frame.hyps)

-- Lemma 3: trimFrame preserves UniqueFloatVars (subset monotonicity!)
theorem trimFrame_preserves_uniqueness {db : DB} {fr : Frame}
    (h_subseq : IsInjectiveSubsequence db.frame.hyps fr.hyps)
    (h_unique : UniqueFloatVars db db.frame) :
    UniqueFloatVars db fr := by
  intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj hsizei hsizej
  -- Extract the index mapping function from IsInjectiveSubsequence
  obtain ⟨f, h_maps, h_inj⟩ := h_subseq
  -- Get the mappings for i and j
  have h_eq_i := h_maps i hi
  have h_eq_j := h_maps j hj
  -- Extract the source indices
  let i' := (f i hi).val
  let j' := (f j hj).val
  have hi' : i' < db.frame.hyps.size := (f i hi).property
  have hj' : j' < db.frame.hyps.size := (f j hj).property
  -- The mapping is injective: i ≠ j implies i' ≠ j'
  have h_i'_ne_j' : i' ≠ j' := h_inj i j hi hj h_ne
  -- Rewrite to use db.frame.hyps
  rw [h_eq_i] at h_fi
  rw [h_eq_j] at h_fj
  -- Apply uniqueness on db.frame
  exact h_unique i' j' hi' hj' h_i'_ne_j' fi fj lbli lblj h_fi h_fj hsizei hsizej

-- Similarly for insertAxiom (full)
-- TODO: Need to prove frame well-formedness from trimFrame'
theorem trimFrame'_success_implies_wellformed_frame
    (db : DB) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_trimFrame : db.trimFrame' fmla = .ok fr) :
    WellFormedFrame db fr := by
  -- WellFormedFrame has two parts
  constructor
  · -- Part 1: All hypotheses in fr are HypOK db
    intro i hi
    -- Strategy: fr.hyps is an injective subsequence of db.frame.hyps, so fr.hyps[i] came from db.frame.hyps
    -- HypOK depends only on the label (via db.find?), not on position in frame

    -- Extract that trimFrame succeeded
    have h_trim : db.trimFrame fmla = (true, fr) := trimFrame'_ok_iff.mp h_trimFrame

    -- Use injective subsequence lemma
    have h_inj_subseq := trimFrame_produces_subsequence h_trim
    obtain ⟨f, h_maps, _⟩ := h_inj_subseq
    have h_eq := h_maps i hi
    let j := (f i hi).val
    have hj : j < db.frame.hyps.size := (f i hi).property

    -- From h_wf, get that db.frame is well-formed
    have ⟨h_frame_wf, _⟩ := h_wf
    have ⟨h_all_hypok, _⟩ := h_frame_wf

    -- Apply to db.frame.hyps[j]
    have h_hypok_j := h_all_hypok j hj

    -- Since fr.hyps[i] = db.frame.hyps[j], and HypOK depends only on the string value
    rw [h_eq]
    exact h_hypok_j

  · -- Part 2: UniqueFloatVars db fr
    -- Extract that trimFrame succeeded
    have h_trim : db.trimFrame fmla = (true, fr) := trimFrame'_ok_iff.mp h_trimFrame

    -- Get subsequence property
    have h_subseq := trimFrame_produces_subsequence h_trim

    -- Get UniqueFloatVars for db.frame
    have ⟨h_frame_wf, _⟩ := h_wf
    have ⟨_, h_unique_frame⟩ := h_frame_wf

    -- Apply the uniqueness preservation lemma!
    exact trimFrame_preserves_uniqueness h_subseq h_unique_frame

-- Helper lemma: mkError always sets error?
theorem mkError_sets_error (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).error? = some ⟨.error pos msg, default⟩ := by
  unfold DB.mkError
  rfl

-- Helper lemma: Extract success conditions from insertAxiom
-- This isolates the control flow reasoning into a separate lemma
theorem insertAxiom_success_conditions
    (db : DB) (pos : Pos) (l : String) (arr : Formula)
    (h_success : (db.insertAxiom pos l arr).error? = none) :
    ∃ (fr : Frame),
      db.trimFrame' arr = .ok fr ∧
      db.interrupt = false ∧
      (db.insert pos l (.assert arr fr)).error? = none := by
  unfold DB.insertAxiom at h_success
  cases h_head : Formula.hasConstHead arr with
  | false =>
      simp [h_head, DB.mkError] at h_success
      cases h_success
  | true =>
      cases h_db_err : db.error with
      | true =>
          have h_db_err_some : db.error? ≠ none := (error_iff_error?_isSome db).1 h_db_err
          have h_no_err : db.error? = none := by
            simp [h_head, h_db_err] at h_success
            exact h_success
          exact False.elim (h_db_err_some h_no_err)
      | false =>
          cases h_trim : db.trimFrame' arr with
          | error msg =>
              have h_no_err' :
                  (db.mkError pos msg).error? = none := by
                simp [h_head, h_db_err, h_trim] at h_success
                exact h_success
              have : False := by
                simp [DB.mkError] at h_no_err'
              exact False.elim this
          | ok fr =>
              by_cases h_int : db.interrupt
              · have h_no_err' :
                    { db with error? := some ⟨.ax pos l arr fr, default⟩ }.error? = none := by
                  have h_success' := h_success
                  simp [h_head, h_db_err, h_trim, h_int] at h_success'
                cases h_no_err'
              · refine ⟨fr, rfl, ?_, ?_⟩
                · simp [Bool.not_eq_true] at h_int
                  exact h_int
                · have h_success' := h_success
                  simp [h_head, h_db_err, h_trim, h_int] at h_success'
                  exact h_success'

theorem insertAxiom_full_maintains_wf
    (db : DB) (pos : Pos) (l : String) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertAxiom pos l arr).error? = none) :
    WellFormedDB (db.insertAxiom pos l arr) := by
  -- Extract success conditions using helper lemma
  obtain ⟨fr, h_trim, h_no_int, h_insert_ok⟩ := insertAxiom_success_conditions db pos l arr h_success
  -- Now we have clean hypotheses:
  -- h_trim : db.trimFrame' arr = .ok fr
  -- h_no_int : db.interrupt = false
  -- h_insert_ok : (db.insert pos l (.assert arr fr)).error? = none

  -- First, prove frame well-formedness from trimFrame' success
  have h_frame_wf : WellFormedFrame db fr := trimFrame'_success_implies_wellformed_frame db arr fr h_wf h_trim
  -- Freshness in the trimmed frame follows from subsequence mapping
  have h_trim_ok : db.trimFrame arr = (true, fr) := trimFrame'_ok_iff.mp h_trim
  rcases trimFrame_produces_subsequence h_trim_ok with ⟨f, h_eq, _h_inj⟩
  have h_fresh_in_frame : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l := by
    intro i hi
    have h_fresh := h_fresh_label (f i hi).val (f i hi).property
    have h_eqi := h_eq i hi
    simpa [h_eqi.symm] using h_fresh

  have h_notvar0 : arr[0]!.isVar = false := by
    cases h_var0 : arr[0]!.isVar with
    | false => rfl
    | true =>
        have : False := by
          simpa [h_var0] using h_first.2
        exact False.elim this
  have h_head : Formula.hasConstHead arr = true := by
    unfold Formula.hasConstHead
    have h_pos : 0 < arr.size := by
      exact h_first.1
    cases h0 : arr[0]! with
    | const _ =>
        simp [h_pos]
    | var _ =>
        have : False := by
          simp [Sym.isVar, h0] at h_notvar0
        exact False.elim this
  have h_db_err : db.error = false := by
    simp [DB.error, h_no_err]

  -- Unfold insertAxiom
  unfold DB.insertAxiom
  simp [h_head, h_db_err, h_trim, h_no_int]
  -- Goal: WellFormedDB (db.insert pos l (.assert arr fr))
  apply insertAxiom_insert_part_maintains_wf db pos l arr fr
  · exact h_wf
  · exact h_no_err
  · exact h_first
  · exact h_frame_wf
  · exact h_fresh_in_frame
  · exact h_fresh_db
  · exact h_fresh_label
  · exact h_fresh_in_asserts
  · exact h_insert_ok

-- Phase B: feedTokens correctness (blocked on Phase A completion)
-- TODO: Complete after proving insertHyp_full and insertAxiom_full
-- Helper: feedTokens .ax case reduces to insertAxiom for the .db field
-- TODO: This helper would enable completing the .ax case
-- The proof requires simplifying through:
-- 1. feedTokens definition
-- 2. Verify.withAt wrapper
-- 3. Id.run + unless check (using h_first)
-- 4. match on tokp.k = .ax
-- 5. Result: .db = s.db.insertAxiom pos l arr
@[simp] theorem id_pure_eq {α} (x : α) : (pure x : Id α) = x := rfl
@[simp] theorem id_do_unit {α} (x : α) : (do PUnit.unit; x : Id α) = x := by rfl
@[simp] theorem id_run_eq {α} (x : α) : Id.run x = x := rfl

theorem feedTokens_ax_db (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_success : (s.feedTokens arr ⟨.ax, pos, l⟩).db.error? = none) :
    (s.feedTokens arr ⟨.ax, pos, l⟩).db = s.db.insertAxiom pos l arr := by
  have h_notvar : arr[0]!.isVar = false := by
    cases h_var : arr[0]!.isVar with
    | false => rfl
    | true =>
        have : False := by
          simpa [h_var] using h_first.2
        exact False.elim this
  have h_pos : 0 < arr.size := by
    exact h_first.1
  have h0_eq : arr[0]! = arr[0]'h_pos := by
    simpa using (Array.getBang_eq_get_nat (a := arr) (i := 0) (h := h_pos))
  have h_notvar_get : arr[0].isVar = false := by
    simpa [h0_eq] using h_notvar
  have h_head : Formula.hasConstHead arr = true := by
    unfold Formula.hasConstHead
    cases h_sym : arr[0]! with
    | const c => simp [h_pos]
    | var v =>
        have h_false : False := by
          simp [Sym.isVar, h_sym] at h_notvar
        exact False.elim h_false

  -- Compute the inner parser state (before withAt wraps errors).
  let s_db := s.withDB fun db => db.insertAxiom pos l arr
  let s_inner : ParserState := { s_db with tokp := .start }
  have h_s_inner :
      { db := (ParserState.withDB (fun db => db.insertAxiom pos l arr) s).db, tokp := TokenParser.start,
        charp := (ParserState.withDB (fun db => db.insertAxiom pos l arr) s).charp,
        line := (ParserState.withDB (fun db => db.insertAxiom pos l arr) s).line,
        linepos := (ParserState.withDB (fun db => db.insertAxiom pos l arr) s).linepos } = s_inner := by
    rfl
  have h_inner :
      (if Formula.hasConstHead arr = true then
          (s_inner : ParserState)
        else
          s.mkError pos "first symbol is not a constant") = s_inner := by
    simp [h_head]

  have h_success_pre :
      (ParserState.withAt l (fun _ =>
          if Formula.hasConstHead arr = true then s_inner
          else s.mkError pos "first symbol is not a constant")).db.error? = none := by
    simpa [ParserState.feedTokens, h_s_inner] using h_success
  have h_success' : (ParserState.withAt l (fun _ => s_inner)).db.error? = none := by
    have h_success_pre' := h_success_pre
    simp [h_inner] at h_success_pre'
    exact h_success_pre'

  have h_inner_no_err : s_inner.db.error? = none := by
    cases h_err : s_inner.db.error? with
    | none => rfl
    | some err =>
        rcases err with ⟨e, idx⟩
        cases e with
        | error pos msg =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, ParserState.withDB, h_err]
            exact (h_err_some h_success').elim
        | ax pos lbl f fr =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, h_err]
            exact (h_err_some h_success').elim
        | thm pos lbl f fr =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, h_err]
            exact (h_err_some h_success').elim

  have h_db_pre :
      (s.feedTokens arr ⟨.ax, pos, l⟩).db =
        (ParserState.withAt l (fun _ =>
          if Formula.hasConstHead arr = true then s_inner
          else s.mkError pos "first symbol is not a constant")).db := by
    simp [ParserState.feedTokens, h_s_inner]
  calc
    (s.feedTokens arr ⟨.ax, pos, l⟩).db
        = (ParserState.withAt l (fun _ =>
            if Formula.hasConstHead arr = true then s_inner
            else s.mkError pos "first symbol is not a constant")).db := by
            exact h_db_pre
    _ = (ParserState.withAt l (fun _ => s_inner)).db := by
            simp [h_inner]
    _ = s_inner.db := by
            simp [ParserState.withAt, h_inner_no_err]
    _ = s.db.insertAxiom pos l arr := by
            rfl

theorem feedTokens_float_db (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_float : arr.size = 2 ∧ arr[1]!.isVar)
    (h_success : (s.feedTokens arr ⟨.float, pos, l⟩).db.error? = none) :
    (s.feedTokens arr ⟨.float, pos, l⟩).db = s.db.insertHyp pos l false arr := by
  have h_notvar : arr[0]!.isVar = false := by
    cases h_var : arr[0]!.isVar with
    | false => rfl
    | true =>
        have : False := by
          simpa [h_var] using h_first.2
        exact False.elim this
  have h_var1 : arr[1]!.isVar = true := by
    simpa using h_float.2
  have h_pos : 0 < arr.size := by
    exact h_first.1
  have h0_eq : arr[0]! = arr[0]'h_pos := by
    simpa using (Array.getBang_eq_get_nat (a := arr) (i := 0) (h := h_pos))
  have h_notvar_get : arr[0].isVar = false := by
    simpa [h0_eq] using h_notvar
  have h_pos1 : 1 < arr.size := by
    -- from arr.size = 2
    simp [h_float.1]
  have h1_eq : arr[1]! = arr[1]'h_pos1 := by
    simpa using (Array.getBang_eq_get_nat (a := arr) (i := 1) (h := h_pos1))
  have h_var1_get : arr[1].isVar = true := by
    simpa [h1_eq] using h_var1
  have h_head : Formula.hasConstHead arr = true := by
    unfold Formula.hasConstHead
    cases h_sym : arr[0]! with
    | const c => simp [h_pos]
    | var v =>
        have h_false : False := by
          simp [Sym.isVar, h_sym] at h_notvar
        exact False.elim h_false
  have h_float_shape : Formula.isFloatShape arr = true := by
    unfold Formula.isFloatShape
    cases h0 : arr[0]! with
    | const c =>
        cases h1 : arr[1]! with
        | const c' =>
            have h_false : False := by
              simp [Sym.isVar, h1] at h_var1
            exact False.elim h_false
        | var v' =>
            simp [h_float.1]
    | var v =>
        have h_false : False := by
          simp [Sym.isVar, h0] at h_notvar
        exact False.elim h_false

  let s_db := s.withDB fun db => db.insertHyp pos l false arr
  let s_inner : ParserState := { s_db with tokp := .start }
  have h_s_inner :
      { db := (ParserState.withDB (fun db => db.insertHyp pos l false arr) s).db, tokp := TokenParser.start,
        charp := (ParserState.withDB (fun db => db.insertHyp pos l false arr) s).charp,
        line := (ParserState.withDB (fun db => db.insertHyp pos l false arr) s).line,
        linepos := (ParserState.withDB (fun db => db.insertHyp pos l false arr) s).linepos } = s_inner := by
    rfl
  have h_inner :
      (if Formula.hasConstHead arr = true then
          if Formula.isFloatShape arr = true then
            (s_inner : ParserState)
          else
            s.mkError pos "expected a constant and a variable"
        else
          s.mkError pos "first symbol is not a constant") = s_inner := by
    simp [h_head, h_float_shape]

  have h_success_pre :
      (ParserState.withAt l (fun _ =>
          if Formula.hasConstHead arr = true then
            if Formula.isFloatShape arr = true then s_inner
            else s.mkError pos "expected a constant and a variable"
          else s.mkError pos "first symbol is not a constant")).db.error? = none := by
    simpa [ParserState.feedTokens, h_s_inner] using h_success
  have h_success' : (ParserState.withAt l (fun _ => s_inner)).db.error? = none := by
    have h_success_pre' := h_success_pre
    simp [h_inner] at h_success_pre'
    exact h_success_pre'

  have h_inner_no_err : s_inner.db.error? = none := by
    cases h_err : s_inner.db.error? with
    | none => rfl
    | some err =>
        rcases err with ⟨e, idx⟩
        cases e with
        | error pos msg =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, ParserState.withDB, h_err]
            exact (h_err_some h_success').elim
        | ax pos lbl f fr =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, h_err]
            exact (h_err_some h_success').elim
        | thm pos lbl f fr =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, h_err]
            exact (h_err_some h_success').elim

  have h_db_pre :
      (s.feedTokens arr ⟨.float, pos, l⟩).db =
        (ParserState.withAt l (fun _ =>
          if Formula.hasConstHead arr = true then
            if Formula.isFloatShape arr = true then s_inner
            else s.mkError pos "expected a constant and a variable"
          else s.mkError pos "first symbol is not a constant")).db := by
    simp [ParserState.feedTokens, h_s_inner]
  calc
    (s.feedTokens arr ⟨.float, pos, l⟩).db
        = (ParserState.withAt l (fun _ =>
            if Formula.hasConstHead arr = true then
              if Formula.isFloatShape arr = true then s_inner
              else s.mkError pos "expected a constant and a variable"
            else s.mkError pos "first symbol is not a constant")).db := by
            exact h_db_pre
    _ = (ParserState.withAt l (fun _ => s_inner)).db := by
            simp [h_inner]
    _ = s_inner.db := by
            simp [ParserState.withAt, h_inner_no_err]
    _ = s.db.insertHyp pos l false arr := by
            rfl

theorem feedTokens_ess_db (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_success : (s.feedTokens arr ⟨.ess, pos, l⟩).db.error? = none) :
    (s.feedTokens arr ⟨.ess, pos, l⟩).db = s.db.insertHyp pos l true arr := by
  have h_notvar : arr[0]!.isVar = false := by
    cases h_var : arr[0]!.isVar with
    | false => rfl
    | true =>
        have : False := by
          simpa [h_var] using h_first.2
        exact False.elim this
  have h_pos : 0 < arr.size := by
    exact h_first.1
  have h0_eq : arr[0]! = arr[0]'h_pos := by
    simpa using (Array.getBang_eq_get_nat (a := arr) (i := 0) (h := h_pos))
  have h_notvar_get : arr[0].isVar = false := by
    simpa [h0_eq] using h_notvar
  have h_head : Formula.hasConstHead arr = true := by
    unfold Formula.hasConstHead
    cases h_sym : arr[0]! with
    | const c => simp [h_pos]
    | var v =>
        have h_false : False := by
          simp [Sym.isVar, h_sym] at h_notvar
        exact False.elim h_false

  let s_db := s.withDB fun db => db.insertHyp pos l true arr
  let s_inner : ParserState := { s_db with tokp := .start }
  have h_s_inner :
      { db := (ParserState.withDB (fun db => db.insertHyp pos l true arr) s).db, tokp := TokenParser.start,
        charp := (ParserState.withDB (fun db => db.insertHyp pos l true arr) s).charp,
        line := (ParserState.withDB (fun db => db.insertHyp pos l true arr) s).line,
        linepos := (ParserState.withDB (fun db => db.insertHyp pos l true arr) s).linepos } = s_inner := by
    rfl
  have h_inner :
      (if Formula.hasConstHead arr = true then
          (s_inner : ParserState)
        else
          s.mkError pos "first symbol is not a constant") = s_inner := by
    simp [h_head]

  have h_success_pre :
      (ParserState.withAt l (fun _ =>
          if Formula.hasConstHead arr = true then s_inner
          else s.mkError pos "first symbol is not a constant")).db.error? = none := by
    simpa [ParserState.feedTokens, h_s_inner] using h_success
  have h_success' : (ParserState.withAt l (fun _ => s_inner)).db.error? = none := by
    have h_success_pre' := h_success_pre
    simp [h_inner] at h_success_pre'
    exact h_success_pre'

  have h_inner_no_err : s_inner.db.error? = none := by
    cases h_err : s_inner.db.error? with
    | none => rfl
    | some err =>
        rcases err with ⟨e, idx⟩
        cases e with
        | error pos msg =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, ParserState.withDB, h_err]
            exact (h_err_some h_success').elim
        | ax pos lbl f fr =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, h_err]
            exact (h_err_some h_success').elim
        | thm pos lbl f fr =>
            have h_err_some : (ParserState.withAt l (fun _ => s_inner)).db.error? ≠ none := by
              simp [ParserState.withAt, h_err]
            exact (h_err_some h_success').elim

  have h_db_pre :
      (s.feedTokens arr ⟨.ess, pos, l⟩).db =
        (ParserState.withAt l (fun _ =>
          if Formula.hasConstHead arr = true then s_inner
          else s.mkError pos "first symbol is not a constant")).db := by
    simp [ParserState.feedTokens, h_s_inner]
  calc
    (s.feedTokens arr ⟨.ess, pos, l⟩).db
        = (ParserState.withAt l (fun _ =>
            if Formula.hasConstHead arr = true then s_inner
            else s.mkError pos "first symbol is not a constant")).db := by
            exact h_db_pre
    _ = (ParserState.withAt l (fun _ => s_inner)).db := by
            simp [h_inner]
    _ = s_inner.db := by
            simp [ParserState.withAt, h_inner_no_err]
    _ = s.db.insertHyp pos l true arr := by
            rfl

theorem feedTokens_maintains_wf
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_wf : WellFormedDB s.db)
    (h_no_err : s.db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_float : tokp.k = TokensKind.float → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_fresh_db : s.db.find? tokp.label = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < s.db.frame.hyps.size), s.db.frame.hyps[i]'hi ≠ tokp.label)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        s.db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ tokp.label)
    (h_success : (s.feedTokens arr tokp).db.error? = none) :
    WellFormedDB (s.feedTokens arr tokp).db := by
  cases tokp with
  | mk k pos label =>
    cases k with
    | float =>
        have h_shape : arr.size = 2 ∧ arr[1]!.isVar := h_float rfl
        have h_success' :
            (s.feedTokens arr ⟨.float, pos, label⟩).db.error? = none := by
          simpa using h_success
        have h_db_eq :
            (s.feedTokens arr ⟨.float, pos, label⟩).db =
              s.db.insertHyp pos label false arr :=
          feedTokens_float_db s arr pos label h_first h_shape h_success'
        have h_insert_ok : (s.db.insertHyp pos label false arr).error? = none := by
          simpa [h_db_eq] using h_success'
        have h_second' : (false = false → (arr.size = 2 ∧ arr[1]!.isVar)) := by
          intro _
          exact h_shape
        have h_wf_insert : WellFormedDB (s.db.insertHyp pos label false arr) :=
          insertHyp_full_maintains_wf s.db pos label false arr
            h_wf h_no_err h_first h_second' h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_wf_insert
    | ess =>
        have h_success' :
            (s.feedTokens arr ⟨.ess, pos, label⟩).db.error? = none := by
          simpa using h_success
        have h_db_eq :
            (s.feedTokens arr ⟨.ess, pos, label⟩).db =
              s.db.insertHyp pos label true arr :=
          feedTokens_ess_db s arr pos label h_first h_success'
        have h_insert_ok : (s.db.insertHyp pos label true arr).error? = none := by
          simpa [h_db_eq] using h_success'
        have h_second' : (true = false → (arr.size = 2 ∧ arr[1]!.isVar)) := by
          intro h_false
          cases h_false
        have h_wf_insert : WellFormedDB (s.db.insertHyp pos label true arr) :=
          insertHyp_full_maintains_wf s.db pos label true arr
            h_wf h_no_err h_first h_second' h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_wf_insert
    | ax =>
        -- Rewrite the parser step to insertAxiom, then reuse the full lemma.
        have h_success' :
            (s.feedTokens arr ⟨.ax, pos, label⟩).db.error? = none := by
          simpa using h_success
        have h_db_eq :
            (s.feedTokens arr ⟨.ax, pos, label⟩).db =
              s.db.insertAxiom pos label arr :=
          feedTokens_ax_db s arr pos label h_first h_success'
        have h_insert_ok : (s.db.insertAxiom pos label arr).error? = none := by
          simpa [h_db_eq] using h_success'
        have h_wf_insert : WellFormedDB (s.db.insertAxiom pos label arr) :=
          insertAxiom_full_maintains_wf s.db pos label arr
            h_wf h_no_err h_first h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_wf_insert
    | thm =>
        -- Successful .thm does not modify the DB (it only moves to proof mode).
        have h_success' :
            (s.feedTokens arr ⟨.thm, pos, label⟩).db.error? = none := by
          simpa using h_success
        have h_notvar : arr[0]!.isVar = false := by
          cases h_var : arr[0]!.isVar with
          | false => rfl
          | true =>
              have : False := by
                simpa [h_var] using h_first.2
              exact False.elim this
        have h_pos : 0 < arr.size := h_first.1
        have h_head : Formula.hasConstHead arr = true := by
          unfold Formula.hasConstHead
          cases h_sym : arr[0]! with
          | const c => simp [h_pos]
          | var v =>
              have h_false : False := by
                simp [Sym.isVar, h_sym] at h_notvar
              exact False.elim h_false
        cases h_trim : s.db.trimFrame' arr with
        | error msg =>
            have h_bad : (ParserState.withAt label (fun _ => s.mkError pos msg)).db.error? ≠ none := by
              simp [ParserState.withAt, ParserState.mkError, ParserState.withDB, DB.mkError]
            have h_success'' :
                (ParserState.withAt label (fun _ => s.mkError pos msg)).db.error? = none := by
              simpa [ParserState.feedTokens, h_head, h_trim] using h_success'
            exact (h_bad h_success'').elim
        | ok fr =>
            by_cases h_interrupt : s.db.interrupt
            · have h_bad :
                (ParserState.withAt label (fun _ =>
                  ParserState.withDB
                    (fun db =>
                      { db with error? := some ⟨.thm pos label arr fr, default⟩ })
                    s)).db.error? ≠ none := by
                simp [ParserState.withAt, ParserState.withDB]
              have h_success'' :
                  (ParserState.withAt label (fun _ =>
                    ParserState.withDB
                      (fun db =>
                        { db with error? := some ⟨.thm pos label arr fr, default⟩ })
                      s)).db.error? = none := by
                simpa [ParserState.feedTokens, h_head, h_trim, h_interrupt] using h_success'
              exact (h_bad h_success'').elim
            · have h_db_eq :
                (s.feedTokens arr ⟨.thm, pos, label⟩).db = s.db := by
                simp [ParserState.feedTokens, h_head, h_trim, h_interrupt,
                  ParserState.resumeThm, ParserState.withAt, h_no_err]
              simpa [h_db_eq] using h_wf

end ParserOps
end Metamath
