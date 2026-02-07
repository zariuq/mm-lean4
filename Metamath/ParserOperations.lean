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
import Metamath.ArrayListExt
import Std.Data.HashSet.Lemmas
import Batteries.Data.String.Lemmas
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


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
    (_h_wf : WellFormedDB db)
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
  exact structure_preserving_maintains_wf db h_struct _h_wf h_no_err_before h_insert_ok

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

/-! ## Well-Scoped Frame Helpers -/

theorem frameFloatVars_mem_preserved_by_insert
    (db : DB) (pos : Pos) (label : String) (obj : String → Object) (fr : Frame)
    (h_not_in : label ∉ fr.hyps.toList) (v : String) :
    v ∈ DB.frameFloatVars (db.insert pos label obj) fr ↔
      v ∈ DB.frameFloatVars db fr := by
  constructor
  · intro h_mem
    have h_mem' :
        v ∈ DB.frameFloatVars (db.insert pos label obj) (Frame.mk #[] fr.hyps) := by
      simpa [DB.frameFloatVars] using h_mem
    rcases (frameFloatVars_mem_iff (db := db.insert pos label obj) (hyps := fr.hyps) (v := v)).1 h_mem' with
      ⟨lbl, f, lbl_name, h_lbl_mem, h_find, h_shape, h_f1⟩
    have h_ne : lbl ≠ label := by
      intro h_eq
      apply h_not_in
      simpa [h_eq] using h_lbl_mem
    have h_find_eq :
        (db.insert pos label obj).find? lbl = db.find? lbl :=
      Metamath.ParserCorrectness.insert_preserves_find?_ne db pos label lbl obj h_ne
    have h_find' : db.find? lbl = some (.hyp false f lbl_name) := by
      simpa [h_find_eq] using h_find
    have h_mem_old :
        v ∈ DB.frameFloatVars db (Frame.mk #[] fr.hyps) :=
      (frameFloatVars_mem_iff (db := db) (hyps := fr.hyps) (v := v)).2
        ⟨lbl, f, lbl_name, h_lbl_mem, h_find', h_shape, h_f1⟩
    simpa [DB.frameFloatVars] using h_mem_old
  · intro h_mem
    have h_mem' :
        v ∈ DB.frameFloatVars db (Frame.mk #[] fr.hyps) := by
      simpa [DB.frameFloatVars] using h_mem
    rcases (frameFloatVars_mem_iff (db := db) (hyps := fr.hyps) (v := v)).1 h_mem' with
      ⟨lbl, f, lbl_name, h_lbl_mem, h_find, h_shape, h_f1⟩
    have h_ne : lbl ≠ label := by
      intro h_eq
      apply h_not_in
      simpa [h_eq] using h_lbl_mem
    have h_find_eq :
        (db.insert pos label obj).find? lbl = db.find? lbl :=
      Metamath.ParserCorrectness.insert_preserves_find?_ne db pos label lbl obj h_ne
    have h_find' :
        (db.insert pos label obj).find? lbl = some (.hyp false f lbl_name) := by
      simpa [h_find_eq] using h_find
    have h_mem_new :
        v ∈ DB.frameFloatVars (db.insert pos label obj) (Frame.mk #[] fr.hyps) :=
      (frameFloatVars_mem_iff (db := db.insert pos label obj) (hyps := fr.hyps) (v := v)).2
        ⟨lbl, f, lbl_name, h_lbl_mem, h_find', h_shape, h_f1⟩
    simpa [DB.frameFloatVars] using h_mem_new

theorem formulaSymsRespectFrame_preserved_by_insert
    (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (fr : Frame) (f : Formula) (h_not_in : label ∉ fr.hyps.toList)
    (h_ok : DB.formulaSymsRespectFrame db f fr = true) :
    DB.formulaSymsRespectFrame (db.insert pos label obj) f fr = true := by
  -- Reduce to per-symbol property from the old frame.
  have h_ok' :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars db fr)
          | .const c => decide (c ∉ DB.frameFloatVars db fr)) = true := by
    simpa [DB.formulaSymsRespectFrame] using h_ok
  have h_all := (List.all_eq_true).1 h_ok'
  have h_ok'' :
      (f.toList.tail).all
        (fun s => match s with
          | .var v => decide (v ∈ DB.frameFloatVars (db.insert pos label obj) fr)
          | .const c => decide (c ∉ DB.frameFloatVars (db.insert pos label obj) fr)) = true := by
    apply (List.all_eq_true).2
    intro s h_mem
    have h_s := h_all s h_mem
    cases s with
    | var v =>
        have h_in_old : v ∈ DB.frameFloatVars db fr := by
          simpa using (decide_eq_true_iff.mp h_s)
        have h_in_new :
            v ∈ DB.frameFloatVars (db.insert pos label obj) fr := by
          exact (frameFloatVars_mem_preserved_by_insert db pos label obj fr h_not_in v).2 h_in_old
        simpa using (decide_eq_true_iff.mpr h_in_new)
    | const c =>
        have h_not_old : c ∉ DB.frameFloatVars db fr := by
          simpa using (decide_eq_true_iff.mp h_s)
        have h_not_new : c ∉ DB.frameFloatVars (db.insert pos label obj) fr := by
          intro h_in_new
          have h_in_old :
              c ∈ DB.frameFloatVars db fr :=
            (frameFloatVars_mem_preserved_by_insert db pos label obj fr h_not_in c).1 h_in_new
          exact h_not_old h_in_old
        simpa using (decide_eq_true_iff.mpr h_not_new)
  simpa [DB.formulaSymsRespectFrame] using h_ok''

theorem floatDeclaredBefore_preserved_by_insert
    (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (fr : Frame) (i : Nat) (v : String)
    (h_i : i < fr.hyps.size)
    (h_not_in : label ∉ fr.hyps.toList)
    (h_decl : FloatDeclaredBefore db fr i v) :
    FloatDeclaredBefore (db.insert pos label obj) fr i v := by
  rcases h_decl with ⟨j, hj, f, lbl, h_find, h_shape, h_f1⟩
  have h_j_lt : j < fr.hyps.size := Nat.lt_trans hj h_i
  have h_mem : fr.hyps[j]! ∈ fr.hyps.toList :=
    Array.getElem!_mem_toList fr.hyps j h_j_lt
  have h_ne : fr.hyps[j]! ≠ label := by
    intro h_eq
    apply h_not_in
    simpa [h_eq] using h_mem
  have h_find_eq :
      (db.insert pos label obj).find? (fr.hyps[j]!) = db.find? (fr.hyps[j]!) :=
    Metamath.ParserCorrectness.insert_preserves_find?_ne db pos label (fr.hyps[j]!) obj h_ne
  have h_find' :
      (db.insert pos label obj).find? (fr.hyps[j]!) = some (.hyp false f lbl) := by
    simpa [h_find_eq] using h_find
  exact ⟨j, hj, f, lbl, h_find', h_shape, h_f1⟩

theorem wellScopedFrame_preserved_by_insert
    (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (fr : Frame) (h_scoped : WellScopedFrame db fr)
    (h_not_in : label ∉ fr.hyps.toList) :
    WellScopedFrame (db.insert pos label obj) fr := by
  constructor
  · intro i hi
    have h_scoped_i := h_scoped.1 i hi
    have h_mem : fr.hyps[i]! ∈ fr.hyps.toList :=
      Array.getElem!_mem_toList fr.hyps i hi
    have h_ne : fr.hyps[i]! ≠ label := by
      intro h_eq
      apply h_not_in
      simpa [h_eq] using h_mem
    have h_find_eq :
        (db.insert pos label obj).find? (fr.hyps[i]!) = db.find? (fr.hyps[i]!) :=
      Metamath.ParserCorrectness.insert_preserves_find?_ne db pos label (fr.hyps[i]!) obj h_ne
    cases h_find : db.find? fr.hyps[i]! with
    | none =>
        simp [h_find_eq, h_find] at h_scoped_i ⊢
    | some obj_i =>
        cases obj_i with
        | hyp ess f lbl' =>
            cases ess with
            | true =>
                have h_scoped_i' :
                    DB.formulaSymsRespectFrame db f (Frame.mk #[] fr.hyps) = true ∧
                    (∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db fr i v) := by
                  simpa [h_find] using h_scoped_i
                have h_syms_new :
                    DB.formulaSymsRespectFrame (db.insert pos label obj) f (Frame.mk #[] fr.hyps) = true := by
                  exact formulaSymsRespectFrame_preserved_by_insert
                    db pos label obj (Frame.mk #[] fr.hyps) f h_not_in h_scoped_i'.1
                have h_decl_new : ∀ v, Sym.var v ∈ f.toList.tail →
                    FloatDeclaredBefore (db.insert pos label obj) fr i v := by
                  intro v h_mem'
                  exact floatDeclaredBefore_preserved_by_insert db pos label obj fr i v hi h_not_in (h_scoped_i'.2 v h_mem')
                -- Match branch: essential case
                simp [h_find_eq, h_find]
                exact ⟨h_syms_new, h_decl_new⟩
            | false =>
                simp [h_find_eq, h_find]
        | _ =>
            simp [h_find_eq, h_find]
  · intro v w h_mem
    have h_scoped_dv := h_scoped.2 v w h_mem
    rcases h_scoped_dv with ⟨h_lt, h_in1, h_in2⟩
    have h_in1' : v ∈ DB.frameFloatVars (db.insert pos label obj) fr := by
      exact (frameFloatVars_mem_preserved_by_insert db pos label obj fr h_not_in v).2 h_in1
    have h_in2' : w ∈ DB.frameFloatVars (db.insert pos label obj) fr := by
      exact (frameFloatVars_mem_preserved_by_insert db pos label obj fr h_not_in w).2 h_in2
    exact ⟨h_lt, h_in1', h_in2'⟩

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

theorem getElem!_push_eq {α : Type u} [Inhabited α] (arr : Array α) (x : α) :
    (arr.push x)[arr.size]! = x := by
  have h_lt : arr.size < (arr.push x).size := by
    simp [Array.size_push]
  have h_get : (arr.push x)[arr.size] = x := by
    exact getElem_push_eq arr x h_lt
  have h_eq : (arr.push x)[arr.size]! = (arr.push x)[arr.size] := by
    simpa using (Array.getBang_eq_get_nat (a := arr.push x) (i := arr.size) (h := h_lt))
  simpa [h_get] using h_eq

theorem wellScopedFrame_push_float
    (db : DB) (fr : Frame) (lbl : String)
    (f_float : Formula) (lbl_float : String)
    (h_scoped : WellScopedFrame db fr)
    (h_scoped_db : WellScopedDB db)
    (h_find_float : db.find? lbl = some (.hyp false f_float lbl_float))
    (h_shape : f_float.isFloatShape = true)
    (h_decl_float : FormulaSymbolsDeclared db f_float) :
    WellScopedFrame db { fr with hyps := fr.hyps.push lbl } := by
  constructor
  · intro i hi
    by_cases h_old : i < fr.hyps.size
    · have h_scoped_i := h_scoped.1 i h_old
      cases h_find_i : db.find? fr.hyps[i]! with
      | none =>
          have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
            Array.getElem!_push_lt h_old
          simp [h_get, h_find_i] at h_scoped_i ⊢
      | some obj_i =>
          cases obj_i with
          | hyp ess f lbl' =>
              cases ess with
              | true =>
                  have h_scoped_i' :
                      DB.formulaSymsRespectFrame db f (Frame.mk #[] fr.hyps) = true ∧
                      (∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db fr i v) := by
                    simpa [h_find_i] using h_scoped_i
                  have h_decl_i : FormulaSymbolsDeclared db f := by
                    have h_scoped_hyp :=
                      h_scoped_db.2 (fr.hyps[i]!) (.hyp true f lbl') h_find_i
                    exact h_scoped_hyp.2
                  have h_syms_new :
                      DB.formulaSymsRespectFrame db f (Frame.mk #[] (fr.hyps.push lbl)) = true := by
                    exact formulaSymsRespectFrame_push_float
                      db f fr.hyps lbl f_float lbl_float h_scoped_i'.1 h_decl_i h_find_float h_shape h_decl_float
                  have h_decl_new :
                      ∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db { fr with hyps := fr.hyps.push lbl } i v := by
                    intro v h_mem
                    exact floatDeclaredBefore_of_prefix db fr lbl i v (Nat.le_of_lt h_old) (h_scoped_i'.2 v h_mem)
                  have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
                    Array.getElem!_push_lt h_old
                  simp [h_get, h_find_i]
                  exact ⟨h_syms_new, h_decl_new⟩
              | false =>
                  have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
                    Array.getElem!_push_lt h_old
                  simp [h_get, h_find_i]
          | _ =>
              have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
                Array.getElem!_push_lt h_old
              simp [h_get, h_find_i]
    · -- new index: i = fr.hyps.size
      have h_lt : i < fr.hyps.size + 1 := by
        simpa [Array.size_push] using hi
      have h_le : i ≤ fr.hyps.size := Nat.le_of_lt_succ h_lt
      have h_ge : fr.hyps.size ≤ i := Nat.le_of_not_lt h_old
      have h_eq : i = fr.hyps.size := Nat.le_antisymm h_le h_ge
      subst h_eq
      have h_get : (fr.hyps.push lbl)[fr.hyps.size]! = lbl := by
        exact getElem!_push_eq fr.hyps lbl
      simp [h_get, h_find_float]
  · intro v w h_mem
    have h_scoped_dv := h_scoped.2 v w h_mem
    rcases h_scoped_dv with ⟨h_lt, h_in1, h_in2⟩
    have h_in1' :
        v ∈ DB.frameFloatVars db { fr with hyps := fr.hyps.push lbl } := by
      simpa [DB.frameFloatVars] using
        (frameFloatVars_mem_of_mem_prefix db fr.hyps lbl v h_in1)
    have h_in2' :
        w ∈ DB.frameFloatVars db { fr with hyps := fr.hyps.push lbl } := by
      simpa [DB.frameFloatVars] using
        (frameFloatVars_mem_of_mem_prefix db fr.hyps lbl w h_in2)
    exact ⟨h_lt, h_in1', h_in2'⟩

theorem wellScopedFrame_push_ess
    (db : DB) (fr : Frame) (lbl : String)
    (f_ess : Formula) (lbl_ess : String)
    (h_scoped : WellScopedFrame db fr)
    (h_find_ess : db.find? lbl = some (.hyp true f_ess lbl_ess))
    (h_syms : DB.formulaSymsRespectFrame db f_ess (Frame.mk #[] fr.hyps) = true) :
    WellScopedFrame db { fr with hyps := fr.hyps.push lbl } := by
  constructor
  · intro i hi
    by_cases h_old : i < fr.hyps.size
    · have h_scoped_i := h_scoped.1 i h_old
      cases h_find_i : db.find? fr.hyps[i]! with
      | none =>
          have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
            Array.getElem!_push_lt h_old
          simp [h_get, h_find_i] at h_scoped_i ⊢
      | some obj_i =>
          cases obj_i with
          | hyp ess f lbl' =>
              cases ess with
              | true =>
                  have h_scoped_i' :
                      DB.formulaSymsRespectFrame db f (Frame.mk #[] fr.hyps) = true ∧
                      (∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db fr i v) := by
                    simpa [h_find_i] using h_scoped_i
                  have h_syms_new :
                      DB.formulaSymsRespectFrame db f (Frame.mk #[] (fr.hyps.push lbl)) = true := by
                    exact formulaSymsRespectFrame_push_ess db f fr.hyps lbl f_ess lbl_ess h_scoped_i'.1 h_find_ess
                  have h_decl_new :
                      ∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db { fr with hyps := fr.hyps.push lbl } i v := by
                    intro v h_mem
                    exact floatDeclaredBefore_of_prefix db fr lbl i v (Nat.le_of_lt h_old) (h_scoped_i'.2 v h_mem)
                  have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
                    Array.getElem!_push_lt h_old
                  simp [h_get, h_find_i]
                  exact ⟨h_syms_new, h_decl_new⟩
              | false =>
                  have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
                    Array.getElem!_push_lt h_old
                  simp [h_get, h_find_i]
          | _ =>
              have h_get : (fr.hyps.push lbl)[i]! = fr.hyps[i]! :=
                Array.getElem!_push_lt h_old
              simp [h_get, h_find_i]
    · -- new essential at the end
      have h_lt : i < fr.hyps.size + 1 := by
        simpa [Array.size_push] using hi
      have h_le : i ≤ fr.hyps.size := Nat.le_of_lt_succ h_lt
      have h_ge : fr.hyps.size ≤ i := Nat.le_of_not_lt h_old
      have h_eq : i = fr.hyps.size := Nat.le_antisymm h_le h_ge
      subst h_eq
      have h_get : (fr.hyps.push lbl)[fr.hyps.size]! = lbl := by
        exact getElem!_push_eq fr.hyps lbl
      have h_syms_new :
          DB.formulaSymsRespectFrame db f_ess (Frame.mk #[] (fr.hyps.push lbl)) = true := by
        exact formulaSymsRespectFrame_push_ess db f_ess fr.hyps lbl f_ess lbl_ess h_syms h_find_ess
      have h_decl_new :
          ∀ v, Sym.var v ∈ f_ess.toList.tail → FloatDeclaredBefore db { fr with hyps := fr.hyps.push lbl } fr.hyps.size v := by
        intro v h_mem
        have h_decl_old : FloatDeclaredBefore db fr fr.hyps.size v :=
          floatDeclaredBefore_of_symsRespectFrame db fr f_ess h_syms v h_mem
        exact floatDeclaredBefore_of_prefix db fr lbl fr.hyps.size v (Nat.le_refl _) h_decl_old
      simp [h_get, h_find_ess]
      exact ⟨h_syms_new, h_decl_new⟩
  · intro v w h_mem
    have h_scoped_dv := h_scoped.2 v w h_mem
    rcases h_scoped_dv with ⟨h_lt, h_in1, h_in2⟩
    have h_in1' :
        v ∈ DB.frameFloatVars db { fr with hyps := fr.hyps.push lbl } := by
      have h_in1' :=
        (frameFloatVars_mem_push_ess_iff db fr.hyps lbl f_ess lbl_ess v h_find_ess).2 h_in1
      simpa [DB.frameFloatVars] using h_in1'
    have h_in2' :
        w ∈ DB.frameFloatVars db { fr with hyps := fr.hyps.push lbl } := by
      have h_in2' :=
        (frameFloatVars_mem_push_ess_iff db fr.hyps lbl f_ess lbl_ess w h_find_ess).2 h_in2
      simpa [DB.frameFloatVars] using h_in2'
    exact ⟨h_lt, h_in1', h_in2'⟩

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

theorem floatVarOccursInFrame_true_implies
    (db : DB) (v : String)
    (h_wf : WellFormedDB db)
    (h_true : db.floatVarOccursInFrame v = true) :
    v ∈ DB.frameFloatVars db db.frame := by
  let pred := fun lbl =>
    match db.find? lbl with
    | some (.hyp false prevF _) =>
        prevF.size >= 2 &&
          (match prevF[1]! with | .var v' => v' | _ => "") == v
    | _ => false
  have h_any : db.frame.hyps.toList.any pred = true := by
    change db.floatVarOccursInFrame v = true
    exact h_true
  rcases (List.any_eq_true).1 h_any with ⟨lbl, h_lbl_mem, h_pred_true⟩
  have h_hyp :
      ∃ (f : Formula) (lbl_name : String),
        (db.find? lbl = some (.hyp false f lbl_name)) ∧
        ((f.size >= 2) ∧
          (((match f[1]! with | .var v' => v' | _ => "") == v) = true)) := by
    unfold pred at h_pred_true
    cases h_find_lbl : db.find? lbl with
    | none =>
        simp [h_find_lbl] at h_pred_true
    | some obj =>
        cases obj with
        | const _ =>
            simp [h_find_lbl] at h_pred_true
        | var _ =>
            simp [h_find_lbl] at h_pred_true
        | assert _ _ _ =>
            simp [h_find_lbl] at h_pred_true
        | hyp ess f lbl_name =>
            cases ess with
            | true =>
                simp [h_find_lbl] at h_pred_true
            | false =>
                have h_parts :
                    f.size >= 2 ∧ ((match f[1]! with | .var v' => v' | _ => "") == v) = true := by
                  simpa [h_find_lbl] using h_pred_true
                refine ⟨f, lbl_name, ?_⟩
                constructor
                · simpa using h_find_lbl
                · exact h_parts
  rcases h_hyp with ⟨f, lbl_name, h_find_lbl, h_parts⟩
  have h_beq : ((match f[1]! with | .var v' => v' | _ => "") == v) = true := h_parts.2
  rcases Array.toList_mem_implies_index db.frame.hyps lbl h_lbl_mem with ⟨i, hi, h_eq_lbl⟩
  have h_eq_get : db.frame.hyps[i]'hi = lbl := by
    have h_bang : db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
      simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
    exact h_bang.symm.trans h_eq_lbl
  have h_hyp_ok : HypOK db (db.frame.hyps[i]'hi) := h_wf.1.1 i hi
  rcases h_hyp_ok with ⟨ess, f', lbl_name', h_find_hyp, h_float_hyp, _h_formula_hyp⟩
  have h_find_hyp' : db.find? lbl = some (.hyp ess f' lbl_name') := by
    simpa [h_eq_get] using h_find_hyp
  have h_find_lbl' : db.find? lbl = some (.hyp false f lbl_name) := by
    simpa using h_find_lbl
  have h_eq_obj :
      Object.hyp ess f' lbl_name' = Object.hyp false f lbl_name := by
    have h_find_eq :
        some (Object.hyp ess f' lbl_name') = some (Object.hyp false f lbl_name) := by
      rw [← h_find_hyp', h_find_lbl']
    exact Option.some.inj h_find_eq
  cases h_eq_obj
  have h_float : WellFormedFloat f := h_float_hyp rfl
  have h_shape : f.isFloatShape = true := isFloatShape_of_wellFormedFloat h_float
  rcases h_float.2 with ⟨_c, v0, _h0, h1⟩
  have h_beq' : (v0 == v) = true := by
    simpa [h1] using h_beq
  have h_v0_eq : v0 = v := (beq_iff_eq).1 h_beq'
  have h_f1 : f[1]! = Sym.var v := by
    simpa [h_v0_eq] using h1
  exact (frameFloatVars_mem_iff (db := db) (hyps := db.frame.hyps) (v := v)).2
    ⟨lbl, f, lbl_name, h_lbl_mem, h_find_lbl, h_shape, h_f1⟩

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
              by_cases h_syms :
                  DB.formulaSymsRespectFrame db f (Verify.Frame.mk #[] db.frame.hyps) = true
              · simp [h_db_err, h_syms]
              · have h_no_err' :
                    (db.mkError pos "hypothesis symbols not in frame").error? = none := by
                  simpa [h_head, h_db_err, h_ess, h_syms] using h_no_err
                have : False := by
                  simp [DB.mkError] at h_no_err'
                exact False.elim this
          | false =>
              cases h_shape : f.isFloatShape with
              | true =>
                  by_cases h_size : f.size ≥ 2
                  · by_cases h_dup :
                      (!db.config.allowDuplicateFloat &&
                        db.floatVarOccursInFrame f[1]!.value) = true
                    · have h_no_err' :
                        (db.mkError pos
                          (toString "variable " ++ toString f[1]!.value ++
                            toString " already has $f hypothesis")).error? = none := by
                        simpa [h_head, h_db_err, h_ess, h_shape, h_size, h_dup] using h_no_err
                      have : False := by
                        simp [DB.mkError] at h_no_err'
                      exact False.elim this
                    · simp [h_db_err, h_size, h_dup]
                  · simp [h_db_err, h_size]
              | false =>
                  have h_no_err' :
                      (db.mkError pos "expected a constant and a variable").error? = none := by
                    simp [h_head, h_db_err, h_ess, h_shape] at h_no_err
                    exact h_no_err
                  have : False := by
                    simp [DB.mkError] at h_no_err'
                  exact False.elim this

theorem insertHypChecks_syms_of_no_error
    (db : DB) (pos : Pos) (f : Formula)
    (h_no_err : (DB.insertHypChecks db pos true f).error? = none) :
    DB.formulaSymsRespectFrame db f (Verify.Frame.mk #[] db.frame.hyps) = true := by
  unfold DB.insertHypChecks at h_no_err
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
          -- ess = true branch: formulaSymsRespectFrame must be true or error would be set
          by_cases h_syms :
              DB.formulaSymsRespectFrame db f (Verify.Frame.mk #[] db.frame.hyps) = true
          · exact h_syms
          · have h_no_err' :
                (db.mkError pos "hypothesis symbols not in frame").error? = none := by
              simpa [h_head, h_db_err, h_syms] using h_no_err
            have : False := by
              simp [DB.mkError] at h_no_err'
            exact False.elim this

-- First, we need a helper: insertHyp (full) maintains WellFormedDB
-- This is what we need from Phase A!
theorem insertHyp_full_maintains_wf
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_wf : WellFormedDB db)
    (_h_no_err : db.error? = none)
    (h_no_dup : db.config.allowDuplicateFloat = false)
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
          simpa [h_check_eq_db] using h_dup'
        have h_db_no_err : db.error? = none := by
          simpa [h_check_eq_db] using h_check_ok
        have h_db_err : db.error = false := by
          simp [DB.error, h_db_no_err]
        have h_dup_cond :
            (!db.config.allowDuplicateFloat &&
              db.floatVarOccursInFrame arr[1]!.value) = true := by
          simp [h_no_dup, h_dup_db]
        have h_no_err' :
            (db.mkError pos
              (toString "variable " ++ toString arr[1]!.value ++
                toString " already has $f hypothesis")).error? = none := by
          simpa [DB.insertHypChecks, h_head, h_db_err, h_ess, h_shape, h_size_ge, h_dup_cond] using h_checks_no_err
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

theorem withHyps_push_preserves_scoped_float
    (db : DB) (l : String) (f_float : Formula) (lbl_float : String)
    (h_scoped : WellScopedDB db)
    (h_find : db.find? l = some (.hyp false f_float lbl_float))
    (h_shape : f_float.isFloatShape = true)
    (h_decl_float : FormulaSymbolsDeclared db f_float) :
    WellScopedDB (db.withHyps (·.push l)) := by
  constructor
  · -- Frame-level scoping
    exact wellScopedFrame_push_float db db.frame l f_float lbl_float
      h_scoped.1 h_scoped h_find h_shape h_decl_float
  · intro lbl obj h_find_obj
    have h_find' : db.find? lbl = some obj := by
      simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_find_obj
    cases obj with
    | const _ => simp
    | var _ => simp
    | assert f fr name =>
        have h_scoped_assert := h_scoped.2 lbl (.assert f fr name) h_find'
        simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_scoped_assert
    | hyp ess f lbl' =>
        constructor
        · intro h_mem_new
          have h_mem_new' : lbl ∈ (db.frame.hyps.push l).toList := by
            simpa [DB.withHyps, DB.withFrame] using h_mem_new
          have h_mem_split : lbl ∈ db.frame.hyps.toList ∨ lbl = l := by
            simpa [Array.toList_push] using h_mem_new'
          cases h_mem_split with
          | inl h_old =>
              have h_old_prop := (h_scoped.2 lbl (.hyp ess f lbl') h_find').1 h_old
              have h_decl := (h_scoped.2 lbl (.hyp ess f lbl') h_find').2
              have h_old_prop' :
                  DB.formulaSymsRespectFrame db f (Frame.mk #[] db.frame.hyps) = true := by
                simpa [DB.formulaSymsRespectFrame, DB.frameFloatVars] using h_old_prop
              -- Lift to the pushed frame
              exact formulaSymsRespectFrame_push_float
                db f db.frame.hyps l f_float lbl_float h_old_prop' h_decl h_find h_shape h_decl_float
          | inr h_eq =>
              subst h_eq
              have h_eq_obj :
                  Object.hyp ess f lbl' = Object.hyp false f_float lbl_float := by
                exact Option.some.inj (h_find'.symm.trans h_find)
              cases h_eq_obj
              -- New float label: formula respects the pushed frame
              exact Metamath.WF.formulaSymsRespectFrame_float_self
                db db.frame.hyps lbl f_float lbl_float h_find h_shape
        · -- FormulaSymbolsDeclared is preserved by withHyps
          have h_decl := (h_scoped.2 lbl (.hyp ess f lbl') h_find').2
          simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_decl

theorem withHyps_push_preserves_scoped_ess
    (db : DB) (l : String) (f_ess : Formula) (lbl_ess : String)
    (h_scoped : WellScopedDB db)
    (h_find : db.find? l = some (.hyp true f_ess lbl_ess))
    (h_syms : DB.formulaSymsRespectFrame db f_ess (Frame.mk #[] db.frame.hyps) = true) :
    WellScopedDB (db.withHyps (·.push l)) := by
  constructor
  · -- Frame-level scoping
    exact wellScopedFrame_push_ess db db.frame l f_ess lbl_ess h_scoped.1 h_find h_syms
  · intro lbl obj h_find_obj
    have h_find' : db.find? lbl = some obj := by
      simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_find_obj
    cases obj with
    | const _ => simp
    | var _ => simp
    | assert f fr name =>
        have h_scoped_assert := h_scoped.2 lbl (.assert f fr name) h_find'
        simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_scoped_assert
    | hyp ess f lbl' =>
        constructor
        · intro h_mem_new
          have h_mem_new' : lbl ∈ (db.frame.hyps.push l).toList := by
            simpa [DB.withHyps, DB.withFrame] using h_mem_new
          have h_mem_split : lbl ∈ db.frame.hyps.toList ∨ lbl = l := by
            simpa [Array.toList_push] using h_mem_new'
          cases h_mem_split with
          | inl h_old =>
              have h_old_prop := (h_scoped.2 lbl (.hyp ess f lbl') h_find').1 h_old
              have h_old_prop' :
                  DB.formulaSymsRespectFrame db f (Frame.mk #[] db.frame.hyps) = true := by
                simpa [DB.formulaSymsRespectFrame, DB.frameFloatVars] using h_old_prop
              -- Lift to the pushed frame (essential push doesn't change float vars)
              exact formulaSymsRespectFrame_push_ess db f db.frame.hyps l f_ess lbl_ess h_old_prop' h_find
          | inr h_eq =>
              subst h_eq
              have h_eq_obj :
                  Object.hyp ess f lbl' = Object.hyp true f_ess lbl_ess := by
                exact Option.some.inj (h_find'.symm.trans h_find)
              cases h_eq_obj
              exact formulaSymsRespectFrame_push_ess db f_ess db.frame.hyps lbl f_ess lbl_ess h_syms h_find
        · have h_decl := (h_scoped.2 lbl (.hyp ess f lbl') h_find').2
          simpa [DBCaseAnalysis.DBLemmas.withHyps_preserves_find?] using h_decl

theorem insertHyp_insert_part_maintains_scoped
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_scoped : WellScopedDB db)
    (h_no_err : db.error? = none)
    (h_decl : FormulaSymbolsDeclared db arr)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (.hyp ess arr)).error? = none) :
    WellScopedDB (db.insert pos l (.hyp ess arr)) := by
  have h_not_in_frame : l ∉ db.frame.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index db.frame.hyps l h_mem with ⟨i, hi, h_eq⟩
    have h_eq' : db.frame.hyps[i]'hi = l := by
      have h_bang :
          db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq
    exact (h_fresh_label i hi) h_eq'
  have h_frame_scoped :
      WellScopedFrame (db.insert pos l (.hyp ess arr)) db.frame := by
    exact wellScopedFrame_preserved_by_insert
      db pos l (.hyp ess arr) db.frame h_scoped.1 h_not_in_frame
  have h_frame_scoped' :
      WellScopedFrame (db.insert pos l (.hyp ess arr)) (db.insert pos l (.hyp ess arr)).frame := by
    simpa [insert_frame_unchanged] using h_frame_scoped
  refine ⟨h_frame_scoped', ?_⟩
  intro lbl obj h_find
  by_cases h_lbl : lbl = l
  · cases h_lbl
    have h_db_err : db.error = false := (error_false_iff_error?_none db).2 h_no_err
    have h_insert_err :
        (db.insert pos l (.hyp ess arr)).error = false := by
      exact (error_false_iff_error?_none (db.insert pos l (.hyp ess arr))).2 h_insert_ok
    have h_find_self :
        (db.insert pos l (.hyp ess arr)).find? l = some (.hyp ess arr l) := by
      exact Verify.DB.insert_find?_self db pos l (.hyp ess arr) h_db_err h_fresh_db h_insert_err
    have h_obj_eq : obj = Object.hyp ess arr l := by
      exact Option.some.inj (h_find.symm.trans h_find_self)
    cases h_obj_eq
    constructor
    · intro h_mem
      have h_mem_old : l ∈ db.frame.hyps.toList := by
        simpa [insert_frame_unchanged] using h_mem
      exact (h_not_in_frame h_mem_old).elim
    · exact formulaSymbolsDeclared_preserved_by_insert
        db pos l (.hyp ess arr) arr h_decl h_fresh_db
  · have h_find_old : db.find? lbl = some obj := by
      have h_eq := insert_preserves_find?_ne db pos l lbl (.hyp ess arr) h_lbl
      simpa [h_eq] using h_find
    cases obj with
    | const _ => simp
    | var _ => simp
    | assert f fr name =>
        have h_old := h_scoped.2 lbl (.assert f fr name) h_find_old
        have h_not_in_fr : l ∉ fr.hyps.toList := by
          intro h_mem
          rcases Array.toList_mem_implies_index fr.hyps l h_mem with ⟨i, hi, h_eq⟩
          have h_eq' : fr.hyps[i]'hi = l := by
            have h_bang :
                fr.hyps[i]! = fr.hyps[i]'hi := by
              simpa using (Array.getBang_eq_get_nat (a := fr.hyps) (i := i) (h := hi))
            exact h_bang.symm.trans h_eq
          exact (h_fresh_in_asserts lbl f fr name h_find_old i hi) h_eq'
        have h_scoped_fr :
            WellScopedFrame (db.insert pos l (.hyp ess arr)) fr := by
          exact wellScopedFrame_preserved_by_insert
            db pos l (.hyp ess arr) fr h_old.1 h_not_in_fr
        have h_syms_new :
            DB.formulaSymsRespectFrame (db.insert pos l (.hyp ess arr)) f fr = true := by
          exact formulaSymsRespectFrame_preserved_by_insert
            db pos l (.hyp ess arr) fr f h_not_in_fr h_old.2.1
        have h_decl_new :
            FormulaSymbolsDeclared (db.insert pos l (.hyp ess arr)) f := by
          exact formulaSymbolsDeclared_preserved_by_insert
            db pos l (.hyp ess arr) f h_old.2.2 h_fresh_db
        exact ⟨h_scoped_fr, h_syms_new, h_decl_new⟩
    | hyp ess' f lbl' =>
        have h_old := h_scoped.2 lbl (.hyp ess' f lbl') h_find_old
        constructor
        · intro h_mem
          have h_mem_old : lbl ∈ db.frame.hyps.toList := by
            simpa [insert_frame_unchanged] using h_mem
          have h_syms_old := h_old.1 h_mem_old
          have h_syms_new :=
            formulaSymsRespectFrame_preserved_by_insert
              db pos l (.hyp ess arr) db.frame f h_not_in_frame h_syms_old
          simpa [insert_frame_unchanged] using h_syms_new
        · exact formulaSymbolsDeclared_preserved_by_insert
            db pos l (.hyp ess arr) f h_old.2 h_fresh_db

theorem insertHyp_full_maintains_scoped
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_scoped : WellScopedDB db)
    (h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : ess = false → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_decl : FormulaSymbolsDeclared db arr)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertHyp pos l ess arr).error? = none) :
    WellScopedDB (db.insertHyp pos l ess arr) := by
  obtain ⟨db_after_check, h_def_check, h_check_ok, h_insert_ok⟩ :=
    insertHyp_success_conditions db pos l ess arr h_success
  have h_checks_no_err : (DB.insertHypChecks db pos ess arr).error? = none := by
    simpa [h_def_check] using h_check_ok
  have h_check_eq : db_after_check = db := by
    have h_eq := insertHypChecks_eq_db_of_no_error db pos ess arr h_checks_no_err
    simpa [h_def_check] using h_eq
  have h_insert_ok' : (db.insert pos l (.hyp ess arr)).error? = none := by
    simpa [h_check_eq] using h_insert_ok

  have h_scoped_after_insert :
      WellScopedDB (db.insert pos l (.hyp ess arr)) := by
    exact insertHyp_insert_part_maintains_scoped
      db pos l ess arr h_scoped h_no_err h_decl
      h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok'

  have h_db_err : db.error = false := (error_false_iff_error?_none db).2 h_no_err
  have h_insert_err :
      (db.insert pos l (.hyp ess arr)).error = false := by
    exact (error_false_iff_error?_none (db.insert pos l (.hyp ess arr))).2 h_insert_ok'
  have h_find :
      (db.insert pos l (.hyp ess arr)).find? l = some (.hyp ess arr l) := by
    exact Verify.DB.insert_find?_self db pos l (.hyp ess arr) h_db_err h_fresh_db h_insert_err
  have h_decl_insert :
      FormulaSymbolsDeclared (db.insert pos l (.hyp ess arr)) arr := by
    exact formulaSymbolsDeclared_preserved_by_insert
      db pos l (.hyp ess arr) arr h_decl h_fresh_db

  have h_not_in_frame : l ∉ db.frame.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index db.frame.hyps l h_mem with ⟨i, hi, h_eq⟩
    have h_eq' : db.frame.hyps[i]'hi = l := by
      have h_bang :
          db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq
    exact (h_fresh_label i hi) h_eq'

  have h_scoped_final :
      WellScopedDB ((db.insert pos l (.hyp ess arr)).withHyps (·.push l)) := by
    cases h_ess : ess with
    | false =>
        have h_shape : Formula.isFloatShape arr = true := by
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
          unfold Formula.isFloatShape
          cases h0 : arr[0]! with
          | const _ =>
              cases h1 : arr[1]! with
              | var _ => simp [h_size_eq]
              | const _ =>
                  have : False := by
                    simp [Sym.isVar, h1] at h_var1
                  exact False.elim this
          | var _ =>
              have : False := by
                simp [Sym.isVar, h0] at h_notvar0
              exact False.elim this
        have h_find_float :
            (db.insert pos l (.hyp ess arr)).find? l = some (.hyp false arr l) := by
          simpa [h_ess] using h_find
        have h_scoped_final' :
            WellScopedDB ((db.insert pos l (.hyp false arr)).withHyps (·.push l)) := by
          exact withHyps_push_preserves_scoped_float
            (db := db.insert pos l (.hyp false arr))
            (l := l) (f_float := arr) (lbl_float := l)
            (by simpa [h_ess] using h_scoped_after_insert)
            (by simpa [h_ess] using h_find_float)
            h_shape
            (by simpa [h_ess] using h_decl_insert)
        simpa [h_ess] using h_scoped_final'
    | true =>
        have h_syms_old :
            DB.formulaSymsRespectFrame db arr (Verify.Frame.mk #[] db.frame.hyps) = true := by
          have h_no_err' : (DB.insertHypChecks db pos true arr).error? = none := by
            simpa [h_ess] using h_checks_no_err
          exact insertHypChecks_syms_of_no_error db pos arr h_no_err'
        have h_syms_new :
            DB.formulaSymsRespectFrame (db.insert pos l (.hyp ess arr)) arr
              (Verify.Frame.mk #[] db.frame.hyps) = true := by
          exact formulaSymsRespectFrame_preserved_by_insert
            db pos l (.hyp ess arr) (Verify.Frame.mk #[] db.frame.hyps) arr h_not_in_frame h_syms_old
        have h_find_ess :
            (db.insert pos l (.hyp ess arr)).find? l = some (.hyp true arr l) := by
          simpa [h_ess] using h_find
        have h_syms_new' :
            DB.formulaSymsRespectFrame (db.insert pos l (.hyp ess arr)) arr
              (Verify.Frame.mk #[] (db.insert pos l (.hyp ess arr)).frame.hyps) = true := by
          simpa [insert_frame_unchanged] using h_syms_new
        have h_scoped_final' :
            WellScopedDB ((db.insert pos l (.hyp true arr)).withHyps (·.push l)) := by
          exact withHyps_push_preserves_scoped_ess
            (db := db.insert pos l (.hyp true arr))
            (l := l) (f_ess := arr) (lbl_ess := l)
            (by simpa [h_ess] using h_scoped_after_insert)
            (by simpa [h_ess] using h_find_ess)
            (by simpa [h_ess] using h_syms_new')
        simpa [h_ess] using h_scoped_final'

  have h_check_err : (DB.insertHypChecks db pos ess arr).error = false := by
    exact (error_false_iff_error?_none _).2 h_checks_no_err
  have h_check_eq' : db.insertHypChecks pos ess arr = db := by
    simpa [h_def_check] using h_check_eq
  have h_insertHyp_eq :
      db.insertHyp pos l ess arr =
        (db.insert pos l (.hyp ess arr)).withHyps (·.push l) := by
    unfold DB.insertHyp
    simp [h_check_eq', h_db_err, h_insert_err]

  simpa [h_insertHyp_eq] using h_scoped_final

theorem wellScopedFrame_preserved_by_withHyps
    (db : DB) (f : Array String → Array String) (fr : Frame) :
    WellScopedFrame db fr → WellScopedFrame (db.withHyps f) fr := by
  intro h
  -- `withHyps` does not change `find?`, and all scoping predicates are defined in terms of `find?`
  -- on labels appearing in `fr`.
  simpa [WellScopedFrame, FloatDeclaredBefore, DB.formulaSymsRespectFrame, DB.frameFloatVars,
    DBCaseAnalysis.DBLemmas.withHyps_preserves_find?, DB.find?] using h

theorem wellScopedFrame_preserved_by_withDJ
    (db : DB) (f : Array DJ → Array DJ) (fr : Frame) :
    WellScopedFrame db fr → WellScopedFrame (db.withDJ f) fr := by
  intro h
  -- `withDJ` only mutates the current frame's DJ array; lookups and hypothesis arrays stay unchanged.
  simpa [WellScopedFrame, FloatDeclaredBefore, DB.formulaSymsRespectFrame, DB.frameFloatVars,
    DB.withDJ, DB.withFrame, DB.find?] using h

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

theorem pairwise_lt_nth {l : List Nat} (h : l.Pairwise (· < ·)) :
    ∀ {i j} (hi : i < l.length) (hj : j < l.length) (_hij : i < j),
      l[i] < l[j] := by
  induction l with
  | nil =>
      intro i j hi
      cases hi
  | cons a l ih =>
      intro i j hi hj hij
      cases i with
      | zero =>
          cases j with
          | zero =>
              cases hij
          | succ j' =>
              cases h with
              | cons h_head h_tail =>
                  have hj' : j' < l.length := by
                    simpa using (Nat.lt_of_succ_lt_succ hj)
                  have h_mem : l[j'] ∈ l := List.getElem_mem (by simpa using hj')
                  have h_lt : a < l[j'] := h_head _ h_mem
                  simpa using h_lt
      | succ i' =>
          cases j with
          | zero =>
              cases hij
          | succ j' =>
              cases h with
              | cons h_head h_tail =>
                  have hi' : i' < l.length := by
                    simpa using (Nat.lt_of_succ_lt_succ hi)
                  have hj' : j' < l.length := by
                    simpa using (Nat.lt_of_succ_lt_succ hj)
                  have hij' : i' < j' := Nat.lt_of_succ_lt_succ hij
                  have h_lt := ih h_tail hi' hj' hij'
                  simpa using h_lt

theorem pairwise_range' (s n : Nat) : List.Pairwise (· < ·) (List.range' s n) := by
  induction n generalizing s with
  | zero =>
      simp
  | succ n ih =>
      -- range' s (n+1) = s :: range' (s+1) n
      apply List.Pairwise.cons
      · intro b hb
        rcases (List.mem_range' (m := b) (s := s + 1) (n := n) (step := 1)).1 hb with
          ⟨i, _hi, rfl⟩
        have h_lt : s < s + 1 + i := by
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self s) (Nat.le_add_right _ _)
        simpa using h_lt
      · simpa using (ih (s := s + 1))

theorem foldlVars_contains_of_mem
    (f : Formula) (vars : HashSet String) (v0 : String)
    (h_mem : Sym.var v0 ∈ f.toList.tail) :
    (f.foldlVars vars HashSet.insert).contains v0 = true := by
  -- Rewrite foldlVars to a list fold over the tail.
  have h_fold :
      f.foldlVars vars HashSet.insert =
        (f.toList.tail).foldl
          (fun a s => match s with
            | Sym.var v => HashSet.insert a v
            | _ => a) vars := by
    unfold Formula.foldlVars
    simpa using
      (_root_.List.ArrayListExt.Array.foldl_eq_list_foldl_drop (arr := f) (init := vars) (start := 1)
        (f := fun a s => match s with
          | Sym.var v => HashSet.insert a v
          | _ => a))
  -- Prove the list fold inserts v.
  have h_list :
      ∀ (ls : List Sym) (acc : HashSet String),
        Sym.var v0 ∈ ls →
        (ls.foldl (fun a s => match s with
          | Sym.var v => HashSet.insert a v
          | _ => a) acc).contains v0 = true := by
    -- Helper: once a variable is contained, further inserts keep it contained.
    have h_preserve :
        ∀ (ls : List Sym) (acc : HashSet String),
          acc.contains v0 = true →
          (ls.foldl (fun a s => match s with
            | Sym.var v => HashSet.insert a v
            | _ => a) acc).contains v0 = true := by
      intro ls
      induction ls with
      | nil =>
          intro acc h_cont
          simpa [List.foldl] using h_cont
      | cons s ss ih =>
          intro acc h_cont
          cases s with
          | var v' =>
              have h_cont' : (acc.insert v').contains v0 = true := by
                -- insert preserves existing membership
                simp [HashSet.contains_insert, h_cont]
              simpa [List.foldl] using ih (acc := acc.insert v') h_cont'
          | const _ =>
              simpa [List.foldl] using ih (acc := acc) h_cont
    intro ls
    induction ls with
    | nil =>
        intro acc h_mem'
        cases h_mem'
    | cons s ss ih =>
        intro acc h_mem'
        have h_mem' : Sym.var v0 = s ∨ Sym.var v0 ∈ ss := by
          simpa using (List.mem_cons).1 h_mem'
        cases h_mem' with
        | inl h_eq =>
            subst h_eq
            -- head inserts v; folding preserves membership
            have h_cont : (acc.insert v0).contains v0 = true := by
              simp [HashSet.contains_insert]
            simpa [List.foldl] using h_preserve ss (acc.insert v0) h_cont
        | inr h_mem_tail =>
            cases s with
            | var v' =>
                by_cases h_eq : v' = v0
                ·
                  have h_cont : (acc.insert v0).contains v0 = true := by
                    simp [HashSet.contains_insert]
                  simpa [List.foldl, h_eq] using h_preserve ss (acc.insert v0) h_cont
                ·
                  have h' := ih (acc := acc.insert v') h_mem_tail
                  simpa [List.foldl, h_eq] using h'
            | const _ =>
                have h' := ih (acc := acc) h_mem_tail
                simpa [List.foldl] using h'
  -- Apply the list lemma to the tail.
  simpa [h_fold] using (h_list (f.toList.tail) vars h_mem)

theorem foldlVars_preserves_contains
    (f : Formula) (vars : HashSet String) (v0 : String)
    (h_cont : vars.contains v0 = true) :
    (f.foldlVars vars HashSet.insert).contains v0 = true := by
  -- Rewrite foldlVars to a list fold over the tail.
  have h_fold :
      f.foldlVars vars HashSet.insert =
        (f.toList.tail).foldl
          (fun a s => match s with
            | Sym.var v => HashSet.insert a v
            | _ => a) vars := by
    unfold Formula.foldlVars
    simpa using
      (_root_.List.ArrayListExt.Array.foldl_eq_list_foldl_drop (arr := f) (init := vars) (start := 1)
        (f := fun a s => match s with
          | Sym.var v => HashSet.insert a v
          | _ => a))
  -- Folding with inserts preserves existing membership.
  have h_preserve :
      ∀ (ls : List Sym) (acc : HashSet String),
        acc.contains v0 = true →
        (ls.foldl (fun a s => match s with
          | Sym.var v => HashSet.insert a v
          | _ => a) acc).contains v0 = true := by
    intro ls
    induction ls with
    | nil =>
        intro acc h_cont'
        simpa [List.foldl] using h_cont'
    | cons s ss ih =>
        intro acc h_cont'
        cases s with
        | var v' =>
            have h_cont'' : (acc.insert v').contains v0 = true := by
              simp [HashSet.contains_insert, h_cont']
            simpa [List.foldl] using ih (acc := acc.insert v') h_cont''
        | const _ =>
            simpa [List.foldl] using ih (acc := acc) h_cont'
  simpa [h_fold] using (h_preserve (f.toList.tail) vars h_cont)

def collectVarsFromHypsList (db : DB) (ls : List String) (vars : HashSet String) :
    HashSet String :=
  ls.foldl
    (fun acc l =>
      match db.find? l with
      | some (.hyp true f _) => f.foldlVars acc HashSet.insert
      | _ => acc) vars

theorem collectVarsFromHypsList_preserves_contains
    (db : DB) (ls : List String) (vars : HashSet String) (v0 : String)
    (h_cont : vars.contains v0 = true) :
    (collectVarsFromHypsList db ls vars).contains v0 = true := by
  induction ls generalizing vars with
  | nil =>
      simpa [collectVarsFromHypsList] using h_cont
  | cons l ls ih =>
      simp [collectVarsFromHypsList]
      cases h_find : db.find? l with
      | none =>
          simpa using ih (vars := vars) h_cont
      | some obj =>
          cases obj with
          | hyp ess f lbl =>
              cases ess with
              | true =>
                  have h_cont' :
                      (f.foldlVars vars HashSet.insert).contains v0 = true :=
                    foldlVars_preserves_contains f vars v0 h_cont
                  simpa using ih (vars := f.foldlVars vars HashSet.insert) h_cont'
              | false =>
                  simpa using ih (vars := vars) h_cont
          | _ =>
              simpa using ih (vars := vars) h_cont

theorem collectVarsFromHypsList_contains_of_mem
    (db : DB) (ls : List String) (vars : HashSet String)
    (lbl : String) (f : Formula) (lbl' : String)
    (h_mem : lbl ∈ ls)
    (h_find : db.find? lbl = some (.hyp true f lbl'))
    (v : String) (h_mem_v : Sym.var v ∈ f.toList.tail) :
    (collectVarsFromHypsList db ls vars).contains v = true := by
  revert vars h_mem h_find
  induction ls with
  | nil =>
      intro vars h_mem h_find
      cases h_mem
  | cons l ls ih =>
      intro vars h_mem h_find
      have h_mem' : lbl = l ∨ lbl ∈ ls := by
        simpa using (List.mem_cons).1 h_mem
      cases h_mem' with
      | inl h_eq =>
          subst h_eq
          -- head is the target label; insert its vars, then preserve through tail
          simp [collectVarsFromHypsList, h_find]
          have h_cont :
              (f.foldlVars vars HashSet.insert).contains v = true :=
            foldlVars_contains_of_mem f vars v h_mem_v
          exact collectVarsFromHypsList_preserves_contains
            db ls (f.foldlVars vars HashSet.insert) v h_cont
      | inr h_mem_tail =>
          cases h_find_l : db.find? l with
          | none =>
              simp [collectVarsFromHypsList, h_find_l]
              exact ih (vars := vars) h_mem_tail h_find
          | some obj =>
              cases obj with
              | hyp ess f1 lbl1 =>
                  cases ess with
                  | true =>
                      simp [collectVarsFromHypsList, h_find_l]
                      exact ih (vars := f1.foldlVars vars HashSet.insert) h_mem_tail h_find
                  | false =>
                      simp [collectVarsFromHypsList, h_find_l]
                      exact ih (vars := vars) h_mem_tail h_find
              | _ =>
                  simp [collectVarsFromHypsList, h_find_l]
                  exact ih (vars := vars) h_mem_tail h_find

def collectFloatVarsFromHypsList (db : DB) (vars : HashSet String) (ls : List String) :
    HashSet String :=
  ls.foldl
    (fun acc l =>
      match db.find? l with
      | some (.hyp false f _) =>
          let v := f[1]!.value
          if vars.contains v then acc.insert v else acc
      | _ => acc) ∅

private theorem collectFloatVarsFromHypsList_mem_implies
    (db : DB) (vars : HashSet String) (ls : List String) (v : String)
    (h_mem : v ∈ collectFloatVarsFromHypsList db vars ls) :
    ∃ lbl f lbl', lbl ∈ ls ∧
      db.find? lbl = some (.hyp false f lbl') ∧
      f[1]!.value = v := by
  let step : HashSet String → String → HashSet String :=
    fun acc l =>
      match db.find? l with
      | some (.hyp false f _) =>
          let v0 := f[1]!.value
          if vars.contains v0 then acc.insert v0 else acc
      | _ => acc
  have h_mem' : v ∈ ls.foldl step ∅ := by
    simpa [collectFloatVarsFromHypsList, step] using h_mem
  have h_aux :
      ∀ (ls : List String) (acc : HashSet String),
        v ∈ ls.foldl step acc →
        v ∉ acc →
        ∃ lbl f lbl', lbl ∈ ls ∧
          db.find? lbl = some (.hyp false f lbl') ∧
          f[1]!.value = v := by
    intro ls acc h_mem_acc h_not
    induction ls generalizing acc with
    | nil =>
        have : v ∈ acc := by
          simpa using h_mem_acc
        exact (h_not this).elim
    | cons l ls ih =>
        have lift_tail :
            (∃ lbl f lbl', lbl ∈ ls ∧
              db.find? lbl = some (.hyp false f lbl') ∧
              f[1]!.value = v) →
            ∃ lbl f lbl', lbl ∈ l :: ls ∧
              db.find? lbl = some (.hyp false f lbl') ∧
              f[1]!.value = v := by
          intro h
          rcases h with ⟨lbl, f', lbl', h_mem_lbl, h_find_lbl, h_val⟩
          exact ⟨lbl, f', lbl', List.mem_cons_of_mem _ h_mem_lbl, h_find_lbl, h_val⟩
        cases h_find : db.find? l with
        | none =>
            have h_mem_tail : v ∈ ls.foldl step acc := by
              simpa [step, h_find, List.foldl] using h_mem_acc
            exact lift_tail (ih (acc := acc) h_mem_tail h_not)
        | some obj =>
            cases obj with
            | hyp ess f lbl' =>
                cases ess with
                | true =>
                    have h_mem_tail : v ∈ ls.foldl step acc := by
                      simpa [step, h_find, List.foldl] using h_mem_acc
                    exact lift_tail (ih (acc := acc) h_mem_tail h_not)
                | false =>
                    by_cases h_in : vars.contains f[1]!.value = true
                    · have h_in_mem : f[1]!.value ∈ vars :=
                        (Std.HashSet.mem_iff_contains).2 (by simpa using h_in)
                      have h_mem_tail : v ∈ ls.foldl step (acc.insert f[1]!.value) := by
                        simpa [step, h_find, h_in, h_in_mem, List.foldl] using h_mem_acc
                      by_cases h_eq : f[1]!.value = v
                      · subst h_eq
                        refine ⟨l, f, lbl', ?_, ?_, rfl⟩
                        · simp
                        · simpa [h_find]
                      ·
                        have h_not' : v ∉ acc.insert f[1]!.value := by
                          intro h_mem_ins
                          have h_cont_ins : (acc.insert f[1]!.value).contains v = true :=
                            (Std.HashSet.mem_iff_contains).1 h_mem_ins
                          have h_cont_acc : acc.contains v = true := by
                            simpa [HashSet.contains_insert, h_eq] using h_cont_ins
                          have h_mem_acc' : v ∈ acc :=
                            (Std.HashSet.mem_iff_contains).2 (by simpa using h_cont_acc)
                          exact h_not h_mem_acc'
                        exact lift_tail (ih (acc := acc.insert f[1]!.value) h_mem_tail h_not')
                    ·
                      have h_in_mem : f[1]!.value ∉ vars := by
                        intro h_mem_vars
                        have h_cont_vars : vars.contains f[1]!.value = true :=
                          (Std.HashSet.mem_iff_contains).1 h_mem_vars
                        exact (by simpa [h_in] using h_cont_vars)
                      have h_mem_tail : v ∈ ls.foldl step acc := by
                        simpa [step, h_find, h_in, h_in_mem, List.foldl] using h_mem_acc
                      exact lift_tail (ih (acc := acc) h_mem_tail h_not)
            | const _ =>
                have h_mem_tail : v ∈ ls.foldl step acc := by
                  simpa [step, h_find, List.foldl] using h_mem_acc
                exact lift_tail (ih (acc := acc) h_mem_tail h_not)
            | var _ =>
                have h_mem_tail : v ∈ ls.foldl step acc := by
                  simpa [step, h_find, List.foldl] using h_mem_acc
                exact lift_tail (ih (acc := acc) h_mem_tail h_not)
            | assert _ _ _ =>
                have h_mem_tail : v ∈ ls.foldl step acc := by
                  simpa [step, h_find, List.foldl] using h_mem_acc
                exact lift_tail (ih (acc := acc) h_mem_tail h_not)
  have h_not : v ∉ (∅ : HashSet String) := by
    simp
  exact h_aux ls ∅ h_mem' h_not

theorem collectFloatVarsFromHypsList_contains_implies
    (db : DB) (vars : HashSet String) (ls : List String) (v : String)
    (h_cont : (collectFloatVarsFromHypsList db vars ls).contains v = true) :
    ∃ lbl f lbl', lbl ∈ ls ∧
      db.find? lbl = some (.hyp false f lbl') ∧
      f[1]!.value = v := by
  have h_mem : v ∈ collectFloatVarsFromHypsList db vars ls :=
    (Std.HashSet.mem_iff_contains).2 (by simpa using h_cont)
  exact collectFloatVarsFromHypsList_mem_implies db vars ls v h_mem

theorem collectFloatVarsFromHypsList_contains_implies_frameFloatVars
    (db : DB) (vars : HashSet String) (v : String)
    (h_wf : WellFormedDB db)
    (h_cont : (collectFloatVarsFromHypsList db vars db.frame.hyps.toList).contains v = true) :
    v ∈ DB.frameFloatVars db db.frame := by
  rcases collectFloatVarsFromHypsList_contains_implies db vars db.frame.hyps.toList v h_cont with
    ⟨lbl, f, lbl', h_mem, h_find, h_f1_val⟩
  have h_wff : WellFormedFloat f := by
    have h_obj := h_wf.2 lbl (Object.hyp false f lbl') h_find
    simpa using h_obj
  have h_shape : f.isFloatShape = true :=
    by
      rcases h_wff with ⟨h_size, c', v', h0, h1⟩
      have h0_lt : 0 < f.size := by
        simpa [h_size]
      have h1_lt : 1 < f.size := by
        simpa [h_size]
      have h0' : f[0]'h0_lt = Sym.const c' := by
        simpa [Array.getBang_eq_get_nat (a := f) (i := 0) (h := h0_lt)] using h0
      have h1' : f[1]'h1_lt = Sym.var v' := by
        simpa [Array.getBang_eq_get_nat (a := f) (i := 1) (h := h1_lt)] using h1
      unfold Formula.isFloatShape
      simp [h_size, h0', h1']
  have h_f1 : f[1]! = Sym.var v := by
    rcases h_wff with ⟨_h_size, _c, v', _h0, h1⟩
    have h_val : v' = v := by
      have h_val' : (f[1]!).value = v' := by
        simp [h1, Verify.Sym.value]
      exact h_val'.symm.trans h_f1_val
    simpa [h_val] using h1
  apply (frameFloatVars_mem_iff db db.frame.hyps v).2
  refine ⟨lbl, f, lbl', h_mem, ?_, h_shape, ?_⟩
  · exact h_find
  · exact h_f1

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

theorem trimFrameHypsPairsList_pairwise_fst
    (db : DB) (vars : HashSet String) (ls : List String) :
    List.Pairwise (· < ·)
      ((_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst) := by
  -- Sublist of the range of indices
  have h_sub :
      List.Sublist
        (((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map Prod.snd)
        (List.range' 0 ls.length) := by
    have h_sub' :
        List.Sublist
          (((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map Prod.snd)
          ((List.zipIdx ls 0).map Prod.snd) :=
      List.Sublist.map _ (List.filter_sublist)
    simpa [List.zipIdx_map_snd] using h_sub'
  have h_pair_range : List.Pairwise (· < ·) (List.range' 0 ls.length) :=
    pairwise_range' 0 ls.length
  have h_pair_sub :
      List.Pairwise (· < ·)
        (((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map Prod.snd) :=
    List.Pairwise.sublist h_sub h_pair_range
  have h_eq :
      (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst =
        ((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map Prod.snd := by
    simp [_root_.Metamath.Verify.DB.trimFrameHypsPairsList, List.map_map]
  simpa [h_eq] using h_pair_sub

theorem trimFrameHypsPairsList_index_lt
    (db : DB) (vars : HashSet String) (ls : List String)
    {i j : Nat} (hi : i < (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).length)
    (hj : j < (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).length)
    (hij : i < j) :
    (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls)[i].1 <
      (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls)[j].1 := by
  have h_pair :=
    trimFrameHypsPairsList_pairwise_fst (db := db) (vars := vars) (ls := ls)
  have hi' : i < ((_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst).length := by
    simpa [List.length_map] using hi
  have hj' : j < ((_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst).length := by
    simpa [List.length_map] using hj
  have h_lt := pairwise_lt_nth h_pair hi' hj' hij
  have h_i :
      ((_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst)[i] =
        (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls)[i].1 := by
    simpa using
      (List.getElem_map (f := Prod.fst)
        (l := _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls) (i := i))
  have h_j :
      ((_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls).map Prod.fst)[j] =
        (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls)[j].1 := by
    simpa using
      (List.getElem_map (f := Prod.fst)
        (l := _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls) (i := j))
  simpa [h_i, h_j] using h_lt

theorem trimFrameHypsPairs_index_lt
    (db : DB) (vars : HashSet String) (hyps : Array String)
    {i j : Nat} (hi : i < (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).size)
    (hj : j < (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).size)
    (hij : i < j) :
    (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps)[i].1 <
      (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps)[j].1 := by
  have h_pairs_list :
      (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).toList =
        _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
    simp [_root_.Metamath.Verify.DB.trimFrameHypsPairs]
  have hi_list : i < (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).toList.length := by
    simpa [Array.length_toList] using hi
  have hj_list : j < (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).toList.length := by
    simpa [Array.length_toList] using hj
  have h_lt_list :
      (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList)[i].1 <
        (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList)[j].1 := by
    have hi' : i < (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList).length := by
      simpa [h_pairs_list] using hi_list
    have hj' : j < (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList).length := by
      simpa [h_pairs_list] using hj_list
    exact trimFrameHypsPairsList_index_lt (db := db) (vars := vars) (ls := hyps.toList) hi' hj' hij
  have h_i :
      (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps)[i] =
        (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList)[i] := by
    have h_eq := (Array.getElem_toList (xs := _root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps) (i := i) hi)
    simpa [h_pairs_list] using h_eq
  have h_j :
      (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps)[j] =
        (_root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList)[j] := by
    have h_eq := (Array.getElem_toList (xs := _root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps) (i := j) hj)
    simpa [h_pairs_list] using h_eq
  simpa [h_i, h_j] using h_lt_list

theorem trimFrameHypsPairsList_mem_of_keep
    {db : DB} {vars : HashSet String} {ls : List String} {i : Nat}
    (hi : i < ls.length)
    (h_keep : _root_.Metamath.Verify.DB.trimFrameKeep db vars ls[i] = true) :
    (i, ls[i]) ∈ _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 ls := by
  have h_get : ls[i]? = some ls[i] :=
    List.getElem?_eq_getElem (l := ls) (i := i) hi
  have h_zip : (ls[i], i) ∈ List.zipIdx ls 0 := by
    exact (List.mem_zipIdx_iff_getElem?).2 (by simpa using h_get)
  have h_filter :
      (ls[i], i) ∈ (List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1) := by
    exact List.mem_filter.2 ⟨h_zip, by simpa using h_keep⟩
  have h_map :
      (i, ls[i]) ∈ ((List.zipIdx ls 0).filter (fun p => _root_.Metamath.Verify.DB.trimFrameKeep db vars p.1)).map
        (fun p => (p.2, p.1)) := by
    exact List.mem_map.2 ⟨(ls[i], i), h_filter, rfl⟩
  simpa [_root_.Metamath.Verify.DB.trimFrameHypsPairsList] using h_map

theorem trimFrameHyps_mem_of_keep
    (db : DB) (vars : HashSet String) (hyps : Array String)
    {i : Nat} (hi : i < hyps.size)
    (h_keep : _root_.Metamath.Verify.DB.trimFrameKeep db vars hyps[i] = true) :
    hyps[i] ∈ (_root_.Metamath.Verify.DB.trimFrameHyps db vars hyps).toList := by
  have h_mem_list :
      (i, hyps[i]) ∈ _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
    have hi_list : i < hyps.toList.length := by
      simpa [Array.length_toList] using hi
    have h_keep' : _root_.Metamath.Verify.DB.trimFrameKeep db vars hyps.toList[i] = true := by
      simpa using h_keep
    have h_mem := trimFrameHypsPairsList_mem_of_keep (db := db) (vars := vars) (ls := hyps.toList) hi_list h_keep'
    simpa using h_mem
  have h_mem_pairs :
      (i, hyps[i]) ∈ (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).toList := by
    have h_eq :
        (_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).toList =
          _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 hyps.toList := by
      simp [_root_.Metamath.Verify.DB.trimFrameHypsPairs]
    simpa [h_eq] using h_mem_list
  -- map snd to get hyps membership
  have h_mem_map :
      hyps[i] ∈ ((_root_.Metamath.Verify.DB.trimFrameHypsPairs db vars hyps).toList.map Prod.snd) := by
    exact List.mem_map.2 ⟨(i, hyps[i]), h_mem_pairs, rfl⟩
  simpa [_root_.Metamath.Verify.DB.trimFrameHyps, Array.toList_map] using h_mem_map


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

/-
## Proof Strategy for trimFrame'_success_implies_scoped_frame

The trimFrame function filters db.frame.hyps to produce fr.hyps:
- Essential hypotheses are ALWAYS kept (trimFrameKeep returns true for non-floats)
- Floating hypotheses are kept iff their variable is in the collected set

WellScopedFrame requires:
1. Essential hyps: formulaSymsRespectFrame and FloatDeclaredBefore ordering
2. DV pairs: ordered (v < w) and both vars in frameFloatVars

Key observations:
- Variables are collected from fmla AND all essential hyps
- trimFrame succeeds (ok = true) only if all collected vars have floats
- So for each essential hyp kept, all its variables' floats are also kept
- Order preservation (trimFrameHypsPairs_index_lt) ensures float-before-essential ordering
-/

-- Helper: trimFrame's collected vars include all variables from essential hypotheses
-- This follows from how trimFrame iterates over essential hyps and collects their vars

-- Helper: If an essential hyp is in fr.hyps, its variables are in the collected set
-- (Because trimFrame collects from ALL essential hyps in the frame)

-- Helper: FloatDeclaredBefore transfers through an order-preserving filter
theorem floatDeclaredBefore_of_filter
    (db : DB) (fr_orig fr_new : Frame)
    (idx_map : (i : Nat) → (hi : i < fr_new.hyps.size) → {j : Nat // j < fr_orig.hyps.size})
    (_h_eq : ∀ i hi, fr_new.hyps[i]'hi = fr_orig.hyps[(idx_map i hi).val]'(idx_map i hi).property)
    (_h_order : ∀ i j hi hj, i < j → (idx_map i hi).val < (idx_map j hj).val)
    (i : Nat) (hi : i < fr_new.hyps.size) (v : String)
    (_h_decl : FloatDeclaredBefore db fr_orig (idx_map i hi).val v)
    (h_float_kept : ∃ (j : Nat) (hj : j < fr_new.hyps.size), j < i ∧
      ∃ (f : Formula) (lbl : String),
        db.find? (fr_new.hyps[j]'hj) = some (.hyp false f lbl) ∧
        f.isFloatShape = true ∧
        f[1]! = Sym.var v) :
    FloatDeclaredBefore db fr_new i v := by
  rcases h_float_kept with ⟨j, hj, h_ji, f, lbl, h_find, h_shape, h_f1⟩
  refine ⟨j, h_ji, f, lbl, ?_, h_shape, h_f1⟩
  have h_eq : fr_new.hyps[j]! = fr_new.hyps[j]'hj := by
    simpa using (Array.getBang_eq_get_nat (a := fr_new.hyps) (i := j) (h := hj))
  simpa [h_eq] using h_find

theorem floatVar_in_trimmed
    (db : DB) (vars : HashSet String) (fr : Frame)
    (h_hyps_eq : fr.hyps = _root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps)
    (v : String)
    (h_in_frame : v ∈ DB.frameFloatVars db db.frame)
    (h_in_vars : vars.contains v = true) :
    v ∈ DB.frameFloatVars db fr := by
  rcases (frameFloatVars_mem_iff db db.frame.hyps v).1 h_in_frame with
    ⟨lbl, f_float, lbl', h_lbl_mem, h_find, h_shape, h_f1⟩
  rcases Array.toList_mem_implies_index db.frame.hyps lbl h_lbl_mem with
    ⟨j', hj_idx, h_lbl_eq⟩
  have h_find' : db.find? db.frame.hyps[j']! = some (.hyp false f_float lbl') := by
    simpa [h_lbl_eq] using h_find
  have h_keep :
      _root_.Metamath.Verify.DB.trimFrameKeep db vars db.frame.hyps[j']! = true := by
    simp [DB.trimFrameKeep, h_find', h_f1, Sym.value, h_in_vars]
  have h_keep'' :
      _root_.Metamath.Verify.DB.trimFrameKeep db vars db.frame.hyps[j'] = true := by
    have h_eq_bang : db.frame.hyps[j']! = db.frame.hyps[j'] := by
      simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := j') (h := hj_idx))
    simpa [h_eq_bang] using h_keep
  have h_mem_trim' :
      db.frame.hyps[j'] ∈
        (_root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps).toList := by
    exact trimFrameHyps_mem_of_keep db vars db.frame.hyps hj_idx h_keep''
  have h_mem_trim :
      db.frame.hyps[j']! ∈
        (_root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps).toList := by
    have h_eq_bang : db.frame.hyps[j']! = db.frame.hyps[j'] := by
      simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := j') (h := hj_idx))
    simpa [h_eq_bang] using h_mem_trim'
  have h_mem_fr : db.frame.hyps[j']! ∈ fr.hyps.toList := by
    simpa [h_hyps_eq] using h_mem_trim
  apply (frameFloatVars_mem_iff db fr.hyps v).2
  refine ⟨db.frame.hyps[j']!, f_float, lbl', h_mem_fr, ?_, h_shape, h_f1⟩
  exact h_find'

theorem trimFrame'_success_implies_scoped_frame
    (db : DB) (fmla : Formula) (fr : Frame)
    (h_scoped : WellScopedDB db)
    (h_trimFrame : db.trimFrame' fmla = .ok fr) :
    WellScopedFrame db fr := by
  -- Extract trimFrame success
  have h_trim : db.trimFrame fmla = (true, fr) := trimFrame'_ok_iff.mp h_trimFrame
  -- Collected vars (from fmla and all essential hyps in db.frame)
  let vars0 : HashSet String := fmla.foldlVars ∅ HashSet.insert
  let vars : HashSet String :=
    Id.run
      (forIn db.frame.hyps vars0 (fun l r =>
        match db.find? l with
        | some (.hyp true f _) => pure (ForInStep.yield (f.foldlVars r HashSet.insert))
        | _ => pure (ForInStep.yield r)))
  let vars_list : HashSet String := collectVarsFromHypsList db db.frame.hyps.toList vars0
  let pairs := _root_.Metamath.Verify.DB.trimFrameHypsPairs db vars db.frame.hyps

  -- Relate the trimFrame forIn computation to collectVarsFromHypsList
  have h_vars_eq : vars = vars_list := by
    have h :=
      (_root_.List.ArrayListExt.Array.idRun_forIn_yield_eq_foldl
        (arr := db.frame.hyps)
        (init := vars0)
        (step := fun acc l =>
          match db.find? l with
          | some (.hyp true f _) => f.foldlVars acc HashSet.insert
          | _ => acc))
    have h_body :
        (fun l r =>
          match db.find? l with
          | some (.hyp true f _) =>
              (pure (ForInStep.yield (f.foldlVars r HashSet.insert)) : Id (ForInStep (HashSet String)))
          | _ => (pure (ForInStep.yield r) : Id (ForInStep (HashSet String)))) =
        (fun l r =>
          (pure
              (ForInStep.yield
                (match db.find? l with
                | some (.hyp true f _) => f.foldlVars r HashSet.insert
                | _ => r)) : Id (ForInStep (HashSet String)))) := by
      funext l r
      cases h_find : db.find? l with
      | none =>
          simp [h_find]
      | some obj =>
          cases obj with
          | hyp ess f a =>
              cases ess with
              | true =>
                  simp [h_find]
              | false =>
                  by_cases h_in : vars.contains f[1]!.value = true <;>
                    simp [h_find, h_in, Std.HashSet.mem_iff_contains]
          | const _ =>
              simp [h_find]
          | var _ =>
              simp [h_find]
          | assert _ _ _ =>
              simp [h_find]
    have h' :
        Id.run
            (forIn db.frame.hyps vars0 (fun l r =>
              match db.find? l with
              | some (.hyp true f _) => pure (ForInStep.yield (f.foldlVars r HashSet.insert))
              | _ => pure (ForInStep.yield r))) =
          db.frame.hyps.toList.foldl
            (fun acc l =>
              match db.find? l with
              | some (.hyp true f _) => f.foldlVars acc HashSet.insert
              | _ => acc) vars0 := by
      simpa [h_body] using h
    dsimp [vars, vars_list, collectVarsFromHypsList]
    exact h'

  -- Helper: foldl with push equals filter (on toList)
  have foldl_push_filter :
      ∀ (ls : List (String × String)) (pred : (String × String) → Bool) (acc : Array (String × String)),
        (ls.foldl (fun acc a => if pred a then acc.push a else acc) acc).toList =
          acc.toList ++ ls.filter pred := by
    intro ls pred acc
    induction ls generalizing acc with
    | nil =>
        simp
    | cons a ls ih =>
        by_cases h_pred : pred a = true
        · simp [List.foldl, List.filter, h_pred, ih, Array.toList_push, List.append_assoc]
        · simp [List.foldl, List.filter, h_pred, ih]

  -- From trimFrame success, identify the output hyps
  have h_hyps_eq' : (db.trimFrame fmla).2.hyps = fr.hyps := by
    exact congrArg (fun p => p.2.hyps) h_trim
  have h_trim_hyps :
      (db.trimFrame fmla).2.hyps =
        _root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps := by
    rfl
  have h_hyps_eq :
      fr.hyps = _root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps := by
    exact h_hyps_eq'.symm.trans h_trim_hyps

  -- From trimFrame success, identify dj as a filter of db.frame.dj
  have h_dj_eq' : (db.trimFrame fmla).2.dj = fr.dj := by
    exact congrArg (fun p => p.2.dj) h_trim
  have h_dj_eq :
      fr.dj.toList =
        db.frame.dj.toList.filter (fun p => vars.contains p.1 && vars.contains p.2) := by
    have h_trim_dj :
        (db.trimFrame fmla).2.dj =
          Id.run
            (forIn db.frame.dj #[] (fun (v : String × String) (r : Array (String × String)) =>
            if vars.contains v.1 && vars.contains v.2 then
              pure (ForInStep.yield (r.push v))
            else
              pure (ForInStep.yield r))) := by
      rfl
    have h_simp :
        Id.run
            (forIn db.frame.dj #[] (fun (v : String × String) (r : Array (String × String)) =>
              if vars.contains v.1 && vars.contains v.2 then
                pure (ForInStep.yield (r.push v))
              else
                pure (ForInStep.yield r))) = fr.dj := by
      exact h_trim_dj.trans h_dj_eq'
    -- Convert forIn to list fold
    have h_body_dj :
        (fun (v : String × String) (r : Array (String × String)) =>
          if vars.contains v.1 && vars.contains v.2 then
            (pure (ForInStep.yield (r.push v)) : Id (ForInStep (Array (String × String))))
          else
            (pure (ForInStep.yield r) : Id (ForInStep (Array (String × String))))) =
        (fun (v : String × String) (r : Array (String × String)) =>
          (pure
              (ForInStep.yield
                (if vars.contains v.1 && vars.contains v.2 then r.push v else r)) :
            Id (ForInStep (Array (String × String))))) := by
      funext v r
      by_cases h : vars.contains v.1 && vars.contains v.2 <;> simp [h]
    have h_dj_fold :
        Id.run
            (forIn db.frame.dj #[] (fun (v : String × String) (r : Array (String × String)) =>
              if vars.contains v.1 && vars.contains v.2 then
                pure (ForInStep.yield (r.push v))
              else
                pure (ForInStep.yield r))) =
          db.frame.dj.toList.foldl
            (fun (acc : Array (String × String)) (a : String × String) =>
              if vars.contains a.1 && vars.contains a.2 then acc.push a else acc)
            #[] := by
      have h_fold :=
        (_root_.List.ArrayListExt.Array.idRun_forIn_yield_eq_foldl
          (arr := db.frame.dj)
          (init := #[])
          (step := fun (acc : Array (String × String)) (a : String × String) =>
            if vars.contains a.1 && vars.contains a.2 then acc.push a else acc))
      have h_lhs :
          Id.run
              (forIn db.frame.dj #[] (fun (v : String × String) (r : Array (String × String)) =>
                if vars.contains v.1 && vars.contains v.2 then
                  pure (ForInStep.yield (r.push v))
                else
                  pure (ForInStep.yield r))) =
            Id.run
              (forIn db.frame.dj #[] (fun (v : String × String) (r : Array (String × String)) =>
                pure
                  (ForInStep.yield
                    (if vars.contains v.1 && vars.contains v.2 then r.push v else r)))) := by
        rw [h_body_dj]
      exact h_lhs.trans h_fold
    have h_simp_list :
        (List.foldl (fun acc a => if (vars.contains a.1 && vars.contains a.2) then acc.push a else acc)
          #[] db.frame.dj.toList).toList = fr.dj.toList := by
      have h_simp' :
          (db.frame.dj.toList.foldl
            (fun acc a => if (vars.contains a.1 && vars.contains a.2) then acc.push a else acc)
            #[]) = fr.dj := by
        exact h_dj_fold.symm.trans h_simp
      simpa using congrArg Array.toList h_simp'
    have h_filter :
        (List.foldl (fun acc a => if (vars.contains a.1 && vars.contains a.2) then acc.push a else acc)
          #[] db.frame.dj.toList).toList =
          db.frame.dj.toList.filter (fun p => vars.contains p.1 && vars.contains p.2) := by
      have h := foldl_push_filter
        (ls := db.frame.dj.toList)
        (pred := fun p => vars.contains p.1 && vars.contains p.2)
        (acc := #[])
      simpa using h
    exact h_simp_list.symm.trans h_filter

  -- Get well-scoped frame for db.frame
  have h_scoped_frame := h_scoped.1

  -- Helper: if v is a float var in db.frame and v ∈ vars, then v is a float var in fr
  have floatVar_in_trimmed :
      ∀ v, v ∈ DB.frameFloatVars db db.frame →
        vars.contains v = true →
        v ∈ DB.frameFloatVars db fr := by
    intro v h_in_frame h_in_vars
    rcases (frameFloatVars_mem_iff db db.frame.hyps v).1 h_in_frame with
      ⟨lbl, f_float, lbl', h_lbl_mem, h_find, h_shape, h_f1⟩
    rcases Array.toList_mem_implies_index db.frame.hyps lbl h_lbl_mem with
      ⟨j', hj_idx, h_lbl_eq⟩
    have h_find' : db.find? db.frame.hyps[j']! = some (.hyp false f_float lbl') := by
      simpa [h_lbl_eq] using h_find
    have h_keep : _root_.Metamath.Verify.DB.trimFrameKeep db vars db.frame.hyps[j']! = true := by
      simp [DB.trimFrameKeep, h_find', h_f1, Sym.value, h_in_vars]
    have h_keep'' : _root_.Metamath.Verify.DB.trimFrameKeep db vars db.frame.hyps[j'] = true := by
      have h_eq_bang : db.frame.hyps[j']! = db.frame.hyps[j'] := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := j') (h := hj_idx))
      simpa [h_eq_bang] using h_keep
    have h_mem_trim' :
        db.frame.hyps[j'] ∈
          (_root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps).toList := by
      exact trimFrameHyps_mem_of_keep db vars db.frame.hyps hj_idx h_keep''
    have h_mem_trim :
        db.frame.hyps[j']! ∈
          (_root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps).toList := by
      have h_eq_bang : db.frame.hyps[j']! = db.frame.hyps[j'] := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := j') (h := hj_idx))
      simpa [h_eq_bang] using h_mem_trim'
    have h_mem_fr : db.frame.hyps[j']! ∈ fr.hyps.toList := by
      simpa [h_hyps_eq] using h_mem_trim
    -- Conclude v in frameFloatVars of fr
    apply (frameFloatVars_mem_iff db fr.hyps v).2
    refine ⟨db.frame.hyps[j']!, f_float, lbl', h_mem_fr, ?_, h_shape, h_f1⟩
    exact h_find'

  constructor
  · -- Part 1: Essential hypotheses
    intro i hi
    -- Check if this is an essential hypothesis
    cases h_find : db.find? fr.hyps[i]! with
    | none => trivial
    | some obj =>
      cases obj with
      | hyp ess f lbl =>
        cases ess with
        | false => trivial  -- Float, nothing to prove
        | true =>
          -- Essential hypothesis case
          -- Need to show:
          -- 1. formulaSymsRespectFrame db f (Frame.mk #[] fr.hyps) = true
          -- 2. ∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db fr i v

          -- Relate fr.hyps[i] to db.frame via trimFrameHypsPairs
          have hi_pairs : i < pairs.size := by
            -- fr.hyps = pairs.map snd
            have hi' : i < (_root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps).size := by
              simpa [h_hyps_eq] using hi
            simpa [_root_.Metamath.Verify.DB.trimFrameHyps, pairs, Array.size_map] using hi'
          have h_fr_i : fr.hyps[i]! = (pairs[i]'hi_pairs).2 := by
            have h_eq : fr.hyps = (pairs.map Prod.snd) := by
              simpa [_root_.Metamath.Verify.DB.trimFrameHyps, pairs] using h_hyps_eq
            have hi_pairs_map : i < (pairs.map Prod.snd).size := by
              simpa [Array.size_map] using hi_pairs
            have h_get :
                (pairs.map Prod.snd)[i]'hi_pairs_map = (pairs[i]'hi_pairs).2 := by
              simpa using (Array.getElem_map (f := Prod.snd) (a := pairs) (i := i) (h := hi_pairs_map))
            have h_get_bang :
                (pairs.map Prod.snd)[i]! = (pairs[i]'hi_pairs).2 := by
              have h_eq_bang :
                  (pairs.map Prod.snd)[i]! = (pairs.map Prod.snd)[i]'hi_pairs_map := by
                simpa using
                  (Array.getBang_eq_get_nat (a := pairs.map Prod.snd) (i := i) (h := hi_pairs_map))
              simpa [h_eq_bang] using h_get
            have h_fr_bang : fr.hyps[i]! = (pairs.map Prod.snd)[i]! := by
              simpa [h_eq] using (rfl : fr.hyps[i]! = fr.hyps[i]!)
            exact h_fr_bang.trans h_get_bang
          -- Extract the original index for this hypothesis
          have h_pair_mem : pairs[i]'hi_pairs ∈ pairs.toList := by
            have h_mem : pairs.toList[i] ∈ pairs.toList :=
              List.getElem_mem (by simpa using (by
                have := hi_pairs; simp at this; exact this))
            have h_eq : pairs.toList[i] = pairs[i]'hi_pairs :=
              Array.getElem_toList (xs := pairs) (i := i) hi_pairs
            simpa [h_eq] using h_mem
          have h_pair_mem' :
              pairs[i]'hi_pairs ∈
                _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 db.frame.hyps.toList := by
            have h_pairs_list :
                pairs.toList =
                  _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 db.frame.hyps.toList := by
              simp [_root_.Metamath.Verify.DB.trimFrameHypsPairs, pairs]
            simpa [h_pairs_list] using h_pair_mem
          have h_exists :=
            trimFrameHypsPairsList_mem (db := db) (vars := vars) (ls := db.frame.hyps.toList) h_pair_mem'
          have hi' : (pairs[i]'hi_pairs).1 < db.frame.hyps.size := by
            have h_lt : (pairs[i]'hi_pairs).1 < db.frame.hyps.toList.length :=
              Classical.choose h_exists
            simpa [Array.length_toList] using h_lt
          have h_eq_i :
              db.frame.hyps[(pairs[i]'hi_pairs).1]'hi' = (pairs[i]'hi_pairs).2 := by
            have h_eq_list : db.frame.hyps.toList[(pairs[i]'hi_pairs).1] = (pairs[i]'hi_pairs).2 :=
              Classical.choose_spec h_exists
            have h_toList :
                db.frame.hyps.toList[(pairs[i]'hi_pairs).1] =
                  db.frame.hyps[(pairs[i]'hi_pairs).1]'hi' := by
              exact
                (Array.getElem_toList (xs := db.frame.hyps) (i := (pairs[i]'hi_pairs).1) hi')
            simpa [h_toList] using h_eq_list
          have h_eq_i' : fr.hyps[i]! = db.frame.hyps[(pairs[i]'hi_pairs).1]! := by
            have h_eq_i_bang :
                db.frame.hyps[(pairs[i]'hi_pairs).1]! = db.frame.hyps[(pairs[i]'hi_pairs).1]'hi' := by
              simpa using
                (Array.getBang_eq_get_nat
                  (a := db.frame.hyps) (i := (pairs[i]'hi_pairs).1) (h := hi'))
            calc
              fr.hyps[i]! = (pairs[i]'hi_pairs).2 := h_fr_i
              _ = db.frame.hyps[(pairs[i]'hi_pairs).1]'hi' := h_eq_i.symm
              _ = db.frame.hyps[(pairs[i]'hi_pairs).1]! := h_eq_i_bang.symm

          -- Use well-scopedness of db.frame at index i'
          have h_find_frame :
              db.find? db.frame.hyps[(pairs[i]'hi_pairs).1]! = some (.hyp true f lbl) := by
            simpa [h_eq_i'] using h_find
          have h_scoped_i' :
              DB.formulaSymsRespectFrame db f (Frame.mk #[] db.frame.hyps) = true ∧
              (∀ v, Sym.var v ∈ f.toList.tail →
                FloatDeclaredBefore db db.frame (pairs[i]'hi_pairs).1 v) := by
            simpa [h_find_frame] using (h_scoped_frame.1 (pairs[i]'hi_pairs).1 hi')

          -- Show vars.contains v for vars in this essential hypothesis
          have h_vars_contains :
              ∀ v, Sym.var v ∈ f.toList.tail → vars.contains v = true := by
            intro v h_mem
            have h_lbl_mem : fr.hyps[i]! ∈ db.frame.hyps.toList := by
              have h_lbl_mem' : db.frame.hyps[(pairs[i]'hi_pairs).1]! ∈ db.frame.hyps.toList := by
                have h_lt_list : (pairs[i]'hi_pairs).1 < db.frame.hyps.toList.length := by
                  simpa [Array.length_toList] using hi'
                have h_mem' :
                    db.frame.hyps.toList[(pairs[i]'hi_pairs).1] ∈ db.frame.hyps.toList :=
                  List.getElem_mem (by simpa using h_lt_list)
                have h_eq_list :
                    db.frame.hyps.toList[(pairs[i]'hi_pairs).1] =
                      db.frame.hyps[(pairs[i]'hi_pairs).1]! := by
                  have h_eq_list' :
                      db.frame.hyps.toList[(pairs[i]'hi_pairs).1] =
                        db.frame.hyps[(pairs[i]'hi_pairs).1]'hi' :=
                    Array.getElem_toList (xs := db.frame.hyps) (i := (pairs[i]'hi_pairs).1) hi'
                  have h_eq_bang :
                      db.frame.hyps[(pairs[i]'hi_pairs).1]! =
                        db.frame.hyps[(pairs[i]'hi_pairs).1]'hi' := by
                    simpa using
                      (Array.getBang_eq_get_nat
                        (a := db.frame.hyps) (i := (pairs[i]'hi_pairs).1) (h := hi'))
                  simpa [h_eq_bang] using h_eq_list'
                simpa [h_eq_list] using h_mem'
              simpa [h_eq_i'] using h_lbl_mem'
            -- Use collectVarsFromHypsList to show v is in vars_list
            have h_list :
                vars_list.contains v = true := by
              simpa [vars_list] using
                (collectVarsFromHypsList_contains_of_mem
                  (db := db)
                  (ls := db.frame.hyps.toList)
                  (vars := vars0)
                  (lbl := fr.hyps[i]!)
                  (f := f)
                  (lbl' := lbl)
                  h_lbl_mem
                  h_find
                  v
                  h_mem)
            -- Rewrite vars via the list-based characterization
            simpa [h_vars_eq] using h_list

          -- Part 1.1: formulaSymsRespectFrame
          have h_decl_f : FormulaSymbolsDeclared db f := by
            have h_scoped_obj := h_scoped.2 (fr.hyps[i]!) (.hyp true f lbl) h_find
            exact h_scoped_obj.2
          have h_var_in :
              ∀ v, Sym.var v ∈ f.toList.tail →
                v ∈ DB.frameFloatVars db (Frame.mk #[] fr.hyps) := by
            intro v h_mem
            -- From db.frame, v has a float; keep it in fr since v ∈ vars
            have h_decl := h_scoped_i'.2 v h_mem
            rcases h_decl with ⟨j', hj', f_float, lbl_float, h_find_f, h_shape, h_f1⟩
            have hj_frame : j' < db.frame.hyps.size := Nat.lt_trans hj' hi'
            have h_in_frame :
                v ∈ DB.frameFloatVars db db.frame := by
              apply (frameFloatVars_mem_iff db db.frame.hyps v).2
              have h_lbl_mem : db.frame.hyps[j']! ∈ db.frame.hyps.toList := by
                have h_lt_list : j' < db.frame.hyps.toList.length := by
                  simpa [Array.length_toList] using hj_frame
                have h_mem' :
                    db.frame.hyps.toList[j'] ∈ db.frame.hyps.toList :=
                  List.getElem_mem (by simpa using h_lt_list)
                have h_eq_list :
                    db.frame.hyps.toList[j'] = db.frame.hyps[j']! := by
                  have h_eq_list' :
                      db.frame.hyps.toList[j'] = db.frame.hyps[j']'hj_frame :=
                    Array.getElem_toList (xs := db.frame.hyps) (i := j') hj_frame
                  have h_eq_bang :
                      db.frame.hyps[j']! = db.frame.hyps[j']'hj_frame := by
                    simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := j') (h := hj_frame))
                  simpa [h_eq_bang] using h_eq_list'
                simpa [h_eq_list] using h_mem'
              exact ⟨db.frame.hyps[j']!, f_float, lbl_float, h_lbl_mem, h_find_f, h_shape, h_f1⟩
            have h_in_fr := floatVar_in_trimmed v h_in_frame (h_vars_contains v h_mem)
            -- frameFloatVars depends only on hyps, so use mk #[] fr.hyps
            simpa [frameFloatVars_mk_eq] using h_in_fr
          have h_syms :
              DB.formulaSymsRespectFrame db f (Frame.mk #[] fr.hyps) = true := by
            exact formulaSymsRespectFrame_of_declared
              (db := db) (fr := Frame.mk #[] fr.hyps) (f := f)
              h_scoped h_decl_f h_var_in

          -- Part 1.2: FloatDeclaredBefore
          have h_float_before :
              ∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db fr i v := by
            intro v h_mem
            have h_decl := h_scoped_i'.2 v h_mem
            rcases h_decl with ⟨j', hj', f_float, lbl_float, h_find_f, h_shape, h_f1⟩
            have hj_frame : j' < db.frame.hyps.size := Nat.lt_trans hj' hi'
            -- show the float for v is kept in fr
            have h_keep : _root_.Metamath.Verify.DB.trimFrameKeep db vars db.frame.hyps[j']! = true := by
              have h_in_vars := h_vars_contains v h_mem
              simp [DB.trimFrameKeep, h_find_f, h_f1, Sym.value, h_in_vars]
            -- find the pair (j', db.frame.hyps[j']!) in pairs list
            have h_keep_list :
                _root_.Metamath.Verify.DB.trimFrameKeep db vars (db.frame.hyps.toList[j']) = true := by
              have h_eq_list :
                  db.frame.hyps.toList[j'] = db.frame.hyps[j']! := by
                have h_eq_list' :
                    db.frame.hyps.toList[j'] = db.frame.hyps[j']'hj_frame :=
                  Array.getElem_toList (xs := db.frame.hyps) (i := j') hj_frame
                have h_eq_bang :
                    db.frame.hyps[j']! = db.frame.hyps[j']'hj_frame := by
                  simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := j') (h := hj_frame))
                simpa [h_eq_bang] using h_eq_list'
              simpa [h_eq_list] using h_keep
            have h_mem_pairs_list :
                (j', db.frame.hyps.toList[j']) ∈
                  _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 db.frame.hyps.toList := by
              have hj_list : j' < db.frame.hyps.toList.length := by
                simpa [Array.length_toList] using hj_frame
              exact trimFrameHypsPairsList_mem_of_keep
                (db := db) (vars := vars) (ls := db.frame.hyps.toList)
                (i := j') hj_list h_keep_list
            have h_pairs_list :
                pairs.toList =
                  _root_.Metamath.Verify.DB.trimFrameHypsPairsList db vars 0 db.frame.hyps.toList := by
              simp [_root_.Metamath.Verify.DB.trimFrameHypsPairs, pairs]
            have h_mem_pairs : (j', db.frame.hyps[j']!) ∈ pairs.toList := by
              have h_eq_list :
                  db.frame.hyps.toList[j'] = db.frame.hyps[j']! := by
                have h_eq_list' :
                    db.frame.hyps.toList[j'] = db.frame.hyps[j']'hj_frame :=
                  Array.getElem_toList (xs := db.frame.hyps) (i := j') hj_frame
                have h_eq_bang :
                    db.frame.hyps[j']! = db.frame.hyps[j']'hj_frame := by
                  simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := j') (h := hj_frame))
                simpa [h_eq_bang] using h_eq_list'
              simpa [h_pairs_list, h_eq_list] using h_mem_pairs_list
            rcases Array.toList_mem_implies_index pairs (j', db.frame.hyps[j']!) h_mem_pairs with
              ⟨j, hj_pairs, h_pair_eq⟩
            have hj : j < fr.hyps.size := by
              have h_size_eq : fr.hyps.size = pairs.size := by
                simpa [h_hyps_eq, _root_.Metamath.Verify.DB.trimFrameHyps, pairs, Array.size_map]
              simpa [h_size_eq] using hj_pairs
            have h_pair_eq' : pairs[j]'hj_pairs = (j', db.frame.hyps[j']!) := by
              have h_eq_bang : pairs[j]! = pairs[j]'hj_pairs := by
                simpa using (Array.getBang_eq_get_nat (a := pairs) (i := j) (h := hj_pairs))
              simpa [h_eq_bang] using h_pair_eq
            -- derive fr.hyps[j]! = db.frame.hyps[j']!
            have h_fr_j_eq : fr.hyps[j]! = db.frame.hyps[j']! := by
              have h_eq : fr.hyps = pairs.map Prod.snd := by
                simpa [_root_.Metamath.Verify.DB.trimFrameHyps, pairs] using h_hyps_eq
              have hj_pairs_map : j < (pairs.map Prod.snd).size := by
                simpa [Array.size_map] using hj_pairs
              have h_get :
                  (pairs.map Prod.snd)[j]'hj_pairs_map = (pairs[j]'hj_pairs).2 := by
                simpa using (Array.getElem_map (f := Prod.snd) (a := pairs) (i := j) (h := hj_pairs_map))
              have h_fr_bang : fr.hyps[j]! = fr.hyps[j]'hj := by
                simpa using (Array.getBang_eq_get_nat (a := fr.hyps) (i := j) (h := hj))
              calc
                fr.hyps[j]! = fr.hyps[j]'hj := h_fr_bang
                _ = (pairs.map Prod.snd)[j]'hj_pairs_map := by simpa [h_eq]
                _ = (pairs[j]'hj_pairs).2 := h_get
                _ = db.frame.hyps[j']! := by
                  simpa using congrArg Prod.snd h_pair_eq'

            -- Now show j < i using order preservation of pairs
            have h_j_fst : (pairs[j]'hj_pairs).1 = j' := by
              simpa using congrArg Prod.fst h_pair_eq'
            have h_lt_j_i : j < i := by
              by_cases h_lt : j < i
              · exact h_lt
              · have h_le : i ≤ j := Nat.le_of_not_lt h_lt
                have h_ne : i ≠ j := by
                  intro h_eq
                  have h_eq_fst : (pairs[i]'hi_pairs).1 = j' := by
                    simpa [h_eq] using h_j_fst
                  have h_contra : False := by
                    exact (Nat.lt_irrefl j') (by simpa [h_eq_fst] using hj')
                  exact h_contra.elim
                have h_lt_ij : i < j := Nat.lt_of_le_of_ne h_le h_ne
                have h_lt_fst :=
                  trimFrameHypsPairs_index_lt (db := db) (vars := vars) (hyps := db.frame.hyps)
                    (hi := hi_pairs) (hj := hj_pairs) h_lt_ij
                -- contradict j' < i'
                have h_lt' : (pairs[i]'hi_pairs).1 < (pairs[j]'hj_pairs).1 := h_lt_fst
                have h_contra : (pairs[i]'hi_pairs).1 < j' := by
                  simpa [h_j_fst] using h_lt'
                exact (Nat.lt_asymm h_contra hj').elim

            -- Build FloatDeclaredBefore in fr
            refine ⟨j, h_lt_j_i, f_float, lbl_float, ?_, h_shape, h_f1⟩
            -- db.find? fr.hyps[j]! = ...
            simpa [h_fr_j_eq] using h_find_f

          constructor
          · exact h_syms
          · exact h_float_before
      | const _ => trivial
      | var _ => trivial
      | assert _ _ _ => trivial

  · -- Part 2: DV pairs
    intro v w h_mem
    have h_mem' : (v, w) ∈ db.frame.dj.toList ∧
        vars.contains v = true ∧ vars.contains w = true := by
      -- Use the filtered characterization of fr.dj
      have h_mem_filter : (v, w) ∈
          db.frame.dj.toList.filter (fun p => vars.contains p.1 && vars.contains p.2) := by
        simpa [h_dj_eq] using h_mem
      rcases List.mem_filter.1 h_mem_filter with ⟨h_in, h_pred⟩
      have h_pred' : vars.contains v = true ∧ vars.contains w = true := by
        -- extract from Bool.and
        have := h_pred
        have h_pred_bool : (vars.contains v && vars.contains w) = true := by
          simpa using h_pred
        exact (Bool.and_eq_true_iff).1 h_pred_bool
      exact ⟨h_in, h_pred'.1, h_pred'.2⟩
    rcases h_mem' with ⟨h_in_db, h_in_v, h_in_w⟩
    have h_scoped_dj := h_scoped_frame.2 v w h_in_db
    rcases h_scoped_dj with ⟨h_lt, h_in_frame_v, h_in_frame_w⟩
    have h_in_fr_v : v ∈ DB.frameFloatVars db fr :=
      floatVar_in_trimmed v h_in_frame_v h_in_v
    have h_in_fr_w : w ∈ DB.frameFloatVars db fr :=
      floatVar_in_trimmed w h_in_frame_w h_in_w
    exact ⟨h_lt, h_in_fr_v, h_in_fr_w⟩

theorem trimFrame'_success_implies_formulaSymsRespectFrame
    (db : DB) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDB db)
    (h_decl : FormulaSymbolsDeclared db fmla)
    (h_trimFrame : db.trimFrame' fmla = .ok fr) :
    DB.formulaSymsRespectFrame db fmla fr = true := by
  have h_trim : db.trimFrame fmla = (true, fr) := trimFrame'_ok_iff.mp h_trimFrame
  -- Collected vars (from fmla and all essential hyps in db.frame)
  let vars0 : HashSet String := fmla.foldlVars ∅ HashSet.insert
  let vars : HashSet String :=
    Id.run
      (forIn db.frame.hyps vars0 (fun l r =>
        match db.find? l with
        | some (.hyp true f _) => pure (ForInStep.yield (f.foldlVars r HashSet.insert))
        | _ => pure (ForInStep.yield r)))
  let vars_list : HashSet String := collectVarsFromHypsList db db.frame.hyps.toList vars0
  -- Relate the trimFrame forIn computation to collectVarsFromHypsList
  have h_vars_eq : vars = vars_list := by
    have h :=
      (_root_.List.ArrayListExt.Array.idRun_forIn_yield_eq_foldl
        (arr := db.frame.hyps)
        (init := vars0)
        (step := fun acc l =>
          match db.find? l with
          | some (.hyp true f _) => f.foldlVars acc HashSet.insert
          | _ => acc))
    have h_body :
        (fun l r =>
          match db.find? l with
          | some (.hyp true f _) =>
              (pure (ForInStep.yield (f.foldlVars r HashSet.insert)) : Id (ForInStep (HashSet String)))
          | _ => (pure (ForInStep.yield r) : Id (ForInStep (HashSet String)))) =
        (fun l r =>
          (pure
              (ForInStep.yield
                (match db.find? l with
                | some (.hyp true f _) => f.foldlVars r HashSet.insert
                | _ => r)) : Id (ForInStep (HashSet String)))) := by
      funext l r
      cases h_find : db.find? l with
      | none =>
          simp [h_find]
      | some obj =>
          cases obj with
          | hyp ess f a =>
              cases ess with
              | true =>
                  simp [h_find]
              | false =>
                  by_cases h_in : f[1]!.value ∈ vars <;> simp [h_find, h_in]
          | const _ =>
              simp [h_find]
          | var _ =>
              simp [h_find]
          | assert _ _ _ =>
              simp [h_find]
    have h' :
        Id.run
            (forIn db.frame.hyps vars0 (fun l r =>
              match db.find? l with
              | some (.hyp true f _) => pure (ForInStep.yield (f.foldlVars r HashSet.insert))
              | _ => pure (ForInStep.yield r))) =
          db.frame.hyps.toList.foldl
            (fun acc l =>
              match db.find? l with
              | some (.hyp true f _) => f.foldlVars acc HashSet.insert
              | _ => acc) vars0 := by
      simpa [h_body] using h
    dsimp [vars, vars_list, collectVarsFromHypsList]
    exact h'

  -- varsWithF: floats whose variable is in vars
  let varsWithF : HashSet String :=
    Id.run
      (forIn db.frame.hyps (∅ : HashSet String) (fun l r =>
        match db.find? l with
        | some (.hyp false f _) =>
            let v := f[1]!.value
            if vars.contains v then
              pure (ForInStep.yield (r.insert v))
            else
              pure (ForInStep.yield r)
        | _ => pure (ForInStep.yield r)))
  let varsWithF_list : HashSet String :=
    collectFloatVarsFromHypsList db vars db.frame.hyps.toList
  have h_varsWithF_eq : varsWithF = varsWithF_list := by
    have h :=
      (_root_.List.ArrayListExt.Array.idRun_forIn_yield_eq_foldl
        (arr := db.frame.hyps)
        (init := (∅ : HashSet String))
        (step := fun acc l =>
          match db.find? l with
          | some (.hyp false f _) =>
              let v := f[1]!.value
              if vars.contains v then acc.insert v else acc
          | _ => acc))
    have h_body :
        (fun l r =>
          match db.find? l with
          | some (.hyp false f _) =>
              let v := f[1]!.value
              if vars.contains v then
                (pure (ForInStep.yield (r.insert v)) : Id (ForInStep (HashSet String)))
              else
                (pure (ForInStep.yield r) : Id (ForInStep (HashSet String)))
          | _ => (pure (ForInStep.yield r) : Id (ForInStep (HashSet String)))) =
        (fun l r =>
          (pure
              (ForInStep.yield
                (match db.find? l with
                | some (.hyp false f _) =>
                    let v := f[1]!.value
                    if vars.contains v then r.insert v else r
                | _ => r)) : Id (ForInStep (HashSet String)))) := by
      funext l r
      cases h_find : db.find? l with
      | none =>
          simp [h_find]
      | some obj =>
          cases obj with
          | hyp ess f a =>
              cases ess with
              | true =>
                  simp [h_find]
              | false =>
                  by_cases h_in : f[1]!.value ∈ vars <;> simp [h_find, h_in]
          | const _ =>
              simp [h_find]
          | var _ =>
              simp [h_find]
          | assert _ _ _ =>
              simp [h_find]
    have h' :
        Id.run
            (forIn db.frame.hyps (∅ : HashSet String) (fun l r =>
              match db.find? l with
              | some (.hyp false f _) =>
                  let v := f[1]!.value
                  if vars.contains v then
                    pure (ForInStep.yield (r.insert v))
                  else
                    pure (ForInStep.yield r)
              | _ => pure (ForInStep.yield r))) =
          db.frame.hyps.toList.foldl
            (fun acc l =>
              match db.find? l with
              | some (.hyp false f _) =>
                  let v := f[1]!.value
                  if vars.contains v then acc.insert v else acc
              | _ => acc) ∅ := by
      -- Avoid simp rewriting to `True`; rewrite the goal to match `h`.
      rw [h_body]
      exact h
    dsimp [varsWithF, varsWithF_list, collectFloatVarsFromHypsList]
    exact h'

  -- Extract the ok condition from trimFrame
  have h_ok : (db.trimFrame fmla).1 = true := by
    exact congrArg Prod.fst h_trim

  -- ok loop equals foldl over vars.toList
  have h_ok_def :
      (db.trimFrame fmla).1 =
        Id.run
          (forIn vars true (fun v ok =>
            if varsWithF.contains v then
              pure (ForInStep.yield ok)
            else
              pure (ForInStep.yield false))) := by
    rfl
  have h_ok' :
      Id.run
          (forIn vars true (fun v ok =>
            if varsWithF.contains v then
              pure (ForInStep.yield ok)
            else
              pure (ForInStep.yield false))) = true := by
    simpa [h_ok_def] using h_ok
  have h_body_ok :
      (fun v ok =>
        if v ∈ varsWithF then
          (pure (ForInStep.yield ok) : Id (ForInStep Bool))
        else
          (pure (ForInStep.yield false) : Id (ForInStep Bool))) =
      (fun v ok =>
        (pure (ForInStep.yield (ok && varsWithF.contains v)) : Id (ForInStep Bool))) := by
    funext v ok
    by_cases h_mem : v ∈ varsWithF
    · have h_cont : varsWithF.contains v = true :=
        (Std.HashSet.mem_iff_contains).1 h_mem
      simp [h_mem, h_cont]
    · have h_cont : varsWithF.contains v = false := by
        cases h_val : varsWithF.contains v with
        | true =>
            have h_mem' : v ∈ varsWithF :=
              (Std.HashSet.mem_iff_contains).2 (by simpa using h_val)
            exact (h_mem h_mem').elim
        | false =>
            rfl
      simp [h_mem, h_cont]
  have h_forIn_list :
      Id.run
          (forIn vars true (fun v ok =>
            pure (ForInStep.yield (ok && varsWithF.contains v)))) =
        Id.run
          (forIn vars.toList true (fun v ok =>
            pure (ForInStep.yield (ok && varsWithF.contains v)))) := by
    -- Reduce HashSet forIn to list forIn
    have h_eq := (Std.HashSet.forIn_eq_forIn_toList (m := vars) (m' := Id)
      (init := true)
      (f := fun v ok => (pure (ForInStep.yield (ok && varsWithF.contains v)) : Id (ForInStep Bool))))
    simpa using h_eq
  have h_fold :
      Id.run
          (forIn vars.toList true (fun v ok =>
            pure (ForInStep.yield (ok && varsWithF.contains v)))) =
        vars.toList.foldl (fun b v => b && varsWithF.contains v) true := by
    -- List forIn yields foldl
    simpa using
      (List.idRun_forIn_yield_eq_foldl
        (l := vars.toList)
        (f := fun v b => (pure (b && varsWithF.contains v) : Id Bool))
        (init := true))
  have h_ok_fold :
      vars.toList.foldl (fun b v => b && varsWithF.contains v) true = true := by
    have h_ok'' :
        Id.run
            (forIn vars true (fun v ok =>
              pure (ForInStep.yield (ok && varsWithF.contains v)))) = true := by
      simpa [h_body_ok] using h_ok'
    have h_ok_list :
        Id.run
            (forIn vars.toList true (fun v ok =>
              pure (ForInStep.yield (ok && varsWithF.contains v)))) = true := by
      simpa [h_forIn_list] using h_ok''
    exact h_fold.symm.trans h_ok_list

  have h_all : ∀ v ∈ vars.toList, varsWithF.contains v = true :=
    (List.foldl_and_eq_true (xs := vars.toList)).1 h_ok_fold

  -- hyps equality from trimFrame
  have h_hyps_eq' : (db.trimFrame fmla).2.hyps = fr.hyps := by
    exact congrArg (fun p => p.2.hyps) h_trim
  have h_trim_hyps :
      (db.trimFrame fmla).2.hyps =
        _root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps := by
    rfl
  have h_hyps_eq :
      fr.hyps = _root_.Metamath.Verify.DB.trimFrameHyps db vars db.frame.hyps := by
    exact h_hyps_eq'.symm.trans h_trim_hyps

  -- Variables in the formula are present in frameFloatVars of fr
  have h_var_in :
      ∀ v, Sym.var v ∈ fmla.toList.tail → v ∈ DB.frameFloatVars db fr := by
    intro v h_mem
    have h_cont0 : vars0.contains v = true :=
      foldlVars_contains_of_mem fmla (∅ : HashSet String) v h_mem
    have h_cont_list : vars_list.contains v = true :=
      collectVarsFromHypsList_preserves_contains
        db db.frame.hyps.toList vars0 v h_cont0
    have h_cont : vars.contains v = true := by
      simpa [h_vars_eq] using h_cont_list
    have h_mem_set : v ∈ vars := (Std.HashSet.mem_iff_contains).2 (by simpa using h_cont)
    have h_mem_list : v ∈ vars.toList := (Std.HashSet.mem_toList).2 h_mem_set
    have h_varsWithF_cont : varsWithF.contains v = true :=
      h_all v h_mem_list
    have h_cont_list2 :
        (collectFloatVarsFromHypsList db vars db.frame.hyps.toList).contains v = true := by
      simpa [varsWithF_list, h_varsWithF_eq] using h_varsWithF_cont
    have h_in_frame : v ∈ DB.frameFloatVars db db.frame :=
      collectFloatVarsFromHypsList_contains_implies_frameFloatVars
        db vars v h_wf h_cont_list2
    exact floatVar_in_trimmed db vars fr h_hyps_eq v h_in_frame h_cont

  exact formulaSymsRespectFrame_of_declared
    (db := db) (fr := fr) (f := fmla) h_scoped h_decl h_var_in

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

theorem insertAxiom_full_maintains_scoped
    (db : DB) (pos : Pos) (l : String) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDB db)
    (h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_decl : FormulaSymbolsDeclared db arr)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertAxiom pos l arr).error? = none) :
    WellScopedDB (db.insertAxiom pos l arr) := by
  -- Extract success conditions using helper lemma
  obtain ⟨fr, h_trim, h_no_int, h_insert_ok⟩ := insertAxiom_success_conditions db pos l arr h_success

  -- Freshness in the trimmed frame follows from subsequence mapping
  have h_trim_ok : db.trimFrame arr = (true, fr) := trimFrame'_ok_iff.mp h_trim
  rcases trimFrame_produces_subsequence h_trim_ok with ⟨f, h_eq, _h_inj⟩
  have h_fresh_in_frame : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l := by
    intro i hi
    have h_fresh := h_fresh_label (f i hi).val (f i hi).property
    have h_eqi := h_eq i hi
    simpa [h_eqi.symm] using h_fresh

  -- l is not in db.frame.hyps (needed for scoping preservation on the current frame)
  have h_not_in_frame : l ∉ db.frame.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index db.frame.hyps l h_mem with ⟨i, hi, h_eqi⟩
    have h_eqi' : db.frame.hyps[i]'hi = l := by
      have h_bang :
          db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eqi
    exact (h_fresh_label i hi) h_eqi'

  -- Build the required properties for the newly introduced assertion frame/formula
  have h_scoped_fr : WellScopedFrame db fr :=
    trimFrame'_success_implies_scoped_frame db arr fr h_scoped h_trim
  have h_syms_fr : DB.formulaSymsRespectFrame db arr fr = true :=
    trimFrame'_success_implies_formulaSymsRespectFrame db arr fr h_wf h_scoped h_decl h_trim

  -- Unfold insertAxiom and simplify to a bare insert
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

  -- Reduce the goal to proving scopedness after `insert`
  unfold DB.insertAxiom
  simp [h_head, h_db_err, h_trim, h_no_int]
  -- Goal: WellScopedDB (db.insert pos l (.assert arr fr))
  -- We prove this directly using preservation lemmas.
  have h_frame_scoped :
      WellScopedFrame (db.insert pos l (.assert arr fr)) db.frame := by
    exact wellScopedFrame_preserved_by_insert
      db pos l (.assert arr fr) db.frame h_scoped.1 h_not_in_frame
  have h_frame_scoped' :
      WellScopedFrame (db.insert pos l (.assert arr fr)) (db.insert pos l (.assert arr fr)).frame := by
    simpa [insert_frame_unchanged] using h_frame_scoped
  refine ⟨h_frame_scoped', ?_⟩
  intro lbl obj h_find
  by_cases h_lbl : lbl = l
  · have h_find_l : (db.insert pos l (.assert arr fr)).find? l = some obj := by
      simpa [h_lbl] using h_find
    have h_db_err' : db.error = false := (error_false_iff_error?_none db).2 h_no_err
    have h_insert_err :
        (db.insert pos l (.assert arr fr)).error = false := by
      exact (error_false_iff_error?_none (db.insert pos l (.assert arr fr))).2 h_insert_ok
    have h_find_self :
        (db.insert pos l (.assert arr fr)).find? l = some (.assert arr fr l) := by
      exact Verify.DB.insert_find?_self db pos l (.assert arr fr) h_db_err' h_fresh_db h_insert_err
    have h_obj_eq : obj = Object.assert arr fr l := by
      exact Option.some.inj (h_find_l.symm.trans h_find_self)
    cases h_obj_eq
    have h_scoped_fr' :
        WellScopedFrame (db.insert pos l (.assert arr fr)) fr := by
      exact wellScopedFrame_preserved_by_insert
        db pos l (.assert arr fr) fr h_scoped_fr (by
          intro h_mem
          rcases Array.toList_mem_implies_index fr.hyps l h_mem with ⟨i, hi, h_eqi⟩
          have h_eqi' : fr.hyps[i]'hi = l := by
            have h_bang :
                fr.hyps[i]! = fr.hyps[i]'hi := by
              simpa using (Array.getBang_eq_get_nat (a := fr.hyps) (i := i) (h := hi))
            exact h_bang.symm.trans h_eqi
          exact h_fresh_in_frame i hi h_eqi')
    have h_syms_fr' :
        DB.formulaSymsRespectFrame (db.insert pos l (.assert arr fr)) arr fr = true := by
      exact formulaSymsRespectFrame_preserved_by_insert
        db pos l (.assert arr fr) fr arr (by
          intro h_mem
          rcases Array.toList_mem_implies_index fr.hyps l h_mem with ⟨i, hi, h_eqi⟩
          have h_eqi' : fr.hyps[i]'hi = l := by
            have h_bang :
                fr.hyps[i]! = fr.hyps[i]'hi := by
              simpa using (Array.getBang_eq_get_nat (a := fr.hyps) (i := i) (h := hi))
            exact h_bang.symm.trans h_eqi
          exact h_fresh_in_frame i hi h_eqi') h_syms_fr
    have h_decl_fr' :
        FormulaSymbolsDeclared (db.insert pos l (.assert arr fr)) arr := by
      exact formulaSymbolsDeclared_preserved_by_insert
        db pos l (.assert arr fr) arr h_decl h_fresh_db
    exact ⟨h_scoped_fr', h_syms_fr', h_decl_fr'⟩
  · have h_find_old : db.find? lbl = some obj := by
      have h_eq :=
        insert_preserves_find?_ne db pos l lbl (.assert arr fr) h_lbl
      simpa [h_eq] using h_find
    cases obj with
    | const _ => simp
    | var _ => simp
    | assert f fr' name =>
        have h_old := h_scoped.2 lbl (.assert f fr' name) h_find_old
        have h_not_in_fr' : l ∉ fr'.hyps.toList := by
          intro h_mem
          rcases Array.toList_mem_implies_index fr'.hyps l h_mem with ⟨i, hi, h_eqi⟩
          have h_eqi' : fr'.hyps[i]'hi = l := by
            have h_bang :
                fr'.hyps[i]! = fr'.hyps[i]'hi := by
              simpa using (Array.getBang_eq_get_nat (a := fr'.hyps) (i := i) (h := hi))
            exact h_bang.symm.trans h_eqi
          exact h_fresh_in_asserts lbl f fr' name h_find_old i hi h_eqi'
        have h_scoped_fr' :
            WellScopedFrame (db.insert pos l (.assert arr fr)) fr' := by
          exact wellScopedFrame_preserved_by_insert
            db pos l (.assert arr fr) fr' h_old.1 h_not_in_fr'
        have h_syms_new :
            DB.formulaSymsRespectFrame (db.insert pos l (.assert arr fr)) f fr' = true := by
          exact formulaSymsRespectFrame_preserved_by_insert
            db pos l (.assert arr fr) fr' f h_not_in_fr' h_old.2.1
        have h_decl_new :
            FormulaSymbolsDeclared (db.insert pos l (.assert arr fr)) f := by
          exact formulaSymbolsDeclared_preserved_by_insert
            db pos l (.assert arr fr) f h_old.2.2 h_fresh_db
        exact ⟨h_scoped_fr', h_syms_new, h_decl_new⟩
    | hyp ess f name =>
        have h_old := h_scoped.2 lbl (.hyp ess f name) h_find_old
        constructor
        · intro h_mem
          have h_syms_old := h_old.1 (by
            -- frame.hyps is unchanged by insert
            simpa [insert_frame_unchanged] using h_mem)
          have h_syms_new :=
            formulaSymsRespectFrame_preserved_by_insert
              db pos l (.assert arr fr) db.frame f h_not_in_frame h_syms_old
          simpa [insert_frame_unchanged] using h_syms_new
        · exact formulaSymbolsDeclared_preserved_by_insert
            db pos l (.assert arr fr) f h_old.2 h_fresh_db

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

  have h_reject :
      (s.db.config.rejectToplevelEss && s.db.scopes.size == 0) = false := by
    by_cases h_reject' :
        (s.db.config.rejectToplevelEss && s.db.scopes.size == 0) = true
    · have h_err :
          (s.feedTokens arr ⟨.ess, pos, l⟩).db.error? ≠ none := by
        -- In this branch, feedTokens returns mkError before insertHyp
        simp [ParserState.feedTokens, h_head, h_reject', ParserState.mkError,
          ParserState.withDB, ParserState.withAt, DB.mkError]
      exact False.elim (h_err h_success)
    · simp [h_reject']

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
    simpa [ParserState.feedTokens, h_s_inner, h_reject] using h_success
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
    simp [ParserState.feedTokens, h_s_inner, h_reject]
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

/-- Successful insertion of a non-`var` object implies the label was absent. -/
theorem insert_success_nonvar_fresh
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_err : db.error? = none)
    (h_success : (db.insert pos l obj).error? = none)
    (h_not_var : ∀ v : String, obj l ≠ .var v) :
    db.find? l = none := by
  have h_insert_err_false : (db.insert pos l obj).error = false :=
    (error_false_iff_error?_none (db.insert pos l obj)).2 h_success
  have h_db_err : db.error = false :=
    (error_false_iff_error?_none db).2 h_no_err
  by_cases h_find_none : db.find? l = none
  · exact h_find_none
  · rcases Option.ne_none_iff_exists'.1 h_find_none with ⟨existing, h_find⟩
    have h_not_var_redef : ¬∃ v v', obj l = .var v ∧ existing = .var v' := by
      intro h
      rcases h with ⟨v, _v', h_obj, _h_existing⟩
      exact (h_not_var v h_obj).elim
    have h_dup_err : (db.insert pos l obj).error = true :=
      Metamath.ParserCorrectness.insert_duplicate_error
        db pos l obj existing h_db_err h_find h_not_var_redef
    simp [h_insert_err_false] at h_dup_err

/-- Successful `insertHyp` implies the inserted label was absent in the original DB. -/
theorem insertHyp_success_fresh_db
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_success : (db.insertHyp pos l ess arr).error? = none) :
    db.find? l = none := by
  obtain ⟨db_after_check, h_def_check, h_check_ok, h_insert_ok⟩ :=
    insertHyp_success_conditions db pos l ess arr h_success
  have h_checks_no_err : (DB.insertHypChecks db pos ess arr).error? = none := by
    simpa [h_def_check] using h_check_ok
  have h_check_eq : db_after_check = db := by
    have h_eq := insertHypChecks_eq_db_of_no_error db pos ess arr h_checks_no_err
    simpa [h_def_check] using h_eq
  have h_fresh_after : db_after_check.find? l = none := by
    exact insert_success_nonvar_fresh db_after_check pos l (.hyp ess arr)
      h_check_ok h_insert_ok (by intro v h_eq; cases h_eq)
  simpa [h_check_eq] using h_fresh_after

/-- Successful `insertAxiom` implies the inserted label was absent in the original DB. -/
theorem insertAxiom_success_fresh_db
    (db : DB) (pos : Pos) (l : String) (arr : Formula)
    (h_success : (db.insertAxiom pos l arr).error? = none) :
    db.find? l = none := by
  obtain ⟨fr, _h_trim, _h_no_int, h_insert_ok⟩ := insertAxiom_success_conditions db pos l arr h_success
  have h_no_err : db.error? = none := by
    by_cases h_err : db.error? = none
    · exact h_err
    · have h_db_err : db.error = true := by
        cases h_opt : db.error? with
        | none =>
            exact (h_err h_opt).elim
        | some intr =>
            exact (error_iff_error?_isSome db).2 (by simpa [h_opt])
      have h_bad : (db.insert pos l (.assert arr fr)).error? ≠ none := by
        unfold DB.insert
        simpa [h_db_err] using h_err
      exact (h_bad h_insert_ok).elim
  exact insert_success_nonvar_fresh db pos l (.assert arr fr)
    h_no_err h_insert_ok (by intro v h_eq; cases h_eq)

/-- Success of `feedTokens` implies the accumulated formula has a constant head. -/
theorem feedTokens_success_hasConstHead
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_success : (s.feedTokens arr tokp).db.error? = none) :
    Formula.hasConstHead arr = true := by
  by_cases h_head : Formula.hasConstHead arr = true
  · exact h_head
  · have h_bad : (s.feedTokens arr tokp).db.error? ≠ none := by
      cases tokp with
      | mk k pos l =>
          simp [ParserState.feedTokens, h_head, ParserState.withAt,
            ParserState.mkError, ParserState.withDB, DB.mkError]
    exact (h_bad h_success).elim

/-- Success of `feedTokens` yields the `h_first` precondition used by maintenance lemmas. -/
theorem feedTokens_success_first_not_var
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_success : (s.feedTokens arr tokp).db.error? = none) :
    arr.size > 0 ∧ !arr[0]!.isVar := by
  have h_head : Formula.hasConstHead arr = true :=
    feedTokens_success_hasConstHead s arr tokp h_success
  have h_wf : WellFormedFormula arr :=
    wellFormedFormula_of_hasConstHead h_head
  rcases h_wf with ⟨h_pos, ⟨c, h0⟩⟩
  refine ⟨h_pos, ?_⟩
  simpa [h0, Sym.isVar]

/-- Success of a float statement implies the float-shape check passed. -/
theorem feedTokens_success_float_shape
    (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String)
    (h_success : (s.feedTokens arr ⟨.float, pos, l⟩).db.error? = none) :
    arr.size = 2 ∧ arr[1]!.isVar := by
  have h_first : arr.size > 0 ∧ !arr[0]!.isVar :=
    feedTokens_success_first_not_var s arr ⟨.float, pos, l⟩ h_success
  have h_notvar : arr[0]!.isVar = false := by
    cases h_var : arr[0]!.isVar with
    | false => rfl
    | true =>
        have : False := by simpa [h_var] using h_first.2
        exact False.elim this
  have h_pos : 0 < arr.size := h_first.1
  have h_head : Formula.hasConstHead arr = true := by
    unfold Formula.hasConstHead
    cases h_sym : arr[0]! with
    | const _ => simp [h_pos]
    | var _ =>
        have : False := by simp [Sym.isVar, h_sym] at h_notvar
        exact False.elim this
  by_cases h_shape : Formula.isFloatShape arr = true
  · exact (wellFormedFloat_of_isFloatShape h_shape).1 |> fun hsz =>
      ⟨hsz, by
        rcases (wellFormedFloat_of_isFloatShape h_shape).2 with ⟨_c, v, _h0, h1⟩
        simpa [h1, Sym.isVar]⟩
  · have h_bad : (s.feedTokens arr ⟨.float, pos, l⟩).db.error? ≠ none := by
      simp [ParserState.feedTokens, h_head, h_shape, ParserState.withAt,
        ParserState.mkError, ParserState.withDB, DB.mkError]
    exact (h_bad h_success).elim

theorem feedTokens_maintains_wf
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_wf : WellFormedDB s.db)
    (h_no_err : s.db.error? = none)
    (_h_no_dup : s.db.config.allowDuplicateFloat = false)
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
            h_wf h_no_err _h_no_dup h_first h_second' h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
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
            h_wf h_no_err _h_no_dup h_first h_second' h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
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

theorem feedTokens_maintains_scoped
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDB s.db)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_decl : FormulaSymbolsDeclared s.db arr)
    (h_float : tokp.k = TokensKind.float → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_fresh_db : s.db.find? tokp.label = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < s.db.frame.hyps.size), s.db.frame.hyps[i]'hi ≠ tokp.label)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        s.db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ tokp.label)
    (h_success : (s.feedTokens arr tokp).db.error? = none) :
    WellScopedDB (s.feedTokens arr tokp).db := by
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
        have h_scoped_insert : WellScopedDB (s.db.insertHyp pos label false arr) :=
          insertHyp_full_maintains_scoped s.db pos label false arr
            h_scoped h_no_err h_first h_second' h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_scoped_insert
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
        have h_scoped_insert : WellScopedDB (s.db.insertHyp pos label true arr) :=
          insertHyp_full_maintains_scoped s.db pos label true arr
            h_scoped h_no_err h_first h_second' h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_scoped_insert
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
        have h_scoped_insert : WellScopedDB (s.db.insertAxiom pos label arr) :=
          insertAxiom_full_maintains_scoped s.db pos label arr
            h_wf h_scoped h_no_err h_first h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_scoped_insert
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
              simpa [h_db_eq] using h_scoped

/-
## Phase 1 (continued): Parser -> WellScopedDB

We already have operation-level theorems showing that successful DB updates
preserve `WellScopedDB` (e.g. `insertHyp_full_maintains_scoped`,
`insertAxiom_full_maintains_scoped`) and that `feedTokens` preserves
`WellScopedDB` when its sub-operations succeed.

To connect this to `Verify.checkBytesCore`, we need a parser-state invariant
that also remembers why entering proof mode is safe (theorem frame is well-scoped,
etc.).  This invariant will be threaded through `feedToken`/`feed`/`feedAll`.
-/

/-- Token-parser invariant needed to prove `WellScopedDB` for the final DB.

In `.math` mode, the parser has already checked that every symbol appended to `arr`
was declared as a `$c` or `$v` symbol (see `ParserState.feedToken`).

In `.proof` mode, we remember the theorem's *trimmed* frame and the fact that
the claimed formula respects that frame.
-/
def TokpInv (db : DB) : TokenParser → Prop
  | .comment p =>
      TokpInv db p
  | .djvars arr =>
      ∀ v ∈ arr.toList, db.isVar v = true ∧ db.floatVarOccursInFrame v = true
  | .math arr _ =>
      FormulaSymbolsDeclared db arr
  | .proof pr =>
      WellFormedFormula pr.fmla ∧
      WellFormedFrame db pr.frame ∧
      WellScopedFrame db pr.frame ∧
      DB.formulaSymsRespectFrame db pr.fmla pr.frame = true ∧
      FormulaSymbolsDeclared db pr.fmla
  | _ => True

/-- Componentwise order on scope snapshots `(djSize, hypsSize)`. -/
def ScopeLE (a b : Nat × Nat) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2

theorem ScopeLE.refl (a : Nat × Nat) : ScopeLE a a := by
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem ScopeLE.trans {a b c : Nat × Nat} :
    ScopeLE a b → ScopeLE b c → ScopeLE a c := by
  intro hab hbc
  exact ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩

/-- The scope stack is monotone (older scopes are smaller). -/
def ScopesMonotone (scopes : Array (Nat × Nat)) : Prop :=
  ∀ i j (hi : i < scopes.size) (hj : j < scopes.size),
    i < j → ScopeLE (scopes[i]'hi) (scopes[j]'hj)

/-- Every saved scope snapshot fits within the current frame size. -/
def ScopesWithinFrame (db : DB) : Prop :=
  ∀ i (hi : i < db.scopes.size), ScopeLE (db.scopes[i]'hi) db.frame.size

def ScopesOk (db : DB) : Prop :=
  ScopesMonotone db.scopes ∧ ScopesWithinFrame db

/-- Parser-state invariant: the working DB stays well-formed and well-scoped, and
the current token-parser state satisfies `TokpInv`. -/
def ParserStateInv (s : ParserState) : Prop :=
  WellFormedDB s.db ∧ WellScopedDBWithScopes s.db ∧ ScopesOk s.db ∧ TokpInv s.db s.tokp

theorem FormulaSymbolsDeclared.nil (db : DB) :
    FormulaSymbolsDeclared db (#[] : Formula) := by
  intro s h_mem
  cases h_mem

theorem FormulaSymbolsDeclared.push
    (db : DB) (arr : Formula) (sym : Sym)
    (h_decl : FormulaSymbolsDeclared db arr)
    (h_sym : match sym with
      | .const c => db.isConst c = true
      | .var v => db.isVar v = true) :
    FormulaSymbolsDeclared db (arr.push sym) := by
  intro s h_mem
  -- `Array.toList_push` turns membership into a disjunction: old element or new tail element.
  have h_mem' : s ∈ arr.toList ∨ s = sym := by
    simpa [Array.toList_push] using h_mem
  cases h_mem' with
  | inl h_old =>
      exact h_decl s h_old
  | inr h_eq =>
      simpa [h_eq] using h_sym

/-- Fresh label is not present in any hypothesis array of a well-formed frame. -/
theorem fresh_not_in_frame_of_wfFrame
    (db : DB) (fr : Frame) (l : String)
    (h_wf : WellFormedFrame db fr)
    (h_fresh : db.find? l = none) :
    ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l := by
  intro i hi h_eq
  rcases h_wf.1 i hi with ⟨ess, f, lbl, h_find, _h_float, _h_formula⟩
  have h_find' : db.find? l = some (.hyp ess f lbl) := by
    simpa [h_eq] using h_find
  simpa [h_fresh] using h_find'

/-- If `l` is absent from `db`, then `l` cannot occur in any well-formed assertion frame. -/
theorem fresh_not_in_assert_frames_of_wf
    (db : DB) (h_wf : WellFormedDB db) (l : String) (h_fresh : db.find? l = none) :
    ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
      db.find? lbl = some (.assert fmla fr_assert name) →
      ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l := by
  intro lbl fmla fr_assert name h_find i hi
  have h_obj := h_wf.2 lbl (.assert fmla fr_assert name) h_find
  exact fresh_not_in_frame_of_wfFrame db fr_assert l h_obj.2 h_fresh i hi

@[simp] theorem default_frame_hyps : (default : Frame).hyps = (#[] : Array String) := rfl
@[simp] theorem default_frame_dj : (default : Frame).dj = (#[] : Array DJ) := rfl
@[simp] theorem default_db_objects : (default : DB).objects = ({} : Std.HashMap String Object) := rfl
@[simp] theorem default_db_scopes : (default : DB).scopes = (#[] : Array (Nat × Nat)) := rfl
@[simp] theorem default_db_frame_hyps : (default : DB).frame.hyps = (#[] : Array String) := rfl
@[simp] theorem default_db_frame_dj : (default : DB).frame.dj = (#[] : Array DJ) := rfl
@[simp] theorem default_parserState_tokp : (default : ParserState).tokp = TokenParser.start := rfl

theorem initDB_wellFormed (config : ModeConfig) :
    WellFormedDB ({ (default : DB) with config := config } : DB) := by
  classical
  -- Everything is empty in the default DB, so all obligations are vacuous.
  let db : DB := { (default : DB) with config := config }
  change WellFormedDB db
  unfold WellFormedDB WellFormedFrame HypOK UniqueFloatVars
  constructor
  · constructor
    · intro i hi
      -- No hypotheses in the initial frame.
      have : False := by simpa [db] using hi
      exact this.elim
    · intro i j hi hj hij fi fj lbli lblj hfi hfj hsi hsj
      have : False := by simpa [db] using hi
      exact this.elim
  · intro lbl obj h_find
    -- No objects in the initial DB.
    have : False := by simpa [DB.find?, db] using h_find
    exact this.elim

theorem initDB_wellScoped (config : ModeConfig) :
    WellScopedDBWithScopes ({ (default : DB) with config := config } : DB) := by
  classical
  let db : DB := { (default : DB) with config := config }
  change WellScopedDBWithScopes db
  unfold WellScopedDBWithScopes WellScopedDB WellScopedFrame
  constructor
  · constructor
    · constructor
      · intro i hi
        -- No hypotheses in the initial frame.
        have : False := by simpa [db] using hi
        exact this.elim
      · intro v w h_mem
        -- No DV constraints in the initial frame.
        have : False := by simpa [db] using h_mem
        exact this.elim
    · intro lbl obj h_find
      -- No objects in the initial DB.
      have : False := by simpa [DB.find?, db] using h_find
      exact this.elim
  · intro sc h_mem
    -- No saved scopes in the initial DB.
    have : False := by
      simpa [db] using h_mem
    cases this

theorem initDB_scopesOk (config : ModeConfig) :
    ScopesOk ({ (default : DB) with config := config } : DB) := by
  classical
  let db : DB := { (default : DB) with config := config }
  refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    have : False := by
      -- No saved scopes in the initial DB.
      simpa [db] using hi
    exact this.elim
  · intro i hi
    have : False := by
      -- No saved scopes in the initial DB.
      simpa [db] using hi
    exact this.elim

theorem initState_inv (config : ModeConfig) :
    ParserStateInv ({ (default : ParserState) with db := { (default : DB) with config := config } } : ParserState) := by
  classical
  refine ⟨initDB_wellFormed config, initDB_wellScoped config, initDB_scopesOk config, ?_⟩
  -- default token parser is `.start`
  simpa [TokpInv]

/-- Mined from the former `ParserOpsInvariants`: extending hypothesis slots keeps `ScopesOk`. -/
theorem scopesOk_withHyps_push
    (db : DB) (l : String) :
    ScopesOk db → ScopesOk (db.withHyps (·.push l)) := by
  intro h
  rcases h with ⟨h_mono, h_within⟩
  refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    have hi_old : i < db.scopes.size := by
      simpa [DB.withHyps, DB.withFrame] using hi
    have hj_old : j < db.scopes.size := by
      simpa [DB.withHyps, DB.withFrame] using hj
    simpa [ScopesMonotone, DB.withHyps, DB.withFrame] using h_mono i j hi_old hj_old hij
  · intro i hi
    have hi_old : i < db.scopes.size := by
      simpa [DB.withHyps, DB.withFrame] using hi
    have h_le : ScopeLE (db.scopes[i]'hi_old) db.frame.size := h_within i hi_old
    rcases h_le with ⟨hx, hy⟩
    cases h_fr : db.frame with
    | mk dj hyps =>
        have hx' : (db.scopes[i]'hi_old).fst ≤ dj.size := by
          simpa [h_fr, Frame.size] using hx
        have hy' : (db.scopes[i]'hi_old).snd ≤ hyps.size := by
          simpa [h_fr, Frame.size] using hy
        have hy'' : (db.scopes[i]'hi_old).snd ≤ (hyps.push l).size := by
          exact Nat.le_trans hy' (by simp [Array.size_push])
        exact ⟨by simpa [h_fr, DB.withHyps, DB.withFrame, Frame.size] using hx',
          by simpa [h_fr, DB.withHyps, DB.withFrame, Frame.size] using hy''⟩

/-- Mined from the former `ParserOpsInvariants`: extending DV slots keeps `ScopesOk`. -/
theorem scopesOk_withDJ_push
    (db : DB) (p : DJ) :
    ScopesOk db → ScopesOk (db.withDJ (·.push p)) := by
  intro h
  rcases h with ⟨h_mono, h_within⟩
  refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    have hi_old : i < db.scopes.size := by
      simpa [DB.withDJ, DB.withFrame] using hi
    have hj_old : j < db.scopes.size := by
      simpa [DB.withDJ, DB.withFrame] using hj
    simpa [ScopesMonotone, DB.withDJ, DB.withFrame] using h_mono i j hi_old hj_old hij
  · intro i hi
    have hi_old : i < db.scopes.size := by
      simpa [DB.withDJ, DB.withFrame] using hi
    have h_le : ScopeLE (db.scopes[i]'hi_old) db.frame.size := h_within i hi_old
    rcases h_le with ⟨hx, hy⟩
    cases h_fr : db.frame with
    | mk dj hyps =>
        have hx' : (db.scopes[i]'hi_old).fst ≤ dj.size := by
          simpa [h_fr, Frame.size] using hx
        have hy' : (db.scopes[i]'hi_old).snd ≤ hyps.size := by
          simpa [h_fr, Frame.size] using hy
        have hx'' : (db.scopes[i]'hi_old).fst ≤ (dj.push p).size := by
          exact Nat.le_trans hx' (by simp [Array.size_push])
        exact ⟨by simpa [h_fr, DB.withDJ, DB.withFrame, Frame.size] using hx'',
          by simpa [h_fr, DB.withDJ, DB.withFrame, Frame.size] using hy'⟩

theorem wellFormedDB_preserved_by_withDJ
    (db : DB) (f : Array DJ → Array DJ) :
    WellFormedDB db → WellFormedDB (db.withDJ f) := by
  intro h
  -- `withDJ` only changes the current frame's DJ array, which does not affect well-formedness.
  simpa [WellFormedDB, WellFormedFrame, HypOK, UniqueFloatVars,
    DB.withDJ, DB.withFrame, DB.find?] using h

theorem wellScopedFrame_push_dj
    (db : DB) (fr : Frame) (p : DJ)
    (h_scoped : WellScopedFrame db fr)
    (h_p : p.1 < p.2 ∧ p.1 ∈ DB.frameFloatVars db fr ∧ p.2 ∈ DB.frameFloatVars db fr) :
    WellScopedFrame db { fr with dj := fr.dj.push p } := by
  rcases h_scoped with ⟨h_hyps, h_dj⟩
  refine ⟨?_, ?_⟩
  · -- Hypothesis scoping ignores `dj`.
    simpa using h_hyps
  · intro v w h_mem
    have h_mem' : (v, w) ∈ fr.dj.toList ∨ (v, w) = p := by
      simpa [Array.toList_push] using h_mem
    cases h_mem' with
    | inl h_old => exact h_dj v w h_old
    | inr h_eq =>
        cases h_eq
        exact h_p


/-!
## Phase 1 (new): Parser -> WellScopedDB (via WellScopedDBWithScopes)

`popScope` shrinks the current frame back to a previously saved prefix, so the
natural invariant to maintain through parsing is `WellScopedDBWithScopes`.

This section proves the preservation lemmas we need to connect `Verify.checkBytesCore`
to `WellScopedDB`.
-/

/-- `pushScope` preserves `WellFormedDB` (it only extends the scope stack). -/
theorem wellFormedDB_pushScope (db : DB) :
    WellFormedDB db → WellFormedDB db.pushScope := by
  intro h
  simpa [DB.pushScope] using h

/-- `pushScope` preserves `WellScopedDBWithScopes`. -/
theorem wellScopedDBWithScopes_pushScope (db : DB) :
    WellScopedDBWithScopes db → WellScopedDBWithScopes db.pushScope := by
  intro h
  rcases h with ⟨h_scoped, h_scopes⟩
  refine ⟨?_, ?_⟩
  · -- DB itself is unchanged, only scopes grow
    simpa [DB.pushScope] using h_scoped
  · intro sc h_mem
    -- Either sc is from the old scopes, or it's the new scope snapshot at the end.
    have h_mem' : sc ∈ db.scopes.toList ∨ sc = db.frame.size := by
      -- `Array.toList_push` gives membership in the old list or equality with the pushed element.
      simpa [DB.pushScope, Array.toList_push] using h_mem
    cases h_mem' with
    | inl h_old =>
        -- Old scopes: reuse the invariant (scopes don't affect objects)
        have h0 := h_scopes sc h_old
        simpa [DB.pushScope] using h0
    | inr h_eq =>
        subst h_eq
        -- New scope snapshot is the current frame size, so shrink is identity.
        have h0 : WellScopedFrame db db.frame := h_scoped.1
        -- Shrinking to the current size yields the same frame.
        -- We keep this as a simp-proof to avoid relying on internal Array.shrink details.
        simpa [DB.pushScope, Frame.size, Frame.shrink, Array.shrink] using h0

/-- `pushScope` preserves the scope-stack shape invariant. -/
theorem scopesOk_pushScope (db : DB) :
    ScopesOk db → ScopesOk db.pushScope := by
  classical
  intro h
  rcases h with ⟨h_mono, h_within⟩
  refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    -- New scopes are `db.scopes.push db.frame.size`.
    by_cases hj_last : j = db.scopes.size
    · subst hj_last
      have hi_old : i < db.scopes.size := by
        -- i < j and j = size
        simpa using hij
      have h_i : (db.scopes.push db.frame.size)[i] = db.scopes[i]'hi_old := by
        simpa using (Array.getElem_push_lt (xs := db.scopes) (x := db.frame.size) (i := i) hi_old)
      have h_j : (db.scopes.push db.frame.size)[db.scopes.size] = db.frame.size := by
        simpa using (Array.getElem_push_eq (xs := db.scopes) (x := db.frame.size))
      have h_le : ScopeLE (db.scopes[i]'hi_old) db.frame.size := h_within i hi_old
      simpa [DB.pushScope, h_i, h_j] using h_le
    · have hj_le : j ≤ db.scopes.size := by
        -- j < size+1
        have : j < (db.scopes.push db.frame.size).size := by
          simpa [DB.pushScope] using hj
        simpa using (Nat.le_of_lt_succ (by simpa using this))
      have hj_old : j < db.scopes.size := Nat.lt_of_le_of_ne hj_le hj_last
      have hi_old : i < db.scopes.size := Nat.lt_trans hij hj_old
      have h_mono_ij : ScopeLE (db.scopes[i]'hi_old) (db.scopes[j]'hj_old) :=
        h_mono i j hi_old hj_old hij
      have h_i : (db.scopes.push db.frame.size)[i] = db.scopes[i]'hi_old := by
        simpa using (Array.getElem_push_lt (xs := db.scopes) (x := db.frame.size) (i := i) hi_old)
      have h_j : (db.scopes.push db.frame.size)[j] = db.scopes[j]'hj_old := by
        simpa using (Array.getElem_push_lt (xs := db.scopes) (x := db.frame.size) (i := j) hj_old)
      simpa [DB.pushScope, h_i, h_j] using h_mono_ij
  · intro i hi
    by_cases hi_last : i = db.scopes.size
    · subst hi_last
      -- New last element equals the current frame size.
      have h_i : (db.scopes.push db.frame.size)[db.scopes.size] = db.frame.size := by
        simpa using (Array.getElem_push_eq (xs := db.scopes) (x := db.frame.size))
      simpa [DB.pushScope, h_i] using ScopeLE.refl db.frame.size
    · have hi_le : i ≤ db.scopes.size := by
        have : i < (db.scopes.push db.frame.size).size := by
          simpa [DB.pushScope] using hi
        simpa using (Nat.le_of_lt_succ (by simpa using this))
      have hi_old : i < db.scopes.size := Nat.lt_of_le_of_ne hi_le hi_last
      have h_le : ScopeLE (db.scopes[i]'hi_old) db.frame.size := h_within i hi_old
      have h_i : (db.scopes.push db.frame.size)[i] = db.scopes[i]'hi_old := by
        simpa using (Array.getElem_push_lt (xs := db.scopes) (x := db.frame.size) (i := i) hi_old)
      simpa [DB.pushScope, h_i] using h_le

/-- `popScope` preserves `WellFormedDB` when it succeeds. -/
theorem wellFormedDB_popScope
    (db : DB) (pos : Pos)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    (h_ok : (db.popScope pos).error? = none) :
    WellFormedDB (db.popScope pos) := by
  exact structure_preserving_maintains_wf db (StructurePreservingOp.popScope pos)
    h_wf h_no_err h_ok

/-- `popScope` preserves the scope-stack shape invariant when it succeeds. -/
theorem scopesOk_popScope
    (db : DB) (pos : Pos)
    (h_ok : ScopesOk db)
    (h_success : (db.popScope pos).error? = none) :
    ScopesOk (db.popScope pos) := by
  classical
  rcases h_ok with ⟨h_mono, h_within⟩
  unfold DB.popScope at h_success ⊢
  cases h_back : db.scopes.back? with
  | none =>
      simp [h_back, DB.mkError] at h_success
  | some sc =>
      -- After popping, scopes shrink by one and frame shrinks to `sc`.
      -- Monotonicity is preserved by restricting to the prefix.
      have h_size_pos : 0 < db.scopes.size := by
        -- back? = some implies nonempty
        cases hsz : db.scopes.size with
        | zero =>
            have : db.scopes.back? = none := by
              simp [Array.back?, hsz]
            cases (this.symm.trans h_back)
        | succ n =>
            exact Nat.succ_pos n
      let last : Nat := db.scopes.size - 1
      have h_last_lt : last < db.scopes.size := Nat.sub_one_lt_of_lt h_size_pos
      have h_last_get? : db.scopes[last]? = some sc := by
        -- back? is getElem? at last
        simpa [Array.back?, last] using h_back
      have h_last_bang : db.scopes[last]! = sc :=
        Array.getElem!_of_getElem?_eq_some db.scopes last sc h_last_get?
      -- New DB is `{ db with frame := db.frame.shrink sc, scopes := db.scopes.pop }`.
      have h_frame_size : (db.frame.shrink sc).size = sc := by
        -- sc is within the current frame size by ScopesWithinFrame at `last`.
        have h_sc_within : ScopeLE (db.scopes[last]'h_last_lt) db.frame.size := h_within last h_last_lt
        have h_sc_within' : ScopeLE sc db.frame.size := by
          -- rewrite scopes[last] = sc
          have h_eq_bang : db.scopes[last]! = db.scopes[last]'h_last_lt := by
            simpa using (Array.getBang_eq_get_nat (a := db.scopes) (i := last) (h := h_last_lt))
          have h_sc_within_bang : ScopeLE (db.scopes[last]!) db.frame.size := by
            simpa [h_eq_bang] using h_sc_within
          simpa [h_last_bang] using h_sc_within_bang
        rcases h_sc_within' with ⟨h_dj, h_hyps⟩
        cases h_fr : db.frame with
        | mk dj hyps =>
            cases h_sc : sc with
            | mk x y =>
                have h_dj' : x ≤ dj.size := by
                  simpa [h_fr, h_sc, Frame.size] using h_dj
                have h_hyps' : y ≤ hyps.size := by
                  simpa [h_fr, h_sc, Frame.size] using h_hyps
                simp [h_fr, h_sc, Frame.size, Frame.shrink, Array.size_shrink,
                  Nat.min_eq_left h_dj', Nat.min_eq_left h_hyps']
      refine ⟨?_, ?_⟩
      · -- ScopesMonotone for the popped scopes
        intro i j hi hj hij
        have hi_old : i < db.scopes.size := by
          -- i < pop.size = size-1
          have hi_pop : i < db.scopes.size - 1 := by
            simpa [Array.size_pop] using hi
          exact Nat.lt_of_lt_of_le hi_pop (Nat.sub_le _ _)
        have hj_old : j < db.scopes.size := by
          have hj_pop : j < db.scopes.size - 1 := by
            simpa [Array.size_pop] using hj
          exact Nat.lt_of_lt_of_le hj_pop (Nat.sub_le _ _)
        have h_mono_ij : ScopeLE (db.scopes[i]'hi_old) (db.scopes[j]'hj_old) :=
          h_mono i j hi_old hj_old hij
        have h_i : (db.scopes.pop)[i]'hi = db.scopes[i]'hi_old := by
          -- getElem_pop rewrites to the original array
          have := (Array.getElem_pop (xs := db.scopes) (i := i) hi)
          simpa using this
        have h_j : (db.scopes.pop)[j]'hj = db.scopes[j]'hj_old := by
          have := (Array.getElem_pop (xs := db.scopes) (i := j) hj)
          simpa using this
        simpa [h_i, h_j] using h_mono_ij
      · -- ScopesWithinFrame for the popped scopes: each older scope <= `sc`
        intro i hi
        have hi_old : i < db.scopes.size := by
          have hi_pop : i < db.scopes.size - 1 := by
            simpa [Array.size_pop] using hi
          exact Nat.lt_of_lt_of_le hi_pop (Nat.sub_le _ _)
        have hi_last : i < last := by
          -- i < size-1 = last
          have hi_pop : i < db.scopes.size - 1 := by
            simpa [Array.size_pop, last] using hi
          simpa [last] using hi_pop
        have h_le_last : ScopeLE (db.scopes[i]'hi_old) (db.scopes[last]'h_last_lt) :=
          h_mono i last hi_old h_last_lt hi_last
        -- rewrite `scopes[last] = sc`
        have h_eq_bang : db.scopes[last]! = db.scopes[last]'h_last_lt := by
          simpa using (Array.getBang_eq_get_nat (a := db.scopes) (i := last) (h := h_last_lt))
        have h_sc_eq : db.scopes[last]'h_last_lt = sc := by
          simpa [h_eq_bang] using h_last_bang
        have h_i : (db.scopes.pop)[i]'hi = db.scopes[i]'hi_old := by
          have := (Array.getElem_pop (xs := db.scopes) (i := i) hi)
          simpa using this
        -- new frame size is sc
        have h_frame : ScopeLE ((db.scopes.pop)[i]'hi) (db.frame.shrink sc).size := by
          -- combine the inequality with the frame-size computation
          simpa [h_i, h_sc_eq, h_frame_size] using h_le_last
        simpa using h_frame

namespace Array

/-- Shrinking twice with a smaller second bound is the same as shrinking once. -/
theorem shrink_shrink_of_le {α : Type _} (xs : Array α) (a b : Nat) (h : b ≤ a) :
    (xs.shrink a).shrink b = xs.shrink b := by
  apply Array.ext'
  -- toList characterization of shrink
  simp [Array.toList_shrink, List.take_take, Nat.min_eq_left h]

/-- Shrinking a pushed array to a size within the original array ignores the pushed element. -/
theorem shrink_push_of_le {α : Type _} (xs : Array α) (x : α) (n : Nat) (h : n ≤ xs.size) :
    (xs.push x).shrink n = xs.shrink n := by
  apply Array.ext'
  -- Use toList characterization of shrink and `take` over append.
  have h_len : n ≤ xs.toList.length := by
    -- Array.toList.length is definitional equal to Array.size
    cases xs <;> simpa using h
  simp [Array.toList_shrink, Array.toList_push, List.take_append_of_le_length h_len]

/-- Extracting a prefix from a pushed array (within the original size) ignores the pushed element. -/
theorem extract_push_of_le {α : Type _} (xs : Array α) (x : α) (n : Nat) (h : n ≤ xs.size) :
    (xs.push x).extract 0 n = xs.extract 0 n := by
  apply Array.ext'
  have h_len : n ≤ xs.toList.length := by
    cases xs <;> simpa using h
  simp [Array.toList_extract_take, Array.toList_push, List.take_append_of_le_length h_len]

end Array

theorem wellScopedDBWithScopes_withDJ_push
    (db : DB) (p : DJ)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDBWithScopes db)
    (h_ok : ScopesOk db)
    (h_p : p.1 < p.2 ∧ p.1 ∈ DB.frameFloatVars db db.frame ∧ p.2 ∈ DB.frameFloatVars db db.frame) :
    WellScopedDBWithScopes (db.withDJ (·.push p)) := by
  classical
  rcases h_scoped with ⟨h_scoped_db, h_scopes⟩
  let db' : DB := db.withDJ (·.push p)
  have h_find_eq : ∀ lbl, db'.find? lbl = db.find? lbl := by
    intro lbl
    simp [db', DB.withDJ, DB.withFrame, DB.find?]
  have h_scoped_frame_old : WellScopedFrame db db.frame := h_scoped_db.1
  have h_scoped_frame_db' : WellScopedFrame db' db.frame := by
    simpa [db'] using (wellScopedFrame_preserved_by_withDJ db (f := (·.push p)) (fr := db.frame) h_scoped_frame_old)
  have h_p' : p.1 < p.2 ∧
      p.1 ∈ DB.frameFloatVars db' db.frame ∧
      p.2 ∈ DB.frameFloatVars db' db.frame := by
    simpa [db', DB.withDJ, DB.withFrame, DB.frameFloatVars, DB.find?] using h_p
  have h_scoped_frame' : WellScopedFrame db' db'.frame := by
    simpa [db'] using (wellScopedFrame_push_dj db' db.frame p h_scoped_frame_db' h_p')

  have h_scoped_db' : WellScopedDB db' := by
    refine ⟨h_scoped_frame', ?_⟩
    intro lbl obj h_find
    have h_find_old : db.find? lbl = some obj := by
      simpa [h_find_eq] using h_find
    have h_obj := h_scoped_db.2 lbl obj h_find_old
    cases obj with
    | const _ =>
        simpa using h_obj
    | var _ =>
        simpa using h_obj
    | assert f fr name =>
        rcases h_obj with ⟨h_fr_scoped, h_syms, h_decl⟩
        refine ⟨?_, ?_, ?_⟩
        · simpa [db'] using (wellScopedFrame_preserved_by_withDJ db (f := (·.push p)) (fr := fr) h_fr_scoped)
        · simpa [db', DB.formulaSymsRespectFrame, DB.frameFloatVars, DB.find?] using h_syms
        · simpa [db', FormulaSymbolsDeclared, DB.isConst, DB.isVar, DB.find?] using h_decl
    | hyp ess f name =>
        constructor
        · intro h_in
          have h_in' : lbl ∈ db.frame.hyps.toList := by
            simpa [db', DB.withDJ, DB.withFrame] using h_in
          have h_syms := h_obj.1 h_in'
          simpa [db', DB.formulaSymsRespectFrame, DB.frameFloatVars, DB.find?] using h_syms
        · simpa [db', FormulaSymbolsDeclared, DB.isConst, DB.isVar, DB.find?] using h_obj.2

  refine ⟨h_scoped_db', ?_⟩
  intro sc h_mem
  have h_mem' : sc ∈ db.scopes.toList := by
    simpa [db', DB.withDJ, DB.withFrame] using h_mem
  have h_scoped_sc : WellScopedFrame db (db.frame.shrink sc) := h_scopes sc h_mem'
  have h_scoped_sc' : WellScopedFrame db' (db.frame.shrink sc) := by
    simpa [db'] using (wellScopedFrame_preserved_by_withDJ db (f := (·.push p)) (fr := db.frame.shrink sc) h_scoped_sc)
  rcases h_ok with ⟨_, h_within⟩
  rcases Array.toList_mem_implies_index db.scopes sc h_mem' with ⟨i, hi, h_eq⟩
  have h_eq' : db.scopes[i]'hi = sc := by
    have h_bang : db.scopes[i]! = db.scopes[i]'hi := by
      simpa using (Array.getBang_eq_get_nat (a := db.scopes) (i := i) (h := hi))
    exact h_bang.symm.trans h_eq
  have h_sc_le : ScopeLE sc db.frame.size := by
    simpa [h_eq'] using h_within i hi
  rcases h_sc_le with ⟨hx, hy⟩
  cases h_fr : db.frame with
  | mk dj hyps =>
      rcases sc with ⟨x, y⟩
      have hx' : x ≤ dj.size := by
        simpa [h_fr, Frame.size] using hx
      have hy' : y ≤ hyps.size := by
        simpa [h_fr, Frame.size] using hy
      have h_shrink :
          (db'.frame.shrink (x, y)) = (db.frame.shrink (x, y)) := by
        have h_dj : (dj.push p).extract 0 x = dj.extract 0 x :=
          Array.extract_push_of_le dj p x hx'
        simp [db', DB.withDJ, DB.withFrame, Frame.shrink, Array.shrink_eq_take,
          Array.take_eq_extract, h_fr, h_dj, Nat.min_eq_left hx', Nat.min_eq_left hy']
      simpa [h_shrink, db', h_fr] using h_scoped_sc'

/-- Frame shrink is idempotent when shrinking to a smaller snapshot. -/
theorem Frame.shrink_shrink_of_le (fr : Frame) (a b : Nat × Nat) (h : ScopeLE b a) :
    (fr.shrink a).shrink b = fr.shrink b := by
  rcases fr with ⟨dj, hyps⟩
  rcases a with ⟨x, y⟩
  rcases b with ⟨x', y'⟩
  rcases h with ⟨hx, hy⟩
  simp [Frame.shrink, Nat.min_eq_left hx, Nat.min_eq_left hy]

namespace List

/-- Membership in `dropLast` implies membership in the original list. -/
theorem mem_of_mem_dropLast {α : Type _} {x : α} {xs : List α} :
    x ∈ xs.dropLast → x ∈ xs := by
  induction xs with
  | nil =>
      intro h
      simpa using h
  | cons a xs ih =>
      cases xs with
      | nil =>
          intro h
          simpa using h
      | cons b tl =>
          intro h
          -- dropLast (a::b::tl) = a :: dropLast (b::tl)
          simp [List.dropLast] at h
          cases h with
          | inl hxa =>
              simp [hxa]
          | inr htail =>
              -- Apply IH on (b::tl)
              have : x ∈ (b :: tl) := ih htail
              simp [this]

end List

@[simp] theorem withHyps_scopes (db : DB) (f : Array String → Array String) :
    (db.withHyps f).scopes = db.scopes := by
  unfold DB.withHyps DB.withFrame
  rfl

@[simp] theorem withDJ_scopes (db : DB) (f : Array DJ → Array DJ) :
    (db.withDJ f).scopes = db.scopes := by
  unfold DB.withDJ DB.withFrame
  rfl

@[simp] theorem insert_scopes (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).scopes = db.scopes := by
  -- `insert` never modifies the scope stack; it only touches `objects` and `error?`.
  unfold DB.insert
  -- Handle the const-in-inner-scope check first.
  cases h_obj : obj l <;> simp [h_obj, DB.mkError]
  -- Remaining branches either return `db`, `mkError`, or `{db with objects := ...}`.
  -- All preserve `scopes`.
  repeat (first | split | simp [DB.mkError] | rfl)

theorem scopesOk_insert
    (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    ScopesOk db → ScopesOk (db.insert pos l obj) := by
  intro h
  rcases h with ⟨h_mono, h_within⟩
  refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    have hi_old : i < db.scopes.size := by
      simpa [insert_scopes] using hi
    have hj_old : j < db.scopes.size := by
      simpa [insert_scopes] using hj
    simpa [insert_scopes] using h_mono i j hi_old hj_old hij
  · intro i hi
    have hi_old : i < db.scopes.size := by
      simpa [insert_scopes] using hi
    simpa [insert_scopes, insert_frame_unchanged] using h_within i hi_old

/-- Strengthening of `insertHyp_full_maintains_scoped`: also preserves the stored-scope snapshots. -/
theorem insertHyp_full_maintains_scopedWithScopes
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDBWithScopes db)
    (h_ok : ScopesOk db)
    (h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : ess = false → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_decl : FormulaSymbolsDeclared db arr)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertHyp pos l ess arr).error? = none) :
    WellScopedDBWithScopes (db.insertHyp pos l ess arr) := by
  classical
  rcases h_scoped with ⟨h_scoped_db, h_scopes_db⟩
  rcases h_ok with ⟨_, h_within⟩

  have h_scoped_new : WellScopedDB (db.insertHyp pos l ess arr) :=
    insertHyp_full_maintains_scoped db pos l ess arr
      h_scoped_db h_no_err h_first h_second h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_success

  -- Reduce `insertHyp` to `insert` + `withHyps` on the success path (as in `insertHyp_full_maintains_scoped`).
  obtain ⟨db_after_check, h_def_check, h_check_ok, h_insert_ok⟩ :=
    insertHyp_success_conditions db pos l ess arr h_success
  have h_checks_no_err : (DB.insertHypChecks db pos ess arr).error? = none := by
    simpa [h_def_check] using h_check_ok
  have h_check_eq : db_after_check = db := by
    have h_eq := insertHypChecks_eq_db_of_no_error db pos ess arr h_checks_no_err
    simpa [h_def_check] using h_eq
  have h_check_err : db_after_check.error = false :=
    (error_false_iff_error?_none db_after_check).2 h_check_ok
  have h_insert_err_after_check : (db_after_check.insert pos l (.hyp ess arr)).error = false :=
    (error_false_iff_error?_none (db_after_check.insert pos l (.hyp ess arr))).2 h_insert_ok
  have h_insertHyp_eq_after_check :
      db.insertHyp pos l ess arr =
        (db_after_check.insert pos l (.hyp ess arr)).withHyps (·.push l) := by
    have h_def_check' := h_def_check.symm
    simp [DB.insertHyp, h_def_check', h_check_err, h_insert_err_after_check]
  have h_insertHyp_eq :
      db.insertHyp pos l ess arr =
        (db.insert pos l (.hyp ess arr)).withHyps (·.push l) := by
    simpa [h_check_eq] using h_insertHyp_eq_after_check

  refine ⟨h_scoped_new, ?_⟩
  intro sc h_mem_sc
  -- `insert`/`withHyps` do not change scopes.
  have h_mem_sc' : sc ∈ db.scopes.toList := by
    simpa [h_insertHyp_eq] using h_mem_sc

  have h_scoped_old : WellScopedFrame db (db.frame.shrink sc) :=
    h_scopes_db sc h_mem_sc'

  -- `l` is not in the current frame hyps, hence not in any saved prefix.
  have h_not_in_frame : l ∉ db.frame.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index db.frame.hyps l h_mem with ⟨i, hi, h_eq_lbl⟩
    have h_eq' : db.frame.hyps[i]'hi = l := by
      have h_bang : db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq_lbl
    exact (h_fresh_label i hi) h_eq'
  have h_not_in_shrink : l ∉ (db.frame.shrink sc).hyps.toList := by
    intro h_mem
    -- shrink is a prefix of the original hyps list
    have : l ∈ db.frame.hyps.toList := by
      have : l ∈ (db.frame.hyps.toList.take sc.2) := by
        simpa [Frame.shrink] using h_mem
      exact List.mem_of_mem_take this
    exact (h_not_in_frame this).elim

  -- Show the old snapshot stays well-scoped after inserting a fresh label, then after `withHyps`.
  have h_scoped_after_insert :
      WellScopedFrame (db.insert pos l (.hyp ess arr)) (db.frame.shrink sc) := by
    exact wellScopedFrame_preserved_by_insert db pos l (.hyp ess arr) (db.frame.shrink sc)
      h_scoped_old h_not_in_shrink
  have h_scoped_after_withHyps :
      WellScopedFrame ((db.insert pos l (.hyp ess arr)).withHyps (·.push l)) (db.frame.shrink sc) := by
    exact wellScopedFrame_preserved_by_withHyps (db := db.insert pos l (.hyp ess arr)) (f := (·.push l))
      (fr := db.frame.shrink sc) h_scoped_after_insert

  -- Finally, rewrite the shrunk frame: pushing to hyps doesn't affect earlier snapshots.
  have h_sc_le : ScopeLE sc db.frame.size := by
    rcases Array.toList_mem_implies_index db.scopes sc h_mem_sc' with ⟨i, hi, h_eq⟩
    have h_eqi : db.scopes[i]'hi = sc := by
      have h_bang : db.scopes[i]! = db.scopes[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.scopes) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq
    simpa [h_eqi] using h_within i hi
  have h_shrink_frame :
      ((db.insert pos l (.hyp ess arr)).withHyps (·.push l)).frame.shrink sc = db.frame.shrink sc := by
    rcases sc with ⟨x, y⟩
    rcases h_sc_le with ⟨_, hy⟩
    -- Rewrite `db.frame` to expose the underlying hyps array for the shrink/push algebra.
    cases h_fr : db.frame with
    | mk dj hyps =>
        have hy' : y ≤ hyps.size := by
          -- `hy : y ≤ (db.frame.size).2`; rewrite via `h_fr` to get a bound on `hyps.size`.
          simpa [Frame.size, h_fr] using hy
        -- After inserting, the frame is unchanged; `withHyps` pushes `l` to the end.
        -- Shrinking back to `y ≤ hyps.size` removes that pushed element.
        simp [DB.withHyps, DB.withFrame, Frame.shrink, h_fr, insert_frame_unchanged,
          Array.extract_push_of_le hyps l y hy']

  simpa [h_insertHyp_eq, h_shrink_frame] using h_scoped_after_withHyps

/-- Strengthening of `insertAxiom_full_maintains_scoped`: also preserves stored-scope snapshots. -/
theorem insertAxiom_full_maintains_scopedWithScopes
    (db : DB) (pos : Pos) (l : String) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDBWithScopes db)
    (h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_decl : FormulaSymbolsDeclared db arr)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertAxiom pos l arr).error? = none) :
    WellScopedDBWithScopes (db.insertAxiom pos l arr) := by
  rcases h_scoped with ⟨h_scoped_db, h_scopes_db⟩
  have h_scoped_new : WellScopedDB (db.insertAxiom pos l arr) :=
    insertAxiom_full_maintains_scoped db pos l arr
      h_wf h_scoped_db h_no_err h_first h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_success

  obtain ⟨fr, h_trim, h_no_int, _h_insert_ok⟩ := insertAxiom_success_conditions db pos l arr h_success
  have h_notvar0 : arr[0]!.isVar = false := by
    cases h_var0 : arr[0]!.isVar with
    | false => rfl
    | true =>
        have : False := by
          simpa [h_var0] using h_first.2
        exact False.elim this
  have h_head : Formula.hasConstHead arr = true := by
    unfold Formula.hasConstHead
    have h_pos : 0 < arr.size := h_first.1
    cases h0 : arr[0]! with
    | const _ => simp [h_pos]
    | var _ =>
        have : False := by
          simp [Sym.isVar, h0] at h_notvar0
        exact False.elim this
  have h_db_err : db.error = false := by
    simp [DB.error, h_no_err]
  have h_insertAxiom_eq :
      db.insertAxiom pos l arr = db.insert pos l (.assert arr fr) := by
    unfold DB.insertAxiom
    simp [h_head, h_db_err, h_trim, h_no_int]

  refine ⟨h_scoped_new, ?_⟩
  intro sc h_mem_sc
  have h_mem_sc' : sc ∈ db.scopes.toList := by
    simpa [h_insertAxiom_eq, insert_scopes] using h_mem_sc
  have h_scoped_old : WellScopedFrame db (db.frame.shrink sc) :=
    h_scopes_db sc h_mem_sc'

  have h_not_in_frame : l ∉ db.frame.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index db.frame.hyps l h_mem with ⟨i, hi, h_eq_lbl⟩
    have h_eq' : db.frame.hyps[i]'hi = l := by
      have h_bang : db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq_lbl
    exact (h_fresh_label i hi) h_eq'
  have h_not_in_shrink : l ∉ (db.frame.shrink sc).hyps.toList := by
    intro h_mem
    have : l ∈ db.frame.hyps.toList := by
      have : l ∈ (db.frame.hyps.toList.take sc.2) := by
        simpa [Frame.shrink] using h_mem
      exact List.mem_of_mem_take this
    exact (h_not_in_frame this).elim

  have h_scoped_after_insert :
      WellScopedFrame (db.insert pos l (.assert arr fr)) (db.frame.shrink sc) := by
    exact wellScopedFrame_preserved_by_insert
      db pos l (.assert arr fr) (db.frame.shrink sc) h_scoped_old h_not_in_shrink

  have h_shrink_frame :
      (db.insert pos l (.assert arr fr)).frame.shrink sc = db.frame.shrink sc := by
    simpa [insert_frame_unchanged]
  simpa [h_insertAxiom_eq, h_shrink_frame] using h_scoped_after_insert

/-- Fresh insertion of an assertion preserves `WellScopedDBWithScopes`. -/
theorem insertAssert_full_maintains_scopedWithScopes
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDBWithScopes db)
    (h_no_err : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_frame_wf : WellFormedFrame db fr)
    (h_frame_scoped : WellScopedFrame db fr)
    (h_syms : DB.formulaSymsRespectFrame db fmla fr = true)
    (h_decl : FormulaSymbolsDeclared db fmla)
    (h_insert_ok : (db.insert pos l (.assert fmla fr)).error? = none) :
    WellScopedDBWithScopes (db.insert pos l (.assert fmla fr)) := by
  classical
  rcases h_scoped with ⟨h_scoped_db, h_scopes_db⟩
  have h_fresh_label :
      ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l := by
    exact fresh_not_in_frame_of_wfFrame db db.frame l h_wf.1 h_fresh_db
  have h_fresh_in_asserts :
      ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l := by
    exact fresh_not_in_assert_frames_of_wf db h_wf l h_fresh_db

  have h_not_in_frame : l ∉ db.frame.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index db.frame.hyps l h_mem with ⟨i, hi, h_eq_lbl⟩
    have h_eq' : db.frame.hyps[i]'hi = l := by
      have h_bang : db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq_lbl
    exact (h_fresh_label i hi) h_eq'

  have h_not_in_fr : l ∉ fr.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index fr.hyps l h_mem with ⟨i, hi, h_eq_lbl⟩
    have h_eq' : fr.hyps[i]'hi = l := by
      have h_bang : fr.hyps[i]! = fr.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := fr.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq_lbl
    have h_hypok := h_frame_wf.1 i hi
    rcases h_hypok with ⟨ess, f, lbl, h_find, _h_float, _h_ess⟩
    have h_find_l : db.find? l = some (.hyp ess f lbl) := by
      simpa [h_eq'] using h_find
    have : db.find? l ≠ none := by
      simp [h_find_l]
    exact (this h_fresh_db).elim

  have h_scoped_frame :
      WellScopedFrame (db.insert pos l (.assert fmla fr)) db.frame := by
    exact wellScopedFrame_preserved_by_insert
      db pos l (.assert fmla fr) db.frame h_scoped_db.1 h_not_in_frame
  have h_scoped_frame' :
      WellScopedFrame (db.insert pos l (.assert fmla fr)) (db.insert pos l (.assert fmla fr)).frame := by
    simpa [insert_frame_unchanged] using h_scoped_frame

  have h_scoped_db' : WellScopedDB (db.insert pos l (.assert fmla fr)) := by
    refine ⟨h_scoped_frame', ?_⟩
    intro lbl obj h_find
    by_cases h_lbl : lbl = l
    · cases h_lbl
      have h_db_err : db.error = false := (error_false_iff_error?_none db).2 h_no_err
      have h_insert_err : (db.insert pos l (.assert fmla fr)).error = false :=
        (error_false_iff_error?_none (db.insert pos l (.assert fmla fr))).2 h_insert_ok
      have h_self : (db.insert pos l (.assert fmla fr)).find? l = some (.assert fmla fr l) := by
        exact Verify.DB.insert_find?_self db pos l (.assert fmla fr)
          h_db_err h_fresh_db h_insert_err
      have h_obj_eq : obj = .assert fmla fr l := by
        exact Option.some.inj (h_find.symm.trans h_self)
      cases h_obj_eq
      -- Promote the frame and formula facts to the new DB.
      have h_scoped_fr' : WellScopedFrame (db.insert pos l (.assert fmla fr)) fr := by
        exact wellScopedFrame_preserved_by_insert
          db pos l (.assert fmla fr) fr h_frame_scoped h_not_in_fr
      have h_syms' :
          DB.formulaSymsRespectFrame (db.insert pos l (.assert fmla fr)) fmla fr = true := by
        exact formulaSymsRespectFrame_preserved_by_insert
          db pos l (.assert fmla fr) fr fmla h_not_in_fr h_syms
      have h_decl' : FormulaSymbolsDeclared (db.insert pos l (.assert fmla fr)) fmla := by
        exact formulaSymbolsDeclared_preserved_by_insert
          db pos l (.assert fmla fr) fmla h_decl h_fresh_db
      exact ⟨h_scoped_fr', h_syms', h_decl'⟩
    · have h_find_old : db.find? lbl = some obj := by
        have h_eq := insert_preserves_find?_ne db pos l lbl (.assert fmla fr) h_lbl
        simpa [h_eq] using h_find
      cases obj with
      | const _ =>
          simp
      | var _ =>
          simp
      | assert f fr' name =>
          have h_old := h_scoped_db.2 lbl (.assert f fr' name) h_find_old
          have h_not_in_fr' : l ∉ fr'.hyps.toList := by
            intro h_mem'
            rcases Array.toList_mem_implies_index fr'.hyps l h_mem' with ⟨i, hi, h_eq_lbl⟩
            have h_eq' : fr'.hyps[i]'hi = l := by
              have h_bang : fr'.hyps[i]! = fr'.hyps[i]'hi := by
                simpa using (Array.getBang_eq_get_nat (a := fr'.hyps) (i := i) (h := hi))
              exact h_bang.symm.trans h_eq_lbl
            exact (h_fresh_in_asserts lbl f fr' name h_find_old i hi) h_eq'
          have h_scoped_fr' : WellScopedFrame (db.insert pos l (.assert fmla fr)) fr' := by
            exact wellScopedFrame_preserved_by_insert
              db pos l (.assert fmla fr) fr' h_old.1 h_not_in_fr'
          have h_syms' :
              DB.formulaSymsRespectFrame (db.insert pos l (.assert fmla fr)) f fr' = true := by
            exact formulaSymsRespectFrame_preserved_by_insert
              db pos l (.assert fmla fr) fr' f h_not_in_fr' h_old.2.1
          have h_decl' : FormulaSymbolsDeclared (db.insert pos l (.assert fmla fr)) f := by
            exact formulaSymbolsDeclared_preserved_by_insert
              db pos l (.assert fmla fr) f h_old.2.2 h_fresh_db
          exact ⟨h_scoped_fr', h_syms', h_decl'⟩
      | hyp ess f lbl' =>
          have h_old := h_scoped_db.2 lbl (.hyp ess f lbl') h_find_old
          constructor
          · intro h_mem_new
            have h_mem_old : lbl ∈ db.frame.hyps.toList := by
              simpa [insert_frame_unchanged] using h_mem_new
            have h_syms_old := h_old.1 h_mem_old
            have h_syms_new :=
              formulaSymsRespectFrame_preserved_by_insert
                db pos l (.assert fmla fr) db.frame f h_not_in_frame h_syms_old
            simpa [insert_frame_unchanged] using h_syms_new
          · exact formulaSymbolsDeclared_preserved_by_insert
              db pos l (.assert fmla fr) f h_old.2 h_fresh_db

  refine ⟨h_scoped_db', ?_⟩
  intro sc h_mem_sc
  have h_mem_sc' : sc ∈ db.scopes.toList := by
    simpa [insert_scopes] using h_mem_sc
  have h_scoped_old : WellScopedFrame db (db.frame.shrink sc) :=
    h_scopes_db sc h_mem_sc'
  have h_not_in_shrink : l ∉ (db.frame.shrink sc).hyps.toList := by
    intro h_mem
    have : l ∈ db.frame.hyps.toList := by
      have : l ∈ (db.frame.hyps.toList.take sc.2) := by
        simpa [Frame.shrink] using h_mem
      exact List.mem_of_mem_take this
    exact (h_not_in_frame this).elim
  have h_scoped_after_insert :
      WellScopedFrame (db.insert pos l (.assert fmla fr)) (db.frame.shrink sc) := by
    exact wellScopedFrame_preserved_by_insert
      db pos l (.assert fmla fr) (db.frame.shrink sc) h_scoped_old h_not_in_shrink
  have h_shrink_frame :
      (db.insert pos l (.assert fmla fr)).frame.shrink sc = db.frame.shrink sc := by
    simpa [insert_frame_unchanged]
  simpa [h_shrink_frame] using h_scoped_after_insert

/-- Fresh insertion of a symbol object (`$c`/`$v`) preserves `WellScopedDBWithScopes`. -/
theorem insert_symbol_fresh_maintains_scopedWithScopes
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_obj_sym : (∃ c, obj l = .const c) ∨ ∃ v, obj l = .var v)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDBWithScopes db)
    (h_no_err : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_insert_ok : (db.insert pos l obj).error? = none) :
    WellScopedDBWithScopes (db.insert pos l obj) := by
  rcases h_scoped with ⟨h_scoped_db, h_scopes_db⟩
  have h_fresh_label :
      ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l := by
    exact fresh_not_in_frame_of_wfFrame db db.frame l h_wf.1 h_fresh_db
  have h_fresh_in_asserts :
      ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l := by
    exact fresh_not_in_assert_frames_of_wf db h_wf l h_fresh_db
  have h_not_in_frame : l ∉ db.frame.hyps.toList := by
    intro h_mem
    rcases Array.toList_mem_implies_index db.frame.hyps l h_mem with ⟨i, hi, h_eq_lbl⟩
    have h_eq' : db.frame.hyps[i]'hi = l := by
      have h_bang : db.frame.hyps[i]! = db.frame.hyps[i]'hi := by
        simpa using (Array.getBang_eq_get_nat (a := db.frame.hyps) (i := i) (h := hi))
      exact h_bang.symm.trans h_eq_lbl
    exact (h_fresh_label i hi) h_eq'

  have h_frame_scoped :
      WellScopedFrame (db.insert pos l obj) db.frame := by
    exact wellScopedFrame_preserved_by_insert db pos l obj db.frame h_scoped_db.1 h_not_in_frame
  have h_frame_scoped' :
      WellScopedFrame (db.insert pos l obj) (db.insert pos l obj).frame := by
    simpa [insert_frame_unchanged] using h_frame_scoped

  have h_scoped_new : WellScopedDB (db.insert pos l obj) := by
    refine ⟨h_frame_scoped', ?_⟩
    intro lbl obj' h_find
    by_cases h_lbl : lbl = l
    · cases h_lbl
      have h_db_err : db.error = false := (error_false_iff_error?_none db).2 h_no_err
      have h_insert_err : (db.insert pos l obj).error = false := by
        exact (error_false_iff_error?_none (db.insert pos l obj)).2 h_insert_ok
      have h_self : (db.insert pos l obj).find? l = some (obj l) := by
        exact Verify.DB.insert_find?_self db pos l obj h_db_err h_fresh_db h_insert_err
      have h_obj_eq : obj' = obj l := by
        exact Option.some.inj (h_find.symm.trans h_self)
      cases h_obj_eq
      rcases h_obj_sym with h_const | h_var
      · rcases h_const with ⟨c, h_const⟩
        simp [h_const]
      · rcases h_var with ⟨v, h_var⟩
        simp [h_var]
    · have h_find_old : db.find? lbl = some obj' := by
        have h_eq := insert_preserves_find?_ne db pos l lbl obj h_lbl
        simpa [h_eq] using h_find
      cases obj' with
      | const _ =>
          simp
      | var _ =>
          simp
      | assert f fr name =>
          have h_old := h_scoped_db.2 lbl (.assert f fr name) h_find_old
          have h_not_in_fr : l ∉ fr.hyps.toList := by
            intro h_mem
            rcases Array.toList_mem_implies_index fr.hyps l h_mem with ⟨i, hi, h_eq_lbl⟩
            have h_eq' : fr.hyps[i]'hi = l := by
              have h_bang : fr.hyps[i]! = fr.hyps[i]'hi := by
                simpa using (Array.getBang_eq_get_nat (a := fr.hyps) (i := i) (h := hi))
              exact h_bang.symm.trans h_eq_lbl
            exact (h_fresh_in_asserts lbl f fr name h_find_old i hi) h_eq'
          have h_scoped_fr : WellScopedFrame (db.insert pos l obj) fr := by
            exact wellScopedFrame_preserved_by_insert db pos l obj fr h_old.1 h_not_in_fr
          have h_syms_new :
              DB.formulaSymsRespectFrame (db.insert pos l obj) f fr = true := by
            exact formulaSymsRespectFrame_preserved_by_insert
              db pos l obj fr f h_not_in_fr h_old.2.1
          have h_decl_new : FormulaSymbolsDeclared (db.insert pos l obj) f := by
            exact formulaSymbolsDeclared_preserved_by_insert
              db pos l obj f h_old.2.2 h_fresh_db
          exact ⟨h_scoped_fr, h_syms_new, h_decl_new⟩
      | hyp ess f lbl' =>
          have h_old := h_scoped_db.2 lbl (.hyp ess f lbl') h_find_old
          constructor
          · intro h_mem_new
            have h_mem_old : lbl ∈ db.frame.hyps.toList := by
              simpa [insert_frame_unchanged] using h_mem_new
            have h_syms_old := h_old.1 h_mem_old
            have h_syms_new :=
              formulaSymsRespectFrame_preserved_by_insert
                db pos l obj db.frame f h_not_in_frame h_syms_old
            simpa [insert_frame_unchanged] using h_syms_new
          · exact formulaSymbolsDeclared_preserved_by_insert
              db pos l obj f h_old.2 h_fresh_db

  refine ⟨h_scoped_new, ?_⟩
  intro sc h_mem_sc
  have h_mem_sc' : sc ∈ db.scopes.toList := by
    simpa [insert_scopes] using h_mem_sc
  have h_scoped_old : WellScopedFrame db (db.frame.shrink sc) :=
    h_scopes_db sc h_mem_sc'
  have h_not_in_shrink : l ∉ (db.frame.shrink sc).hyps.toList := by
    intro h_mem
    have : l ∈ db.frame.hyps.toList := by
      have : l ∈ (db.frame.hyps.toList.take sc.2) := by
        simpa [Frame.shrink] using h_mem
      exact List.mem_of_mem_take this
    exact (h_not_in_frame this).elim
  have h_scoped_after_insert :
      WellScopedFrame (db.insert pos l obj) (db.frame.shrink sc) := by
    exact wellScopedFrame_preserved_by_insert
      db pos l obj (db.frame.shrink sc) h_scoped_old h_not_in_shrink
  have h_shrink_frame :
      (db.insert pos l obj).frame.shrink sc = db.frame.shrink sc := by
    simpa [insert_frame_unchanged]
  simpa [h_shrink_frame] using h_scoped_after_insert

/-- Strengthening of `feedTokens_maintains_scoped`: also preserves stored-scope snapshots. -/
theorem feedTokens_maintains_scopedWithScopes
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_decl : FormulaSymbolsDeclared s.db arr)
    (h_float : tokp.k = TokensKind.float → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_fresh_db : s.db.find? tokp.label = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < s.db.frame.hyps.size), s.db.frame.hyps[i]'hi ≠ tokp.label)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        s.db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ tokp.label)
    (h_success : (s.feedTokens arr tokp).db.error? = none) :
    WellScopedDBWithScopes (s.feedTokens arr tokp).db := by
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
        have h_scoped_insert : WellScopedDBWithScopes (s.db.insertHyp pos label false arr) :=
          insertHyp_full_maintains_scopedWithScopes s.db pos label false arr
            h_wf h_scoped h_ok h_no_err h_first h_second' h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_scoped_insert
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
        have h_scoped_insert : WellScopedDBWithScopes (s.db.insertHyp pos label true arr) :=
          insertHyp_full_maintains_scopedWithScopes s.db pos label true arr
            h_wf h_scoped h_ok h_no_err h_first h_second' h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_scoped_insert
    | ax =>
        have h_success' :
            (s.feedTokens arr ⟨.ax, pos, label⟩).db.error? = none := by
          simpa using h_success
        have h_db_eq :
            (s.feedTokens arr ⟨.ax, pos, label⟩).db =
              s.db.insertAxiom pos label arr :=
          feedTokens_ax_db s arr pos label h_first h_success'
        have h_insert_ok : (s.db.insertAxiom pos label arr).error? = none := by
          simpa [h_db_eq] using h_success'
        have h_scoped_insert : WellScopedDBWithScopes (s.db.insertAxiom pos label arr) :=
          insertAxiom_full_maintains_scopedWithScopes s.db pos label arr
            h_wf h_scoped h_no_err h_first h_decl h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok
        simpa [h_db_eq] using h_scoped_insert
    | thm =>
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
              simpa [h_db_eq] using h_scoped

/-- Non-`$p` `feedTokens` steps preserve `WellScopedDBWithScopes` using only
    success-side facts (head check, float shape, and fresh label extraction). -/
theorem feedTokens_maintains_scopedWithScopes_nonthm
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_non_thm : tokp.k ≠ TokensKind.thm)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_decl : FormulaSymbolsDeclared s.db arr)
    (h_success : (s.feedTokens arr tokp).db.error? = none) :
    WellScopedDBWithScopes (s.feedTokens arr tokp).db := by
  cases tokp with
  | mk k pos label =>
      cases k with
      | float =>
          have h_first : arr.size > 0 ∧ !arr[0]!.isVar :=
            feedTokens_success_first_not_var s arr ⟨.float, pos, label⟩ (by simpa using h_success)
          have h_shape : arr.size = 2 ∧ arr[1]!.isVar :=
            feedTokens_success_float_shape s arr pos label (by simpa using h_success)
          have h_fresh_db : s.db.find? label = none := by
            have h_db_eq :
                (s.feedTokens arr ⟨.float, pos, label⟩).db = s.db.insertHyp pos label false arr :=
              feedTokens_float_db s arr pos label h_first h_shape (by simpa using h_success)
            have h_insert_ok : (s.db.insertHyp pos label false arr).error? = none := by
              simpa [h_db_eq] using h_success
            exact insertHyp_success_fresh_db s.db pos label false arr h_insert_ok
          have h_fresh_label :
              ∀ (i : Nat) (hi : i < s.db.frame.hyps.size), s.db.frame.hyps[i]'hi ≠ label := by
            exact fresh_not_in_frame_of_wfFrame s.db s.db.frame label h_wf.1 h_fresh_db
          have h_fresh_in_asserts :
              ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
                s.db.find? lbl = some (.assert fmla fr_assert name) →
                ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ label := by
            exact fresh_not_in_assert_frames_of_wf s.db h_wf label h_fresh_db
          have h_float : (TokensKind.float = TokensKind.float → (arr.size = 2 ∧ arr[1]!.isVar)) := by
            intro _; exact h_shape
          exact feedTokens_maintains_scopedWithScopes s arr ⟨.float, pos, label⟩
            h_wf h_scoped h_ok h_no_err h_no_dup h_first h_decl h_float
            h_fresh_db h_fresh_label h_fresh_in_asserts (by simpa using h_success)
      | ess =>
          have h_first : arr.size > 0 ∧ !arr[0]!.isVar :=
            feedTokens_success_first_not_var s arr ⟨.ess, pos, label⟩ (by simpa using h_success)
          have h_fresh_db : s.db.find? label = none := by
            have h_db_eq :
                (s.feedTokens arr ⟨.ess, pos, label⟩).db = s.db.insertHyp pos label true arr :=
              feedTokens_ess_db s arr pos label h_first (by simpa using h_success)
            have h_insert_ok : (s.db.insertHyp pos label true arr).error? = none := by
              simpa [h_db_eq] using h_success
            exact insertHyp_success_fresh_db s.db pos label true arr h_insert_ok
          have h_fresh_label :
              ∀ (i : Nat) (hi : i < s.db.frame.hyps.size), s.db.frame.hyps[i]'hi ≠ label := by
            exact fresh_not_in_frame_of_wfFrame s.db s.db.frame label h_wf.1 h_fresh_db
          have h_fresh_in_asserts :
              ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
                s.db.find? lbl = some (.assert fmla fr_assert name) →
                ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ label := by
            exact fresh_not_in_assert_frames_of_wf s.db h_wf label h_fresh_db
          have h_float : (TokensKind.ess = TokensKind.float → (arr.size = 2 ∧ arr[1]!.isVar)) := by
            intro h_eq
            cases h_eq
          exact feedTokens_maintains_scopedWithScopes s arr ⟨.ess, pos, label⟩
            h_wf h_scoped h_ok h_no_err h_no_dup h_first h_decl h_float
            h_fresh_db h_fresh_label h_fresh_in_asserts (by simpa using h_success)
      | ax =>
          have h_first : arr.size > 0 ∧ !arr[0]!.isVar :=
            feedTokens_success_first_not_var s arr ⟨.ax, pos, label⟩ (by simpa using h_success)
          have h_fresh_db : s.db.find? label = none := by
            have h_db_eq :
                (s.feedTokens arr ⟨.ax, pos, label⟩).db = s.db.insertAxiom pos label arr :=
              feedTokens_ax_db s arr pos label h_first (by simpa using h_success)
            have h_insert_ok : (s.db.insertAxiom pos label arr).error? = none := by
              simpa [h_db_eq] using h_success
            exact insertAxiom_success_fresh_db s.db pos label arr h_insert_ok
          have h_fresh_label :
              ∀ (i : Nat) (hi : i < s.db.frame.hyps.size), s.db.frame.hyps[i]'hi ≠ label := by
            exact fresh_not_in_frame_of_wfFrame s.db s.db.frame label h_wf.1 h_fresh_db
          have h_fresh_in_asserts :
              ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
                s.db.find? lbl = some (.assert fmla fr_assert name) →
                ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ label := by
            exact fresh_not_in_assert_frames_of_wf s.db h_wf label h_fresh_db
          have h_float : (TokensKind.ax = TokensKind.float → (arr.size = 2 ∧ arr[1]!.isVar)) := by
            intro h_eq
            cases h_eq
          exact feedTokens_maintains_scopedWithScopes s arr ⟨.ax, pos, label⟩
            h_wf h_scoped h_ok h_no_err h_no_dup h_first h_decl h_float
            h_fresh_db h_fresh_label h_fresh_in_asserts (by simpa using h_success)
      | thm =>
          exact (h_non_thm rfl).elim

/-- In `.math` mode for non-`$p` statements, successful `feedToken` preserves
    `WellScopedDBWithScopes`. -/
theorem feedToken_math_nonthm_maintains_scopedWithScopes
    (s : ParserState) (i : Nat) (tk : ByteSlice) (arr : Array Sym) (p : TokensParser)
    (h_tokp : s.tokp = .math arr p)
    (h_non_thm : p.k ≠ TokensKind.thm)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_decl : FormulaSymbolsDeclared s.db arr)
    (h_success : (s.feedToken i tk).db.error? = none) :
    WellScopedDBWithScopes (s.feedToken i tk).db := by
  by_cases h_open : tk.eqArray "$(".toAscii
  · -- Enter comment mode; DB is unchanged.
    have h_db_eq : (s.feedToken i tk).db = s.db := by
      simp [ParserState.feedToken, h_tokp, h_open]
    simpa [h_db_eq] using h_scoped
  · by_cases h_delim : tk.eqArray p.k.delim
    · -- Delimiter closes the math statement and dispatches to feedTokens.
      have h_success_feedTokens : (s.feedTokens arr p).db.error? = none := by
        simpa [ParserState.feedToken, h_tokp, h_open, h_delim] using h_success
      have h_scoped_feedTokens :
          WellScopedDBWithScopes (s.feedTokens arr p).db :=
        feedTokens_maintains_scopedWithScopes_nonthm s arr p h_non_thm
          h_wf h_scoped h_ok h_no_err h_no_dup h_decl h_success_feedTokens
      simpa [ParserState.feedToken, h_tokp, h_open, h_delim] using h_scoped_feedTokens
    · -- Non-delimiter token in `.math`: on success, only tokp changes.
      have h_db_eq : (s.feedToken i tk).db = s.db := by
        by_cases h_math_ok : (toMath tk).fst = true
        · let tk' := (toMath tk).2
          cases h_find : s.db.find? tk' with
          | none =>
              have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                simp [ParserState.feedToken, h_tokp, h_open, h_delim, ParserState.withMath,
                  h_math_ok, tk', h_find, ParserState.mkError, ParserState.withDB, DB.mkError]
              exact (h_bad h_success).elim
          | some obj =>
              cases obj with
              | const _ =>
                  simp [ParserState.feedToken, h_tokp, h_open, h_delim, ParserState.withMath,
                    h_math_ok, tk', h_find, Bind.bind, Pure.pure]
              | var _ =>
                  simp [ParserState.feedToken, h_tokp, h_open, h_delim, ParserState.withMath,
                    h_math_ok, tk', h_find, Bind.bind, Pure.pure]
              | hyp _ _ _ =>
                  have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                    simp [ParserState.feedToken, h_tokp, h_open, h_delim, ParserState.withMath,
                      h_math_ok, tk', h_find, ParserState.mkError, ParserState.withDB, DB.mkError]
                  exact (h_bad h_success).elim
              | assert _ _ _ =>
                  have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                    simp [ParserState.feedToken, h_tokp, h_open, h_delim, ParserState.withMath,
                      h_math_ok, tk', h_find, ParserState.mkError, ParserState.withDB, DB.mkError]
                  exact (h_bad h_success).elim
        · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
            simp [ParserState.feedToken, h_tokp, h_open, h_delim, ParserState.withMath,
              h_math_ok, ParserState.mkError, ParserState.withDB, DB.mkError]
          exact (h_bad h_success).elim
      simpa [h_db_eq] using h_scoped

/-- `popScope` preserves `WellScopedDBWithScopes` when it succeeds. -/
theorem wellScopedDBWithScopes_popScope
    (db : DB) (pos : Pos)
    (h_wf : WellFormedDB db)
    (h_scoped : WellScopedDBWithScopes db)
    (h_ok : ScopesOk db)
    (h_success : (db.popScope pos).error? = none) :
    WellScopedDBWithScopes (db.popScope pos) := by
  classical
  rcases h_scoped with ⟨h_scoped_db, h_scopes⟩
  rcases h_ok with ⟨h_mono, h_within⟩
  unfold DB.popScope at h_success ⊢
  cases h_back : db.scopes.back? with
  | none =>
      simp [h_back, DB.mkError] at h_success
  | some sc =>
      -- Use `sc` as the new frame snapshot.
      have h_size_pos : 0 < db.scopes.size := by
        cases hsz : db.scopes.size with
        | zero =>
            have : db.scopes.back? = none := by
              simp [Array.back?, hsz]
            cases (this.symm.trans h_back)
        | succ n =>
            exact Nat.succ_pos n
      let last : Nat := db.scopes.size - 1
      have h_last_lt : last < db.scopes.size := Nat.sub_one_lt_of_lt h_size_pos
      have h_last_get? : db.scopes[last]? = some sc := by
        simpa [Array.back?, last] using h_back
      have h_last_bang : db.scopes[last]! = sc :=
        Array.getElem!_of_getElem?_eq_some db.scopes last sc h_last_get?
      have h_sc_mem : sc ∈ db.scopes.toList := by
        have h_mem : db.scopes[last]! ∈ db.scopes.toList :=
          Array.getElem!_mem_toList db.scopes last h_last_lt
        simpa [h_last_bang] using h_mem

      -- New DB is `{ db with frame := db.frame.shrink sc, scopes := db.scopes.pop }`.
      let db' : DB := { db with frame := db.frame.shrink sc, scopes := db.scopes.pop }
      have h_find_eq : ∀ lbl, db'.find? lbl = db.find? lbl := by
        intro lbl
        simp [db', DB.find?]

      -- The new current frame is well-scoped by the stored-scope invariant.
      have h_frame_scoped_old : WellScopedFrame db (db.frame.shrink sc) :=
        h_scopes sc h_sc_mem
      have h_frame_scoped : WellScopedFrame db' (db.frame.shrink sc) := by
        -- `find?` is unchanged; unfold to rewrite.
        simpa [db', WellScopedFrame, FloatDeclaredBefore, DB.formulaSymsRespectFrame, DB.frameFloatVars, DB.find?] using
          h_frame_scoped_old

      have h_scoped_db' : WellScopedDB db' := by
        refine ⟨?_, ?_⟩
        · -- current frame
          simpa [db'] using h_frame_scoped
        · intro lbl obj h_find
          have h_find_old : db.find? lbl = some obj := by
            simpa [h_find_eq] using h_find
          have h_obj := h_scoped_db.2 lbl obj h_find_old
          cases obj with
          | const _ => simpa using h_obj
          | var _ => simpa using h_obj
          | assert f fr name =>
              rcases h_obj with ⟨h_fr_scoped, h_syms, h_decl⟩
              refine ⟨?_, ?_, ?_⟩
              · -- frames are unaffected by popScope (objects unchanged)
                simpa [WellScopedFrame, FloatDeclaredBefore, DB.formulaSymsRespectFrame, DB.frameFloatVars, DB.find?, h_find_eq] using h_fr_scoped
              · simpa [DB.formulaSymsRespectFrame, DB.frameFloatVars, DB.find?, h_find_eq] using h_syms
              · simpa [FormulaSymbolsDeclared, DB.isConst, DB.isVar, DB.find?, h_find_eq] using h_decl
          | hyp ess f name =>
              constructor
              · intro h_in
                -- Only hyps in the new frame matter.
                cases ess with
                | true =>
                    -- Use the well-scopedness of the new current frame at the index of this label.
                    rcases Array.toList_mem_implies_index db'.frame.hyps lbl (by simpa [db'] using h_in) with
                      ⟨i, hi, h_eq⟩
                    have h_eq' : db'.frame.hyps[i]! = lbl := h_eq
                    have h_find' : db'.find? db'.frame.hyps[i]! = some (.hyp true f name) := by
                      simpa [h_eq', h_find_eq] using h_find
                    have h_find'' : db'.find? (db.frame.shrink sc).hyps[i]! = some (.hyp true f name) := by
                      simpa [db'] using h_find'
                    have h_scoped_i := (h_frame_scoped.1 i hi)
                    -- Rewrite the match to the essential-hyp branch.
                    have h_scoped_i' :
                        DB.formulaSymsRespectFrame db' f (Frame.mk #[] (db.frame.shrink sc).hyps) = true ∧
                        (∀ v, Sym.var v ∈ f.toList.tail → FloatDeclaredBefore db' (db.frame.shrink sc) i v) := by
                      simpa [h_find''] using h_scoped_i
                    -- formulaSymsRespectFrame ignores dj
                    have h_syms_mk :
                        DB.formulaSymsRespectFrame db' f (Frame.mk #[] db'.frame.hyps) = true := by
                      simpa [db'] using h_scoped_i'.1
                    simpa [frameFloatVars_mk_eq] using h_syms_mk
                | false =>
                    -- Float hypothesis: its own variable is in `frameFloatVars` since the label is in the frame.
                    have h_float : WellFormedFloat f := by
                      -- object well-formedness from WellFormedDB
                      have h_obj_wf := h_wf.2 lbl (.hyp false f name) h_find_old
                      simpa using h_obj_wf
                    have h_shape : f.isFloatShape = true :=
                      isFloatShape_of_wellFormedFloat h_float
                    rcases h_float with ⟨h_size, ⟨c, v, h0, h1⟩⟩
                    have h_lbl_mem : lbl ∈ db'.frame.hyps.toList := by
                      simpa [db'] using h_in
                    have h_mem :
                        v ∈ DB.frameFloatVars db' db'.frame := by
                      apply (frameFloatVars_mem_iff db' db'.frame.hyps v).2
                      refine ⟨lbl, f, name, h_lbl_mem, ?_, ?_, h1⟩
                      · simpa [h_find_eq] using h_find
                      · -- `isFloatShape` follows from WellFormedFloat
                        exact h_shape
                    have h_tail : f.toList.tail = [Sym.var v] := by
                      have h_tail' := toList_tail_of_size_two f h_size
                      simpa [h1] using h_tail'
                    unfold DB.formulaSymsRespectFrame
                    simp [h_tail, h_mem]
              · -- FormulaSymbolsDeclared unchanged (objects unchanged)
                simpa [FormulaSymbolsDeclared, DB.isConst, DB.isVar, DB.find?, h_find_eq] using h_obj.2

      -- Now show scope snapshots remain well-scoped after popping.
      refine ⟨?_, ?_⟩
      · exact h_scoped_db'
      · intro sc' h_mem'
        -- sc' is in the popped scope list, hence in the original one.
        have h_mem_old : sc' ∈ db.scopes.toList := by
          -- scopes.pop.toList is a prefix of scopes.toList
          have : sc' ∈ db.scopes.pop.toList := by
            simpa [db', h_back] using h_mem'
          -- pop.toList = dropLast, and dropLast membership implies membership.
          have : sc' ∈ db.scopes.toList.dropLast := by
            simpa [Array.pop] using this
          exact List.mem_of_mem_dropLast this
        have h_scoped_sc' : WellScopedFrame db (db.frame.shrink sc') := h_scopes sc' h_mem_old
        -- Use monotonicity to show sc' <= sc (as the last scope element).
        rcases Array.toList_mem_implies_index db'.scopes sc' (by simpa [db'] using h_mem') with
          ⟨i, hi, h_eq⟩
        have hi_old : i < db.scopes.size := by
          -- i < pop.size
          have hi_pop : i < db.scopes.size - 1 := by
            simpa [db', Array.size_pop] using hi
          exact Nat.lt_of_lt_of_le hi_pop (Nat.sub_le _ _)
        have hi_last : i < last := by
          have hi_pop : i < db.scopes.size - 1 := by
            simpa [db', Array.size_pop, last] using hi
          simpa [last] using hi_pop
        have h_le : ScopeLE (db.scopes[i]'hi_old) (db.scopes[last]'h_last_lt) :=
          h_mono i last hi_old h_last_lt hi_last
        have h_sc'_eq : db.scopes[i]'hi_old = sc' := by
          have h_eq_bang : db'.scopes[i]! = db'.scopes[i]'hi := by
            simpa using (Array.getBang_eq_get_nat (a := db'.scopes) (i := i) (h := hi))
          have h_eqi : db'.scopes[i]'hi = sc' := by
            exact h_eq_bang.symm.trans h_eq
          have h_eqi' : (db.scopes.pop)[i]'hi = sc' := by
            simpa [db'] using h_eqi
          have h_pop_eq : (db.scopes.pop)[i]'hi = db.scopes[i]'hi_old := by
            have := (Array.getElem_pop (xs := db.scopes) (i := i) hi)
            simpa using this
          exact h_pop_eq.symm.trans h_eqi'
        have h_sc_eq : db.scopes[last]'h_last_lt = sc := by
          have h_eq_bang : db.scopes[last]! = db.scopes[last]'h_last_lt := by
            simpa using (Array.getBang_eq_get_nat (a := db.scopes) (i := last) (h := h_last_lt))
          simpa [h_eq_bang] using h_last_bang
        have h_le' : ScopeLE sc' sc := by
          simpa [h_sc'_eq, h_sc_eq] using h_le
        -- Rewrite the frame shrink.
        have h_shrink : (db.frame.shrink sc).shrink sc' = db.frame.shrink sc' := by
          simpa using Frame.shrink_shrink_of_le (fr := db.frame) (a := sc) (b := sc') h_le'
        -- Transfer and rewrite.
        have h_scoped_sc'' : WellScopedFrame db' (db.frame.shrink sc') := by
          simpa [db', WellScopedFrame, FloatDeclaredBefore, DB.formulaSymsRespectFrame, DB.frameFloatVars, DB.find?] using h_scoped_sc'
        simpa [db', h_shrink] using h_scoped_sc''

/-- In `.start` mode, successful `feedToken` preserves `WellScopedDBWithScopes`. -/
theorem feedToken_start_maintains_scopedWithScopes
    (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_tokp : s.tokp = .start)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_success : (s.feedToken i tk).db.error? = none) :
    WellScopedDBWithScopes (s.feedToken i tk).db := by
  by_cases h_open : tk.eqArray "$(".toAscii
  · -- Enter comment mode; DB unchanged.
    have h_db_eq : (s.feedToken i tk).db = s.db := by
      simp [ParserState.feedToken, h_tokp, h_open]
    simpa [h_db_eq] using h_scoped
  · by_cases h_cmd : tk.len == 2 && tk[0]! == '$'.toUInt8
    · -- One-character command after '$'.
      by_cases h_lbrace : tk[1]!.toChar = '{'
      · have h_db_eq : (s.feedToken i tk).db = s.db.pushScope := by
          simp [ParserState.feedToken, h_tokp, h_open, h_cmd, h_lbrace, ParserState.withDB]
        simpa [h_db_eq] using wellScopedDBWithScopes_pushScope s.db h_scoped
      · by_cases h_rbrace : tk[1]!.toChar = '}'
        · have h_pop_ok : (s.db.popScope (s.mkPos i)).error? = none := by
            simpa [ParserState.feedToken, h_tokp, h_open, h_cmd, h_lbrace, h_rbrace, ParserState.withDB] using h_success
          have h_scoped_pop :
              WellScopedDBWithScopes (s.db.popScope (s.mkPos i)) :=
            wellScopedDBWithScopes_popScope s.db (s.mkPos i) h_wf h_scoped h_ok h_pop_ok
          simpa [ParserState.feedToken, h_tokp, h_open, h_cmd, h_lbrace, h_rbrace, ParserState.withDB] using h_scoped_pop
        · by_cases h_c : tk[1]!.toChar = 'c'
          · have h_db_eq : (s.feedToken i tk).db = s.db := by
              simp [ParserState.feedToken, h_tokp, h_open, h_cmd, h_lbrace, h_rbrace, h_c]
            simpa [h_db_eq] using h_scoped
          · by_cases h_v : tk[1]!.toChar = 'v'
            · have h_db_eq : (s.feedToken i tk).db = s.db := by
                simp [ParserState.feedToken, h_tokp, h_open, h_cmd, h_lbrace, h_rbrace, h_c, h_v]
              simpa [h_db_eq] using h_scoped
            · by_cases h_d : tk[1]!.toChar = 'd'
              · have h_db_eq : (s.feedToken i tk).db = s.db := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_cmd, h_lbrace, h_rbrace, h_c, h_v, h_d]
                simpa [h_db_eq] using h_scoped
              · -- Label path; success excludes mkError and leaves DB unchanged.
                have h_db_eq : (s.feedToken i tk).db = s.db := by
                  unfold ParserState.feedToken
                  simp [h_tokp, h_open, h_cmd, h_lbrace, h_rbrace, h_c, h_v, h_d, ParserState.label]
                  by_cases h_label_ok : (toLabel tk).fst
                  · simp [h_label_ok]
                  · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                      simp [ParserState.feedToken, h_tokp, h_open, h_cmd, h_lbrace, h_rbrace, h_c, h_v, h_d,
                        ParserState.label, h_label_ok, ParserState.mkError, ParserState.withDB, DB.mkError]
                    exact (h_bad h_success).elim
                simpa [h_db_eq] using h_scoped
    · -- Not a `$x` command: label path; success excludes mkError.
      have h_db_eq : (s.feedToken i tk).db = s.db := by
        unfold ParserState.feedToken
        simp [h_tokp, h_open, h_cmd, ParserState.label]
        by_cases h_label_ok : (toLabel tk).fst
        · simp [h_label_ok]
        · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
            simp [ParserState.feedToken, h_tokp, h_open, h_cmd,
              ParserState.label, h_label_ok, ParserState.mkError, ParserState.withDB, DB.mkError]
          exact (h_bad h_success).elim
      simpa [h_db_eq] using h_scoped

/-- In `.const` mode, successful `feedToken` preserves `WellScopedDBWithScopes`. -/
theorem feedToken_const_maintains_scopedWithScopes
    (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_tokp : s.tokp = .const)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_no_err : s.db.error? = none)
    (h_success : (s.feedToken i tk).db.error? = none) :
    WellScopedDBWithScopes (s.feedToken i tk).db := by
  by_cases h_open : tk.eqArray "$(".toAscii
  · have h_db_eq : (s.feedToken i tk).db = s.db := by
      simp [ParserState.feedToken, h_tokp, h_open]
    simpa [h_db_eq] using h_scoped
  · by_cases h_end : tk.eqArray "$.".toAscii
    · have h_db_eq : (s.feedToken i tk).db = s.db := by
        simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym]
      simpa [h_db_eq] using h_scoped
    · by_cases h_math_ok : (toMath tk).fst = true
      · let tk' := (toMath tk).snd
        have h_insert_ok : (s.db.insert (s.mkPos i) tk' (fun x => Object.const x)).error? = none := by
          simpa [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
            h_math_ok, tk', ParserState.withDB] using h_success
        have h_fresh_db : s.db.find? tk' = none := by
          exact insert_success_nonvar_fresh s.db (s.mkPos i) tk' (fun x => Object.const x)
            h_no_err h_insert_ok (by intro v h_eq; cases h_eq)
        have h_scoped_insert :
            WellScopedDBWithScopes (s.db.insert (s.mkPos i) tk' (fun x => Object.const x)) := by
          exact insert_symbol_fresh_maintains_scopedWithScopes
            s.db (s.mkPos i) tk' (fun x => Object.const x)
            (by left; exact ⟨tk', rfl⟩)
            h_wf h_scoped h_no_err h_fresh_db h_insert_ok
        have h_db_eq :
            (s.feedToken i tk).db = s.db.insert (s.mkPos i) tk' (fun x => Object.const x) := by
          simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
            h_math_ok, tk', ParserState.withDB]
        simpa [h_db_eq] using h_scoped_insert
      · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
          simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath, h_math_ok,
            ParserState.mkError, ParserState.withDB, DB.mkError]
        exact (h_bad h_success).elim

/-- In `.var` mode, successful `feedToken` preserves `WellScopedDBWithScopes`. -/
theorem feedToken_var_maintains_scopedWithScopes
    (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_tokp : s.tokp = .var)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_no_err : s.db.error? = none)
    (h_success : (s.feedToken i tk).db.error? = none) :
    WellScopedDBWithScopes (s.feedToken i tk).db := by
  have h_db_err_false : s.db.error = false := by
    exact (error_false_iff_error?_none s.db).2 h_no_err
  by_cases h_open : tk.eqArray "$(".toAscii
  · have h_db_eq : (s.feedToken i tk).db = s.db := by
      simp [ParserState.feedToken, h_tokp, h_open]
    simpa [h_db_eq] using h_scoped
  · by_cases h_end : tk.eqArray "$.".toAscii
    · have h_db_eq : (s.feedToken i tk).db = s.db := by
        simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym]
      simpa [h_db_eq] using h_scoped
    · by_cases h_math_ok : (toMath tk).fst = true
      · let tk' := (toMath tk).snd
        cases h_find : s.db.find? tk' with
        | none =>
            have h_insert_ok : (s.db.insert (s.mkPos i) tk' (fun x => Object.var x)).error? = none := by
              simpa [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
                h_math_ok, tk', ParserState.withDB, h_find] using h_success
            have h_scoped_insert :
                WellScopedDBWithScopes (s.db.insert (s.mkPos i) tk' (fun x => Object.var x)) := by
              exact insert_symbol_fresh_maintains_scopedWithScopes
                s.db (s.mkPos i) tk' (fun x => Object.var x)
                (by right; exact ⟨tk', rfl⟩)
                h_wf h_scoped h_no_err h_find h_insert_ok
            have h_db_eq :
                (s.feedToken i tk).db = s.db.insert (s.mkPos i) tk' (fun x => Object.var x) := by
              simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
                h_math_ok, tk', ParserState.withDB, h_find]
            simpa [h_db_eq] using h_scoped_insert
        | some obj =>
            cases obj with
            | var _ =>
                have h_db_eq : (s.feedToken i tk).db = s.db := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
                    h_math_ok, tk', ParserState.withDB, h_find, DB.insert, h_no_err]
                simpa [h_db_eq] using h_scoped
            | const _ =>
                have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
                    h_math_ok, tk', ParserState.withDB, h_find, DB.insert, h_no_err, h_db_err_false, DB.mkError]
                exact (h_bad h_success).elim
            | hyp _ _ _ =>
                have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
                    h_math_ok, tk', ParserState.withDB, h_find, DB.insert, h_no_err, h_db_err_false, DB.mkError]
                exact (h_bad h_success).elim
            | assert _ _ _ =>
                have h_bad : (s.feedToken i tk).db.error? ≠ none := by
                  simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath,
                    h_math_ok, tk', ParserState.withDB, h_find, DB.insert, h_no_err, h_db_err_false, DB.mkError]
                exact (h_bad h_success).elim
      · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
          simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.sym, ParserState.withMath, h_math_ok,
            ParserState.mkError, ParserState.withDB, DB.mkError]
        exact (h_bad h_success).elim

/-- Internal: `djvars_loop_aux` preserves `WellScopedDBWithScopes` on success. -/
theorem djvars_loop_aux_maintains_scopedWithScopes
    (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) (i : Nat)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_tokp : TokpInv s.db (.djvars arr))
    (h_var : s.db.isVar tk = true)
    (h_in_scope : s.db.floatVarOccursInFrame tk = true)
    (h_success : (ParserState.djvars_loop_aux arr s pos tk i).db.error? = none) :
    WellScopedDBWithScopes (ParserState.djvars_loop_aux arr s pos tk i).db := by
  -- Induction on the remainder `arr.size - i`.
  refine Nat.rec (motive := fun m => ∀ i (s : ParserState),
      arr.size - i = m →
      WellFormedDB s.db →
      WellScopedDBWithScopes s.db →
      ScopesOk s.db →
      TokpInv s.db (.djvars arr) →
      s.db.isVar tk = true →
      s.db.floatVarOccursInFrame tk = true →
      (ParserState.djvars_loop_aux arr s pos tk i).db.error? = none →
      WellScopedDBWithScopes (ParserState.djvars_loop_aux arr s pos tk i).db)
    ?base ?step (arr.size - i) i s rfl h_wf h_scoped h_ok h_tokp h_var h_in_scope h_success
  · intro i s hs h_wf h_scoped _h_ok _h_tokp _h_var _h_in_scope _h_success
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simpa [hs] using hpos
    -- Base: no loop step, DB unchanged.
    simpa [ParserState.djvars_loop_aux, hi] using h_scoped
  · intro m ih i s hs h_wf h_scoped h_ok h_tokp h_var h_in_scope h_success
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      ·
        have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        have : False := by
          have hs' := hs
          simpa [hz] using hs'
        exact False.elim this
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    -- Unfold one step
    unfold ParserState.djvars_loop_aux at h_success ⊢
    simp [hi] at h_success ⊢
    let tk1 : String := arr[i]
    by_cases h_eq : tk1 = tk
    · -- duplicate variable branch: mkError, cannot succeed
      -- duplicate variable branch: mkError, cannot succeed
      have h_success' :
          (s.mkError pos s!"duplicate disjoint variable {tk}").db.error? = none := by
          simpa [tk1, h_eq] using h_success
      have h_bad : (s.mkError pos s!"duplicate disjoint variable {tk}").db.error? ≠ none := by
        simp [ParserState.mkError, ParserState.withDB, DB.mkError]
      exact (h_bad h_success').elim
    · -- Non-duplicate: push DJ pair and recurse.
      -- Non-duplicate: push DJ pair and recurse.
      have h_success' :
          (ParserState.djvars_loop_aux arr
              (s.withDB
                (fun db => DB.withDJ (fun dj => dj.push (if arr[i] < tk then (arr[i], tk) else (tk, arr[i]))) db) )
              pos tk (i + 1)).db.error? = none := by
          simpa [tk1, h_eq] using h_success
      have h_mem_tk1 : tk1 ∈ arr.toList := by
        -- `tk1` is `arr[i]`
        have h_mem := Array.getElem!_mem_toList arr i hi
        -- `arr[i]!` equals `arr[i]` in this branch.
        simpa [tk1] using h_mem
      have h_tk1_props := h_tokp tk1 h_mem_tk1
      have h_var_tk1 : s.db.isVar tk1 = true := h_tk1_props.1
      have h_scope_tk1 : s.db.floatVarOccursInFrame tk1 = true := h_tk1_props.2
      have h_tk1_in :
          tk1 ∈ DB.frameFloatVars s.db s.db.frame := by
        exact floatVarOccursInFrame_true_implies s.db tk1 h_wf h_scope_tk1
      have h_tk_in :
          tk ∈ DB.frameFloatVars s.db s.db.frame := by
        exact floatVarOccursInFrame_true_implies s.db tk h_wf h_in_scope
      have h_ne : tk1 ≠ tk := by
        exact h_eq
      have h_lt_pair : (if tk1 < tk then tk1 else tk) < (if tk1 < tk then tk else tk1) := by
        by_cases h_lt : tk1 < tk
        · simp [h_lt]
        · -- `tk1 ≠ tk` and `¬ tk1 < tk` imply `tk < tk1`
          have h_gt : tk < tk1 := by
            by_cases h_gt' : tk < tk1
            · exact h_gt'
            · have h_eq' : tk1 = tk := String.lt_antisymm h_lt h_gt'
              exact (h_ne h_eq').elim
          simpa [h_lt] using h_gt
      let p : DJ := if tk1 < tk then (tk1, tk) else (tk, tk1)
      have h_p : p = if tk1 < tk then (tk1, tk) else (tk, tk1) := rfl
      have h_p' : p.1 < p.2 ∧
          p.1 ∈ DB.frameFloatVars s.db s.db.frame ∧
          p.2 ∈ DB.frameFloatVars s.db s.db.frame := by
        by_cases h_lt : tk1 < tk
        · simp [h_p, h_lt, h_lt_pair, h_tk1_in, h_tk_in]
        · -- In this branch p = (tk, tk1)
          have h_gt : tk < tk1 := by
            by_cases h_gt' : tk < tk1
            · exact h_gt'
            · have h_eq' : tk1 = tk := String.lt_antisymm h_lt h_gt'
              exact (h_ne h_eq').elim
          simp [h_p, h_lt, h_gt, h_tk1_in, h_tk_in]
      -- Update invariants for the recursive call.
      have h_wf' : WellFormedDB (s.db.withDJ (·.push p)) := by
        exact wellFormedDB_preserved_by_withDJ s.db (·.push p) h_wf
      have h_scoped' : WellScopedDBWithScopes (s.db.withDJ (·.push p)) := by
        exact wellScopedDBWithScopes_withDJ_push s.db p h_wf h_scoped h_ok h_p'
      have h_ok' : ScopesOk (s.db.withDJ (·.push p)) := by
        exact scopesOk_withDJ_push s.db p h_ok
      have h_tokp' : TokpInv (s.db.withDJ (·.push p)) (.djvars arr) := by
        -- `isVar` and `floatVarOccursInFrame` are unchanged by `withDJ`.
        intro v h_mem
        have h_old := h_tokp v h_mem
        constructor
        · simpa [DB.isVar, DB.withDJ, DB.withFrame, DB.find?] using h_old.1
        · simpa [DB.floatVarOccursInFrame, DB.withDJ, DB.withFrame, DB.find?] using h_old.2
      have h_var' : (s.db.withDJ (·.push p)).isVar tk = true := by
        simpa [DB.isVar, DB.withDJ, DB.withFrame, DB.find?] using h_var
      have h_in_scope' : (s.db.withDJ (·.push p)).floatVarOccursInFrame tk = true := by
        simpa [DB.floatVarOccursInFrame, DB.withDJ, DB.withFrame, DB.find?] using h_in_scope
      have h_success_rec :
          (ParserState.djvars_loop_aux arr (s.withDB fun db => db.withDJ (·.push p)) pos tk (i + 1)).db.error? = none := by
        simpa [tk1, h_p] using h_success'
      -- Apply IH
      have h_rec :=
        ih (i + 1) (s.withDB fun db => db.withDJ (·.push p)) hs'
          h_wf' h_scoped' h_ok' h_tokp' h_var' h_in_scope' h_success_rec
      -- finish by rewriting the outer call (avoid recursive simp loops)
      simpa [ParserState.djvars_loop_aux, hi, tk1, h_eq, ParserState.withDB, h_p,
        -ParserState.djvars_loop_aux.eq_1] using h_rec

/-- `djvars_loop` preserves `WellScopedDBWithScopes` on success. -/
theorem djvars_loop_maintains_scopedWithScopes
    (arr : Array String) (s : ParserState) (pos : Pos) (tk : String)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_tokp : TokpInv s.db (.djvars arr))
    (h_var : s.db.isVar tk = true)
    (h_in_scope : s.db.floatVarOccursInFrame tk = true)
    (h_success : (ParserState.djvars_loop arr s pos tk).db.error? = none) :
    WellScopedDBWithScopes (ParserState.djvars_loop arr s pos tk).db := by
  unfold ParserState.djvars_loop at h_success ⊢
  simp [h_var, h_in_scope] at h_success ⊢
  exact djvars_loop_aux_maintains_scopedWithScopes arr s pos tk 0
    h_wf h_scoped h_ok h_tokp h_var h_in_scope h_success

/-- In `.djvars` mode, successful `feedToken` preserves `WellScopedDBWithScopes`. -/
theorem feedToken_djvars_maintains_scopedWithScopes
    (s : ParserState) (i : Nat) (tk : ByteSlice) (arr : Array String)
    (h_tokp : s.tokp = .djvars arr)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_tokp_inv : TokpInv s.db s.tokp)
    (h_success : (s.feedToken i tk).db.error? = none) :
    WellScopedDBWithScopes (s.feedToken i tk).db := by
  by_cases h_open : tk.eqArray "$(".toAscii
  · have h_db_eq : (s.feedToken i tk).db = s.db := by
      simp [ParserState.feedToken, h_tokp, h_open]
    simpa [h_db_eq] using h_scoped
  · by_cases h_end : tk.eqArray "$.".toAscii
    · have h_db_eq : (s.feedToken i tk).db = s.db := by
        simp [ParserState.feedToken, h_tokp, h_open, h_end]
      simpa [h_db_eq] using h_scoped
    · by_cases h_math_ok : (toMath tk).fst = true
      · let tk' := (toMath tk).snd
        have h_success_loop :
            (ParserState.djvars_loop arr s (s.mkPos i) tk').db.error? = none := by
          simpa [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.withMath, h_math_ok, tk'] using h_success
        have h_var : s.db.isVar tk' = true := by
          by_cases h_var : s.db.isVar tk'
          · exact h_var
          · have h_bad :
              (ParserState.djvars_loop arr s (s.mkPos i) tk').db.error? ≠ none := by
              simp [ParserState.djvars_loop, h_var, ParserState.mkError, ParserState.withDB, DB.mkError]
            exact (h_bad h_success_loop).elim
        have h_in_scope : s.db.floatVarOccursInFrame tk' = true := by
          by_cases h_float : s.db.floatVarOccursInFrame tk'
          · exact h_float
          · have h_bad :
              (ParserState.djvars_loop arr s (s.mkPos i) tk').db.error? ≠ none := by
              simp [ParserState.djvars_loop, h_var, h_float, ParserState.mkError, ParserState.withDB, DB.mkError]
            exact (h_bad h_success_loop).elim
        have h_tokp' : TokpInv s.db (.djvars arr) := by
          simpa [h_tokp] using h_tokp_inv
        have h_scoped_loop :
            WellScopedDBWithScopes (ParserState.djvars_loop arr s (s.mkPos i) tk').db := by
          exact djvars_loop_maintains_scopedWithScopes arr s (s.mkPos i) tk'
            h_wf h_scoped h_ok h_tokp' h_var h_in_scope h_success_loop
        simpa [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.withMath, h_math_ok, tk'] using h_scoped_loop
      · have h_bad : (s.feedToken i tk).db.error? ≠ none := by
          simp [ParserState.feedToken, h_tokp, h_open, h_end, ParserState.withMath, h_math_ok,
            ParserState.mkError, ParserState.withDB, DB.mkError]
        exact (h_bad h_success).elim

theorem withAt_success_eq
    (l : String) (f : Unit → ParserState)
    (h_success : (ParserState.withAt l f).db.error? = none) :
    (f ()).db.error? = none ∧ (ParserState.withAt l f).db = (f ()).db := by
  unfold ParserState.withAt at h_success
  generalize hs : f () = s0
  cases h_err : s0.db.error? with
  | none =>
      have h_ok : s0.db.error? = none := by
        simpa [hs, h_err] using h_success
      have h_eq : (ParserState.withAt l f).db = s0.db := by
        simp [ParserState.withAt, hs, h_err]
      exact ⟨by simpa [hs] using h_ok, by simpa [hs, h_err] using h_eq⟩
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e <;>
          · have h_bad : (ParserState.withAt l f).db.error? ≠ none := by
              simp [ParserState.withAt, hs, h_err, ParserState.withDB]
            exact (h_bad h_success).elim

theorem feedProof_success_db
    (s : ParserState) (tk : ByteSlice) (pr : ProofState)
    (h_success : (s.feedProof tk pr).db.error? = none) :
    (s.feedProof tk pr).db = s.db := by
  unfold ParserState.feedProof at h_success ⊢
  -- `withAt` success implies the inner state succeeds.
  have h_inner := withAt_success_eq pr.label
    (fun _ =>
      match ParserState.feedProof.go s tk pr with
      | .ok pr => { s with tokp := .proof pr }
      | .error msg => s.mkError pr.pos msg) h_success
  rcases h_inner with ⟨h_inner_ok, h_eq⟩
  cases h_go : ParserState.feedProof.go s tk pr with
  | ok pr' =>
      -- inner state is `{s with tokp := .proof pr'}`; db unchanged
      simpa [h_go] using h_eq
  | error msg =>
      have h_bad : (s.mkError pr.pos msg).db.error? ≠ none := by
        simp [ParserState.mkError, ParserState.withDB, DB.mkError]
      have : (s.mkError pr.pos msg).db.error? = none := by
        simpa [h_go] using h_inner_ok
      exact (h_bad this).elim

theorem finishProof_success_insert
    (s : ParserState) (pr : ProofState)
    (h_success : (s.finishProof pr).db.error? = none) :
    (s.finishProof pr).db = s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame) ∧
    (s.db.insert pr.pos pr.label (.assert pr.fmla pr.frame)).error? = none := by
  cases pr with
  | mk pos l fmla fr heap stack ptp =>
      cases ptp with
      | start =>
          have h_bad : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .start⟩).db.error? ≠ none := by
            simp [ParserState.finishProof, ParserState.withAt, ParserState.mkError, ParserState.withDB, DB.mkError]
          exact (h_bad h_success).elim
      | preload =>
          have h_bad : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .preload⟩).db.error? ≠ none := by
            simp [ParserState.finishProof, ParserState.withAt, ParserState.mkError, ParserState.withDB, DB.mkError]
          exact (h_bad h_success).elim
      | normal =>
          let inner : Unit → ParserState := fun _ => Id.run do
            let s := { s with tokp := .start }
            unless stack.size == 1 do
              return s.mkError pos "more than one element on stack"
            unless stack[0]! == fmla do
              return s.mkError pos "theorem does not prove what it claims"
            s.withDB fun db => db.insert pos l (.assert fmla fr)
          have h_success_at : (ParserState.withAt l inner).db.error? = none := by
            simpa [ParserState.finishProof, inner] using h_success
          have h_inner := withAt_success_eq l inner h_success_at
          rcases h_inner with ⟨h_inner_ok, h_inner_eq⟩
          by_cases h_size : stack.size == 1
          · by_cases h_eq' : stack[0]! == fmla
            · have h_inner_db : (inner ()).db = s.db.insert pos l (.assert fmla fr) := by
                simp [inner, Id.run, h_size, h_eq', ParserState.withDB]
              have h_db_eq : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .normal⟩).db =
                  s.db.insert pos l (.assert fmla fr) := by
                calc
                  (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .normal⟩).db
                      = (ParserState.withAt l inner).db := by
                          simpa [ParserState.finishProof, inner]
                  _ = (inner ()).db := h_inner_eq
                  _ = s.db.insert pos l (.assert fmla fr) := h_inner_db
              have h_ok : (s.db.insert pos l (.assert fmla fr)).error? = none := by
                simpa [h_inner_db] using h_inner_ok
              exact ⟨h_db_eq, h_ok⟩
            · have h_bad : (inner ()).db.error? ≠ none := by
                simp [inner, h_size, h_eq', ParserState.mkError, ParserState.withDB, DB.mkError]
              exact (h_bad h_inner_ok).elim
          · have h_bad : (inner ()).db.error? ≠ none := by
              simp [inner, h_size, ParserState.mkError, ParserState.withDB, DB.mkError]
            exact (h_bad h_inner_ok).elim
      | compressed chr =>
          by_cases h_chr : chr = 0
          · subst h_chr
            let inner : Unit → ParserState := fun _ => Id.run do
              let s := { s with tokp := .start }
              unless stack.size == 1 do
                return s.mkError pos "more than one element on stack"
              unless stack[0]! == fmla do
                return s.mkError pos "theorem does not prove what it claims"
              s.withDB fun db => db.insert pos l (.assert fmla fr)
            have h_success_at : (ParserState.withAt l inner).db.error? = none := by
              simpa [ParserState.finishProof, inner] using h_success
            have h_inner := withAt_success_eq l inner h_success_at
            rcases h_inner with ⟨h_inner_ok, h_inner_eq⟩
            by_cases h_size : stack.size == 1
            · by_cases h_eq' : stack[0]! == fmla
              · have h_inner_db : (inner ()).db = s.db.insert pos l (.assert fmla fr) := by
                  simp [inner, Id.run, h_size, h_eq', ParserState.withDB]
                have h_db_eq : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .compressed 0⟩).db =
                      s.db.insert pos l (.assert fmla fr) := by
                  calc
                    (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .compressed 0⟩).db
                        = (ParserState.withAt l inner).db := by
                            simpa [ParserState.finishProof, inner]
                    _ = (inner ()).db := h_inner_eq
                    _ = s.db.insert pos l (.assert fmla fr) := h_inner_db
                have h_ok : (s.db.insert pos l (.assert fmla fr)).error? = none := by
                  simpa [h_inner_db] using h_inner_ok
                exact ⟨h_db_eq, h_ok⟩
              · have h_bad : (inner ()).db.error? ≠ none := by
                  simp [inner, h_size, h_eq', ParserState.mkError, ParserState.withDB, DB.mkError]
                exact (h_bad h_inner_ok).elim
            · have h_bad : (inner ()).db.error? ≠ none := by
                simp [inner, h_size, ParserState.mkError, ParserState.withDB, DB.mkError]
              exact (h_bad h_inner_ok).elim
          · -- chr ≠ 0 -> parse error
            have h_bad : (s.finishProof ⟨pos, l, fmla, fr, heap, stack, .compressed chr⟩).db.error? ≠ none := by
              simp [ParserState.finishProof, h_chr, ParserState.withAt, ParserState.mkError, ParserState.withDB, DB.mkError]
            exact (h_bad h_success).elim

/-- In `.proof` mode, successful `feedToken` preserves `WellScopedDBWithScopes`. -/
theorem feedToken_proof_maintains_scopedWithScopes
    (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState)
    (h_tokp : s.tokp = .proof pr)
    (h_wf : WellFormedDB s.db)
    (h_scoped : WellScopedDBWithScopes s.db)
    (h_ok : ScopesOk s.db)
    (h_no_err : s.db.error? = none)
    (h_tokp_inv : TokpInv s.db s.tokp)
    (h_success : (s.feedToken i tk).db.error? = none) :
    WellScopedDBWithScopes (s.feedToken i tk).db := by
  by_cases h_open : tk.eqArray "$(".toAscii
  · have h_db_eq : (s.feedToken i tk).db = s.db := by
      simp [ParserState.feedToken, h_tokp, h_open]
    simpa [h_db_eq] using h_scoped
  · cases pr with
    | mk pos l fmla fr heap stack ptp =>
        by_cases h_end : tk.eqArray "$.".toAscii
        · -- finishProof branch
          let s0 : ParserState := { s with tokp := default }
          have h_success_finish :
              (s0.finishProof ⟨pos, l, fmla, fr, heap, stack, ptp⟩).db.error? = none := by
            simpa [ParserState.feedToken, h_tokp, h_open, h_end, s0] using h_success
          -- Extract the proof invariants.
          have h_tokp' : TokpInv s.db (.proof ⟨pos, l, fmla, fr, heap, stack, ptp⟩) := by
            simpa [h_tokp] using h_tokp_inv
          rcases h_tokp' with ⟨_h_fmla_wf, h_frame_wf, h_frame_scoped, h_syms, h_decl⟩
          have h_finish := finishProof_success_insert s0 ⟨pos, l, fmla, fr, heap, stack, ptp⟩ h_success_finish
          rcases h_finish with ⟨h_db_eq_finish, h_insert_ok⟩
          have h_db_eq_finish' :
              (s0.finishProof ⟨pos, l, fmla, fr, heap, stack, ptp⟩).db =
                s.db.insert pos l (.assert fmla fr) := by
            simpa [s0] using h_db_eq_finish
          have h_insert_ok' : (s.db.insert pos l (.assert fmla fr)).error? = none := by
            simpa [s0] using h_insert_ok
          have h_fresh_db : s.db.find? l = none := by
            exact insert_success_nonvar_fresh s.db pos l (.assert fmla fr)
              h_no_err h_insert_ok' (by intro v h_eq; cases h_eq)
          have h_scoped_insert :
              WellScopedDBWithScopes (s.db.insert pos l (.assert fmla fr)) := by
            exact insertAssert_full_maintains_scopedWithScopes s.db pos l fmla fr
              h_wf h_scoped h_no_err h_fresh_db h_frame_wf h_frame_scoped h_syms h_decl h_insert_ok'
          have h_db_eq :
              (s.feedToken i tk).db = s.db.insert pos l (.assert fmla fr) := by
            simpa [ParserState.feedToken, h_tokp, h_open, h_end, s0] using h_db_eq_finish'
          simpa [h_db_eq] using h_scoped_insert
        · -- feedProof branch: on success, DB is unchanged.
          let s0 : ParserState := { s with tokp := default }
          have h_success_feed :
              (s0.feedProof tk ⟨pos, l, fmla, fr, heap, stack, ptp⟩).db.error? = none := by
            simpa [ParserState.feedToken, h_tokp, h_open, h_end, s0] using h_success
          have h_db_eq' : (s0.feedProof tk ⟨pos, l, fmla, fr, heap, stack, ptp⟩).db = s.db := by
            -- feedProof doesn't touch DB on success
            have h_db_eq := feedProof_success_db s0 tk ⟨pos, l, fmla, fr, heap, stack, ptp⟩ h_success_feed
            simpa [s0] using h_db_eq
          have h_db_eq : (s.feedToken i tk).db = s.db := by
            simpa [ParserState.feedToken, h_tokp, h_open, h_end, s0] using h_db_eq'
          simpa [h_db_eq] using h_scoped

end ParserOps
end Metamath
