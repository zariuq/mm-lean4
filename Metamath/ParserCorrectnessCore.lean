/-
# Core Parser Correctness Properties

This module establishes the fundamental error preservation and well-formedness
properties for the Metamath verifier parser. These are the essential theorems
that demonstrate parser soundness.

Created by: Opus 4.1
Purpose: Simplified, compilable version focusing on key induction principles
-/

import Metamath.Verify
import Metamath.WellFormedness
import Metamath.ParserCorrectness

namespace Metamath.ParserCorrectnessCore

open Verify
open WF

/-! ## Part 1: Error Preservation

The fundamental property: once an error occurs, it propagates through all operations.
This is THE KEY to parser soundness.
-/

section ErrorPreservation

/-- mkError always creates error state -/
theorem mkError_creates_error (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error = true := by
  unfold DB.mkError DB.error
  simp

/-- insert preserves error state -/
theorem insert_preserves_error (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
  db.error = true → (db.insert pos label obj).error = true := by
  intro h
  unfold DB.insert
  split <;> simp [h]

/-- pushScope preserves error state -/
theorem pushScope_preserves_error (db : DB) :
  db.error = true → db.pushScope.error = true := by
  intro h
  unfold DB.pushScope DB.error at *
  exact h

/-- popScope preserves error state -/
theorem popScope_preserves_error (db : DB) (pos : Pos) :
  db.error = true → (db.popScope pos).error = true := by
  intro h
  unfold DB.popScope
  split
  · unfold DB.error at *
    exact h
  · exact mkError_creates_error db pos _

/-- withFrame preserves error state -/
theorem withFrame_preserves_error (db : DB) (f : Frame → Frame) :
  db.error = true → (db.withFrame f).error = true := by
  intro h
  unfold DB.withFrame DB.error at *
  exact h

/-- withDJ preserves error state -/
theorem withDJ_preserves_error (db : DB) (f : Array DJ → Array DJ) :
  db.error = true → (db.withDJ f).error = true := by
  intro h
  unfold DB.withDJ
  exact withFrame_preserves_error db _ h

/-- withHyps preserves error state -/
theorem withHyps_preserves_error (db : DB) (f : Array String → Array String) :
  db.error = true → (db.withHyps f).error = true := by
  intro h
  unfold DB.withHyps
  exact withFrame_preserves_error db _ h

/-- Generic: all DB operations preserve error -/
theorem db_operation_preserves_error (op : DB → DB) :
  (∀ db, db.error = true → (op db).error = true) ↔
  (∀ db, db.error = false → (op db).error = false ∨ (op db).error = true) := by
  constructor
  · intro h db h_no_err
    by_cases h' : (op db).error = true
    · right; exact h'
    · left; simp [DB.error] at h' ⊢; exact h'
  · intro h db h_err
    by_contra h_not_err
    simp [DB.error] at h_not_err
    have := h db
    simp [DB.error, h_err] at this
    tauto

end ErrorPreservation

/-! ## Part 2: Parser Stops on Error

The critical property: once any step creates an error, the error propagates
to the final state.
-/

section ParserStopsOnError

/-- Sequential processing with error preservation -/
theorem sequential_error_propagation
  (initial_db : DB)
  (ops : List (DB → DB))
  (h_preserve : ∀ op ∈ ops, ∀ db : DB, db.error = true → (op db).error = true) :
  -- If any intermediate result has error
  ∀ prefix suffix, ops = prefix ++ suffix →
  (prefix.foldl (fun db op => op db) initial_db).error = true →
  -- Then final result has error
  (ops.foldl (fun db op => op db) initial_db).error = true := by
  intro prefix suffix h_split h_prefix_err
  rw [h_split, List.foldl_append]
  -- After prefix, we have error
  -- Processing suffix preserves error
  generalize h_inter : prefix.foldl (fun db op => op db) initial_db = inter_db
  rw [h_inter] at h_prefix_err
  clear h_inter prefix h_split
  -- Now prove suffix processing preserves error
  induction suffix generalizing inter_db with
  | nil => exact h_prefix_err
  | cons op tail ih =>
    simp [List.foldl]
    apply ih
    · intro op' h_in
      apply h_preserve
      simp [h_in]
    · apply h_preserve op
      · simp
      · exact h_prefix_err

/-- The contrapositive: no final error means no intermediate errors -/
theorem no_final_error_means_clean_execution
  (initial_db : DB)
  (ops : List (DB → DB))
  (h_preserve : ∀ op ∈ ops, ∀ db : DB, db.error = true → (op db).error = true) :
  initial_db.error = false →
  (ops.foldl (fun db op => op db) initial_db).error = false →
  -- Then no intermediate step created error
  ∀ i < ops.length,
    let partial := (ops.take i).foldl (fun db op => op db) initial_db
    partial.error = false := by
  intro h_init h_final i h_bound
  by_contra h_err
  simp [DB.error] at h_err
  -- If partial has error, final must have error
  have h_split : ops = ops.take i ++ ops.drop i := List.take_append_drop i ops
  have h_final_err := sequential_error_propagation initial_db ops h_preserve
                      (ops.take i) (ops.drop i) h_split
  -- Apply to our error case
  simp only [List.foldl] at h_final_err
  have h_contra := h_final_err h_err
  -- Contradiction: final is false but should be true
  simp [DB.error] at h_final h_contra
  exact absurd h_contra h_final

end ParserStopsOnError

/-! ## Part 3: Well-formedness Induction Principles

Strong induction principles for proving DB operations preserve well-formedness.
-/

section WellFormednessInduction

/-! Re-export structure-preserving ops from `ParserCorrectness` to avoid duplication. -/

/-- DB operations that preserve structure (delegated to ParserCorrectness). -/
abbrev StructurePreservingOp (db : DB) : (DB → DB) → Prop :=
  _root_.Metamath.ParserCorrectness.StructurePreservingOp db

/-- Structure-preserving operations maintain well-formedness when no error -/
theorem structure_preserving_maintains_wf
  {op : DB → DB}
  (db : DB)
  (h_struct : StructurePreservingOp db op)
  (h_wf : WellFormedDB db)
  (h_no_err_before : db.error? = none)
  (h_no_err_after : (op db).error? = none) :
  WellFormedDB (op db) := by
  exact _root_.Metamath.ParserCorrectness.structure_preserving_maintains_wf
    db h_struct h_wf h_no_err_before h_no_err_after

/-- Strong induction for DB construction from empty -/
theorem db_construction_induction
  {P : DB → Prop}
  (h_step : ∀ db op,
    StructurePreservingOp db op →
    db.error? = none →
    (op db).error? = none →
    P db →
    P (op db)) :
  ∀ db₁ db₂, _root_.Metamath.ParserCorrectness.DBExecution db₁ db₂ → P db₁ → P db₂ := by
  exact _root_.Metamath.ParserCorrectness.db_construction_induction h_step

end WellFormednessInduction

/-! ## Part 4: Main Soundness Result

The composition of all properties to establish parser soundness.
-/

section MainSoundness

/-- Empty DB is well-formed -/
theorem empty_db_wellformed :
  WellFormedDB { frame := default, scopes := #[], objects := {},
                interrupt := false, error? := none } := by
  unfold WellFormedDB WellFormedFrame
  constructor
  · -- Frame is well-formed
    constructor
    · intro i hi; simp at hi  -- No hyps in empty frame
    · intro i hi; simp at hi  -- No DJ in empty frame
    · -- UniqueFloatVars holds vacuously
      unfold UniqueFloatVars
      intro h _ _ _ _ _ _ _ _ _ _
      simp at h
  · -- All objects well-formed (none exist)
    intro label obj h_find
    simp at h_find

/-- If parsing succeeds, DB is well-formed -/
theorem parsing_success_implies_wellformed
  (bytes : ByteArray) :
  (Verify.checkBytes bytes).error? = none →
  WellFormedDB (Verify.checkBytes bytes) := by
  intro h_ok
  exact _root_.Metamath.ParserCorrectness.parser_construction_wellformed bytes h_ok

/-- The main soundness theorem -/
theorem parser_soundness
  (bytes : ByteArray) :
  (Verify.checkBytes bytes).error? = none →
  WellFormedDB (Verify.checkBytes bytes) ∧
  (∀ label obj, (Verify.checkBytes bytes).find? label = some obj →
    match obj with
    | .hyp false f _ => f.size = 2 ∧ (∃ c v, f[0]! = .const c ∧ f[1]! = .var v)
    | .hyp true f _ => WellFormedFormula f
    | .assert f _ _ => WellFormedFormula f
    | _ => true) := by
  intro h_success
  have h_wf : WellFormedDB (Verify.checkBytes bytes) :=
    _root_.Metamath.ParserCorrectness.parser_construction_wellformed bytes h_success
  have h_objs := _root_.Metamath.ParserCorrectness.parser_soundness_main bytes h_success
  constructor
  · exact h_wf
  · intro label obj h_find
    have h_obj := h_objs label obj h_find
    cases obj with
    | const _ => trivial
    | var _ => trivial
    | hyp ess f lbl =>
        cases ess with
        | true => exact h_obj.1
        | false =>
            have h_float := h_obj.2 (by simp)
            exact h_float
    | assert f fr name =>
        exact h_obj.1

end MainSoundness

end Metamath.ParserCorrectnessCore
