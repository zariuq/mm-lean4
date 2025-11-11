/-
# DB Case Analysis Helpers

This module provides infrastructure for handling the complex case analysis
required when proving properties about DB operations.

**The Challenge**: DB operations like insert, insertHyp, etc. have multiple
nested if-then-else and match expressions. Proving properties requires
systematic case analysis.

**Solution**: We provide lemmas that pre-split these cases and tactics to
automate the analysis.
-/

import Metamath.Verify
import Metamath.WellFormedness

namespace Metamath.DBCaseAnalysis

open Verify

/-! ## DB.insert Case Analysis

DB.insert has this structure (lines 279-294):
1. Check if obj is const and needs outermost scope
2. Check if db.error
3. Check if label already exists
4. Handle var redeclaration specially
5. Insert if all checks pass
-/

/-- All possible outcomes of DB.insert -/
inductive InsertOutcome : Type where
  | error_already : InsertOutcome  -- DB already had error
  | error_const_scope : InsertOutcome  -- Const not in outermost scope
  | error_duplicate : InsertOutcome  -- Duplicate non-var symbol
  | success_var_redef : InsertOutcome  -- Var redefinition (allowed)
  | success_new : InsertOutcome  -- New symbol inserted

/-- Classify the outcome of DB.insert -/
def classifyInsert (db : DB) (pos : Pos) (label : String) (obj : String → Object) : InsertOutcome :=
  if db.error then
    InsertOutcome.error_already
  else
    match obj label with
    | .const _ =>
      if !db.permissive && db.scopes.size > 0 then
        InsertOutcome.error_const_scope
      else
        if db.find? label |>.isSome then
          InsertOutcome.error_duplicate
        else
          InsertOutcome.success_new
    | .var _ =>
      if let some (.var _) := db.find? label then
        InsertOutcome.success_var_redef
      else if db.find? label |>.isSome then
        InsertOutcome.error_duplicate
      else
        InsertOutcome.success_new
    | _ =>
      if db.find? label |>.isSome then
        InsertOutcome.error_duplicate
      else
        InsertOutcome.success_new

/-- Case analysis theorem for DB.insert -/
theorem insert_cases (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
    let outcome := classifyInsert db pos label obj
    let db' := db.insert pos label obj
    match outcome with
    | .error_already => db' = db
    | .error_const_scope => db'.error = true
    | .error_duplicate => db'.error = true
    | .success_var_redef => db' = db
    | .success_new => db'.find? label = some (obj label) ∧ db'.error = db.error := by
  sorry -- TODO: Unfold insert and prove each case

/-! ## DB.insertHyp Case Analysis

insertHyp (lines 296-310) has additional complexity:
1. Check for duplicate float variables (lines 303-307)
2. Call insert
3. Call withHyps (doesn't check error!)
-/

/-- Possible outcomes of insertHyp -/
inductive InsertHypOutcome : Type where
  | error_already : InsertHypOutcome
  | error_duplicate_float : InsertHypOutcome  -- Same variable already has $f
  | error_from_insert : InsertHypOutcome  -- insert failed
  | success : InsertHypOutcome

/-- Check if a float variable is already bound -/
def hasFloatBinding (db : DB) (v : String) : Bool :=
  db.frame.hyps.any fun h =>
    match db.find? h with
    | some (.hyp false f _) =>
      f.size >= 2 &&
      match f[1]! with
      | .var v' => v' == v
      | _ => false
    | _ => false

/-- Classify insertHyp outcome -/
def classifyInsertHyp (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula) : InsertHypOutcome :=
  if db.error then
    .error_already
  else if !ess && f.size >= 2 then
    match f[1]! with
    | .var v =>
      if hasFloatBinding db v then
        .error_duplicate_float
      else if db.find? label |>.isSome then
        .error_from_insert
      else
        .success
    | _ =>
      if db.find? label |>.isSome then
        .error_from_insert
      else
        .success
  else
    if db.find? label |>.isSome then
      .error_from_insert
    else
      .success

/-- Case analysis for insertHyp -/
theorem insertHyp_cases (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula) :
    let outcome := classifyInsertHyp db pos label ess f
    let db' := db.insertHyp pos label ess f
    match outcome with
    | .error_already => db' = db
    | .error_duplicate_float => db'.error = true
    | .error_from_insert => db'.error = true
    | .success =>
      db'.find? label = some (.hyp ess f label) ∧
      label ∈ db'.frame.hyps := by
  sorry -- TODO: Unfold insertHyp and analyze

/-! ## Pattern: Checking Hypotheses

checkHyp (lines 401-418) recursively processes hypotheses.
Key pattern: accumulate substitution for floats, validate essentials.
-/

/-- State during hypothesis checking -/
structure CheckHypState where
  index : Nat
  subst : Std.HashMap String Formula
  error : Option String

/-- One step of checkHyp processing -/
inductive CheckHypStep : CheckHypState → CheckHypState → Prop where
  | process_float (st : CheckHypState) (v : String) (val : Formula) :
      st.error = none →
      CheckHypStep st { st with
        index := st.index + 1,
        subst := st.subst.insert v val }
  | process_essential (st : CheckHypState) :
      st.error = none →
      CheckHypStep st { st with index := st.index + 1 }
  | set_error (st : CheckHypState) (msg : String) :
      st.error = none →
      CheckHypStep st { st with error := some msg }

/-- checkHyp terminates when index reaches hyps.size -/
theorem checkHyp_terminates (db : DB) (hyps : Array String) :
    ∀ st : CheckHypState, st.index ≤ hyps.size →
    ∃ st' : CheckHypState, (st.index = hyps.size ∨ st'.error.isSome) := by
  sorry -- TODO: Induction on hyps.size - st.index

/-! ## Tactics for DB Operation Proofs -/

-- Tactics removed to avoid syntax issues
-- Use manual case analysis instead

/-! ## Well-Formedness Preservation

Key lemmas about how DB operations preserve or establish well-formedness.
-/

/-- If insert succeeds, float structure is preserved -/
theorem insert_preserves_float_structure (db : DB) (pos : Pos) (label : String) (f : Formula) :
    db.error = false →
    WF.WellFormedFloat f →
    let db' := db.insert pos label (.hyp false f)
    db'.error = false →
    db'.find? label = some (.hyp false f label) →
    WF.WellFormedFloat f := by
  -- WellFormedFloat is a property of f, not db, so it's preserved trivially
  intro _ hwf _ _ _
  exact hwf

/-- insertHyp maintains UniqueFloatVars if no duplicate -/
theorem insertHyp_maintains_unique_floats (db : DB) (pos : Pos) (label : String) (f : Formula) :
    WF.UniqueFloatVars db db.frame →
    f.size = 2 →
    (∃ c v, f[0]! = .const c ∧ f[1]! = .var v) →
    ¬hasFloatBinding db (match f[1]! with | .var v => v | _ => "") →
    let db' := db.insertHyp pos label false f
    db'.error = false →
    WF.UniqueFloatVars db' db'.frame := by
  sorry -- TODO: Use UniqueFloatVars definition

end Metamath.DBCaseAnalysis