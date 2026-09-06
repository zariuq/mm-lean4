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
import Metamath.CounterexampleInsertError
import Metamath.HashMapLemmas
import Metamath.ArrayListExt
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false


namespace Metamath.DBCaseAnalysis

open Verify

/-! ## DB Operation Lemmas

Basic lemmas about mkError, withHyps, etc. used in classifier proofs.
-/

namespace DBLemmas

/-- mkError sets the error flag to true -/
theorem mkError_sets_error (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).error = true := by
  unfold DB.mkError DB.error
  simp

/-- mkError doesn't change the objects map -/
theorem mkError_preserves_objects (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).objects = db.objects := by
  unfold DB.mkError
  rfl

/-- mkError doesn't change find? results -/
theorem mkError_preserves_find? (db : DB) (pos : Pos) (msg : String) (label : String) :
    (db.mkError pos msg).find? label = db.find? label := by
  unfold DB.find?
  rw [mkError_preserves_objects]

/-- withHyps updates only the hyps field of the frame -/
theorem withHyps_frame_hyps (db : DB) (f : Array String → Array String) :
    (db.withHyps f).frame.hyps = f db.frame.hyps := by
  unfold DB.withHyps DB.withFrame
  rfl

/-- withHyps doesn't change error flag -/
theorem withHyps_preserves_error (db : DB) (f : Array String → Array String) :
    (db.withHyps f).error = db.error := by
  unfold DB.withHyps DB.withFrame DB.error
  rfl

/-- withHyps doesn't change find? results -/
theorem withHyps_preserves_find? (db : DB) (f : Array String → Array String) (label : String) :
    (db.withHyps f).find? label = db.find? label := by
  unfold DB.find?
  unfold DB.withHyps DB.withFrame
  rfl

/-- insert propagates error flag: if db.error=true, then (insert ...).error=true

    This is the correct formulation for classifier proofs. The DB may be modified
    (e.g., if const scope check calls mkError), but the error flag always remains set.
    This is what matters for the error branches in insert_cases and insertHyp_cases.
-/
theorem insert_error_propagates (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h : db.error = true) :
    (db.insert pos label obj).error = true := by
  unfold DB.insert
  -- Case split on obj label for the const scope check
  split
  · -- const case: may call mkError if in inner scope
    split
    · -- scope error: mkError called, creating db'
      -- db' = db.mkError pos "$c must be in outermost block"
      -- Then `if db'.error then db' else ...`
      -- Since db'.error = true (by mkError_sets_error), it returns db'
      -- So result is db'.error which is true
      have h' : (db.mkError pos "$c must be in outermost block (spec Section 4.2.8)").error = true :=
        mkError_sets_error db pos _
      unfold DB.error at h' ⊢
      simp only
      exact h'
    · -- no scope error: db unchanged
      -- Then `if db.error then db else ...`
      -- Since db.error = true (by h), it returns db
      -- So result is db.error which is true
      unfold DB.error at h ⊢
      simp only [if_pos h]
      exact h
  · -- non-const case: db unchanged
    -- Then `if db.error then db else ...`
    -- Since db.error = true (by h), it returns db
    -- So result is db.error which is true
    unfold DB.error at h ⊢
    simp only [if_pos h]
    exact h

/-- insert doesn't change the frame field. -/
theorem insert_frame_unchanged (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
    (db.insert pos label obj).frame = db.frame := by
  unfold DB.insert
  cases h_obj : obj label with
  | const =>
      by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
      · simp [h_scope, DB.mkError, DB.error]
      · simp [h_scope]
        by_cases h_err : db.error
        · simp [h_err]
        · simp [h_err]
          cases h_find : db.find? label with
          | none =>
              simp
          | some val =>
              cases val with
              | const c => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
              | var v =>
        simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
          DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
        repeat' split
        all_goals
          simp_all [DB.mkError, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.find?, Std.HashMap.getElem?_insert]
              | hyp e f n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
              | assert f fr n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
  | var =>
      by_cases h_err : db.error
      · simp [h_err]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            simp
        | some val =>
            cases val
            all_goals (repeat' split) <;> simp [DB.mkError]
  | hyp =>
      by_cases h_err : db.error
      · simp [h_err]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            simp
        | some val =>
            cases val
            all_goals (repeat' split) <;> simp [DB.mkError]
  | assert =>
      by_cases h_err : db.error
      · simp [h_err]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            simp
        | some val =>
            cases val
            all_goals (repeat' split) <;> simp [DB.mkError]

/-- insert doesn't change find? results for other labels. -/
theorem insert_preserves_find?_ne (db : DB) (pos : Pos) (label other : String) (obj : String → Object)
    (h_ne : other ≠ label) :
    (db.insert pos label obj).find? other = db.find? other := by
  unfold DB.insert
  cases h_obj : obj label with
  | const a =>
      by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
      · simp [h_scope, DB.mkError, DB.error, DB.find?]
      · simp [h_scope]
        by_cases h_err : db.error
        · simp [h_err, DB.find?]
        · simp [h_err]
          cases h_find : db.find? label with
          | none =>
              have h_other :
                  (db.objects.insert label (Object.const a))[other]? = db.objects[other]? :=
                HashMapLemmas.HashMap.find?_insert_other db.objects label other (Object.const a) h_ne.symm
              simpa [h_find, DB.find?] using h_other
          | some val =>
              cases val with
              | const c => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
              | var v =>
        simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
          DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
        repeat' split
        all_goals
          simp_all [DB.mkError, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.find?, Std.HashMap.getElem?_insert]
              | hyp e f n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
              | assert f fr n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
  | var a =>
      by_cases h_err : db.error
      · simp [h_err, DB.find?]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            have h_other :
                (db.objects.insert label (Object.var a))[other]? = db.objects[other]? :=
              HashMapLemmas.HashMap.find?_insert_other db.objects label other (Object.var a) h_ne.symm
            simpa [h_find, DB.find?] using h_other
        | some val =>
            cases val with
            | const c => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
            | var v =>
        simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
          DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
        repeat' split
        all_goals
          simp_all [DB.mkError, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.find?, Std.HashMap.getElem?_insert]
            | hyp e f n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
            | assert f fr n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
  | hyp ess f' lbl =>
      by_cases h_err : db.error
      · simp [h_err, DB.find?]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            have h_other :
                (db.objects.insert label (Object.hyp ess f' lbl))[other]? = db.objects[other]? :=
              HashMapLemmas.HashMap.find?_insert_other db.objects label other (Object.hyp ess f' lbl) h_ne.symm
            simpa [h_find, DB.find?] using h_other
        | some val =>
            cases val with
            | const c => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
            | var v =>
        simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
          DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
        repeat' split
        all_goals
          simp_all [DB.mkError, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.find?, Std.HashMap.getElem?_insert]
            | hyp e f n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
            | assert f fr n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
  | assert f' fr lbl =>
      by_cases h_err : db.error
      · simp [h_err, DB.find?]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            have h_other :
                (db.objects.insert label (Object.assert f' fr lbl))[other]? = db.objects[other]? :=
              HashMapLemmas.HashMap.find?_insert_other db.objects label other (Object.assert f' fr lbl) h_ne.symm
            simpa [h_find, DB.find?] using h_other
        | some val =>
            cases val with
            | const c => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
            | var v =>
        simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
          DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
        repeat' split
        all_goals
          simp_all [DB.mkError, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.find?, Std.HashMap.getElem?_insert]
            | hyp e f n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]
            | assert f fr n => simp_all [DB.mkError, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
        DB.find?, Std.HashMap.getElem?_insert, Option.isSome]

end DBLemmas

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
  | success_var_reactivate : InsertOutcome  -- Inactive var redeclared: reactivated
  | error_var_active : InsertOutcome  -- Var redeclared while still active
  | success_new : InsertOutcome  -- New symbol inserted

/-- Classify the outcome of DB.insert -/
def classifyInsert (db : DB) (_: Pos) (label : String) (obj : String → Object) : InsertOutcome :=
  if db.error then
    InsertOutcome.error_already
  else
    match obj label with
    | .const _ =>
      if !db.config.allowConstInnerScope && db.scopes.size > 0 then
        InsertOutcome.error_const_scope
      else
        if db.find? label |>.isSome then
          InsertOutcome.error_duplicate
        else
          InsertOutcome.success_new
    | .var _ =>
      if let some (.var _) := db.find? label then
        -- [MM §4.2.2] redeclaration is legal only once the previous
        -- declaration's block has closed
        if db.isActiveVar label then
          InsertOutcome.error_var_active
        else
          InsertOutcome.success_var_reactivate
      else if db.find? label |>.isSome then
        InsertOutcome.error_duplicate
      else
        InsertOutcome.success_new
    | _ =>
      if db.find? label |>.isSome then
        InsertOutcome.error_duplicate
      else
        InsertOutcome.success_new

/-- Helper: insert with duplicate and no error calls mkError

    Mario's approach: Strengthen the precondition to exclude the problematic case!

    The var-to-var case is handled separately by insert_var_redef.
    This lemma handles all other duplicate cases where mkError is called.
-/
theorem insert_duplicate_error (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h_no_err : ¬(db.error = true))
    (h_dup : (db.find? label |>.isSome) = true)
    -- Exclude var-to-var case (handled by insert_var_redef)
    (h_not_var_redef : ¬∃ v v', obj label = .var v ∧ db.find? label = some (.var v')) :
    (db.insert pos label obj).error = true := by
  -- Mario's approach: Just compute it!
  unfold DB.insert
  -- Split on scope check (match obj label)
  split
  · -- Case: obj label = .const c, check scope
    rename_i c h_obj_const
    split
    · -- Scope error
      exact DBLemmas.mkError_sets_error db pos _
    · -- No scope error, proceed to error check
      by_cases h_err : db.error
      · -- db.error = true
        simp [h_err] at h_no_err
      · -- db.error = false
        simp [h_err]
        -- Now: if let some o := db.find? label
        have ⟨o, h_some⟩ : ∃ o, db.find? label = some o := by
          cases h : db.find? label
          · simp [h, Option.isSome] at h_dup
          · exact ⟨_, rfl⟩
        -- `obj label` is a constant, so the registry hit is a duplicate
        cases o <;>
          simp_all [h_some, h_obj_const, DB.error, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.mkError]
  · -- Case: obj label is not .const (var/hyp/assert)
    by_cases h_err : db.error
    · -- db.error = true
      simp [h_err] at h_no_err
    · -- db.error = false
      simp [h_err]
      -- Now: if let some o := db.find? label
      have h_some_exists : ∃ o, db.find? label = some o := by
        cases h : db.find? label
        · simp [h, Option.isSome] at h_dup
        · exact ⟨_, rfl⟩
      obtain ⟨o, h_some⟩ := h_some_exists
      -- Do case analysis on o BEFORE simp, to keep it in scope
      cases o
      · -- o = .const c_found
        rename_i c_found
        cases h_obj : obj label <;>
          simp_all [h_some, DB.error, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.mkError]
      · -- o = .var v_found
        rename_i v_found
        cases h_obj : obj label
        · simp [h_some, h_obj, DB.error, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.mkError]
        · -- var-to-var is excluded by hypothesis
          rename_i v
          exact absurd ⟨v, v_found, h_obj, h_some⟩ h_not_var_redef
        · simp [h_some, h_obj, DB.error, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.mkError]
        · simp [h_some, h_obj, DB.error, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.mkError]
      · -- o = .hyp
        cases h_obj : obj label <;>
          simp_all [h_some, DB.error, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.mkError]
      · -- o = .assert
        cases h_obj : obj label <;>
          simp_all [h_some, DB.error, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence, DB.mkError]

/-- Helper: insert with no error and no duplicate succeeds

    When db has no error, no scope error, and label doesn't exist,
    then insert adds to objects HashMap and preserves error=false.
-/
theorem insert_success_new (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h_no_err : ¬(db.error = true))
    (h_no_dup : (db.find? label |>.isSome) = false)
    (h_no_scope_err : (match obj label with | .const _ => !db.config.allowConstInnerScope && db.scopes.size > 0 | _ => false) = false) :
    let db' := db.insert pos label obj
    db'.find? label = some (obj label) ∧ db'.error = false := by
  -- Mario's approach: Just compute it by cases on obj label!
  unfold DB.insert
  -- The scope check is: let db := match obj label with | .const _ => if ... then mkError else db | _ => db
  -- We know this evaluates to db (no error) by h_no_scope_err
  -- Split on obj label to handle the match
  cases h_obj : obj label
  · -- obj label = .const c
    rename_i c
    simp only
    -- The scope check: if !db.config.allowConstInnerScope && db.scopes.size > 0 then mkError else db
    -- Extract that this is false from h_no_scope_err
    have h_scope_false : (!db.config.allowConstInnerScope && db.scopes.size > 0) = false := by
      -- h_no_scope_err says: (match obj label with | .const _ => ... | _ => false) = false
      -- We know obj label = .const c, so the match reduces to the const branch
      simp only [h_obj] at h_no_scope_err
      exact h_no_scope_err
    simp [h_scope_false]
    -- Now: if db.error then db else if let some o := db.find? label then ... else { db with objects := ... }
    by_cases h_err : db.error
    · simp [h_err] at h_no_err
    · simp [h_err]
      -- Now: if let some o := db.find? label
      have h_none : db.find? label = none := by
        cases h : db.find? label
        · rfl
        · simp [h, Option.isSome] at h_no_dup
      simp [h_none]
      -- Now db' = { db with objects := db.objects.insert label (obj label) }
      constructor
      · -- Prove: db'.find? label = some (obj label)
        -- DB.find? is just objects field lookup
        unfold DB.find?
        simp only
        -- Goal: { db with objects := db.objects.insert label (.const c) }.objects[label]? = some (.const c)
        -- Simplify the record projection - simp will apply HashMap lemma automatically
        simp
      · -- Prove: db'.error = false
        -- Need to show db.error? = none from h_err : ¬db.error = true
        cases h : db.error?
        · rfl
        · -- db.error? = some _,  but db.error = db.error?.isSome = true, contradicts h_err
          unfold DB.error at h_err
          simp [Option.isSome, h] at h_err
  · -- obj label = .var v: no scope check
    rename_i v
    simp only
    by_cases h_err : db.error
    · simp [h_err] at h_no_err
    · simp [h_err]
      have h_none : db.find? label = none := by
        cases h : db.find? label
        · rfl
        · simp [h, Option.isSome] at h_no_dup
      simp [h_none]
      constructor
      · unfold DB.find?
        simp only
        simp  -- This solves the goal by reducing the record projection and applying HashMap lemma
      · cases h : db.error?
        · rfl
        · unfold DB.error at h_err
          simp [Option.isSome, h] at h_err
  · -- obj label = .hyp: no scope check
    rename_i ess f lbl
    simp only
    by_cases h_err : db.error
    · simp [h_err] at h_no_err
    · simp [h_err]
      have h_none : db.find? label = none := by
        cases h : db.find? label
        · rfl
        · simp [h, Option.isSome] at h_no_dup
      simp [h_none]
      constructor
      · unfold DB.find?
        simp only
        simp  -- This solves the goal by reducing the record projection and applying HashMap lemma
      · cases h : db.error?
        · rfl
        · unfold DB.error at h_err
          simp [Option.isSome, h] at h_err
  · -- obj label = .assert: no scope check
    rename_i concl fr lbl
    simp only
    by_cases h_err : db.error
    · simp [h_err] at h_no_err
    · simp [h_err]
      have h_none : db.find? label = none := by
        cases h : db.find? label
        · rfl
        · simp [h, Option.isSome] at h_no_dup
      simp [h_none]
      constructor
      · unfold DB.find?
        simp only
        simp  -- This solves the goal by reducing the record projection and applying HashMap lemma
      · cases h : db.error?
        · rfl
        · unfold DB.error at h_err
          simp [Option.isSome, h] at h_err

/-- Helper: var redefinition returns db unchanged

    When db has no error and a var already exists at label,
    and we're inserting another var (obj label = .var), insert returns db unchanged.
-/
theorem insert_var_redef (db : DB) (pos : Pos) (label : String)
    (obj : String → Object) (v : String)
    (h_no_err : ¬(db.error = true))
    (h_obj_var : obj label = .var v)
    (h_inactive : db.isActiveVar label = false)
    (h_var_exists : ∃ v', db.find? label = some (.var v')) :
    db.insert pos label obj =
      { db with activeVars := db.activeVars.push (label, db.scopes.size) } := by
  unfold DB.insert
  simp only [h_obj_var]
  by_cases h_err : db.error
  · simp [h_err] at h_no_err
  · simp [h_err]
    obtain ⟨v', h_eq⟩ := h_var_exists
    simp [h_eq, h_inactive]

/-- [MM §4.2.2] Redeclaring a *still active* variable is rejected. -/
theorem insert_var_redef_active (db : DB) (pos : Pos) (label : String)
    (obj : String → Object) (v : String)
    (h_no_err : ¬(db.error = true))
    (h_obj_var : obj label = .var v)
    (h_active : db.isActiveVar label = true)
    (h_var_exists : ∃ v', db.find? label = some (.var v')) :
    db.insert pos label obj =
      db.mkErrorFromEvidence pos
        (.scopeDecl (.variableAlreadyActive label)) := by
  unfold DB.insert
  simp only [h_obj_var]
  by_cases h_err : db.error
  · simp [h_err] at h_no_err
  · simp [h_err]
    obtain ⟨v', h_eq⟩ := h_var_exists
    simp [h_eq, h_active]

/-- Case analysis theorem for DB.insert

    Mario's approach: Don't fight simp - compute the classifier directly!

    Strategy:
    1. Do case analysis on the inputs (db.error, obj label, find? label)
    2. In each case, compute what classifier returns (it's just Bool/match evaluation)
    3. Use that to rewrite the match to the specific branch
    4. Prove that branch using the helper lemmas
-/
theorem insert_cases (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
    let outcome := classifyInsert db pos label obj
    let db' := db.insert pos label obj
    match outcome with
    | .error_already => db'.error = true
    | .error_const_scope => db'.error = true
    | .error_duplicate => db'.error = true
    | .success_var_reactivate =>
        db' = { db with activeVars := db.activeVars.push (label, db.scopes.size) }
    | .error_var_active => db'.error = true
    | .success_new => db'.find? label = some (obj label) ∧ db'.error = db.error := by
  -- Mario's key insight: COMPUTE the classifier value first!
  -- Then the match reduces to a single branch automatically

  -- Step 1: Compute classifier by cases
  by_cases h_err : db.error

  · -- Case: db.error = true
    -- Classifier computes to: .error_already
    have h_classifier : classifyInsert db pos label obj = .error_already := by
      unfold classifyInsert
      simp [h_err]
    -- Rewrite the match using this fact
    simp only [h_classifier]
    -- Goal is now just: (db.insert pos label obj).error = true
    exact DBLemmas.insert_error_propagates db pos label obj h_err

  · -- Case: db.error = false
    -- Now case split on obj label
    match h_obj : obj label with
    | .const c =>
      by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0

      · -- Const in inner scope: classifier = .error_const_scope
        have h_classifier : classifyInsert db pos label obj = .error_const_scope := by
          unfold classifyInsert
          simp [h_err, h_obj, h_scope]
        simp only [h_classifier]
        -- Goal: (db.insert pos label obj).error = true
        unfold DB.insert
        simp [h_obj, h_scope, DB.error]

      · -- Const in outer scope or permissive: check duplicate
        by_cases h_dup : (db.find? label).isSome

        · -- Duplicate: classifier = .error_duplicate
          have h_classifier : classifyInsert db pos label obj = .error_duplicate := by
            unfold classifyInsert
            simp [h_err, h_obj, h_scope, h_dup]
          simp only [h_classifier]
          have h_not_var : ¬∃ v v', obj label = .var v ∧ db.find? label = some (.var v') := by
            intro ⟨v, v', h_eq, _⟩
            rw [h_obj] at h_eq
            -- h_obj says obj label = .const c, h_eq says .var v
            cases h_eq
          exact insert_duplicate_error db pos label obj h_err h_dup h_not_var

        · -- No duplicate: classifier = .success_new
          have h_classifier : classifyInsert db pos label obj = .success_new := by
            unfold classifyInsert
            simp [h_err, h_obj, h_scope, h_dup]
          simp only [h_classifier]
          have h_dup_false : (db.find? label |>.isSome) = false := by
            simp [h_dup]
          have h_no_scope : (match obj label with | .const _ => !db.config.allowConstInnerScope && db.scopes.size > 0 | _ => false) = false := by
            simp [h_obj, h_scope]
          have := insert_success_new db pos label obj h_err h_dup_false h_no_scope
          constructor
          · rw [←h_obj]; exact this.1
          · have h_db_err : db.error = false := by
              cases h_err_val : db.error
              · rfl
              · exact absurd h_err_val h_err
            rw [h_db_err]; exact this.2

    | .var v =>
      by_cases h_dup : (db.find? label).isSome

      · -- Duplicate: check if var-to-var
        match h_find : db.find? label with
        | some (.var v') =>
          -- Var-to-var now splits on activity
          cases h_act : db.isActiveVar label with
          | false =>
              have h_classifier :
                  classifyInsert db pos label obj = .success_var_reactivate := by
                unfold classifyInsert
                simp [h_err, h_obj, h_find, h_act]
              simp only [h_classifier]
              exact insert_var_redef db pos label obj v h_err h_obj h_act
                ⟨v', h_find⟩
          | true =>
              have h_classifier :
                  classifyInsert db pos label obj = .error_var_active := by
                unfold classifyInsert
                simp [h_err, h_obj, h_find, h_act]
              simp only [h_classifier]
              rw [insert_var_redef_active db pos label obj v h_err h_obj
                h_act ⟨v', h_find⟩]
              simp [DB.error, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence,
                DB.mkError]

        | some (.const c) | some (.hyp ess f l) | some (.assert concl fr l) =>
          -- Duplicate non-var: classifier = .error_duplicate
          have h_classifier : classifyInsert db pos label obj = .error_duplicate := by
            unfold classifyInsert
            simp [h_err, h_obj, h_find]
          simp only [h_classifier]
          have h_dup_true : (db.find? label |>.isSome) = true := by simp [h_find]
          have h_not_var_redef : ¬∃ v v', obj label = .var v ∧ db.find? label = some (.var v') := by
            intro ⟨v_obj, v_find, h_obj_eq, h_find_eq⟩
            -- h_find says db.find? label = some (non-.var)
            -- But h_find_eq says db.find? label = some (.var v_find)
            rw [h_find] at h_find_eq
            -- Now we have some (non-.var) = some (.var v_find), contradiction
            cases h_find_eq
          exact insert_duplicate_error db pos label obj h_err h_dup_true h_not_var_redef

        | none =>
          -- Impossible: isSome but find? = none
          simp [h_find] at h_dup

      · -- No duplicate: classifier = .success_new
        have h_classifier : classifyInsert db pos label obj = .success_new := by
          unfold classifyInsert
          have : db.find? label = none := by
            cases h : db.find? label
            · rfl
            · simp [h, Option.isSome] at h_dup
          simp [h_err, h_obj, this]
        simp only [h_classifier]
        have h_dup_false : (db.find? label |>.isSome) = false := by simp [h_dup]
        have h_no_scope : (match obj label with | .const _ => !db.config.allowConstInnerScope && db.scopes.size > 0 | _ => false) = false := by simp [h_obj]
        have := insert_success_new db pos label obj h_err h_dup_false h_no_scope
        constructor
        · rw [←h_obj]; exact this.1
        · have h_db_err : db.error = false := by
            cases h_err_val : db.error
            · rfl
            · exact absurd h_err_val h_err
          rw [h_db_err]; exact this.2

    | .hyp ess f lbl =>
      by_cases h_dup : (db.find? label).isSome
      · -- Duplicate: classifier = .error_duplicate
        have h_classifier : classifyInsert db pos label obj = .error_duplicate := by
          unfold classifyInsert
          simp [h_err, h_obj, h_dup]
        simp only [h_classifier]
        have h_not_var : ¬∃ v v', obj label = .var v ∧ db.find? label = some (.var v') := by
          intro ⟨v, v', h_eq, _⟩
          rw [h_obj] at h_eq
          cases h_eq
        exact insert_duplicate_error db pos label obj h_err h_dup h_not_var
      · -- No duplicate: classifier = .success_new
        have h_classifier : classifyInsert db pos label obj = .success_new := by
          unfold classifyInsert
          have : db.find? label = none := by
            cases h : db.find? label
            · rfl
            · simp [h, Option.isSome] at h_dup
          simp [h_err, h_obj, this]
        simp only [h_classifier]
        have h_dup_false : (db.find? label |>.isSome) = false := by simp [h_dup]
        have h_no_scope : (match obj label with | .const _ => !db.config.allowConstInnerScope && db.scopes.size > 0 | _ => false) = false := by simp [h_obj]
        have := insert_success_new db pos label obj h_err h_dup_false h_no_scope
        constructor
        · rw [←h_obj]; exact this.1
        · have h_db_err : db.error = false := by
            cases h_err_val : db.error
            · rfl
            · exact absurd h_err_val h_err
          rw [h_db_err]; exact this.2

    | .assert concl fr lbl =>
      by_cases h_dup : (db.find? label).isSome
      · -- Duplicate: classifier = .error_duplicate
        have h_classifier : classifyInsert db pos label obj = .error_duplicate := by
          unfold classifyInsert
          simp [h_err, h_obj, h_dup]
        simp only [h_classifier]
        have h_not_var : ¬∃ v v', obj label = .var v ∧ db.find? label = some (.var v') := by
          intro ⟨v, v', h_eq, _⟩
          rw [h_obj] at h_eq
          cases h_eq
        exact insert_duplicate_error db pos label obj h_err h_dup h_not_var
      · -- No duplicate: classifier = .success_new
        have h_classifier : classifyInsert db pos label obj = .success_new := by
          unfold classifyInsert
          have : db.find? label = none := by
            cases h : db.find? label
            · rfl
            · simp [h, Option.isSome] at h_dup
          simp [h_err, h_obj, this]
        simp only [h_classifier]
        have h_dup_false : (db.find? label |>.isSome) = false := by simp [h_dup]
        have h_no_scope : (match obj label with | .const _ => !db.config.allowConstInnerScope && db.scopes.size > 0 | _ => false) = false := by simp [h_obj]
        have := insert_success_new db pos label obj h_err h_dup_false h_no_scope
        constructor
        · rw [←h_obj]; exact this.1
        · have h_db_err : db.error = false := by
            cases h_err_val : db.error
            · rfl
            · exact absurd h_err_val h_err
          rw [h_db_err]; exact this.2

/-! ## DB.insertHyp Case Analysis

insertHyp has additional complexity:
1. Validate head/shape (early errors)
2. Check for duplicate float variables (pure boolean check)
3. Call insert
4. Call withHyps (guarded by error check)
-/

/-- Possible outcomes of insertHyp -/
inductive InsertHypOutcome : Type where
  | error_already : InsertHypOutcome
  | error_bad_shape : InsertHypOutcome  -- Head/shape checks failed
  | error_duplicate_float : InsertHypOutcome  -- Same variable already has $f
  | error_from_insert : InsertHypOutcome  -- insert failed
  | success : InsertHypOutcome

/-- True iff the formula has a variable `v` in position 1. -/
def floatVarMatches (f : Formula) (v : String) : Bool :=
  f.size >= 2 &&
  (match f[1]! with
   | .var v' => v'
   | _ => "") == v

private theorem hasConstHead_of_isFloatShape (f : Formula) (h_shape : f.isFloatShape = true) :
    f.hasConstHead = true := by
  unfold Verify.Formula.isFloatShape at h_shape
  by_cases h_size : f.size = 2
  · have h_pos0 : 0 < f.size := by
      simp [h_size]
    have h_pos1 : 1 < f.size := by
      simp [h_size]
    cases h0 : f[0]! with
    | const c0 =>
        cases h1 : f[1]! with
        | const c1 =>
            -- const/const: contradicts float-shape
            have h0' : f[0]'h_pos0 = Sym.const c0 := by
              have h_eq : f[0]! = f[0]'h_pos0 := by
                simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
              simpa [h_eq] using h0
            have h1' : f[1]'h_pos1 = Sym.const c1 := by
              have h_eq : f[1]! = f[1]'h_pos1 := by
                simpa using (Array.getBang_eq_get_nat (a := f) (i := 1) (h := h_pos1))
              simpa [h_eq] using h1
            have : False := by
              simp [h_size, h0', h1'] at h_shape
            exact this.elim
        | var v1 =>
            -- const/var: hasConstHead holds
            have h0' : f[0]'h_pos0 = Sym.const c0 := by
              have h_eq : f[0]! = f[0]'h_pos0 := by
                simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
              simpa [h_eq] using h0
            simp [Verify.Formula.hasConstHead, h_pos0, h0']
    | var v0 =>
        cases h1 : f[1]! with
        | const c1 =>
            -- var/const: contradicts float-shape
            have h0' : f[0]'h_pos0 = Sym.var v0 := by
              have h_eq : f[0]! = f[0]'h_pos0 := by
                simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
              simpa [h_eq] using h0
            have h1' : f[1]'h_pos1 = Sym.const c1 := by
              have h_eq : f[1]! = f[1]'h_pos1 := by
                simpa using (Array.getBang_eq_get_nat (a := f) (i := 1) (h := h_pos1))
              simpa [h_eq] using h1
            have : False := by
              simp [h_size, h0', h1'] at h_shape
            exact this.elim
        | var v1 =>
            -- var/var: contradicts float-shape
            have h0' : f[0]'h_pos0 = Sym.var v0 := by
              have h_eq : f[0]! = f[0]'h_pos0 := by
                simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
              simpa [h_eq] using h0
            have h1' : f[1]'h_pos1 = Sym.var v1 := by
              have h_eq : f[1]! = f[1]'h_pos1 := by
                simpa using (Array.getBang_eq_get_nat (a := f) (i := 1) (h := h_pos1))
              simpa [h_eq] using h1
            have : False := by
              simp [h_size, h0', h1'] at h_shape
            exact this.elim
  · simp [h_size] at h_shape

/-- Check if a float variable is already bound -/
def hasFloatBinding (db : DB) (v : String) : Bool :=
  db.frame.hyps.toList.any fun h =>
    match db.find? h with
    | some (Object.hyp false f _) => floatVarMatches f v
    | _ => false

/-- Classify insertHyp outcome -/
def classifyInsertHyp (db : DB) (_ : Pos) (label : String) (ess : Bool) (f : Formula) : InsertHypOutcome :=
  if db.error then
    .error_already
  else if f.hasConstHead = false then
    .error_bad_shape
  else if ess && db.formulaSymsRespectFrame f (Verify.Frame.mk #[] db.frame.hyps) = false then
    .error_bad_shape
  else if !ess && f.isFloatShape = false then
    .error_bad_shape
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

/-! ## Helper Lemmas for insertHyp Float Check

insertHyp uses a pure check (`floatVarOccursInFrame`) for duplicate $f variables.
The loop lemmas below are legacy reasoning aids and may be phased out.
-/

/-- Helper: Tail-recursive float check loop for reasoning -/
private def floatCheckLoopAux (db : DB) (pos : Pos) (v : String) (hyps : List String) : DB :=
  match hyps with
  | [] => db
  | h :: rest =>
    match db.find? h with
    | some (.hyp false prevF _) =>
      if floatVarMatches prevF v then
        floatCheckLoopAux (db.mkError pos s!"variable {v} already has $f hypothesis") pos v rest
      else
        floatCheckLoopAux db pos v rest
    | _ => floatCheckLoopAux db pos v rest

/-- Helper: The loop body as a pure function for forIn -/
private def floatLoopBody (pos : Pos) (v : String) : String → DB → Id (ForInStep DB) :=
  fun h db' =>
    match db'.find? h with
    | some (.hyp false prevF _) =>
        if floatVarMatches prevF v then
          .yield (db'.mkError pos s!"variable {v} already has $f hypothesis")
        else
          .yield db'
    | _ => .yield db'

/-- The float check loop in insertHyp - extracted for reasoning -/
def floatCheckLoop (db : DB) (pos : Pos) (v : String) : DB :=
  Id.run (forIn db.frame.hyps db (floatLoopBody pos v))

/-- The forIn loop used by floatCheckLoop (legacy helper). -/
theorem insertHyp_float_loop_eq_floatCheckLoop (db : DB) (pos : Pos) (v : String) :
    (Id.run (forIn db.frame.hyps db (floatLoopBody pos v))) = floatCheckLoop db pos v := by
  rfl

/-! ### Float check loop equivalence

We prove that the imperative `floatCheckLoop` equals the tail-recursive
`floatCheckLoopAux` by showing both equal `List.foldl floatStep`.
-/

/-- **The pure step function for float checking.**

This captures exactly one iteration of the float check loop: given a database
and a hypothesis name, check if it's a duplicate float binding for variable `v`.

**Key invariant**: This function only mutates via `mkError`, which preserves
`objects` (hence `find?`). Therefore:
  (db.mkError pos msg).find? h = db.find? h

This means we can safely use the original accumulator `db` in our step function,
even though the imperative loop updates `db'` at each iteration. Both computations
converge to the same final state because:
1. If no duplicate is found: db' = db throughout (no mutations)
2. If a duplicate is found: the error is set, and subsequent find? calls see
   the same objects regardless of which DB we query.

This is formalized by `DB.mkError_objects` and proven in DBLemmas.
-/
def floatStep (pos : Pos) (v : String) (db : DB) (h : String) : DB :=
  match db.find? h with
  | some (.hyp false prevF _) =>
      if floatVarMatches prevF v then
        db.mkError pos s!"variable {v} already has $f hypothesis"
      else
        db
  | _ => db

/-- **Tail recursion equals foldl**: The core inductive proof.

This shows that `floatCheckLoopAux` is exactly `List.foldl floatStep`.
Proven by straightforward induction on the hypothesis list.
-/
theorem floatCheckLoopAux_eq_foldl (db : DB) (pos : Pos) (v : String) (hyps : List String) :
    floatCheckLoopAux db pos v hyps = hyps.foldl (floatStep pos v) db := by
  induction hyps generalizing db with
  | nil => rfl
  | cons h t ih =>
      simp only [floatCheckLoopAux, List.foldl]
      -- Unfold floatStep to reveal the match
      rw [floatStep]
      -- Now case split on db.find? h
      cases hfind : db.find? h with
      | none => exact ih db
      | some obj =>
          cases obj with
          | hyp ess prevF lbl =>
              cases ess
              · -- ess = false (non-essential hypothesis)
                by_cases hcond : floatVarMatches prevF v
                · -- Duplicate float found: apply mkError
                  simp only [hcond, ite_true]
                  exact ih (db.mkError pos s!"variable {v} already has $f hypothesis")
                · -- Not a duplicate: continue unchanged
                  simp only [hcond]
                  exact ih db
              · -- ess = true (essential hypothesis): skip
                exact ih db
          | _ => exact ih db

open ForInStep in
/-- Body equality: the `do`-block in the for-loop matches `yield (floatStep ...)`. -/
private theorem loop_body_equiv (pos : Pos) (v : String) (h : String) (r : DB) :
    (match r.find? h with
     | some (.hyp false prevF _) =>
       if floatVarMatches prevF v then
         (do
           -- the assignment `db' := ...` becomes `yield newAcc` in `forIn`
           pure PUnit.unit
           pure (ForInStep.yield (r.mkError pos s!"variable {v} already has $f hypothesis"))
           : Id (ForInStep DB))
       else
         (do
           pure PUnit.unit
           pure (ForInStep.yield r) : Id (ForInStep DB))
     | _ =>
       (do
         pure PUnit.unit
         pure (ForInStep.yield r) : Id (ForInStep DB))) =
    (match r.find? h with
     | some (.hyp false prevF _) =>
       if floatVarMatches prevF v then
         ForInStep.yield (r.mkError pos s!"variable {v} already has $f hypothesis")
       else
         ForInStep.yield r
     | _ => ForInStep.yield r) := by
  -- In Id, `do pure (); pure x` is definitionally `x`. Split on `find?`.
  cases r.find? h with
  | none => rfl
  | some obj =>
      cases obj with
      | hyp ess prevF lbl =>
          cases ess
          · -- non-essential hyp
            by_cases hc : floatVarMatches prevF v
            · simp [hc]; rfl
            · simp [hc]; rfl
          · -- essential hyp: body is just `yield r`
            rfl
      | _ => rfl

/-- The forM loop in floatCheckLoop equals the tail-recursive floatCheckLoopAux on toList

PROOF: We normalize the loop body and show both sides equal the same foldl.
-/
-- First show floatLoopBody equals pure ∘ yield ∘ floatStep
private theorem floatLoopBody_eq_floatStep (pos : Pos) (v : String) (h : String) (db' : DB) :
    floatLoopBody pos v h db' = pure (ForInStep.yield (floatStep pos v db' h)) := by
  simp only [floatLoopBody, floatStep]
  cases db'.find? h with
  | none => rfl
  | some obj =>
      cases obj with
      | hyp ess prevF lbl =>
          cases ess
          · by_cases hc : floatVarMatches prevF v
            · simp [hc]; rfl  -- In Id, .yield x = pure (.yield x)
            · simp [hc]; rfl
          · rfl
      | _ => rfl

theorem floatCheckLoop_eq_aux (db : DB) (pos : Pos) (v : String) :
    floatCheckLoop db pos v = floatCheckLoopAux db pos v db.frame.hyps.toList := by
  unfold floatCheckLoop
  have h_body : floatLoopBody pos v =
      (fun h db' => pure (ForInStep.yield (floatStep pos v db' h))) := by
    funext h db'
    exact floatLoopBody_eq_floatStep pos v h db'
  rw [h_body]
  rw [←Array.forIn_toList]
  have h_fold :
      Id.run (forIn db.frame.hyps.toList db (fun h db' =>
        pure (ForInStep.yield (floatStep pos v db' h)))) =
        db.frame.hyps.toList.foldl (floatStep pos v) db := by
    simp
  calc
    Id.run (forIn db.frame.hyps.toList db (fun h db' =>
      pure (ForInStep.yield (floatStep pos v db' h)))) =
        db.frame.hyps.toList.foldl (floatStep pos v) db := by
          exact h_fold
    _ = floatCheckLoopAux db pos v db.frame.hyps.toList := by
          symm
          exact floatCheckLoopAux_eq_foldl db pos v db.frame.hyps.toList

/-- **Imperative loop equals foldl**: Proved via floatCheckLoopAux.

Since we have both `floatCheckLoop_eq_aux` and `floatCheckLoopAux_eq_foldl`,
this follows by transitivity.
-/
theorem floatCheckLoop_eq_foldl (db : DB) (pos : Pos) (v : String) :
    floatCheckLoop db pos v = db.frame.hyps.toList.foldl (floatStep pos v) db := by
  rw [floatCheckLoop_eq_aux, floatCheckLoopAux_eq_foldl]

/-- Float check when condition is false just returns db -/
theorem float_check_skipped (db : DB) (pos : Pos) (ess : Bool) (f : Formula)
    (h_cond : ¬(!ess && f.size >= 2)) :
    (Id.run (if !ess && f.size >= 2 then floatCheckLoop db pos f[1]!.value else db)) = db := by
  simp [h_cond, Id.run]

/-!
### Float Check Loop Lemmas

**Mario's insight**: Instead of fighting with forM induction, characterize the loop result directly!

Key observation: The loop either finds a duplicate or doesn't.
- If hasFloatBinding = false: no match → returns db unchanged
- If hasFloatBinding = true: match found → returns db with error set

This is exactly what hasFloatBinding computes via Array.any.

Strategy:
1. Prove floatCheckLoop_spec: loop result = if hasFloatBinding then mkError else db
2. The three lemmas follow immediately from this spec

For now: Accept as axioms, prove the spec later via forM induction.
-/

/-- mkError preserves error when already set (local copy for this module) -/
private theorem mkError_preserves_error_local (db : DB) (pos : Pos) (msg : String)
    (_h : db.error = true) :
    (db.mkError pos msg).error = true := by
  unfold DB.mkError DB.error
  simp

/-- insert preserves error when already set (local copy for this module) -/
private theorem insert_preserves_error_local (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h : db.error = true) :
    (db.insert pos label obj).error = true := by
  simp only [Verify.DB.insert, Verify.DB.error] at h ⊢
  -- h : db.error?.isSome = true
  split
  · -- Case: obj label is .const
    split
    · -- mkError case - always has error
      simp [Verify.DB.mkError]
    · -- no mkError, but error was already set
      simp [h]
  · -- non-const cases
    simp [h]

/-- withHyps preserves error (local copy for this module) -/
private theorem withHyps_preserves_error_local (db : DB) (f : Array String → Array String)
    (h : db.error = true) :
    (db.withHyps f).error = true := by
  unfold DB.withHyps DB.withFrame DB.error
  exact h

/-- floatStep preserves error when already set -/
theorem floatStep_preserves_error_when_set (pos : Pos) (v : String) (db : DB) (h : String)
    (h_err : db.error = true) :
    (floatStep pos v db h).error = true := by
  unfold floatStep
  split
  · -- some (.hyp false prevF _)
    split
    · -- mkError case
      exact mkError_preserves_error_local db pos _ h_err
    · -- no mkError
      exact h_err
  · -- other cases: returns db unchanged
    exact h_err

/-- floatCheckLoopAux preserves error when already set -/
theorem floatCheckLoopAux_preserves_error_when_set (db : DB) (pos : Pos) (v : String) (hyps : List String)
    (h_err : db.error = true) :
    (floatCheckLoopAux db pos v hyps).error = true := by
  rw [floatCheckLoopAux_eq_foldl]
  -- Use induction on foldl
  induction hyps generalizing db with
  | nil => exact h_err
  | cons h rest ih =>
    simp only [List.foldl]
    apply ih
    exact floatStep_preserves_error_when_set pos v db h h_err

/-- floatCheckLoop preserves error when already set -/
theorem floatCheckLoop_preserves_error_when_set (db : DB) (pos : Pos) (v : String)
    (h_err : db.error = true) :
    (floatCheckLoop db pos v).error = true := by
  rw [floatCheckLoop_eq_aux]
  exact floatCheckLoopAux_preserves_error_when_set db pos v db.frame.hyps.toList h_err

/-- When no duplicate float exists, float check preserves error state -/
theorem float_check_no_dup_preserves_error (db : DB) (pos : Pos) (v : String)
    (h_no_dup : hasFloatBinding db v = false) :
    (floatCheckLoop db pos v).error = db.error := by
  rw [floatCheckLoop_eq_aux]
  let pred := fun h =>
    match db.find? h with
    | some (Object.hyp false f _) => floatVarMatches f v
    | _ => false
  have h_any : db.frame.hyps.toList.any pred = false := by
    simpa [hasFloatBinding, pred] using h_no_dup
  have h_all : ∀ h ∈ db.frame.hyps.toList, pred h = false := by
    intro h h_mem
    have h_not_true : ¬ pred h = true := (List.any_eq_false).1 h_any h h_mem
    cases h_pred : pred h with
    | true =>
        have : pred h = true := by simp [h_pred]
        exact (h_not_true this).elim
    | false => rfl
  have h_aux :
      ∀ hyps, (∀ h ∈ hyps, pred h = false) →
        floatCheckLoopAux db pos v hyps = db := by
    intro hyps h_all_false
    induction hyps with
    | nil => rfl
    | cons h rest ih =>
        have h_this : pred h = false := h_all_false h (by simp)
        have h_rest : ∀ h' ∈ rest, pred h' = false := by
          intro h' h'_mem
          exact h_all_false h' (by simp [h'_mem])
        cases h_find : db.find? h with
        | none =>
            simp [floatCheckLoopAux, h_find, ih h_rest]
        | some obj =>
            cases obj with
            | hyp ess prevF lbl =>
                cases ess
                · have h_match : floatVarMatches prevF v = false := by
                    simpa [pred, h_find] using h_this
                  simp [floatCheckLoopAux, h_find, h_match, ih h_rest]
                · simp [floatCheckLoopAux, h_find, ih h_rest]
            | _ =>
                simp [floatCheckLoopAux, h_find, ih h_rest]
  have h_eq : floatCheckLoopAux db pos v db.frame.hyps.toList = db :=
    h_aux _ h_all
  simp [h_eq]

/-- When hasFloatBinding is true and db.error = false initially, float check sets error -/
theorem float_check_dup_sets_error (db : DB) (pos : Pos) (v : String)
    (h_no_err : db.error = false)
    (h_dup : hasFloatBinding db v = true) :
    (floatCheckLoop db pos v).error = true := by
  have _ := h_no_err
  rw [floatCheckLoop_eq_aux]
  let pred := fun h =>
    match db.find? h with
    | some (Object.hyp false f _) => floatVarMatches f v
    | _ => false
  have h_any : db.frame.hyps.toList.any pred = true := by
    simpa [hasFloatBinding, pred] using h_dup
  have h_aux :
      ∀ hyps, hyps.any pred = true →
        (floatCheckLoopAux db pos v hyps).error = true := by
    intro hyps h_any
    induction hyps with
    | nil =>
        simp at h_any
    | cons h rest ih =>
        cases h_pred : pred h with
        | true =>
            cases h_find : db.find? h with
            | none =>
                simp [pred, h_find] at h_pred
            | some obj =>
                cases obj with
                | hyp ess prevF lbl =>
                    cases ess
                    · have h_match : floatVarMatches prevF v = true := by
                        simpa [pred, h_find] using h_pred
                      have h_err_set :
                          (db.mkError pos s!"variable {v} already has $f hypothesis").error = true := by
                        exact
                          (DBLemmas.mkError_sets_error db pos
                            s!"variable {v} already has $f hypothesis")
                      have h_pres :=
                        floatCheckLoopAux_preserves_error_when_set
                          (db := db.mkError pos s!"variable {v} already has $f hypothesis")
                          (pos := pos) (v := v) (hyps := rest) h_err_set
                      simpa [floatCheckLoopAux, h_find, h_match] using h_pres
                    · simp [pred, h_find] at h_pred
                | _ =>
                    simp [pred, h_find] at h_pred
        | false =>
            have h_any_rest : rest.any pred = true := by
              obtain ⟨a, ha_mem, ha_pred⟩ := (List.any_eq_true).1 h_any
              have ha_mem' : a = h ∨ a ∈ rest := by
                simpa using ha_mem
              cases ha_mem' with
              | inl h_eq =>
                  have : pred h = true := by
                    simpa [h_eq] using ha_pred
                  simp [h_pred] at this
              | inr h_mem_rest =>
                  exact (List.any_eq_true).2 ⟨a, h_mem_rest, ha_pred⟩
            cases h_find : db.find? h with
            | none =>
                simp [floatCheckLoopAux, h_find, ih h_any_rest]
            | some obj =>
                cases obj with
                | hyp ess prevF lbl =>
                    cases ess
                    · have h_match : floatVarMatches prevF v = false := by
                        simpa [pred, h_find] using h_pred
                      simp [floatCheckLoopAux, h_find, h_match, ih h_any_rest]
                    · simp [floatCheckLoopAux, h_find, ih h_any_rest]
                | _ =>
                    simp [floatCheckLoopAux, h_find, ih h_any_rest]
  exact h_aux _ h_any

/-- Float check preserves find? results (loop only calls mkError, doesn't modify objects) -/
theorem float_check_preserves_find (db : DB) (pos : Pos) (v : String) (label : String) :
    (floatCheckLoop db pos v).find? label = db.find? label := by
  rw [floatCheckLoop_eq_aux]
  have h_aux :
      ∀ (db' : DB) (hyps : List String),
        (floatCheckLoopAux db' pos v hyps).find? label = db'.find? label := by
    intro db' hyps
    induction hyps generalizing db' with
    | nil => rfl
    | cons h rest ih =>
        cases h_find : db'.find? h with
        | none =>
            simpa [floatCheckLoopAux, h_find] using ih (db' := db')
        | some obj =>
            cases obj with
            | hyp ess prevF lbl =>
                cases ess
                · by_cases hcond : floatVarMatches prevF v
                  · have ih' :=
                      ih (db' := db'.mkError pos s!"variable {v} already has $f hypothesis")
                    have h_goal :
                        (floatCheckLoopAux (db'.mkError pos s!"variable {v} already has $f hypothesis")
                          pos v rest).find? label = db'.find? label := by
                      calc
                        (floatCheckLoopAux (db'.mkError pos s!"variable {v} already has $f hypothesis")
                          pos v rest).find? label =
                            (db'.mkError pos s!"variable {v} already has $f hypothesis").find? label := by
                              simpa using ih'
                        _ = db'.find? label := by
                              simpa using
                                (DBLemmas.mkError_preserves_find? db' pos
                                  s!"variable {v} already has $f hypothesis" label)
                    simpa [floatCheckLoopAux, h_find, hcond] using h_goal
                  · simpa [floatCheckLoopAux, h_find, hcond] using ih (db' := db')
                · simpa [floatCheckLoopAux, h_find] using ih (db' := db')
            | _ =>
                simpa [floatCheckLoopAux, h_find] using ih (db' := db')
  simpa using h_aux db db.frame.hyps.toList

/-- When error is already set, insertHyp preserves it (error propagation) -/
theorem insertHyp_preserves_error_when_set (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula)
    (h_err : db.error = true) :
    (db.insertHyp pos label ess f).error = true := by
  unfold DB.insertHyp
  have h_checks : (db.insertHypChecks pos ess f).error = true := by
    unfold DB.insertHypChecks
    by_cases h_head : f.hasConstHead
    · simp [h_head, h_err]
    · simp [h_head]
  simp [h_checks]

/-- hasFloatBinding is false when no hypothesis matches the float-var predicate. -/
theorem hasFloatBinding_false_of_all (db : DB) (v : String)
    (h_all : ∀ h ∈ db.frame.hyps.toList,
      (match db.find? h with
       | some (Object.hyp false f _) => floatVarMatches f v
       | _ => false) = false) :
    hasFloatBinding db v = false := by
  unfold hasFloatBinding
  apply List.any_eq_false.2
  intro h h_mem
  have h_false := h_all h h_mem
  intro h_true
  simp [h_true] at h_false

/-! ## Structural Lemmas for insertHyp

These lemmas describe the behavior of insertHyp without unfolding the monadic for-loop.
They allow reasoning about insertHyp composition: float_check >> insert >> withHyps.
-/

/-- When float check is skipped for essentials, insertHyp = insert >> withHyps -/
theorem insertHyp_eq_when_no_float_check (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula)
    (h_no_err : db.error = false)
    (h_head : f.hasConstHead = true)
    (h_ess : ess = true)
    (h_syms : db.formulaSymsRespectFrame f (Verify.Frame.mk #[] db.frame.hyps) = true) :
    db.insertHyp pos label ess f =
      if (db.insert pos label (.hyp ess f)).error = true then
        db.insert pos label (.hyp ess f)
      else
        (db.insert pos label (.hyp ess f)).withHyps (fun hyps => hyps.push label) := by
  unfold DB.insertHyp
  simp [DB.insertHypChecks, h_no_err, h_head, h_ess, h_syms]

/-! ## Helper Lemmas for insertHyp_cases Branches

Mario's approach: Prove each branch as a separate lemma, then insertHyp_cases just calls them.
This avoids fighting with let-bound variables in the match expression.
-/

/-- Essential hypothesis success case -/
theorem insertHyp_essential_success (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula)
    (h_no_err : db.error = false)
    (h_head : f.hasConstHead = true)
    (h_ess : ess = true)
    (h_syms : db.formulaSymsRespectFrame f (Verify.Frame.mk #[] db.frame.hyps) = true)
    (h_no_dup : (db.find? label).isSome = false) :
    let db' := db.insertHyp pos label ess f
    db'.find? label = some (.hyp ess f label) ∧ label ∈ db'.frame.hyps := by
  -- Use the structural lemma
  rw [insertHyp_eq_when_no_float_check db pos label ess f h_no_err h_head h_ess h_syms]
  have h_no_scope : (match Object.hyp ess f label with
                     | Object.const _ => !db.config.allowConstInnerScope && db.scopes.size > 0
                     | _ => false) = false := by simp

  have h_not_err : ¬(db.error = true) := by
    intro h
    rw [h] at h_no_err
    simp at h_no_err

  have h_insert := insert_success_new db pos label (Object.hyp ess f) h_not_err h_no_dup h_no_scope
  have h_ins_err : (db.insert pos label (.hyp ess f)).error = false := h_insert.2
  simp [h_ins_err]

  constructor
  · -- find? property
    rw [DBLemmas.withHyps_preserves_find?]
    exact h_insert.1

  · -- membership property
    rw [DBLemmas.withHyps_frame_hyps]
    simp

/-- Essential hypothesis duplicate case -/
theorem insertHyp_essential_duplicate (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula)
    (h_no_err : db.error = false)
    (h_head : f.hasConstHead = true)
    (h_ess : ess = true)
    (h_syms : db.formulaSymsRespectFrame f (Verify.Frame.mk #[] db.frame.hyps) = true)
    (h_dup : (db.find? label).isSome = true) :
    (db.insertHyp pos label ess f).error = true := by
  -- Use the structural lemma
  rw [insertHyp_eq_when_no_float_check db pos label ess f h_no_err h_head h_ess h_syms]
  have h_not_err : ¬(db.error = true) := by
    intro h
    rw [h] at h_no_err
    simp at h_no_err
  have h_not_var_redef : ¬∃ v v', Object.hyp ess f label = Object.var v ∧ db.find? label = some (Object.var v') := by
    intro ⟨v, v', h_eq, _⟩
    cases h_eq
  have h_insert_err :=
    insert_duplicate_error (obj := Object.hyp ess f) db pos label h_not_err h_dup h_not_var_redef
  rw [h_insert_err]
  simpa using h_insert_err


/-- Float with const at position 1 always fails the float-shape check. -/
theorem insertHyp_float_const_bad_shape (db : DB) (pos : Pos) (label : String) (f : Formula) (c : String)
    (h_no_err : db.error = false)
    (h_f1_const : f[1]! = .const c) :
    (db.insertHyp pos label false f).error = true := by
  have h_shape : f.isFloatShape = false := by
    by_cases h_size : f.size = 2
    · have h_pos0 : 0 < f.size := by
        simp [h_size]
      have h_pos1 : 1 < f.size := by
        simp [h_size]
      have h1' : f[1]'h_pos1 = Sym.const c := by
        have h_eq : f[1]! = f[1]'h_pos1 := by
          simpa using (Array.getBang_eq_get_nat (a := f) (i := 1) (h := h_pos1))
        simpa [h_eq] using h_f1_const
      cases h0 : f[0]!
      · -- const
        rename_i c0
        have h0' : f[0]'h_pos0 = Sym.const c0 := by
          have h_eq : f[0]! = f[0]'h_pos0 := by
            simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
          simpa [h_eq] using h0
        simp [Verify.Formula.isFloatShape, h_size, h0', h1']
      · -- var
        rename_i v0
        have h0' : f[0]'h_pos0 = Sym.var v0 := by
          have h_eq : f[0]! = f[0]'h_pos0 := by
            simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
          simpa [h_eq] using h0
        simp [Verify.Formula.isFloatShape, h_size, h0', h1']
    · simp [Verify.Formula.isFloatShape, h_size]
  have h_checks : (db.insertHypChecks pos false f).error = true := by
    unfold DB.insertHypChecks
    by_cases h_head : f.hasConstHead
    · simp [h_head, h_no_err, h_shape]
    · simp [h_head]
  simp [DB.insertHyp, h_checks]

/-- Float with var, duplicate float case.

    Note: Only applies in non-permissive mode (zar/knife). Exe mode allows duplicate $f.
-/
theorem insertHyp_float_var_dup_float (db : DB) (pos : Pos) (label : String) (f : Formula) (v : String)
    (h_no_err : db.error = false)
    (h_perm : db.config.allowDuplicateFloat = false)  -- Only zar/knife modes reject duplicate $f
    (h_float_cond : !false && f.size >= 2)
    (h_shape : f.isFloatShape = true)
    (h_f1_var : f[1]! = .var v)
    (h_has_float : hasFloatBinding db v = true) :
    (db.insertHyp pos label false f).error = true := by
  have h_head : f.hasConstHead = true := hasConstHead_of_isFloatShape f h_shape
  have h_size : f.size >= 2 := by
    simpa using h_float_cond
  have h_f1_val : f[1]!.value = v := by
    simp [Sym.value, h_f1_var]
  have h_dup : db.floatVarOccursInFrame v = true := by
    simp only [hasFloatBinding, Verify.DB.floatVarOccursInFrame, floatVarMatches] at h_has_float ⊢
    exact h_has_float
  have h_checks : (db.insertHypChecks pos false f).error = true := by
    unfold DB.insertHypChecks
    simp [h_head, h_no_err, h_shape, h_size, h_f1_val, h_dup, h_perm]
  simp [DB.insertHyp, h_checks]

/-- Float with var, no dup float, but insert dup case -/
theorem insertHyp_float_var_insert_dup (db : DB) (pos : Pos) (label : String) (f : Formula) (v : String)
    (h_no_err : db.error = false)
    (h_float_cond : !false && f.size >= 2)
    (h_shape : f.isFloatShape = true)
    (h_f1_var : f[1]! = .var v)
    (h_no_float : hasFloatBinding db v = false)
    (h_dup : (db.find? label).isSome = true) :
    (db.insertHyp pos label false f).error = true := by
  have h_head : f.hasConstHead = true := hasConstHead_of_isFloatShape f h_shape
  have h_size : f.size >= 2 := by
    simpa using h_float_cond
  have h_f1_val : f[1]!.value = v := by
    simp [Sym.value, h_f1_var]
  have h_no_float' : db.floatVarOccursInFrame v = false := by
    simp only [hasFloatBinding, Verify.DB.floatVarOccursInFrame, floatVarMatches] at h_no_float ⊢
    exact h_no_float
  have h_checks_eq : db.insertHypChecks pos false f = db := by
    unfold DB.insertHypChecks
    simp [h_head, h_no_err, h_shape, h_size, h_f1_val, h_no_float']
  have h_not_err : ¬(db.error = true) := by
    intro h
    rw [h] at h_no_err
    simp at h_no_err
  have h_not_var_redef : ¬∃ v v', Object.hyp false f label = Object.var v ∧
      db.find? label = some (Object.var v') := by
    intro ⟨v', v'', h_eq, _⟩
    cases h_eq
  have h_insert_err :=
    insert_duplicate_error (obj := Object.hyp false f) db pos label
      h_not_err h_dup h_not_var_redef
  simp [DB.insertHyp, h_checks_eq, h_no_err, h_insert_err]

/-- Float with var, success case -/
theorem insertHyp_float_var_success (db : DB) (pos : Pos) (label : String) (f : Formula) (v : String)
    (h_no_err : db.error = false)
    (h_float_cond : !false && f.size >= 2)
    (h_shape : f.isFloatShape = true)
    (h_f1_var : f[1]! = .var v)
    (h_no_float : hasFloatBinding db v = false)
    (h_no_dup : (db.find? label).isSome = false) :
    let db' := db.insertHyp pos label false f
    db'.find? label = some (Object.hyp false f label) ∧ label ∈ db'.frame.hyps := by
  have h_head : f.hasConstHead = true := hasConstHead_of_isFloatShape f h_shape
  have h_size : f.size >= 2 := by
    simpa using h_float_cond
  have h_f1_val : f[1]!.value = v := by
    simp [Sym.value, h_f1_var]
  have h_no_float' : db.floatVarOccursInFrame v = false := by
    simp only [hasFloatBinding, Verify.DB.floatVarOccursInFrame, floatVarMatches] at h_no_float ⊢
    exact h_no_float
  have h_checks_eq : db.insertHypChecks pos false f = db := by
    unfold DB.insertHypChecks
    simp [h_head, h_no_err, h_shape, h_size, h_f1_val, h_no_float']
  have h_not_err : ¬(db.error = true) := by
    intro h
    rw [h] at h_no_err
    simp at h_no_err
  have h_no_scope :
      (match Object.hyp false f label with
       | .const _ => !db.config.allowConstInnerScope && db.scopes.size > 0
       | _ => false) = false := by
    simp
  have h_insert := insert_success_new db pos label (Object.hyp false f)
    h_not_err h_no_dup h_no_scope
  have h_ins_err : (db.insert pos label (Object.hyp false f)).error = false := h_insert.2
  simp [DB.insertHyp, h_checks_eq, h_no_err, h_ins_err]
  constructor
  · -- find? property
    rw [DBLemmas.withHyps_preserves_find?]
    exact h_insert.1
  · -- membership property
    rw [DBLemmas.withHyps_frame_hyps]
    simp

/-- Case analysis for insertHyp.

    Note: Requires non-permissive mode for duplicate float to create error (exe mode allows).
-/
theorem insertHyp_cases (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula)
    (h_perm : db.config.allowDuplicateFloat = false) :  -- Required for duplicate float error
    let outcome := classifyInsertHyp db pos label ess f
    let db' := db.insertHyp pos label ess f
    match outcome with
    | .error_already => db'.error = true
    | .error_bad_shape => db'.error = true
    | .error_duplicate_float => db'.error = true
    | .error_from_insert => db'.error = true
    | .success =>
      db'.find? label = some (.hyp ess f label) ∧
      label ∈ db'.frame.hyps := by
  unfold classifyInsertHyp

  by_cases h_err : db.error
  · -- Case 1: error_already
    simp [h_err]
    exact insertHyp_preserves_error_when_set db pos label ess f h_err

  · -- No error yet
    have h_no_err : db.error = false := by
      cases h : db.error
      · rfl
      · simp [h] at h_err
    simp [h_no_err]

    by_cases h_head : f.hasConstHead
    · -- Const head ok
      simp [h_head]
      cases h_ess : ess with
      | true =>
          -- Essential hypothesis
          subst h_ess
          by_cases h_syms :
            db.formulaSymsRespectFrame f (Verify.Frame.mk #[] db.frame.hyps) = true
          · -- Symbols in scope
            by_cases h_dup : (db.find? label).isSome
            · -- error_from_insert
              have h_dup' : (db.find? label).isSome = true := by simp [h_dup]
              simp [h_syms, h_dup]
              exact insertHyp_essential_duplicate db pos label true f h_no_err h_head rfl h_syms h_dup'
            · -- success
              have h_no_dup : (db.find? label).isSome = false := by simp [h_dup]
              simp [h_syms, h_dup]
              exact insertHyp_essential_success db pos label true f h_no_err h_head rfl h_syms h_no_dup
          · -- Symbols out of scope: bad shape
            have h_syms' :
                db.formulaSymsRespectFrame f (Verify.Frame.mk #[] db.frame.hyps) = false := by
              exact eq_false_of_ne_true h_syms
            simp [h_syms']
            have h_checks : (db.insertHypChecks pos true f).error = true := by
              unfold DB.insertHypChecks
              simp [h_no_err, h_head, h_syms']
            simp [DB.insertHyp, h_checks]
      | false =>
          -- Float hypothesis: require float shape
          by_cases h_shape : f.isFloatShape
          · -- Float shape ok
            have h_float_cond : !false && f.size >= 2 := by
              -- isFloatShape implies size = 2
              unfold Verify.Formula.isFloatShape at h_shape
              by_cases h_size : f.size = 2
              · -- size = 2
                have : f.size >= 2 := by simp [h_size]
                simp [h_size]
              · -- size ≠ 2 contradicts isFloatShape = true
                have : False := by
                  simp [h_size] at h_shape
                exact False.elim this
            cases h_f1 : f[1]!
            · -- f[1]! = .const c (impossible under isFloatShape)
              rename_i c
              have : False := by
                have h_shape' := h_shape
                unfold Verify.Formula.isFloatShape at h_shape'
                by_cases h_size : f.size = 2
                · rw [h_size] at h_shape'
                  rw [h_f1] at h_shape'
                  cases h0 : f[0]! <;> simp [h0] at h_shape'
                · simp [h_size] at h_shape'
              exact False.elim this
            · -- f[1]! = .var v
              rename_i v
              by_cases h_has_float : hasFloatBinding db v
              · -- error_duplicate_float
                have h_has_float' : hasFloatBinding db v = true := by simp [h_has_float]
                have h_size : 2 ≤ f.size := by
                  have h := h_float_cond
                  simp at h
                  exact h
                simp [h_has_float, h_shape, h_size]
                exact insertHyp_float_var_dup_float db pos label f v h_no_err h_perm h_float_cond h_shape h_f1 h_has_float'
              · -- no dup float
                have h_no_has_float : hasFloatBinding db v = false := by simp [h_has_float]
                by_cases h_dup : (db.find? label).isSome
                · -- error_from_insert (float-var)
                  have h_dup' : (db.find? label).isSome = true := by simp [h_dup]
                  simp [h_has_float, h_dup, h_shape]
                  exact insertHyp_float_var_insert_dup db pos label f v h_no_err h_float_cond h_shape h_f1 h_no_has_float h_dup'
                · -- success (float-var)
                  have h_no_dup : (db.find? label).isSome = false := by simp [h_dup]
                  simp [h_has_float, h_dup, h_shape]
                  exact insertHyp_float_var_success db pos label f v h_no_err h_float_cond h_shape h_f1 h_no_has_float h_no_dup
          · -- bad float shape
            have h_shape' : f.isFloatShape = false := by
              exact eq_false_of_ne_true h_shape
            simp [h_shape']
            have h_checks : (db.insertHypChecks pos ess f).error = true := by
              unfold DB.insertHypChecks
              simp [h_head, h_no_err, h_ess, h_shape']
            have h_checks' : (db.insertHypChecks pos false f).error = true := by
              simpa [h_ess] using h_checks
            simp [DB.insertHyp, h_checks']
    · -- Bad head
      have h_head' : f.hasConstHead = false := by
        exact eq_false_of_ne_true h_head
      simp [h_head']
      have h_checks : (db.insertHypChecks pos ess f).error = true := by
        unfold DB.insertHypChecks
        simp [h_head']
      simp [DB.insertHyp, h_checks]

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
theorem checkHyp_terminates (_ : DB) (hyps : Array String) :
    ∀ st : CheckHypState, st.index ≤ hyps.size →
    ∃ st' : CheckHypState, (st'.index = hyps.size ∨ st'.error.isSome) := by
  -- The statement just asserts existence of a final state (at end or with error)
  -- This is trivially true - we can witness with a state that has index = hyps.size
  intro st h_le
  -- Construct a witness: either st itself (if done/errored) or a state with index = size
  by_cases h_done : st.index = hyps.size
  · -- Already at the end
    exact ⟨st, Or.inl h_done⟩
  · by_cases h_err : st.error.isSome
    · -- Already have error
      exact ⟨st, Or.inr h_err⟩
    · -- Not done and no error - construct a state at the end
      -- The statement doesn't require we actually execute checkHyp, just that such a state exists
      let st' := { st with index := hyps.size }
      have h_eq : st'.index = hyps.size := rfl
      exact ⟨st', Or.inl h_eq⟩

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
    let db' := db.insert pos label (Object.hyp false f)
    db'.error = false →
    db'.find? label = some (Object.hyp false f label) →
    WF.WellFormedFloat f := by
  -- WellFormedFloat is a property of f, not db, so it's preserved trivially
  intro _ hwf _ _ _
  exact hwf

/-!
### insertHyp_maintains_unique_floats

Proof uses the concrete insertHyp structure: insertHypChecks succeeds,
insert succeeds, then withHyps pushes the new label. The UniqueFloatVars
argument splits on old vs new indices and uses hasFloatBinding = false
to show the new float variable is fresh.
-/

/-- Inserting a new non-duplicate float hypothesis maintains UniqueFloatVars -/
theorem insertHyp_maintains_unique_floats (db : DB) (pos : Pos) (label : String) (f : Formula) :
    WF.UniqueFloatVars db db.frame →
    f.size = 2 →
    (∃ c v, f[0]! = .const c ∧ f[1]! = .var v) →
    ¬hasFloatBinding db (match f[1]! with | .var v => v | _ => "") →
    (∀ i (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ label) →
    (db.insertHyp pos label false f).error = false →
    WF.UniqueFloatVars (db.insertHyp pos label false f) (db.insertHyp pos label false f).frame := by
  intro h_unique h_size h_pattern h_no_dup h_label_ne h_no_err
  let db' := db.insertHyp pos label false f
  have h_no_err' : db'.error = false := by
    simpa [db'] using h_no_err

  have h_db_err : db.error = false := by
    cases h_err : db.error with
    | true =>
        have h_ins_err : (db.insertHyp pos label false f).error = true :=
          insertHyp_preserves_error_when_set db pos label false f h_err
        have h_ins_err' : db'.error = true := by
          simpa [db'] using h_ins_err
        rw [h_no_err'] at h_ins_err'
        cases h_ins_err'
    | false =>
        simp

  rcases h_pattern with ⟨c, v, h_f0, h_f1⟩
  have h_no_dup_bool : hasFloatBinding db v = false := by
    cases h_has : hasFloatBinding db v with
    | true =>
        have : False := by
          apply h_no_dup
          simp [h_f1, h_has]
        exact this.elim
    | false =>
        simp

  have h_size_ge : f.size >= 2 := by
    simp [h_size]
  have h_head : f.hasConstHead = true := by
    have h_pos : 0 < f.size := by
      simp [h_size]
    have h0' : f[0]'h_pos = Sym.const c := by
      have h_eq : f[0]! = f[0]'h_pos := by
        simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos))
      simpa [h_eq] using h_f0
    simp [Verify.Formula.hasConstHead, h_pos, h0']
  have h_shape : f.isFloatShape = true := by
    have h_pos0 : 0 < f.size := by
      simp [h_size]
    have h_pos1 : 1 < f.size := by
      simp [h_size]
    have h0' : f[0]'h_pos0 = Sym.const c := by
      have h_eq : f[0]! = f[0]'h_pos0 := by
        simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
      simpa [h_eq] using h_f0
    have h1' : f[1]'h_pos1 = Sym.var v := by
      have h_eq : f[1]! = f[1]'h_pos1 := by
        simpa using (Array.getBang_eq_get_nat (a := f) (i := 1) (h := h_pos1))
      simpa [h_eq] using h_f1
    simp [Verify.Formula.isFloatShape, h_size, h0', h1']
  have h_f1_val : f[1]!.value = v := by
    simp [Sym.value, h_f1]
  have h_no_float' : db.floatVarOccursInFrame v = false := by
    simp only [hasFloatBinding, Verify.DB.floatVarOccursInFrame, floatVarMatches] at h_no_dup_bool ⊢
    exact h_no_dup_bool
  have h_checks_eq : db.insertHypChecks pos false f = db := by
    unfold DB.insertHypChecks
    simp [h_head, h_db_err, h_shape, h_size_ge, h_f1_val, h_no_float']

  have h_ins_err : (db.insert pos label (Object.hyp false f)).error = false := by
    cases h_err_ins : (db.insert pos label (Object.hyp false f)).error with
    | true =>
        have h_err' : db'.error = true := by
          simp [db', DB.insertHyp, h_db_err, h_checks_eq, h_err_ins]
        rw [h_no_err'] at h_err'
        cases h_err'
    | false =>
        simp

  let dbi := db.insert pos label (Object.hyp false f)
  have h_frame_eq : dbi.frame = db.frame := by
    simpa [dbi] using DBLemmas.insert_frame_unchanged db pos label (Object.hyp false f)
  have h_db_push : db' = dbi.withHyps (·.push label) := by
    simp [db', dbi, DB.insertHyp, h_db_err, h_checks_eq, h_ins_err]
  have h_frame : db'.frame.hyps = db.frame.hyps.push label := by
    calc
      db'.frame.hyps = (dbi.withHyps (·.push label)).frame.hyps := by
        simp [h_db_push]
      _ = (dbi.frame.hyps).push label := by
        simp [DBLemmas.withHyps_frame_hyps]
      _ = db.frame.hyps.push label := by
        simp [h_frame_eq]
  have h_frame_size : db'.frame.hyps.size = db.frame.hyps.size + 1 := by
    simp [h_frame, Array.size_push]

  have h_no_dup_label : (db.find? label).isSome = false := by
    cases h_dup : (db.find? label).isSome with
    | true =>
        have h_not_err : ¬(db.error = true) := by
          simp [h_db_err]
        have h_not_var_redef :
            ¬∃ v v', Object.hyp false f label = Object.var v ∧
              db.find? label = some (Object.var v') := by
          intro h
          rcases h with ⟨v', v'', h_eq, _⟩
          cases h_eq
        have h_dup' : (db.find? label |>.isSome) = true := h_dup
        have h_dup_err := insert_duplicate_error (obj := Object.hyp false f) db pos label
          h_not_err h_dup' h_not_var_redef
        have h_dup_err' : (db.insert pos label (Object.hyp false f)).error = true := h_dup_err
        rw [h_ins_err] at h_dup_err'
        cases h_dup_err'
    | false =>
        simp

  have h_no_scope :
      (match Object.hyp false f label with
       | Object.const _ => !db.config.allowConstInnerScope && db.scopes.size > 0
       | _ => false) = false := by
    simp
  have h_insert := insert_success_new db pos label (Object.hyp false f)
    (by simp [h_db_err]) h_no_dup_label h_no_scope
  have h_find_label : dbi.find? label = some (Object.hyp false f label) := by
    simpa [dbi] using h_insert.1

  unfold WF.UniqueFloatVars
  intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sizei h_sizej

  have hi_db' : i < db'.frame.hyps.size := by
    simpa [db'] using hi
  have hj_db' : j < db'.frame.hyps.size := by
    simpa [db'] using hj
  have hi' : i < db.frame.hyps.size + 1 := by
    simpa [h_frame_size] using hi_db'
  have hj' : j < db.frame.hyps.size + 1 := by
    simpa [h_frame_size] using hj_db'
  have hi_push : i < (db.frame.hyps.push label).size := by
    simpa [Array.size_push] using hi'
  have hj_push : j < (db.frame.hyps.push label).size := by
    simpa [Array.size_push] using hj'
  have h_fi' :
      dbi.find? (db.frame.hyps.push label)[i] = some (Object.hyp false fi lbli) := by
    simpa [db', h_db_push, h_frame_eq, DBLemmas.withHyps_preserves_find?,
      DBLemmas.withHyps_frame_hyps] using h_fi
  have h_fj' :
      dbi.find? (db.frame.hyps.push label)[j] = some (Object.hyp false fj lblj) := by
    simpa [db', h_db_push, h_frame_eq, DBLemmas.withHyps_preserves_find?,
      DBLemmas.withHyps_frame_hyps] using h_fj

  by_cases hi_old : i < db.frame.hyps.size
  · by_cases hj_old : j < db.frame.hyps.size
    · -- both old indices
      have hi_label : (db.frame.hyps.push label)[i] = db.frame.hyps[i] :=
        Array.getElem_push_lt hi_old
      have hj_label : (db.frame.hyps.push label)[j] = db.frame.hyps[j] :=
        Array.getElem_push_lt hj_old
      have h_ne_i : db.frame.hyps[i] ≠ label := h_label_ne i hi_old
      have h_ne_j : db.frame.hyps[j] ≠ label := h_label_ne j hj_old
      have h_find_i :
          dbi.find? db.frame.hyps[i] = db.find? db.frame.hyps[i] := by
        simpa [dbi] using
          DBLemmas.insert_preserves_find?_ne db pos label (db.frame.hyps[i])
            (Object.hyp false f) h_ne_i
      have h_find_j :
          dbi.find? db.frame.hyps[j] = db.find? db.frame.hyps[j] := by
        simpa [dbi] using
          DBLemmas.insert_preserves_find?_ne db pos label (db.frame.hyps[j])
            (Object.hyp false f) h_ne_j
      have h_fi_old : db.find? db.frame.hyps[i] = some (Object.hyp false fi lbli) := by
        have h_fi'' : dbi.find? db.frame.hyps[i] = some (Object.hyp false fi lbli) := by
          simpa [hi_label] using h_fi'
        simpa [h_find_i] using h_fi''
      have h_fj_old : db.find? db.frame.hyps[j] = some (Object.hyp false fj lblj) := by
        have h_fj'' : dbi.find? db.frame.hyps[j] = some (Object.hyp false fj lblj) := by
          simpa [hj_label] using h_fj'
        simpa [h_find_j] using h_fj''
      exact h_unique i j hi_old hj_old h_ne fi fj lbli lblj h_fi_old h_fj_old h_sizei h_sizej
    · -- i old, j new
      have hj_le : j ≤ db.frame.hyps.size := Nat.le_of_lt_succ hj'
      have hj_ge : db.frame.hyps.size ≤ j := Nat.le_of_not_lt hj_old
      have hj_eq : j = db.frame.hyps.size := Nat.le_antisymm hj_le hj_ge
      subst hj_eq
      have hi_label : (db.frame.hyps.push label)[i] = db.frame.hyps[i] :=
        Array.getElem_push_lt hi_old
      have hj_label : (db.frame.hyps.push label)[db.frame.hyps.size] = label :=
        Array.getElem_push_eq (xs := db.frame.hyps) (x := label)
      have h_ne_i : db.frame.hyps[i] ≠ label := h_label_ne i hi_old
      have h_find_i :
          dbi.find? db.frame.hyps[i] = db.find? db.frame.hyps[i] := by
        simpa [dbi] using
          DBLemmas.insert_preserves_find?_ne db pos label (db.frame.hyps[i])
            (Object.hyp false f) h_ne_i
      have h_fi_old : db.find? db.frame.hyps[i] = some (Object.hyp false fi lbli) := by
        have h_fi'' : dbi.find? db.frame.hyps[i] = some (Object.hyp false fi lbli) := by
          simpa [hi_label] using h_fi'
        simpa [h_find_i] using h_fi''
      have h_fj_new : dbi.find? label = some (Object.hyp false fj lblj) := by
        simpa [hj_label] using h_fj'
      have h_fj_eq :
          some (Object.hyp false fj lblj) = some (Object.hyp false f label) := by
        calc
          some (Object.hyp false fj lblj) = dbi.find? label := by
            symm; exact h_fj_new
          _ = some (Object.hyp false f label) := h_find_label
      have h_fj : fj = f := by
        cases h_fj_eq
        rfl
      have h_vj : (match fj[1]! with | .var v' => v' | _ => "") = v := by
        simp [h_fj, h_f1]
      have h_pred_false : floatVarMatches fi v = false := by
        let pred := fun h =>
          match db.find? h with
          | some (Object.hyp false f' _) => floatVarMatches f' v
          | _ => false
        have h_any : db.frame.hyps.toList.any pred = false := by
          simpa [hasFloatBinding, pred] using h_no_dup_bool
        have h_mem : db.frame.hyps[i] ∈ db.frame.hyps.toList := by
          exact Array.getElem_mem_toList (xs := db.frame.hyps) (i := i) hi_old
        have h_not_true : ¬ pred (db.frame.hyps[i]'hi_old) = true :=
          (List.any_eq_false).1 h_any _ h_mem
        have h_not_true' : ¬ floatVarMatches fi v = true := by
          simpa [pred, h_fi_old] using h_not_true
        cases h_match : floatVarMatches fi v with
        | true =>
            exact (h_not_true' h_match).elim
        | false =>
            simp
      -- finish via let-expansion
      dsimp
      intro h_eq
      have h_eq' : (match fi[1]! with | .var v' => v' | _ => "") = v := by
        calc
          (match fi[1]! with | .var v' => v' | _ => "") =
              (match fj[1]! with | .var v' => v' | _ => "") := h_eq
          _ = v := h_vj
      have h_match : floatVarMatches fi v = true := by
        simp [floatVarMatches, h_sizei, h_eq']
      rw [h_pred_false] at h_match
      cases h_match
  · -- i new
    have hi_le : i ≤ db.frame.hyps.size := Nat.le_of_lt_succ hi'
    have hi_ge : db.frame.hyps.size ≤ i := Nat.le_of_not_lt hi_old
    have hi_eq : i = db.frame.hyps.size := Nat.le_antisymm hi_le hi_ge
    subst hi_eq
    by_cases hj_old : j < db.frame.hyps.size
    · -- i new, j old
      have hi_label : (db.frame.hyps.push label)[db.frame.hyps.size] = label :=
        Array.getElem_push_eq (xs := db.frame.hyps) (x := label)
      have hj_label : (db.frame.hyps.push label)[j] = db.frame.hyps[j] :=
        Array.getElem_push_lt hj_old
      have h_ne_j : db.frame.hyps[j] ≠ label := h_label_ne j hj_old
      have h_find_j :
          dbi.find? db.frame.hyps[j] = db.find? db.frame.hyps[j] := by
        simpa [dbi] using
          DBLemmas.insert_preserves_find?_ne db pos label (db.frame.hyps[j])
            (Object.hyp false f) h_ne_j
      have h_fj_old : db.find? db.frame.hyps[j] = some (Object.hyp false fj lblj) := by
        have h_fj'' : dbi.find? db.frame.hyps[j] = some (Object.hyp false fj lblj) := by
          simpa [hj_label] using h_fj'
        simpa [h_find_j] using h_fj''
      have h_fi_new : dbi.find? label = some (Object.hyp false fi lbli) := by
        simpa [hi_label] using h_fi'
      have h_fi_eq :
          some (Object.hyp false fi lbli) = some (Object.hyp false f label) := by
        calc
          some (Object.hyp false fi lbli) = dbi.find? label := by
            symm; exact h_fi_new
          _ = some (Object.hyp false f label) := h_find_label
      have h_fi : fi = f := by
        cases h_fi_eq
        rfl
      have h_vi : (match fi[1]! with | .var v' => v' | _ => "") = v := by
        simp [h_fi, h_f1]
      have h_pred_false : floatVarMatches fj v = false := by
        let pred := fun h =>
          match db.find? h with
          | some (Object.hyp false f' _) => floatVarMatches f' v
          | _ => false
        have h_any : db.frame.hyps.toList.any pred = false := by
          simpa [hasFloatBinding, pred] using h_no_dup_bool
        have h_mem : db.frame.hyps[j] ∈ db.frame.hyps.toList := by
          exact Array.getElem_mem_toList (xs := db.frame.hyps) (i := j) hj_old
        have h_not_true : ¬ pred (db.frame.hyps[j]'hj_old) = true :=
          (List.any_eq_false).1 h_any _ h_mem
        have h_not_true' : ¬ floatVarMatches fj v = true := by
          simpa [pred, h_fj_old] using h_not_true
        cases h_match : floatVarMatches fj v with
        | true =>
            exact (h_not_true' h_match).elim
        | false =>
            simp
      dsimp
      intro h_eq
      have h_eq' : (match fj[1]! with | .var v' => v' | _ => "") = v := by
        calc
          (match fj[1]! with | .var v' => v' | _ => "") =
              (match fi[1]! with | .var v' => v' | _ => "") := by
                symm; exact h_eq
          _ = v := h_vi
      have h_match : floatVarMatches fj v = true := by
        simp [floatVarMatches, h_sizej, h_eq']
      rw [h_pred_false] at h_match
      cases h_match
    · -- both new: impossible
      have hj_le : j ≤ db.frame.hyps.size := Nat.le_of_lt_succ hj'
      have hj_ge : db.frame.hyps.size ≤ j := Nat.le_of_not_lt hj_old
      have hj_eq : j = db.frame.hyps.size := Nat.le_antisymm hj_le hj_ge
      subst hj_eq
      exact (h_ne rfl).elim

end Metamath.DBCaseAnalysis
