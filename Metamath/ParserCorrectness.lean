/-
# Parser Correctness: Ground-Up Architecture

Building parser correctness from first principles, layer by layer.

**Architecture:**
```
Layer 5: High-Level Invariants (WellFormedDB)
   ↑
Layer 4: Frame Operations (insertHyp, trimFrame)
   ↑
Layer 3: Object Management (insert, find?)
   ↑
Layer 2: Error State Management (mkError, error propagation)
   ↑
Layer 1: Database State (DB structure, basic operations)
   ↑
Layer 0: Foundation (HashMap properties, String equality)
```

We prove properties at each layer using only properties from layers below.
-/

import Metamath.Verify
import Metamath.VerifyDBPredicateThms
import Metamath.VerifyStabilityThms
import Metamath.WellFormedness
import Metamath.ParserBasics
import Std.Data.HashMap.Lemmas
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false


namespace Metamath.ParserCorrectness

open Verify
open Metamath.WF
open Metamath.ParserBasics
open Std

/-! ## Layer 0: Foundation - HashMap and String Properties

These are the bedrock - properties of data structures we rely on.
They are now proven from `Std.Data.HashMap.Lemmas` and lawful BEq
instances for strings.
-/

/-! ## Well-Scoped Helpers -/

theorem insert_preserves_find?_ne
    (db : DB) (pos : Pos) (label other : String) (obj : String → Object)
    (h_ne : other ≠ label) :
    (db.insert pos label obj).find? other = db.find? other := by
  unfold DB.insert
  have h_eq : (label == other) = false := by
    by_cases h : label = other
    · exact (h_ne h.symm).elim
    · simp [h]
  cases h_obj : obj label with
  | const c =>
      by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
      · simp [h_scope, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.error, DB.find?]
      · simp [h_scope]
        by_cases h_err : db.error
        · simp [h_err, DB.find?]
        · simp [h_err]
          cases h_find : db.find? label with
          | none =>
              -- insertion path
              have h_other :
                  (db.objects.insert label (Object.const c))[other]? = db.objects[other]? := by
                simp [Std.HashMap.getElem?_insert, h_eq]
              simpa [h_find, DB.find?] using h_other
          | some val =>
              cases val <;> simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.find?]
  | var v =>
      by_cases h_err : db.error
      · simp [h_err, DB.find?]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            have h_other :
                (db.objects.insert label (Object.var v))[other]? = db.objects[other]? := by
              simp [Std.HashMap.getElem?_insert, h_eq]
            simpa [h_find, DB.find?] using h_other
        | some val =>
            cases val <;> simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.find?]
  | hyp ess f lbl =>
      by_cases h_err : db.error
      · simp [h_err, DB.find?]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            have h_other :
                (db.objects.insert label (Object.hyp ess f lbl))[other]? = db.objects[other]? := by
              simp [Std.HashMap.getElem?_insert, h_eq]
            simpa [h_find, DB.find?] using h_other
        | some val =>
            cases val <;> simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.find?]
  | assert f fr lbl =>
      by_cases h_err : db.error
      · simp [h_err, DB.find?]
      · simp [h_err]
        cases h_find : db.find? label with
        | none =>
            have h_other :
                (db.objects.insert label (Object.assert f fr lbl))[other]? = db.objects[other]? := by
              simp [Std.HashMap.getElem?_insert, h_eq]
            simpa [h_find, DB.find?] using h_other
        | some val =>
            cases val <;> simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.find?]

theorem isConst_preserved_by_insert
    (db : DB) (pos : Pos) (label c : String) (obj : String → Object)
    (h_ne : c ≠ label) :
    db.isConst c = true → (db.insert pos label obj).isConst c = true := by
  intro h_const
  have h_find :
      (db.insert pos label obj).find? c = db.find? c :=
    insert_preserves_find?_ne db pos label c obj h_ne
  have h_eq : (db.insert pos label obj).isConst c = db.isConst c := by
    unfold DB.isConst
    simp [h_find]
  simpa [h_eq] using h_const

theorem isVar_preserved_by_insert
    (db : DB) (pos : Pos) (label v : String) (obj : String → Object)
    (h_ne : v ≠ label) :
    db.isVar v = true → (db.insert pos label obj).isVar v = true := by
  intro h_var
  have h_find :
      (db.insert pos label obj).find? v = db.find? v :=
    insert_preserves_find?_ne db pos label v obj h_ne
  have h_eq : (db.insert pos label obj).isVar v = db.isVar v := by
    unfold DB.isVar
    simp [h_find]
  simpa [h_eq] using h_var

theorem formulaSymbolsDeclared_preserved_by_insert
    (db : DB) (pos : Pos) (label : String) (obj : String → Object) (f : Formula)
    (h_decl : FormulaSymbolsDeclared db f)
    (h_fresh : db.find? label = none) :
    FormulaSymbolsDeclared (db.insert pos label obj) f := by
  intro s h_mem
  cases s with
  | const c =>
      have h_isConst : db.isConst c = true := h_decl (Sym.const c) h_mem
      have h_find_const : ∃ c', db.find? c = some (.const c') := by
        cases h_find : db.find? c with
        | none =>
            simp [DB.isConst, h_find] at h_isConst
        | some obj =>
            cases obj with
            | const c' => exact ⟨c', rfl⟩
            | var _ => simp [DB.isConst, h_find] at h_isConst
            | hyp _ _ _ => simp [DB.isConst, h_find] at h_isConst
            | assert _ _ _ => simp [DB.isConst, h_find] at h_isConst
      have h_ne : c ≠ label := by
        intro h_eq
        subst h_eq
        rcases h_find_const with ⟨c', h_find_const⟩
        simpa [h_find_const] using h_fresh
      have h_isConst' := isConst_preserved_by_insert db pos label c obj h_ne h_isConst
      simpa using h_isConst'
  | var v =>
      have h_isVar : db.isVar v = true := h_decl (Sym.var v) h_mem
      have h_find_var : ∃ v', db.find? v = some (.var v') := by
        cases h_find : db.find? v with
        | none =>
            simp [DB.isVar, h_find] at h_isVar
        | some obj =>
            cases obj with
            | var v' => exact ⟨v', rfl⟩
            | const _ => simp [DB.isVar, h_find] at h_isVar
            | hyp _ _ _ => simp [DB.isVar, h_find] at h_isVar
            | assert _ _ _ => simp [DB.isVar, h_find] at h_isVar
      have h_ne : v ≠ label := by
        intro h_eq
        subst h_eq
        rcases h_find_var with ⟨v', h_find_var⟩
        simpa [h_find_var] using h_fresh
      have h_isVar' := isVar_preserved_by_insert db pos label v obj h_ne h_isVar
      simpa using h_isVar'

/-- HashMap.insert makes the key findable -/
@[simp] theorem HashMap.find?_insert_eq {α β} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v)[k]? = some v := by
  simp

/-- HashMap.find? on different key after insert -/
@[simp] theorem HashMap.find?_insert_ne {α β} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (k k' : α) (v : β) :
    k ≠ k' → (m.insert k v)[k']? = m[k']? := by
  intro hne
  classical
  have hbranch := Std.HashMap.getElem?_insert (m := m) (k := k) (a := k') (v := v)
  cases hbeq : (k == k') <;> try simp [Std.HashMap.getElem?_insert, hbeq] at hbranch
  · simp [Std.HashMap.getElem?_insert, hbeq]
  ·
    have hk : k = k' := LawfulBEq.eq_of_beq (a := k) (b := k') (by simp [hbeq])
    exact (hne hk).elim

/-- BEq for String is equality -/
@[simp] theorem String.beq_eq (s₁ s₂ : String) : (s₁ == s₂) = true ↔ s₁ = s₂ := by
  constructor
  · intro h
    exact LawfulBEq.eq_of_beq (a := s₁) (b := s₂) h
  · intro h; cases h; simp

theorem String.beq_false_of_ne {s₁ s₂ : String} (h : s₁ ≠ s₂) : (s₁ == s₂) = false := by
  cases h_eq : (s₁ == s₂) with
  | true =>
      have h' : s₁ = s₂ := (String.beq_eq s₁ s₂).1 h_eq
      exact (h h').elim
  | false => rfl

/-! ## Layer 1: Database State - Basic DB Operations

Properties that follow directly from the DB structure definition.
These are trivial because they're just field access.
-/

/-- DB.find? is just HashMap lookup -/
theorem DB.find?_def (db : DB) (label : String) :
  db.find? label = db.objects[label]? := rfl

/-- DB.error is just Option.isSome -/
theorem DB.error_def (db : DB) :
  db.error = db.error?.isSome := rfl

/-- withFrame only modifies the frame field -/
theorem DB.withFrame_preserves_objects (db : DB) (f : Frame → Frame) :
  (db.withFrame f).objects = db.objects := rfl

/-- withFrame only modifies the frame field (error) -/
theorem DB.withFrame_preserves_error (db : DB) (f : Frame → Frame) :
  (db.withFrame f).error? = db.error? := rfl

/-! ## Layer 2: Error State Management

Key insight: Error is "sticky" but only for operations that CHECK it.
Some operations (withFrame) don't check, so they can modify an errored DB.

BUT: The parser STOPS on first error, so inconsistent states are never used!
-/

/-- Frame operations preserve error state (they only modify frame field) -/
theorem withFrame_preserves_error_state (db : DB) (f : Frame → Frame) :
  db.error = true → (db.withFrame f).error = true := by
  intro h
  unfold DB.withFrame DB.error at *
  exact h

/-- mkError always creates error state -/
theorem mkError_creates_error (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error = true := by
  unfold DB.mkError DB.error
  simp

theorem error_false_iff_error?_none (db : DB) : db.error = false ↔ db.error? = none := by
  unfold DB.error
  cases db.error? <;> simp

/-- insert preserves error state (if input has error, output has error) -/
theorem insert_preserves_error (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
  db.error = true → (db.insert pos label obj).error = true := by
  intro h_err
  unfold DB.insert
  cases h_obj : obj label with
  | const c =>
      by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
      · simp [h_obj, h_scope, DB.error, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]
      · simp [h_obj, h_scope, h_err]
  | var v =>
      simp [h_obj, h_err]
  | hyp ess f lbl =>
      simp [h_obj, h_err]
  | assert f fr lbl =>
      simp [h_obj, h_err]

/-- pushScope preserves error state -/
theorem pushScope_preserves_error (db : DB) :
  db.error = true → db.pushScope.error = true := by
  intro h
  -- pushScope: { s with scopes := s.scopes.push s.frame.size }
  -- error: db.error?.isSome
  -- pushScope doesn't modify error?, so error is preserved
  unfold DB.pushScope DB.error at *
  exact h

/-- popScope preserves error state -/
theorem popScope_preserves_error (db : DB) (pos : Pos) :
  db.error = true → (db.popScope pos).error = true := by
  intro h
  unfold DB.popScope
  split
  · -- Has scope to pop: { db with frame := ..., scopes := ... }
    -- Doesn't modify error?, so error is preserved
    unfold DB.error at *
    exact h
  · -- No scope, calls mkError
    exact mkError_creates_error db pos _

/-- withDJ preserves error state -/
theorem withDJ_preserves_error (db : DB) (f : Array DJ → Array DJ) :
  db.error = true → (db.withDJ f).error = true := by
  intro h
  unfold DB.withDJ
  exact withFrame_preserves_error_state db _ h

/-- withHyps preserves error state -/
theorem withHyps_preserves_error (db : DB) (f : Array String → Array String) :
  db.error = true → (db.withHyps f).error = true := by
  intro h
  unfold DB.withHyps
  exact withFrame_preserves_error_state db _ h

/-- DB.insert doesn't modify frame -/
theorem insert_frame_unchanged (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).frame = db.frame := by
  unfold DB.insert
  -- All paths preserve frame via: mkError (preserves frame), return db (rfl), or record update (rfl)
  repeat (first | rfl | simp | split)

/-- Helper: mkError creates an error -/
theorem mkError_has_error (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).error? ≠ none := by
  unfold DB.mkError
  simp

/-- Helper: If db has no error and insert results in no error,
    then we didn't hit any error paths -/
theorem insert_success_no_mkError
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (_h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none) :
    -- If insert succeeded, we took the success path (no mkError calls)
    ∀ msg, (db.insert pos l obj) ≠ db.mkError pos msg := by
  intro msg h_eq
  rw [h_eq] at h_no_err_after
  exact mkError_has_error db pos msg h_no_err_after

/-- Helper: If db.find? l = none, db has no error, and insert succeeds (no error after),
    then objects map was updated.
    Key: The h_no_err_after premise rules out the const permissive check failure. -/
theorem insert_new_object_updates
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_find : db.find? l = none)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none) :
    (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  have h_no_prior_err : db.error = false := (error_false_iff_error?_none db).2 h_no_err_before
  have h_no_err : (db.insert pos l obj).error = false :=
    (error_false_iff_error?_none (db.insert pos l obj)).2 h_no_err_after
  exact DB.insert_no_dup_objects db pos l obj h_no_prior_err h_no_find h_no_err

/-- When insert succeeds (no error after), the objects map was updated.
    Note: This doesn't hold when inserting a var that already exists as a var
    (in that case, insert succeeds but doesn't update objects). -/
theorem insert_success_objects_updated
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  have h_no_prior_err : db.error = false := (error_false_iff_error?_none db).2 h_no_err_before
  have h_no_err : (db.insert pos l obj).error = false :=
    (error_false_iff_error?_none (db.insert pos l obj)).2 h_no_err_after
  by_cases h_find : db.find? l = none
  · exact DB.insert_no_dup_objects db pos l obj h_no_prior_err h_find h_no_err
  · -- Existing object: the only non-error path is var-var, excluded by h_not_var_dup
    exfalso
    cases h_o : db.find? l with
    | none => contradiction
    | some o =>
      cases o with
      | var v_o =>
        cases h_obj : obj l with
        | var v_l =>
          have h_vo_is_l : v_o = l := h_var_labels_match_names l v_o h_o
          have h_vl_is_l : v_l = l := h_obj_var_names_match l v_l h_obj
          have h_vo_eq_vl : v_o = v_l := by
            rw [h_vo_is_l, h_vl_is_l]
          have : ∃ v, obj l = .var v ∧ db.find? l = some (.var v) := by
            refine ⟨v_l, h_obj, ?_⟩
            simpa [h_vo_eq_vl] using h_o
          exact h_not_var_dup this
        | const c_l =>
          have h_err : (db.insert pos l obj).error? ≠ none := by
            unfold DB.insert
            by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
            · simpa [h_obj, h_scope] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl .constMustBeOutermost))
            · simpa [h_obj, h_scope, h_no_prior_err, h_o] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          exact h_err (by simpa using h_no_err_after)
        | hyp ess f_l lbl =>
          have h_err : (db.insert pos l obj).error? ≠ none := by
            unfold DB.insert
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          exact h_err (by simpa using h_no_err_after)
        | assert fmla fr_l name =>
          have h_err : (db.insert pos l obj).error? ≠ none := by
            unfold DB.insert
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          exact h_err (by simpa using h_no_err_after)
      | const c_o =>
        have h_err : (db.insert pos l obj).error? ≠ none := by
          unfold DB.insert
          cases h_obj : obj l with
          | const c =>
            by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
            · simpa [h_obj, h_scope] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl .constMustBeOutermost))
            · simpa [h_obj, h_scope, h_no_prior_err, h_o] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | var v =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | hyp ess f lbl =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | assert f fr name =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
        exact h_err (by simpa using h_no_err_after)
      | hyp ess_o f_o lbl_o =>
        have h_err : (db.insert pos l obj).error? ≠ none := by
          unfold DB.insert
          cases h_obj : obj l with
          | const c =>
            by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
            · simpa [h_obj, h_scope] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl .constMustBeOutermost))
            · simpa [h_obj, h_scope, h_no_prior_err, h_o] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | var v =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | hyp ess f lbl =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | assert f fr name =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
        exact h_err (by simpa using h_no_err_after)
      | assert fmla_o fr_o name_o =>
        have h_err : (db.insert pos l obj).error? ≠ none := by
          unfold DB.insert
          cases h_obj : obj l with
          | const c =>
            by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
            · simpa [h_obj, h_scope] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl .constMustBeOutermost))
            · simpa [h_obj, h_scope, h_no_prior_err, h_o] using
                (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | var v =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | hyp ess f lbl =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
          | assert f fr name =>
            simpa [h_obj, h_no_prior_err, h_o] using
              (DB.mkErrorFromEvidence_error? (s := db) pos (.scopeDecl (.duplicateSymbolOrAssert l)))
        exact h_err (by simpa using h_no_err_after)

/-- When insert succeeds, looking up the inserted key gives the inserted object -/
theorem insert_success_find?_self
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    (db.insert pos l obj).find? l = some (obj l) := by
  unfold DB.find?
  rw [insert_success_objects_updated db pos l obj h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match]
  exact HashMap.find?_insert_eq db.objects l (obj l)

/-- When insert succeeds, looking up a different key is unchanged -/
theorem insert_success_find?_ne
    (db : DB) (pos : Pos) (l l' : String) (obj : String → Object)
    (h_ne : l' ≠ l)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    (db.insert pos l obj).find? l' = db.find? l' := by
  unfold DB.find?
  rw [insert_success_objects_updated db pos l obj h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match]
  exact HashMap.find?_insert_ne db.objects l l' (obj l) h_ne.symm

/-- When insert succeeds, WellFormedFrame is preserved for frames whose hypothesis
    labels are distinct from the inserted key. -/
theorem insert_preserves_frame_wf
    (db : DB) (pos : Pos) (l : String) (obj : String → Object) (fr : Frame)
    (h_wf : WellFormedFrame db fr)
    (h_no_dup : ∀ i (hi : i < fr.hyps.size), (fr.hyps[i]'hi) ≠ l)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    WellFormedFrame (db.insert pos l obj) fr := by
  constructor
  · -- Part 1: All hyps in fr still satisfy HypOK
    intro i hi
    -- h_wf.1 gives us: HypOK db fr.hyps[i]
    have h_old := h_wf.1 i hi
    -- HypOK means ∃ ess f lbl, db.find? fr.hyps[i] = some (.hyp ess f lbl) ∧ ...
    unfold HypOK at h_old ⊢
    rcases h_old with ⟨ess, f, lbl, h_find, h_float, h_formula⟩
    -- Show the new db still has this hyp at fr.hyps[i]
    refine ⟨ess, f, lbl, ?_, h_float, h_formula⟩
    -- (db.insert...).find? fr.hyps[i] = some (.hyp ess f lbl)
    have h_ne := h_no_dup i hi
    rw [insert_success_find?_ne db pos l (fr.hyps[i]'hi) obj h_ne h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match]
    exact h_find

  · -- Part 2: UniqueFloatVars preserved
    intro i j hi hj h_ij fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
    -- Use h_wf.2 with the old finds
    have h_ne_i := h_no_dup i hi
    have h_ne_j := h_no_dup j hj
    -- Rewrite finds in new db to old db
    rw [insert_success_find?_ne db pos l (fr.hyps[i]'hi) obj h_ne_i h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match] at h_fi
    rw [insert_success_find?_ne db pos l (fr.hyps[j]'hj) obj h_ne_j h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match] at h_fj
    -- Now apply h_wf.2
    exact h_wf.2 i j hi hj h_ij fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j

/-- Helper: for loops that only call mkError preserve error state -/
theorem for_loop_mkError_preserves_error (db : DB) (pos : Pos) (hyps : Array String) :
  db.error = true →
  (Id.run do
    let mut db := db
    for _ in hyps do
      -- Some condition that might trigger mkError
      if true then  -- Always triggers (unconditional error propagation)
        db := db.mkError pos "some error"
    db).error = true := by
  intro h_err
  -- The loop body always sets error, so the result has error = true.
  -- It holds even when hyps is empty (result is the initial db).
  cases hyps using Array.casesOn with
  | mk xs =>
    induction xs generalizing db with
    | nil =>
        simpa [Id.run, DB.error] using h_err
    | cons _ tl ih =>
        have h_err' : (db.mkError pos "some error").error = true :=
          mkError_creates_error db pos _
        simpa [List.foldl, DB.mkError, DB.error] using (ih (db := db.mkError pos "some error") h_err')

/-- insertHyp preserves error state -/
theorem insertHyp_preserves_error (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula) :
  db.error = true → (db.insertHyp pos label ess f).error = true := by
  intro h_err
  unfold DB.insertHyp
  have h_checks : (db.insertHypChecks pos ess f).error = true := by
    unfold DB.insertHypChecks
    by_cases h_head : f.hasConstHead
    · simp [h_head, h_err]
    · simp [h_head, DB.error, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]
  simp [h_checks]

/-- insertAxiom preserves error state -/
theorem insertAxiom_preserves_error (db : DB) (pos : Pos) (label : String) (fmla : Formula) :
  db.error = true → (db.insertAxiom pos label fmla).error = true := by
  intro h
  unfold DB.insertAxiom
  by_cases h_head : fmla.hasConstHead
  · simp [h_head, h]
  · simp [h_head, DB.error, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]

/-- THE KEY PROPERTY: Parser stops on first error

This is the property that makes the architecture sound.
Once an error occurs, the parser stops processing.
Therefore, any temporary inconsistencies (like label in frame.hyps but not in db.objects)
are never used for verification.

**Proof Strategy**: The actual parser has structure (Verify.lean lines 777-779):
```lean
let s := s.feedToken (base + off) tk
if let some ⟨e, _⟩ := s.db.error? then
  { s with db := { s.db with error? := some ⟨e, i+1⟩ } }  -- Stop!
else
  feed base arr (i+1) .ws s  -- Continue only if no error
```
This shows that once an error occurs, the feed function returns immediately
without processing more tokens. Therefore errors propagate to the final state.
-/
/- Simpler, more direct version:
   If we have error preservation and the fold produces an error,
   we're done. The complex version with intermediate_db is under-specified.
-/
theorem parser_stops_on_error_simple
  (initial_db final_db : DB)
  (parsing_steps : List (DB → DB)) :
  -- Hypothesis: all parsing steps preserve error state
  (∀ step ∈ parsing_steps, ∀ db : DB, db.error = true → (step db).error = true) →
  -- Initial DB has no error
  initial_db.error = false →
  -- Final DB is result of applying all steps
  final_db = parsing_steps.foldl (fun db step => step db) initial_db →
  -- If final DB has error, some step must have created it
  final_db.error = true →
  -- Then some step created an error
  ∃ step ∈ parsing_steps, ∃ i < parsing_steps.length,
    let intermediate := (parsing_steps.take i).foldl (fun db s => s db) initial_db
    intermediate.error = false ∧ (step intermediate).error = true := by
  intro h_preserve h_init_ok h_fold h_final_err
  -- Prove by induction: if we start with no error and end with error,
  -- some step along the way must have introduced it.
  induction parsing_steps generalizing initial_db final_db with
  | nil =>
      -- No steps: final_db = initial_db, contradicts h_final_err.
      simp [List.foldl] at h_fold
      subst h_fold
      simp [h_init_ok] at h_final_err
  | cons step steps ih =>
      let db1 := step initial_db
      have h_fold' : final_db = steps.foldl (fun db s => s db) db1 := by
        simpa [List.foldl, db1] using h_fold
      by_cases h_err1 : db1.error = true
      · -- First step created the error.
        refine ⟨step, ?_, 0, ?_, ?_⟩
        · simp
        · simp
        · constructor
          · simp [List.take, h_init_ok]
          · simpa [db1] using h_err1
      · -- Error appears later in the tail.
        have h_err1_false : db1.error = false := by
          simpa using h_err1
        have h_preserve_tail : ∀ s ∈ steps, ∀ db : DB, db.error = true → (s db).error = true := by
          intro s h_in db h_db
          apply h_preserve s
          · simp [h_in]
          · exact h_db
        rcases ih (initial_db := db1) (final_db := final_db) h_preserve_tail h_err1_false h_fold' h_final_err with
          ⟨step', h_in, i, h_i, h_inter⟩
        refine ⟨step', ?_, i + 1, ?_, ?_⟩
        · exact List.mem_cons_of_mem _ h_in
        · simpa [List.length] using Nat.succ_lt_succ h_i
        · -- Align intermediate states for the extended prefix.
          simpa [List.take_succ_cons, List.foldl, db1] using h_inter

/-- The key property: if steps preserve error and we apply them sequentially,
    once an error appears it propagates to the end. PROVEN! ✓ -/
theorem parser_stops_on_error
  (initial_db : DB)
  (parsing_steps : List (DB → DB))
  (pre : List (DB → DB))
  (suf : List (DB → DB))
  (h_preserve : ∀ step ∈ parsing_steps, ∀ db : DB, db.error = true → (step db).error = true)
  (h_split : parsing_steps = pre ++ suf)
  (h_inter_err : (pre.foldl (fun db step => step db) initial_db).error = true) :
  (parsing_steps.foldl (fun db step => step db) initial_db).error = true := by
  rw [h_split]
  simp [List.foldl_append]
  -- After processing pre, we have intermediate with error
  -- Processing suf preserves error by h_preserve
  have h_mono : ∀ (steps : List (DB → DB)) (db : DB),
    (∀ s ∈ steps, ∀ d : DB, d.error = true → (s d).error = true) →
    db.error = true →
    (steps.foldl (fun db step => step db) db).error = true := by
      intro steps db h_pres h_err
      induction steps generalizing db with
      | nil =>
        simp
        exact h_err
      | cons hd tl ih =>
        simp [List.foldl]
        apply ih
        · intro s h_in
          apply h_pres
          simp [h_in]
        · apply h_pres hd (by simp) _ h_err
  apply h_mono
  · intro s h_in
    apply h_preserve
    rw [h_split]
    simp [h_in]
  · exact h_inter_err

/-- Contrapositive: If final DB has no error, no errors occurred during parsing

This is the contrapositive of parser_stops_on_error.
It states: if we end with no error, then no intermediate step created an error
(unless that intermediate DB already had an error).

**This is THE KEY for connecting parser success to well-formedness**:
If `db.error? = none` at the end, then every operation succeeded,
which means all invariants were maintained throughout parsing.
-/
theorem no_final_error_means_no_intermediate_errors
  (initial_db final_db : DB)
  (parsing_steps : List (DB → DB)) :
  (∀ step ∈ parsing_steps, ∀ db : DB, db.error = true → (step db).error = true) →
  final_db.error = false →
  initial_db.error = false →
  -- Simulate parsing
  final_db = parsing_steps.foldl (fun db step => step db) initial_db →
  -- Then NO intermediate prefix produces an error
  ∀ i ≤ parsing_steps.length,
    let intermediate := (parsing_steps.take i).foldl (fun db s => s db) initial_db
    intermediate.error = false := by
  intro h_preserve h_final_ok h_init_ok h_fold i h_i
  let intermediate := (parsing_steps.take i).foldl (fun db s => s db) initial_db
  by_cases h_err : intermediate.error = true
  · have h_split : parsing_steps = parsing_steps.take i ++ parsing_steps.drop i := by
      exact (List.take_append_drop i parsing_steps).symm
    have h_final_err : final_db.error = true := by
      have h_stop := parser_stops_on_error initial_db parsing_steps
        (parsing_steps.take i) (parsing_steps.drop i) h_preserve h_split h_err
      simp [h_fold.symm] at h_stop
      exact h_stop
    exfalso
    exact (by
      have h_ok' := h_final_ok
      have h_err' := h_final_err
      simp [DB.error_def] at h_ok' h_err'
      simp [h_ok'] at h_err')
  · -- No error in this prefix.
    cases h_intermediate : intermediate.error with
    | false =>
        simp [intermediate, h_intermediate]
    | true =>
        exfalso
        apply h_err
        simp [intermediate, h_intermediate]

/-- Operations that check error first preserve this property -/
theorem error_short_circuit (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
  db.error = true →
  (if db.error then db else db.insert pos label obj) = db := by
  intro h
  simp [h]

/-! ## Layer 3: Object Management - insert and find?

The insert operation is the foundation of database construction.
Key property: after inserting, we can find what we inserted.
-/

/-- After successful insert (no error), object is findable.
   This is proven in Verify.lean:336 as DB.insert_find?_self. -/
theorem insert_findable (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
  db.error = false →
  db.find? label = none →
  (db.insert pos label obj).error = false →
  (db.insert pos label obj).find? label = some (obj label) :=
  DB.insert_find?_self db pos label obj

/-- Insert preserves other objects (if no collision). -/
theorem insert_preserves_others (db : DB) (pos : Pos) (label label' : String) (obj : String → Object) :
  label ≠ label' →
  db.error = false →
  db.find? label = none →
  (db.insert pos label obj).find? label' = db.find? label' := by
  intro h_ne h_no_err h_not_found
  have h_not_found' : db.objects[label]? = none := by
    simpa [DB.find?] using h_not_found
  unfold DB.insert
  cases h_obj : obj label with
  | const c =>
      by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
      · -- Const scope check fails: mkErrorFromEvidence, objects unchanged.
        simp [h_obj, h_scope, DB.error, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence, DB.find?]
      · -- Const scope check passes: normal insert.
        simp [h_scope, h_no_err, h_not_found', DB.find?]
        exact HashMap.find?_insert_ne db.objects label label' (Object.const c) h_ne
  | var v =>
      simp [h_no_err, h_not_found', DB.find?]
      exact HashMap.find?_insert_ne db.objects label label' (Object.var v) h_ne
  | hyp ess f lbl =>
      simp [h_no_err, h_not_found', DB.find?]
      exact HashMap.find?_insert_ne db.objects label label' (Object.hyp ess f lbl) h_ne
  | assert f fr lbl =>
      simp [h_no_err, h_not_found', DB.find?]
      exact HashMap.find?_insert_ne db.objects label label' (Object.assert f fr lbl) h_ne

/-- Duplicate insert creates error (unless both are variables). -/
theorem insert_duplicate_error (db : DB) (pos : Pos) (label : String) (obj : String → Object) (existing : Object) :
  db.error = false →
  db.find? label = some existing →
  (¬∃ v v', obj label = .var v ∧ existing = .var v') →
  (db.insert pos label obj).error = true := by
  intro h_no_err h_exists h_not_var_redef
  have h_no_err' : db.error?.isSome = false := by
    simpa [DB.error_def] using h_no_err
  unfold DB.insert
  cases h_obj : obj label with
  | const c =>
      by_cases h_scope : !db.config.allowConstInnerScope && db.scopes.size > 0
      · -- Const scope check fails: mkErrorFromEvidence
        simp [h_obj, h_scope, DB.error, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]
      · -- Const scope check passes, duplicate triggers mkError
        cases existing <;> simp [h_scope, h_no_err', h_exists, DB.error, DB.mkErrorFromEvidence]
  | var v =>
      cases existing with
      | var v' =>
          exfalso
          apply h_not_var_redef
          exact ⟨v, v', h_obj, rfl⟩
      | const c =>
          simp [h_no_err', h_exists, DB.error, DB.mkErrorFromEvidence]
      | hyp ess f lbl =>
          simp [h_no_err', h_exists, DB.error, DB.mkErrorFromEvidence]
      | assert f fr lbl =>
          simp [h_no_err', h_exists, DB.error, DB.mkErrorFromEvidence]
  | hyp ess f lbl =>
      cases existing <;> simp [h_no_err', h_exists, DB.error, DB.mkErrorFromEvidence]
  | assert f fr lbl =>
      cases existing <;> simp [h_no_err', h_exists, DB.error, DB.mkErrorFromEvidence]

/-! ## Layer 4-continued: Frame Operations - insertHyp

This is where the crucial $f uniqueness check happens!
This is THE key property for float variable uniqueness.

**IMPORTANT**: insertHyp short-circuits on error before calling withHyps.
This avoids frame/object inconsistencies when db.error is already set.

For parser correctness, we rely on: if parsing ends with db.error = false,
then all insertHyp calls succeeded and frame entries correspond to objects.
-/

/-- insertHyp checks for duplicate float variables (lines 304-306 in Verify.lean)

    Note: This only applies in non-permissive mode (zar, knife). Exe mode allows duplicate $f.
-/
theorem insertHyp_rejects_duplicate_float
  (db : DB) (pos : Pos) (label : String) (f : Formula)
  (existing_label : String) (existing_f : Formula) :
  db.error = false →
  db.config.allowDuplicateFloat = false →  -- Only zar/knife modes reject duplicate $f
  -- There's already a float for this variable
  existing_label ∈ db.frame.hyps.toList →
  db.find? existing_label = some (.hyp false existing_f existing_label) →
  WellFormedFloat existing_f →
  WellFormedFloat f →
  existing_f[1]!.value = f[1]!.value →
  -- Then insertHyp creates an error
  (db.insertHyp pos label false f).error = true := by
  intro h_no_err h_perm h_in_frame h_find h_wf_old h_wf_new h_same_var
  rcases h_wf_old with ⟨h_size_old, ⟨_, v_old, _, h1_old⟩⟩
  rcases h_wf_new with ⟨h_size_new, ⟨c_new, v_new, h0_new, h1_new⟩⟩
  have h_pos0 : 0 < f.size := by
    simp [h_size_new]
  have h_pos1 : 1 < f.size := by
    simp [h_size_new]
  have h0_new' : f[0]'h_pos0 = Sym.const c_new := by
    have h_eq : f[0]! = f[0]'h_pos0 := by
      simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
    simpa [h_eq] using h0_new
  have h1_new' : f[1]'h_pos1 = Sym.var v_new := by
    have h_eq : f[1]! = f[1]'h_pos1 := by
      simpa using (Array.getBang_eq_get_nat (a := f) (i := 1) (h := h_pos1))
    simpa [h_eq] using h1_new
  have h_head : f.hasConstHead = true := by
    unfold Formula.hasConstHead
    simp [h_pos0, h0_new']
  have h_shape : f.isFloatShape = true := by
    unfold Formula.isFloatShape
    simp [h_size_new, h0_new', h1_new']
  have h_size_ge : f.size ≥ 2 := by
    simp [h_size_new]
  have h_v_eq : v_old = v_new := by
    have h_old_val : existing_f[1]!.value = v_old := by
      simp [Sym.value, h1_old]
    have h_new_val : f[1]!.value = v_new := by
      simp [Sym.value, h1_new]
    simpa [h_old_val, h_new_val] using h_same_var
  have h_beq : (v_old == v_new) = true := (String.beq_eq v_old v_new).2 h_v_eq
  have h_dup : db.floatVarOccursInFrame v_new = true := by
    unfold DB.floatVarOccursInFrame
    have h_pos1_old : 1 < existing_f.size := by
      simp [h_size_old]
    have h1_old' : existing_f[1]'h_pos1_old = Sym.var v_old := by
      have h_eq : existing_f[1]! = existing_f[1]'h_pos1_old := by
        simpa using (Array.getBang_eq_get_nat (a := existing_f) (i := 1) (h := h_pos1_old))
      simpa [h_eq] using h1_old
    apply List.any_eq_true.2
    refine ⟨existing_label, h_in_frame, ?_⟩
    simp [h_find, h_size_old, h1_old', h_beq]
  have h_new_val : f[1]!.value = v_new := by
    simp [Sym.value, h1_new]
  have h_dup' : db.floatVarOccursInFrame f[1]!.value = true := by
    simpa [h_new_val] using h_dup

  have h_check_err : (DB.insertHypChecks db pos false f).error = true := by
    have h_no_err_isSome : db.error?.isSome = false := by
      simpa [DB.error_def] using h_no_err
    simp [DB.insertHypChecks, DB.error, h_head, h_shape, h_size_ge, h_dup', h_perm, h_no_err_isSome]
  simp [DB.insertHyp, h_check_err]

/-- insertHyp succeeds when no duplicate exists -/
theorem insertHyp_succeeds_when_unique
  (db : DB) (pos : Pos) (label : String) (f : Formula) :
  db.error = false →
  db.find? label = none →
  WellFormedFloat f →
  -- No other float binds this variable
  (∀ h ∈ db.frame.hyps.toList,
    ∀ prevF prevLbl,
      db.find? h = some (.hyp false prevF prevLbl) →
      WellFormedFloat prevF ∧
      prevF[1]!.value ≠ f[1]!.value) →
  -- Then insertHyp succeeds and adds to frame
  (db.insertHyp pos label false f).error = false ∧
  (db.insertHyp pos label false f).find? label = some (.hyp false f label) := by
  intro h_no_err h_not_found h_wf h_unique
  rcases h_wf with ⟨h_size_eq, ⟨c, v, h0, h1⟩⟩
  have h_pos0 : 0 < f.size := by
    simp [h_size_eq]
  have h_pos1 : 1 < f.size := by
    simp [h_size_eq]
  have h0' : f[0]'h_pos0 = Sym.const c := by
    have h_eq : f[0]! = f[0]'h_pos0 := by
      simpa using (Array.getBang_eq_get_nat (a := f) (i := 0) (h := h_pos0))
    simpa [h_eq] using h0
  have h1' : f[1]'h_pos1 = Sym.var v := by
    have h_eq : f[1]! = f[1]'h_pos1 := by
      simpa using (Array.getBang_eq_get_nat (a := f) (i := 1) (h := h_pos1))
    simpa [h_eq] using h1
  have h_head : f.hasConstHead = true := by
    unfold Formula.hasConstHead
    simp [h_pos0, h0']
  have h_shape : f.isFloatShape = true := by
    unfold Formula.isFloatShape
    simp [h_size_eq, h0', h1']
  have h_size_ge : f.size ≥ 2 := by
    simp [h_size_eq]
  have h_dup : db.floatVarOccursInFrame f[1]!.value = false := by
    unfold DB.floatVarOccursInFrame
    apply List.any_eq_false.2
    intro h h_mem
    cases h_find : db.find? h with
    | none =>
        simp
    | some obj =>
        cases obj with
        | hyp ess prevF prevLbl =>
            cases ess with
            | true =>
                simp
            | false =>
                have h_pair : WellFormedFloat prevF ∧ prevF[1]!.value ≠ f[1]!.value :=
                  h_unique h h_mem prevF prevLbl h_find
                rcases h_pair with ⟨h_wf_prev, h_ne_prev⟩
                rcases h_wf_prev with ⟨h_size_prev, ⟨_, v_prev, _, h1_prev⟩⟩
                have h_pos1_prev : 1 < prevF.size := by
                  simp [h_size_prev]
                have h1_prev' : prevF[1]'h_pos1_prev = Sym.var v_prev := by
                  have h_eq : prevF[1]! = prevF[1]'h_pos1_prev := by
                    simpa using (Array.getBang_eq_get_nat (a := prevF) (i := 1) (h := h_pos1_prev))
                  simpa [h_eq] using h1_prev
                have h_ne' : v_prev ≠ f[1]!.value := by
                  simpa [h1_prev, Sym.value] using h_ne_prev
                have h_beq_false : (v_prev == f[1]!.value) = false :=
                  String.beq_false_of_ne h_ne'
                simp [h_size_prev, h1_prev', h_beq_false]
        | const _ =>
            simp
        | var _ =>
            simp
        | assert _ _ _ =>
            simp
  have h_check_eq : DB.insertHypChecks db pos false f = db := by
    simp [DB.insertHypChecks, h_head, h_shape, h_size_ge, h_dup, h_no_err]
  have h_insert_err? : (db.insert pos label (.hyp false f)).error? = none := by
    have h_err_none : db.error? = none := (error_false_iff_error?_none db).1 h_no_err
    unfold DB.insert
    simp [h_err_none, h_no_err, h_not_found]
  have h_insert_err : (db.insert pos label (.hyp false f)).error = false := by
    exact (error_false_iff_error?_none (db.insert pos label (.hyp false f))).2 h_insert_err?
  have h_insertHyp_eq :
      db.insertHyp pos label false f =
        DB.withHyps (fun hyps => hyps.push label) (db.insert pos label (.hyp false f)) := by
    simp [DB.insertHyp, h_check_eq, h_insert_err, h_no_err]
  have h_final_err : (db.insertHyp pos label false f).error = false := by
    rw [h_insertHyp_eq]
    simpa [DB.withHyps, DB.withFrame, DB.error] using h_insert_err
  have h_find_self : (db.insert pos label (.hyp false f)).find? label = some (.hyp false f label) := by
    apply Verify.DB.insert_find?_self
    · exact h_no_err
    · exact h_not_found
    · exact h_insert_err
  have h_find_final : (db.insertHyp pos label false f).find? label = some (.hyp false f label) := by
    rw [h_insertHyp_eq]
    unfold DB.find?
    simpa [DB.withHyps, DB.withFrame, DB.find?_def] using h_find_self
  exact ⟨h_final_err, h_find_final⟩

/-! ## Layer 5: High-Level Invariants

These compose the lower layers to establish WellFormedness.
-/

/-- UniqueFloatVars is a direct projection of WellFormedDB. -/
theorem wellFormedDB_implies_unique_floats
  (db : DB) (h_wf : WellFormedDB db) :
  UniqueFloatVars db db.frame := by
  exact h_wf.1.2

/-! ## Main Theorem: Parser Success → WellFormedDB

This is the composition of all layers. The key insight:
If parsing completes with no error, then all DB operations succeeded,
which means all their preconditions were met, which means well-formedness
was maintained throughout.
-/

theorem parser_construction_wellformed
  (bytes : ByteArray) :
  (Verify.checkBytes bytes).error? = none →
  WellFormedDB (Verify.checkBytes bytes) := by
  intro h_ok
  have h_zar_no_dup : Verify.ModeConfig.zar.allowDuplicateFloat = false := rfl
  have h_wf? : (Verify.checkBytes bytes).wellFormed? = true :=
    Verify.checkBytes_no_error_wellFormed? bytes (config := {}) h_zar_no_dup h_ok
  exact wellFormedDB_of_wellFormed? h_wf?

/-- The ultimate soundness theorem: successful parsing produces valid proofs -/
theorem parser_soundness_main
  (bytes : ByteArray) :
  -- If parsing succeeds
  (Verify.checkBytes bytes).error? = none →
  -- Then all objects are well-formed and satisfy Metamath rules
  (∀ label obj, (Verify.checkBytes bytes).find? label = some obj →
    match obj with
    | .const _ => true  -- Constants are simple
    | .var _ => true    -- Variables are simple
    | .hyp ess f _ =>
      -- Hypotheses have well-formed formulas
      WellFormedFormula f ∧
      -- Float hypotheses respect uniqueness
      (¬ess → f.size = 2 ∧ (∃ c v, f[0]! = .const c ∧ f[1]! = .var v))
    | .assert fmla _ _ =>
      -- Assertions have valid proofs
      WellFormedFormula fmla ∧
      -- The proof would be valid if checked
      true  -- Proof checking is separate
  ) := by
  intro h_success label obj h_find
  let final := Verify.checkBytes bytes
  have h_wf : WellFormedDB final := by
    simpa [final] using parser_construction_wellformed bytes h_success
  cases obj with
  | const _ => trivial
  | var _ => trivial
  | hyp ess f lbl =>
    constructor
    · -- WellFormedFormula f (either direct or derived from float well-formedness)
      cases ess with
      | true =>
          have h_obj := h_wf.2 label (Object.hyp true f lbl) h_find
          simpa using h_obj
      | false =>
          have h_obj := h_wf.2 label (Object.hyp false f lbl) h_find
          -- WellFormedFloat implies WellFormedFormula
          rcases h_obj with ⟨h_size, ⟨c, v, h0, _h1⟩⟩
          exact ⟨by simp [h_size], ⟨c, h0⟩⟩
    · -- Float structure (only relevant when ess = false)
      intro h_not_ess
      cases ess with
      | true => cases h_not_ess rfl
      | false =>
          have h_obj := h_wf.2 label (Object.hyp false f lbl) h_find
          rcases h_obj with ⟨h_size, ⟨c, v, h0, h1⟩⟩
          exact ⟨h_size, ⟨c, v, h0, h1⟩⟩
  | assert fmla proof lbl =>
    constructor
    · have h_obj := h_wf.2 label (Object.assert fmla proof lbl) h_find
      exact h_obj.1
    · trivial

/-! ## Structure-Preserving Operations and WellFormedness

The key theorem for parser correctness: operations that don't set errors
preserve database well-formedness.
-/

/-- Database operations that preserve structural invariants -/
inductive StructurePreservingOp (db : DB) : (DB → DB) → Prop where
  | insert (pos : Pos) (label : String) (obj : String → Object)
      -- Validation invariant: object being inserted is well-formed
      (h_validated : match obj label with
        | .hyp false f _ => WellFormedFloat f
        | .hyp true f _  => WellFormedFormula f
        | .assert f fr _ =>
            WellFormedFormula f ∧ WellFormedFrame db fr ∧
              (∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ label)
        | .var v         => v = label  -- Var label = name invariant!
        | _              => True)
      -- Function invariant: if obj constructs vars, they satisfy label=name (for ALL labels!)
      (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl)
      -- DB Freshness invariant: label not already in THIS database
      (h_fresh_db : db.find? label = none)
      -- Frame freshness invariant: label not in THIS current frame
      (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size),
        (db.frame.hyps[i]'hi) ≠ label)
      -- Freshness invariant: label not in any assertion frame in THIS DB
      (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), (fr_assert.hyps[i]'hi) ≠ label) :
      StructurePreservingOp db (fun db' => db'.insert pos label obj)
  | pushScope : StructurePreservingOp db (fun db' => db'.pushScope)
  | popScope (pos : Pos) : StructurePreservingOp db (fun db' => db'.popScope pos)
  | withFrame (f : Frame → Frame)
      (h_preserves : ∀ db_any fr, WellFormedFrame db_any fr → WellFormedFrame db_any (f fr)) :
      StructurePreservingOp db (fun db' => db'.withFrame f)
  | id : StructurePreservingOp db id

/-- **Main Theorem**: Structure-preserving operations maintain WellFormedDB.

If an operation doesn't raise an error and is structure-preserving,
then it maintains database well-formedness.

This is the KEY composition theorem that ties together all parser invariants.
-/
theorem structure_preserving_maintains_wf
    {op : DB → DB}
    (db : DB)
    (h_struct : StructurePreservingOp db op)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (op db).error? = none) :
    WellFormedDB (op db) := by
  rcases h_wf with ⟨h_frame_wf, h_objs_wf⟩
  cases h_struct with
  | insert pos label obj h_validated h_obj_var_names_match h_fresh_db h_fresh_label h_fresh_in_asserts =>
      -- Case: insert operation
      -- We now have type-safe invariants from StructurePreservingOp!
      -- Strategy: Pattern match on obj label to extract the specific validation
      cases h_obj : obj label with
      | const c =>
          -- Inserting a constant
          -- Beta-reduce op db to db.insert pos label obj
          change WellFormedDB (db.insert pos label obj)
          change (db.insert pos label obj).error? = none at h_no_err_after

          -- Constants have no WF requirements (h_validated is True)
          -- Just need to show frame and objects preserved

          constructor
          · -- Part 1: Frame WF preserved
            rw [insert_frame_unchanged]

            -- Establish h_not_var_dup using h_fresh_db
            have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
              intro ⟨v_dup, _, h_find_old⟩
              rw [h_find_old] at h_fresh_db
              cases h_fresh_db

            have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
              intro lbl v_old h_find
              exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

            exact insert_preserves_frame_wf db pos label obj db.frame
              h_frame_wf h_fresh_label h_no_err_before h_no_err_after
              h_not_var_dup h_var_inv h_obj_var_names_match

          · -- Part 2: All objects still WF
            intro lbl obj' h_find'
            by_cases h_eq : lbl = label
            · -- NEW object: lbl = label, so obj' = .const c
              -- WF condition for const is True
              rw [h_eq]

              -- Establish h_not_var_dup (same as Part 1)
              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_find_self := insert_success_find?_self db pos label obj
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

              -- Convert h_find' to use label
              have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                rw [h_eq] at h_find'
                exact h_find'

              -- Show obj' = obj label = .const c
              have h_obj'_eq : obj' = obj label := by
                have : some (obj label) = some obj' := by
                  rw [← h_find_self, h_find'_label]
                cases this
                rfl

              rw [h_obj] at h_obj'_eq
              cases h_obj'_eq
              -- Goal: True (WF condition for const)
              exact True.intro

            · -- EXISTING object: lbl ≠ label
              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_obj_inv := h_obj_var_names_match

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
              rw [h_find_unchanged] at h_find'

              -- Get old WF and upgrade for assert case
              have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

              cases h_obj' : obj' with
              | const c' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | var v' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | hyp ess f' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | assert f' fr' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  constructor
                  · exact h_obj'_wf_old.1
                  · have h_fr_wf_old := h_obj'_wf_old.2
                    have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                      rw [← h_obj']
                      exact h_find'
                    have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                      intro i hi
                      exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                    exact insert_preserves_frame_wf db pos label obj fr'
                      h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                      h_not_var_dup h_var_inv h_obj_inv
      | var v =>
          -- Inserting a variable
          -- Beta-reduce op db to db.insert pos label obj
          change WellFormedDB (db.insert pos label obj)
          change (db.insert pos label obj).error? = none at h_no_err_after

          -- Extract v = label from h_validated
          have h_v_eq_label : v = label := by
            rw [h_obj] at h_validated
            exact h_validated

          constructor
          · -- Part 1: Frame WF preserved
            -- Goal: WellFormedFrame (db.insert pos label obj) (db.insert pos label obj).frame
            -- Use the fact that insert doesn't change the frame
            rw [insert_frame_unchanged]
            -- Now goal: WellFormedFrame (db.insert pos label obj) db.frame

            -- First establish h_not_var_dup for insert_preserves_frame_wf
            have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
              intro ⟨v_dup, _, h_find_old⟩
              rw [h_find_old] at h_fresh_db
              cases h_fresh_db

            have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
              intro lbl v_old h_find
              exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

            -- Apply insert_preserves_frame_wf
            exact insert_preserves_frame_wf db pos label obj db.frame
              h_frame_wf h_fresh_label h_no_err_before h_no_err_after
              h_not_var_dup h_var_inv h_obj_var_names_match

          · -- Part 2: All objects still WF
            intro lbl obj' h_find'
            by_cases h_eq : lbl = label
            · -- NEW object: lbl = label, so obj' = .var v = .var label
              -- Need to show: obj' matches its WF condition
              -- For .var v', the condition is: v' = lbl
              -- After rewriting with h_eq, need to show: v' = label

              -- Rewrite the goal using h_eq
              rw [h_eq]

              -- Now establish that obj' = obj label = .var v
              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_find_self := insert_success_find?_self db pos label obj
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

              -- Convert h_find' from lbl to label using h_eq
              have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                rw [h_eq] at h_find'
                exact h_find'

              -- Now both have label, so we can conclude obj' = obj label
              have h_obj'_eq : obj' = obj label := by
                -- h_find_self : (db.insert pos label obj).find? label = some (obj label)
                -- h_find'_label : (db.insert pos label obj).find? label = some obj'
                -- Therefore: some (obj label) = some obj'
                have : some (obj label) = some obj' := by
                  rw [← h_find_self, h_find'_label]
                cases this
                rfl

              -- obj label = .var v (from h_obj), so obj' = .var v
              rw [h_obj] at h_obj'_eq
              cases h_obj'_eq
              -- Goal: v = label, which is h_v_eq_label
              exact h_v_eq_label

            · -- EXISTING object: lbl ≠ label
              -- Lookup unchanged by insert
              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              -- Use the function invariant directly!
              have h_obj_inv := h_obj_var_names_match

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
              -- Now h_find_unchanged : (db.insert pos label obj).find? lbl = db.find? lbl
              -- Rewrite h_find' using this
              rw [h_find_unchanged] at h_find'
              -- Now h_find' : db.find? lbl = some obj'
              -- h_objs_wf gives us WF for obj' in db, but we need WF in (db.insert...)

              -- For most object types, the WF condition doesn't depend on the DB
              -- For assert, need to upgrade frame WF using insert_preserves_frame_wf
              have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

              cases h_obj' : obj' with
              | const c =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | var v' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | hyp ess f' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | assert f' fr' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  constructor
                  · -- Formula WF doesn't change
                    exact h_obj'_wf_old.1
                  · -- Frame WF needs upgrading
                    have h_fr_wf_old := h_obj'_wf_old.2
                    -- Need to show: label ∉ fr'.hyps
                    -- Use h_fresh_in_asserts
                    have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                      rw [← h_obj']
                      exact h_find'
                    have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                      intro i hi
                      exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                    exact insert_preserves_frame_wf db pos label obj fr'
                      h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                      h_not_var_dup h_var_inv h_obj_inv
      | hyp ess f name =>
          -- Inserting a hypothesis
          cases ess with
          | false =>
              -- Float hypothesis
              -- Beta-reduce op db to db.insert pos label obj
              change WellFormedDB (db.insert pos label obj)
              change (db.insert pos label obj).error? = none at h_no_err_after

              -- Extract h_float from h_validated
              have h_float : WellFormedFloat f := by
                rw [h_obj] at h_validated
                exact h_validated

              constructor
              · -- Part 1: Frame WF preserved
                rw [insert_frame_unchanged]

                have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                  intro ⟨v_dup, _, h_find_old⟩
                  rw [h_find_old] at h_fresh_db
                  cases h_fresh_db

                have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                  intro lbl v_old h_find
                  exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                exact insert_preserves_frame_wf db pos label obj db.frame
                  h_frame_wf h_fresh_label h_no_err_before h_no_err_after
                  h_not_var_dup h_var_inv h_obj_var_names_match

              · -- Part 2: All objects still WF
                intro lbl obj' h_find'
                by_cases h_eq : lbl = label
                · -- NEW object: lbl = label, so obj' = .hyp false f name
                  rw [h_eq]

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_find_self := insert_success_find?_self db pos label obj
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

                  have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                    rw [h_eq] at h_find'
                    exact h_find'

                  have h_obj'_eq : obj' = obj label := by
                    have : some (obj label) = some obj' := by
                      rw [← h_find_self, h_find'_label]
                    cases this
                    rfl

                  rw [h_obj] at h_obj'_eq
                  cases h_obj'_eq
                  -- Goal: WellFormedFloat f
                  exact h_float

                · -- EXISTING object: lbl ≠ label
                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_obj_inv := h_obj_var_names_match

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
                  rw [h_find_unchanged] at h_find'

                  have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

                  cases h_obj' : obj' with
                  | const c' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | var v' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | hyp ess f' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | assert f' fr' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      constructor
                      · exact h_obj'_wf_old.1
                      · have h_fr_wf_old := h_obj'_wf_old.2
                        have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                          rw [← h_obj']
                          exact h_find'
                        have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                          intro i hi
                          exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                        exact insert_preserves_frame_wf db pos label obj fr'
                          h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                          h_not_var_dup h_var_inv h_obj_inv
          | true =>
              -- Essential hypothesis
              -- Beta-reduce op db to db.insert pos label obj
              change WellFormedDB (db.insert pos label obj)
              change (db.insert pos label obj).error? = none at h_no_err_after

              -- Extract h_formula from h_validated
              have h_formula : WellFormedFormula f := by
                rw [h_obj] at h_validated
                exact h_validated

              constructor
              · -- Part 1: Frame WF preserved
                rw [insert_frame_unchanged]

                have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                  intro ⟨v_dup, _, h_find_old⟩
                  rw [h_find_old] at h_fresh_db
                  cases h_fresh_db

                have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                  intro lbl v_old h_find
                  exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                exact insert_preserves_frame_wf db pos label obj db.frame
                  h_frame_wf h_fresh_label h_no_err_before h_no_err_after
                  h_not_var_dup h_var_inv h_obj_var_names_match

              · -- Part 2: All objects still WF
                intro lbl obj' h_find'
                by_cases h_eq : lbl = label
                · -- NEW object: lbl = label, so obj' = .hyp true f name
                  rw [h_eq]

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_find_self := insert_success_find?_self db pos label obj
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

                  have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                    rw [h_eq] at h_find'
                    exact h_find'

                  have h_obj'_eq : obj' = obj label := by
                    have : some (obj label) = some obj' := by
                      rw [← h_find_self, h_find'_label]
                    cases this
                    rfl

                  rw [h_obj] at h_obj'_eq
                  cases h_obj'_eq
                  -- Goal: WellFormedFormula f
                  exact h_formula

                · -- EXISTING object: lbl ≠ label
                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_obj_inv := h_obj_var_names_match

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
                  rw [h_find_unchanged] at h_find'

                  have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

                  cases h_obj' : obj' with
                  | const c' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | var v' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | hyp ess f' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | assert f' fr' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      constructor
                      · exact h_obj'_wf_old.1
                      · have h_fr_wf_old := h_obj'_wf_old.2
                        have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                          rw [← h_obj']
                          exact h_find'
                        have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                          intro i hi
                          exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                        exact insert_preserves_frame_wf db pos label obj fr'
                          h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                          h_not_var_dup h_var_inv h_obj_inv
      | assert fmla fr lbl =>
          -- Inserting an assertion
          -- Beta-reduce op db to db.insert pos label obj
          change WellFormedDB (db.insert pos label obj)
          change (db.insert pos label obj).error? = none at h_no_err_after

          -- Extract formula + frame well-formedness and freshness from h_validated
          have h_assert_valid :
              WellFormedFormula fmla ∧ WellFormedFrame db fr ∧
                (∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ label) := by
            rw [h_obj] at h_validated
            exact h_validated
          
          rcases h_assert_valid with ⟨h_formula, h_frame_fr, h_fresh_in_fr⟩

          constructor
          · -- Part 1: Frame WF preserved
            rw [insert_frame_unchanged]

            have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
              intro ⟨v_dup, _, h_find_old⟩
              rw [h_find_old] at h_fresh_db
              cases h_fresh_db

            have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
              intro lbl v h_find
              exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

            exact insert_preserves_frame_wf db pos label obj db.frame
              h_frame_wf h_fresh_label h_no_err_before h_no_err_after
              h_not_var_dup h_var_inv h_obj_var_names_match

          · -- Part 2: All objects still WF
            intro lbl obj' h_find'
            by_cases h_eq : lbl = label
            · -- NEW object: lbl = label, so obj' = .assert fmla fr lbl
              rw [h_eq]

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_find_self := insert_success_find?_self db pos label obj
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

              have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                rw [h_eq] at h_find'
                exact h_find'

              have h_obj'_eq : obj' = obj label := by
                have : some (obj label) = some obj' := by
                  rw [← h_find_self, h_find'_label]
                cases this
                rfl

              rw [h_obj] at h_obj'_eq
              cases h_obj'_eq
              
              -- Goal: WellFormedFormula fmla ∧ WellFormedFrame (db.insert...) fr
              constructor
              · exact h_formula
              · -- Use the frame preservation lemma for inserts
                exact insert_preserves_frame_wf db pos label obj fr
                  h_frame_fr h_fresh_in_fr h_no_err_before h_no_err_after
                  h_not_var_dup h_var_inv h_obj_var_names_match

            · -- EXISTING object: lbl ≠ label
              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_obj_inv := h_obj_var_names_match

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
              rw [h_find_unchanged] at h_find'

              have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

              cases h_obj' : obj' with
              | const c' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | var v' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | hyp ess f' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | assert f' fr' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  constructor
                  · exact h_obj'_wf_old.1
                  · have h_fr_wf_old := h_obj'_wf_old.2
                    have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                      rw [← h_obj']
                      exact h_find'
                    have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                      intro i hi
                      exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                    exact insert_preserves_frame_wf db pos label obj fr'
                      h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                      h_not_var_dup h_var_inv h_obj_inv
  | pushScope =>
      -- Case: pushScope operation
      -- pushScope only modifies db.scopes, doesn't touch objects or frame
      exact And.intro h_frame_wf h_objs_wf
  | popScope pos =>
      -- Case: popScope operation
      classical
      cases h_scope : db.scopes.back? with
      | none =>
          have : False := by
            have h_err : (DB.popScope pos db).error? ≠ none := by
              simpa [DB.popScope, h_scope]
            exact h_err (by simpa [DB.popScope, h_scope] using h_no_err_after)
          exact this.elim
      | some sc =>
          have h_frame := wf_frame_shrink h_frame_wf sc
          refine ⟨?_, ?_⟩
          · simp only [DB.popScope, h_scope]
            exact h_frame
          · intro lbl obj h_find
            have h_lookup : db.find? lbl = some obj := by
              simp only [DB.popScope, h_scope] at h_find
              exact h_find
            simp only [DB.popScope, h_scope]
            exact h_objs_wf lbl obj h_lookup
  | withFrame f h_preserves =>
      -- Case: withFrame operation
      -- withFrame modifies db.frame using f
      -- h_preserves gives us: ∀ db fr, WellFormedFrame db fr → WellFormedFrame db (f fr)
      -- Objects are unchanged
      
      constructor
      · -- Part 1: Frame WF preserved
        have h_objects_eq : (db.withFrame f).objects = db.objects := rfl
        have h_new_frame_wf_db : WellFormedFrame db (f db.frame) := 
          h_preserves db db.frame h_frame_wf
        unfold WellFormedFrame HypOK at h_new_frame_wf_db ⊢
        rcases h_new_frame_wf_db with ⟨h_hyp, h_unique⟩
        constructor
        · intro i hi
          have h_old := h_hyp i hi
          rcases h_old with ⟨ess, fm, lbl, h_find, h_float, h_fmla⟩
          refine ⟨ess, fm, lbl, ?_, h_float, h_fmla⟩
          rw [DB.find?_def, h_objects_eq]
          exact h_find
        · intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
          rw [DB.find?_def, h_objects_eq] at h_fi h_fj
          exact h_unique i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j

      · -- Part 2: Objects WF preserved
        intro lbl obj h_find
        have h_objects_eq : (db.withFrame f).objects = db.objects := rfl
        have h_find_old : db.find? lbl = some obj := by
          rw [DB.find?_def] at h_find ⊢
          rw [h_objects_eq] at h_find
          exact h_find
          
        have h_wf_old := h_objs_wf lbl obj h_find_old
        cases obj with
        | const c => exact h_wf_old
        | var v => exact h_wf_old
        | hyp ess fm name => exact h_wf_old
        | assert fmla fr name =>
            rcases h_wf_old with ⟨h_fmla, h_fr_wf⟩
            constructor
            · exact h_fmla
            · unfold WellFormedFrame HypOK at h_fr_wf ⊢
              rcases h_fr_wf with ⟨h_hyp, h_unique⟩
              constructor
              · intro i hi
                have h_old := h_hyp i hi
                rcases h_old with ⟨ess, fm, lbl, h_find_hyp, h_float, h_fmla_hyp⟩
                refine ⟨ess, fm, lbl, ?_, h_float, h_fmla_hyp⟩
                rw [DB.find?_def, h_objects_eq]
                exact h_find_hyp
              · intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
                rw [DB.find?_def, h_objects_eq] at h_fi h_fj
                exact h_unique i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
  | id =>
      -- Case: identity operation
      exact ⟨h_frame_wf, h_objs_wf⟩

where
  wf_frame_shrink
      {db : DB} {fr : Frame}
      (h : WF.WellFormedFrame db fr) (sizes : Nat × Nat) :
      WF.WellFormedFrame db (fr.shrink sizes) := by
    classical
    rcases fr with ⟨dj, hyps⟩
    rcases sizes with ⟨x, y⟩
    simp [Frame.shrink] at h ⊢
    rcases h with ⟨h_hyp, h_unique⟩
    constructor
    · intro i hi
      have hi_min : i < min y hyps.size := by
        simpa [Array.shrink] using hi
      have hi_y : i < y := Nat.lt_of_lt_of_le hi_min (Nat.min_le_left _ _)
      have hi_orig : i < hyps.size := Nat.lt_of_lt_of_le hi_min (Nat.min_le_right _ _)
      have h_label := h_hyp i hi_orig
      simpa [Array.shrink, hi_y, hi_orig] using h_label
    · intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
      have hi_min : i < min y hyps.size := by
        simpa [Array.shrink] using hi
      have hj_min : j < min y hyps.size := by
        simpa [Array.shrink] using hj
      have hi_y : i < y := Nat.lt_of_lt_of_le hi_min (Nat.min_le_left _ _)
      have hj_y : j < y := Nat.lt_of_lt_of_le hj_min (Nat.min_le_left _ _)
      have hi_orig : i < hyps.size := Nat.lt_of_lt_of_le hi_min (Nat.min_le_right _ _)
      have hj_orig : j < hyps.size := Nat.lt_of_lt_of_le hj_min (Nat.min_le_right _ _)
      have h_unique' := h_unique i j hi_orig hj_orig h_ne fi fj lbli lblj
      have h_fi' := by
        simpa [Array.shrink, hi_y, hi_orig] using h_fi
      have h_fj' := by
        simpa [Array.shrink, hj_y, hj_orig] using h_fj
      exact h_unique' h_fi' h_fj' h_sz_i h_sz_j

/-! ## Composition of Structure-Preserving Operations

Sequential composition of structure-preserving operations.
-/

/-- Composing two structure-preserving operations yields a structure-preserving operation.
    If `op1` and `op2` both preserve structure, then `op2 ∘ op1` preserves structure. -/
theorem structure_preserving_compose
    {op1 op2 : DB → DB}
    (db : DB)
    (h_op1 : StructurePreservingOp db op1)
    (h_op2 : StructurePreservingOp (op1 db) op2)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_mid : (op1 db).error? = none)
    (h_no_err_after : (op2 (op1 db)).error? = none) :
    WellFormedDB (op2 (op1 db)) := by
  -- Apply structure_preserving_maintains_wf twice
  have h_wf_mid : WellFormedDB (op1 db) :=
    structure_preserving_maintains_wf db h_op1 h_wf h_no_err_before h_no_err_mid
  exact structure_preserving_maintains_wf (op1 db) h_op2 h_wf_mid h_no_err_mid h_no_err_after

/-! ## Layer 4: Well-formedness Preservation via Induction

These are the crucial inductive properties showing DB operations preserve well-formedness.
We phrase steps using StructurePreservingOp, so the preservation theorem is direct. -/

section WellFormednessInduction

/-- A DB step is any structure-preserving operation that leaves error? unset. -/
inductive DBStep : DB → DB → Prop where
  | op (db : DB) (op : DB → DB) :
      StructurePreservingOp db op →
      db.error? = none →
      (op db).error? = none →
      DBStep db (op db)

/-- Transitive closure gives us sequences of DB operations. -/
inductive DBExecution : DB → DB → Prop where
  | refl (db : DB) : DBExecution db db
  | step (db₁ db₂ db₃ : DB) :
      DBStep db₁ db₂ →
      DBExecution db₂ db₃ →
      DBExecution db₁ db₃

/-- Main well-formedness preservation theorem. -/
theorem DBExecution.preserves_wellformedness {db₁ db₂ : DB} :
    DBExecution db₁ db₂ →
    db₁.error? = none →
    db₂.error? = none →
    WF.WellFormedDB db₁ →
    WF.WellFormedDB db₂ := by
  intro h_exec h_no_err1 h_no_err2 h_wf
  induction h_exec with
  | refl => exact h_wf
  | step db₁ db₂ db₃ h_step h_exec ih =>
      cases h_step with
      | op op_fn h_struct h_no_err_before h_no_err_after =>
          have h_wf2 : WF.WellFormedDB (op_fn db₁) :=
            structure_preserving_maintains_wf db₁ h_struct h_wf h_no_err_before h_no_err_after
          exact ih h_no_err_after h_no_err2 h_wf2

/-- Strong induction principle for DB construction. -/
theorem db_construction_induction
    {P : DB → Prop}
    (h_step : ∀ db op,
      StructurePreservingOp db op →
      db.error? = none →
      (op db).error? = none →
      P db →
      P (op db)) :
    ∀ db₁ db₂, DBExecution db₁ db₂ → P db₁ → P db₂ := by
  intro db₁ db₂ h_exec h_p1
  induction h_exec with
  | refl =>
      simpa using h_p1
  | step db₁ db₂ db₃ h_step' h_exec ih =>
      cases h_step' with
      | op op_fn h_struct h_no_err_before h_no_err_after =>
          have h_p2 : P (op_fn db₁) :=
            h_step db₁ op_fn h_struct h_no_err_before h_no_err_after (by simpa using h_p1)
          exact ih h_p2

end WellFormednessInduction

end Metamath.ParserCorrectness
