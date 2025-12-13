/-
# DB Operation Lemmas

Supporting lemmas for database operations that are used throughout the verification.
These lemmas establish basic properties of mkError, find?, withHyps, etc.
-/

import Metamath.Verify

namespace Metamath.DBLemmas

open Verify

/-! ## mkError lemmas -/

/-- mkError sets the error flag to true -/
theorem mkError_sets_error (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).error = true := by
  unfold DB.mkError DB.error
  simp

/-- mkError preserves the error flag when already set -/
theorem mkError_preserves_error (db : DB) (pos : Pos) (msg : String)
    (_h : db.error = true) :
    (db.mkError pos msg).error = true := by
  unfold DB.mkError DB.error
  simp

/-- mkError makes error? non-none -/
theorem mkError_error?_some (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).error? = some ⟨.error pos msg, default⟩ := by
  unfold DB.mkError
  rfl

/-- After mkError, error? is not none -/
theorem mkError_error?_ne_none (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).error? ≠ none := by
  rw [mkError_error?_some]
  simp

/-! ## DB.find? preservation lemmas -/

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

/-- mkError doesn't change the frame -/
theorem mkError_preserves_frame (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).frame = db.frame := by
  unfold DB.mkError
  rfl

/-- mkError doesn't change the scopes -/
theorem mkError_preserves_scopes (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).scopes = db.scopes := by
  unfold DB.mkError
  rfl

/-- mkError doesn't change the permissive flag -/
theorem mkError_preserves_permissive (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).permissive = db.permissive := by
  unfold DB.mkError
  rfl

/-! ## withHyps lemmas -/

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

/-- withHyps doesn't change objects -/
theorem withHyps_preserves_objects (db : DB) (f : Array String → Array String) :
    (db.withHyps f).objects = db.objects := by
  unfold DB.withHyps DB.withFrame
  rfl

/-- withHyps doesn't change find? results -/
theorem withHyps_preserves_find? (db : DB) (f : Array String → Array String) (label : String) :
    (db.withHyps f).find? label = db.find? label := by
  unfold DB.find?
  rw [withHyps_preserves_objects]

/-- withHyps doesn't change the DJ constraints -/
theorem withHyps_preserves_dj (db : DB) (f : Array String → Array String) :
    (db.withHyps f).frame.dj = db.frame.dj := by
  unfold DB.withHyps DB.withFrame
  rfl

/-! ## insert lemmas -/

/-- insert with error already set keeps error = true -/
theorem insert_with_error (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h : db.error = true) :
    (db.insert pos label obj).error = true := by
  unfold DB.insert DB.error at *
  split
  · -- const case
    split
    · -- mkError called
      simp [DB.mkError]
    · -- no mkError
      simp [*]
  · -- non-const case
    simp [*]

/-- When insert succeeds (no error), it updates objects -/
theorem insert_success_updates_objects (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h_no_error : db.error = false)
    (h_no_dup : db.find? label = none)
    (h_not_const_inner : ¬(match obj label with | .const _ => !db.permissive && db.scopes.size > 0 | _ => false)) :
    (db.insert pos label obj).objects = db.objects.insert label (obj label) := by
  -- Need to prove that insert doesn't error, then use DB.insert_no_dup_objects
  -- The h_not_const_inner hypothesis ensures the const check doesn't fail
  have h_no_err_after : (db.insert pos label obj).error = false := by
    unfold DB.insert DB.error at *
    split
    · -- const case
      split
      · -- const check fails - contradicts h_not_const_inner
        exfalso
        apply h_not_const_inner
        simp_all
      · -- const check passes - db unchanged, continue with if-then-else
        simp_all
    · -- non-const case - db unchanged, continue with if-then-else
      simp_all
  exact DB.insert_no_dup_objects db pos label obj h_no_error h_no_dup h_no_err_after

/-- When insert succeeds, find? label returns the inserted object -/
theorem insert_success_find? (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h_no_error : db.error = false)
    (h_no_dup : db.find? label = none)
    (h_not_const_inner : ¬(match obj label with | .const _ => !db.permissive && db.scopes.size > 0 | _ => false)) :
    (db.insert pos label obj).find? label = some (obj label) := by
  -- Prove that insert doesn't error, then use DB.insert_find?_self
  have h_no_err_after : (db.insert pos label obj).error = false := by
    unfold DB.insert DB.error at *
    split
    · -- const case
      split
      · exfalso; apply h_not_const_inner; simp_all
      · simp_all
    · simp_all
  exact DB.insert_find?_self db pos label obj h_no_error h_no_dup h_no_err_after

/-- insert preserves error=false when no error conditions -/
theorem insert_preserves_no_error (db : DB) (pos : Pos) (label : String) (obj : String → Object)
    (h_no_error : db.error = false)
    (h_no_dup : db.find? label = none)
    (h_not_const_inner : ¬(match obj label with | .const _ => !db.permissive && db.scopes.size > 0 | _ => false)) :
    (db.insert pos label obj).error = false := by
  unfold DB.insert DB.error at *
  split
  · -- const case
    split
    · -- const check fails - contradicts h_not_const_inner
      exfalso
      apply h_not_const_inner
      simp_all
    · -- const check passes
      simp_all
  · -- non-const case
    simp_all

end Metamath.DBLemmas
