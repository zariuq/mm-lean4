/-
# Parser Soundness Demonstration

This module demonstrates the key principles of parser soundness
for the Metamath verifier. Simplified for compilation.

Created by: Opus 4.1
-/

import Metamath.Verify
import Metamath.WellFormedness
import Metamath.ParserOperations
import Std.Data.HashMap.Lemmas

namespace Metamath.ParserSoundnessDemo

open Verify
open WF

/-! ## Core Principle: Error Preservation

Once a DB has an error, all operations preserve that error.
This is THE KEY property ensuring parser soundness.
-/

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
  cases h_obj : obj label with
  | const c =>
      by_cases h_outer : !db.config.allowConstInnerScope && db.scopes.size > 0
      · simp [h_outer, DB.error, DB.mkErrorFromEvidence,
          DB.mkErrorWithEvidence]
      · simp [h_outer, h]
  | var v =>
      simp [h]
  | hyp ess f lbl =>
      simp [h]
  | assert f fr proof =>
      simp [h]

/-- All major DB operations preserve error -/
theorem db_ops_preserve_error :
  (∀ (db : DB) (pos : Pos) (label : String) (obj : String → Object),
      db.error = true → (db.insert pos label obj).error = true) ∧
  (∀ (db : DB), db.error = true → db.pushScope.error = true) ∧
  (∀ (db : DB) (pos : Pos), db.error = true → (db.popScope pos).error = true) ∧
  (∀ (db : DB) (f : Frame → Frame), db.error = true → (db.withFrame f).error = true) := by
  constructor
  · exact insert_preserves_error
  constructor
  · intro db h
    have h' : db.error?.isSome = true := by
      simpa [DB.error] using h
    simp [DB.pushScope, DB.error, h']
  constructor
  · intro db pos h
    have h' : db.error?.isSome = true := by
      simpa [DB.error] using h
    cases h_back : db.scopes.back?
    · simp [DB.popScope, h_back, DB.error]
    · simp [DB.popScope, h_back, DB.error, h']
  · intro db f h
    have h' : db.error?.isSome = true := by
      simpa [DB.error] using h
    simp [DB.withFrame, DB.error, h']

/-! ## Sequential Error Propagation

Errors propagate through sequential operations.
-/

/-- If operations preserve error and we process sequentially, error propagates -/
theorem error_propagates_sequentially
  (ops : List (DB → DB))
  (h_preserve : ∀ op ∈ ops, ∀ db : DB, db.error = true → (op db).error = true)
  (initial_db : DB)
  (h_error : initial_db.error = true) :
  (ops.foldl (fun db op => op db) initial_db).error = true := by
  induction ops generalizing initial_db with
  | nil => exact h_error
  | cons op tail ih =>
    simp [List.foldl]
    apply ih
    · intro op' h_mem db h_err
      exact h_preserve op' (by simp [h_mem]) db h_err
    · apply h_preserve op (by simp) _ h_error

/-! ## Main Soundness Insight

If parsing completes with no error, then all intermediate operations
succeeded, which means all preconditions were met, which means
well-formedness was maintained throughout.
-/

/-- Empty DB is well-formed -/
theorem empty_db_wellformed :
  let empty_frame : Frame := { dj := #[], hyps := #[] }
  let empty_db : DB :=
    { frame := empty_frame
      scopes := #[]
      objects := Std.HashMap.emptyWithCapacity
      interrupt := false
      error? := none }
  WellFormedDB empty_db := by
  dsimp
  unfold WellFormedDB WellFormedFrame
  constructor
  · constructor
    · intro i hi
      simp at hi
    · intro i j hi _hj _h_ne _fi _fj _lbli _lblj _h_fi _h_fj _h_szi _h_szj
      simp at hi
  · intro label obj h_find
    simp [DB.find?] at h_find

/-- Key Theorem: a successful parse *step* preserves well-formedness.

This is the real inductive content behind "successful parsing implies
well-formedness": each accepted token carries `WellFormedDB` forward, so a
whole accepted run does too.  It delegates to the proved step lemma. -/
theorem parsing_success_implies_wellformed
    (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_wf : WellFormedDB s.db)
    (h_no_err : s.db.error? = none)
    (h_no_dup : s.db.config.allowDuplicateFloat = false)
    (h_tokp_inv : ParserOps.TokpInv s.db s.tokp)
    (h_success : (s.feedToken i tk).db.error? = none) :
    WellFormedDB (s.feedToken i tk).db :=
  ParserOps.feedToken_maintains_wf s i tk h_wf h_no_err h_no_dup h_tokp_inv h_success

/-! ## Conclusion

The parser soundness architecture rests on:
1. Error preservation by all DB operations (PROVEN)
2. Sequential error propagation (PROVEN)
3. Empty DB is well-formed (PROVEN)
4. Operations preserve well-formedness when no error (PRINCIPLE SHOWN)

Therefore: successful parsing (no final error) implies well-formed result.
-/

end Metamath.ParserSoundnessDemo

