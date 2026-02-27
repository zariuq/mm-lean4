import Metamath.Verify
import Metamath.VerifyParserPostThms

namespace Metamath
namespace Verify

namespace ParserState

theorem label_invalidLabel_errorCode_implies_toLabel_false
    (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (h_no_err : s.db.error? = none) :
    (s.label pos tk).db.parseErrorCode? = some .invalidLabel →
      (toLabel tk).fst = false := by
  intro h_code
  unfold ParserState.label at h_code
  cases h_lbl : toLabel tk with
  | mk ok lbl =>
      cases h_ok : ok with
      | true =>
          simp [h_lbl, h_ok, h_no_err, DB.parseErrorCode?] at h_code
      | false =>
          simp

theorem done_preserves_existing_parseErrorCode
    (s : ParserState) (base : Nat) (code : ParseErrorCode)
    (h_prev : s.db.parseErrorCode? = some code) :
    (s.done base).parseErrorCode? = some code := by
  have h_err_some : s.db.error?.isSome = true := by
    unfold DB.parseErrorCode? at h_prev
    cases h_err : s.db.error? with
    | none =>
        simp [h_err] at h_prev
    | some intr =>
        simp
  have h_done : s.done base = s.db := by
    unfold ParserState.done
    simp [h_err_some, DB.error, Id.run, Pure.pure]
  simpa [h_done] using h_prev

end ParserState

theorem checkBytes_internalGate_violation
    (arr : ByteArray) (config : ModeConfig)
    (h_none : (checkBytesCore arr config).error? = none)
    (h_code : (checkBytes arr config).parseErrorCode? = some .internalIllFormedDatabaseAfterParse) :
      ( (¬ (checkBytesCore arr config).config.allowDuplicateFloat ∧
          (checkBytesCore arr config).wellFormed? = false)
        ∨ (checkBytesCore arr config).assertDvVarsInFrame? = false ) := by
  unfold checkBytes at h_code
  let db := checkBytesCore arr config
  have h_none' : db.error? = none := by
    simpa [db] using h_none
  have h_code' :
      (if (db.config.allowDuplicateFloat || db.wellFormed?) && db.assertDvVarsInFrame?
        then db
        else db.mkErrorFromEvidence ⟨0, 0⟩
          (.internalGate db.config.allowDuplicateFloat db.wellFormed? db.assertDvVarsInFrame?)).parseErrorCode? =
        some .internalIllFormedDatabaseAfterParse := by
    simpa [db, h_none'] using h_code
  let A := db.config.allowDuplicateFloat
  let WF := db.wellFormed?
  let B := db.assertDvVarsInFrame?
  have h_code'' :
      (if (A || WF) && B
        then db
        else db.mkErrorFromEvidence ⟨0, 0⟩ (.internalGate A WF B)).parseErrorCode? =
        some .internalIllFormedDatabaseAfterParse := by
    simpa [A, WF, B] using h_code'
  by_cases h_gate : (A || WF) && B
  · have h_db_code : db.parseErrorCode? = some .internalIllFormedDatabaseAfterParse := by
      simpa [h_gate] using h_code''
    have h_db_none : db.parseErrorCode? = none := by
      simp [DB.parseErrorCode?, h_none']
    have : False := by
      simp [h_db_none] at h_db_code
    exact False.elim this
  · cases hAorWF : (A || WF) <;> cases hB : B
    · exact Or.inr (by simpa [B, db] using hB)
    · cases hA : A <;> cases hWF : WF
      · have hAne : ¬ A = true := by
          simp [hA]
        exact Or.inl ⟨by simpa [A, db] using hAne, by simpa [WF, db] using hWF⟩
      · simp [hA, hWF] at hAorWF
      · simp [hA, hWF] at hAorWF
      · simp [hA, hWF] at hAorWF
    · exact Or.inr (by simpa [B, db] using hB)
    · have h_true : ((A || WF) && B) = true := by
        simp [hAorWF, hB]
      exact (h_gate h_true).elim

theorem checkBytesCore_preserves_feedAll_parseErrorCode
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code :
      (({ (default : ParserState) with db := { (default : DB) with config := config } }).feedAll 0 arr).db.parseErrorCode? = some code) :
    (checkBytesCore arr config).parseErrorCode? = some code := by
  unfold checkBytesCore
  let initialDB : DB := { (default : DB) with config := config }
  let initialState : ParserState := { (default : ParserState) with db := initialDB }
  have h_done :
      ((initialState.feedAll 0 arr).done arr.size).parseErrorCode? = some code := by
    exact ParserState.done_preserves_existing_parseErrorCode
      (s := initialState.feedAll 0 arr) (base := arr.size) (code := code)
      (by simpa [initialState, initialDB] using h_code)
  simpa [initialState, initialDB] using h_done

theorem checkBytes_preserves_checkBytesCore_parseErrorCode
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code : (checkBytesCore arr config).parseErrorCode? = some code) :
    (checkBytes arr config).parseErrorCode? = some code := by
  unfold checkBytes
  by_cases h_none : (checkBytesCore arr config).error? = none
  · exfalso
    simp [DB.parseErrorCode?, h_none] at h_code
  · simp [h_none, h_code]

theorem checkBytes_preserves_feedAll_parseErrorCode
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code :
      (({ (default : ParserState) with db := { (default : DB) with config := config } }).feedAll 0 arr).db.parseErrorCode? = some code) :
    (checkBytes arr config).parseErrorCode? = some code := by
  exact checkBytes_preserves_checkBytesCore_parseErrorCode arr config code
    (checkBytesCore_preserves_feedAll_parseErrorCode arr config code h_code)

theorem checkBytes_no_error_wellFormed?
    (arr : ByteArray) (config : ModeConfig := {}) :
    config.allowDuplicateFloat = false →
    (checkBytes arr config).error? = none →
    (checkBytes arr config).wellFormed? = true := by
  intro h_no_dup h_ok
  simp only [checkBytes] at h_ok ⊢
  have h_dup : (checkBytesCore arr config).config.allowDuplicateFloat = false := by
    simp only [checkBytesCore_config, h_no_dup]
  by_cases h_err : (checkBytesCore arr config).error? = none
  · simp only [h_err, ↓reduceIte] at h_ok ⊢
    by_cases h_wf : (checkBytesCore arr config).wellFormed? = true
    · have h_assert : (checkBytesCore arr config).assertDvVarsInFrame? = true := by
        by_cases h_a : (checkBytesCore arr config).assertDvVarsInFrame? = true
        · exact h_a
        · simp [h_wf, h_a, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at h_ok
      simp only [h_wf, Bool.or_true, h_assert, Bool.true_and, ↓reduceIte]
    · have h_cond :
          (((checkBytesCore arr config).config.allowDuplicateFloat ||
              (checkBytesCore arr config).wellFormed?) &&
            (checkBytesCore arr config).assertDvVarsInFrame?) = false := by
        cases h : (checkBytesCore arr config).wellFormed? with
        | true => exact (h_wf h).elim
        | false => simp only [h_dup, Bool.false_or, Bool.false_and]
      simp only [h_cond, Bool.false_eq_true, ↓reduceIte, DB.mkErrorFromEvidence] at h_ok
      cases h_ok
  · simp [h_err] at h_ok

theorem checkBytes_no_error_assertDvVarsInFrame?
    (arr : ByteArray) (config : ModeConfig := {}) :
    (checkBytes arr config).error? = none →
    (checkBytes arr config).assertDvVarsInFrame? = true := by
  intro h_ok
  by_cases h_err : (checkBytesCore arr config).error? = none
  · simp [checkBytes, h_err] at h_ok ⊢
    by_cases h_assert : (checkBytesCore arr config).assertDvVarsInFrame? = true
    · by_cases h_gate : config.allowDuplicateFloat = true ∨ (checkBytesCore arr config).wellFormed? = true
      · simp [h_gate, h_assert]
      · have h_mk :
            ((checkBytesCore arr config).mkErrorFromEvidence ⟨0, 0⟩
              (.internalGate (checkBytesCore arr config).config.allowDuplicateFloat
                (checkBytesCore arr config).wellFormed?
                (checkBytesCore arr config).assertDvVarsInFrame?)).assertDvVarsInFrame? =
              (checkBytesCore arr config).assertDvVarsInFrame? := by
            rfl
        have h_cond_false :
            ((config.allowDuplicateFloat = true ∨ (checkBytesCore arr config).wellFormed? = true) ∧
              (checkBytesCore arr config).assertDvVarsInFrame? = true) = false := by
          simp [h_gate, h_assert]
        have h_mk_true :
            ((checkBytesCore arr config).mkErrorFromEvidence ⟨0, 0⟩
              (.internalGate (checkBytesCore arr config).config.allowDuplicateFloat
                (checkBytesCore arr config).wellFormed?
                (checkBytesCore arr config).assertDvVarsInFrame?)).assertDvVarsInFrame? = true := by
            simpa [h_mk] using h_assert
        simpa [h_cond_false] using h_mk_true
    · simp [h_assert, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at h_ok
  · simp [checkBytes, h_err] at h_ok

end Verify
end Metamath
