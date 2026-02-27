import Metamath.Verify

namespace Metamath
namespace Verify
namespace DB

@[simp] theorem default_config : (default : DB).config = {} := by
  rfl

@[simp] theorem mkError_eq_mkErrorWithEvidence_internalGate
    (s : DB) (pos : Pos) (msg : String) :
    s.mkError pos msg = s.mkErrorWithEvidence pos msg (.internalGate false false false) := rfl

@[simp] theorem mkError_config (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).config = s.config := rfl

@[simp] theorem mkError_error?_isSome (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).error?.isSome = true := rfl

@[simp] theorem mkError_errorEvidence? (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).errorEvidence? = some (.internalGate false false false) := rfl

@[simp] theorem mkError_error (s : DB) (pos : Pos) (msg : String) :
    (s.mkError pos msg).error = true := rfl

@[simp] theorem mkParseError_config (s : DB) (pos : Pos) (err : DoneModeError) :
    (s.mkParseError pos err).config = s.config := by
  simp [mkParseError, mkErrorFromEvidence, mkErrorWithEvidence]

@[simp] theorem mkParseError_error?_isSome (s : DB) (pos : Pos) (err : DoneModeError) :
    (s.mkParseError pos err).error?.isSome = true := by
  simp [mkParseError, mkErrorFromEvidence, mkErrorWithEvidence]

@[simp] theorem mkErrorWithEvidence_config (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).config = s.config := rfl

@[simp] theorem mkErrorWithEvidence_error?_isSome (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).error?.isSome = true := rfl

@[simp] theorem mkErrorWithEvidence_frame (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).frame = s.frame := rfl

@[simp] theorem mkErrorWithEvidence_scopes (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).scopes = s.scopes := rfl

@[simp] theorem mkErrorWithEvidence_objects (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).objects = s.objects := rfl

@[simp] theorem mkErrorWithEvidence_interrupt (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).interrupt = s.interrupt := rfl

@[simp] theorem mkErrorWithEvidence_error (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).error = true := by
  rfl

@[simp] theorem mkErrorWithEvidence_error? (s : DB) (pos : Pos) (msg : String) (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).error? ≠ none := by
  simp [mkErrorWithEvidence]

@[simp] theorem mkErrorFromEvidence_frame (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).frame = s.frame := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_scopes (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).scopes = s.scopes := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_objects (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).objects = s.objects := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_interrupt (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).interrupt = s.interrupt := by
  simp [mkErrorFromEvidence]

@[simp] theorem mkErrorFromEvidence_error? (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).error? ≠ none := by
  simp [mkErrorFromEvidence, mkErrorWithEvidence]

@[simp] theorem mkErrorFromEvidence_config (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).config = s.config := by
  unfold DB.mkErrorFromEvidence DB.mkErrorWithEvidence
  rfl

@[simp] theorem mkErrorFromEvidence_error?_isSome (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).error?.isSome = true := by
  unfold DB.mkErrorFromEvidence DB.mkErrorWithEvidence
  simp

@[simp] theorem mkErrorFromEvidence_error (s : DB) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).error = true := by
  simp [mkErrorFromEvidence, DB.error, mkErrorWithEvidence]

@[simp] theorem mkParseError_errorEvidence? (s : DB) (pos : Pos) (err : DoneModeError) :
    (s.mkParseError pos err).errorEvidence? = some (.doneMode err) := by
  simp [mkParseError, mkErrorFromEvidence, mkErrorWithEvidence]

@[simp] theorem withFrame_config (f : Frame → Frame) (s : DB) : (s.withFrame f).config = s.config := rfl

@[simp] theorem pushScope_config (s : DB) : (s.pushScope).config = s.config := rfl

@[simp] theorem popScope_config (pos : Pos) (s : DB) : (s.popScope pos).config = s.config := by
  unfold popScope
  cases h : s.scopes.back? <;> simp [DB.mkErrorFromEvidence_config]

@[simp] theorem withDJ_config (f : Array DJ → Array DJ) (s : DB) : (s.withDJ f).config = s.config := rfl

@[simp] theorem withHyps_config (f : Array String → Array String) (s : DB) : (s.withHyps f).config = s.config := rfl

@[simp] theorem insert_config (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).config = db.config := by
  unfold insert
  repeat (first | split | simp [DB.mkErrorFromEvidence_config] | rfl)

@[simp] theorem insertHypChecks_config (db : DB) (pos : Pos) (ess : Bool) (f : Formula) :
    (db.insertHypChecks pos ess f).config = db.config := by
  unfold insertHypChecks
  by_cases h_head : f.hasConstHead
  · simp [h_head]
    cases h_err : db.error with
    | true =>
        simp
    | false =>
        simp
        cases h_ess : ess with
        | true =>
            simp
            by_cases h_syms : formulaSymsRespectFrame db f (Frame.mk #[] db.frame.hyps)
            · simp [h_syms]
            · simp [h_syms, DB.mkErrorFromEvidence_config]
        | false =>
            simp
            by_cases h_shape : f.isFloatShape
            · simp [h_shape]
              by_cases h_size : f.size >= 2
              · simp [h_size]
                by_cases h_dup :
                  db.config.allowDuplicateFloat = false ∧
                    db.floatVarOccursInFrame f[1]!.value = true
                · simp [h_err, h_dup, DB.mkErrorFromEvidence_config]
                · simp [h_err, h_dup]
              · simp [h_size]
            · simp [h_shape, DB.error, DB.mkErrorFromEvidence_config]
  · simp [h_head, DB.error, DB.mkErrorFromEvidence_config]

@[simp] theorem insertHyp_config (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) :
    (db.insertHyp pos l ess f).config = db.config := by
  unfold insertHyp
  simp only [DB.error]
  split <;> try simp [DB.insertHypChecks_config]
  split <;> simp [DB.insertHypChecks_config, DB.insert_config, DB.withHyps_config]

@[simp] theorem insertAxiom_config (db : DB) (pos : Pos) (l : String) (fmla : Formula) :
    (db.insertAxiom pos l fmla).config = db.config := by
  unfold insertAxiom
  by_cases h_head : fmla.hasConstHead
  · simp only [h_head, ↓reduceIte, DB.error]
    split
    · simp
    ·
      cases h_trim : db.trimFrame' fmla with
      | error msg => simp [DB.mkErrorFromEvidence_config]
      | ok fr =>
        simp only []
        split
        · simp
        · simp [DB.insert_config]
  ·
    simp only [h_head, Bool.false_eq_true, ↓reduceIte, DB.error, DB.mkErrorFromEvidence_config,
      DB.mkErrorFromEvidence_error?_isSome]

end DB
end Verify
end Metamath
