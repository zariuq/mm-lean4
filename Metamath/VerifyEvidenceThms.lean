import Metamath.Verify
import Metamath.VerifyDBThms

namespace Metamath
namespace Verify

/-- Any decoded `checkBytes` parser code carries concrete error evidence. -/
theorem checkBytes_parseErrorCode?_has_evidence
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode) :
    (checkBytes arr config).parseErrorCode? = some code →
    ∃ ev, (checkBytes arr config).errorEvidence? = some ev := by
  intro h_code
  rcases DB.parseErrorCode?_sound (s := checkBytes arr config) code h_code with
    ⟨_pos, _msg, _idx, ev, _h_err, h_ev, _h_ev_code⟩
  exact ⟨ev, h_ev⟩

/-- Any decoded parser code in an arbitrary DB carries concrete error evidence. -/
theorem parseErrorCode?_has_evidence
    (s : DB) (code : ParseErrorCode) :
    s.parseErrorCode? = some code →
    ∃ ev, s.errorEvidence? = some ev := by
  intro h_code
  rcases DB.parseErrorCode?_sound s code h_code with
    ⟨_pos, _msg, _idx, ev, _h_err, h_ev, _h_ev_code⟩
  exact ⟨ev, h_ev⟩

theorem DB.parseErrorCode?_eq_none_of_error?_none (s : DB)
    (h_no_err : s.error? = none) :
    s.parseErrorCode? = none := by
  simp [DB.parseErrorCode?, h_no_err]

/-- Any evidence in `mkError`-compat format decodes to the internal consistency code. -/
theorem parseErrorCode?_eq_internal_of_internalGate_false_false_false
    (s : DB)
    (h_ev : s.errorEvidence? = some (.internalGate false false false))
    (h_err : s.error? = some ⟨.error pos msg, idx⟩) :
    s.parseErrorCode? = some .internalIllFormedDatabaseAfterParse := by
  simp [DB.parseErrorCode?, h_err, h_ev, ErrorEvidence.code]

/-- Decoding a non-internal code excludes the legacy `mkError`-compat evidence payload. -/
theorem parseErrorCode?_nonInternal_excludes_internalGate_false_false_false
    (s : DB) (code : ParseErrorCode)
    (h_code : s.parseErrorCode? = some code)
    (h_noninternal : code ≠ .internalIllFormedDatabaseAfterParse) :
    s.errorEvidence? ≠ some (.internalGate false false false) := by
  intro h_ev
  rcases DB.parseErrorCode?_sound s code h_code with
    ⟨_pos, _msg, _idx, ev, _h_err, h_ev_some, h_ev_code⟩
  have h_ev_eq : ev = .internalGate false false false := by
    have h_some_eq : some ev = some (.internalGate false false false) := by
      exact h_ev_some.symm.trans h_ev
    exact Option.some.inj h_some_eq
  have h_code_internal : code = .internalIllFormedDatabaseAfterParse := by
    simpa [h_ev_eq, ErrorEvidence.code] using h_ev_code.symm
  exact h_noninternal h_code_internal

/-- `checkBytes` non-internal decoded codes are evidence-first and exclude legacy raw-error payloads. -/
theorem checkBytes_nonInternal_excludes_internalGate_false_false_false
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code : (checkBytes arr config).parseErrorCode? = some code)
    (h_noninternal : code ≠ .internalIllFormedDatabaseAfterParse) :
    (checkBytes arr config).errorEvidence? ≠ some (.internalGate false false false) := by
  exact parseErrorCode?_nonInternal_excludes_internalGate_false_false_false
    (s := checkBytes arr config) code h_code h_noninternal

/-- Evidence-first invariant: decoded non-internal `checkBytes` rejections always carry
non-legacy structured evidence (never the raw `mkError` compatibility payload). -/
theorem checkBytes_nonInternal_evidenceFirst
    (arr : ByteArray) (config : ModeConfig) (code : ParseErrorCode)
    (h_code : (checkBytes arr config).parseErrorCode? = some code)
    (h_noninternal : code ≠ .internalIllFormedDatabaseAfterParse) :
    ∃ ev,
      (checkBytes arr config).errorEvidence? = some ev ∧
      ev ≠ .internalGate false false false := by
  rcases checkBytes_parseErrorCode?_has_evidence arr config code h_code with ⟨ev, h_ev⟩
  refine ⟨ev, h_ev, ?_⟩
  intro h_ev_internal
  have h_legacy_excluded :
      (checkBytes arr config).errorEvidence? ≠ some (.internalGate false false false) :=
    checkBytes_nonInternal_excludes_internalGate_false_false_false
      arr config code h_code h_noninternal
  exact h_legacy_excluded (h_ev.trans (by simp [h_ev_internal]))

/-- Generic evidence-first invariant: decoded non-internal parser errors always carry
non-legacy structured evidence (never the raw `mkError` compatibility payload). -/
theorem parseErrorCode?_nonInternal_evidenceFirst
    (s : DB) (code : ParseErrorCode)
    (h_code : s.parseErrorCode? = some code)
    (h_noninternal : code ≠ .internalIllFormedDatabaseAfterParse) :
    ∃ ev, s.errorEvidence? = some ev ∧ ev ≠ .internalGate false false false := by
  rcases parseErrorCode?_has_evidence (s := s) code h_code with
    ⟨ev, h_ev⟩
  refine ⟨ev, h_ev, ?_⟩
  intro h_ev_internal
  have h_legacy_excluded :
      s.errorEvidence? ≠ some (.internalGate false false false) :=
    parseErrorCode?_nonInternal_excludes_internalGate_false_false_false
      (s := s) code h_code h_noninternal
  exact h_legacy_excluded (h_ev.trans (by simp [h_ev_internal]))

end Verify
end Metamath
