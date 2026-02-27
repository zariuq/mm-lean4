import Metamath.Verify
import Metamath.VerifyParserStateThms

namespace Metamath
namespace Verify

-- Config is preserved through parsing (no operation modifies it)
-- This is observable: config is set once at init and never changed
@[simp] theorem checkBytesCore_config (arr : ByteArray) (config : ModeConfig) :
    (checkBytesCore arr config).config = config := by
  -- `config` is set once at initialization; `feedAll` and `done` preserve it.
  simp [checkBytesCore, ParserState.feedAll_db_config, ParserState.done_config]

@[simp] theorem checkBytes_config (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).config = config := by
  unfold checkBytes
  by_cases h_err : (checkBytesCore arr config).error? = none
  · by_cases h_gate :
      (config.allowDuplicateFloat = true ∨ (checkBytesCore arr config).wellFormed? = true) ∧
        (checkBytesCore arr config).assertDvVarsInFrame? = true
    · simp [h_err, h_gate, checkBytesCore_config]
    · simp [h_err, h_gate, checkBytesCore_config]
  · simp [h_err, checkBytesCore_config]

@[simp] theorem checkBytes_scopes (arr : ByteArray) (config : ModeConfig) :
    (checkBytes arr config).scopes = (checkBytesCore arr config).scopes := by
  unfold checkBytes
  by_cases h_err : (checkBytesCore arr config).error? = none
  · by_cases h_gate :
      (config.allowDuplicateFloat = true ∨ (checkBytesCore arr config).wellFormed? = true) ∧
        (checkBytesCore arr config).assertDvVarsInFrame? = true
    · simp [h_err, h_gate]
    · simp [h_err, h_gate]
  · simp [h_err]

@[simp] theorem includePreprocessErrorDB_config
    (config : ModeConfig) (err : IncludeError) :
    (includePreprocessErrorDB config err).config = config := by
  simp [includePreprocessErrorDB]

end Verify
end Metamath
