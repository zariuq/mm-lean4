import Metamath.Verify

namespace Metamath
namespace Verify

/-- Pure boundary after include expansion.
Maps expanded bytes to `checkBytes` and include-preprocess failures to
`includePreprocessErrorDB`. -/
def checkExpandedResult (config : ModeConfig)
    (expanded : Except IncludeError (ByteArray × Std.HashSet String)) : DB :=
  match expanded with
  | .error err => includePreprocessErrorDB config err
  | .ok (processed, _) => checkBytes processed config

end Verify
end Metamath

