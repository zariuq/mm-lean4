import Metamath.Verify
import Metamath.VerifyIncludeBoundary

namespace Metamath.Legacy

open Metamath.Verify

/-!
Legacy two-pass include runtime.

This module is intentionally separated from `Verify.lean` so the primary runtime
surface remains single-pass by default.
-/

def expandIncludes (fname : String) (processing seen : Std.HashSet String)
    (config : ModeConfig := {}) (depth : Nat := config.maxIncludeDepth) :
    IO (Except IncludeError (ByteArray × Std.HashSet String)) := do
  match depth with
  | 0 =>
      return .error (.depthExceeded fname)
  | depth + 1 =>
      let canonPath ← IO.FS.realPath fname
      let canonStr := canonPath.toString
      if processing.contains canonStr then
        return .error (.cycleDetected canonStr)
      if seen.contains canonStr then
        return .ok (ByteArray.empty, seen)

      let seen := seen.insert canonStr
      let contents ← IO.FS.readBinFile fname

      match scanIncludes contents fname config with
      | .error err => return .error err
      | .ok chunks =>
          let mut result := ByteArray.empty
          let mut seen := seen
          for chunk in chunks do
            match chunk with
            | .bytes bytes =>
                result := result ++ bytes
            | .needInclude includeFile =>
                let baseDir := System.FilePath.parent fname |>.getD "."
                let fullPath := baseDir / includeFile
                try
                  match ← expandIncludes fullPath.toString (processing.insert canonStr) seen config depth with
                  | .ok (expanded, seen') =>
                    seen := seen'
                    result := result ++ expanded
                    result := result.push ' '.toUInt8
                  | .error e => return .error e
                catch e =>
                  return .error (.readFailure includeFile fullPath.toString e.toString)
          return .ok (result, seen)
termination_by depth
decreasing_by
  simp_wf

def checkTwoPassLegacy (fname : String) (config : ModeConfig := {}) : IO DB := do
  let expanded ←
    expandIncludes fname
      (Std.HashSet.emptyWithCapacity 16)
      (Std.HashSet.emptyWithCapacity 16)
      config
      config.maxIncludeDepth
  return checkExpandedResult config expanded

end Metamath.Legacy
