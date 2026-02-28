import Metamath.VerifySinglePassThms
import Metamath.Legacy.Runtime

namespace Metamath.Legacy

open Metamath.Verify

/-! ## Theorem map (legacy two-pass compatibility)

Recommended public order for include-checker reasoning:
1. Use `IncludeSafeSemantic` when you want a non-ad-hoc semantic condition.
2. Convert to bridge form via `includeSafeSemantic_implies_includeSafe`.
3. Conclude checker equivalence via
   `checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic`
   (or `_of_includeSafe` / `_of_bridgeWitness`).

Legacy-oriented theorems are retained for compatibility:
- `checkTwoPassLegacy_eq_checkExpandedResult_expandIncludes`
- `_of_sharedExpandedBytes`, `_of_sharedIncludeError`
- `checkSinglePass_eq_checkTwoPassLegacy_zeroIncludeDepth`
-/

/-- Legacy two-pass checker is definitionally `checkExpandedResult` after `expandIncludes`. -/
@[simp] theorem checkTwoPassLegacy_eq_checkExpandedResult_expandIncludes
    (fname : String) (config : ModeConfig) :
    checkTwoPassLegacy fname config =
      (do
        let expanded ←
          expandIncludes fname
            (Std.HashSet.emptyWithCapacity 16)
            (Std.HashSet.emptyWithCapacity 16)
            config
            config.maxIncludeDepth
        pure (checkExpandedResult config expanded)) := rfl

/-- Two-pass include expander immediately returns the depth-limit include error when
called with zero fuel. -/
@[simp] theorem expandIncludes_zeroFuel
    (fname : String) (processing seen : Std.HashSet String) (config : ModeConfig) :
    expandIncludes fname processing seen config 0 =
      pure (.error (.depthExceeded fname)) := by
  simp [expandIncludes]

/-- On include-preprocess failures, single-pass and two-pass pure post-processing
agree definitionally. -/
@[simp] theorem finalizeSinglePassResult_error_eq_checkExpandedResult_error
    (config : ModeConfig) (err : IncludeError) :
    finalizeSinglePassResult config (.error err) =
      checkExpandedResult config (.error err) := rfl

/-- Pure shared-trace bridge: if both front-ends expose the same expanded bytes
trace, single-pass finalization and two-pass post-processing coincide. -/
theorem finalizeSinglePassResult_eq_checkExpandedResult_of_sharedExpandedBytes
    (config : ModeConfig) (processed : ByteArray) (seen : Std.HashSet String) :
    finalizeSinglePassResult config
      (.ok ((singlePassInitialState config).feedAll 0 processed, processed.size, seen)) =
    checkExpandedResult config (.ok (processed, seen)) := by
  simp [checkExpandedResult]

/-- IO-level bridge theorem: if single-pass initialization and legacy include
expansion expose the same expanded bytes, both checkers return the same DB. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_sharedExpandedBytes
    (fname : String) (config : ModeConfig)
    (processed : ByteArray) (seenSingle seenLegacy : Std.HashSet String)
    (h_single :
      singlePassInitialResult fname config =
        pure (.ok ((singlePassInitialState config).feedAll 0 processed,
          processed.size, seenSingle)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.ok (processed, seenLegacy))) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  rw [checkSinglePass_eq_finalize_singlePassInitialResult]
  rw [checkTwoPassLegacy_eq_checkExpandedResult_expandIncludes]
  rw [h_single, h_legacy]
  have h_inner :
      finalizeSinglePassResult config
        (.ok ((singlePassInitialState config).feedAll 0 processed, processed.size, seenSingle)) =
      checkExpandedResult config (.ok (processed, seenLegacy)) := by
    calc
      finalizeSinglePassResult config
          (.ok ((singlePassInitialState config).feedAll 0 processed, processed.size, seenSingle))
          = checkBytes processed config := by
              exact
                finalizeSinglePassResult_ok_initialFeedAll_eq_checkBytes
                  (config := config) (processed := processed) (seen := seenSingle)
      _ = checkExpandedResult config (.ok (processed, seenLegacy)) := by
            simp [checkExpandedResult]
  have h_inner_io :
      (pure (finalizeSinglePassResult config
        (.ok ((singlePassInitialState config).feedAll 0 processed, processed.size, seenSingle))) :
          IO DB) =
      pure (checkExpandedResult config (.ok (processed, seenLegacy))) :=
    congrArg (fun db => (pure db : IO DB)) h_inner
  simpa using h_inner_io

/-- IO-level bridge theorem: if both front-ends produce the same include error,
both checkers return the same DB. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_sharedIncludeError
    (fname : String) (config : ModeConfig) (err : IncludeError)
    (h_single :
      singlePassInitialResult fname config = pure (.error err))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error err)) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  rw [checkSinglePass_eq_finalize_singlePassInitialResult]
  rw [checkTwoPassLegacy_eq_checkExpandedResult_expandIncludes]
  rw [h_single, h_legacy]
  have h_inner :
      finalizeSinglePassResult config (.error err) =
      checkExpandedResult config (.error err) := by
    exact finalizeSinglePassResult_error_eq_checkExpandedResult_error
      (config := config) (err := err)
  have h_inner_io :
      (pure (finalizeSinglePassResult config (.error err)) : IO DB) =
      pure (checkExpandedResult config (.error err)) :=
    congrArg (fun db => (pure db : IO DB)) h_inner
  simpa using h_inner_io

/-- Specialized IO bridge: if both front-ends report the same include read-failure
payload, both checkers are equal. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_includeReadFailure
    (fname : String) (config : ModeConfig)
    (name path err : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.readFailure name path err)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.readFailure name path err))) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  exact checkSinglePass_eq_checkTwoPassLegacy_of_sharedIncludeError
    fname config (.readFailure name path err) h_single h_legacy

/-- Specialized IO bridge: if both front-ends report the same include-cycle payload,
both checkers are equal. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_includeCycleDetected
    (fname : String) (config : ModeConfig)
    (path : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.cycleDetected path)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.cycleDetected path))) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  exact checkSinglePass_eq_checkTwoPassLegacy_of_sharedIncludeError
    fname config (.cycleDetected path) h_single h_legacy

/-- Unified bridge witness for checker-equivalence reasoning.
This packages the two canonical synchrony cases between single-pass and two-pass:
1) shared expanded bytes, 2) shared include error. -/
inductive CheckerBridgeWitness (fname : String) (config : ModeConfig) : Prop where
  | sharedExpandedBytes
      (processed : ByteArray) (seenSingle seenLegacy : Std.HashSet String)
      (h_single :
        singlePassInitialResult fname config =
          pure (.ok ((singlePassInitialState config).feedAll 0 processed,
            processed.size, seenSingle)))
      (h_legacy :
        expandIncludes fname
          (Std.HashSet.emptyWithCapacity 16)
          (Std.HashSet.emptyWithCapacity 16)
          config
          config.maxIncludeDepth =
          pure (.ok (processed, seenLegacy))) :
      CheckerBridgeWitness fname config
  | sharedIncludeError
      (err : IncludeError)
      (h_single :
        singlePassInitialResult fname config = pure (.error err))
      (h_legacy :
        expandIncludes fname
          (Std.HashSet.emptyWithCapacity 16)
          (Std.HashSet.emptyWithCapacity 16)
          config
          config.maxIncludeDepth =
          pure (.error err)) :
      CheckerBridgeWitness fname config

/-- Unified checker equivalence theorem from a bridge witness. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_bridgeWitness
    (fname : String) (config : ModeConfig)
    (h : CheckerBridgeWitness fname config) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  cases h with
  | sharedExpandedBytes processed seenSingle seenLegacy h_single h_legacy =>
      exact checkSinglePass_eq_checkTwoPassLegacy_of_sharedExpandedBytes
        fname config processed seenSingle seenLegacy h_single h_legacy
  | sharedIncludeError err h_single h_legacy =>
      exact checkSinglePass_eq_checkTwoPassLegacy_of_sharedIncludeError
        fname config err h_single h_legacy

/-- Public predicate: include handling is "safe/equivalent" for this `(fname, config)`
when a bridge witness exists between single-pass and two-pass front-ends. -/
def IncludeSafe (fname : String) (config : ModeConfig) : Prop :=
  CheckerBridgeWitness fname config

/-- Semantic representation predicate: single-pass result corresponds to expanding to
`processed` bytes from the canonical initial parser state. -/
def SinglePassRepresentsExpanded (config : ModeConfig)
    (r : Except IncludeError (ParserState × Nat × Std.HashSet String))
    (processed : ByteArray) : Prop :=
  ∃ seenSingle,
    r = .ok ((singlePassInitialState config).feedAll 0 processed, processed.size, seenSingle)

/-- Semantic representation predicate: two-pass include expansion corresponds to
`processed` bytes (up to duplicate-suppression bookkeeping in `seen`). -/
def TwoPassRepresentsExpanded
    (r : Except IncludeError (ByteArray × Std.HashSet String))
    (processed : ByteArray) : Prop :=
  ∃ seenLegacy, r = .ok (processed, seenLegacy)

/-- Non-ad-hoc semantic safety predicate.
This states that both front-ends either:
1) represent the same expanded byte stream, or
2) produce the same include error. -/
inductive IncludeSafeSemantic (fname : String) (config : ModeConfig) : Prop where
  | expanded
      (single :
        Except IncludeError (ParserState × Nat × Std.HashSet String))
      (legacy : Except IncludeError (ByteArray × Std.HashSet String))
      (processed : ByteArray)
      (h_single_run : singlePassInitialResult fname config = pure single)
      (h_legacy_run :
        expandIncludes fname
          (Std.HashSet.emptyWithCapacity 16)
          (Std.HashSet.emptyWithCapacity 16)
          config
          config.maxIncludeDepth = pure legacy)
      (h_single_rep : SinglePassRepresentsExpanded config single processed)
      (h_legacy_rep : TwoPassRepresentsExpanded legacy processed) :
      IncludeSafeSemantic fname config
  | includeError
      (err : IncludeError)
      (h_single_run : singlePassInitialResult fname config = pure (.error err))
      (h_legacy_run :
        expandIncludes fname
          (Std.HashSet.emptyWithCapacity 16)
          (Std.HashSet.emptyWithCapacity 16)
          config
          config.maxIncludeDepth = pure (.error err)) :
      IncludeSafeSemantic fname config

/-- Semantic constructor wrapper: shared include read-failure payload gives
`IncludeSafeSemantic` immediately. -/
theorem includeSafeSemantic_of_includeReadFailure
    (fname : String) (config : ModeConfig)
    (name path err : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.readFailure name path err)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.readFailure name path err))) :
    IncludeSafeSemantic fname config :=
  IncludeSafeSemantic.includeError
    (.readFailure name path err) h_single h_legacy

/-- Semantic constructor wrapper: shared include cycle payload gives
`IncludeSafeSemantic` immediately. -/
theorem includeSafeSemantic_of_includeCycleDetected
    (fname : String) (config : ModeConfig)
    (path : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.cycleDetected path)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.cycleDetected path))) :
    IncludeSafeSemantic fname config :=
  IncludeSafeSemantic.includeError
    (.cycleDetected path) h_single h_legacy

/-- Semantic constructor wrapper: shared include depth-exceeded payload gives
`IncludeSafeSemantic` immediately. -/
theorem includeSafeSemantic_of_includeDepthExceeded
    (fname : String) (config : ModeConfig)
    (path : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.depthExceeded path)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.depthExceeded path))) :
    IncludeSafeSemantic fname config :=
  IncludeSafeSemantic.includeError
    (.depthExceeded path) h_single h_legacy

/-- Semantic safety implies bridge witness safety. -/
theorem includeSafeSemantic_implies_includeSafe
    (fname : String) (config : ModeConfig)
    (h_sem : IncludeSafeSemantic fname config) :
    IncludeSafe fname config := by
  cases h_sem with
  | expanded single legacy processed h_single_run h_legacy_run h_single_rep h_legacy_rep =>
      rcases h_single_rep with ⟨seenSingle, h_single_repr⟩
      rcases h_legacy_rep with ⟨seenLegacy, h_legacy_repr⟩
      apply CheckerBridgeWitness.sharedExpandedBytes
        (processed := processed) (seenSingle := seenSingle) (seenLegacy := seenLegacy)
      · calc
          singlePassInitialResult fname config = pure single := h_single_run
          _ = pure
              (.ok ((singlePassInitialState config).feedAll 0 processed, processed.size, seenSingle)) := by
                simp [h_single_repr]
      · calc
          expandIncludes fname
            (Std.HashSet.emptyWithCapacity 16)
            (Std.HashSet.emptyWithCapacity 16)
            config
            config.maxIncludeDepth = pure legacy := h_legacy_run
          _ = pure (.ok (processed, seenLegacy)) := by simp [h_legacy_repr]
  | includeError err h_single_run h_legacy_run =>
      exact CheckerBridgeWitness.sharedIncludeError err h_single_run h_legacy_run

/-- Semantic safety directly implies checker equivalence. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic
    (fname : String) (config : ModeConfig)
    (h_sem : IncludeSafeSemantic fname config) :
    checkSinglePass fname config = checkTwoPassLegacy fname config :=
  checkSinglePass_eq_checkTwoPassLegacy_of_bridgeWitness
    fname config (includeSafeSemantic_implies_includeSafe fname config h_sem)

/-- Public checker-equivalence theorem under `IncludeSafe`. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_includeSafe
    (fname : String) (config : ModeConfig)
    (h_safe : IncludeSafe fname config) :
    checkSinglePass fname config = checkTwoPassLegacy fname config :=
  checkSinglePass_eq_checkTwoPassLegacy_of_bridgeWitness fname config h_safe

/-- Read-failure payload specialization routed through the semantic
`IncludeSafeSemantic` path. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic_includeReadFailure
    (fname : String) (config : ModeConfig)
    (name path err : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.readFailure name path err)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.readFailure name path err))) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  exact checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic
    fname config
    (includeSafeSemantic_of_includeReadFailure
      fname config name path err h_single h_legacy)

/-- Cycle payload specialization routed through the semantic
`IncludeSafeSemantic` path. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic_includeCycleDetected
    (fname : String) (config : ModeConfig)
    (path : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.cycleDetected path)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.cycleDetected path))) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  exact checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic
    fname config
    (includeSafeSemantic_of_includeCycleDetected
      fname config path h_single h_legacy)

/-- Depth-exceeded payload specialization routed through the semantic
`IncludeSafeSemantic` path. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic_includeDepthExceeded
    (fname : String) (config : ModeConfig)
    (path : String)
    (h_single :
      singlePassInitialResult fname config = pure (.error (.depthExceeded path)))
    (h_legacy :
      expandIncludes fname
        (Std.HashSet.emptyWithCapacity 16)
        (Std.HashSet.emptyWithCapacity 16)
        config
        config.maxIncludeDepth =
        pure (.error (.depthExceeded path))) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  exact checkSinglePass_eq_checkTwoPassLegacy_of_includeSafeSemantic
    fname config
    (includeSafeSemantic_of_includeDepthExceeded
      fname config path h_single h_legacy)

/-- Canonical bridge witness for zero include-depth fuel. -/
theorem checkerBridgeWitness_zeroIncludeDepth
    (fname : String) (config : ModeConfig)
    (h_depth : config.maxIncludeDepth = 0) :
    CheckerBridgeWitness fname config := by
  apply CheckerBridgeWitness.sharedIncludeError
    (err := .depthExceeded fname)
  · unfold singlePassInitialResult
    rw [h_depth]
    exact
      processFileSinglePass_zeroFuel
        (fname := fname)
        (processing := Std.HashSet.emptyWithCapacity 16)
        (seen := Std.HashSet.emptyWithCapacity 16)
        (config := config)
        (s := singlePassInitialState config)
        (base := 0)
  · rw [h_depth]
    exact
      expandIncludes_zeroFuel
        (fname := fname)
        (processing := Std.HashSet.emptyWithCapacity 16)
        (seen := Std.HashSet.emptyWithCapacity 16)
        (config := config)

/-- `IncludeSafe` canary: zero include-depth fuel is always bridge-safe. -/
theorem includeSafe_zeroIncludeDepth
    (fname : String) (config : ModeConfig)
    (h_depth : config.maxIncludeDepth = 0) :
    IncludeSafe fname config :=
  checkerBridgeWitness_zeroIncludeDepth fname config h_depth

/-- Concrete equivalence canary: with zero include-depth fuel, both checkers
immediately return the same include-depth error DB. -/
theorem checkSinglePass_eq_checkTwoPassLegacy_zeroIncludeDepth
    (fname : String) (config : ModeConfig)
    (h_depth : config.maxIncludeDepth = 0) :
    checkSinglePass fname config = checkTwoPassLegacy fname config := by
  exact checkSinglePass_eq_checkTwoPassLegacy_of_includeSafe
    fname config (includeSafe_zeroIncludeDepth fname config h_depth)

end Metamath.Legacy
