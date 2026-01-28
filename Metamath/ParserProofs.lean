/-
# Parser Correctness Proofs

This module proves the parser behavior axioms from ParserInvariants.lean
by analyzing the parser implementation in Verify.lean.

The proofs work by:
1. Defining invariants (properties maintained during parsing)
2. Showing parser operations maintain invariants
3. Showing initial state satisfies invariants
4. Concluding by induction that successful parsing implies properties hold
-/

import Metamath.Verify
import Metamath.Spec
import Metamath.ParserInvariants
import Metamath.ParserOperations
import Metamath.DBCaseAnalysis
import Metamath.ArrayListExt
import Metamath.WellFormedness
import Metamath.KernelExtras
import Batteries.Tactic.Init

namespace Metamath.ParserProofs

open Verify
open KernelExtras.HashMap
open Std (HashMap)
open Metamath.WF

/-- Parser invariant: the working database is well-formed. -/
def parserInvariant (db : DB) : Prop := WellFormedDB db

@[simp] theorem default_frame_hyps : (default : Frame).hyps = (#[] : Array String) := rfl
@[simp] theorem default_db_frame_hyps : (default : DB).frame.hyps = (#[] : Array String) := rfl
@[simp] theorem default_db_objects : (default : DB).objects = ({} : HashMap String Object) := rfl

/-- The initial database (empty objects/frame) is well-formed. -/
theorem init_db_wellFormed (permissive : Bool := false) :
    parserInvariant ({ (default : DB) with permissive := permissive } : DB) := by
  classical
  -- Work with a named database value.
  let db : DB := { (default : DB) with permissive := permissive }
  change WellFormedDB db
  -- All components are empty in the default DB, so well-formedness is trivial.
  unfold WellFormedDB WellFormedFrame HypOK UniqueFloatVars
  have hhyps_size : db.frame.hyps.size = 0 := by simp [db]
  constructor
  · constructor
    · intro i hi
      -- hyps is empty, so no index is in-bounds
      simp [hhyps_size] at hi
    · intro i j hi hj hneq fi fj lbli lblj hfi hfj hsize_i hsize_j
      -- likewise, any i is out of bounds
      simp [hhyps_size] at hi
  · intro lbl obj hfind
    -- Empty objects map: find? cannot return `some obj`
    -- hfind says lookup is `some obj`, contradicting emptiness
    have hFalse : False := by
      simp [DB.find?, db] at hfind
    exact hFalse.elim

/-- Pushing a scope does not affect well-formedness (scopes are ignored by WellFormedDB). -/
theorem pushScope_preserves_wf {db : DB} :
    parserInvariant db → parserInvariant db.pushScope := by
  intro h
  -- pushScope only changes `scopes`; frame/objects unchanged
  simpa [parserInvariant, DB.pushScope]
/-! ## Float Uniqueness Invariant

The key invariant for proving `parser_validates_float_uniqueness`:
"In any frame, no two float hypotheses bind the same variable"
-/

/-- **Invariant**: No duplicate float variables in a frame.

Given a frame's hypotheses and the database, this predicate states that
no two distinct float hypotheses in the frame bind the same variable.
-/
def frame_has_unique_floats (db : DB) (hyps : Array String) : Prop :=
  ∀ (i j : Nat) (hi : i < hyps.size) (hj : j < hyps.size),
    i ≠ j →
    ∀ (fi fj : Formula) (lbli lblj : String),
      db.find? hyps[i] = some (.hyp false fi lbli) →
      db.find? hyps[j] = some (.hyp false fj lblj) →
      fi.size >= 2 → fj.size >= 2 →
      let vi := match fi[1]! with | .var v => v | _ => ""
      let vj := match fj[1]! with | .var v => v | _ => ""
      vi ≠ vj

/-- **Invariant**: Every hypothesis label in a frame resolves to a hypothesis in the DB. -/
def frame_hyps_exist (db : DB) (hyps : Array String) : Prop :=
  ∀ (i : Nat) (hi : i < hyps.size),
    ∃ ess f lbl, db.find? hyps[i] = some (.hyp ess f lbl)

/-- **Invariant**: Every float hypothesis in a frame has well-formed float shape. -/
def frame_float_wf (db : DB) (hyps : Array String) : Prop :=
  ∀ (i : Nat) (hi : i < hyps.size) (f : Formula) (lbl : String),
    db.find? hyps[i] = some (.hyp false f lbl) → f.isFloatShape = true

/-- **Invariant**: Database has unique floats in all frames.

This extends the frame-level invariant to all frames in the database.
For every assertion in the database, its frame satisfies frame_has_unique_floats.
-/
def db_has_unique_floats (db : DB) : Prop :=
  -- Current frame being built
  frame_has_unique_floats db db.frame.hyps ∧
  frame_hyps_exist db db.frame.hyps ∧
  frame_float_wf db db.frame.hyps ∧
  -- All completed frames (assertions)
  ∀ (label : String) (fmla : Formula) (fr : Frame) (proof : String),
    db.find? label = some (.assert fmla fr proof) →
    frame_has_unique_floats db fr.hyps ∧
    frame_hyps_exist db fr.hyps ∧
    frame_float_wf db fr.hyps

/-! ## Helper Lemmas -/

/-- Helper: `mkError` does not touch the frame. -/
@[simp] theorem DB.mkError_frame (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).frame = db.frame := rfl

/-- Helper: updating only `objects` preserves `.frame`. -/
@[simp] theorem DB.updateObjects_frame (db : DB) (m : Std.HashMap String Object) :
  ({ db with objects := m }).frame = db.frame := rfl

/-- Helper: mkError does not touch objects. -/
@[simp] theorem DB.mkError_objects (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).objects = db.objects := rfl

/-- Helper: find? after updating objects looks in the new map. -/
@[simp] theorem DB.updateObjects_find? (db : DB) (m : Std.HashMap String Object) (l : String) :
  ({ db with objects := m }).find? l = m[l]? := rfl

/-- Helper: withHyps only modifies frame.hyps, not objects -/
@[simp] theorem DB.withHyps_objects (db : DB) (f : Array String → Array String) :
  (db.withHyps f).objects = db.objects := rfl

@[simp] theorem DB.withHyps_frame_hyps (db : DB) (f : Array String → Array String) :
  (db.withHyps f).frame.hyps = f db.frame.hyps := rfl

/-- Helper: withHyps preserves find? for all labels -/
theorem DB.withHyps_find? (db : DB) (f : Array String → Array String) (l : String) :
  (db.withHyps f).find? l = db.find? l := by
  unfold DB.withHyps DB.find?
  rfl

/-- withHyps preserves the frame field for assertions looked up via find? -/
theorem DB.withHyps_preserves_assertion_frames (db : DB) (f : Array String → Array String)
  (l : String) (fmla : Formula) (fr : Frame) (proof : String) :
  db.find? l = some (.assert fmla fr proof) →
  (db.withHyps f).find? l = some (.assert fmla fr proof) := by
  intro h
  rw [DB.withHyps_find?]
  exact h

@[simp] theorem frame_has_unique_floats_withHyps (db : DB) (f : Array String → Array String) (hyps : Array String) :
  frame_has_unique_floats (db.withHyps f) hyps = frame_has_unique_floats db hyps := by
  apply propext
  constructor
  · intro h i j hi hj hneq fi fj lbli lblj hfi hfj hsi hsj
    have hfi' : db.find? hyps[i] = some (.hyp false fi lbli) := by
      simpa [DB.withHyps_find?] using hfi
    have hfj' : db.find? hyps[j] = some (.hyp false fj lblj) := by
      simpa [DB.withHyps_find?] using hfj
    exact h i j hi hj hneq fi fj lbli lblj hfi' hfj' hsi hsj
  · intro h i j hi hj hneq fi fj lbli lblj hfi hfj hsi hsj
    have hfi' : (db.withHyps f).find? hyps[i] = some (.hyp false fi lbli) := by
      simpa [DB.withHyps_find?] using hfi
    have hfj' : (db.withHyps f).find? hyps[j] = some (.hyp false fj lblj) := by
      simpa [DB.withHyps_find?] using hfj
    exact h i j hi hj hneq fi fj lbli lblj hfi' hfj' hsi hsj

/-- withHyps preserves existence of hypotheses in a frame. -/
@[simp] theorem frame_hyps_exist_withHyps (db : DB) (f : Array String → Array String) (hyps : Array String) :
  frame_hyps_exist (db.withHyps f) hyps = frame_hyps_exist db hyps := by
  apply propext
  constructor
  · intro h i hi
    rcases h i hi with ⟨ess, fml, lbl, hfind⟩
    have hfind' : db.find? hyps[i] = some (.hyp ess fml lbl) := by
      simpa [DB.withHyps_find?] using hfind
    exact ⟨ess, fml, lbl, hfind'⟩
  · intro h i hi
    rcases h i hi with ⟨ess, fml, lbl, hfind⟩
    have hfind' : (db.withHyps f).find? hyps[i] = some (.hyp ess fml lbl) := by
      simpa [DB.withHyps_find?] using hfind
    exact ⟨ess, fml, lbl, hfind'⟩

/-- withHyps preserves float well-formedness in a frame. -/
@[simp] theorem frame_float_wf_withHyps (db : DB) (f : Array String → Array String) (hyps : Array String) :
  frame_float_wf (db.withHyps f) hyps = frame_float_wf db hyps := by
  apply propext
  constructor
  · intro h i hi fml lbl hfind
    have hfind' : db.find? hyps[i] = some (.hyp false fml lbl) := by
      simpa [DB.withHyps_find?] using hfind
    exact h i hi fml lbl hfind'
  · intro h i hi fml lbl hfind
    have hfind' : (db.withHyps f).find? hyps[i] = some (.hyp false fml lbl) := by
      simpa [DB.withHyps_find?] using hfind
    exact h i hi fml lbl hfind'

/-- If every frame label exists in the DB, then a fresh label is not in the frame. -/
theorem frame_hyps_exist_not_in
  (db : DB) (hyps : Array String) (l : String)
  (h_exist : frame_hyps_exist db hyps)
  (h_fresh : db.find? l = none) :
  ∀ (i : Nat) (hi : i < hyps.size), hyps[i]'hi ≠ l := by
  intro i hi h_eq
  rcases h_exist i hi with ⟨ess, f, lbl, hfind⟩
  have hfind' : db.find? l = some (.hyp ess f lbl) := by
    simpa [h_eq] using hfind
  have hcontra : False := by
    simp [h_fresh] at hfind'
  exact hcontra

/-- Once error is set, mkError keeps it set -/
@[simp] theorem error_persists_mkError (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error? ≠ none := by
  unfold DB.mkError
  simp

/-- DB.error is true after mkError -/
@[simp] theorem DB.error_mkError (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error = true := by
  -- DB.error is defined as db.error?.isSome
  -- mkError sets error? := some …
  unfold DB.error DB.mkError
  simp

/-- If-then-else with mkError.error always takes the then branch -/
@[simp] theorem if_error_mkError_eq {α}
    (db : DB) (pos : Pos) (msg : String) (t₁ t₂ : α) :
  (if (db.mkError pos msg).error then t₁ else t₂) = t₁ := by
  simp [DB.error_mkError]


/-- If db has error, withHyps preserves it -/
@[simp] theorem error_persists_withHyps (db : DB) (f : Array String → Array String)
  (h : db.error? ≠ none) :
  (db.withHyps f).error? ≠ none := by
  unfold DB.withHyps
  exact h

/-- If db has error, insert returns db with error preserved.

Proof strategy: DB.insert checks `if db.error then db else ...` at line 316,
so if db has an error, it returns db unchanged, preserving the error.
-/
@[simp] theorem insert_preserves_error (db : DB) (pos : Pos) (l : String) (obj : String → Object)
  (h : db.error? ≠ none) :
  (db.insert pos l obj).error? ≠ none := by
  -- DB.insert checks `if db.error then db else ...`, returning db unchanged when error is set
  unfold DB.insert DB.error
  -- When error? ≠ none, db.error?.isSome = true, so all branches preserve error
  -- Use the same repeat pattern that worked for insert_frame_unchanged
  have h_some : db.error?.isSome = true := by
    cases heq : db.error? with
    | none => exfalso; exact h heq
    | some _ => rfl
  simp
  -- Any remaining branches either return db or mkError, both preserve error
  repeat (first | assumption | simp [DB.mkError] | split)

/-- `DB.insert` never changes `.frame`.

Proof strategy: All execution paths in DB.insert preserve the frame field:
- Const check path: If error, calls mkError (preserves frame by mkError_frame)
- Error check: If db.error, returns db unchanged
- Duplicate check: Either returns db or calls mkError (both preserve frame)
- Success path: Updates only objects field (preserves frame definitionally)

This is definitionally true but requires careful Lean 4 tactic engineering
to navigate the nested conditionals in DB.insert.
-/
theorem insert_frame_unchanged
    (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).frame = db.frame := by
  -- Inline all cases of insert; each case preserves `frame`.
  unfold DB.insert
  -- All paths preserve frame via: mkError (simp lemma), return db (rfl), or record update (rfl)
  -- Use repeated split to cover all nested branches
  repeat (first | rfl | simp | split)

/-- If inserting a hypothesis succeeds, we must have taken the insert branch,
    hence looking up `l` yields the newly inserted `.hyp`.

    GPT-5 Pro proven lemma - specialized to .hyp (non-var object).

    Proof strategy (GPT-5 Pro validated):
    1. Unfold DB.insert
    2. Case split on db.error?.isSome
       - If true: contradict h_success (insert would propagate error)
       - If false: proceed to duplicate check
    3. Case split on db.find? l
       - If some o: For `.hyp`, ok test is false → error contradicts success
       - If none: Final insert branch → use Std.HashMap.getElem?_insert_self

    This proof works because .hyp is not .var, so the "duplicate var OK" branch doesn't apply.
    -/
@[simp] theorem DB.find?_insert_self_hyp
  (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
  (h_success : (db.insert pos l (.hyp ess f)).error? = none) :
  (db.insert pos l (.hyp ess f)).find? l = some (.hyp ess f l) := by
  classical
  -- Expand once; the first `let db := ...` reduces because `.hyp` is not `.const`
  unfold DB.insert at h_success ⊢
  -- The match on `obj l` specializes to `.hyp _ _ l`
  -- so the first "const strictness" gate becomes a no-op:
  -- use simp to discharge that top-level `match` and expose the `if db.error` split
  simp [DB.find?] at h_success ⊢
  -- split on the `db.error` gate
  by_cases h_err : db.error
  · -- If `db.error = true`, the if-then-else returns `db` unchanged,
    -- so `h_success` says `db.error? = none`, which contradicts `db.error = true`.
    -- Show the contradiction by splitting on `db.error?`.
    simp [h_err] at h_success
    cases hopt : db.error? with
    | none =>
        -- `db.error = true` means `db.error?.isSome = true` by def,
        -- but `isSome none = false`: contradiction
        simp [DB.error, hopt] at h_err
    | some e =>
        -- Here the result's `error?` is `some e`, contradicting `h_success : ... = none`
        simp [hopt] at h_success
  · -- `db.error = false`: continue to duplicate check
    simp [h_err] at h_success ⊢
    -- split on `db.find? l`
    cases hfind : db.find? l with
    | none =>
        -- Success branch: actual insert happens
        split
        · -- db.objects[l]? = some case - impossible since hfind says db.find? l = none
          next o heq =>
            -- hfind : db.find? l = none means db.objects[l]? = none
            have h_none : db.objects[l]? = none := by unfold DB.find? at hfind; exact hfind
            -- But heq : db.objects[l]? = some o, contradiction
            rw [heq] at h_none
            simp at h_none
        · exact KernelExtras.HashMap.find?_insert_self db.objects l (.hyp ess f l)
    | some o =>
        -- Duplicate path: compute `ok`; for `.hyp`, ok is always `false`
        have hok : (match o with
          | .var _ => (match Object.hyp ess f l with | .var _ => true | _ => false)
          | _ => false) = false := by
          cases o <;> simp
        -- In this branch `ok = false`, so insert raises an error; contradicts `h_success`
        have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
          error_persists_mkError db pos s!"duplicate symbol/assert {l}"
        have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
          have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
          cases o <;> simp [hfind'] at h_success
        exact (hne hcontra).elim

@[simp] theorem DB.find?_insert_self_assert
  (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  (h_success : (db.insert pos l (fun _ => .assert fmla fr proof)).error? = none) :
  (db.insert pos l (fun _ => .assert fmla fr proof)).find? l = some (.assert fmla fr proof) := by
  classical
  -- Same pattern as find?_insert_self_hyp but for assert
  unfold DB.insert at h_success ⊢
  -- Assert is not const, so first gate is no-op
  simp [DB.find?] at h_success ⊢
  -- Split on db.error
  by_cases h_err : db.error
  · -- Error case: contradicts h_success
    simp [h_err] at h_success
    cases hopt : db.error? with
    | none =>
        simp [DB.error, hopt] at h_err
    | some e =>
        simp [hopt] at h_success
  · -- No error: continue to duplicate check
    simp [h_err] at h_success ⊢
    -- Split on db.find? l
    cases hfind : db.find? l with
    | none =>
        -- Success branch: actual insert happens
        split
        · -- Impossible: db.objects[l]? = some but hfind says db.find? l = none
          next o heq =>
            have h_none : db.objects[l]? = none := by unfold DB.find? at hfind; exact hfind
            rw [heq] at h_none
            simp at h_none
        · exact KernelExtras.HashMap.find?_insert_self db.objects l (.assert fmla fr proof)
    | some o =>
        -- Duplicate path: for assert, ok is always false
        have hok : (match o with
          | .var _ => (match Object.assert fmla fr proof with | .var _ => true | _ => false)
          | _ => false) = false := by
          cases o <;> simp
        -- ok = false means error; contradicts h_success
        have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
          error_persists_mkError db pos s!"duplicate symbol/assert {l}"
        have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
          have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
          cases o <;> simp [hfind'] at h_success
        exact (hne hcontra).elim

/-- **Helper Lemma**: If inserting an assertion succeeds, the label was fresh.

Proof strategy:
1. Assume db.find? l ≠ none (for contradiction)
2. Then db.find? l = some o for some object o
3. In DB.insert, if some o exists then ok must be true to succeed
4. For assertions, ok is always false (only var-on-var can overwrite)
5. Therefore mkError is called, contradicting success
-/
theorem insert_assert_success_implies_fresh
  (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  (h_success : (db.insert pos l (fun _ => .assert fmla fr proof)).error? = none) :
  db.find? l = none := by
  by_contra h_exists
  obtain ⟨o, hfind⟩ := Option.ne_none_iff_exists.mp h_exists
  unfold DB.insert at h_success
  simp only at h_success
  by_cases h_err : db.error
  · -- If db already has error, insert returns db with error
    simp only [h_err, ite_true] at h_success
    have : db.error? ≠ none := by
      cases hopt : db.error? with
      | none => simp [DB.error, hopt] at h_err
      | some e => simp
    exact this h_success
  · -- db.error = false, so we check for duplicates
    simp only [h_err] at h_success
    -- Now h_success is about: match db.find? l with | some o => ... | none => ...
    -- We have hfind : db.find? l = some o
    cases hfind_case : db.find? l with
    | none =>
        -- Contradiction: hfind says some o, but case says none
        simp [hfind_case] at hfind
    | some o_db =>
        -- hfind : some o = db.find? l, hfind_case : db.find? l = some o_db
        -- So some o = some o_db, hence o = o_db
        have h_eq_opt : some o = some o_db := hfind.trans hfind_case
        injection h_eq_opt with h_eq_o
        -- Now we're in the "some o_db" branch
        simp only [hfind_case] at h_success
        -- The control flow depends on what type o_db is
        -- For .assert, the ok check always fails, so mkError is called
        cases o_db <;> simp at h_success
        -- All cases lead to mkError except .var which we show is impossible
        all_goals {
          -- h_success is now (db.mkError...).error? = none
          have hne := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
          exact hne h_success
        }

/-- If inserting a hypothesis succeeds, the label must be fresh (no prior object at that label). -/
theorem insert_hyp_success_implies_fresh
  (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
  (h_success : (db.insert pos l (.hyp ess f)).error? = none) :
  db.find? l = none := by
  by_contra h_exists
  obtain ⟨o, hfind⟩ := Option.ne_none_iff_exists.mp h_exists
  unfold DB.insert at h_success
  simp only at h_success
  by_cases h_err : db.error
  · -- If db already has error, insert returns db with error
    simp [h_err] at h_success
    have : db.error? ≠ none := by
      cases hopt : db.error? with
      | none => simp [DB.error, hopt] at h_err
      | some _ => simp
    exact this h_success
  · -- db.error = false, so we check for duplicates
    simp [h_err] at h_success
    -- We are in the duplicate branch since db.find? l = some o
    cases hfind_case : db.find? l with
    | none =>
        -- Contradiction with hfind
        simp [hfind_case] at hfind
    | some o_db =>
        have h_success' := h_success
        -- simplify the control flow using the known lookup
        simp [hfind_case] at h_success'
        -- In the duplicate branch with a hyp insertion, ok = false so mkError is called
        -- regardless of the existing object o_db.
        cases o_db <;> (
          have hne := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
          exact hne h_success')

/-- If `insert` succeeds, all keys different from the inserted label are preserved.

    GPT-5 Pro proven lemma - works for any object type.

    Proof strategy (GPT-5 Pro validated):
    1. Unfold DB.insert
    2. Case split on db.error?.isSome
       - If true: contradict h_success
       - If false: proceed to duplicate check
    3. Case split on db.find? l
       - If some o: Success means this is the "unchanged" branch (ok = true) → reflexive
       - If none: Final insert branch → use Std.HashMap.getElem?_insert with l' ≠ l

    This works for ANY object type because either DB is unchanged or only key `l` is modified.
    -/
@[simp] theorem DB.find?_insert_ne
  (db : DB) (pos : Pos) (l : String) (l' : String) (obj : String → Object)
  (h_ne : l' ≠ l)
  (h_success : (db.insert pos l obj).error? = none) :
  (db.insert pos l obj).find? l' = db.find? l' := by
  classical
  -- Expand definition once. We'll peel the branches by hand.
  unfold DB.insert at h_success ⊢
  -- First gate: on `obj l` for the const/strictness rule
  cases hobj : obj l with
  | const c =>
      -- "const strictness" sub-branch
      -- Split that internal `if !db.permissive && db.scopes.size > 0`
      by_cases h_strict : (!db.permissive && db.scopes.size > 0)
      · -- In the strict-const case, insert raises an error → contradicts `h_success`
        -- With DB.error_mkError, simp collapses the control flow to False
        -- With DB.error_mkError, simp collapses the control flow and closes the goal
        simp [DB.mkError, DB.error, hobj, h_strict] at h_success
      · -- Not strict: the `let db := ...` is just `db`; continue
        -- Next gate: `if db.error then db else ...`
        by_cases h_err : db.error
        · -- returns `db`; contradicts success unless `db.error? = none`
          -- and in that case the result is literally `db`
          -- but `h_err=true` implies `db.error? ≠ none`, contradiction:
          simp [hobj, h_strict, h_err] at h_success
          cases hopt : db.error? with
          | none => simp [DB.error, hopt] at h_err
          | some e => simp [hopt] at h_success
        · -- Real work happens here: duplicate or insert
          simp [hobj, h_strict, h_err] at h_success ⊢
          -- Now split on duplicate check
          cases hfind : db.find? l with
          | none =>
              -- No duplicate → actual insert at `l`
              -- So at key `l' ≠ l` the lookup is preserved:
              simp [DB.find?, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
          | some o =>
              -- Duplicate; compute ok
              -- ok=true iff `o` is `.var _` and `obj l` is `.var _`
              -- but we are in the `.const` case for `obj l`, so ok=false → mkError → contradict
              have hok : (match o with
                | .var _ => (match Object.const c with | .var _ => true | _ => false)
                | _ => false) = false := by
                cases o <;> simp
              -- Contradiction with success:
              have : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
              have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
                cases o <;> simp [DB.find?, hfind'] at h_success
              exact (this hcontra).elim
  | var x =>
      -- Variable case short-circuits like const but without strictness gate.
      -- Proceed to `db.error` and duplicate logic:
      by_cases h_err : db.error
      · simp [hobj, h_err] at h_success
        cases hopt : db.error? with
        | none => simp [DB.error, hopt] at h_err
        | some e => simp [hopt] at h_success
      · simp [hobj, h_err] at h_success ⊢
        cases hfind : db.find? l with
        | none =>
            -- inserted at l; use HashMap lemma at l' ≠ l
            simp [DB.find?, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
        | some o =>
            -- ok=true exactly when old is `.var _` (already true by `some o` + match),
            -- and new is `.var _` (true in this branch). In that subcase the DB returns unchanged.
            -- We can discharge both subcases (ok=true and ok=false) by `cases o`:
            cases o with
            | var y =>
                -- ok = true → returned DB is unchanged → reflexive equality of find?
                have hok : (match Object.var y with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = true := by simp
                simp [DB.find?]
            | const c' =>
                -- ok = false → mkError, contradiction
                have hok : (match Object.const c' with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = false := by simp
                have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
                  error_persists_mkError db pos s!"duplicate symbol/assert {l}"
                have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                  have hfind' : db.objects[l]? = some (Object.const c') := by unfold DB.find? at hfind; exact hfind
                  simp [DB.find?, hfind'] at h_success
                exact (hne hcontra).elim
            | hyp ess' f' l' =>
                have hok : (match Object.hyp ess' f' l' with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = false := by simp
                have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
                  error_persists_mkError db pos s!"duplicate symbol/assert {l}"
                have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                  have hfind' : db.objects[l]? = some (Object.hyp ess' f' l') := by unfold DB.find? at hfind; exact hfind
                  simp [DB.find?, hfind'] at h_success
                exact (hne hcontra).elim
            | assert f' fr' prf' =>
                have hok : (match Object.assert f' fr' prf' with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = false := by simp
                have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
                  error_persists_mkError db pos s!"duplicate symbol/assert {l}"
                have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                  have hfind' : db.objects[l]? = some (Object.assert f' fr' prf') := by unfold DB.find? at hfind; exact hfind
                  simp [DB.find?, hfind'] at h_success
                exact (hne hcontra).elim
  | hyp ess f _ =>
      -- This mirrors the proof of DB.find?_insert_self_hyp, but at key l' ≠ l.
      by_cases h_err : db.error
      · simp [hobj, h_err] at h_success
        cases hopt : db.error? with
        | none => simp [DB.error, hopt] at h_err
        | some e => simp [hopt] at h_success
      · simp [hobj, h_err] at h_success ⊢
        cases hfind : db.find? l with
        | none =>
            -- Insert at l → preserve l'
            simp [DB.find?, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
        | some o =>
            -- ok=false (new is hyp, not var) → mkError → contradiction
            have hok : (match o with
              | .var _ => (match Object.hyp ess f l with | .var _ => true | _ => false)
              | _ => false) = false := by
              cases o <;> simp
            have : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
            have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
              have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
              cases o <;> simp [DB.find?, hfind'] at h_success
            exact (this hcontra).elim
  | assert _ _ _ =>
      -- Same shape as hyp: ok=false in duplicate branch; otherwise HashMap lemma
      by_cases h_err : db.error
      · simp [hobj, h_err] at h_success
        cases hopt : db.error? with
        | none => simp [DB.error, hopt] at h_err
        | some e => simp [hopt] at h_success
      · simp [hobj, h_err] at h_success ⊢
        cases hfind : db.find? l with
        | none =>
            simp [DB.find?, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
        | some o =>
            have hok : (match o with
              | .var _ => (match (obj l : Object) with | .var _ => true | _ => false)
              | _ => false) = false := by
              cases o <;> simp [hobj]
            have : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
            have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
              have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
              cases o <;> simp [DB.find?, hfind'] at h_success
            exact (this hcontra).elim

/-- If insert succeeds, lookups at other labels are preserved.

Proof strategy:
- Success means we reached the final case: { db with objects := db.objects.insert l (obj l) }
- For find? l' where l' ≠ l, we use DB.find?_insert_ne wrapper
- All error paths either return db (preserving find?) or set error (contradicting h_success)
-/
theorem insert_find_preserved (db : DB) (pos : Pos) (l : String) (l' : String) (obj : String → Object)
  (h_ne : l ≠ l')
  (h_success : (db.insert pos l obj).error? = none) :
  (db.insert pos l obj).find? l' = db.find? l' := by
  -- Use the DB-level wrapper lemma (swap inequality)
  exact DB.find?_insert_ne db pos l l' obj (Ne.symm h_ne) h_success

/-! ## Frame Preservation Lemmas -/

/-- If frame has unique floats in db, and we insert at a label NOT in the frame,
then the frame still has unique floats in the new db. -/
theorem frame_has_unique_floats_insert_ne
  (db : DB) (pos : Pos) (l : String) (obj : String → Object)
  (fr_hyps : Array String)
  (h_fr : frame_has_unique_floats db fr_hyps)
  (h_not_in : ∀ (i : Nat) (hi : i < fr_hyps.size), fr_hyps[i]'hi ≠ l)
  (h_success : (db.insert pos l obj).error? = none) :
  frame_has_unique_floats (db.insert pos l obj) fr_hyps := by
  unfold frame_has_unique_floats at h_fr ⊢
  intros i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
  have h_i_ne : fr_hyps[i]'hi ≠ l := h_not_in i hi
  have h_j_ne : fr_hyps[j]'hj ≠ l := h_not_in j hj
  rw [DB.find?_insert_ne _ _ _ _ _ h_i_ne h_success] at h_fi
  rw [DB.find?_insert_ne _ _ _ _ _ h_j_ne h_success] at h_fj
  exact h_fr i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj

/-- If all labels in a frame exist, and we insert at a fresh label,
    then existence is preserved for that frame. -/
theorem frame_hyps_exist_insert_ne
  (db : DB) (pos : Pos) (l : String) (obj : String → Object)
  (fr_hyps : Array String)
  (h_fr : frame_hyps_exist db fr_hyps)
  (h_not_in : ∀ (i : Nat) (hi : i < fr_hyps.size), fr_hyps[i]'hi ≠ l)
  (h_success : (db.insert pos l obj).error? = none) :
  frame_hyps_exist (db.insert pos l obj) fr_hyps := by
  intro i hi
  rcases h_fr i hi with ⟨ess, f, lbl, hfind⟩
  have h_ne : fr_hyps[i]'hi ≠ l := h_not_in i hi
  have h_pres := DB.find?_insert_ne db pos l (fr_hyps[i]'hi) obj h_ne h_success
  have hfind' : (db.insert pos l obj).find? (fr_hyps[i]'hi) = some (.hyp ess f lbl) := by
    simpa [h_pres] using hfind
  exact ⟨ess, f, lbl, hfind'⟩

/-- Float well-formedness in a frame is preserved when inserting at a fresh label. -/
theorem frame_float_wf_insert_ne
  (db : DB) (pos : Pos) (l : String) (obj : String → Object)
  (fr_hyps : Array String)
  (h_fr : frame_float_wf db fr_hyps)
  (h_not_in : ∀ (i : Nat) (hi : i < fr_hyps.size), fr_hyps[i]'hi ≠ l)
  (h_success : (db.insert pos l obj).error? = none) :
  frame_float_wf (db.insert pos l obj) fr_hyps := by
  intro i hi f lbl hfind
  have h_ne : fr_hyps[i]'hi ≠ l := h_not_in i hi
  have h_pres := DB.find?_insert_ne db pos l (fr_hyps[i]'hi) obj h_ne h_success
  have hfind' : db.find? (fr_hyps[i]'hi) = some (.hyp false f lbl) := by
    simpa [h_pres] using hfind
  exact h_fr i hi f lbl hfind'

/-- Adding an *essential* hyp (not a float) preserves the frame-level uniqueness invariant,
    assuming the insert succeeds and the label is fresh. -/
theorem frame_unique_floats_add_essential
  (db : DB) (hyps : Array String) (pos : Pos) (l : String) (f : Formula)
  (h_unique : frame_has_unique_floats db hyps)
  (h_success : (db.insert pos l (.hyp true f)).error? = none) :
  frame_has_unique_floats (db.insert pos l (.hyp true f)) (hyps.push l) := by
  classical
  unfold frame_has_unique_floats at h_unique ⊢
  intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
  have hsz : (hyps.push l).size = hyps.size + 1 := by simp
  -- Check if i or j is the newly added index
  by_cases hi_new : i = hyps.size
  · -- i points to the newly inserted label, but hypotheses claim it's a float → contradiction
    have h_lbli : (hyps.push l)[i] = l := by simp [hi_new]
    rw [h_lbli] at h_fi
    have h_contra : False := by
      have h_inserted := DB.find?_insert_self_hyp db pos l true f h_success
      have h_obj : Object.hyp true f l = Object.hyp false fi lbli := by
        rw [h_inserted] at h_fi
        exact Option.some.inj h_fi
      have h_flag := congrArg (fun o => match o with | Object.hyp b _ _ => b | _ => false) h_obj
      simp at h_flag
    exact False.elim h_contra
  · by_cases hj_new : j = hyps.size
    · -- Symmetric case: j is new index
      have h_lblj : (hyps.push l)[j] = l := by simp [hj_new]
      rw [h_lblj] at h_fj
      have h_contra : False := by
        have h_inserted := DB.find?_insert_self_hyp db pos l true f h_success
        have h_obj : Object.hyp true f l = Object.hyp false fj lblj := by
          rw [h_inserted] at h_fj
          exact Option.some.inj h_fj
        have h_flag := congrArg (fun o => match o with | Object.hyp b _ _ => b | _ => false) h_obj
        simp at h_flag
      exact False.elim h_contra
    · -- Both indices refer to old entries
      have hi_lt_succ : i < hyps.size + 1 := by simpa [hsz] using hi
      have hj_lt_succ : j < hyps.size + 1 := by simpa [hsz] using hj
      have hi_le : i ≤ hyps.size := Nat.le_of_lt_succ hi_lt_succ
      have hj_le : j ≤ hyps.size := Nat.le_of_lt_succ hj_lt_succ
      have hi_old : i < hyps.size := by
        rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
        · exact hi_lt
        · exact (hi_new hi_eq).elim
      have hj_old : j < hyps.size := by
        rcases Nat.lt_or_eq_of_le hj_le with hj_lt | hj_eq
        · exact hj_lt
        · exact (hj_new hj_eq).elim
      -- Preserve original labels for old indices
      have h_lbli_old : (hyps.push l)[i] = hyps[i] := by
        simp [Array.getElem_push_lt, hi_old]
      have h_lblj_old : (hyps.push l)[j] = hyps[j] := by
        simp [Array.getElem_push_lt, hj_old]
      rw [h_lbli_old] at h_fi
      rw [h_lblj_old] at h_fj
      -- Show l is distinct from any existing hypothesis label
      have h_l_ne_i : l ≠ hyps[i] := by
        intro h_eq
        -- If hyps[i] = l, then find? l would be the newly inserted essential hyp,
        -- contradicting h_fi which says it's a float hyp.
        have h_fi_l : (db.insert pos l (.hyp true f)).find? l = some (.hyp false fi lbli) := by
          simpa [h_eq] using h_fi
        have h_inserted := DB.find?_insert_self_hyp db pos l true f h_success
        have h_obj : Object.hyp true f l = Object.hyp false fi lbli := by
          rw [h_inserted] at h_fi_l
          exact Option.some.inj h_fi_l
        have h_false : False := by
          cases (congrArg (fun o => match o with | Object.hyp b _ _ => b | _ => false) h_obj)
        exact h_false.elim
      have h_l_ne_j : l ≠ hyps[j] := by
        intro h_eq
        have h_fj_l : (db.insert pos l (.hyp true f)).find? l = some (.hyp false fj lblj) := by
          simpa [h_eq] using h_fj
        have h_inserted := DB.find?_insert_self_hyp db pos l true f h_success
        have h_obj : Object.hyp true f l = Object.hyp false fj lblj := by
          rw [h_inserted] at h_fj_l
          exact Option.some.inj h_fj_l
        have h_false : False := by
          cases (congrArg (fun o => match o with | Object.hyp b _ _ => b | _ => false) h_obj)
        exact h_false.elim
      -- Use insert_find_preserved to rewrite lookups back to db
      have h_pres_i := insert_find_preserved db pos l hyps[i] (.hyp true f) h_l_ne_i h_success
      have h_pres_j := insert_find_preserved db pos l hyps[j] (.hyp true f) h_l_ne_j h_success
      have h_fi_db : db.find? hyps[i] = some (.hyp false fi lbli) := by
        simpa [h_pres_i] using h_fi
      have h_fj_db : db.find? hyps[j] = some (.hyp false fj lblj) := by
        simpa [h_pres_j] using h_fj
      -- Apply the original uniqueness hypothesis
      exact h_unique i j hi_old hj_old h_ne fi fj lbli lblj h_fi_db h_fj_db h_szi h_szj

/-- If a formula has float shape, it is exactly `[const, var]`. -/
theorem floatShape_components (f : Formula) (h_shape : f.isFloatShape = true) :
  f.size = 2 ∧ ∃ c v, f[0]! = .const c ∧ f[1]! = .var v := by
  simpa [WF.WellFormedFloat] using (WF.wellFormedFloat_of_isFloatShape (f := f) h_shape)

/-- Adding a *float* hyp preserves the frame-level uniqueness invariant,
    assuming the new float is well-formed and not a duplicate. -/
theorem frame_unique_floats_add_float
  (db : DB) (hyps : Array String) (pos : Pos) (l : String) (f : Formula)
  (h_unique : frame_has_unique_floats db hyps)
  (h_exist : frame_hyps_exist db hyps)
  (h_float_wf : frame_float_wf db hyps)
  (h_shape : f.isFloatShape = true)
  (h_dup : ¬ ∃ (h_label : String),
    h_label ∈ hyps.toList ∧
    ∃ (prevF : Formula) (lbl : String),
      db.find? h_label = some (.hyp false prevF lbl) ∧
      prevF.size >= 2 ∧
      prevF[1]! = .var f[1]!.value)
  (h_success : (db.insert pos l (.hyp false f)).error? = none) :
  frame_has_unique_floats (db.insert pos l (.hyp false f)) (hyps.push l) := by
  classical
  have h_fresh : db.find? l = none :=
    insert_hyp_success_implies_fresh db pos l false f h_success
  have h_not_in : ∀ (i : Nat) (hi : i < hyps.size), hyps[i]'hi ≠ l :=
    frame_hyps_exist_not_in db hyps l h_exist h_fresh
  obtain ⟨_h_size, _c, v, _h0, h1⟩ := floatShape_components f h_shape
  have h_v : f[1]!.value = v := by
    simp [Sym.value, h1]
  unfold frame_has_unique_floats at h_unique ⊢
  intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
  have hsz : (hyps.push l).size = hyps.size + 1 := by simp
  by_cases hi_new : i = hyps.size
  · -- i is the new label
    have h_lbl_i : (hyps.push l)[i] = l := by simp [hi_new]
    have h_self := DB.find?_insert_self_hyp db pos l false f h_success
    have h_fi_l : (db.insert pos l (.hyp false f)).find? l = some (.hyp false fi lbli) := by
      simpa [h_lbl_i] using h_fi
    have h_obj : Object.hyp false f l = Object.hyp false fi lbli := by
      rw [h_self] at h_fi_l
      exact Option.some.inj h_fi_l
    cases h_obj
    -- j must be old
    have hj_lt_succ : j < hyps.size + 1 := by simpa [hsz] using hj
    have hj_le : j ≤ hyps.size := Nat.le_of_lt_succ hj_lt_succ
    have hj_old : j < hyps.size := by
      rcases Nat.lt_or_eq_of_le hj_le with hj_lt | hj_eq
      · exact hj_lt
      ·
        have h_ij : i = j := by
          calc
            i = hyps.size := hi_new
            _ = j := hj_eq.symm
        exact (h_ne h_ij).elim
    have h_lblj_old : (hyps.push l)[j] = hyps[j] := by
      simp [Array.getElem_push_lt, hj_old]
    have h_ne_j : hyps[j] ≠ l := h_not_in j hj_old
    have h_pres_j := insert_find_preserved db pos l (hyps[j]) (.hyp false f) (Ne.symm h_ne_j) h_success
    have h_fj_db : db.find? hyps[j] = some (.hyp false fj lblj) := by
      simpa [h_lblj_old, h_pres_j] using h_fj
    have h_fj_shape : fj.isFloatShape = true := h_float_wf j hj_old fj lblj h_fj_db
    obtain ⟨h_fj_size, _c', vj, _h0', h_fj1⟩ := floatShape_components fj h_fj_shape
    have h_vj : (match fj[1]! with | .var v' => v' | _ => "") = vj := by
      simp [h_fj1]
    have h_v_ne : v ≠ vj := by
      intro h_eq
      apply h_dup
      have h_mem : hyps[j] ∈ hyps.toList :=
        Array.getElem_mem_toList (xs := hyps) (i := j) (h := hj_old)
      refine ⟨hyps[j], h_mem, fj, lblj, h_fj_db, ?_, ?_⟩
      · omega
      · simp [h_fj1, h_eq.symm, h_v.symm]
    -- Finish: vi = v, vj = vj
    have h_vi : (match f[1]! with | .var v' => v' | _ => "") = v := by
      simp [h1]
    simpa [h_vi, h_vj] using h_v_ne
  · by_cases hj_new : j = hyps.size
    · -- symmetric: j is new label
      have h_lbl_j : (hyps.push l)[j] = l := by simp [hj_new]
      have h_self := DB.find?_insert_self_hyp db pos l false f h_success
      have h_fj_l : (db.insert pos l (.hyp false f)).find? l = some (.hyp false fj lblj) := by
        simpa [h_lbl_j] using h_fj
      have h_obj : Object.hyp false f l = Object.hyp false fj lblj := by
        rw [h_self] at h_fj_l
        exact Option.some.inj h_fj_l
      cases h_obj
      -- i must be old
      have hi_lt_succ : i < hyps.size + 1 := by simpa [hsz] using hi
      have hi_le : i ≤ hyps.size := Nat.le_of_lt_succ hi_lt_succ
      have hi_old : i < hyps.size := by
        rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
        · exact hi_lt
        ·
          have h_ij : i = j := by
            calc
              i = hyps.size := hi_eq
              _ = j := hj_new.symm
          exact (h_ne h_ij).elim
      have h_lbli_old : (hyps.push l)[i] = hyps[i] := by
        simp [Array.getElem_push_lt, hi_old]
      have h_ne_i : hyps[i] ≠ l := h_not_in i hi_old
      have h_pres_i := insert_find_preserved db pos l (hyps[i]) (.hyp false f) (Ne.symm h_ne_i) h_success
      have h_fi_db : db.find? hyps[i] = some (.hyp false fi lbli) := by
        simpa [h_lbli_old, h_pres_i] using h_fi
      have h_fi_shape : fi.isFloatShape = true := h_float_wf i hi_old fi lbli h_fi_db
      obtain ⟨h_fi_size, _c', vi, _h0', h_fi1⟩ := floatShape_components fi h_fi_shape
      have h_vi : (match fi[1]! with | .var v' => v' | _ => "") = vi := by
        simp [h_fi1]
      have h_v_ne : vi ≠ v := by
        intro h_eq
        apply h_dup
        have h_mem : hyps[i] ∈ hyps.toList :=
          Array.getElem_mem_toList (xs := hyps) (i := i) (h := hi_old)
        refine ⟨hyps[i], h_mem, fi, lbli, h_fi_db, ?_, ?_⟩
        · omega
        · simp [h_fi1, h_eq, h_v.symm]
      have h_vj : (match f[1]! with | .var v' => v' | _ => "") = v := by
        simp [h1]
      -- vi ≠ vj
      have h_vi_ne_vj : vi ≠ v := h_v_ne
      simpa [h_vi, h_vj] using h_vi_ne_vj
    · -- both indices refer to old entries
      have hi_lt_succ : i < hyps.size + 1 := by simpa [hsz] using hi
      have hj_lt_succ : j < hyps.size + 1 := by simpa [hsz] using hj
      have hi_le : i ≤ hyps.size := Nat.le_of_lt_succ hi_lt_succ
      have hj_le : j ≤ hyps.size := Nat.le_of_lt_succ hj_lt_succ
      have hi_old : i < hyps.size := by
        rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
        · exact hi_lt
        · exact (hi_new hi_eq).elim
      have hj_old : j < hyps.size := by
        rcases Nat.lt_or_eq_of_le hj_le with hj_lt | hj_eq
        · exact hj_lt
        · exact (hj_new hj_eq).elim
      have h_lbli_old : (hyps.push l)[i] = hyps[i] := by
        simp [Array.getElem_push_lt, hi_old]
      have h_lblj_old : (hyps.push l)[j] = hyps[j] := by
        simp [Array.getElem_push_lt, hj_old]
      have h_ne_i : hyps[i] ≠ l := h_not_in i hi_old
      have h_ne_j : hyps[j] ≠ l := h_not_in j hj_old
      have h_pres_i := insert_find_preserved db pos l (hyps[i]) (.hyp false f) (Ne.symm h_ne_i) h_success
      have h_pres_j := insert_find_preserved db pos l (hyps[j]) (.hyp false f) (Ne.symm h_ne_j) h_success
      have h_fi_db : db.find? hyps[i] = some (.hyp false fi lbli) := by
        simpa [h_lbli_old, h_pres_i] using h_fi
      have h_fj_db : db.find? hyps[j] = some (.hyp false fj lblj) := by
        simpa [h_lblj_old, h_pres_j] using h_fj
      exact h_unique i j hi_old hj_old h_ne fi fj lbli lblj h_fi_db h_fj_db h_szi h_szj

/-- Extract variable name from a formula (assuming it's at position 1) -/
def extract_var (f : Formula) : String :=
  if h : 1 < f.size then
    match f[1] with
    | .var v => v
    | .const c => c  -- Shouldn't happen for well-formed floats
  else ""

/-- Helper: behaviour of the duplicate-detection loop in `insertHyp` (float case). -/
theorem insertHyp_loop_behavior
  (db : DB) (pos : Pos) (l : String) (f : Formula)
  (h_no_error : db.error? = none) (h_size : f.size >= 2) :
  let v := f[1]!.value
  (∃ (h_label : String),
    h_label ∈ db.frame.hyps.toList ∧
    ∃ (prevF : Formula) (lbl : String),
      db.find? h_label = some (.hyp false prevF lbl) ∧
      prevF.size >= 2 ∧
      prevF[1]! = .var v) →
  (db.insertHyp pos l false f).error? ≠ none := by
  classical
  intro v h_dup
  have _ := h_no_error
  rcases h_dup with ⟨h_label, h_mem, prevF, lbl, h_find, h_size_prev, h_var⟩
  have h_dup' : db.floatVarOccursInFrame v = true := by
    unfold DB.floatVarOccursInFrame
    apply List.any_eq_true.2
    refine ⟨h_label, h_mem, ?_⟩
    simp [h_find, h_size_prev, h_var]
  have h_dup'' : db.floatVarOccursInFrame f[1]!.value = true := by
    simpa using h_dup'
  have h_checks_err : (db.insertHypChecks pos false f).error = true := by
    unfold DB.insertHypChecks
    by_cases h_head : f.hasConstHead
    · by_cases h_shape : f.isFloatShape
      ·
        simp [h_head, h_shape, h_no_error, h_size, h_dup'', DB.mkError, DB.error]
      · simp [h_head, h_shape, h_no_error, DB.mkError, DB.error]
    · simp [h_head, DB.mkError, DB.error]
  have h_err : (db.insertHyp pos l false f).error = true := by
    simp [DB.insertHyp, h_checks_err]
  exact (_root_.Metamath.ParserOps.error_iff_error?_isSome (db.insertHyp pos l false f)).1 h_err

/-- If insertHyp is called with a float that would duplicate an existing float variable,
    it sets an error. -/
theorem insertHyp_detects_duplicate
  (db : DB) (pos : Pos) (l : String) (f : Formula)
  (h_no_error : db.error? = none)
  (h_size : f.size >= 2) :
  let v := f[1]!.value
  -- If there exists a float in current frame with same variable
  (∃ (h_label : String),
    h_label ∈ db.frame.hyps.toList ∧
    ∃ (prevF : Formula) (lbl : String),
      db.find? h_label = some (.hyp false prevF lbl) ∧
      prevF.size >= 2 ∧
      prevF[1]! = .var v) →
  -- Then insertHyp sets error
  (db.insertHyp pos l false f).error? ≠ none := by
  classical
  intro v h_dup
  have h_loop :=
    insertHyp_loop_behavior db pos l f h_no_error h_size h_dup
  simpa using h_loop

/-- Essential hypotheses preserve uniqueness (either by failing with error or
    by extending the frame without adding floats). -/
theorem insertHyp_essential_preserves_unique
  (db : DB) (pos : Pos) (l : String) (f : Formula)
  (h_unique : db_has_unique_floats db) (h_no_error : db.error? = none) :
  let db' := db.insertHyp pos l true f
  db'.error? ≠ none ∨ db_has_unique_floats db' := by
  classical
  dsimp
  rcases h_unique with ⟨h_curr_unique, h_curr_exist, h_curr_float_wf, h_frames⟩
  by_cases h_success : (db.insertHyp pos l true f).error? = none
  · -- Success: uniqueness is preserved
    right
    obtain ⟨db_after_check, h_check_eq, h_check_ok, h_insert_ok⟩ :=
      _root_.Metamath.ParserOps.insertHyp_success_conditions db pos l true f h_success
    have h_check_ok' : (DB.insertHypChecks db pos true f).error? = none := by
      simpa [h_check_eq] using h_check_ok
    have h_check_eq_db : DB.insertHypChecks db pos true f = db :=
      _root_.Metamath.ParserOps.insertHypChecks_eq_db_of_no_error db pos true f h_check_ok'
    have h_insert_ok' :
        ((DB.insertHypChecks db pos true f).insert pos l (.hyp true f)).error? = none := by
      simpa [h_check_eq] using h_insert_ok
    have h_ins : (db.insert pos l (.hyp true f)).error? = none := by
      simpa [h_check_eq_db] using h_insert_ok'
    have h_insert_err : (db.insert pos l (.hyp true f)).error = false := by
      simp [DB.error, h_ins]
    have h_db_err : db.error = false := by
      simp [DB.error, h_no_error]
    have h_db' :
        db.insertHyp pos l true f =
          (db.insert pos l (.hyp true f)).withHyps (fun hyps => hyps.push l) := by
      simp [DB.insertHyp, h_check_eq_db, h_db_err, h_insert_err]
    -- Current frame
    have h_frame : frame_has_unique_floats (db.insert pos l (.hyp true f))
        (db.frame.hyps.push l) :=
      frame_unique_floats_add_essential db db.frame.hyps pos l f h_curr_unique h_ins
    have h_frame' :
        frame_has_unique_floats (db.insert pos l (.hyp true f))
          ((db.insert pos l (.hyp true f)).frame.hyps.push l) := by
      simpa [insert_frame_unchanged db pos l (.hyp true f)] using h_frame
    have h_frame_db' :
        frame_has_unique_floats (db.insertHyp pos l true f)
          (db.insertHyp pos l true f).frame.hyps := by
      -- transport across withHyps
      have h_equiv :=
        frame_has_unique_floats_withHyps (db.insert pos l (.hyp true f))
          (fun hyps => hyps.push l)
          ((db.insert pos l (.hyp true f)).frame.hyps.push l)
      simpa [h_db'] using (h_equiv.mpr h_frame')
    -- Current frame: every label resolves to a hypothesis
    have h_fresh : db.find? l = none :=
      insert_hyp_success_implies_fresh db pos l true f h_ins
    have h_not_in_curr :
        ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l :=
      frame_hyps_exist_not_in db db.frame.hyps l h_curr_exist h_fresh
    have h_exist_curr' :
        frame_hyps_exist (db.insert pos l (.hyp true f)) (db.frame.hyps.push l) := by
      intro i hi
      by_cases hi_new : i = db.frame.hyps.size
      · have h_lbl : (db.frame.hyps.push l)[i] = l := by simp [hi_new]
        have h_self := DB.find?_insert_self_hyp db pos l true f h_ins
        exact ⟨true, f, l, by simpa [h_lbl] using h_self⟩
      · have hsz : (db.frame.hyps.push l).size = db.frame.hyps.size + 1 := by simp
        have hi_lt_succ : i < db.frame.hyps.size + 1 := by simpa [hsz] using hi
        have hi_le : i ≤ db.frame.hyps.size := Nat.le_of_lt_succ hi_lt_succ
        have hi_old : i < db.frame.hyps.size := by
          rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
          · exact hi_lt
          · exact (hi_new hi_eq).elim
        rcases h_curr_exist i hi_old with ⟨ess, fml, lbl, hfind⟩
        have h_ne : db.frame.hyps[i]'hi_old ≠ l := h_not_in_curr i hi_old
        have h_pres := insert_find_preserved db pos l (db.frame.hyps[i]) (.hyp true f) (Ne.symm h_ne) h_ins
        have h_lbl : (db.frame.hyps.push l)[i] = db.frame.hyps[i] := by
          simp [Array.getElem_push_lt, hi_old]
        have hfind' : (db.insert pos l (.hyp true f)).find? (db.frame.hyps[i]) = some (.hyp ess fml lbl) := by
          simpa [h_pres] using hfind
        exact ⟨ess, fml, lbl, by simpa [h_lbl] using hfind'⟩
    have h_exist_curr'' :
        frame_hyps_exist (db.insert pos l (.hyp true f))
          ((db.insert pos l (.hyp true f)).frame.hyps.push l) := by
      simpa [insert_frame_unchanged db pos l (.hyp true f)] using h_exist_curr'
    have h_exist_db' :
        frame_hyps_exist (db.insertHyp pos l true f)
          (db.insertHyp pos l true f).frame.hyps := by
      have h_equiv :=
        frame_hyps_exist_withHyps (db.insert pos l (.hyp true f))
          (fun hyps => hyps.push l)
          ((db.insert pos l (.hyp true f)).frame.hyps.push l)
      simpa [h_db'] using (h_equiv.mpr h_exist_curr'')
    -- Current frame: float hypotheses remain well-formed
    have h_float_old :
        frame_float_wf (db.insert pos l (.hyp true f)) db.frame.hyps :=
      frame_float_wf_insert_ne db pos l (.hyp true f) db.frame.hyps
        h_curr_float_wf h_not_in_curr h_ins
    have h_float_curr' :
        frame_float_wf (db.insert pos l (.hyp true f)) (db.frame.hyps.push l) := by
      intro i hi fml lbl hfind
      by_cases hi_new : i = db.frame.hyps.size
      · have h_lbl : (db.frame.hyps.push l)[i] = l := by simp [hi_new]
        have h_self := DB.find?_insert_self_hyp db pos l true f h_ins
        have h_contra : some (Object.hyp true f l) = some (Object.hyp false fml lbl) := by
          calc
            some (Object.hyp true f l)
                = (db.insert pos l (.hyp true f)).find? l := h_self.symm
            _ = (db.insert pos l (.hyp true f)).find? (db.frame.hyps.push l)[i] := by
                simp [h_lbl]
            _ = some (Object.hyp false fml lbl) := hfind
        cases Option.some.inj h_contra
      · have hsz : (db.frame.hyps.push l).size = db.frame.hyps.size + 1 := by simp
        have hi_lt_succ : i < db.frame.hyps.size + 1 := by simpa [hsz] using hi
        have hi_le : i ≤ db.frame.hyps.size := Nat.le_of_lt_succ hi_lt_succ
        have hi_old : i < db.frame.hyps.size := by
          rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
          · exact hi_lt
          · exact (hi_new hi_eq).elim
        have h_lbl : (db.frame.hyps.push l)[i] = db.frame.hyps[i] := by
          simp [Array.getElem_push_lt, hi_old]
        have hfind' :
            (db.insert pos l (.hyp true f)).find? (db.frame.hyps[i]) =
              some (.hyp false fml lbl) := by
          simpa [h_lbl] using hfind
        exact h_float_old i hi_old fml lbl hfind'
    have h_float_curr'' :
        frame_float_wf (db.insert pos l (.hyp true f))
          ((db.insert pos l (.hyp true f)).frame.hyps.push l) := by
      simpa [insert_frame_unchanged db pos l (.hyp true f)] using h_float_curr'
    have h_float_db' :
        frame_float_wf (db.insertHyp pos l true f)
          (db.insertHyp pos l true f).frame.hyps := by
      have h_equiv :=
        frame_float_wf_withHyps (db.insert pos l (.hyp true f))
          (fun hyps => hyps.push l)
          ((db.insert pos l (.hyp true f)).frame.hyps.push l)
      simpa [h_db'] using (h_equiv.mpr h_float_curr'')
    -- Assertions: unchanged by essential hyp insertion
    have h_assert :
        ∀ (label : String) (fmla : Formula) (fr : Frame) (proof : String),
          (db.insertHyp pos l true f).find? label =
              some (.assert fmla fr proof) →
          frame_has_unique_floats (db.insertHyp pos l true f) fr.hyps ∧
          frame_hyps_exist (db.insertHyp pos l true f) fr.hyps ∧
          frame_float_wf (db.insertHyp pos l true f) fr.hyps := by
      intro label fmla fr proof h_find
      -- First rewrite the lookup through the withHyps wrapper
      have h_find_insert :
          (db.insert pos l (.hyp true f)).find? label =
            some (.assert fmla fr proof) := by
        simpa [h_db', DB.withHyps_find?] using h_find
      -- Show label ≠ l (otherwise we would find the newly inserted hyp)
      have h_label_ne : label ≠ l := by
        intro h_eq
        have h_self := DB.find?_insert_self_hyp db pos l true f h_ins
        have h_contra :
            some (Object.assert fmla fr proof) =
              some (Object.hyp true f l) := by
          calc
            some (Object.assert fmla fr proof)
                = (db.insert pos l (.hyp true f)).find? label := h_find_insert.symm
            _ = (db.insert pos l (.hyp true f)).find? l := by simp [h_eq]
            _ = some (Object.hyp true f l) := h_self
        -- Constructors differ: contradiction
        cases Option.some.inj h_contra
      -- Pull the assertion lookup back to the original db
      have h_find_db :
          db.find? label = some (.assert fmla fr proof) := by
        have h_pres := insert_find_preserved db pos l label (.hyp true f) (Ne.symm h_label_ne) h_ins
        simpa [h_pres] using h_find_insert
      -- Use the original uniqueness assumption on assertion frames
      have h_frames := h_frames label fmla fr proof h_find_db
      rcases h_frames with ⟨h_fr_unique, h_fr_exist, h_fr_float_wf⟩
      have h_l_not_in_fr :
          ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l :=
        frame_hyps_exist_not_in db fr.hyps l h_fr_exist h_fresh
      -- Show that inserting an essential hyp preserves frame_has_unique_floats
      have h_frames_insert :
          frame_has_unique_floats (db.insert pos l (.hyp true f)) fr.hyps := by
        intro i j hi hj hneq fi fj lbli lblj hfi hfj hsi hsj
        -- If either index refers to the newly inserted label l, contradiction with hyp=false in hfi/hfj
        by_cases h_li : fr.hyps[i] = l
        · have h_self := DB.find?_insert_self_hyp db pos l true f h_ins
          have hfi_l : (db.insert pos l (.hyp true f)).find? l = some (Object.hyp false fi lbli) := by
            simpa [h_li] using hfi
          have h_contra : some (Object.hyp false fi lbli) = some (Object.hyp true f l) := by
            calc
              some (Object.hyp false fi lbli)
                  = (db.insert pos l (.hyp true f)).find? l := hfi_l.symm
              _ = some (Object.hyp true f l) := h_self
          cases Option.some.inj h_contra
        · by_cases h_lj : fr.hyps[j] = l
          · have h_self := DB.find?_insert_self_hyp db pos l true f h_ins
            have hfj_l : (db.insert pos l (.hyp true f)).find? l = some (Object.hyp false fj lblj) := by
              simpa [h_lj] using hfj
            have h_contra : some (Object.hyp false fj lblj) = some (Object.hyp true f l) := by
              calc
                some (Object.hyp false fj lblj)
                    = (db.insert pos l (.hyp true f)).find? l := hfj_l.symm
                _ = some (Object.hyp true f l) := h_self
            cases Option.some.inj h_contra
          · -- Neither index is the new label; use preservation of lookups
            have h_fi_db : db.find? fr.hyps[i] = some (.hyp false fi lbli) := by
              have h_pres := insert_find_preserved db pos l (fr.hyps[i]) (.hyp true f) (Ne.symm h_li) h_ins
              simpa [h_pres] using hfi
            have h_fj_db : db.find? fr.hyps[j] = some (.hyp false fj lblj) := by
              have h_pres := insert_find_preserved db pos l (fr.hyps[j]) (.hyp true f) (Ne.symm h_lj) h_ins
              simpa [h_pres] using hfj
            exact h_fr_unique i j hi hj hneq fi fj lbli lblj h_fi_db h_fj_db hsi hsj
      have h_frames_exist :
          frame_hyps_exist (db.insert pos l (.hyp true f)) fr.hyps :=
        frame_hyps_exist_insert_ne db pos l (.hyp true f) fr.hyps
          h_fr_exist h_l_not_in_fr h_ins
      have h_frames_float :
          frame_float_wf (db.insert pos l (.hyp true f)) fr.hyps :=
        frame_float_wf_insert_ne db pos l (.hyp true f) fr.hyps
          h_fr_float_wf h_l_not_in_fr h_ins
      -- Transport through withHyps
      have h_equiv :=
        frame_has_unique_floats_withHyps (db.insert pos l (.hyp true f))
          (fun hyps => hyps.push l) fr.hyps
      have h_equiv_exist :=
        frame_hyps_exist_withHyps (db.insert pos l (.hyp true f))
          (fun hyps => hyps.push l) fr.hyps
      have h_equiv_float :=
        frame_float_wf_withHyps (db.insert pos l (.hyp true f))
          (fun hyps => hyps.push l) fr.hyps
      refine ⟨?_, ?_, ?_⟩
      · simpa [h_db'] using (h_equiv.mpr h_frames_insert)
      · simpa [h_db'] using (h_equiv_exist.mpr h_frames_exist)
      · simpa [h_db'] using (h_equiv_float.mpr h_frames_float)
    exact ⟨h_frame_db', h_exist_db', h_float_db', h_assert⟩
  · -- Failure: insertHyp sets error
    left
    exact h_success

/-- When a float hypothesis is fresh (no duplicate variable), uniqueness is preserved. -/
theorem insertHyp_float_fresh_preserves_unique
  (db : DB) (pos : Pos) (l : String) (f : Formula)
  (h_unique : db_has_unique_floats db) (h_no_error : db.error? = none)
  (_h_size : f.size >= 2)
  (h_dup : ¬ ∃ (h_label : String),
    h_label ∈ db.frame.hyps.toList ∧
    ∃ (prevF : Formula) (lbl : String),
      db.find? h_label = some (.hyp false prevF lbl) ∧
      prevF.size >= 2 ∧
      prevF[1]! = .var f[1]!.value)
  (h_success : (db.insertHyp pos l false f).error? = none) :
  db_has_unique_floats (db.insertHyp pos l false f) := by
  classical
  rcases h_unique with ⟨h_curr_unique, h_curr_exist, h_curr_float_wf, h_frames⟩
  -- Extract the insert success conditions
  obtain ⟨db_after_check, h_def_check, h_check_ok, h_insert_ok⟩ :=
    _root_.Metamath.ParserOps.insertHyp_success_conditions db pos l false f h_success
  have h_eq_check : db_after_check = db := by
    have h_no_err : (DB.insertHypChecks db pos false f).error? = none := by
      simpa [h_def_check] using h_check_ok
    have h_eq' := _root_.Metamath.ParserOps.insertHypChecks_eq_db_of_no_error db pos false f h_no_err
    calc
      db_after_check = DB.insertHypChecks db pos false f := h_def_check
      _ = db := h_eq'
  have h_checks_eq : DB.insertHypChecks db pos false f = db := by
    exact h_def_check.symm.trans h_eq_check
  have h_ins : (db.insert pos l (.hyp false f)).error? = none := by
    simpa [h_eq_check] using h_insert_ok
  -- Shape check must have passed
  have h_db_err : db.error = false := by
    simp [DB.error, h_no_error]
  have h_shape : f.isFloatShape = true := by
    have h_checks_no_err : (DB.insertHypChecks db pos false f).error? = none := by
      simpa [h_def_check, h_eq_check] using h_check_ok
    by_cases h_head : f.hasConstHead
    · cases h_shape' : f.isFloatShape with
      | true =>
          simp
      | false =>
          have h_fail : (DB.insertHypChecks db pos false f).error? ≠ none := by
            simp [DB.insertHypChecks, h_head, h_shape', h_no_error, DB.mkError, DB.error]
          exact (h_fail h_checks_no_err).elim
    ·
      have h_fail : (DB.insertHypChecks db pos false f).error? ≠ none := by
        simp [DB.insertHypChecks, h_head, DB.mkError, DB.error]
      exact (h_fail h_checks_no_err).elim
  -- insertHyp reduces to insert + withHyps when checks and insert succeed
  have h_ins_err : (db.insert pos l (.hyp false f)).error = false := by
    simpa [DB.error] using h_ins
  have h_db' :
      db.insertHyp pos l false f =
        (db.insert pos l (.hyp false f)).withHyps (fun hyps => hyps.push l) := by
    simp [DB.insertHyp, h_checks_eq, h_db_err, h_ins_err]
  -- Current frame uniqueness after insert
  have h_frame :
      frame_has_unique_floats (db.insert pos l (.hyp false f))
        (db.frame.hyps.push l) :=
    frame_unique_floats_add_float db db.frame.hyps pos l f
      h_curr_unique h_curr_exist h_curr_float_wf h_shape h_dup h_ins
  have h_frame' :
      frame_has_unique_floats (db.insert pos l (.hyp false f))
        ((db.insert pos l (.hyp false f)).frame.hyps.push l) := by
    simpa [insert_frame_unchanged db pos l (.hyp false f)] using h_frame
  have h_frame_db' :
      frame_has_unique_floats (db.insertHyp pos l false f)
        (db.insertHyp pos l false f).frame.hyps := by
    have h_equiv :=
      frame_has_unique_floats_withHyps (db.insert pos l (.hyp false f))
        (fun hyps => hyps.push l)
        ((db.insert pos l (.hyp false f)).frame.hyps.push l)
    simpa [h_db'] using (h_equiv.mpr h_frame')
  -- Current frame: existence and float well-formedness
  have h_fresh : db.find? l = none :=
    insert_hyp_success_implies_fresh db pos l false f h_ins
  have h_not_in_curr :
      ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l :=
    frame_hyps_exist_not_in db db.frame.hyps l h_curr_exist h_fresh
  have h_exist_curr' :
      frame_hyps_exist (db.insert pos l (.hyp false f)) (db.frame.hyps.push l) := by
    intro i hi
    by_cases hi_new : i = db.frame.hyps.size
    · have h_lbl : (db.frame.hyps.push l)[i] = l := by simp [hi_new]
      have h_self := DB.find?_insert_self_hyp db pos l false f h_ins
      exact ⟨false, f, l, by simpa [h_lbl] using h_self⟩
    · have hsz : (db.frame.hyps.push l).size = db.frame.hyps.size + 1 := by simp
      have hi_lt_succ : i < db.frame.hyps.size + 1 := by simpa [hsz] using hi
      have hi_le : i ≤ db.frame.hyps.size := Nat.le_of_lt_succ hi_lt_succ
      have hi_old : i < db.frame.hyps.size := by
        rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
        · exact hi_lt
        · exact (hi_new hi_eq).elim
      rcases h_curr_exist i hi_old with ⟨ess, fml, lbl, hfind⟩
      have h_ne : db.frame.hyps[i]'hi_old ≠ l := h_not_in_curr i hi_old
      have h_pres := insert_find_preserved db pos l (db.frame.hyps[i]) (.hyp false f) (Ne.symm h_ne) h_ins
      have h_lbl : (db.frame.hyps.push l)[i] = db.frame.hyps[i] := by
        simp [Array.getElem_push_lt, hi_old]
      have hfind' : (db.insert pos l (.hyp false f)).find? (db.frame.hyps[i]) = some (.hyp ess fml lbl) := by
        simpa [h_pres] using hfind
      exact ⟨ess, fml, lbl, by simpa [h_lbl] using hfind'⟩
  have h_exist_curr'' :
      frame_hyps_exist (db.insert pos l (.hyp false f))
        ((db.insert pos l (.hyp false f)).frame.hyps.push l) := by
    simpa [insert_frame_unchanged db pos l (.hyp false f)] using h_exist_curr'
  have h_exist_db' :
      frame_hyps_exist (db.insertHyp pos l false f)
        (db.insertHyp pos l false f).frame.hyps := by
    have h_equiv :=
      frame_hyps_exist_withHyps (db.insert pos l (.hyp false f))
        (fun hyps => hyps.push l)
        ((db.insert pos l (.hyp false f)).frame.hyps.push l)
    simpa [h_db'] using (h_equiv.mpr h_exist_curr'')
  have h_float_curr' :
      frame_float_wf (db.insert pos l (.hyp false f)) (db.frame.hyps.push l) := by
    intro i hi fml lbl hfind
    by_cases hi_new : i = db.frame.hyps.size
    · have h_lbl : (db.frame.hyps.push l)[i] = l := by simp [hi_new]
      have h_self := DB.find?_insert_self_hyp db pos l false f h_ins
      have h_obj : Object.hyp false f l = Object.hyp false fml lbl := by
        have hfind_l : (db.insert pos l (.hyp false f)).find? l = some (.hyp false fml lbl) := by
          simpa [h_lbl] using hfind
        rw [h_self] at hfind_l
        exact Option.some.inj hfind_l
      cases h_obj
      exact h_shape
    · have hsz : (db.frame.hyps.push l).size = db.frame.hyps.size + 1 := by simp
      have hi_lt_succ : i < db.frame.hyps.size + 1 := by simpa [hsz] using hi
      have hi_le : i ≤ db.frame.hyps.size := Nat.le_of_lt_succ hi_lt_succ
      have hi_old : i < db.frame.hyps.size := by
        rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
        · exact hi_lt
        · exact (hi_new hi_eq).elim
      have h_lbl : (db.frame.hyps.push l)[i] = db.frame.hyps[i] := by
        simp [Array.getElem_push_lt, hi_old]
      have h_ne : db.frame.hyps[i]'hi_old ≠ l := h_not_in_curr i hi_old
      have h_pres := insert_find_preserved db pos l (db.frame.hyps[i]) (.hyp false f) (Ne.symm h_ne) h_ins
      have hfind' : db.find? (db.frame.hyps[i]) = some (.hyp false fml lbl) := by
        simpa [h_lbl, h_pres] using hfind
      exact h_curr_float_wf i hi_old fml lbl hfind'
  have h_float_curr'' :
      frame_float_wf (db.insert pos l (.hyp false f))
        ((db.insert pos l (.hyp false f)).frame.hyps.push l) := by
    simpa [insert_frame_unchanged db pos l (.hyp false f)] using h_float_curr'
  have h_float_db' :
      frame_float_wf (db.insertHyp pos l false f)
        (db.insertHyp pos l false f).frame.hyps := by
    have h_equiv :=
      frame_float_wf_withHyps (db.insert pos l (.hyp false f))
        (fun hyps => hyps.push l)
        ((db.insert pos l (.hyp false f)).frame.hyps.push l)
    simpa [h_db'] using (h_equiv.mpr h_float_curr'')
  -- Assertions: unchanged by float hyp insertion
  have h_assert :
      ∀ (label : String) (fmla : Formula) (fr : Frame) (proof : String),
        (db.insertHyp pos l false f).find? label =
            some (.assert fmla fr proof) →
        frame_has_unique_floats (db.insertHyp pos l false f) fr.hyps ∧
        frame_hyps_exist (db.insertHyp pos l false f) fr.hyps ∧
        frame_float_wf (db.insertHyp pos l false f) fr.hyps := by
    intro label fmla fr proof h_find
    have h_find_insert :
        (db.insert pos l (.hyp false f)).find? label =
          some (.assert fmla fr proof) := by
      simpa [h_db', DB.withHyps_find?] using h_find
    have h_label_ne : label ≠ l := by
      intro h_eq
      have h_self := DB.find?_insert_self_hyp db pos l false f h_ins
      have h_contra :
          some (Object.assert fmla fr proof) =
            some (Object.hyp false f l) := by
        calc
          some (Object.assert fmla fr proof)
              = (db.insert pos l (.hyp false f)).find? label := h_find_insert.symm
          _ = (db.insert pos l (.hyp false f)).find? l := by simp [h_eq]
          _ = some (Object.hyp false f l) := h_self
      cases Option.some.inj h_contra
    have h_find_db :
        db.find? label = some (.assert fmla fr proof) := by
      have h_pres := insert_find_preserved db pos l label (.hyp false f) (Ne.symm h_label_ne) h_ins
      simpa [h_pres] using h_find_insert
    have h_frames' := h_frames label fmla fr proof h_find_db
    rcases h_frames' with ⟨h_fr_unique, h_fr_exist, h_fr_float_wf⟩
    have h_l_not_in_fr :
        ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i]'hi ≠ l :=
      frame_hyps_exist_not_in db fr.hyps l h_fr_exist h_fresh
    have h_frames_insert :
        frame_has_unique_floats (db.insert pos l (.hyp false f)) fr.hyps :=
      frame_has_unique_floats_insert_ne db pos l (fun _ => Object.hyp false f l) fr.hyps
        h_fr_unique h_l_not_in_fr h_ins
    have h_frames_exist :
        frame_hyps_exist (db.insert pos l (.hyp false f)) fr.hyps :=
      frame_hyps_exist_insert_ne db pos l (.hyp false f) fr.hyps
        h_fr_exist h_l_not_in_fr h_ins
    have h_frames_float :
        frame_float_wf (db.insert pos l (.hyp false f)) fr.hyps :=
      frame_float_wf_insert_ne db pos l (.hyp false f) fr.hyps
        h_fr_float_wf h_l_not_in_fr h_ins
    have h_equiv :=
      frame_has_unique_floats_withHyps (db.insert pos l (.hyp false f))
        (fun hyps => hyps.push l) fr.hyps
    have h_equiv_exist :=
      frame_hyps_exist_withHyps (db.insert pos l (.hyp false f))
        (fun hyps => hyps.push l) fr.hyps
    have h_equiv_float :=
      frame_float_wf_withHyps (db.insert pos l (.hyp false f))
        (fun hyps => hyps.push l) fr.hyps
    refine ⟨?_, ?_, ?_⟩
    · simpa [h_db'] using (h_equiv.mpr h_frames_insert)
    · simpa [h_db'] using (h_equiv_exist.mpr h_frames_exist)
    · simpa [h_db'] using (h_equiv_float.mpr h_frames_float)
  exact ⟨h_frame_db', h_exist_db', h_float_db', h_assert⟩

/-! ## Main Theorem -/

/-- **Key Lemma**: insertHyp maintains database uniqueness invariant.

This is the core of the proof. If the database satisfies the uniqueness invariant
and we call insertHyp:
- If it would create a duplicate, error is set
- Otherwise, the invariant is maintained
-/
theorem insertHyp_maintains_db_uniqueness
  (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
  (h_unique : db_has_unique_floats db)
  (h_no_error : db.error? = none) :
  let db' := db.insertHyp pos l ess f
  -- Either error is set (duplicate detected) or invariant maintained
  db'.error? ≠ none ∨ db_has_unique_floats db' := by
  classical
  dsimp
  -- Case analysis on ess (essential vs float)
  by_cases h_ess : ess = true
  · -- Case 1: Essential hypothesis (not a float)
    subst h_ess
    have h := insertHyp_essential_preserves_unique db pos l f h_unique h_no_error
    simpa using h
  · -- Case 2: Float hypothesis (ess = false)
    -- From h_ess, we have ¬(ess = true), which for Bool means ess = false
    have h_ess_false : ess = false := by
      cases ess
      · rfl
      · contradiction
    -- insertHyp checks for duplicates at lines 332-335
    by_cases h_size : f.size >= 2
    · -- Float with valid size
      let v := f[1]!.value
      -- Check if duplicate exists
      by_cases h_dup : ∃ (h_label : String),
        h_label ∈ db.frame.hyps.toList ∧
        ∃ (prevF : Formula) (lbl : String),
          db.find? h_label = some (.hyp false prevF lbl) ∧
          prevF.size >= 2 ∧
          prevF[1]! = .var v
      · -- Duplicate exists → insertHyp sets error
        left
        rw [h_ess_false]
        have h_err := insertHyp_detects_duplicate db pos l f h_no_error h_size h_dup
        exact h_err
      · -- No duplicate → invariant maintained
        by_cases h_success : (db.insertHyp pos l false f).error? = none
        · right
          have h_inv :=
            insertHyp_float_fresh_preserves_unique db pos l f h_unique h_no_error h_size h_dup h_success
          simpa [h_ess_false] using h_inv
        · left
          simpa [h_ess_false] using h_success
    · -- Float with invalid size (shouldn't happen in practice)
      -- insertHyp doesn't check for duplicates if size < 2
      -- This case shouldn't occur with parser_validates_all_float_structures
      -- but we handle it defensively
      left
      have h_db_err : db.error = false := by
        simp [DB.error, h_no_error]
      have h_shape : f.isFloatShape = false := by
        -- If size < 2, float shape check fails
        by_cases h_size_eq : f.size = 2
        · have : False := h_size (by simp [h_size_eq])
          exact this.elim
        · simp [Formula.isFloatShape, h_size_eq]
      have h_checks_err : (db.insertHypChecks pos false f).error = true := by
        unfold DB.insertHypChecks
        by_cases h_head : f.hasConstHead
        · simp [h_head, h_shape, h_no_error, DB.mkError, DB.error]
        · simp [h_head, DB.mkError, DB.error]
      have h_err : (db.insertHyp pos l false f).error = true := by
        simp [DB.insertHyp, h_checks_err]
      have h_err' : (db.insertHyp pos l false f).error? ≠ none :=
        (_root_.Metamath.ParserOps.error_iff_error?_isSome (db.insertHyp pos l false f)).1 h_err
      simpa [h_ess_false] using h_err'

/-- **Theorem**: pushScope maintains float uniqueness.

pushScope saves the current frame size for later restoration.
It doesn't modify the frame itself, so uniqueness is preserved.
-/
theorem pushScope_maintains_uniqueness
  (db : DB)
  (h_unique : db_has_unique_floats db) :
  db_has_unique_floats db.pushScope := by
  -- pushScope: { db with scopes := db.scopes.push db.frame.size }
  -- Frame unchanged, objects unchanged
  unfold DB.pushScope
  exact h_unique

/-! ## Array Utility Lemmas -/

/-- Size of a shrunk array is the minimum of the target size and original size. -/
theorem Array.size_shrink {α : Type _} (arr : Array α) (n : Nat) :
  (arr.shrink n).size = min n arr.size := by
  simp [Array.shrink]
  omega

/-- Array.shrink preserves elements at valid indices. -/
theorem Array.getElem_shrink {α : Type _} (arr : Array α) (n : Nat) (i : Nat)
  (h1 : i < n) (h2 : i < arr.size) :
  (arr.shrink n)[i]'(by simp [Array.shrink]; omega) = arr[i] := by
  simp [Array.shrink]

/-- **Theorem**: popScope maintains float uniqueness.

popScope restores the frame to a previous size.
Since it's removing hypotheses (not adding), and the previous state
had unique floats, uniqueness is preserved.
-/
theorem popScope_maintains_uniqueness
  (db : DB) (pos : Pos)
  (h_unique : db_has_unique_floats db)
  (_h_no_error : db.error? = none) :
  let db' := db.popScope pos
  db'.error? ≠ none ∨ db_has_unique_floats db' := by
  -- popScope either:
  -- 1. Sets error if no scope to pop, OR
  -- 2. Shrinks frame to previous size
  -- In case 2, we're removing hypotheses, so uniqueness preserved
  dsimp
  rcases h_unique with ⟨h_curr_unique, h_curr_exist, h_curr_float_wf, h_frames⟩
  cases h_back : db.scopes.back? with
  | none =>
      left
      simp [DB.popScope, h_back, DB.mkError]
  | some sc =>
      right
      -- Pop succeeds: frame shrinks to first sc elements
      let db' : DB := { db with frame := db.frame.shrink sc, scopes := db.scopes.pop }
      have h_pop : db.popScope pos = db' := by
        simp [DB.popScope, h_back, db']
      have h_find_eq : ∀ lbl, db'.find? lbl = db.find? lbl := by
        intro lbl
        simp [db', DB.find?]
      -- Unfold definitions for the unique float property
      simp [h_pop, db_has_unique_floats]
      constructor
      · -- Current frame: fewer hyps but same uniqueness
        have h_curr := h_curr_unique
        unfold frame_has_unique_floats at h_curr ⊢
        intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
        -- Shrink preserves prefix indices
        have hi' := hi
        have hj' := hj
        simp [db', Frame.shrink] at hi' hj'
        have hi_n : i < sc.2 := Nat.lt_of_lt_of_le hi' (Nat.min_le_left _ _)
        have hi_orig : i < db.frame.hyps.size := Nat.lt_of_lt_of_le hi' (Nat.min_le_right _ _)
        have hj_n : j < sc.2 := Nat.lt_of_lt_of_le hj' (Nat.min_le_left _ _)
        have hj_orig : j < db.frame.hyps.size := Nat.lt_of_lt_of_le hj' (Nat.min_le_right _ _)
        have h_i_eq : db'.frame.hyps[i] = db.frame.hyps[i] := by
          simp [db', Frame.shrink]
        have h_j_eq : db'.frame.hyps[j] = db.frame.hyps[j] := by
          simp [db', Frame.shrink]
        -- Rewrite lookups through the shrunk frame and preserved objects
        have h_fi' : db.find? db.frame.hyps[i] = some (.hyp false fi lbli) := by
          have := h_fi
          simp [h_find_eq, h_i_eq] at this
          exact this
        have h_fj' : db.find? db.frame.hyps[j] = some (.hyp false fj lblj) := by
          have := h_fj
          simp [h_find_eq, h_j_eq] at this
          exact this
        exact h_curr i j hi_orig hj_orig h_ne fi fj lbli lblj h_fi' h_fj' h_szi h_szj
      constructor
      · -- Current frame: every label resolves to a hypothesis
        intro i hi
        have hi' := hi
        simp [db', Frame.shrink] at hi'
        have hi_n : i < sc.2 := Nat.lt_of_lt_of_le hi' (Nat.min_le_left _ _)
        have hi_orig : i < db.frame.hyps.size := Nat.lt_of_lt_of_le hi' (Nat.min_le_right _ _)
        have h_i_eq : db'.frame.hyps[i] = db.frame.hyps[i] := by
          simp [db', Frame.shrink]
        rcases h_curr_exist i hi_orig with ⟨ess, fml, lbl, hfind⟩
        have hfind' : db'.find? (db.frame.hyps[i]) = some (.hyp ess fml lbl) := by
          simpa [h_find_eq] using hfind
        exact ⟨ess, fml, lbl, by simpa [h_i_eq] using hfind'⟩
      constructor
      · -- Current frame: floats remain well-formed
        intro i hi fml lbl hfind
        have hi' := hi
        simp [db', Frame.shrink] at hi'
        have hi_n : i < sc.2 := Nat.lt_of_lt_of_le hi' (Nat.min_le_left _ _)
        have hi_orig : i < db.frame.hyps.size := Nat.lt_of_lt_of_le hi' (Nat.min_le_right _ _)
        have h_i_eq : db'.frame.hyps[i] = db.frame.hyps[i] := by
          simp [db', Frame.shrink]
        have hfind' : db.find? (db.frame.hyps[i]) = some (.hyp false fml lbl) := by
          simpa [h_find_eq, h_i_eq] using hfind
        exact h_curr_float_wf i hi_orig fml lbl hfind'
      · -- Assertions: objects unchanged, so lookups identical
        intro label fmla fr proof h_find
        have h_find' : db.find? label = some (.assert fmla fr proof) := by
          simpa [h_find_eq] using h_find
        exact h_frames label fmla fr proof h_find'

/-- **Theorem**: trimFrame maintains float uniqueness.

trimFrame removes hypotheses that aren't needed for the current formula.
Since it's removing (not adding) hypotheses, uniqueness is preserved.
-/
theorem trimFrame_maintains_uniqueness
  (db : DB) (fmla : Formula)
  (h_unique : frame_has_unique_floats db db.frame.hyps) :
  let (_ok, fr) := db.trimFrame fmla
  frame_has_unique_floats db fr.hyps := by
  -- trimFrameHyps is an injective subsequence of the original frame hyps,
  -- so uniqueness lifts from db.frame to the trimmed frame.
  classical
  cases h_trim : db.trimFrame fmla with
  | mk ok fr =>
      have h_subseq :=
        _root_.Metamath.ParserOps.trimFrame_produces_subsequence
          (db := db) (fmla := fmla) (ok := ok) (fr := fr) h_trim
      have h_unique' : UniqueFloatVars db db.frame := by
        simpa [frame_has_unique_floats, UniqueFloatVars] using h_unique
      have h_unique_fr :=
        _root_.Metamath.ParserOps.trimFrame_preserves_uniqueness h_subseq h_unique'
      simpa [frame_has_unique_floats, UniqueFloatVars, h_trim] using h_unique_fr

/-! ## Derived Invariant from WellFormedDB -/

/-- Unique floats in a frame follow from WellFormedFrame. -/
theorem frame_has_unique_floats_of_wf (db : DB) (fr : Frame)
  (h_wf : WF.WellFormedFrame db fr) :
  frame_has_unique_floats db fr.hyps := by
  simpa [frame_has_unique_floats, WF.UniqueFloatVars] using h_wf.2

/-- Hyp existence in a frame follows from WellFormedFrame. -/
theorem frame_hyps_exist_of_wf (db : DB) (fr : Frame)
  (h_wf : WF.WellFormedFrame db fr) :
  frame_hyps_exist db fr.hyps := by
  intro i hi
  have h_ok := h_wf.1 i hi
  unfold WF.HypOK at h_ok
  rcases h_ok with ⟨ess, f, lbl, hfind, _h_float, _h_formula⟩
  exact ⟨ess, f, lbl, hfind⟩

/-- Float well-formedness in a frame follows from WellFormedFrame. -/
theorem frame_float_wf_of_wf (db : DB) (fr : Frame)
  (h_wf : WF.WellFormedFrame db fr) :
  frame_float_wf db fr.hyps := by
  intro i hi f lbl hfind
  have h_ok := h_wf.1 i hi
  unfold WF.HypOK at h_ok
  rcases h_ok with ⟨ess, f', lbl', hfind', h_float, _h_formula⟩
  have h_obj : Object.hyp ess f' lbl' = Object.hyp false f lbl := by
    apply Option.some.inj
    exact hfind'.symm.trans hfind
  cases h_obj
  have h_float' : WF.WellFormedFloat f := h_float rfl
  rcases h_float' with ⟨h_size, c, v, h0, h1⟩
  have h_pos0 : 0 < f.size := by omega
  have h_pos1 : 1 < f.size := by omega
  have h0' : f[0] = Sym.const c := by
    simpa [getElem!_pos f 0 h_pos0] using h0
  have h1' : f[1] = Sym.var v := by
    simpa [getElem!_pos f 1 h_pos1] using h1
  unfold Formula.isFloatShape
  simp [h_size, h0', h1']

/-- The float-uniqueness invariant is implied by WellFormedDB. -/
theorem db_has_unique_floats_of_wf (db : DB)
  (h_wf : WF.WellFormedDB db) :
  db_has_unique_floats db := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact frame_has_unique_floats_of_wf db db.frame h_wf.1
  · exact frame_hyps_exist_of_wf db db.frame h_wf.1
  · exact frame_float_wf_of_wf db db.frame h_wf.1
  · intro label fmla fr proof h_find
    have h_fr : WF.WellFormedFrame db fr := by
      have h := h_wf.2 label (Object.assert fmla fr proof) h_find
      exact h.2
    exact ⟨frame_has_unique_floats_of_wf db fr h_fr,
      frame_hyps_exist_of_wf db fr h_fr,
      frame_float_wf_of_wf db fr h_fr⟩

/-- Parser success (from bytes) implies the float-uniqueness invariant. -/
theorem parser_success_implies_unique_floats
  (bytes : ByteArray) :
  (Verify.checkBytes bytes).error? = none →
  db_has_unique_floats (Verify.checkBytes bytes) := by
  intro h_ok
  have h_wf : WF.WellFormedDB (Verify.checkBytes bytes) := by
    have h_parse : ∃ b, Verify.checkBytes bytes = Verify.checkBytes b := by
      exact ⟨bytes, rfl⟩
    exact ParserInvariants.parser_success_wellformed (db := Verify.checkBytes bytes) h_parse h_ok
  exact db_has_unique_floats_of_wf (Verify.checkBytes bytes) h_wf

/-- Prove parser_validates_float_uniqueness via WellFormedDB. -/
theorem prove_parser_validates_float_uniqueness :
  ∀ (db : DB) (label : String) (fmla : Formula) (fr : Frame) (proof : String),
    WF.WellFormedDB db →
    db.find? label = some (.assert fmla fr proof) →
    ∀ (i j : Nat) (hi : i < fr.hyps.size) (hj : j < fr.hyps.size) (_ : i ≠ j),
      ∀ (fi fj : Formula) (vi vj : String) (lbli lblj : String),
        db.find? fr.hyps[i] = some (.hyp false fi lbli) →
        db.find? fr.hyps[j] = some (.hyp false fj lblj) →
        fi.size >= 2 → fj.size >= 2 →
        (match fi[1]! with | .var v => v | _ => "") = vi →
        (match fj[1]! with | .var v => v | _ => "") = vj →
        vi ≠ vj := by
  intro db label fmla fr proof h_wf h_find
  exact ParserInvariants.parser_validates_float_uniqueness db label fmla fr proof h_wf h_find

end Metamath.ParserProofs
