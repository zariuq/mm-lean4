import Metamath.SourceCompleteness.Bytes
import Metamath.AssertDvInvariant
import Metamath.PrefixTraceCompressed
import Metamath.PrefixProvenance

/-!
# Source invariants of the parser

`SourceInv s` says that every object name of `s.db` is a token of its kind (`KeysAreTokens`),
that every floating hypothesis of the active frame types an active variable declared no deeper
than the block holding the hypothesis (`FloatVarsActive`), that the interrupt flag is off, and
that the pending token-parser mode holds only label tokens and active variables
(`SourceTokpInv`).

Every `feedToken` step keeps `SourceInv` (`feedToken_maintains_sourceInv`), assuming only that
the token read as a label or a math symbol is a token of that kind.  The step needs two further
database facts: every declaration depth is still open and every scope snapshot fits the active
frame (`ScopesOk`), and every frame hypothesis is registered (`FrameHypsFound`).  Given those it
holds in every mode and on every path, erroneous ones included (`feedToken_sourceInv_of_facts`).

The proof follows the parser's structure.  Operations that only raise errors, add `$d` pairs or
change the token mode keep the registry, the frame hypotheses, the scope stack, the activity stack
and the interrupt flag (`Keeps`).  The remaining ones are `pushScope`, `popScope`, `insert` (for
`$c` and `$v`), `insertHyp`, `insertAxiom` and the `insert` of a finished `$p`, each handled once
at the database level.  A new `$f` types a variable that was active when its math string was read
(`SourceTokpInv`), and no operation between that read and the insertion changes activity.
`popScope` removes the hypotheses of the closing block together with the activity entries of its
depth, and `FloatVarsActive` says exactly that a surviving hypothesis keeps its variable.

`SourceLoopInv` adds the two database facts; it holds initially and every error-free step keeps
it in every mode (`feedToken_maintains_sourceLoopInv`), and so does `feed` over any byte array
whose non-whitespace runs are tokens (`feed_maintains_sourceLoopInv`, `feedAll_init_sourceInv`).
-/

set_option autoImplicit false

namespace Metamath.SourceCompleteness

open Metamath.Verify
open Metamath.WF (WellFormedDB)
open Metamath.ParserOps (ScopesOk)

/-- The token-state companion of the source invariants: a pending label (`.label`, the label of
a statement being read in `.math`, the label of a `$p` in `.proof`) is a label token, and every
variable in a math string being read is active.  Comment and include administration are looked
through. -/
def SourceTokpInv (db : DB) : TokenParser → Prop
  | .comment p => SourceTokpInv db p
  | .includePath resume _ => SourceTokpInv db resume
  | .includeClose resume _ _ => SourceTokpInv db resume
  | .label _ lab => IsLabelToken lab
  | .math arr p =>
      IsLabelToken p.label ∧ ∀ v, Verify.Sym.var v ∈ arr.toList → db.isActiveVar v = true
  | .proof pr => IsLabelToken pr.label
  | .start => True
  | .const _ => True
  | .var _ => True
  | .djvars _ => True

/-- The source invariants of a parser state. -/
def SourceInv (s : ParserState) : Prop :=
  KeysAreTokens s.db ∧ FloatVarsActive s.db ∧ s.db.interrupt = false ∧
    SourceTokpInv s.db s.tokp

/-- The token condition `KeysAreTokens` places on one registry entry. -/
def KeyOK (l : String) : Object → Prop
  | .const _ | .var _ => IsMathToken l
  | .hyp _ _ _ | .assert _ _ _ => IsLabelToken l

theorem keysAreTokens_iff (db : DB) :
    KeysAreTokens db ↔ ∀ l o, db.find? l = some o → KeyOK l o := by
  constructor
  · intro h l o h_find
    have := h l o h_find
    cases o <;> exact this
  · intro h l o h_find
    have := h l o h_find
    cases o <;> exact this

/-- `db'` agrees with `db` on every component the source invariants read: the registry, the
hypotheses of the active frame, the scope stack, the activity stack and the interrupt flag. -/
structure Keeps (db db' : DB) : Prop where
  objects : db'.objects = db.objects
  hyps : db'.frame.hyps = db.frame.hyps
  scopes : db'.scopes = db.scopes
  activeVars : db'.activeVars = db.activeVars
  interrupt : db'.interrupt = db.interrupt

theorem Keeps.refl (db : DB) : Keeps db db := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {a b c : DB} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.objects.trans h1.objects, h2.hyps.trans h1.hyps, h2.scopes.trans h1.scopes,
    h2.activeVars.trans h1.activeVars, h2.interrupt.trans h1.interrupt⟩

/-- `FloatVarsActive` as a statement about the four components it reads. -/
def FloatVarsActiveOn (objs : Std.HashMap String Object) (hyps : Array String)
    (scopes : Array (Nat × Nat)) (av : Array (String × Nat)) : Prop :=
  ∀ k (hk : k < hyps.size) f nm, objs[hyps[k]]? = some (.hyp false f nm) →
    ∃ d, (f[1]!.value, d) ∈ av.toList ∧
      ∀ j (hj : j < scopes.size), j < d → scopes[j].2 ≤ k

theorem floatVarsActive_iff (db : DB) :
    FloatVarsActive db ↔ FloatVarsActiveOn db.objects db.frame.hyps db.scopes db.activeVars :=
  Iff.rfl

theorem floatVarsActive_of_keeps {db db' : DB} (hk : Keeps db db') (h : FloatVarsActive db) :
    FloatVarsActive db' := by
  rw [floatVarsActive_iff, hk.objects, hk.hyps, hk.scopes, hk.activeVars]
  exact h

theorem keysAreTokens_of_objects_eq {db db' : DB} (h_eq : db'.objects = db.objects)
    (h : KeysAreTokens db) : KeysAreTokens db' := by
  intro l o h_find
  exact h l o (by show db.objects[l]? = some o; rw [← h_eq]; exact h_find)

theorem isActiveVar_of_keeps {db db' : DB} (hk : Keeps db db') (v : String) :
    db'.isActiveVar v = db.isActiveVar v := by
  simp only [DB.isActiveVar, DB.isVar, DB.find?, hk.objects, hk.activeVars]

theorem sourceTokpInv_of_keeps {db db' : DB} (hk : Keeps db db') :
    ∀ tp, SourceTokpInv db tp → SourceTokpInv db' tp := by
  intro tp
  induction tp with
  | comment p ih => exact ih
  | includePath resume _ ih => exact ih
  | includeClose resume _ _ ih => exact ih
  | math arr p =>
      intro h
      exact ⟨h.1, fun v hv => by rw [isActiveVar_of_keeps hk]; exact h.2 v hv⟩
  | label _ _ => exact id
  | proof _ => exact id
  | start => exact id
  | const _ => exact id
  | var _ => exact id
  | djvars _ => exact id

/-! ## Database operations -/

theorem keeps_mkErrorFromEvidence (db : DB) (pos : Pos) (ev : ErrorEvidence) :
    Keeps db (db.mkErrorFromEvidence pos ev) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem keeps_recordIncomplete (db : DB) (b : Bool) (l : String) :
    Keeps db (db.recordIncomplete b l) := by
  unfold DB.recordIncomplete
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Keeps.refl db

theorem keeps_insertHypChecks (db : DB) (pos : Pos) (ess : Bool) (f : Verify.Formula) :
    Keeps db (db.insertHypChecks pos ess f) := by
  unfold DB.insertHypChecks
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem insert_frame (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).frame = db.frame := by
  unfold DB.insert
  cases obj l <;> dsimp only <;> repeat' split
  all_goals rfl

theorem insert_interrupt (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).interrupt = db.interrupt := by
  unfold DB.insert
  cases obj l <;> dsimp only <;> repeat' split
  all_goals rfl

/-- `insert` of a non-variable either fails, keeping every component the invariants read, or
registers the object at a fresh name. -/
theorem insert_nonvar_cases (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_nv : ∀ v, obj l ≠ .var v) :
    (Keeps db (db.insert pos l obj) ∧ (db.insert pos l obj).error = true) ∨
      (db.find? l = none ∧
        db.insert pos l obj = { db with objects := db.objects.insert l (obj l) }) := by
  unfold DB.insert
  cases h_o : obj l with
  | var v => exact absurd h_o (h_nv v)
  | const c =>
      dsimp only
      repeat' split
      all_goals first
        | (left; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp_all [DB.error]⟩)
        | (right; exact ⟨by simp_all, rfl⟩)
        | (exfalso; simp_all [DB.error])
  | hyp ess f n =>
      dsimp only
      repeat' split
      all_goals first
        | (left; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp_all [DB.error]⟩)
        | (right; exact ⟨by simp_all, rfl⟩)
  | assert f fr n =>
      dsimp only
      repeat' split
      all_goals first
        | (left; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp_all [DB.error]⟩)
        | (right; exact ⟨by simp_all, rfl⟩)

/-! ### Keys -/

theorem keysAreTokens_insert {db : DB} (pos : Pos) (l : String) (obj : String → Object)
    (h : KeysAreTokens db) (h_obj : KeyOK l (obj l)) : KeysAreTokens (db.insert pos l obj) := by
  rcases AssertDv.insert_objects_cases db pos l obj with h_eq | h_eq
  · exact keysAreTokens_of_objects_eq h_eq h
  · rw [keysAreTokens_iff] at h ⊢
    intro n o h_find
    have h_find' : (db.objects.insert l (obj l))[n]? = some o := by
      rw [← h_eq]
      exact h_find
    rw [Std.HashMap.getElem?_insert] at h_find'
    split at h_find'
    · rename_i h_ln
      have h_ln' : l = n := by simpa using h_ln
      subst h_ln'
      injection h_find' with h_o
      subst h_o
      exact h_obj
    · exact h n o h_find'

theorem keysAreTokens_insertHyp {db : DB} (pos : Pos) (l : String) (ess : Bool)
    (f : Verify.Formula) (h : KeysAreTokens db) (h_l : IsLabelToken l) :
    KeysAreTokens (db.insertHyp pos l ess f) := by
  have h1 : KeysAreTokens (db.insertHypChecks pos ess f) :=
    keysAreTokens_of_objects_eq (keeps_insertHypChecks db pos ess f).objects h
  have h2 : KeysAreTokens ((db.insertHypChecks pos ess f).insert pos l (.hyp ess f)) :=
    keysAreTokens_insert pos l _ h1 h_l
  simp only [DB.insertHyp]
  split
  · exact h1
  · split
    · exact h2
    · exact keysAreTokens_of_objects_eq rfl h2

theorem keysAreTokens_insertAxiom {db : DB} (pos : Pos) (l : String) (fmla : Verify.Formula)
    (h : KeysAreTokens db) (h_l : IsLabelToken l) :
    KeysAreTokens (db.insertAxiom pos l fmla) := by
  simp only [DB.insertAxiom]
  repeat' split
  all_goals first
    | exact h
    | exact keysAreTokens_of_objects_eq rfl h
    | exact keysAreTokens_insert _ _ _ h h_l

/-! ### Floating hypotheses -/

/-- Opening a block adds a snapshot at the current frame size; every declaration depth is at most
the old stack size, so the new snapshot never constrains an existing hypothesis. -/
theorem floatVarsActive_pushScope {db : DB} (h_bnd : db.ActiveVarsBounded)
    (h : FloatVarsActive db) : FloatVarsActive db.pushScope := by
  intro k hk f nm h_find
  obtain ⟨d, h_mem, h_sc⟩ := h k hk f nm h_find
  refine ⟨d, h_mem, ?_⟩
  intro j hj h_jd
  simp only [DB.pushScope] at hj ⊢
  by_cases hj' : j < db.scopes.size
  · rw [Array.getElem_push_lt hj']
    exact h_sc j hj' h_jd
  · exfalso
    have h_d : d ≤ db.scopes.size := h_bnd _ h_mem
    simp only [Array.size_push] at hj
    omega

/-- Closing a block removes the hypotheses opened in it and the activity entries of its depth; a
surviving hypothesis lies before the block, so its variable's depth survives the filter. -/
theorem floatVarsActive_popScope {db : DB} (pos : Pos) (h : FloatVarsActive db) :
    FloatVarsActive (db.popScope pos) := by
  unfold DB.popScope
  split
  · rename_i sc h_back
    have h_size : 0 < db.scopes.size := by
      rcases h_sz : db.scopes.size with _ | n
      · simp [Array.back?, h_sz] at h_back
      · exact Nat.succ_pos n
    have h_last : db.scopes.size - 1 < db.scopes.size := by omega
    have h_sc : db.scopes[db.scopes.size - 1] = sc := by
      rw [Array.back?_eq_getElem?] at h_back
      rw [Array.getElem?_eq_getElem h_last] at h_back
      exact Option.some.inj h_back
    intro k hk f nm h_find
    have h_hyps : (db.frame.shrink sc).hyps = db.frame.hyps.shrink sc.2 := by
      rcases db.frame with ⟨dj, hyps⟩
      rfl
    have hk' : k < (db.frame.hyps.shrink sc.2).size := by
      simpa [h_hyps] using hk
    have hk_sc : k < sc.2 := by
      rw [Array.size_shrink] at hk'
      omega
    have hk_old : k < db.frame.hyps.size := by
      rw [Array.size_shrink] at hk'
      omega
    have h_get : (db.frame.shrink sc).hyps[k] = db.frame.hyps[k] := by
      simp only [h_hyps, Array.getElem_shrink]
    have h_find' : db.find? db.frame.hyps[k] = some (.hyp false f nm) := by
      rw [← h_get]
      exact h_find
    obtain ⟨d, h_mem, h_old⟩ := h k hk_old f nm h_find'
    have h_d : d ≤ db.scopes.size - 1 := by
      by_contra h_contra
      have := h_old (db.scopes.size - 1) h_last (by omega)
      rw [h_sc] at this
      omega
    refine ⟨d, ?_, ?_⟩
    · simp only [Array.toList_filter, List.mem_filter, decide_eq_true_eq]
      exact ⟨h_mem, h_d⟩
    · intro j hj h_jd
      have hj_old : j < db.scopes.size := by
        simp only [Array.size_pop] at hj
        omega
      simp only [Array.getElem_pop]
      exact h_old j hj_old h_jd
  · exact floatVarsActive_of_keeps (keeps_mkErrorFromEvidence _ _ _) h

theorem floatVarsActive_insert {db : DB} (pos : Pos) (l : String) (obj : String → Object)
    (h_obj : ∀ f nm, obj l ≠ .hyp false f nm) (h : FloatVarsActive db) :
    FloatVarsActive (db.insert pos l obj) := by
  have h_hyps : (db.insert pos l obj).frame.hyps = db.frame.hyps := by rw [insert_frame]
  have h_sc : (db.insert pos l obj).scopes = db.scopes :=
    Metamath.ParserOps.insert_scopes db pos l obj
  have h_av : ∀ e, e ∈ db.activeVars.toList →
      e ∈ (db.insert pos l obj).activeVars.toList := by
    intro e he
    rcases Metamath.ParserOps.insert_activeVars_cases db pos l obj with h_eq | h_eq
    · rw [h_eq]; exact he
    · rw [h_eq, Array.toList_push]; exact List.mem_append_left _ he
  rw [floatVarsActive_iff, h_hyps, h_sc]
  intro k hk f nm h_find
  have h_old : db.objects[db.frame.hyps[k]]? = some (.hyp false f nm) := by
    rcases AssertDv.insert_objects_cases db pos l obj with h_eq | h_eq
    · rw [h_eq] at h_find; exact h_find
    · rw [h_eq, Std.HashMap.getElem?_insert] at h_find
      split at h_find
      · injection h_find with h_o
        exact absurd h_o (h_obj f nm)
      · exact h_find
  obtain ⟨d, h_mem, h_d⟩ := h k hk f nm h_old
  exact ⟨d, h_av _ h_mem, h_d⟩

/-- Every hypothesis label of the active frame is registered. -/
def FrameHypsFound (db : DB) : Prop :=
  ∀ k (hk : k < db.frame.hyps.size), db.find? db.frame.hyps[k] ≠ none

/-- `FrameHypsFound` as a statement about the two components it reads. -/
def FrameHypsFoundOn (objs : Std.HashMap String Object) (hyps : Array String) : Prop :=
  ∀ k (hk : k < hyps.size), objs[hyps[k]]? ≠ none

theorem frameHypsFound_iff (db : DB) :
    FrameHypsFound db ↔ FrameHypsFoundOn db.objects db.frame.hyps := Iff.rfl

theorem frameHypsFound_of_mono {db db' : DB} (h_hyps : db'.frame.hyps = db.frame.hyps)
    (h_mono : ∀ n o, db.find? n = some o → db'.find? n = some o) (h : FrameHypsFound db) :
    FrameHypsFound db' := by
  have h' : FrameHypsFoundOn db.objects db'.frame.hyps := by rw [h_hyps]; exact h
  intro k hk h_none
  obtain ⟨o, h_o⟩ := Option.ne_none_iff_exists'.mp (h' k hk)
  have := h_mono _ o h_o
  rw [h_none] at this
  cases this

theorem frameHypsFound_of_keeps {db db' : DB} (hk : Keeps db db') (h : FrameHypsFound db) :
    FrameHypsFound db' := by
  rw [frameHypsFound_iff, hk.objects, hk.hyps]
  exact h

/-- Registering a hypothesis at a fresh label and pushing it keeps `FloatVarsActiveOn`, provided a
`$f` types a variable with an activity entry; every snapshot lies at or below the new index. -/
theorem floatVarsActiveOn_push {objs : Std.HashMap String Object} {hyps : Array String}
    {scopes : Array (Nat × Nat)} {av : Array (String × Nat)} {l : String} {ess : Bool}
    {f : Verify.Formula}
    (h : FloatVarsActiveOn objs hyps scopes av)
    (h_fresh : ∀ k (hk : k < hyps.size), hyps[k] ≠ l)
    (h_within : ∀ j (hj : j < scopes.size), scopes[j].2 ≤ hyps.size)
    (h_act : ess = false → ∃ d, (f[1]!.value, d) ∈ av.toList) :
    FloatVarsActiveOn (objs.insert l (.hyp ess f l)) (hyps.push l) scopes av := by
  intro k hk g nm h_find
  rw [Array.size_push] at hk
  by_cases hk' : k < hyps.size
  · have h_get : (hyps.push l)[k] = hyps[k] := Array.getElem_push_lt hk'
    rw [h_get, Std.HashMap.getElem?_insert] at h_find
    split at h_find
    · rename_i h_eq
      exact absurd (by simpa using h_eq : l = hyps[k]).symm (h_fresh k hk')
    · exact h k hk' g nm h_find
  · have hk_eq : k = hyps.size := by omega
    subst hk_eq
    have h_get : (hyps.push l)[hyps.size] = l := Array.getElem_push_eq
    rw [h_get, Std.HashMap.getElem?_insert_self] at h_find
    injection h_find with h_o
    injection h_o with h_ess h_f h_nm
    subst h_ess
    subst h_f
    obtain ⟨d, h_mem⟩ := h_act rfl
    exact ⟨d, h_mem, fun j hj _ => h_within j hj⟩

theorem frameHypsFoundOn_push {objs : Std.HashMap String Object} {hyps : Array String}
    {l : String} {o : Object} (h : FrameHypsFoundOn objs hyps) :
    FrameHypsFoundOn (objs.insert l o) (hyps.push l) := by
  intro k hk
  rw [Array.size_push] at hk
  by_cases hk' : k < hyps.size
  · have h_get : (hyps.push l)[k] = hyps[k] := Array.getElem_push_lt hk'
    rw [h_get, Std.HashMap.getElem?_insert]
    split
    · simp
    · exact h k hk'
  · have hk_eq : k = hyps.size := by omega
    subst hk_eq
    have h_get : (hyps.push l)[hyps.size] = l := Array.getElem_push_eq
    rw [h_get, Std.HashMap.getElem?_insert_self]
    simp

/-- `insertHyp` either keeps every component the invariants read, or registers the hypothesis at
a fresh label and pushes the label onto the active frame. -/
theorem insertHyp_cases (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Verify.Formula) :
    Keeps db (db.insertHyp pos l ess f) ∨
      (db.find? l = none ∧
        Keeps { db with objects := db.objects.insert l (.hyp ess f l),
                        frame := ⟨db.frame.dj, db.frame.hyps.push l⟩ }
          (db.insertHyp pos l ess f)) := by
  have hk1 := keeps_insertHypChecks db pos ess f
  simp only [DB.insertHyp]
  split
  · exact Or.inl hk1
  · rename_i h_err1
    rcases insert_nonvar_cases (db.insertHypChecks pos ess f) pos l (.hyp ess f)
        (fun v h => by cases h) with ⟨hk2, h_err2⟩ | ⟨h_fresh, h_eq⟩
    · split
      · exact Or.inl (hk1.trans hk2)
      · rename_i h_err2'
        exact absurd h_err2 h_err2'
    · rw [h_eq]
      split
      · rename_i h_err2
        exact absurd h_err2 h_err1
      · right
        refine ⟨?_, ?_⟩
        · show db.objects[l]? = none
          rw [← hk1.objects]
          exact h_fresh
        · refine ⟨?_, ?_, hk1.scopes, hk1.activeVars, hk1.interrupt⟩
          · show (db.insertHypChecks pos ess f).objects.insert l (.hyp ess f l) =
              db.objects.insert l (.hyp ess f l)
            rw [hk1.objects]
          · show (db.insertHypChecks pos ess f).frame.hyps.push l = db.frame.hyps.push l
            rw [hk1.hyps]

theorem floatVarsActive_insertHyp {db : DB} (pos : Pos) (l : String) (ess : Bool)
    (f : Verify.Formula) (h : FloatVarsActive db) (h_found : FrameHypsFound db)
    (h_within : ∀ j (hj : j < db.scopes.size), db.scopes[j].2 ≤ db.frame.hyps.size)
    (h_act : ess = false → ∃ d, (f[1]!.value, d) ∈ db.activeVars.toList) :
    FloatVarsActive (db.insertHyp pos l ess f) := by
  rcases insertHyp_cases db pos l ess f with hk | ⟨h_fresh, hk⟩
  · exact floatVarsActive_of_keeps hk h
  · apply floatVarsActive_of_keeps hk
    rw [floatVarsActive_iff]
    refine floatVarsActiveOn_push h ?_ h_within h_act
    intro k hk h_eq
    apply h_found k hk
    rw [h_eq]
    exact h_fresh

theorem frameHypsFound_insertHyp {db : DB} (pos : Pos) (l : String) (ess : Bool)
    (f : Verify.Formula) (h : FrameHypsFound db) :
    FrameHypsFound (db.insertHyp pos l ess f) := by
  rcases insertHyp_cases db pos l ess f with hk | ⟨_, hk⟩
  · exact frameHypsFound_of_keeps hk h
  · apply frameHypsFound_of_keeps hk
    rw [frameHypsFound_iff]
    exact frameHypsFoundOn_push h

theorem floatVarsActive_insertAxiom {db : DB} (pos : Pos) (l : String) (fmla : Verify.Formula)
    (h : FloatVarsActive db) : FloatVarsActive (db.insertAxiom pos l fmla) := by
  simp only [DB.insertAxiom]
  repeat' split
  all_goals first
    | exact h
    | exact floatVarsActive_of_keeps ⟨rfl, rfl, rfl, rfl, rfl⟩ h
    | exact floatVarsActive_insert _ _ _ (fun f nm h_eq => by cases h_eq) h

theorem frameHypsFound_insert {db : DB} (pos : Pos) (l : String) (obj : String → Object)
    (h : FrameHypsFound db) : FrameHypsFound (db.insert pos l obj) :=
  frameHypsFound_of_mono (by rw [insert_frame]) (Metamath.ParserOps.insert_find?_mono db pos l obj)
    h

theorem frameHypsFound_insertAxiom {db : DB} (pos : Pos) (l : String) (fmla : Verify.Formula)
    (h : FrameHypsFound db) : FrameHypsFound (db.insertAxiom pos l fmla) := by
  simp only [DB.insertAxiom]
  repeat' split
  all_goals first
    | exact h
    | exact frameHypsFound_of_keeps ⟨rfl, rfl, rfl, rfl, rfl⟩ h
    | exact frameHypsFound_insert _ _ _ h

theorem frameHypsFound_pushScope {db : DB} (h : FrameHypsFound db) :
    FrameHypsFound db.pushScope := h

theorem frameHypsFound_popScope {db : DB} (pos : Pos) (h : FrameHypsFound db) :
    FrameHypsFound (db.popScope pos) := by
  unfold DB.popScope
  split
  · rename_i sc _
    intro k hk
    have h_hyps : (db.frame.shrink sc).hyps = db.frame.hyps.shrink sc.2 := by
      rcases db.frame with ⟨dj, hyps⟩
      rfl
    have hk' : k < (db.frame.hyps.shrink sc.2).size := by simpa [h_hyps] using hk
    have hk_old : k < db.frame.hyps.size := by
      rw [Array.size_shrink] at hk'
      omega
    have h_get : (db.frame.shrink sc).hyps[k] = db.frame.hyps[k] := by
      simp only [h_hyps, Array.getElem_shrink]
    show db.find? (db.frame.shrink sc).hyps[k] ≠ none
    rw [h_get]
    exact h k hk_old
  · exact frameHypsFound_of_keeps (keeps_mkErrorFromEvidence _ _ _) h

/-! ### The interrupt flag -/

theorem insertHyp_interrupt (db : DB) (pos : Pos) (l : String) (ess : Bool)
    (f : Verify.Formula) : (db.insertHyp pos l ess f).interrupt = db.interrupt := by
  rcases insertHyp_cases db pos l ess f with hk | ⟨_, hk⟩
  · exact hk.interrupt
  · exact hk.interrupt

theorem insertAxiom_interrupt (db : DB) (pos : Pos) (l : String) (fmla : Verify.Formula) :
    (db.insertAxiom pos l fmla).interrupt = db.interrupt := by
  simp only [DB.insertAxiom]
  repeat' split
  all_goals first
    | rfl
    | exact insert_interrupt _ _ _ _

theorem popScope_interrupt (db : DB) (pos : Pos) : (db.popScope pos).interrupt = db.interrupt := by
  unfold DB.popScope
  split <;> rfl

/-! ## The database part -/

/-- The database components of `SourceInv`, together with `FrameHypsFound`. -/
structure SourceDBInv (db : DB) : Prop where
  keys : KeysAreTokens db
  floats : FloatVarsActive db
  interrupt : db.interrupt = false
  found : FrameHypsFound db

theorem SourceDBInv.of_keeps {db db' : DB} (h : SourceDBInv db) (hk : Keeps db db') :
    SourceDBInv db' :=
  ⟨keysAreTokens_of_objects_eq hk.objects h.keys, floatVarsActive_of_keeps hk h.floats,
    hk.interrupt.trans h.interrupt, frameHypsFound_of_keeps hk h.found⟩

/-- The two facts about the scope stack that a step reads: every declaration depth is still open,
and every scope snapshot fits in the active frame.  Both are part of `ScopesOk`. -/
structure ScopeFacts (db : DB) : Prop where
  bounded : db.ActiveVarsBounded
  within : ∀ j (hj : j < db.scopes.size), db.scopes[j].2 ≤ db.frame.hyps.size

theorem frame_size_snd (fr : Verify.Frame) : fr.size.2 = fr.hyps.size := by
  rcases fr with ⟨dj, hyps⟩
  rfl

theorem scopeFacts_of_scopesOk {db : DB} (h : ScopesOk db) : ScopeFacts db := by
  refine ⟨h.2.2.1, ?_⟩
  intro j hj
  have := (h.2.1 j hj).2
  rw [frame_size_snd] at this
  exact this

theorem sourceDBInv_pushScope {db : DB} (h : SourceDBInv db) (h_bnd : db.ActiveVarsBounded) :
    SourceDBInv db.pushScope :=
  ⟨keysAreTokens_of_objects_eq rfl h.keys, floatVarsActive_pushScope h_bnd h.floats,
    h.interrupt, frameHypsFound_pushScope h.found⟩

theorem sourceDBInv_popScope {db : DB} (pos : Pos) (h : SourceDBInv db) :
    SourceDBInv (db.popScope pos) :=
  ⟨keysAreTokens_of_objects_eq (Metamath.PrefixProvability.Checker.popScope_objects db pos)
      h.keys,
    floatVarsActive_popScope pos h.floats, (popScope_interrupt db pos).trans h.interrupt,
    frameHypsFound_popScope pos h.found⟩

theorem sourceDBInv_insert {db : DB} (pos : Pos) (l : String) (obj : String → Object)
    (h : SourceDBInv db) (h_key : KeyOK l (obj l)) (h_nf : ∀ f nm, obj l ≠ .hyp false f nm) :
    SourceDBInv (db.insert pos l obj) :=
  ⟨keysAreTokens_insert pos l obj h.keys h_key, floatVarsActive_insert pos l obj h_nf h.floats,
    (insert_interrupt db pos l obj).trans h.interrupt, frameHypsFound_insert pos l obj h.found⟩

theorem sourceDBInv_insertHyp {db : DB} (pos : Pos) (l : String) (ess : Bool) (f : Verify.Formula)
    (h : SourceDBInv db) (hS : ScopeFacts db) (h_l : IsLabelToken l)
    (h_act : ess = false → ∃ d, (f[1]!.value, d) ∈ db.activeVars.toList) :
    SourceDBInv (db.insertHyp pos l ess f) :=
  ⟨keysAreTokens_insertHyp pos l ess f h.keys h_l,
    floatVarsActive_insertHyp pos l ess f h.floats h.found hS.within h_act,
    (insertHyp_interrupt db pos l ess f).trans h.interrupt,
    frameHypsFound_insertHyp pos l ess f h.found⟩

theorem sourceDBInv_insertAxiom {db : DB} (pos : Pos) (l : String) (fmla : Verify.Formula)
    (h : SourceDBInv db) (h_l : IsLabelToken l) : SourceDBInv (db.insertAxiom pos l fmla) :=
  ⟨keysAreTokens_insertAxiom pos l fmla h.keys h_l,
    floatVarsActive_insertAxiom pos l fmla h.floats,
    (insertAxiom_interrupt db pos l fmla).trans h.interrupt,
    frameHypsFound_insertAxiom pos l fmla h.found⟩

/-- One step's obligation: the database part and the token-state companion of the output. -/
def StepOK (s : ParserState) : Prop :=
  SourceDBInv s.db ∧ SourceTokpInv s.db s.tokp

theorem stepOK_of_keeps {s s' : ParserState} (hD : SourceDBInv s.db) (hk : Keeps s.db s'.db)
    (hT : SourceTokpInv s.db s'.tokp) : StepOK s' :=
  ⟨hD.of_keeps hk, sourceTokpInv_of_keeps hk _ hT⟩

/-! ## Parser-level helpers -/

theorem keeps_withAt (l : String) (f : Unit → ParserState) :
    Keeps (f ()).db (ParserState.withAt l f).db := by
  unfold ParserState.withAt
  dsimp only
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Keeps.refl _

theorem keeps_label (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    Keeps s.db (s.label pos tk).db := by
  unfold ParserState.label
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem label_tokp (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    (s.label pos tk).tokp = s.tokp ∨
      ((toLabel tk).1 = true ∧ (s.label pos tk).tokp = .label pos (toLabel tk).2) := by
  unfold ParserState.label
  split
  rename_i ok tk' heq
  split
  · right
    rename_i h_ok
    rw [heq]
    exact ⟨h_ok, rfl⟩
  · left
    rfl

theorem djvars_loop_aux_step (arr : Array String) (s : ParserState) (pos : Pos) (tk : String)
    (i : Nat) :
    Keeps s.db (ParserState.djvars_loop_aux arr s pos tk i).db ∧
      ((ParserState.djvars_loop_aux arr s pos tk i).tokp = s.tokp ∨
        (ParserState.djvars_loop_aux arr s pos tk i).tokp = .djvars (arr.push tk)) := by
  refine Nat.rec
    (motive := fun m => ∀ i (s : ParserState), arr.size - i = m →
      Keeps s.db (ParserState.djvars_loop_aux arr s pos tk i).db ∧
        ((ParserState.djvars_loop_aux arr s pos tk i).tokp = s.tokp ∨
          (ParserState.djvars_loop_aux arr s pos tk i).tokp = .djvars (arr.push tk)))
    ?base ?step (arr.size - i) i s rfl
  · intro i s hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simp
  · intro m ih i s hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      · have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        simp [hz] at hs
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    unfold ParserState.djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    split
    · exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
    · obtain ⟨hk, htp⟩ := ih (i + 1) _ hs'
      exact ⟨⟨hk.objects, hk.hyps, hk.scopes, hk.activeVars, hk.interrupt⟩, htp⟩

theorem djvars_loop_step (arr : Array String) (s : ParserState) (pos : Pos) (tk : String) :
    Keeps s.db (ParserState.djvars_loop arr s pos tk).db ∧
      ((ParserState.djvars_loop arr s pos tk).tokp = s.tokp ∨
        (ParserState.djvars_loop arr s pos tk).tokp = .djvars (arr.push tk)) := by
  unfold ParserState.djvars_loop
  split
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
  · exact djvars_loop_aux_step arr s pos tk 0

theorem withMath_cases (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) :
    (Keeps s.db (s.withMath pos tk f).db ∧ (s.withMath pos tk f).tokp = s.tokp) ∨
      ((toMath tk).1 = true ∧ s.withMath pos tk f = f s (toMath tk).2) := by
  unfold ParserState.withMath
  split
  rename_i ok tk' heq
  split
  · exact Or.inl ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · rename_i h_ok
    right
    rw [heq]
    exact ⟨by simpa using h_ok, rfl⟩

theorem stepOK_withMath (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) (hD : SourceDBInv s.db)
    (hT : SourceTokpInv s.db s.tokp)
    (hf : (toMath tk).1 = true → StepOK (f s (toMath tk).2)) :
    StepOK (s.withMath pos tk f) := by
  rcases withMath_cases s pos tk f with ⟨hk, htp⟩ | ⟨h_ok, h_eq⟩
  · exact stepOK_of_keeps hD hk (by rw [htp]; exact hT)
  · rw [h_eq]
    exact hf h_ok

theorem stepOK_withAt (l : String) (f : Unit → ParserState) (h : StepOK (f ())) :
    StepOK (ParserState.withAt l f) := by
  have hk := keeps_withAt l f
  refine ⟨h.1.of_keeps hk, ?_⟩
  rw [ParserState.withAt_tokp]
  exact sourceTokpInv_of_keeps hk _ h.2

theorem sourceTokpInv_math_push {db : DB} {arr : Array Verify.Sym} {p : TokensParser}
    {sym : Verify.Sym} (h : SourceTokpInv db (.math arr p))
    (h_sym : ∀ v, sym = .var v → db.isActiveVar v = true) :
    SourceTokpInv db (.math (arr.push sym) p) := by
  refine ⟨h.1, fun v hv => ?_⟩
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | hv
  · exact h.2 v hv
  · exact h_sym v hv.symm

theorem activeVar_entry {db : DB} {v : String} (h : db.isActiveVar v = true) :
    ∃ d, (v, d) ∈ db.activeVars.toList := by
  unfold DB.isActiveVar at h
  rw [Bool.and_eq_true, Array.any_eq_true'] at h
  obtain ⟨_, e, h_mem, h_eq⟩ := h
  refine ⟨e.2, ?_⟩
  have h_e1 : e.1 = v := by simpa using h_eq
  rw [Array.mem_toList_iff, ← h_e1]
  exact h_mem

theorem floatShape_var_mem {arr : Array Verify.Sym} (h : Formula.isFloatShape arr = true) :
    ∃ v, arr[1]! = .var v ∧ Verify.Sym.var v ∈ arr.toList := by
  obtain ⟨h_size, c, v, _, h1⟩ := Metamath.WF.wellFormedFloat_of_isFloatShape h
  refine ⟨v, h1, ?_⟩
  have h_lt : 1 < arr.size := by omega
  have h_get : arr[1]! = arr[1] := Array.getBang_eq_get_nat arr 1 h_lt
  rw [Array.mem_toList_iff, ← h1, h_get]
  exact Array.getElem_mem h_lt

/-! ### Proof mode keeps the label -/

theorem goNormal_label (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState)
    (h_ok : ParserState.feedProof.goNormal s tk pr = .ok pr') : pr'.label = pr.label := by
  unfold ParserState.feedProof.goNormal at h_ok
  by_cases h_unknown : tk.eqArray "?".toAscii
  · by_cases h_reject : s.db.config.rejectUnknownSteps
    · simp [h_unknown, h_reject] at h_ok
    · simp [h_unknown, h_reject] at h_ok
      injection h_ok with hpr
      subst hpr
      simp [ProofState.push]
  · by_cases h_lbl_ok : (toLabel tk).fst
    · have h_step : s.db.stepNormal pr (toLabel tk).snd = .ok pr' := by
        simpa [h_unknown, h_lbl_ok] using h_ok
      exact Metamath.PrefixProvenance.stepNormal_preserves_label s.db pr pr' _ h_step
    · simp [h_unknown, h_lbl_ok] at h_ok

/-- A proof step never changes the label of the proof state. -/
theorem go_label (s : ParserState) (tk : ByteSlice) (pr pr' : ProofState)
    (h_ok : ParserState.feedProof.go s tk pr = .ok pr') : pr'.label = pr.label := by
  unfold ParserState.feedProof.go at h_ok
  cases h_ptp : pr.ptp with
  | start =>
      by_cases h_open : tk.eqArray "(".toAscii
      · cases h_pre : s.db.preloadMandatoryHyps pr with
        | error msg =>
            simp [h_ptp, h_open, h_pre] at h_ok
            have h_map_err :
                ((fun a =>
                    { pos := a.pos, label := a.label, fmla := a.fmla, frame := a.frame,
                      heap := a.heap, stack := a.stack, ptp := ProofTokenParser.preload,
                      incomplete := a.incomplete }) <$>
                  (Except.error msg : Except ProofCheckFail ProofState))
                  = (Except.error msg : Except ProofCheckFail ProofState) := by
              rfl
            simp [h_map_err] at h_ok
        | ok pr_mid =>
            simp [h_ptp, h_open, h_pre] at h_ok
            injection h_ok with hpr
            subst hpr
            exact Metamath.PrefixTraceCompressed.preloadMandatoryHyps_preserves_label s.db pr pr_mid
              h_pre
      · have h_norm :
            ParserState.feedProof.goNormal s tk { pr with ptp := .normal } = .ok pr' := by
          simpa [h_ptp, h_open] using h_ok
        exact goNormal_label s tk { pr with ptp := .normal } pr' h_norm
  | preload =>
      by_cases h_close : tk.eqArray ")".toAscii
      · simp [h_ptp, h_close] at h_ok
        injection h_ok with hpr
        subst hpr
        rfl
      · by_cases h_lbl_ok : (toLabel tk).fst
        · cases h_guard : s.db.explicitCompressedHeaderLabelCheck pr (toLabel tk).snd with
          | error err =>
              simp [h_ptp, h_close, h_lbl_ok, h_guard, bind, Except.bind] at h_ok
          | ok value =>
              cases value
              have h_pre : s.db.preload pr (toLabel tk).snd = .ok pr' := by
                simpa [h_ptp, h_close, h_lbl_ok, h_guard, bind, Except.bind, pure,
                  Except.pure] using h_ok
              exact Metamath.PrefixTraceCompressed.preload_preserves_label s.db pr pr' _ h_pre
        · simp [h_ptp, h_close, h_lbl_ok] at h_ok
  | normal =>
      have h_norm : ParserState.feedProof.goNormal s tk pr = .ok pr' := by
        simpa [h_ptp] using h_ok
      exact goNormal_label s tk pr pr' h_norm
  | compressed chr =>
      cases h_dec : ParserState.decodeCompressed tk chr s.db.config.compressedInvalidBytes
          s.db.config.compressedSavePlacement with
      | error msg =>
          simp [h_ptp, h_dec, Bind.bind, Except.bind] at h_ok
      | ok dec =>
          rcases dec with ⟨acts, chr'⟩
          cases h_apply : ParserState.applyCompressedActions s.db pr acts with
          | error msg =>
              simp [h_ptp, h_dec, h_apply, Bind.bind, Except.bind] at h_ok
          | ok pr_mid =>
              have h_eq :
                  { pos := pr_mid.pos, label := pr_mid.label, fmla := pr_mid.fmla,
                    frame := pr_mid.frame, heap := pr_mid.heap, stack := pr_mid.stack,
                    ptp := ProofTokenParser.compressed chr',
                    incomplete := pr_mid.incomplete } = pr' := by
                have h_ok' :
                    (Except.pure
                      ({ pos := pr_mid.pos, label := pr_mid.label, fmla := pr_mid.fmla,
                         frame := pr_mid.frame, heap := pr_mid.heap, stack := pr_mid.stack,
                         ptp := ProofTokenParser.compressed chr',
                         incomplete := pr_mid.incomplete } : ProofState)
                      : Except ProofCheckFail ProofState) = Except.ok pr' := by
                  simp only [h_ptp, h_dec, h_apply, Bind.bind, Except.bind, pure,
                    Except.pure] at h_ok ⊢
                  exact h_ok
                cases h_ok'
                rfl
              subst h_eq
              exact Metamath.PrefixTraceCompressed.applyCA_preserves_label s.db pr acts pr_mid
                h_apply

theorem feedProof_step (s : ParserState) (tk : ByteSlice) (pr : ProofState) :
    Keeps s.db (s.feedProof tk pr).db ∧
      ((s.feedProof tk pr).tokp = s.tokp ∨
        ∃ pr', pr'.label = pr.label ∧ (s.feedProof tk pr).tokp = .proof pr') := by
  unfold ParserState.feedProof
  refine ⟨Keeps.trans ?_ (keeps_withAt _ _), ?_⟩
  · split
    · exact Keeps.refl _
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [ParserState.withAt_tokp]
    split
    · rename_i pr' h_go
      exact Or.inr ⟨pr', go_label s tk pr pr' h_go, rfl⟩
    · exact Or.inl rfl

theorem finishProof_sourceDBInv (s : ParserState) (pr : ProofState) (hD : SourceDBInv s.db)
    (h_l : IsLabelToken pr.label) : SourceDBInv (s.finishProof pr).db := by
  cases pr with
  | mk pos l fmla fr heap stack ptp inc =>
    unfold ParserState.finishProof
    refine SourceDBInv.of_keeps ?_ (keeps_withAt _ _)
    simp only [Id.run]
    repeat' split
    all_goals first
      | exact hD
      | exact hD.of_keeps ⟨rfl, rfl, rfl, rfl, rfl⟩
      | exact (sourceDBInv_insert pos l (Object.assert fmla fr) hD h_l
          (fun f nm h => by cases h)).of_keeps (keeps_recordIncomplete _ _ _)

/-! ### Closing a statement -/

/-- The delimiter of a statement: `$f`, `$e` and `$a` insert at the statement's label, and `$p`
opens a proof carrying it. -/
theorem feedTokens_step (s : ParserState) (arr : Array Verify.Sym) (p : TokensParser)
    (hD : SourceDBInv s.db) (hS : ScopeFacts s.db) (h_tokp : s.tokp = .math arr p)
    (hT : SourceTokpInv s.db (.math arr p)) : StepOK (s.feedTokens arr p) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; exact hT
  obtain ⟨k, pos, l⟩ := p
  have h_l : IsLabelToken l := hT.1
  unfold ParserState.feedTokens
  apply stepOK_withAt
  cases k with
  | float =>
      simp only [Id.run]
      repeat' split
      all_goals first
        | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
        | skip
      rename_i h_shape
      have h_shape' : Formula.isFloatShape arr = true := by simpa using h_shape
      obtain ⟨v, h1, h_mem⟩ := floatShape_var_mem h_shape'
      refine ⟨sourceDBInv_insertHyp pos l false arr hD hS h_l (fun _ => ?_), trivial⟩
      rw [h1]
      exact activeVar_entry (hT.2 v h_mem)
  | ess =>
      simp only [Id.run]
      repeat' split
      all_goals first
        | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
        | exact ⟨sourceDBInv_insertHyp pos l true arr hD hS h_l (fun h => by cases h), trivial⟩
  | ax =>
      simp only [Id.run]
      repeat' split
      all_goals first
        | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
        | exact ⟨sourceDBInv_insertAxiom pos l arr hD h_l, trivial⟩
  | thm =>
      simp only [Id.run]
      repeat' split
      all_goals first
        | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
        | exact ⟨hD, h_l⟩

/-! ### Mode by mode -/

theorem feedToken_comment_step (s : ParserState) (i : Nat) (tk : ByteSlice) (inner : TokenParser)
    (h_tokp : s.tokp = .comment inner) (hD : SourceDBInv s.db) (hT : SourceTokpInv s.db inner) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; exact hT
  unfold ParserState.feedToken
  simp only [h_tokp]
  repeat' split
  all_goals first
    | exact ⟨hD, hT⟩
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0

theorem feedToken_open_eq (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_nc : ∀ q, s.tokp ≠ .comment q) (h_open : tk.eqArray "$(".toAscii = true) :
    s.feedToken i tk = { s with tokp := .comment s.tokp } := by
  unfold ParserState.feedToken
  cases h_tokp : s.tokp <;>
    first
      | exact absurd h_tokp (h_nc _)
      | simp [h_open]

theorem feedToken_incl_cases (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_nc : ∀ q, s.tokp ≠ .comment q) (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = true) :
    (∃ ev, s.feedToken i tk = s.mkErrorFromEvidence (s.mkPos i) ev) ∨
      s.feedToken i tk = { s with tokp := .includePath s.tokp (s.mkPos i) } := by
  unfold ParserState.feedToken
  cases h_tokp : s.tokp <;>
    first
      | exact absurd h_tokp (h_nc _)
      | (simp only [h_open, h_incl, Bool.false_eq_true, if_false, if_true]
         split
         · exact Or.inl ⟨_, rfl⟩
         · exact Or.inr rfl)

theorem feedToken_start_step (s : ParserState) (i : Nat) (tk : ByteSlice)
    (h_tokp : s.tokp = .start) (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) (hD : SourceDBInv s.db) (hS : ScopeFacts s.db)
    (hL : (toLabel tk).1 = true → IsLabelToken (toLabel tk).2) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; trivial
  have hTs : ∀ db, SourceTokpInv db s.tokp := fun db => by rw [h_tokp]; trivial
  have h_label : ∀ q, StepOK (s.label q tk) := by
    intro q
    refine stepOK_of_keeps hD (keeps_label s q tk) ?_
    rcases label_tokp s q tk with h | ⟨h_ok, h⟩
    · rw [h]; exact hT0
    · rw [h]; exact hL h_ok
  unfold ParserState.feedToken
  simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | exact h_label _
    | exact ⟨hD, trivial⟩
    | exact ⟨sourceDBInv_pushScope hD hS.bounded, hTs _⟩
    | exact ⟨sourceDBInv_popScope _ hD, hTs _⟩

theorem sym_sourceDBInv (s : ParserState) (q : Pos) (tk : ByteSlice) (f : String → Object)
    (hD : SourceDBInv s.db) (hM : (toMath tk).1 = true → IsMathToken (toMath tk).2)
    (h_key : ∀ l, IsMathToken l → KeyOK l (f l)) (h_nf : ∀ l g nm, f l ≠ .hyp false g nm) :
    SourceDBInv (s.sym q tk f).db := by
  unfold ParserState.sym
  split
  · exact hD
  · rcases withMath_cases s q tk (fun s tk => s.withDB fun db => db.insert q tk f)
      with ⟨hk, _⟩ | ⟨h_ok, h_eq⟩
    · exact hD.of_keeps hk
    · rw [h_eq]
      exact sourceDBInv_insert q _ f hD (h_key _ (hM h_ok)) (h_nf _)

theorem feedToken_const_step (s : ParserState) (i : Nat) (tk : ByteSlice) (seen : Bool)
    (h_tokp : s.tokp = .const seen) (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) (hD : SourceDBInv s.db)
    (hM : (toMath tk).1 = true → IsMathToken (toMath tk).2) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; trivial
  have h_sym : ∀ q, SourceDBInv (s.sym q tk .const).db := fun q =>
    sym_sourceDBInv s q tk .const hD hM (fun _ h => h) (fun _ _ _ h => by cases h)
  unfold ParserState.feedToken
  simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | exact ⟨hD, trivial⟩
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
    | exact ⟨h_sym _, trivial⟩

theorem feedToken_var_step (s : ParserState) (i : Nat) (tk : ByteSlice) (seen : Bool)
    (h_tokp : s.tokp = .var seen) (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) (hD : SourceDBInv s.db)
    (hM : (toMath tk).1 = true → IsMathToken (toMath tk).2) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; trivial
  have h_sym : ∀ q, SourceDBInv (s.sym q tk .var).db := fun q =>
    sym_sourceDBInv s q tk .var hD hM (fun _ h => h) (fun _ _ _ h => by cases h)
  unfold ParserState.feedToken
  simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | exact ⟨hD, trivial⟩
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
    | exact ⟨h_sym _, trivial⟩

theorem feedToken_djvars_step (s : ParserState) (i : Nat) (tk : ByteSlice) (arr : Array String)
    (h_tokp : s.tokp = .djvars arr) (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) (hD : SourceDBInv s.db) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; trivial
  unfold ParserState.feedToken
  simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
  split
  · split
    · exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
    · exact ⟨hD, trivial⟩
  · apply stepOK_withMath _ _ _ _ hD hT0
    intro _
    obtain ⟨hk, htp⟩ := djvars_loop_step arr s (s.mkPos i) (toMath tk).2
    refine stepOK_of_keeps hD hk ?_
    rcases htp with h | h
    · rw [h]; exact hT0
    · rw [h]; trivial

theorem feedToken_label_step (s : ParserState) (i : Nat) (tk : ByteSlice) (q : Pos)
    (lab : String) (h_tokp : s.tokp = .label q lab) (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) (hD : SourceDBInv s.db) (hT : IsLabelToken lab) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; exact hT
  unfold ParserState.feedToken
  simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
    | exact ⟨hD, hT, fun v hv => by simp at hv⟩

theorem feedToken_math_step (s : ParserState) (i : Nat) (tk : ByteSlice)
    (arr : Array Verify.Sym) (p : TokensParser) (h_tokp : s.tokp = .math arr p)
    (h_open : tk.eqArray "$(".toAscii = false) (h_incl : tk.eqArray "$[".toAscii = false)
    (hD : SourceDBInv s.db) (hS : ScopeFacts s.db) (hT : SourceTokpInv s.db (.math arr p)) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; exact hT
  by_cases h_delim : tk.eqArray p.k.delim = true
  · have h_eq : s.feedToken i tk = s.feedTokens arr p := by
      simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_delim]
    rw [h_eq]
    exact feedTokens_step s arr p hD hS h_tokp hT
  · have h_delim' : tk.eqArray p.k.delim = false := by simpa using h_delim
    unfold ParserState.feedToken
    simp only [h_tokp, h_open, h_incl, h_delim', Bool.false_eq_true, if_false]
    apply stepOK_withMath _ _ _ _ hD hT0
    intro _
    simp only [Id.run]
    split
    · exact ⟨hD, sourceTokpInv_math_push hT (fun v h => by cases h)⟩
    · split
      · rename_i h_act
        refine ⟨hD, sourceTokpInv_math_push hT (fun v h => ?_)⟩
        injection h with h
        subst h
        exact h_act
      · exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
    · split
      · exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
      · exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0

theorem feedToken_includePath_step (s : ParserState) (i : Nat) (tk : ByteSlice)
    (resume : TokenParser) (q : Pos) (h_tokp : s.tokp = .includePath resume q)
    (h_open : tk.eqArray "$(".toAscii = false) (h_incl : tk.eqArray "$[".toAscii = false)
    (hD : SourceDBInv s.db) (hT : SourceTokpInv s.db resume) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; exact hT
  unfold ParserState.feedToken
  simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT

theorem feedToken_includeClose_step (s : ParserState) (i : Nat) (tk : ByteSlice)
    (resume : TokenParser) (q : Pos) (path : String)
    (h_tokp : s.tokp = .includeClose resume q path)
    (h_open : tk.eqArray "$(".toAscii = false) (h_incl : tk.eqArray "$[".toAscii = false)
    (hD : SourceDBInv s.db) (hT : SourceTokpInv s.db resume) :
    StepOK (s.feedToken i tk) := by
  have hT0 : SourceTokpInv s.db s.tokp := by rw [h_tokp]; exact hT
  unfold ParserState.feedToken
  simp only [h_tokp, h_open, h_incl, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT0
    | exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT

theorem feedToken_proof_step (s : ParserState) (i : Nat) (tk : ByteSlice) (pr : ProofState)
    (h_tokp : s.tokp = .proof pr) (h_open : tk.eqArray "$(".toAscii = false)
    (h_incl : tk.eqArray "$[".toAscii = false) (hD : SourceDBInv s.db)
    (hT : IsLabelToken pr.label) : StepOK (s.feedToken i tk) := by
  by_cases h_dot : tk.eqArray "$.".toAscii = true
  · have h_eq : s.feedToken i tk = ({ s with tokp := default } : ParserState).finishProof pr := by
      simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_dot]
    rw [h_eq]
    refine ⟨finishProof_sourceDBInv _ pr hD hT, ?_⟩
    rw [Metamath.ParserOps.finishProof_tokp_start]
    trivial
  · have h_dot' : tk.eqArray "$.".toAscii = false := by simpa using h_dot
    have h_eq : s.feedToken i tk = ({ s with tokp := default } : ParserState).feedProof tk pr := by
      simp [ParserState.feedToken, h_tokp, h_open, h_incl, h_dot']
    rw [h_eq]
    obtain ⟨hk, htp⟩ := feedProof_step ({ s with tokp := default } : ParserState) tk pr
    refine stepOK_of_keeps hD hk ?_
    rcases htp with h | ⟨pr', h_lab, h⟩
    · rw [h]; trivial
    · rw [h]
      show IsLabelToken pr'.label
      rw [h_lab]
      exact hT

/-- **One step.**  Every `feedToken` transition keeps the database part and the token-state
companion, given the scope facts; no success or mode hypothesis is needed. -/
theorem feedToken_stepOK (s : ParserState) (i : Nat) (tk : ByteSlice)
    (hD : SourceDBInv s.db) (hT : SourceTokpInv s.db s.tokp) (hS : ScopeFacts s.db)
    (hL : (toLabel tk).1 = true → IsLabelToken (toLabel tk).2)
    (hM : (toMath tk).1 = true → IsMathToken (toMath tk).2) :
    StepOK (s.feedToken i tk) := by
  by_cases h_c : ∃ q, s.tokp = .comment q
  · obtain ⟨inner, h_tokp⟩ := h_c
    rw [h_tokp] at hT
    exact feedToken_comment_step s i tk inner h_tokp hD hT
  have h_nc : ∀ q, s.tokp ≠ .comment q := fun q h => h_c ⟨q, h⟩
  by_cases h_open : tk.eqArray "$(".toAscii = true
  · rw [feedToken_open_eq s i tk h_nc h_open]
    exact ⟨hD, hT⟩
  have h_open' : tk.eqArray "$(".toAscii = false := by simpa using h_open
  by_cases h_incl : tk.eqArray "$[".toAscii = true
  · rcases feedToken_incl_cases s i tk h_nc h_open' h_incl with ⟨ev, h_eq⟩ | h_eq
    · rw [h_eq]
      exact stepOK_of_keeps hD ⟨rfl, rfl, rfl, rfl, rfl⟩ hT
    · rw [h_eq]
      exact ⟨hD, hT⟩
  have h_incl' : tk.eqArray "$[".toAscii = false := by simpa using h_incl
  cases h_tokp : s.tokp with
  | comment inner => exact absurd h_tokp (h_nc inner)
  | start => exact feedToken_start_step s i tk h_tokp h_open' h_incl' hD hS hL
  | const seen => exact feedToken_const_step s i tk seen h_tokp h_open' h_incl' hD hM
  | var seen => exact feedToken_var_step s i tk seen h_tokp h_open' h_incl' hD hM
  | djvars arr => exact feedToken_djvars_step s i tk arr h_tokp h_open' h_incl' hD
  | label q lab =>
      rw [h_tokp] at hT
      exact feedToken_label_step s i tk q lab h_tokp h_open' h_incl' hD hT
  | math arr p =>
      rw [h_tokp] at hT
      exact feedToken_math_step s i tk arr p h_tokp h_open' h_incl' hD hS hT
  | includePath resume q =>
      rw [h_tokp] at hT
      exact feedToken_includePath_step s i tk resume q h_tokp h_open' h_incl' hD hT
  | includeClose resume q path =>
      rw [h_tokp] at hT
      exact feedToken_includeClose_step s i tk resume q path h_tokp h_open' h_incl' hD hT
  | proof pr =>
      rw [h_tokp] at hT
      exact feedToken_proof_step s i tk pr h_tokp h_open' h_incl' hD hT

/-! ## The source invariants -/

theorem frameHypsFound_of_wellFormedDB {db : DB} (h : WellFormedDB db) : FrameHypsFound db := by
  intro k hk h_none
  obtain ⟨ess, f, lbl, h_find, _⟩ := h.1.1 k hk
  rw [h_none] at h_find
  cases h_find

/-- **One step, from the facts it uses.**  No success, error-freeness or mode hypothesis. -/
theorem feedToken_sourceInv_of_facts (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (h_inv : SourceInv s) (h_found : FrameHypsFound s.db) (h_sc : ScopesOk s.db)
    (hL : (toLabel tk).1 = true → IsLabelToken (toLabel tk).2)
    (hM : (toMath tk).1 = true → IsMathToken (toMath tk).2) :
    SourceInv (s.feedToken pos tk) := by
  have h := feedToken_stepOK s pos tk ⟨h_inv.1, h_inv.2.1, h_inv.2.2.1, h_found⟩ h_inv.2.2.2
    (scopeFacts_of_scopesOk h_sc) hL hM
  exact ⟨h.1.keys, h.1.floats, h.1.interrupt, h.2⟩

/-- **One step under the parser invariant.** A state satisfying the parser invariant supplies
the two database facts of `feedToken_sourceInv_of_facts`. -/
theorem feedToken_maintains_sourceInv (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (h_inv : SourceInv s) (h_pinv : ParserOps.ParserStateInv s)
    (hL : (toLabel tk).1 = true → IsLabelToken (toLabel tk).2)
    (hM : (toMath tk).1 = true → IsMathToken (toMath tk).2) :
    SourceInv (s.feedToken pos tk) :=
  feedToken_sourceInv_of_facts s pos tk h_inv (frameHypsFound_of_wellFormedDB h_pinv.1)
    h_pinv.2.2.1 hL hM

theorem initState_sourceInv (config : ModeConfig) :
    SourceInv
      ({ (default : ParserState) with db := { (default : DB) with config := config } }) := by
  have h_none : ∀ n, ({ (default : DB) with config := config } : DB).find? n = none :=
    fun n => Metamath.PrefixProvability.Checker.default_db_find?_none n
  refine ⟨?_, ?_, rfl, trivial⟩
  · intro l o h_find
    rw [h_none] at h_find
    cases h_find
  · intro k hk
    simp at hk

/-! ## A loop invariant

`SourceInv` with the two database facts a step reads beyond it.  Every error-free step keeps
it in every mode, so it can be threaded through any token loop. -/

/-- `SourceInv` together with the database facts a step reads beyond it. -/
def SourceLoopInv (s : ParserState) : Prop :=
  SourceInv s ∧ ScopesOk s.db ∧ FrameHypsFound s.db

theorem sourceLoopInv_of_parserStateInv {s : ParserState} (h_inv : SourceInv s)
    (h_pinv : ParserOps.ParserStateInv s) : SourceLoopInv s :=
  ⟨h_inv, h_pinv.2.2.1, frameHypsFound_of_wellFormedDB h_pinv.1⟩

theorem feedToken_maintains_sourceLoopInv (s : ParserState) (pos : Nat) (tk : ByteSlice)
    (h : SourceLoopInv s) (h_no_err : s.db.error? = none)
    (hL : (toLabel tk).1 = true → IsLabelToken (toLabel tk).2)
    (hM : (toMath tk).1 = true → IsMathToken (toMath tk).2)
    (h_success : (s.feedToken pos tk).db.error? = none) :
    SourceLoopInv (s.feedToken pos tk) := by
  have hstep := feedToken_stepOK s pos tk ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2.2⟩ h.1.2.2.2
    (scopeFacts_of_scopesOk h.2.1) hL hM
  exact ⟨⟨hstep.1.keys, hstep.1.floats, hstep.1.interrupt, hstep.2⟩,
    Metamath.ParserOps.feedToken_maintains_scopesOk s pos tk h.2.1 h_no_err h_success,
    hstep.1.found⟩

theorem initState_sourceLoopInv (config : ModeConfig) :
    SourceLoopInv
      ({ (default : ParserState) with db := { (default : DB) with config := config } }) :=
  sourceLoopInv_of_parserStateInv (initState_sourceInv config)
    (Metamath.ParserOps.initState_inv config)

theorem sourceLoopInv_updateLine (s : ParserState) (i : Nat) (c : UInt8) (h : SourceLoopInv s) :
    SourceLoopInv (s.updateLine i c) := by
  unfold ParserState.updateLine
  split
  · exact h
  · exact h

/-! ## States between tokens -/

/-! ## The byte loop -/

/-- The facts about one token that a step reads. -/
def TokenFacts (tk : ByteSlice) : Prop :=
  ((toLabel tk).1 = true → IsLabelToken (toLabel tk).2) ∧
    ((toMath tk).1 = true → IsMathToken (toMath tk).2)

/-- Every nonempty run of non-whitespace bytes of `arr` has the token facts. -/
def RunsAreTokens (arr : ByteArray) : Prop :=
  ∀ off j, off < j → j ≤ arr.size →
    (∀ m (hm : m < arr.size), off ≤ m → m < j → isWhitespace arr[m] = false) →
    TokenFacts (ByteSlice.mk arr off (j - off))

/-- The lexer state of `feed` at byte `i` when no token is carried over from an earlier chunk:
between tokens, or inside a run of non-whitespace bytes that started at `off`. -/
def LexState (arr : ByteArray) (i : Nat) : ParserState.FeedState → Prop
  | .ws => True
  | .token (.this off) =>
      off < i ∧ ∀ m (hm : m < arr.size), off ≤ m → m < i → isWhitespace arr[m] = false
  | .token (.old _ _ _) => False

/-- Successful `feed` from a lexer state with no carried-over token keeps the loop invariant. -/
theorem feed_maintains_sourceLoopInv (base : Nat) (arr : ByteArray) (h_runs : RunsAreTokens arr)
    (i : Nat) (rs : ParserState.FeedState) (s : ParserState)
    (h_lex : LexState arr i rs) (h : SourceLoopInv s) (h_no_err : s.db.error? = none)
    (h_success : (s.feed base arr i rs).db.error? = none) :
    SourceLoopInv (s.feed base arr i rs) := by
  refine Nat.rec
    (motive := fun m => ∀ i rs (s : ParserState), arr.size - i = m → LexState arr i rs →
      SourceLoopInv s → s.db.error? = none → (s.feed base arr i rs).db.error? = none →
      SourceLoopInv (s.feed base arr i rs))
    ?base ?step (arr.size - i) i rs s rfl h_lex h h_no_err h_success
  · intro i rs s hs _ h _ _
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simp [hs] at hpos
    unfold ParserState.feed
    simp only [hi, ↓reduceDIte]
    exact h
  · intro m ih i rs s hs h_lex h h_no_err h_success
    have hi : i < arr.size := by omega
    have hs' : arr.size - (i + 1) = m := by omega
    by_cases h_ws : s.db.config.isWhitespace arr[i] = true
    · cases rs with
      | ws =>
          have h_success_rec :
              ((s.updateLine (base + i) arr[i]).feed base arr (i + 1) .ws).db.error? = none := by
            unfold ParserState.feed at h_success
            simpa [hi, h_ws] using h_success
          have h_rec := ih (i + 1) .ws (s.updateLine (base + i) arr[i]) hs' trivial
            (sourceLoopInv_updateLine s _ _ h) (by simpa using h_no_err) h_success_rec
          unfold ParserState.feed
          simpa [hi, h_ws] using h_rec
      | token ot =>
          cases ot with
          | this off =>
              have h_facts := h_runs off i h_lex.1 (Nat.le_of_lt hi) h_lex.2
              let s0 := s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
              let s1 : ParserState := s0.updateLine (base + i) arr[i]
              cases h_err : s1.db.error? with
              | some intr =>
                  have h_err0 : s0.db.error? = some intr := by
                    simpa [s1] using h_err
                  have h_bad : (s.feed base arr i (.token (.this off))).db.error? ≠ none := by
                    unfold ParserState.feed
                    simp [hi, h_ws, s0, h_err0]
                  exact (h_bad h_success).elim
              | none =>
                  have h_tok_ok : s0.db.error? = none := by
                    simpa [s1] using h_err
                  have h0 : SourceLoopInv s0 :=
                    feedToken_maintains_sourceLoopInv s (base + off)
                      (ByteSlice.mk arr off (i - off)) h h_no_err h_facts.1 h_facts.2 h_tok_ok
                  have h_success_rec : (s1.feed base arr (i + 1) .ws).db.error? = none := by
                    unfold ParserState.feed at h_success
                    simp [hi, h_ws, s0, h_tok_ok] at h_success
                    exact h_success
                  have h_rec := ih (i + 1) .ws s1 hs' trivial (sourceLoopInv_updateLine s0 _ _ h0)
                    h_err h_success_rec
                  unfold ParserState.feed
                  simpa [hi, h_ws, s0, s1, h_tok_ok] using h_rec
          | old base' off arr' => exact h_lex.elim
    · have h_wsm : s.db.config.isWhitespace arr[i] = false := by simpa using h_ws
      have h_ws' : isWhitespace arr[i] = false := s.db.config.isWhitespace_eq_false h_wsm
      cases rs with
      | ws =>
          have h_success_rec : (s.feed base arr (i + 1) (.token (.this i))).db.error? = none := by
            unfold ParserState.feed at h_success
            simpa [hi, h_wsm] using h_success
          have h_lex' : LexState arr (i + 1) (.token (.this i)) := by
            refine ⟨Nat.lt_succ_self i, fun k hk h1 h2 => ?_⟩
            have hki : k = i := by omega
            subst hki
            exact h_ws'
          have h_rec := ih (i + 1) (.token (.this i)) s hs' h_lex' h h_no_err h_success_rec
          unfold ParserState.feed
          simpa [hi, h_wsm] using h_rec
      | token ot =>
          have h_success_rec : (s.feed base arr (i + 1) (.token ot)).db.error? = none := by
            unfold ParserState.feed at h_success
            simpa [hi, h_wsm] using h_success
          have h_lex' : LexState arr (i + 1) (.token ot) := by
            cases ot with
            | this off =>
                refine ⟨Nat.lt_succ_of_lt h_lex.1, fun k hk h1 h2 => ?_⟩
                by_cases hki : k < i
                · exact h_lex.2 k hk h1 hki
                · have hki' : k = i := by omega
                  subst hki'
                  exact h_ws'
            | old base' off arr' => exact h_lex.elim
          have h_rec := ih (i + 1) (.token ot) s hs' h_lex' h h_no_err h_success_rec
          unfold ParserState.feed
          simpa [hi, h_wsm] using h_rec

/-- Successful `feedAll` from a state that carries no partial token keeps the loop invariant. -/
theorem feedAll_maintains_sourceLoopInv (s : ParserState) (base : Nat) (arr : ByteArray)
    (h_runs : RunsAreTokens arr) (h_charp : s.charp = .ws)
    (h : SourceLoopInv s) (h_no_err : s.db.error? = none)
    (h_success : (s.feedAll base arr).db.error? = none) :
    SourceLoopInv (s.feedAll base arr) := by
  simp only [ParserState.feedAll, h_charp] at h_success ⊢
  exact feed_maintains_sourceLoopInv base arr h_runs 0 .ws s trivial h h_no_err h_success

/-- Every nonempty run of non-whitespace bytes is a lexical token, so it has the token facts. -/
theorem runsAreTokens (arr : ByteArray) : RunsAreTokens arr := by
  intro off j h_lt h_le h_ws
  have hlex : LexToken (ByteSlice.mk arr off (j - off)) := by
    rw [LexToken, ByteSlice.bytes_mk]
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg List.length h
      simp [ByteArray.length_toList] at this
      omega
    · intro b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      simp only [List.getElem_take, List.getElem_drop]
      simp only [List.length_take, List.length_drop, ByteArray.length_toList] at hi
      have hm : off + i < arr.size := by omega
      have hget : ∀ k (hk : k < arr.toList.length), arr.toList[k] =
          arr[k]'(by simpa [ByteArray.length_toList] using hk) := by
        intro k hk
        simp [ByteArray.toList_eq_data_toList, ByteArray.getElem_eq_getElem_data]
      rw [hget]
      exact h_ws (off + i) hm (by omega) (by omega)
  exact ⟨toLabel_isLabelToken hlex, toMath_isMathToken hlex⟩

/-- Every error-free state that `feedAll` reaches from the initial state, in any mode, satisfies
the source invariants. -/
theorem feedAll_init_sourceInv (config : ModeConfig) (arr : ByteArray)
    (h_success : (({ (default : ParserState) with
      db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr).db.error?
        = none) :
    SourceInv (({ (default : ParserState) with
      db := { (default : DB) with config := config } } : ParserState).feedAll 0 arr) :=
  (feedAll_maintains_sourceLoopInv _ 0 arr (runsAreTokens arr) rfl (initState_sourceLoopInv config)
    rfl h_success).1

/-! ## Examples

`FloatVarsActive` accepts a `$f` whose variable is declared outside every open block, and
rejects a `$f` that precedes a block but types a variable declared inside it (closing that block
would deactivate the variable and keep the hypothesis).  `SourceTokpInv` accepts a pending label
token, and rejects a pending label that is not a token and a math string holding an inactive
variable. -/

namespace Examples

/-- `wx $f wff x $.` -/
def objWx : Object := .hyp false #[.const "wff", .var "x"] "wx"

def objectsWx : Std.HashMap String Object := (∅ : Std.HashMap String Object).insert "wx" objWx

/-- `$v x $. wx $f wff x $.` at the outermost level. -/
def dbGood : DB :=
  { (default : DB) with
    frame := ⟨#[], #["wx"]⟩
    objects := objectsWx
    activeVars := #[("x", 0)] }

/-- `wx` sits before a block opened at hypothesis count 1, while `x` is tagged with the depth of
that block. -/
def dbBad : DB :=
  { (default : DB) with
    frame := ⟨#[], #["wx"]⟩
    scopes := #[(0, 1)]
    objects := objectsWx
    activeVars := #[("x", 1)] }

theorem objectsWx_wx : objectsWx["wx"]? = some objWx := Std.HashMap.getElem?_insert_self

theorem dbGood_floatVarsActive : FloatVarsActive dbGood := by
  intro k hk f nm h_find
  have hk0 : k = 0 := by
    have : k < 1 := hk
    omega
  subst hk0
  have h_obj : some objWx = some (Object.hyp false f nm) := by
    rw [← objectsWx_wx]
    exact h_find
  injection h_obj with h_o
  injection h_o with _ h_f _
  subst h_f
  refine ⟨0, ?_, fun j hj _ => absurd hj (Nat.not_lt_zero j)⟩
  show ("x", 0) ∈ [("x", 0)]
  exact List.mem_singleton.mpr rfl

theorem dbBad_not_floatVarsActive : ¬ FloatVarsActive dbBad := by
  intro h
  obtain ⟨d, h_mem, h_sc⟩ := h 0 (Nat.zero_lt_one) #[.const "wff", .var "x"] "wx" objectsWx_wx
  have h_d : ("x", d) = ("x", 1) := List.mem_singleton.mp h_mem
  injection h_d with _ h_d1
  subst h_d1
  have := h_sc 0 Nat.zero_lt_one Nat.zero_lt_one
  exact absurd this (by decide)

theorem label_sourceTokpInv (db : DB) : SourceTokpInv db (.label ⟨0, 0⟩ "ax-1") := by
  show IsLabelToken "ax-1"
  decide

theorem label_not_sourceTokpInv (db : DB) : ¬ SourceTokpInv db (.label ⟨0, 0⟩ "a b") := by
  show ¬ IsLabelToken "a b"
  decide

theorem math_inactive_not_sourceTokpInv :
    ¬ SourceTokpInv (default : DB)
      (.math #[.const "|-", .var "x"] ⟨.ax, ⟨0, 0⟩, "ax-1"⟩) := by
  intro h
  have h_act := h.2 "x" (by simp)
  have h_var : (default : DB).isVar "x" = true := DB.isActiveVar_isVar h_act
  simp [DB.isVar, Metamath.PrefixProvability.Checker.default_db_find?_none] at h_var

end Examples

end Metamath.SourceCompleteness
