import Metamath.ParserInvariantPreservation
import Metamath.StoredStatementSoundness

/-!
# Declaring dummy variables, and accepting a proof

`Verify.DB.declareDummies` applies the parser's own actions for `$v d $.`, `lbl $f tc d $.` and
`$d d w $.` to a database state between statements: each dummy variable is declared, typed by a
floating hypothesis, and made disjoint from every float variable of the active frame and from
every earlier dummy. The `$d` pairs are stored as the parser stores them (`djvars_loop_aux`).

At an error-free, well-formed, well-scoped state with fresh declarations (`DummyDeclsFresh`), the
declarations succeed (`declareDummies_error`), the registry gains exactly the dummy variables and
their floating hypotheses (`declareDummies_find?`), the active frame gains the floating hypotheses
and the `$d` pairs (`declareDummies_frame`, `declareDummies_toFrame`), the stored assertions are
unchanged (`declareDummies_toDatabaseTotal`), and the parser invariant is preserved
(`declareDummies_stateInv`).

`ProofAccepted` is the parser's path for a `$p` statement with a normal-mode proof, from the state
between statements to the stored assertion: the claim's head check, frame trimming at `$=`, the
proof steps, and `finishProof` at `$.`.
-/

set_option autoImplicit false

namespace Metamath.CheckerCompleteness

open Metamath.Verify

/-- A dummy variable to declare: its typecode, its name, and the label of its `$f` hypothesis. -/
structure DummyDecl where
  tc : String
  var : String
  lbl : String

/-- A `$d` pair as the parser stores it (`djvars_loop_aux`): the smaller name first. -/
def canonDJ (d w : String) : Verify.DJ := if d < w then (d, w) else (w, d)

/-- The `$d` pairs between each of `ds` and every variable before it: those of `seen`, then the
earlier members of `ds`. -/
def dummyDJs : List String → List String → List Verify.DJ
  | _, [] => []
  | seen, d :: ds => seen.map (canonDJ d) ++ dummyDJs (seen ++ [d]) ds

/-- Declare one dummy variable: `$v d $.` and `lbl $f tc d $.`. -/
def _root_.Metamath.Verify.DB.declareDummy (db : DB) (pos : Pos) (d : DummyDecl) : DB :=
  (db.insert pos d.var .var).insertHyp pos d.lbl false #[.const d.tc, .var d.var]

/-- Declare the dummy variables `ds` in the current scope, then make each disjoint from every float
variable of the active frame and from every earlier dummy. -/
def _root_.Metamath.Verify.DB.declareDummies (db : DB) (pos : Pos) (ds : List DummyDecl) : DB :=
  (ds.foldl (fun db d => db.declareDummy pos d) db).withDJ fun dj =>
    dj ++ (dummyDJs (db.frameFloatVars db.frame) (ds.map (·.var))).toArray

/-- Dummy variables that can be declared at `db` before proving `label`: fresh names, distinct
from each other and from `label`, typed by declared constants. -/
structure DummyDeclsFresh (db : DB) (label : String) (ds : List DummyDecl) : Prop where
  var_fresh : ∀ d ∈ ds, db.find? d.var = none
  lbl_fresh : ∀ d ∈ ds, db.find? d.lbl = none
  nodup : (ds.map (·.var) ++ ds.map (·.lbl) ++ [label]).Nodup
  tc_const : ∀ d ∈ ds, db.isConst d.tc = true

/-- The parser accepts the normal-mode proof `proof` of the `$p` statement `label` with claim `f`
at the state `s` between statements: the claim has a constant head, the frame trims at `$=`, the
proof steps run, and `finishProof` stores the assertion at `$.`. -/
def ProofAccepted (s : ParserState) (pos : Pos) (label : String) (f : Verify.Formula)
    (proof : Array String) : Prop :=
  f.hasConstHead = true ∧ s.db.interrupt = false ∧ ∃ frImpl pr,
    s.db.trimFrame' f = .ok frImpl ∧
    proof.foldlM (fun pr l => s.db.stepNormal pr l)
      { s.db.mkProofState pos label f frImpl with ptp := .normal } = .ok pr ∧
    (s.finishProof pr).db.error? = none

/-- After declaring finitely many fresh dummy variables, the parser accepts a normal-mode proof of
the `$p` statement `label` with claim `f`. -/
def AcceptedWithDummies (s : ParserState) (pos : Pos) (label : String) (f : Verify.Formula) : Prop :=
  ∃ ds, DummyDeclsFresh s.db label ds ∧ ∃ proof,
    ProofAccepted (s.withDB (·.declareDummies pos ds)) pos label f proof

open Metamath.WF (WellFormedDB WellScopedDB WellScopedDBWithScopes)
open Metamath.ParserOps (ParserStateInv ScopesOk TokpInv)

/-! ## One dummy -/

/-- Registering a fresh variable does not change which variables have a floating hypothesis in the
active frame. -/
theorem floatVarOccursInFrame_insert_var (db : DB) (x v : String)
    (av : Array (String × Nat)) (h_x : db.find? x = none) :
    ({ db with objects := db.objects.insert x (.var x), activeVars := av } :
        DB).floatVarOccursInFrame v =
      db.floatVarOccursInFrame v := by
  unfold DB.floatVarOccursInFrame
  apply congrArg (List.any db.frame.hyps.toList)
  funext lbl
  by_cases h : x = lbl
  · subst h
    simp [DB.find?]
    simp [DB.find?] at h_x
    simp [h_x]
  · simp [DB.find?, h]

/-- `$v x $.` for a fresh `x`, on an error-free database. -/
theorem insert_var_fresh_eq (db : DB) (pos : Pos) (x : String)
    (h_err : db.error? = none) (h_x : db.find? x = none) :
    db.insert pos x .var =
      { db with objects := db.objects.insert x (.var x),
                activeVars := db.activeVars.push (x, db.scopes.size) } := by
  have h_err' : db.error = false := by simp [DB.error, h_err]
  simp only [DB.insert, h_err', h_x]
  rfl

/-- Registering a hypothesis under a fresh label, on an error-free database. -/
theorem insert_hyp_fresh_eq (db : DB) (pos : Pos) (l : String) (ess : Bool)
    (f : Verify.Formula) (h_err : db.error? = none) (h_l : db.find? l = none) :
    db.insert pos l (.hyp ess f) =
      { db with objects := db.objects.insert l (.hyp ess f l) } := by
  have h_err' : db.error = false := by simp [DB.error, h_err]
  simp [DB.insert, h_err', h_l]

/-- The checks for `$f tc v $.` pass when `v` has no floating hypothesis in the active frame. -/
theorem insertHypChecks_float_eq (db : DB) (pos : Pos) (tc v : String)
    (h_err : db.error? = none)
    (h_occ : db.floatVarOccursInFrame v = false) :
    db.insertHypChecks pos false #[Verify.Sym.const tc, Verify.Sym.var v] = db := by
  have h_err' : db.error = false := by simp [DB.error, h_err]
  simp [DB.insertHypChecks, Formula.hasConstHead, Formula.isFloatShape, h_err', h_occ, Sym.value]

/-- Declaring one fresh dummy variable, in closed form. -/
theorem declareDummy_eq (db : DB) (pos : Pos) (d : DummyDecl)
    (h_err : db.error? = none) (h_var : db.find? d.var = none) (h_lbl : db.find? d.lbl = none)
    (h_ne : d.var ≠ d.lbl) (h_occ : db.floatVarOccursInFrame d.var = false) :
    db.declareDummy pos d =
      { db with
        objects := (db.objects.insert d.var (.var d.var)).insert d.lbl
          (.hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl)
        activeVars := db.activeVars.push (d.var, db.scopes.size)
        frame := ⟨db.frame.dj, db.frame.hyps.push d.lbl⟩ } := by
  unfold DB.declareDummy
  have h_ins_eq := insert_var_fresh_eq db pos d.var h_err h_var
  generalize db.insert pos d.var .var = db1 at h_ins_eq ⊢
  have h_occ1 : db1.floatVarOccursInFrame d.var = false := by
    rw [h_ins_eq, floatVarOccursInFrame_insert_var db d.var d.var _ h_var]
    exact h_occ
  have h_err1 : db1.error? = none := by
    rw [h_ins_eq]; exact h_err
  have h_lbl1 : db1.find? d.lbl = none := by
    rw [h_ins_eq]
    simp [DB.find?, h_ne]
    simpa [DB.find?] using h_lbl
  simp only [DB.insertHyp]
  rw [insertHypChecks_float_eq db1 pos d.tc d.var h_err1 h_occ1,
    insert_hyp_fresh_eq db1 pos d.lbl false _ h_err1 h_lbl1]
  subst h_ins_eq
  simp [DB.error, h_err, DB.withHyps, DB.withFrame]

/-- Lookups after declaring one fresh dummy. -/
theorem declareDummy_find? (db : DB) (pos : Pos) (d : DummyDecl)
    (h_err : db.error? = none) (h_var : db.find? d.var = none) (h_lbl : db.find? d.lbl = none)
    (h_ne : d.var ≠ d.lbl) (h_occ : db.floatVarOccursInFrame d.var = false) (l : String) :
    (db.declareDummy pos d).find? l =
      if d.lbl = l then some (.hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl)
      else if d.var = l then some (.var d.var) else db.find? l := by
  rw [declareDummy_eq db pos d h_err h_var h_lbl h_ne h_occ]
  simp only [DB.find?, Std.HashMap.getElem?_insert, beq_iff_eq]

/-- Declaring a dummy does not give any other variable a floating hypothesis. -/
theorem declareDummy_floatVarOccursInFrame (db : DB) (pos : Pos) (d : DummyDecl)
    (h_err : db.error? = none) (h_var : db.find? d.var = none) (h_lbl : db.find? d.lbl = none)
    (h_ne : d.var ≠ d.lbl) (h_occ : db.floatVarOccursInFrame d.var = false) (v : String)
    (h_v : d.var ≠ v) (h_occ_v : db.floatVarOccursInFrame v = false) :
    (db.declareDummy pos d).floatVarOccursInFrame v = false := by
  have h_find := declareDummy_find? db pos d h_err h_var h_lbl h_ne h_occ
  have h_frame : (db.declareDummy pos d).frame = ⟨db.frame.dj, db.frame.hyps.push d.lbl⟩ := by
    rw [declareDummy_eq db pos d h_err h_var h_lbl h_ne h_occ]
  unfold DB.floatVarOccursInFrame at h_occ_v ⊢
  rw [List.any_eq_false] at h_occ_v ⊢
  rw [h_frame]
  intro lbl h_mem h_true
  rw [h_find lbl] at h_true
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h_mem
  by_cases h1 : d.lbl = lbl
  · simp [h1, h_v] at h_true
  · by_cases h2 : d.var = lbl
    · simp [h1, h2] at h_true
    · rcases h_mem with h_old | h_new
      · simp only [h1, h2, if_false] at h_true
        exact h_occ_v lbl h_old h_true
      · exact h1 h_new.symm

/-! ## The fold over the dummies -/

/-- Distinct names of `d :: ds`: those of `d` differ from each other and from those of `ds`. -/
theorem nodup_dummy_cons {d : DummyDecl} {ds : List DummyDecl}
    (h : ((d :: ds).map (·.var) ++ (d :: ds).map (·.lbl)).Nodup) :
    d.var ≠ d.lbl ∧
    (∀ e ∈ ds, e.var ≠ d.var ∧ e.var ≠ d.lbl ∧ e.lbl ≠ d.var ∧ e.lbl ≠ d.lbl) ∧
    (ds.map (·.var) ++ ds.map (·.lbl)).Nodup := by
  simp only [List.map_cons, List.cons_append, List.nodup_cons, List.nodup_append,
    List.mem_append, List.mem_cons, List.mem_map, not_or, not_exists, not_and] at h
  obtain ⟨⟨h1, h2, h3⟩, h4, ⟨h5, h6⟩, h7⟩ := h
  refine ⟨h2, fun e he =>
    ⟨h1 e he, h7 e.var ⟨e, he, rfl⟩ d.lbl (Or.inl rfl), h3 e he, h5 e he⟩, ?_⟩
  rw [List.nodup_append]
  refine ⟨h4, h6, fun a ha b hb => h7 a ?_ b (Or.inr ?_)⟩
  · simpa using ha
  · simpa using hb

/-- The effect of declaring the dummies `ds` one by one on `db`, relative to `db`. -/
structure DeclaredDummies (db : DB) (ds : List DummyDecl) (db' : DB) : Prop where
  error : db'.error? = db.error?
  find_of_not_mem :
    ∀ l, l ∉ ds.map (·.var) → l ∉ ds.map (·.lbl) → db'.find? l = db.find? l
  find_var : ∀ d ∈ ds, db'.find? d.var = some (.var d.var)
  find_lbl : ∀ d ∈ ds,
    db'.find? d.lbl = some (.hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl)
  frame : db'.frame = ⟨db.frame.dj, db.frame.hyps ++ (ds.map (·.lbl)).toArray⟩
  scopes : db'.scopes = db.scopes
  config : db'.config = db.config
  interrupt : db'.interrupt = db.interrupt
  activeVars : db'.activeVars = db.activeVars ++ (ds.map fun d => (d.var, db.scopes.size)).toArray

/-- Declaring fresh, distinct dummies one by one, when none of their variables has a floating
hypothesis in the active frame. -/
theorem foldl_declareDummy_spec (pos : Pos) :
    ∀ (ds : List DummyDecl) (db : DB),
      db.error? = none →
      (∀ d ∈ ds, db.find? d.var = none) →
      (∀ d ∈ ds, db.find? d.lbl = none) →
      (ds.map (·.var) ++ ds.map (·.lbl)).Nodup →
      (∀ d ∈ ds, db.floatVarOccursInFrame d.var = false) →
      DeclaredDummies db ds (ds.foldl (fun db d => db.declareDummy pos d) db)
  | [], db, _, _, _, _, _ => by
      refine ⟨rfl, fun _ _ _ => rfl, by simp, by simp, ?_, rfl, rfl, rfl, ?_⟩
      · simp
      · simp
  | d :: ds, db, h_err, h_var, h_lbl, h_nd, h_occ => by
      obtain ⟨h_ne, h_rest, h_nd'⟩ := nodup_dummy_cons h_nd
      have h_var_d := h_var d (List.mem_cons_self ..)
      have h_lbl_d := h_lbl d (List.mem_cons_self ..)
      have h_occ_d := h_occ d (List.mem_cons_self ..)
      have h_find := declareDummy_find? db pos d h_err h_var_d h_lbl_d h_ne h_occ_d
      have h_eq := declareDummy_eq db pos d h_err h_var_d h_lbl_d h_ne h_occ_d
      have h_err1 : (db.declareDummy pos d).error? = none := by rw [h_eq]; exact h_err
      have h_var1 : ∀ e ∈ ds, (db.declareDummy pos d).find? e.var = none := by
        intro e he
        obtain ⟨h1, h2, _, _⟩ := h_rest e he
        rw [h_find, if_neg (Ne.symm h2), if_neg (Ne.symm h1)]
        exact h_var e (List.mem_cons_of_mem _ he)
      have h_lbl1 : ∀ e ∈ ds, (db.declareDummy pos d).find? e.lbl = none := by
        intro e he
        obtain ⟨_, _, h3, h4⟩ := h_rest e he
        rw [h_find, if_neg (Ne.symm h4), if_neg (Ne.symm h3)]
        exact h_lbl e (List.mem_cons_of_mem _ he)
      have h_occ1 : ∀ e ∈ ds, (db.declareDummy pos d).floatVarOccursInFrame e.var = false := by
        intro e he
        exact declareDummy_floatVarOccursInFrame db pos d h_err h_var_d h_lbl_d h_ne h_occ_d e.var
          (Ne.symm (h_rest e he).1) (h_occ e (List.mem_cons_of_mem _ he))
      have ih := foldl_declareDummy_spec pos ds (db.declareDummy pos d) h_err1 h_var1 h_lbl1 h_nd'
        h_occ1
      have h_d_var_ds : d.var ∉ ds.map (·.var) := by
        simp only [List.mem_map, not_exists, not_and]
        intro e he h; exact (h_rest e he).1 h
      have h_d_var_ds' : d.var ∉ ds.map (·.lbl) := by
        simp only [List.mem_map, not_exists, not_and]
        intro e he h; exact (h_rest e he).2.2.1 h
      have h_d_lbl_ds : d.lbl ∉ ds.map (·.var) := by
        simp only [List.mem_map, not_exists, not_and]
        intro e he h; exact (h_rest e he).2.1 h
      have h_d_lbl_ds' : d.lbl ∉ ds.map (·.lbl) := by
        simp only [List.mem_map, not_exists, not_and]
        intro e he h; exact (h_rest e he).2.2.2 h
      simp only [List.foldl_cons]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ih.error, h_err1, h_err]
      · intro l hl1 hl2
        simp only [List.map_cons, List.mem_cons, not_or] at hl1 hl2
        rw [ih.find_of_not_mem l hl1.2 hl2.2, h_find, if_neg (Ne.symm hl2.1),
          if_neg (Ne.symm hl1.1)]
      · intro e he
        rcases List.mem_cons.mp he with h_e | h_e
        · subst h_e
          rw [ih.find_of_not_mem _ h_d_var_ds h_d_var_ds', h_find, if_neg (Ne.symm h_ne),
            if_pos rfl]
        · exact ih.find_var e h_e
      · intro e he
        rcases List.mem_cons.mp he with h_e | h_e
        · subst h_e
          rw [ih.find_of_not_mem _ h_d_lbl_ds h_d_lbl_ds', h_find, if_pos rfl]
        · exact ih.find_lbl e h_e
      · rw [ih.frame, h_eq]
        simp
      · rw [ih.scopes, h_eq]
      · rw [ih.config, h_eq]
      · rw [ih.interrupt, h_eq]
      · rw [ih.activeVars, h_eq]
        simp

/-! ## Declaring the dummies -/

/-- A name not registered in a well-formed, well-scoped database has no floating hypothesis in the
active frame. -/
theorem floatVarOccursInFrame_of_find?_none (db : DB) (h_wf : WellFormedDB db)
    (h_sc : WellScopedDB db) (v : String) (h_v : db.find? v = none) :
    db.floatVarOccursInFrame v = false := by
  cases h : db.floatVarOccursInFrame v with
  | false => rfl
  | true =>
      have h_mem := Metamath.ParserOps.floatVarOccursInFrame_true_implies db v h_wf h
      have h_isVar := Metamath.WF.frameFloatVars_mem_isVar db db.frame h_sc v h_mem
      simp [DB.isVar, h_v] at h_isVar

/-- The dummy variables and labels are pairwise distinct. -/
theorem DummyDeclsFresh.nodup_names {db : DB} {label : String} {ds : List DummyDecl}
    (h : DummyDeclsFresh db label ds) : (ds.map (·.var) ++ ds.map (·.lbl)).Nodup :=
  List.Nodup.sublist (List.sublist_append_left _ _) h.nodup

/-- The declaration fold at a well-formed, well-scoped, error-free state. -/
theorem declaredDummies_foldl (db : DB) (pos : Pos) (label : String) (ds : List DummyDecl)
    (h_err : db.error? = none) (h_wf : WellFormedDB db) (h_sc : WellScopedDB db)
    (h_fresh : DummyDeclsFresh db label ds) :
    DeclaredDummies db ds (ds.foldl (fun db d => db.declareDummy pos d) db) :=
  foldl_declareDummy_spec pos ds db h_err h_fresh.var_fresh h_fresh.lbl_fresh h_fresh.nodup_names
    (fun d hd => floatVarOccursInFrame_of_find?_none db h_wf h_sc d.var (h_fresh.var_fresh d hd))

/-- The declarations succeed. -/
theorem declareDummies_error (db : DB) (pos : Pos) (label : String) (ds : List DummyDecl)
    (h_err : db.error? = none) (h_wf : WellFormedDB db) (h_sc : WellScopedDB db)
    (h_fresh : DummyDeclsFresh db label ds) :
    (db.declareDummies pos ds).error? = none :=
  (declaredDummies_foldl db pos label ds h_err h_wf h_sc h_fresh).error.trans h_err

/-- Names other than the dummy variables and labels keep their objects. -/
theorem declareDummies_find?_of_not_mem (db : DB) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_err : db.error? = none) (h_wf : WellFormedDB db)
    (h_sc : WellScopedDB db) (h_fresh : DummyDeclsFresh db label ds) (l : String)
    (h_var : l ∉ ds.map (·.var)) (h_lbl : l ∉ ds.map (·.lbl)) :
    (db.declareDummies pos ds).find? l = db.find? l :=
  (declaredDummies_foldl db pos label ds h_err h_wf h_sc h_fresh).find_of_not_mem l h_var h_lbl

/-- Each dummy name is a variable. -/
theorem declareDummies_find?_var (db : DB) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_err : db.error? = none) (h_wf : WellFormedDB db)
    (h_sc : WellScopedDB db) (h_fresh : DummyDeclsFresh db label ds) (d : DummyDecl)
    (hd : d ∈ ds) :
    (db.declareDummies pos ds).find? d.var = some (.var d.var) :=
  (declaredDummies_foldl db pos label ds h_err h_wf h_sc h_fresh).find_var d hd

/-- Each dummy label is the floating hypothesis `$f tc v`. -/
theorem declareDummies_find?_lbl (db : DB) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_err : db.error? = none) (h_wf : WellFormedDB db)
    (h_sc : WellScopedDB db) (h_fresh : DummyDeclsFresh db label ds) (d : DummyDecl)
    (hd : d ∈ ds) :
    (db.declareDummies pos ds).find? d.lbl =
      some (.hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl) :=
  (declaredDummies_foldl db pos label ds h_err h_wf h_sc h_fresh).find_lbl d hd

/-- The registry only grows. -/
theorem declareDummies_find?_mono (db : DB) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_err : db.error? = none) (h_wf : WellFormedDB db)
    (h_sc : WellScopedDB db) (h_fresh : DummyDeclsFresh db label ds) :
    ∀ l o, db.find? l = some o → (db.declareDummies pos ds).find? l = some o := by
  intro l o h_find
  have h_var : l ∉ ds.map (·.var) := by
    intro h
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    rw [h_fresh.var_fresh d hd] at h_find
    cases h_find
  have h_lbl : l ∉ ds.map (·.lbl) := by
    intro h
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    rw [h_fresh.lbl_fresh d hd] at h_find
    cases h_find
  rw [declareDummies_find?_of_not_mem db pos label ds h_err h_wf h_sc h_fresh l h_var h_lbl]
  exact h_find

/-- Lookups after declaring the dummies: unchanged away from the dummy names; each dummy name is a
variable; each dummy label is its floating hypothesis. -/
theorem declareDummies_find? (db : DB) (pos : Pos) (label : String) (ds : List DummyDecl)
    (h_err : db.error? = none) (h_wf : WellFormedDB db) (h_sc : WellScopedDB db)
    (h_fresh : DummyDeclsFresh db label ds) :
    (∀ l, l ∉ ds.map (·.var) → l ∉ ds.map (·.lbl) →
      (db.declareDummies pos ds).find? l = db.find? l) ∧
    (∀ d ∈ ds, (db.declareDummies pos ds).find? d.var = some (.var d.var)) ∧
    (∀ d ∈ ds, (db.declareDummies pos ds).find? d.lbl =
      some (.hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl)) :=
  ⟨declareDummies_find?_of_not_mem db pos label ds h_err h_wf h_sc h_fresh,
    declareDummies_find?_var db pos label ds h_err h_wf h_sc h_fresh,
    declareDummies_find?_lbl db pos label ds h_err h_wf h_sc h_fresh⟩

/-- The active frame gains the `$d` pairs and the floating hypotheses of the dummies. -/
theorem declareDummies_frame (db : DB) (pos : Pos) (label : String) (ds : List DummyDecl)
    (h_err : db.error? = none) (h_wf : WellFormedDB db) (h_sc : WellScopedDB db)
    (h_fresh : DummyDeclsFresh db label ds) :
    (db.declareDummies pos ds).frame =
      ⟨db.frame.dj ++ (dummyDJs (db.frameFloatVars db.frame) (ds.map (·.var))).toArray,
        db.frame.hyps ++ (ds.map (·.lbl)).toArray⟩ := by
  have h := (declaredDummies_foldl db pos label ds h_err h_wf h_sc h_fresh).frame
  show (DB.withDJ _ _).frame = _
  simp only [DB.withDJ, DB.withFrame, h]

/-- The remaining fields: interrupt flag, mode configuration, scope stack, and the activity stack
(each dummy is active at the current depth). -/
theorem declareDummies_fields (db : DB) (pos : Pos) (label : String) (ds : List DummyDecl)
    (h_err : db.error? = none) (h_wf : WellFormedDB db) (h_sc : WellScopedDB db)
    (h_fresh : DummyDeclsFresh db label ds) :
    (db.declareDummies pos ds).interrupt = db.interrupt ∧
    (db.declareDummies pos ds).config = db.config ∧
    (db.declareDummies pos ds).scopes = db.scopes ∧
    (db.declareDummies pos ds).activeVars =
      db.activeVars ++ (ds.map fun d => (d.var, db.scopes.size)).toArray := by
  have h := declaredDummies_foldl db pos label ds h_err h_wf h_sc h_fresh
  exact ⟨h.interrupt, h.config, h.scopes, h.activeVars⟩

/-! ## Float variables and the kernel view -/

private theorem mapM_option_eq_some_map {α β : Type} (f : α → Option β) (g : α → β)
    (l : List α) (h : ∀ x ∈ l, f x = some (g x)) : l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, h x (List.mem_cons_self ..),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rfl

/-- The stored assertions are unchanged: the new objects are variables and floating
hypotheses. -/
theorem declareDummies_toDatabaseTotal (db : DB) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_err : db.error? = none) (h_wf : WellFormedDB db)
    (h_sc : WellScopedDB db) (h_fresh : DummyDeclsFresh db label ds) :
    Kernel.toDatabaseTotal (db.declareDummies pos ds) = Kernel.toDatabaseTotal db := by
  have h_mono := declareDummies_find?_mono db pos label ds h_err h_wf h_sc h_fresh
  funext l
  unfold Kernel.toDatabaseTotal
  by_cases h_var : l ∈ ds.map (·.var)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h_var
    rw [declareDummies_find?_var db pos label ds h_err h_wf h_sc h_fresh d hd,
      h_fresh.var_fresh d hd]
  · by_cases h_lbl : l ∈ ds.map (·.lbl)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h_lbl
      rw [declareDummies_find?_lbl db pos label ds h_err h_wf h_sc h_fresh d hd,
        h_fresh.lbl_fresh d hd]
    · rw [declareDummies_find?_of_not_mem db pos label ds h_err h_wf h_sc h_fresh l h_var h_lbl]
      cases h_find : db.find? l with
      | none => rfl
      | some o =>
          cases o with
          | assert f fr n =>
              have h_obj := h_wf.2 l (.assert f fr n) h_find
              obtain ⟨frS, h_frS⟩ := Kernel.toFrame_some_of_wfFrame_any db fr h_obj.2
              simp only
              rw [Metamath.StoredStatementSoundness.Runtime.toFrame_stable_of_find_mono db
                (db.declareDummies pos ds) fr frS h_mono h_frS, h_frS]
          | const _ => rfl
          | var _ => rfl
          | hyp _ _ _ => rfl

/-- The kernel view of the new active frame: the old hypotheses followed by one floating
hypothesis per dummy, and the old `$d` pairs followed by the new ones. -/
theorem declareDummies_toFrame (db : DB) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_err : db.error? = none) (h_wf : WellFormedDB db)
    (h_sc : WellScopedDB db) (h_fresh : DummyDeclsFresh db label ds) (frAct : Spec.Frame)
    (h_fr : Kernel.toFrame db db.frame = some frAct) :
    Kernel.toFrame (db.declareDummies pos ds) (db.declareDummies pos ds).frame =
      some ⟨frAct.hyps ++ ds.map (fun d => Spec.Hyp.floating ⟨d.tc⟩ ⟨d.var⟩),
        frAct.dv ++ (dummyDJs (db.frameFloatVars db.frame) (ds.map (·.var))).map
          Kernel.convertDV⟩ := by
  have h_mono := declareDummies_find?_mono db pos label ds h_err h_wf h_sc h_fresh
  have h_new := declareDummies_find?_lbl db pos label ds h_err h_wf h_sc h_fresh
  have h_old := Metamath.StoredStatementSoundness.Runtime.toFrame_stable_of_find_mono db
    (db.declareDummies pos ds) db.frame frAct h_mono h_fr
  have h_dv := Kernel.toFrame_dv_eq db db.frame frAct h_fr
  have h_old_hyps : db.frame.hyps.toList.mapM (Kernel.convertHyp (db.declareDummies pos ds)) =
      some frAct.hyps := by
    unfold Kernel.toFrame at h_old
    cases h_m : db.frame.hyps.toList.mapM (Kernel.convertHyp (db.declareDummies pos ds)) with
    | none => simp [h_m] at h_old
    | some hs =>
        simp only [h_m] at h_old
        cases h_old
        rfl
  have h_new_hyps : (ds.map (·.lbl)).mapM (Kernel.convertHyp (db.declareDummies pos ds)) =
      some (ds.map (fun d => Spec.Hyp.floating ⟨d.tc⟩ ⟨d.var⟩)) := by
    rw [List.mapM_map]
    apply mapM_option_eq_some_map
    intro d hd
    simp [Kernel.convertHyp, h_new d hd, Kernel.toExprOpt, Kernel.toSym, Sym.value]
  rw [declareDummies_frame db pos label ds h_err h_wf h_sc h_fresh]
  unfold Kernel.toFrame
  simp only [Array.toList_append, List.mapM_append, h_old_hyps, h_new_hyps, h_dv]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
    Spec.Frame.mk.injEq, true_and]
  -- `Verify.DJ` is a (non-reducible) synonym of `String × String`
  exact List.map_append

/-! ## The parser invariant -/

/-- Declaring one fresh dummy preserves the database components of the parser invariant. -/
theorem declareDummy_invariants (db : DB) (pos : Pos) (d : DummyDecl)
    (h_wf : WellFormedDB db) (h_sc : WellScopedDBWithScopes db) (h_ok : ScopesOk db)
    (h_err : db.error? = none) (h_var : db.find? d.var = none) (h_lbl : db.find? d.lbl = none)
    (h_ne : d.var ≠ d.lbl) (h_tc : db.isConst d.tc = true) :
    WellFormedDB (db.declareDummy pos d) ∧ WellScopedDBWithScopes (db.declareDummy pos d) ∧
      ScopesOk (db.declareDummy pos d) := by
  have h_occ := floatVarOccursInFrame_of_find?_none db h_wf h_sc.1 d.var h_var
  -- `$v d $.`
  have h_ins_eq := insert_var_fresh_eq db pos d.var h_err h_var
  have h_err1 : (db.insert pos d.var .var).error? = none := by rw [h_ins_eq]; exact h_err
  have h_wf1 : WellFormedDB (db.insert pos d.var .var) :=
    Metamath.ParserOps.insertVar_maintains_wf db pos d.var h_wf h_err h_var
      (Metamath.ParserOps.fresh_not_in_frame_of_wfFrame db db.frame d.var h_wf.1 h_var)
      (Metamath.ParserOps.fresh_not_in_assert_frames_of_wf db h_wf d.var h_var) h_err1
  have h_sc1 : WellScopedDBWithScopes (db.insert pos d.var .var) :=
    Metamath.ParserOps.insert_symbol_fresh_maintains_scopedWithScopes db pos d.var .var
      (Or.inr ⟨d.var, rfl⟩) h_wf h_sc h_err h_var h_err1
  have h_ok1 : ScopesOk (db.insert pos d.var .var) :=
    Metamath.ParserOps.scopesOk_insert db pos d.var .var h_ok
  have h_lbl1 : (db.insert pos d.var .var).find? d.lbl = none := by
    rw [h_ins_eq]
    simp [DB.find?, h_ne]
    simpa [DB.find?] using h_lbl
  have h_occ1 : (db.insert pos d.var .var).floatVarOccursInFrame d.var = false := by
    rw [h_ins_eq, floatVarOccursInFrame_insert_var db d.var d.var _ h_var]
    exact h_occ
  have h_tc_ne : d.tc ≠ d.var := by
    intro h
    rw [h] at h_tc
    simp [DB.isConst, h_var] at h_tc
  have h_decl : Metamath.WF.FormulaSymbolsDeclared (db.insert pos d.var .var)
      #[Verify.Sym.const d.tc, Verify.Sym.var d.var] := by
    intro s h_s
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_s
    rcases h_s with rfl | rfl
    · show (db.insert pos d.var .var).isConst d.tc = true
      rw [h_ins_eq]
      simpa [DB.isConst, DB.find?, Ne.symm h_tc_ne] using h_tc
    · show (db.insert pos d.var .var).isVar d.var = true
      rw [h_ins_eq]
      simp [DB.isVar, DB.find?]
  have h_first : (#[Verify.Sym.const d.tc, Verify.Sym.var d.var] : Verify.Formula).size > 0 ∧
      !(#[Verify.Sym.const d.tc, Verify.Sym.var d.var] : Verify.Formula)[0]!.isVar := by
    simp [Verify.Sym.isVar]
  have h_second : false = false →
      (#[Verify.Sym.const d.tc, Verify.Sym.var d.var] : Verify.Formula).size = 2 ∧
      (#[Verify.Sym.const d.tc, Verify.Sym.var d.var] : Verify.Formula)[1]!.isVar := by
    intro _
    simp [Verify.Sym.isVar]
  have h_fresh_label1 := Metamath.ParserOps.fresh_not_in_frame_of_wfFrame
    (db.insert pos d.var .var) (db.insert pos d.var .var).frame d.lbl h_wf1.1 h_lbl1
  have h_fresh_asserts1 := Metamath.ParserOps.fresh_not_in_assert_frames_of_wf
    (db.insert pos d.var .var) h_wf1 d.lbl h_lbl1
  have h_success : ((db.insert pos d.var .var).insertHyp pos d.lbl false
      #[Verify.Sym.const d.tc, Verify.Sym.var d.var]).error? = none := by
    show (db.declareDummy pos d).error? = none
    rw [declareDummy_eq db pos d h_err h_var h_lbl h_ne h_occ]
    exact h_err
  refine ⟨?_, ?_, ?_⟩
  · -- `lbl $f tc d $.`: the new floating hypothesis is for a fresh variable
    generalize h_db1 : db.insert pos d.var .var = db1 at *
    have h_hyp_eq : db1.insert pos d.lbl
        (fun _ => .hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl) =
          { db1 with
            objects := db1.objects.insert d.lbl
              (.hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl) } :=
      insert_hyp_fresh_eq db1 pos d.lbl false _ h_err1 h_lbl1
    have h_step_eq : db.declareDummy pos d =
        (db1.insert pos d.lbl
          (fun _ => .hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl)).withHyps
          (·.push d.lbl) := by
      rw [h_hyp_eq, declareDummy_eq db pos d h_err h_var h_lbl h_ne h_occ, h_ins_eq]
      rfl
    rw [h_step_eq]
    have h_ins_ok : (db1.insert pos d.lbl
        (fun _ => .hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl)).error? =
          none := by
      rw [h_hyp_eq]; exact h_err1
    have h_wf2 := Metamath.ParserOps.insertHyp_insert_part_maintains_wf db1 pos d.lbl false _
      h_wf1 h_err1 h_first h_second h_lbl1 h_fresh_label1 h_fresh_asserts1 h_ins_ok
    have h_find_lbl : (db1.insert pos d.lbl
        (fun _ => .hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl)).find? d.lbl =
          some (.hyp false #[Verify.Sym.const d.tc, Verify.Sym.var d.var] d.lbl) := by
      rw [h_hyp_eq]
      simp [DB.find?]
    apply Metamath.ParserOps.withHyps_push_preserves_wf _ d.lbl h_wf2
    · refine ⟨false, #[Verify.Sym.const d.tc, Verify.Sym.var d.var], d.lbl, h_find_lbl,
        fun _ => ⟨rfl, d.tc, d.var, rfl, rfl⟩, fun h => ?_⟩
      cases h
    · intro k hk fi f_l lbli lbl_l h_find_k h_find_l h_size_i _
      rw [h_find_lbl] at h_find_l
      cases h_find_l
      have hk1 : k < db1.frame.hyps.size := by
        rw [h_hyp_eq] at hk; exact hk
      have h_ne_k : db1.frame.hyps[k] ≠ d.lbl := h_fresh_label1 k hk1
      have h_find_k1 : db1.find? db1.frame.hyps[k] = some (.hyp false fi lbli) := by
        have h' := h_find_k
        simp only [h_hyp_eq] at h'
        simpa [DB.find?, Ne.symm h_ne_k] using h'
      have h_vi := Metamath.ParserOps.floatVarOccursInFrame_false_implies db1 d.var h_occ1 k hk1
        fi lbli h_find_k1 h_size_i
      simpa using h_vi
  · exact Metamath.ParserOps.insertHyp_full_maintains_scopedWithScopes _ pos d.lbl false _
      h_wf1 h_sc1 h_ok1 h_err1 h_first h_second h_decl h_lbl1 h_fresh_label1 h_fresh_asserts1
      h_success
  · exact Metamath.ParserOps.scopesOk_insertHyp _ pos d.lbl false _ h_ok1

/-- Constants stay constants when the registry only grows. -/
theorem isConst_of_find?_mono {db db' : DB}
    (h_mono : ∀ l o, db.find? l = some o → db'.find? l = some o) {c : String}
    (h : db.isConst c = true) : db'.isConst c = true := by
  unfold DB.isConst at h ⊢
  cases h_find : db.find? c with
  | none => rw [h_find] at h; cases h
  | some o =>
      rw [h_mono c o h_find]
      rw [h_find] at h
      exact h

/-- Variables stay variables when the registry only grows. -/
theorem isVar_of_find?_mono {db db' : DB}
    (h_mono : ∀ l o, db.find? l = some o → db'.find? l = some o) {v : String}
    (h : db.isVar v = true) : db'.isVar v = true := by
  unfold DB.isVar at h ⊢
  cases h_find : db.find? v with
  | none => rw [h_find] at h; cases h
  | some o =>
      rw [h_mono v o h_find]
      rw [h_find] at h
      exact h

/-- Declaring the dummies one by one preserves the database components of the parser
invariant. -/
theorem foldl_declareDummy_invariants (pos : Pos) :
    ∀ (ds : List DummyDecl) (db : DB),
      WellFormedDB db → WellScopedDBWithScopes db → ScopesOk db → db.error? = none →
      (∀ d ∈ ds, db.find? d.var = none) → (∀ d ∈ ds, db.find? d.lbl = none) →
      (ds.map (·.var) ++ ds.map (·.lbl)).Nodup → (∀ d ∈ ds, db.isConst d.tc = true) →
      WellFormedDB (ds.foldl (fun db d => db.declareDummy pos d) db) ∧
      WellScopedDBWithScopes (ds.foldl (fun db d => db.declareDummy pos d) db) ∧
      ScopesOk (ds.foldl (fun db d => db.declareDummy pos d) db)
  | [], _, h_wf, h_sc, h_ok, _, _, _, _, _ => ⟨h_wf, h_sc, h_ok⟩
  | d :: ds, db, h_wf, h_sc, h_ok, h_err, h_var, h_lbl, h_nd, h_tc => by
      obtain ⟨h_ne, h_rest, h_nd'⟩ := nodup_dummy_cons h_nd
      have h_var_d := h_var d (List.mem_cons_self ..)
      have h_lbl_d := h_lbl d (List.mem_cons_self ..)
      have h_occ_d := floatVarOccursInFrame_of_find?_none db h_wf h_sc.1 d.var h_var_d
      have h_find := declareDummy_find? db pos d h_err h_var_d h_lbl_d h_ne h_occ_d
      have h_eq := declareDummy_eq db pos d h_err h_var_d h_lbl_d h_ne h_occ_d
      obtain ⟨h_wf1, h_sc1, h_ok1⟩ := declareDummy_invariants db pos d h_wf h_sc h_ok h_err
        h_var_d h_lbl_d h_ne (h_tc d (List.mem_cons_self ..))
      have h_err1 : (db.declareDummy pos d).error? = none := by rw [h_eq]; exact h_err
      have h_var1 : ∀ e ∈ ds, (db.declareDummy pos d).find? e.var = none := by
        intro e he
        obtain ⟨h1, h2, _, _⟩ := h_rest e he
        rw [h_find, if_neg (Ne.symm h2), if_neg (Ne.symm h1)]
        exact h_var e (List.mem_cons_of_mem _ he)
      have h_lbl1 : ∀ e ∈ ds, (db.declareDummy pos d).find? e.lbl = none := by
        intro e he
        obtain ⟨_, _, h3, h4⟩ := h_rest e he
        rw [h_find, if_neg (Ne.symm h4), if_neg (Ne.symm h3)]
        exact h_lbl e (List.mem_cons_of_mem _ he)
      have h_mono1 : ∀ l o, db.find? l = some o → (db.declareDummy pos d).find? l = some o := by
        intro l o h_l
        have h1 : d.lbl ≠ l := by
          intro h; rw [← h, h_lbl_d] at h_l; cases h_l
        have h2 : d.var ≠ l := by
          intro h; rw [← h, h_var_d] at h_l; cases h_l
        rw [h_find, if_neg h1, if_neg h2]
        exact h_l
      have h_tc1 : ∀ e ∈ ds, (db.declareDummy pos d).isConst e.tc = true :=
        fun e he => isConst_of_find?_mono h_mono1 (h_tc e (List.mem_cons_of_mem _ he))
      simp only [List.foldl_cons]
      exact foldl_declareDummy_invariants pos ds _ h_wf1 h_sc1 h_ok1 h_err1 h_var1 h_lbl1 h_nd'
        h_tc1

/-- Appending `$d` pairs of declared variables, each ordered, preserves the database components of
the parser invariant. -/
theorem withDJ_append_invariants :
    ∀ (L : List Verify.DJ) (db : DB),
      WellFormedDB db → WellScopedDBWithScopes db → ScopesOk db →
      (∀ p ∈ L, p.1 < p.2 ∧ db.isVar p.1 = true ∧ db.isVar p.2 = true) →
      WellFormedDB (db.withDJ (· ++ L.toArray)) ∧
      WellScopedDBWithScopes (db.withDJ (· ++ L.toArray)) ∧
      ScopesOk (db.withDJ (· ++ L.toArray))
  | [], db, h_wf, h_sc, h_ok, _ => by
      have h : db.withDJ (· ++ ([] : List Verify.DJ).toArray) = db := by
        simp [DB.withDJ, DB.withFrame]
      rw [h]
      exact ⟨h_wf, h_sc, h_ok⟩
  | p :: L, db, h_wf, h_sc, h_ok, h_pairs => by
      have h_eq : db.withDJ (· ++ (p :: L).toArray) =
          (db.withDJ (·.push p)).withDJ (· ++ L.toArray) := by
        simp [DB.withDJ, DB.withFrame]
      have h_p := h_pairs p (List.mem_cons_self ..)
      have h_wf' := Metamath.ParserOps.wellFormedDB_preserved_by_withDJ db (·.push p) h_wf
      have h_sc' := Metamath.ParserOps.wellScopedDBWithScopes_withDJ_push db p h_wf h_sc h_ok h_p
      have h_ok' := Metamath.ParserOps.scopesOk_withDJ_push db p h_ok
      rw [h_eq]
      exact withDJ_append_invariants L _ h_wf' h_sc' h_ok'
        (fun q hq => h_pairs q (List.mem_cons_of_mem _ hq))

/-- A `$d` pair as the parser stores it is ordered. -/
theorem canonDJ_ordered {v w : String} (h : v ≠ w) :
    (canonDJ v w).1 < (canonDJ v w).2 ∧
    (((canonDJ v w).1 = v ∧ (canonDJ v w).2 = w) ∨
      ((canonDJ v w).1 = w ∧ (canonDJ v w).2 = v)) := by
  unfold canonDJ
  by_cases h_lt : v < w
  · simp [h_lt]
  · have h_gt : w < v := by
      by_cases h_gt' : w < v
      · exact h_gt'
      · exact absurd (String.lt_antisymm h_lt h_gt') h
    simp [h_lt, h_gt]

/-- Each pair of `dummyDJs seen vs` joins a member of `vs` to a different earlier name. -/
theorem mem_dummyDJs_canon (vs : List String) :
    ∀ (seen : List String) (p : Verify.DJ), (∀ v ∈ vs, v ∉ seen) → vs.Nodup →
      p ∈ dummyDJs seen vs →
      ∃ v w, p = canonDJ v w ∧ v ∈ vs ∧ (w ∈ seen ∨ w ∈ vs) ∧ v ≠ w := by
  induction vs with
  | nil =>
      intro seen p _ _ h
      simp [dummyDJs] at h
  | cons v vs ih =>
      intro seen p h_fresh h_nd h
      simp only [dummyDJs, List.mem_append, List.mem_map] at h
      rcases h with ⟨w, hw, rfl⟩ | h
      · refine ⟨v, w, rfl, List.mem_cons_self .., Or.inl hw, ?_⟩
        intro h_eq
        subst h_eq
        exact h_fresh v (List.mem_cons_self ..) hw
      · have h_fresh' : ∀ u ∈ vs, u ∉ seen ++ [v] := by
          intro u hu h_mem
          rcases List.mem_append.mp h_mem with h1 | h1
          · exact h_fresh u (List.mem_cons_of_mem _ hu) h1
          · rw [List.mem_singleton] at h1
            subst h1
            exact (List.nodup_cons.mp h_nd).1 hu
        obtain ⟨u, w, rfl, hu, hw, h_ne⟩ := ih (seen ++ [v]) p h_fresh'
          (List.nodup_cons.mp h_nd).2 h
        refine ⟨u, w, rfl, List.mem_cons_of_mem _ hu, ?_, h_ne⟩
        rcases hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact Or.inl hw
          · rw [List.mem_singleton] at hw
            subst hw
            exact Or.inr (List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ hw)

/-- Declaring fresh dummy variables between statements preserves the parser invariant. -/
theorem declareDummies_stateInv (s : ParserState) (pos : Pos) (label : String)
    (ds : List DummyDecl) (h_inv : ParserStateInv s) (h_tokp : s.tokp = .start)
    (h_err : s.db.error? = none) (h_fresh : DummyDeclsFresh s.db label ds) :
    ParserStateInv (s.withDB (·.declareDummies pos ds)) := by
  obtain ⟨h_wf, h_sc, h_ok, _⟩ := h_inv
  have h_nd := h_fresh.nodup_names
  obtain ⟨h_wfF, h_scF, h_okF⟩ := foldl_declareDummy_invariants pos ds s.db h_wf h_sc h_ok h_err
    h_fresh.var_fresh h_fresh.lbl_fresh h_nd h_fresh.tc_const
  have hF := declaredDummies_foldl s.db pos label ds h_err h_wf h_sc.1 h_fresh
  have h_monoF : ∀ l o, s.db.find? l = some o →
      (ds.foldl (fun db d => db.declareDummy pos d) s.db).find? l = some o := by
    intro l o h_l
    have h_var : l ∉ ds.map (·.var) := by
      intro h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      rw [h_fresh.var_fresh d hd] at h_l
      cases h_l
    have h_lbl : l ∉ ds.map (·.lbl) := by
      intro h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      rw [h_fresh.lbl_fresh d hd] at h_l
      cases h_l
    rw [hF.find_of_not_mem l h_var h_lbl]
    exact h_l
  have h_isVar_new : ∀ v ∈ ds.map (·.var),
      (ds.foldl (fun db d => db.declareDummy pos d) s.db).isVar v = true := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    simp [DB.isVar, hF.find_var d hd]
  have h_isVar_old : ∀ w ∈ s.db.frameFloatVars s.db.frame,
      (ds.foldl (fun db d => db.declareDummy pos d) s.db).isVar w = true :=
    fun w hw => isVar_of_find?_mono h_monoF
      (Metamath.WF.frameFloatVars_mem_isVar s.db s.db.frame h_sc.1 w hw)
  have h_vs_fresh : ∀ v ∈ ds.map (·.var), v ∉ s.db.frameFloatVars s.db.frame := by
    intro v hv h_mem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    have h_isVar := Metamath.WF.frameFloatVars_mem_isVar s.db s.db.frame h_sc.1 d.var h_mem
    simp [DB.isVar, h_fresh.var_fresh d hd] at h_isVar
  have h_vs_nd : (ds.map (·.var)).Nodup :=
    List.Nodup.sublist (List.sublist_append_left _ _) h_nd
  have h_pairs : ∀ p ∈ dummyDJs (s.db.frameFloatVars s.db.frame) (ds.map (·.var)),
      p.1 < p.2 ∧ (ds.foldl (fun db d => db.declareDummy pos d) s.db).isVar p.1 = true ∧
        (ds.foldl (fun db d => db.declareDummy pos d) s.db).isVar p.2 = true := by
    intro p hp
    obtain ⟨v, w, rfl, hv, hw, h_ne⟩ :=
      mem_dummyDJs_canon (ds.map (·.var)) _ p h_vs_fresh h_vs_nd hp
    have h_v := h_isVar_new v hv
    have h_w : (ds.foldl (fun db d => db.declareDummy pos d) s.db).isVar w = true := by
      rcases hw with hw | hw
      · exact h_isVar_old w hw
      · exact h_isVar_new w hw
    obtain ⟨h_lt, h_cases⟩ := canonDJ_ordered h_ne
    refine ⟨h_lt, ?_, ?_⟩
    · rcases h_cases with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]; exact h_v
      · rw [h1]; exact h_w
    · rcases h_cases with ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [h2]; exact h_w
      · rw [h2]; exact h_v
  obtain ⟨h_wf', h_sc', h_ok'⟩ := withDJ_append_invariants _ _ h_wfF h_scF h_okF h_pairs
  refine ⟨h_wf', h_sc', h_ok', ?_⟩
  show TokpInv _ s.tokp
  rw [h_tokp]
  trivial

/-! ## Examples

A kernel-checked positive instance, and a negative one showing that `declareDummies_error` needs
the well-scopedness hypothesis: without it a floating hypothesis of the active frame may name an
unregistered variable, and declaring that name as a dummy then fails the parser's check that a
variable has at most one floating hypothesis in the active frame. -/

namespace DeclareExamples

/-- `wff` is a constant; nothing else is declared; the active frame is empty. -/
def dbP : DB :=
  { (default : DB) with objects := (∅ : Std.HashMap String Object).insert "wff" (.const "wff") }

/-- The dummy `x`, typed by `wx $f wff x $.`. -/
def dX : DummyDecl := ⟨"wff", "x", "wx"⟩

theorem dbP_find? (l : String) :
    dbP.find? l = if l = "wff" then some (.const "wff") else none := by
  show ((∅ : Std.HashMap String Object).insert "wff" (.const "wff"))[l]? = _
  rw [Std.HashMap.getElem?_insert]
  by_cases h : l = "wff"
  · subst h; simp
  · simp [h, Ne.symm h]

theorem dbP_wf : WellFormedDB dbP := by
  refine ⟨⟨fun i hi => absurd hi (by simp [dbP]), fun i j hi _ => absurd hi (by simp [dbP])⟩,
    ?_⟩
  intro lbl obj h
  rw [dbP_find?] at h
  by_cases h' : lbl = "wff"
  · rw [if_pos h'] at h
    cases h
    trivial
  · rw [if_neg h'] at h
    cases h

theorem dbP_scoped : WellScopedDB dbP := by
  refine ⟨⟨fun i hi => absurd hi (by simp [dbP]), fun v w h => by cases h⟩, ?_⟩
  intro lbl obj h
  rw [dbP_find?] at h
  by_cases h' : lbl = "wff"
  · rw [if_pos h'] at h
    cases h
    trivial
  · rw [if_neg h'] at h
    cases h

theorem dbP_fresh : DummyDeclsFresh dbP "th" [dX] where
  var_fresh := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    rw [dbP_find?]
    decide
  lbl_fresh := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    rw [dbP_find?]
    decide
  nodup := by decide
  tc_const := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    show (if let some (.const _) := dbP.find? "wff" then true else false) = true
    rw [dbP_find?]
    rfl

/-- Positive: declaring `x` at `dbP` succeeds, and the kernel view of the active frame gains exactly
`$f wff x` (there is no earlier float variable, so no `$d` pair). -/
theorem dbP_declare :
    (dbP.declareDummies ⟨0, 0⟩ [dX]).error? = none ∧
    Kernel.toFrame (dbP.declareDummies ⟨0, 0⟩ [dX]) (dbP.declareDummies ⟨0, 0⟩ [dX]).frame =
      some ⟨[.floating ⟨"wff"⟩ ⟨"x"⟩], []⟩ := by
  refine ⟨declareDummies_error dbP ⟨0, 0⟩ "th" [dX] rfl dbP_wf dbP_scoped dbP_fresh, ?_⟩
  rw [declareDummies_toFrame dbP ⟨0, 0⟩ "th" [dX] rfl dbP_wf dbP_scoped dbP_fresh ⟨[], []⟩
    rfl]
  rfl

/-- `wx $f wff x $.` is in the active frame although `x` was never declared. -/
def dbN : DB :=
  { (default : DB) with
    frame := ⟨#[], #["wx"]⟩
    objects := ((∅ : Std.HashMap String Object).insert "wff" (.const "wff")).insert "wx"
      (.hyp false #[.const "wff", .var "x"] "wx") }

/-- The dummy `x`, typed by `wy $f wff x $.`. -/
def dY : DummyDecl := ⟨"wff", "x", "wy"⟩

theorem dbN_find? (l : String) :
    dbN.find? l =
      if l = "wx" then some (.hyp false #[.const "wff", .var "x"] "wx")
      else if l = "wff" then some (.const "wff") else none := by
  show (((∅ : Std.HashMap String Object).insert "wff" (.const "wff")).insert "wx"
    (.hyp false #[.const "wff", .var "x"] "wx"))[l]? = _
  rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
  by_cases h1 : l = "wx"
  · subst h1; simp
  · by_cases h2 : l = "wff"
    · subst h2; simp
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem dbN_wf : WellFormedDB dbN := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    have h_i : i = 0 := by
      have : i < 1 := hi
      omega
    subst h_i
    refine ⟨false, #[.const "wff", .var "x"], "wx", ?_, fun _ => ⟨rfl, "wff", "x", rfl, rfl⟩,
      fun h => by cases h⟩
    show dbN.find? "wx" = _
    rw [dbN_find?, if_pos rfl]
  · intro i j hi hj h_ne
    have : i < 1 := hi
    have : j < 1 := hj
    omega
  · intro lbl obj h
    rw [dbN_find?] at h
    by_cases h1 : lbl = "wx"
    · rw [if_pos h1] at h
      cases h
      exact ⟨rfl, "wff", "x", rfl, rfl⟩
    · rw [if_neg h1] at h
      by_cases h2 : lbl = "wff"
      · rw [if_pos h2] at h
        cases h
        trivial
      · rw [if_neg h2] at h
        cases h

theorem dbN_fresh : DummyDeclsFresh dbN "th" [dY] where
  var_fresh := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    rw [dbN_find?]
    decide
  lbl_fresh := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    rw [dbN_find?]
    decide
  nodup := by decide
  tc_const := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    show (if let some (.const _) := dbN.find? "wff" then true else false) = true
    rw [dbN_find?]
    rfl

/-- Negative: at `dbN` (error-free, well-formed, default configuration, fresh dummy) the
declaration fails, because `x` already has the floating hypothesis `wx` in the active frame. -/
theorem dbN_declare_error : (dbN.declareDummies ⟨0, 0⟩ [dY]).error? ≠ none := by
  have h_x : dbN.find? "x" = none := by rw [dbN_find?]; decide
  have h_ins := insert_var_fresh_eq dbN ⟨0, 0⟩ "x" rfl h_x
  have h_occ : (dbN.insert ⟨0, 0⟩ "x" .var).floatVarOccursInFrame "x" = true := by
    rw [h_ins, floatVarOccursInFrame_insert_var dbN "x" "x" _ h_x]
    show ([("wx" : String)].any fun lbl => match dbN.find? lbl with
      | some (.hyp false prevF _) =>
          prevF.size >= 2 && (match prevF[1]! with | .var v' => v' | _ => "") == "x"
      | _ => false) = true
    simp [dbN_find?]
  have h_err1 : (dbN.insert ⟨0, 0⟩ "x" .var).error? = none := by rw [h_ins]; rfl
  have h_cfg : dbN.config.allowDuplicateFloat = false := rfl
  have h_chk : ((dbN.insert ⟨0, 0⟩ "x" .var).insertHypChecks ⟨0, 0⟩ false
      #[.const "wff", .var "x"]).error = true := by
    simp [DB.insertHypChecks, Formula.hasConstHead, Formula.isFloatShape, DB.error, h_err1, h_cfg,
      h_occ, Sym.value, DB.mkErrorFromEvidence, DB.mkErrorWithEvidence]
  show ((dbN.insert ⟨0, 0⟩ "x" .var).insertHyp ⟨0, 0⟩ "wy" false
    #[.const "wff", .var "x"]).error? ≠ none
  simp only [DB.insertHyp, h_chk, if_true]
  exact fun h => by simp [DB.error, h] at h_chk

/-- Hence `dbN` is not well-scoped: its floating hypothesis `wx` names an undeclared variable. -/
theorem dbN_not_wellScoped : ¬ WellScopedDB dbN := fun h =>
  dbN_declare_error (declareDummies_error dbN ⟨0, 0⟩ "th" [dY] rfl dbN_wf h dbN_fresh)

end DeclareExamples

end Metamath.CheckerCompleteness
