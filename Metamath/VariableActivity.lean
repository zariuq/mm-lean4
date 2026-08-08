/-
# Metamath.VariableActivity

Variable activity as the Metamath book defines it, and the proof that the
verifier's `activeVars` stack implements it.

[MM §4.2.2] "A variable ... is active from the place it is declared until the
end of the block in which it was declared."  The verifier does not store block
membership directly: it tags each `$v` declaration with the block depth that
made it and filters the tagged list when a block closes.  Nothing said that this
representation *is* the book's rule, so this module supplies the missing link.

The reference model is the one `mmverify.py` uses and the book describes: a
stack of blocks, each carrying the variables its `$v` statements declared.  A
variable is active exactly when some open block declared it.  `DB.scopeStack`
abstracts the tagged array to that model, and the simulation theorems below show
each block operation commutes with the abstraction.

Two facts are proved separately because they carry different weight:

* `scopeStack_popScope` and `scopeStack_declare` hold unconditionally — the
  abstraction never looks past the current depth, so closing a block and adding
  a declaration commute with it outright;
* `scopeStack_pushScope` and the characterization
  `isActiveVar_iff_scopeStack_active` need `ActiveVarsBounded`.  Opening a block
  exposes a new depth, and the new block is empty only because no stale tag
  names it; the characterization is exactly the claim that no declaration
  survives the block that made it.  That invariant travels with `ScopesOk`,
  which `Metamath.ParserOperations` threads through every parse step.
-/

import Metamath.Verify
import Metamath.ParserOperations

namespace Metamath
namespace Verify

open Metamath.Verify

/-! ## The book's model -/

/-- [MM §4.2.2] A stack of open blocks, outermost first, each listing the
variables declared by the `$v` statements inside it. -/
abbrev ScopeStack := List (List String)

namespace ScopeStack

/-- A variable is active exactly when some open block declared it. -/
def active (st : ScopeStack) (v : String) : Bool :=
  st.any (fun block => block.contains v)

/-- Opening a block (`${`) pushes an empty innermost block. -/
def open' (st : ScopeStack) : ScopeStack := st ++ [[]]

/-- Closing a block (`$}`) discards the innermost block, and with it exactly the
declarations that block made. -/
def close (st : ScopeStack) : ScopeStack := st.dropLast

/-- A `$v` declaration adds the variable to the innermost open block. -/
def declare (st : ScopeStack) (v : String) : ScopeStack :=
  match st.reverse with
  | [] => [[v]]
  | inner :: outer => ((inner ++ [v]) :: outer).reverse

end ScopeStack

/-! ## The abstraction -/

namespace DB

/-- Abstract the depth-tagged declaration array to the book's block stack: block
`d` holds the names tagged with depth `d`, for every currently-open depth.

Depths beyond `scopes.size` are not represented — a tag deeper than the current
nesting denotes a block that has already closed, and `ActiveVarsBounded` records
that no such tag survives. -/
def scopeStack (db : DB) : ScopeStack :=
  (List.range (db.scopes.size + 1)).map fun d =>
    db.activeVars.toList.filterMap fun e => if e.2 = d then some e.1 else none

/-! ## Simulation: each block operation commutes with the abstraction -/

/-- Opening a block adds an empty innermost block, and nothing else.

The new block is empty precisely because no surviving declaration is tagged
deeper than the current nesting — which is what `ActiveVarsBounded` says. -/
theorem scopeStack_pushScope (db : DB) (h_bnd : db.ActiveVarsBounded) :
    (db.pushScope).scopeStack = db.scopeStack.open' := by
  unfold scopeStack ScopeStack.open' DB.pushScope
  simp only [List.range_succ, List.map_append, Array.size_push]
  congr 1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
    List.filterMap_eq_nil_iff]
  intro e h_mem
  have h := h_bnd e h_mem
  simp only [ite_eq_right_iff]
  omega

/-- Closing a block discards exactly the innermost block — with it, exactly the
declarations that block made, and no others.

This is the direction that carries the book's rule: a variable declared inside
the closing block disappears, while every declaration made in an enclosing block
survives untouched. -/
theorem scopeStack_popScope (db : DB) (pos : Pos) (sc : Nat × Nat)
    (h_back : db.scopes.back? = some sc) :
    (DB.popScope pos db).scopeStack = db.scopeStack.close := by
  have h_pos : 0 < db.scopes.size := by
    cases h_sz : db.scopes.size with
    | zero =>
        exfalso
        have h_none : db.scopes.back? = none := by
          simp [Array.back?, h_sz]
        rw [h_none] at h_back
        cases h_back
    | succ n => omega
  unfold scopeStack ScopeStack.close DB.popScope
  simp only [h_back, Array.size_pop]
  have h_eq : db.scopes.size - 1 + 1 = db.scopes.size := by omega
  rw [h_eq, ← List.map_dropLast]
  have h_dl :
      (List.range (db.scopes.size + 1)).dropLast = List.range db.scopes.size := by
    simp [List.range_succ]
  rw [h_dl]
  apply List.map_congr_left
  intro d h_d
  have h_lt := List.mem_range.mp h_d
  have h_dle : d ≤ db.scopes.size - 1 := by omega
  -- at a depth that survives the pop, the filter removes nothing this depth names
  have h_keep : ∀ l : List (String × Nat),
      List.filterMap (fun e => if e.2 = d then some e.1 else none)
          (List.filter (fun e => decide (e.2 ≤ db.scopes.size - 1)) l)
        = List.filterMap (fun e => if e.2 = d then some e.1 else none) l := by
    intro l
    induction l with
    | nil => simp
    | cons e t ih =>
        by_cases h_f : e.2 ≤ db.scopes.size - 1
        · -- survives the filter: both sides consume it identically
          by_cases h_de : e.2 = d <;>
            simp [h_f, h_de, h_dle, ih]
        · -- dropped by the filter, but too deep to be named by `d` anyway
          have h_ne : ¬ (e.2 = d) := by omega
          simp [h_f, h_ne, ih]
  simpa [Array.toList_filter] using h_keep db.activeVars.toList

/-- A `$v` declaration adds the variable to the innermost open block.

Stated on the array update that `insert`'s variable branch performs, so it is
independent of which of the two branches (fresh name, or reactivated name)
produced it. -/
theorem scopeStack_declare (db : DB) (v : String) :
    ({ db with activeVars := db.activeVars.push (v, db.scopes.size) } : DB).scopeStack
      = db.scopeStack.declare v := by
  unfold scopeStack ScopeStack.declare
  simp only [Array.toList_push]
  have h_split :
      List.range (db.scopes.size + 1) = List.range db.scopes.size ++ [db.scopes.size] := by
    simp [List.range_succ]
  rw [h_split, List.map_append]
  have h_outer :
      List.map (fun d => List.filterMap (fun e => if e.2 = d then some e.1 else none)
          (db.activeVars.toList ++ [(v, db.scopes.size)])) (List.range db.scopes.size)
        = List.map (fun d => List.filterMap (fun e => if e.2 = d then some e.1 else none)
            db.activeVars.toList) (List.range db.scopes.size) := by
    apply List.map_congr_left
    intro d h_d
    have h_lt := List.mem_range.mp h_d
    have h_ne : ¬ ((v, db.scopes.size).2 = d) := by simpa using (by omega : db.scopes.size ≠ d)
    simp [List.filterMap_append, h_ne]
  rw [h_outer]
  simp [List.map_append, List.filterMap_append]

/-! ## Characterization: the implementation *is* the book's rule -/

/-- The activity scan, restated as membership with an explicit depth tag. -/
theorem activeVars_any_iff (a : Array (String × Nat)) (v : String) :
    (a.any fun e => e.1 == v) = true ↔ ∃ d, (v, d) ∈ a := by
  simp only [Array.any_eq_true, Array.mem_iff_getElem, beq_iff_eq]
  constructor
  · rintro ⟨i, h_i, h_eq⟩
    exact ⟨a[i].2, i, h_i, by simp [← h_eq]⟩
  · rintro ⟨d, i, h_i, h_eq⟩
    exact ⟨i, h_i, by simp [h_eq]⟩

/-- [MM §4.2.2] A declared name is active exactly when some still-open block
declared it.

This is the statement the tagged-array representation was always meant to have,
and it is where `ActiveVarsBounded` earns its keep: without it a tag could name a
block that has already closed, and the two sides would part company. -/
theorem isActiveVar_iff_scopeStack_active (db : DB) (v : String)
    (h_bnd : db.ActiveVarsBounded) :
    db.isActiveVar v = true ↔ (db.isVar v = true ∧ db.scopeStack.active v = true) := by
  unfold isActiveVar
  rw [Bool.and_eq_true, activeVars_any_iff]
  unfold scopeStack ScopeStack.active
  constructor
  · rintro ⟨h_var, d, h_mem⟩
    refine ⟨h_var, ?_⟩
    have h_le : d ≤ db.scopes.size := h_bnd (v, d) (by simpa using h_mem)
    simp only [List.any_eq_true, List.mem_map]
    refine ⟨_, ⟨d, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    simp only [List.contains_iff_mem, List.mem_filterMap]
    exact ⟨(v, d), by simpa using h_mem, by simp⟩
  · rintro ⟨h_var, h_active⟩
    refine ⟨h_var, ?_⟩
    simp only [List.any_eq_true, List.mem_map] at h_active
    obtain ⟨block, ⟨d, _, rfl⟩, h_in⟩ := h_active
    simp only [List.contains_iff_mem, List.mem_filterMap] at h_in
    obtain ⟨e, h_mem, h_some⟩ := h_in
    by_cases h_eq : e.2 = d
    · simp only [h_eq, if_pos] at h_some
      have h_fst : e.1 = v := by simpa using h_some
      refine ⟨e.2, ?_⟩
      have h_pair : (v, e.2) = e := by simp [← h_fst]
      rw [h_pair]
      simpa using h_mem
    · simp [h_eq] at h_some

/-! ## The invariant holds of every state a parse can reach -/

open Metamath.ParserOps in
/-- `ActiveVarsBounded` is part of `ScopesOk`, which the parser threads through
`feedToken`, `feed` and `feedAll`.  Recording the projection makes the reach
from a parse to the characterization above explicit. -/
theorem ActiveVarsBounded_of_scopesOk {db : DB} (h : ScopesOk db) :
    db.ActiveVarsBounded := h.2.2.1

open Metamath.ParserOps in
/-- The initial parser DB satisfies the bound. -/
theorem initDB_activeVarsBounded (config : ModeConfig) :
    ({ (default : DB) with config := config } : DB).ActiveVarsBounded :=
  ActiveVarsBounded_of_scopesOk (initDB_scopesOk config)

open Metamath.ParserOps in
/-- [MM §4.2.2] The payoff: on any state a successful parse can reach, a
declared name is active exactly when a still-open block declared it.

This is the statement that the depth-tagged stack *is* the book's rule rather
than merely agreeing with it on the cases anyone happened to test. -/
theorem isActiveVar_iff_scopeStack_active_of_scopesOk {db : DB} (v : String)
    (h : ScopesOk db) :
    db.isActiveVar v = true ↔ (db.isVar v = true ∧ db.scopeStack.active v = true) :=
  isActiveVar_iff_scopeStack_active db v (ActiveVarsBounded_of_scopesOk h)

end DB

end Verify
end Metamath
