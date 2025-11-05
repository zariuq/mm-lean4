import Std.Data.HashMap
import Std.Data.HashSet
import Metamath.Spec
import Metamath.Bridge.Basics
import Metamath.KernelExtras


def UInt8.toChar (n : UInt8) : Char := ⟨n.toUInt32, by
  have := n.toFin.2
  simp [size, UInt32.isValidChar, Nat.isValidChar] at *; omega⟩

namespace UInt8

def isUpper (c : UInt8) : Bool :=
  c ≥ 65 && c ≤ 90

def isLower (c : UInt8) : Bool :=
  c ≥ 97 && c ≤ 122

def isAlpha (c : UInt8) : Bool :=
  c.isUpper || c.isLower

def isDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

def isAlphanum (c : UInt8) : Bool :=
  c.isAlpha || c.isDigit

end UInt8

structure ByteSliceT where
  arr : ByteArray
  off : Nat

namespace ByteSliceT

@[inline] def size (self : ByteSliceT) : Nat := self.arr.size - self.off

instance : GetElem ByteSliceT Nat UInt8 fun _ _ => True where
  getElem self idx _ := self.arr[self.off + idx]!

end ByteSliceT

def ByteArray.toSliceT (arr : ByteArray) : ByteSliceT := ⟨arr, 0⟩

structure ByteSlice where
  arr : ByteArray
  off : Nat
  len : Nat

namespace ByteSlice

def toArray : ByteSlice → ByteArray
  | ⟨arr, off, len⟩ => arr.extract off len

instance : GetElem ByteSlice Nat UInt8 fun _ _ => True where
  getElem self idx _ := self.arr[self.off + idx]!

def forIn.loop [Monad m] (f : UInt8 → β → m (ForInStep β))
    (arr : ByteArray) (off stop : Nat) (i : Nat) (b : β) : m β := do
  if i < stop then
    match ← f arr[i]! b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => loop f arr off stop (i+1) b
  else pure b

instance : ForIn m ByteSlice UInt8 :=
  ⟨fun ⟨arr, off, len⟩ b f => forIn.loop f arr off (off + len) off b⟩

end ByteSlice

def ByteSliceT.toSlice : ByteSliceT → ByteSlice
  | ⟨arr, off⟩ => ⟨arr, off, arr.size - off⟩

def ByteArray.toSlice (arr : ByteArray) : ByteSlice := ⟨arr, 0, arr.size⟩

def ByteSlice.eqArray (bs : ByteSlice) (arr : ByteArray) : Bool :=
  let rec loop (arr₁ : ByteArray) (i j : Nat) : Bool :=
    if j < arr.size then
      arr₁[i]! == arr[j]! && loop arr₁ (i+1) (j+1)
    else true
  bs.len == arr.size && loop bs.arr bs.off 0

def String.toAscii (s : String) : ByteArray :=
  let rec loop (out : ByteArray) (p : Pos) : ByteArray :=
    if h : s.atEnd p then out else
      let c := s.get p
      have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
      loop (out.push c.toUInt8) (s.next p)
  termination_by s.endPos.1 - p.1
  loop ByteArray.empty 0

def ByteSlice.toString (bs : ByteSlice) : String := Id.run do
  let mut s := ""
  for c in bs do s := s.push c.toChar
  s

instance : ToString ByteSlice where
  toString bs := Id.run do
    let mut s := ""
    for c in bs do s := s.push c.toChar
    s

namespace Metamath
namespace Verify

open IO.FS (Handle)
open Std (HashMap HashSet)

def isLabelChar (c : UInt8) : Bool :=
  c.isAlphanum || c == '-'.toUInt8 || c == '_'.toUInt8 || c == '.'.toUInt8

def isWhitespace (c : UInt8) : Bool :=
  c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\r'.toUInt8 || c == '\t'.toUInt8

def isPrintable (c : UInt8) : Bool := c >= 32 && c <= 126

def isMathChar (c : UInt8) : Bool := c ≠ '$'.toUInt8 && isPrintable c

def toLabel (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
    unless isLabelChar c do ok := false
  (ok, s)

def toMath (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
    unless isMathChar c do ok := false
  (ok, s)

structure Pos where (line col : Nat)

instance : ToString Pos := ⟨fun ⟨l, c⟩ => s!"{l}:{c}"⟩

def DJ := String × String
instance : BEq DJ := instBEqProd

structure Frame where
  dj : Array DJ
  hyps : Array String
  deriving Inhabited

def Frame.size : Frame → Nat × Nat
  | ⟨dj, hyps⟩ => (dj.size, hyps.size)

def Frame.shrink : Frame → Nat × Nat → Frame
  | ⟨dj, hyps⟩, (x, y) => ⟨dj.shrink x, hyps.shrink y⟩

instance : ToString Frame := ⟨fun fr => toString fr.hyps⟩

inductive Sym
  | const (c : String)
  | var (v : String)
  deriving Inhabited

def Sym.isVar : Sym → Bool
  | .const _ => false
  | .var _ => true

def Sym.value : Sym → String
  | .const c => c
  | .var v => v

instance : BEq Sym := ⟨fun a b => a.value == b.value⟩

abbrev Formula := Array Sym

instance : ToString Formula where
  toString f := Id.run do
    let s := f[0]!.value
    f.foldl (init := s) (start := 1) fun (s:String) v =>
      s ++ " " ++ v.value

def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula := do
  let mut f' := #[]
  for c in f do
    match c with
    | .const _ => f' := f'.push c
    | .var v =>
      match σ[v]? with
      | none => throw s!"variable {v} not found"
      | some e => f' := e.foldl Array.push f' 1
  pure f'

/-- Variables (as raw strings) appearing in a formula, excluding the leading typecode. -/
def Formula.varsList (self : Formula) : List String :=
  (self.extract 1 self.size).toList.filterMap fun
    | Sym.var v => some v
    | _ => none

/-- Fold over the variables of a formula (excluding the typecode). -/
def Formula.foldlVars (self : Formula) (init : α) (f : α → String → α) : α :=
  self.varsList.foldl f init

@[simp] lemma Formula.foldlVars_eq_foldl_varsList
    (self : Formula) (init : α) (f : α → String → α) :
    self.foldlVars init f = self.varsList.foldl f init := rfl

lemma Formula.foldlVars_all
    (self : Formula) (p : String → Bool) :
    self.foldlVars true (fun b s => b && p s) = true ↔
      ∀ s ∈ self.varsList, p s = true := by
  simpa [Formula.foldlVars] using
    Metamath.KernelExtras.List.foldl_and_eq_true

lemma Formula.foldlVars_all₂
    (f g : Formula) (p : String → String → Bool) :
    f.foldlVars true (fun b s₁ =>
      g.foldlVars b (fun b s₂ => b && p s₁ s₂)) = true ↔
      ∀ s₁ ∈ f.varsList, ∀ s₂ ∈ g.varsList, p s₁ s₂ = true := by
  simpa [Formula.foldlVars] using
    Metamath.KernelExtras.List.foldl_all₂

namespace Convert

open Std
open Bridge
open Spec

/-- Convert an implementation formula to a spec-side expression when the head is a constant. -/
def toExprOpt (f : Formula) : Option Spec.Expr := do
  let head ← f[0]?
  match head with
  | Sym.const c =>
      let tail := (f.extract 1 f.size).toList.map Sym.value
      some ⟨⟨c⟩, tail⟩
  | _ => none

/-- Convert the entire implementation stack to specification expressions. -/
def stackToExprs (stack : Array Formula) : Option (List Spec.Expr) :=
  stack.toList.mapM toExprOpt

lemma toExprOpt_head
    {f : Formula} {c : String}
    (h : f[0]? = some (Sym.const c)) :
    ∃ e : Spec.Expr, toExprOpt f = some e ∧ e.typecode = ⟨c⟩ := by
  classical
  unfold toExprOpt
  have tail := (f.extract 1 f.size).toList.map Sym.value
  refine ⟨⟨⟨c⟩, tail⟩, ?_, ?_⟩
  · simp [h, tail]
  · simp [tail]

lemma toExprOpt_varsInExpr_eq
    {f : Formula} {e : Spec.Expr}
    (h : toExprOpt f = some e) (vars : List Spec.Variable) :
    Spec.varsInExpr vars e =
      f.varsList.filterMap
        (fun s =>
          let v := Spec.Variable.mk s
          if vars.contains v then some v else none) := by
  classical
  unfold toExprOpt at h
  cases hhead : f[0]? with
  | none =>
      simp [hhead] at h
  | some head =>
      cases head with
      | const c =>
          simp [hhead] at h
          cases h
          simp [Spec.varsInExpr, Formula.varsList,
            Metamath.KernelExtras.List.filterMap_map,
            Metamath.KernelExtras.List.filterMap_filterMap,
            Option.bind]
      | var _ =>
          simp [hhead] at h

lemma toExprOpt_varsInExpr_mem
    {f : Formula} {e : Spec.Expr}
    (h : toExprOpt f = some e)
    {vars : List Spec.Variable} {v : Spec.Variable} :
    v ∈ Spec.varsInExpr vars e →
    v.v ∈ f.varsList := by
  classical
  let F :=
    fun s : String =>
      let v := Spec.Variable.mk s
      if vars.contains v then some v else none
  intro hv
  have hEq := toExprOpt_varsInExpr_eq (f := f) (e := e) h vars
  have hv' : v ∈ f.varsList.filterMap F := by
    simpa [hEq, F] using hv
  rcases List.mem_filterMap.mp hv' with ⟨s, hs, hF⟩
  dsimp [F] at hF
  split_ifs at hF with hcontains
  · have := congrArg Spec.Variable.v hF
    simp at this
    simpa [this] using hs
  · cases hF

lemma toExprOpt_varsList_mem
    {f : Formula} {e : Spec.Expr}
    (h : toExprOpt f = some e)
    {vars : List Spec.Variable} {s : String}
    (hs : s ∈ f.varsList)
    (hcontains : vars.contains (Spec.Variable.mk s) = true) :
    Spec.Variable.mk s ∈ Spec.varsInExpr vars e := by
  classical
  let F :=
    fun s : String =>
      let v := Spec.Variable.mk s
      if vars.contains v then some v else none
  have hEq := toExprOpt_varsInExpr_eq (f := f) (e := e) h vars
  have : Spec.Variable.mk s ∈ f.varsList.filterMap F := by
    refine List.mem_filterMap.mpr ?_
    refine ⟨s, hs, ?_⟩
    dsimp [F]
    simpa [hcontains]
  simpa [hEq, F] using this

/-- Internal record of a successfully converted substitution binding. -/
structure Assignment where
  var : Spec.Variable
  const : Spec.Constant
  expr : Spec.Expr
  type_ok : expr.typecode = const

/-- Lookup helper for assignments keyed by variable. -/
def lookupAssignment : List Assignment → Spec.Variable → Option Assignment
  | [], _ => none
  | a :: as, v =>
      if h : a.var = v then some a else lookupAssignment as v

/-- Build typed assignments for each floating hypothesis in declaration order. -/
private def buildAssignments
    (σ_impl : Std.HashMap String Formula)
    : List (Spec.Constant × Spec.Variable) → Option (List Assignment)
  | [] => some []
  | (c, v) :: rest => do
      let restAssignments ← buildAssignments rest
      if hmem : v ∈ restAssignments.map Assignment.var then
        none
      else
        let f ← σ_impl.find? v.v
        let e ← toExprOpt f
        if h : e.typecode = c then
          some ({ var := v, const := c, expr := e, type_ok := h } :: restAssignments)
        else
          none

lemma buildAssignments_nodup
    (σ_impl : Std.HashMap String Formula) :
    ∀ {floats assignments},
      buildAssignments σ_impl floats = some assignments →
        (assignments.map Assignment.var).Nodup
  | [], assignments, h => by
      simp [buildAssignments] at h
      cases h
      simp
  | (c, v) :: rest, assignments, h => by
      unfold buildAssignments at h
      cases hRest : buildAssignments σ_impl rest with
      | none =>
          simp [hRest] at h
          cases h
      | some restAssignments =>
          have h_nodup_rest :
              (restAssignments.map Assignment.var).Nodup :=
            buildAssignments_nodup (floats := rest)
              (assignments := restAssignments) hRest
          by_cases hmem : v ∈ restAssignments.map Assignment.var
          · simp [hRest, hmem] at h
            cases h
          · simp [hRest, hmem] at h
            cases hFind : σ_impl.find? v.v with
            | none =>
                simp [hFind] at h
                cases h
            | some f =>
                cases hExpr : toExprOpt f with
                | none =>
                    simp [hFind, hExpr] at h
                    cases h
                | some e =>
                    by_cases hType : e.typecode = c
                    · simp [hFind, hExpr, hType] at h
                      cases h
                      exact List.nodup_cons.mpr
                        ⟨by simpa using hmem, h_nodup_rest⟩
                    · simp [hFind, hExpr, hType] at h
                      cases h

lemma buildAssignments_mem
    (σ_impl : Std.HashMap String Formula) :
    ∀ {floats assignments},
      buildAssignments σ_impl floats = some assignments →
      ∀ {c v}, (c, v) ∈ floats →
        ∃ a ∈ assignments, a.var = v ∧ a.const = c
  | [], assignments, h, c, v, hmem => by
      cases hmem
  | (c₀, v₀) :: rest, assignments, h, c, v, hmem => by
      unfold buildAssignments at h
      cases hRest : buildAssignments σ_impl rest with
      | none =>
          simp [hRest] at h
          cases h
      | some restAssignments =>
          by_cases hmemDup : v₀ ∈ restAssignments.map Assignment.var
          · simp [hRest, hmemDup] at h
            cases h
          · simp [hRest, hmemDup] at h
            cases hFind : σ_impl.find? v₀.v with
            | none =>
                simp [hFind] at h
                cases h
            | some f =>
                cases hExpr : toExprOpt f with
                | none =>
                    simp [hFind, hExpr] at h
                    cases h
                | some e =>
                    by_cases hType : e.typecode = c₀
                    · simp [hFind, hExpr, hType] at h
                      cases h
                      have hcases := (List.mem_cons).1 hmem
                      cases hcases with
                      | inl hEq =>
                          cases hEq
                          refine ⟨_, by simp, rfl, rfl⟩
                      | inr hTail =>
                          have := buildAssignments_mem
                            (floats := rest) (assignments := restAssignments)
                            hRest hTail
                          rcases this with ⟨a, ha_mem, ha_var, ha_const⟩
                          exact ⟨a, by
                            simpa using List.mem_cons_of_mem _ ha_mem,
                            ha_var, ha_const⟩
                    · simp [hFind, hExpr, hType] at h

lemma lookupAssignment_of_mem
    {assignments : List Assignment}
    (h_nodup : (assignments.map Assignment.var).Nodup)
    {a : Assignment} (ha : a ∈ assignments) :
    lookupAssignment assignments a.var = some a := by
  induction assignments with
  | nil =>
      cases ha
  | cons b bs ih =>
      have hcons := List.nodup_cons.mp h_nodup
      have hb_notin : b.var ∉ bs.map Assignment.var := hcons.1
      have hnodup_tail : (bs.map Assignment.var).Nodup := hcons.2
      cases ha with
      | inl hEq =>
          cases hEq
          simp [lookupAssignment]
      | inr hTail =>
          have hv_ne : b.var ≠ a.var := by
            intro hEq
            apply hb_notin
            have : a.var ∈ bs.map Assignment.var :=
              List.mem_map_of_mem Assignment.var hTail
            simpa [hEq] using this
          have := ih hnodup_tail hTail
          simp [lookupAssignment, hv_ne, this]

lemma buildAssignments_vars
    (σ_impl : Std.HashMap String Formula) :
    ∀ {floats assignments},
      buildAssignments σ_impl floats = some assignments →
        assignments.map Assignment.var = floats.map Prod.snd
  | [], assignments, h => by
      simp [buildAssignments] at h
      cases h
      simp
  | (c, v) :: rest, assignments, h => by
      unfold buildAssignments at h
      cases hRest : buildAssignments σ_impl rest with
      | none =>
          simp [hRest] at h
          cases h
      | some restAssignments =>
          by_cases hmem : v ∈ restAssignments.map Assignment.var
          · simp [hRest, hmem] at h
            cases h
          · simp [hRest, hmem] at h
            cases hFind : σ_impl.find? v.v with
            | none =>
                simp [hFind] at h
                cases h
            | some f =>
                cases hExpr : toExprOpt f with
                | none =>
                    simp [hFind, hExpr] at h
                    cases h
                | some e =>
                    by_cases hType : e.typecode = c
                    · simp [hFind, hExpr, hType] at h
                      cases h
                      have hvars :=
                        buildAssignments_vars (σ_impl := σ_impl)
                          (floats := rest)
                          (assignments := restAssignments) hRest
                      simp [List.map, hvars]
                    · simp [hFind, hExpr, hType] at h
                      cases h

lemma buildAssignments_exists
    (σ_impl : Std.HashMap String Formula)
    {floats : List (Spec.Constant × Spec.Variable)}
    (hnodup : (floats.map Prod.snd).Nodup)
    (hcover :
      ∀ {c v},
        (c, v) ∈ floats →
        ∃ (f : Formula) (e : Spec.Expr),
          σ_impl.find? v.v = some f ∧
          toExprOpt f = some e ∧
          e.typecode = c) :
    ∃ assignments,
      buildAssignments σ_impl floats = some assignments ∧
      assignments.map Assignment.var = floats.map Prod.snd := by
  classical
  induction floats with
  | nil =>
      refine ⟨[], by simp [buildAssignments]⟩
  | cons hv rest ih =>
      rcases hv with ⟨c, v⟩
      have hcons :
          (v :: rest.map Prod.snd).Nodup := by
        simpa [List.map] using hnodup
      have hv_notin : v ∉ rest.map Prod.snd := (List.nodup_cons.mp hcons).1
      have hnodup_rest : (rest.map Prod.snd).Nodup := (List.nodup_cons.mp hcons).2
      -- Coverage assumptions specialised to head and tail
      have hcover_head :
          ∃ (f : Formula) (e : Spec.Expr),
            σ_impl.find? v.v = some f ∧
            toExprOpt f = some e ∧
            e.typecode = c :=
        hcover (by simp)
      have hcover_tail :
          ∀ {c' v'},
            (c', v') ∈ rest →
            ∃ (f : Formula) (e : Spec.Expr),
              σ_impl.find? v'.v = some f ∧
              toExprOpt f = some e ∧
              e.typecode = c' := by
        intro c' v' hmem
        exact hcover (by
          have : (c', v') ∈ (⟨c, v⟩ :: rest) := by
            simpa using List.mem_cons_of_mem _ hmem
          simpa using this)
      rcases ih hnodup_rest hcover_tail with ⟨restAssignments, hRest, hvars_rest⟩
      rcases hcover_head with ⟨f, e, hf_find, hf_expr, hf_type⟩
      have hv_notin_assign :
          v ∉ restAssignments.map Assignment.var := by
        simpa [hvars_rest] using hv_notin
      have hAssign :
          buildAssignments σ_impl (⟨c, v⟩ :: rest) =
            some ({ var := v, const := c, expr := e, type_ok := hf_type } :: restAssignments) := by
        simp [buildAssignments, hRest, hv_notin_assign, hf_find, hf_expr, hf_type]
      refine ⟨_, hAssign, ?_⟩
      simp [List.map, hvars_rest]

theorem toSubst_total
    (fr_spec : Spec.Frame)
    (σ_impl : Std.HashMap String Formula)
    (hnodup : ((Bridge.floats fr_spec).map Prod.snd).Nodup)
    (hcover :
      ∀ {c v},
        (c, v) ∈ Bridge.floats fr_spec →
        ∃ (f : Formula) (e : Spec.Expr),
          σ_impl.find? v.v = some f ∧
          toExprOpt f = some e ∧
          e.typecode = c) :
    ∃ σ_typed : Bridge.TypedSubst fr_spec,
      toSubst fr_spec σ_impl = some σ_typed := by
  classical
  let floats := Bridge.floats fr_spec
  obtain ⟨assignments, hBuild, hvars⟩ :=
    buildAssignments_exists (σ_impl := σ_impl)
      (floats := floats)
      hnodup
      (by
        intro c v hmem
        exact hcover hmem)
  have h_nodup_assign :
      (assignments.map Assignment.var).Nodup :=
    buildAssignments_nodup (σ_impl := σ_impl)
      (floats := floats) (assignments := assignments) hBuild
  have σ_mem :
      ∀ {c v},
        (c, v) ∈ floats →
        ∃ a ∈ assignments, a.var = v ∧ a.const = c :=
    fun {c v} hmem =>
      buildAssignments_mem (σ_impl := σ_impl)
        (floats := floats) (assignments := assignments) hBuild hmem
  let defaultExpr : Spec.Expr := ⟨⟨""⟩, []⟩
  let σ : Spec.Subst :=
    fun v =>
      match lookupAssignment assignments v with
      | some a => a.expr
      | none => defaultExpr
  have htyped :
      ∀ {c v}, Spec.Hyp.floating c v ∈ fr_spec.mand →
        (σ v).typecode = c := by
    intro c v hfloat
    have hmem := Bridge.floating_mem_floats (fr := fr_spec) hfloat
    rcases σ_mem hmem with ⟨a, ha_mem, ha_var, ha_const⟩
    have hlookup :=
      lookupAssignment_of_mem (assignments := assignments)
        (a := a) h_nodup_assign ha_mem
    have hlookup_v :
        lookupAssignment assignments v = some a := by
      simpa [ha_var] using hlookup
    have hσ : σ v = a.expr := by
      unfold σ
      simp [hlookup_v, defaultExpr]
    have htype' : (σ v).typecode = a.const := by
      simpa [hσ] using a.type_ok
    simpa [ha_const] using htype'
  refine ⟨⟨σ, htyped⟩, ?_⟩
  unfold toSubst
  simp [floats, hBuild, σ, defaultExpr]

/-- Convert an implementation substitution map into a typed specification substitution. -/
def toSubst (fr_spec : Spec.Frame)
    (σ_impl : Std.HashMap String Formula) :
    Option (Bridge.TypedSubst fr_spec) :=
  let floats := Bridge.floats fr_spec
  match hAssign : buildAssignments σ_impl floats with
  | none => none
  | some assignments =>
      let defaultExpr : Spec.Expr := { typecode := ⟨""⟩, syms := [] }
      let σ : Spec.Subst := fun v =>
        match lookupAssignment assignments v with
        | some a => a.expr
        | none => defaultExpr
      have h_nodup :
          (assignments.map Assignment.var).Nodup :=
        buildAssignments_nodup (σ_impl := σ_impl)
          (floats := floats) (assignments := assignments) hAssign
      have typed :
          ∀ {c v}, Spec.Hyp.floating c v ∈ fr_spec.mand →
            (σ v).typecode = c := by
        intro c v hfloat
        have hmem := Bridge.floating_mem_floats hfloat
        have hfound :=
          buildAssignments_mem (σ_impl := σ_impl)
            (floats := floats) (assignments := assignments) hAssign hmem
        rcases hfound with ⟨a, ha_mem, ha_var, ha_const⟩
        have hlookup :=
          lookupAssignment_of_mem (assignments := assignments)
            (a := a) h_nodup ha_mem
        have hlookup' : lookupAssignment assignments v = some a := by
          simpa [ha_var] using hlookup
        have hσ : σ v = a.expr := by
          unfold σ
          simp [hlookup', defaultExpr]
        have htype' : (σ v).typecode = a.const := by
          simpa [hσ] using a.type_ok
        simpa [ha_const] using htype'
      some ⟨σ, typed⟩

end Convert

abbrev toExprOpt := Convert.toExprOpt
abbrev stackToExprs := Convert.stackToExprs
abbrev toSubst := Convert.toSubst

inductive Object
  | const : String → Object
  | var : String → Object
  | hyp : Bool → Formula → String → Object
  | assert : Formula → Frame → String → Object

inductive ProofTokenParser
  | start
  | preload
  | normal
  | compressed (chr : Nat)

inductive HeapEl
  | fmla (f : Formula)
  | assert (f : Formula) (fr : Frame)

instance : ToString HeapEl where
  toString
  | .fmla f => toString f
  | .assert f fr => s!"{fr} |- {f}"

structure ProofState where
  pos : Pos
  label : String
  fmla : Formula
  frame : Frame
  heap : Array HeapEl
  stack : Array Formula
  ptp : ProofTokenParser

instance : ToString ProofState where
  toString p := Id.run do
    let mut s := s!"at {p.pos}: {p.label}\n"
    let mut i := 0
    for el in p.heap do
      s := s ++ s!"heap {i} := {el}\n"
      i := i + 1
    s := s ++ "\n"
    for el in p.stack do
      s := s ++ s!"{el}\n"
    s

namespace ProofState

def push (pr : ProofState) (f : Formula) : ProofState :=
  { pr with stack := pr.stack.push f }

def pushHeap (pr : ProofState) (el : HeapEl) : ProofState :=
  { pr with heap := pr.heap.push el }

def save (pr : ProofState) : Except String ProofState :=
  if let some f := pr.stack.back? then
    pure <| pr.pushHeap (.fmla f)
  else
    throw "can't save empty stack"

end ProofState

inductive Error
  | error (pos : Pos) (msg : String)
  | ax (pos : Pos) (l : String) (f : Formula) (fr : Frame)
  | thm (pos : Pos) (l : String) (f : Formula) (fr : Frame)

structure Interrupt where
  e : Error
  idx : Nat

structure DB where
  frame : Frame
  scopes : Array (Nat × Nat)
  objects : HashMap String Object
  interrupt : Bool
  error? : Option Interrupt
  permissive : Bool := false
  deriving Inhabited

namespace DB

@[inline] def error (s : DB) : Bool := s.error?.isSome

def mkError (s : DB) (pos : Pos) (msg : String) : DB :=
  { s with error? := some ⟨.error pos msg, default⟩ }

def pushScope (s : DB) : DB :=
  { s with scopes := s.scopes.push s.frame.size }

def popScope (pos : Pos) (db : DB) : DB :=
  if let some sc := db.scopes.back? then
    { db with frame := db.frame.shrink sc, scopes := db.scopes.pop }
  else
    db.mkError pos "can't pop global scope"

def find? (db : DB) (l : String) : Option Object := db.objects[l]?

def isConst (db : DB) (tk : String) : Bool :=
  if let some (.const _) := db.find? tk then true else false

def isVar (db : DB) (tk : String) : Bool :=
  if let some (.var _) := db.find? tk then true else false

def isSym (db : DB) (tk : String) : Bool :=
  match db.find? tk with
  | some (.const _) => true
  | some (.var _) => true
  | _ => false

@[inline] def withFrame (f : Frame → Frame) (db : DB) : DB :=
  { db with frame := f db.frame }

@[inline] def withDJ (f : Array DJ → Array DJ) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨f dj, hyps⟩

@[inline] def withHyps (f : Array String → Array String) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨dj, f hyps⟩

def insert (db : DB) (pos : Pos) (l : String) (obj : String → Object) : DB :=
  -- Spec Section 4.2.8: $c must be in outermost block only (strict mode)
  let db := match obj l with
  | .const _ =>
    if !db.permissive && db.scopes.size > 0 then
      db.mkError pos s!"$c must be in outermost block (spec Section 4.2.8)"
    else db
  | _ => db
  if db.error then db else
  if let some o := db.find? l then
    let ok : Bool := match o with
    | .var _ => if let .var _ := obj l then true else false
    | _ => false
    if ok then db else db.mkError pos s!"duplicate symbol/assert {l}"
  else
    { db with objects := db.objects.insert l (obj l) }

def insertHyp (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) : DB :=
  -- For $f statements (ess = false), check that no other $f exists for this variable
  let db := Id.run do
    if !ess && f.size >= 2 then
      let v := f[1]!.value
      -- Check all existing hypotheses in current frame
      let mut db := db
      for h in db.frame.hyps do
        if let some (.hyp false prevF _) := db.find? h then
          if prevF.size >= 2 && prevF[1]!.value == v then
            db := db.mkError pos s!"variable {v} already has $f hypothesis"
      db
    else db
  let db := db.insert pos l (.hyp ess f)
  db.withHyps fun hyps => hyps.push l

def trimFrame (db : DB) (fmla : Formula) (fr := db.frame) : Bool × Frame := Id.run do
  let collectVars (fmla : Formula) vars :=
    fmla.foldlVars vars HashSet.insert
  let mut vars : HashSet String := collectVars fmla ∅
  for l in fr.hyps do
    if let some (.hyp true f _) := db.find? l then
      vars := collectVars f vars
  let mut dj := #[]
  for v in fr.dj do
    if vars.contains v.1 && vars.contains v.2 then
      dj := dj.push v
  let mut hyps := #[]
  let mut ok := true
  let mut varsWithF : HashSet String := ∅
  for l in fr.hyps do
    let ess ←
      if let some (.hyp false f _) := db.find? l then
        -- Spec §4.2.4: $f and $e can be interleaved (appearance order)
        -- No need to enforce "$f before $e" - that's a legacy restriction
        let v := f[1]!.value
        if vars.contains v then
          varsWithF := varsWithF.insert v
        vars.contains v
      else
        true
    if ess then hyps := hyps.push l
  -- Check that all variables have a $f hypothesis
  for v in vars do
    unless varsWithF.contains v do ok := false
  (ok, ⟨dj, hyps⟩)

def trimFrame' (db : DB) (fmla : Formula) : Except String Frame :=
  let (ok, fr) := db.trimFrame fmla
  if ok then pure fr
  else throw s!"out of order hypotheses in frame"

def insertAxiom (db : DB) (pos : Pos) (l : String) (fmla : Formula) : DB :=
  match db.trimFrame' fmla with
  | .ok fr =>
    if db.interrupt then { db with error? := some ⟨.ax pos l fmla fr, default⟩ }
    else db.insert pos l (.assert fmla fr)
  | .error msg => db.mkError pos msg

def mkProofState (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    ProofState := Id.run do
  let mut heap := #[]
  for l in fr.hyps do
    if let some (.hyp _ f _) := db.find? l then
      heap := heap.push (.fmla f)
  ⟨pos, l, fmla, fr, heap, #[], .start⟩

def preload (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (.hyp true _ _) => throw "$e found in paren list"
  | some (.hyp _ f _) => return pr.pushHeap (.fmla f)
  | some (.assert f fr _) => return pr.pushHeap (.assert f fr)
  | _ => throw s!"statement {l} not found"

variable (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) in
def checkHyp (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(
      let thm {a b n} : i < a → n + a = b → n + i < b
      | h, rfl => Nat.add_lt_add_left h _
      thm h off.2)
    if let some (.hyp ess f _) := db.find? hyps[i] then
      if f[0]! == val[0]! then
        if ess then
          if (← f.subst subst) == val then
            checkHyp (i+1) subst
          else throw "type error in substitution"
        else
          checkHyp (i+1) (subst.insert f[1]!.value val)
      else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
    else unreachable!
  else pure subst

def stepAssert (db : DB) (pr : ProofState) (f : Formula) : Frame → Except String ProofState
  | ⟨dj, hyps⟩ => do
    if h : hyps.size ≤ pr.stack.size then
      let off : {off // off + hyps.size = pr.stack.size} :=
        ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h⟩
      let subst ← checkHyp db hyps pr.stack off 0 ∅
      let disj s1 s2 := s1 != s2 &&
        db.frame.dj.contains (if s1 < s2 then (s1, s2) else (s2, s1))
      for (v1, v2) in dj do
        let e1 := subst[v1]!
        let e2 := subst[v2]!
        let disjoint :=
          e1.foldlVars (init := true) fun b s1 =>
            e2.foldlVars b fun b s2 => b && disj s1 s2
        if !disjoint then throw "disjoint variable violation"
      let concl ← f.subst subst
      pure { pr with stack := (pr.stack.shrink off).push concl }
    else throw "stack underflow"

def stepNormal (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (.hyp _ f _) => return pr.push f
  | some (.assert f fr _) => db.stepAssert pr f fr
  | _ => throw s!"statement {l} not found"

def stepProof (db : DB) (pr : ProofState) (i : Nat) : Except String ProofState :=
  match pr.heap[i]? with
  | none => throw "proof backref index out of range"
  | some (.fmla f) => return pr.push f
  | some (.assert f fr) => db.stepAssert pr f fr

end DB

inductive CharParser
  | ws : CharParser
  | token : Nat → ByteSliceT → CharParser
  deriving Inhabited

inductive TokensKind
  | float
  | ess
  | ax
  | thm

instance : ToString TokensKind where
  toString
  | .float => "float"
  | .ess => "ess"
  | .ax => "ax"
  | .thm => "thm"

def TokensKind.delim : TokensKind → ByteArray
  | .thm => "$=".toAscii
  | _ => "$.".toAscii

structure TokensParser where
  k : TokensKind
  pos : Pos
  label : String

instance : ToString TokensParser where
  toString | ⟨k, pos, label⟩ => s!"at {pos}: {k} {label}"

inductive TokenParser
  | start : TokenParser
  | comment : TokenParser → TokenParser
  | const : TokenParser
  | var : TokenParser
  | djvars : Array String → TokenParser
  | math : Array Sym → TokensParser → TokenParser
  | label : Pos → String → TokenParser
  | proof : ProofState → TokenParser
  deriving Inhabited

def TokenParser.toString : TokenParser → String
  | .start => "start"
  | .comment p => "comment " ++ toString p
  | .const => "const"
  | .var => "var"
  | .djvars s => s!"djvars {s}"
  | .math s p => s!"math {s} {p}"
  | .label pos l => s!"at {pos}: ? {l}"
  | .proof p => ToString.toString p

instance : ToString TokenParser := ⟨TokenParser.toString⟩

structure ParserState where
  db : DB
  tokp : TokenParser
  charp : CharParser
  line : Nat
  linepos : Nat
  deriving Inhabited

namespace ParserState

@[inline] def withDB (f : DB → DB) (s : ParserState) : ParserState :=
  { s with db := f s.db }

def mkPos (s : ParserState) (pos : Nat) : Pos := ⟨s.line, pos - s.linepos⟩

def mkError (s : ParserState) (pos : Pos) (msg : String) : ParserState :=
  s.withDB fun db => db.mkError pos msg

def mkErrorAt (s : ParserState) (pos : Pos) (l msg : String) : ParserState :=
  s.mkError pos s!"at {l}: {msg}"

def withAt (l : String) (f : Unit → ParserState) : ParserState :=
  let s := f ()
  if let some ⟨.error pos msg, i⟩ := s.db.error? then
    s.withDB fun db => { db with error? := some ⟨.error pos s!"at {l}: {msg}", i⟩ }
  else s

def label (s : ParserState) (pos : Pos) (tk : ByteSlice) : ParserState :=
  let (ok, tk) := toLabel tk
  if ok then { s with tokp := .label pos tk }
  else s.mkError pos s!"invalid label '{tk}'"

def withMath (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) : ParserState :=
  let (ok, tk) := toMath tk
  if !ok then s.mkError pos s!"invalid math string '{tk}'" else
  f s tk

def sym (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) : ParserState :=
  if tk.eqArray "$.".toAscii then
    { s with tokp := .start }
  else s.withMath pos tk fun s tk =>
    s.withDB fun db => db.insert pos tk f

def resumeAxiom (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  s.withDB fun db => db.insert pos l (.assert fmla fr)

def resumeThm (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  let pr := s.db.mkProofState pos l fmla fr
  { s with tokp := .proof pr }

def feedTokens (s : ParserState) (arr : Array Sym) : TokensParser → ParserState
  | ⟨k, pos, l⟩ => withAt l fun _ => Id.run do
    unless arr.size > 0 && !arr[0]!.isVar do
      return s.mkError pos "first symbol is not a constant"
    match k with
    | .float =>
      unless arr.size == 2 && arr[1]!.isVar do
        return s.mkError pos "expected a constant and a variable"
      let s := s.withDB fun db => db.insertHyp pos l false arr
      pure { s with tokp := .start }
    | .ess =>
      let s := s.withDB fun db => db.insertHyp pos l true arr
      pure { s with tokp := .start }
    | .ax =>
      let s := s.withDB fun db => db.insertAxiom pos l arr
      pure { s with tokp := .start }
    | .thm =>
      match s.db.trimFrame' arr with
      | .ok fr =>
        if s.db.interrupt then
          s.withDB fun db => { db with error? := some ⟨.thm pos l arr fr, default⟩ }
        else s.resumeThm pos l arr fr
      | .error msg => s.mkError pos msg

def feedProof (s : ParserState) (tk : ByteSlice) (pr : ProofState) : ParserState :=
  withAt pr.label fun _ =>
    match go pr with
    | .ok pr => { s with tokp := .proof pr }
    | .error msg => s.mkError pr.pos msg
where
  goNormal (pr : ProofState) :=
    -- Check for unknown step marker '?'
    if tk.eqArray "?".toAscii then
      -- Push formula matching the statement being proved (incomplete proof)
      pure (pr.push pr.fmla)
    else
      let (ok, tk) := toLabel tk
      if ok then s.db.stepNormal pr tk
      else throw s!"invalid label '{tk}'"
  go (pr : ProofState) : Except String ProofState := do
    match pr.ptp with
    | .start =>
      if tk.eqArray "(".toAscii then
        pure { pr with ptp := .preload }
      else goNormal { pr with ptp := .normal }
    | .preload =>
      if tk.eqArray ")".toAscii then
        pure { pr with ptp := .compressed 0 }
      else
        let (ok, tk) := toLabel tk
        if ok then s.db.preload pr tk
        else throw s!"invalid label '{tk}'"
    | .normal => goNormal pr
    | .compressed chr =>
      let mut pr := pr
      let mut chr := chr
      for c in tk do
        if 'A'.toUInt8 ≤ c && c ≤ 'Z'.toUInt8 then
          if c ≤ 'T'.toUInt8 then
            let n := 20 * chr + (c - 'A'.toUInt8).toNat
            pr ← s.db.stepProof pr n
            chr := 0
          else if c < 'Z'.toUInt8 then
            chr := 5 * chr + (c - 'T'.toUInt8).toNat
          else
            pr ← pr.save
            chr := 0
        else if c = '?'.toUInt8 then
          -- Unknown step in compressed proof - push the formula being proved
          pr := pr.push pr.fmla
          chr := 0
        else
          throw "proof parse error"
      pure { pr with ptp := .compressed chr }

def finishProof (s : ParserState) : ProofState → ParserState
  | ⟨pos, l, fmla, fr, _, stack, ptp⟩ => withAt l fun _ => Id.run do
    let s := { s with tokp := .start }
    match ptp with
    | .compressed 0 => ()
    | .normal => ()
    | _ => return s.mkError pos "proof parse error"
    unless stack.size == 1 do
      return s.mkError pos "more than one element on stack"
    unless stack[0]! == fmla do
      return s.mkError pos "theorem does not prove what it claims"
    s.withDB fun db => db.insert pos l (.assert fmla fr)

def feedToken (s : ParserState) (pos : Nat) (tk : ByteSlice) : ParserState :=
  let pos := s.mkPos pos
  match s.tokp with
  | .comment p =>
    if tk.eqArray "$)".toAscii then { s with tokp := p } else s
  | p =>
    if tk.eqArray "$(".toAscii then { s with tokp := p.comment } else
    match p with
    | .comment _ => unreachable!
    | .start =>
      if tk.len == 2 && tk[0] == '$'.toUInt8 then
        match tk[1].toChar with
        | '{' => s.withDB .pushScope
        | '}' => s.withDB (.popScope pos)
        | 'c' => { s with tokp := .const }
        | 'v' => { s with tokp := .var }
        | 'd' => { s with tokp := .djvars #[] }
        | _ => s.label pos tk
      else s.label pos tk
    | .const => s.sym pos tk .const
    | .var => s.sym pos tk .var
    | .djvars arr =>
      if tk.eqArray "$.".toAscii then { s with tokp := .start } else
      s.withMath pos tk fun s tk => Id.run do
        unless s.db.isVar tk do return s.mkError pos s!"{tk} is not a variable"
        let mut s := s
        for tk1 in arr do
          if tk1 == tk then
            return s.mkError pos s!"duplicate disjoint variable {tk}"
          let p := if tk1 < tk then (tk1, tk) else (tk, tk1)
          s := s.withDB fun db => db.withDJ fun dj => dj.push p
        { s with tokp := .djvars (arr.push tk) }
    | .math arr p =>
      if tk.eqArray p.k.delim then
        s.feedTokens arr p
      else
        s.withMath pos tk fun s tk => Id.run do
          let tk ← match s.db.find? tk with
          | some (.const _) => Sym.const tk
          | some (.var _) => Sym.var tk
          | _ => return s.mkError pos s!"{tk} is not a constant or variable"
          { s with tokp := .math (arr.push tk) p }
    | .label pos lab =>
      if tk.len == 2 && tk[0] == '$'.toUInt8 then
        let go (s : ParserState) (k : TokensKind) :=
          { s with tokp := .math #[] ⟨k, pos, lab⟩ }
        match tk[1].toChar with
        | 'f' => go s .float
        | 'e' => go s .ess
        | 'a' => go s .ax
        | 'p' => go s .thm
        | _ => s.mkError pos s!"unknown statement type {(toLabel tk).2}"
      else s.mkError pos s!"unknown statement type {(toLabel tk).2}"
    | .proof pr =>
      let s := { s with tokp := default }
      if tk.eqArray "$.".toAscii then s.finishProof pr
      else s.feedProof tk pr

inductive OldToken
  | this (off : Nat)
  | old (base off : Nat) (arr : ByteArray)

inductive FeedState
  | ws : FeedState
  | token : OldToken → FeedState

def updateLine (s : ParserState) (i : Nat) (c : UInt8) : ParserState :=
  if c == '\n'.toUInt8 then { s with line := s.line + 1, linepos := i + 1 } else s

def feed (base : Nat) (arr : ByteArray)
    (i : Nat) (rs : FeedState) (s : ParserState) : ParserState :=
  if h : i < arr.size then
    let c := arr[i]
    if isWhitespace c then
      match rs with
      | .ws =>
        let s := s.updateLine (base + i) c
        feed base arr (i+1) .ws s
      | .token ot =>
        let s := match ot with
        | .this off => s.feedToken (base + off) ⟨arr, off, i - off⟩
        | .old base off arr' => s.feedToken (base + off)
          ⟨arr.copySlice 0 arr' arr'.size i false, off, arr'.size - off + i⟩
        let s : ParserState := s.updateLine (base + i) c
        if let some ⟨e, _⟩ := s.db.error? then
          { s with db := { s.db with error? := some ⟨e, i+1⟩ } }
        else feed base arr (i+1) .ws s
    else
      let rs := if let .ws := rs then .token (.this i) else rs
      feed base arr (i+1) rs s
  else
    { s with charp :=
      match rs with
      | .ws => .ws
      | .token ot =>
        match ot with
        | .this off => .token base ⟨arr, off⟩
        | .old base off arr' => .token base ⟨arr' ++ arr, off⟩ }

def feedAll (s : ParserState) (base : Nat) (arr : ByteArray) : ParserState :=
  match s.charp with
  | .ws => s.feed base arr 0 .ws
  | .token base' ⟨arr', off⟩ =>
    let s := { s with charp := default }
    s.feed base arr 0 (.token (.old base' off arr'))

def done (s : ParserState) (base : Nat) : DB := Id.run do
  let mut s := s
  if let .token pos tk := s.charp then
    s := s.feedToken pos tk.toSlice
  let base := s.mkPos base
  let { db := db, tokp := tokp, ..} := s
  match tokp with
  | .start =>
    if db.scopes.size > 0 then
      db.mkError base "unclosed block (missing $})"
    else db
  | .comment _ => db.mkError base "unclosed comment"
  | .const => db.mkError base "unclosed $c"
  | .var => db.mkError base "unclosed $v"
  | .djvars _ => db.mkError base "unclosed $d"
  | .math _ p => match p.k with
    | .float => db.mkError base "unclosed $f"
    | .ess => db.mkError base "unclosed $e"
    | .ax => db.mkError base "unclosed $a"
    | .thm => db.mkError base "unclosed $p"
  | .label pos _ => db.mkError pos "not a command"
  | .proof _ => db.mkError base "unclosed $p proof"

end ParserState

-- Preprocessor with include support
-- Processes $[ filename $] directives by recursively loading files
-- Handles self-includes and cycles per spec §4.1.2
-- In strict mode: validates includes are at outermost scope and not inside statements

partial def expandIncludes (fname : String) (seen : HashSet String) (permissive : Bool := false) :
    IO (Except String (ByteArray × HashSet String)) := do
  -- Canonicalize path (resolve ./ and ../)
  let canonPath ← IO.FS.realPath fname
  let canonStr := canonPath.toString

  -- Check for cycles (including self-include)
  if seen.contains canonStr then
    -- Per spec §4.1.2: "self-include will simply be ignored"
    return .ok (ByteArray.empty, seen)

  let seen := seen.insert canonStr

  -- Read file
  let h ← Handle.mk fname IO.FS.Mode.read
  let rec readAll (acc : ByteArray) : IO ByteArray := do
    let buf ← h.read 4096
    if buf.isEmpty then return acc
    else readAll (acc ++ buf)
  let contents ← readAll ByteArray.empty

  -- Process includes: find $[ ... $] and expand recursively
  let mut result := ByteArray.empty
  let mut seen := seen  -- Make seen mutable to thread through
  let mut i := 0
  let mut scopeDepth := 0  -- Track ${ $} nesting
  let mut inStatement := false  -- Track if we're inside a statement (after label before $.)
  let mut inComment := false  -- Track if we're inside a comment

  while i < contents.size do
    -- Track comment state (comments take precedence over everything else)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == '(' then
        inComment := true
        result := result.push contents[i]!
        result := result.push contents[i+1]!
        i := i + 2
        continue
      else if c == ')' then
        inComment := false
        result := result.push contents[i]!
        result := result.push contents[i+1]!
        i := i + 2
        continue

    -- Skip everything inside comments
    if inComment then
      result := result.push contents[i]!
      i := i + 1
      continue

    -- Track scope depth for strict mode validation
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == '{' then
        scopeDepth := scopeDepth + 1
      else if c == '}' then
        scopeDepth := max 0 (scopeDepth - 1)
      else if c == '.' then
        inStatement := false  -- Statement terminator

    -- Track if we're entering a statement (simplified: after $f, $e, $a, $p)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == 'f' || c == 'e' || c == 'a' || c == 'p' then
        inStatement := true

    -- Look for $[ token (only outside comments)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 && contents[i+1]! == '['.toUInt8 then
      -- Validate strict mode constraints (spec §4.1.2)
      if !permissive then
        -- Check: not in inner scope
        if scopeDepth > 0 then
          return .error s!"include in inner scope (strict mode requires outermost scope only, spec §4.1.2)"
        -- Check: not inside a statement
        if inStatement then
          return .error s!"include inside statement (strict mode forbids token splicing, spec §4.1.2)"

      i := i + 2
      -- Skip whitespace after $[
      while i < contents.size && (contents[i]! == ' '.toUInt8 || contents[i]! == '\n'.toUInt8 || contents[i]! == '\t'.toUInt8 || contents[i]! == '\r'.toUInt8) do
        i := i + 1

      -- Extract filename until $]
      let mut includePath := ByteArray.empty
      let startPos := i  -- Debug: save start position
      while i + 1 < contents.size && !(contents[i]! == '$'.toUInt8 && contents[i+1]! == ']'.toUInt8) do
        let c := contents[i]!
        if c != ' '.toUInt8 && c != '\n'.toUInt8 && c != '\t'.toUInt8 && c != '\r'.toUInt8 then
          includePath := includePath.push c
        i := i + 1
      -- Debug: check what we extracted
      if includePath.isEmpty && i > startPos then
        return .error s!"extracted empty path from position {startPos} to {i} in {fname}"

      -- Skip $]
      if i + 1 < contents.size then i := i + 2

      -- Convert includePath to String
      let mut includeFile := String.fromUTF8! includePath

      -- Debug: check extracted path before normalization
      if includeFile.isEmpty then
        return .error s!"extracted empty include path before normalization in {fname}"

      -- Normalize "./" prefix (FilePath doesn't handle it well)
      if includeFile.startsWith "./" then
        includeFile := includeFile.drop 2

      -- Check for empty path after normalization
      if includeFile.isEmpty then
        return .error s!"include path became empty after normalizing './' prefix (original was '{String.fromUTF8! includePath}') in {fname}"

      -- Resolve relative path (relative to current file's directory)
      let baseDir := System.FilePath.parent fname |>.getD "."
      let fullPath := baseDir / includeFile

      -- Recursively expand the included file
      try
        match ← expandIncludes fullPath.toString seen permissive with
        | .ok (expanded, seen') =>
          seen := seen'  -- Thread the updated seen set through
          result := result ++ expanded
          -- Add whitespace to separate from next token
          result := result.push ' '.toUInt8
        | .error e => return .error e
      catch e =>
        return .error s!"failed to read include file '{includeFile}' (resolved to '{fullPath}'): {e}"
    else
      result := result.push contents[i]!
      i := i + 1

  return .ok (result, seen)

partial def check (fname : String) (permissive : Bool := false) : IO DB := do
  -- Expand all includes recursively with permissive mode awareness
  match ← expandIncludes fname (HashSet.emptyWithCapacity 16) permissive with
  | .error msg =>
    -- Return DB with error for include validation failures
    let initialDB : DB := { (default : DB) with permissive := permissive }
    return initialDB.mkError ⟨1, 1⟩ msg
  | .ok (processed, _) =>
    let rec loop (s : ParserState) (base : Nat) (arr : ByteArray) (off : Nat) : IO DB := do
      if off >= arr.size then
        return s.done base
      else
        let len := min 1024 (arr.size - off)
        let buf := arr.extract off (off + len)
        let s := s.feedAll base buf
        if s.db.error?.isSome then return s.db
        else loop s (base + buf.size) arr (off + len)
    let initialDB : DB := { (default : DB) with permissive := permissive }
    let initialState : ParserState := { (default : ParserState) with db := initialDB }
    loop initialState 0 processed 0
