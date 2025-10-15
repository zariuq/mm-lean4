-- Test file to verify our new Kernel lemmas compile independently
import Metamath.Spec
import Metamath.Verify
import Metamath.Bridge

open Metamath.Spec
open Metamath.Verify
open Metamath.Bridge

-- Test toExpr bridge lemmas
lemma toExpr_success (f : Formula) :
    (Metamath.Kernel.toExpr f).isSome ↔ f.size > 0 := by
  unfold Metamath.Kernel.toExpr
  split
  · next h => simp
  · next h => simp

lemma toExpr_typecode (f : Formula) (e : Expr) :
    Metamath.Kernel.toExpr f = some e → e.typecode = ⟨f[0].value⟩ := by
  intro h
  unfold Metamath.Kernel.toExpr at h
  split at h
  · next h_size => simp at h; cases h; rfl
  · contradiction

lemma toExpr_none_iff (f : Formula) :
    Metamath.Kernel.toExpr f = none ↔ f.size = 0 := by
  unfold Metamath.Kernel.toExpr
  split
  · next h => simp; omega
  · next h => simp; omega

-- Test Array ↔ List bridge lemmas
lemma Array.size_toList {α : Type _} (arr : Array α) :
    arr.toList.length = arr.size := by
  simp [Array.toList]

lemma Array.forall_iff_toList {α : Type _} (arr : Array α) (P : α → Prop) :
    (∀ i < arr.size, P arr[i]) ↔ (∀ x ∈ arr.toList, P x) := by
  constructor
  · intro h_forall x h_mem
    have ⟨i, h_i_lt, h_eq⟩ := List.mem_iff_get.mp h_mem
    rw [Array.toList_eq] at h_eq
    simp at h_eq
    rw [←h_eq]
    exact h_forall i h_i_lt
  · intro h_forall i h_i_lt
    apply h_forall
    have : arr[i] ∈ arr.toList := by
      rw [List.mem_iff_get]
      exists i
      constructor
      · simp [Array.toList]; exact h_i_lt
      · simp [Array.toList_eq]
    exact this

lemma Array.get_toList_eq {α : Type _} (arr : Array α) (i : Nat) (h : i < arr.size) :
    arr.toList[i]'(by simp [Array.toList]; exact h) = arr[i] := by
  simp [Array.toList_eq]

-- Test checkFloat definition
def checkFloat (σ_impl : Std.HashMap String Formula)
    (float : Constant × Variable) : Option Bool :=
  let (tc, v) := float
  match σ_impl[v.v.drop 1]? with
  | some f =>
      match Metamath.Kernel.toExpr f with
      | some e => if e.typecode = tc then some true else some false
      | none => none
  | none => none

-- Test extract_from_allM_true lemma
lemma extract_from_allM_true (floats : List (Constant × Variable))
    (σ_impl : Std.HashMap String Formula)
    (hAll : floats.allM (checkFloat σ_impl) = some true)
    (c : Constant) (v : Variable)
    (h_in : (c, v) ∈ floats) :
    ∃ (f : Formula) (e : Expr),
      σ_impl[v.v.drop 1]? = some f ∧
      Metamath.Kernel.toExpr f = some e ∧
      e.typecode = c := by
  induction floats with
  | nil => contradiction
  | cons hd tl ih =>
      unfold List.allM at hAll
      simp [pure, Bind.bind] at hAll
      split at hAll
      · contradiction
      · next h_check_hd =>
          split at hAll
          · contradiction
          · next h_b_true =>
              cases h_in with
              | head h_eq =>
                  have h_check_cv : checkFloat σ_impl (c, v) = some true := by
                    rw [←h_eq]; exact h_check_hd
                  unfold checkFloat at h_check_cv
                  split at h_check_cv
                  · contradiction
                  · next f h_lookup =>
                      split at h_check_cv
                      · contradiction
                      · next e h_conv =>
                          split at h_check_cv
                          · contradiction
                          · next h_tc => exact ⟨f, e, h_lookup, h_conv, h_tc⟩
              | tail h_mem_tl => exact ih hAll h_mem_tl

#check extract_from_allM_true
#check toExpr_success
#check toExpr_typecode
#check Array.forall_iff_toList
