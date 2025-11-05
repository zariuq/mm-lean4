import Metamath.Spec

namespace Metamath
namespace Bridge

open Spec

/-- The expression required by a single mandatory hypothesis, under σ. -/
def needOf (vars : List Spec.Variable)
    (σ : Spec.Subst) : Spec.Hyp → Spec.Expr
  | .floating _ v => σ v
  | .essential e => Spec.applySubst vars σ e

/-- The ordered list of mandatory hypothesis images for a frame and substitution. -/
def needed (vars : List Spec.Variable)
    (fr : Spec.Frame) (σ : Spec.Subst) : List Spec.Expr :=
  fr.mand.map (needOf vars σ)

/-- Floating hypotheses of a frame, in declaration order. -/
def floats (fr : Spec.Frame) : List (Spec.Constant × Spec.Variable) :=
  fr.mand.foldr
    (fun h acc =>
      match h with
      | .floating c v => (c, v) :: acc
      | .essential _ => acc)
    []

/-- Essential hypotheses of a frame, in declaration order. -/
def essentials (fr : Spec.Frame) : List Spec.Expr :=
  fr.mand.foldr
    (fun h acc =>
      match h with
      | .floating _ _ => acc
      | .essential e => e :: acc)
    []

/-- Witness-carrying substitution respecting floating hypothesis types. -/
structure TypedSubst (fr : Spec.Frame) where
  σ : Spec.Subst
  typed :
    ∀ {c v}, Spec.Hyp.floating c v ∈ fr.mand →
      (σ v).typecode = c

theorem floating_mem_floats_list :
    ∀ {hyps : List Spec.Hyp} {c : Spec.Constant} {v : Spec.Variable},
      Spec.Hyp.floating c v ∈ hyps →
      (c, v) ∈ hyps.foldr
        (fun h acc =>
          match h with
          | Spec.Hyp.floating c' v' => (c', v') :: acc
          | Spec.Hyp.essential _ => acc)
        []
  | [], _, _, h => by cases h
  | Spec.Hyp.floating c' v' :: hyps, c, v, h => by
      have hcases := (List.mem_cons).1 h
      simp [List.foldr]
      cases hcases with
      | inl hEq =>
          cases hEq
          simp
      | inr hTail =>
          exact Or.inr (floating_mem_floats_list (hyps := hyps) hTail)
  | Spec.Hyp.essential _ :: hyps, c, v, h => by
      have hTail : Spec.Hyp.floating c v ∈ hyps := by
        have hcases := (List.mem_cons).1 h
        cases hcases with
        | inl hEq =>
            cases hEq
        | inr hTail => exact hTail
      simpa [List.foldr] using
        floating_mem_floats_list (hyps := hyps) hTail

/-- Every floating hypothesis in `fr.mand` appears in `Bridge.floats fr`. -/
theorem floating_mem_floats
    {fr : Spec.Frame} {c : Spec.Constant} {v : Spec.Variable}
    (h : Spec.Hyp.floating c v ∈ fr.mand) :
    (c, v) ∈ floats fr := by
  simpa [floats] using
    floating_mem_floats_list
      (hyps := fr.mand) (c := c) (v := v) h

/-- The variable projection of `floats` agrees with the frame's floating variables. -/
theorem floats_map_snd (fr : Spec.Frame) :
    (floats fr).map Prod.snd =
      fr.mand.filterMap (fun h => match h with
        | Spec.Hyp.floating _ v => some v
        | Spec.Hyp.essential _ => none) := by
  unfold floats
  induction fr.mand with
  | nil => simp
  | cons h hs ih =>
      cases h with
      | floating c v =>
          simp [List.foldr, ih]
      | essential _ =>
          simp [List.foldr, ih]

/-- Auxiliary lemma: membership in the folded list implies membership
    in the source hypothesis list. -/
theorem floats_list_mem :
    ∀ {hyps : List Spec.Hyp} {c : Spec.Constant} {v : Spec.Variable},
      (c, v) ∈ hyps.foldr
        (fun h acc =>
          match h with
          | Spec.Hyp.floating c v => (c, v) :: acc
          | Spec.Hyp.essential _ => acc)
        [] →
      Spec.Hyp.floating c v ∈ hyps
  | [], _, _, h => by
      simpa using h
  | Spec.Hyp.floating c' v' :: hyps, c, v, h => by
      have hcases :
          c = c' ∧ v = v' ∨
            (c, v) ∈ hyps.foldr
              (fun h acc =>
                match h with
                | Spec.Hyp.floating c v => (c, v) :: acc
                | Spec.Hyp.essential _ => acc)
              [] := by
        simpa [List.foldr] using h
      cases hcases with
      | inl hEq =>
          rcases hEq with ⟨rfl, rfl⟩
          simp
      | inr hTail =>
          have := floats_list_mem (hyps := hyps) (c := c) (v := v) hTail
          exact List.mem_cons_of_mem _ this
  | Spec.Hyp.essential _ :: hyps, c, v, h => by
      simp [List.foldr] at h
      have := floats_list_mem (hyps := hyps) (c := c) (v := v) h
      exact List.mem_cons_of_mem _ this

/-- Each element of `Bridge.floats` originates from a floating hypothesis in the frame. -/
theorem floats_mem_floating
    {fr : Spec.Frame} {c : Spec.Constant} {v : Spec.Variable}
    (h : (c, v) ∈ floats fr) :
    Spec.Hyp.floating c v ∈ fr.mand := by
  unfold floats at h
  simpa using floats_list_mem (hyps := fr.mand) (c := c) (v := v) h

end Bridge
end Metamath
