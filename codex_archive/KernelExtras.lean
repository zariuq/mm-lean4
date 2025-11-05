import Metamath.Spec
import Std

namespace Metamath.Kernel

open Metamath.Spec

/-- Update a substitution at a single variable. -/
def Subst.update (σ : Subst) (v : Variable) (e : Expr) : Subst :=
  fun w => if w = v then e else σ w

@[simp] lemma update_hits (σ : Subst) (v : Variable) (e : Expr) :
  (Subst.update σ v e) v = e := by simp [Subst.update]

@[simp] lemma update_agrees_off (σ : Subst) (v : Variable) (e : Expr)
  {w : Variable} (hne : w ≠ v) :
  (Subst.update σ v e) w = σ w := by simp [Subst.update, hne]

/-- “σ is identity on S”. Replace RHS with your dedicated `Expr.var` if available. -/
def Subst.IdOn (σ : Subst) (S : List Variable) : Prop :=
  ∀ v, v ∈ S → σ v = ⟨(σ v).typecode, [v.v]⟩

/-- If σ₂ is identity on all vars of `e`, then applying σ₂ after σ₁ is a no-op on `e`. -/
theorem applySubst_id_on
  (vars : List Variable) (σ₁ σ₂ : Subst) (e : Expr)
  (hId : Subst.IdOn σ₂ (varsInExpr vars (applySubst vars σ₁ e))) :
  applySubst vars σ₂ (applySubst vars σ₁ e) = applySubst vars σ₁ e := by
  -- Placeholder; prove by recursion on `e.syms` using `hId` on variable symbols.
  sorry

/-- Sufficient condition to carry DV through σ₂ ∘ σ₁: σ₂ is identity on
    all variables that appear in images of σ₁ on the DV set. -/
theorem dvOK_comp_sufficient
  (vars : List Variable)
  (dv   : List (Variable × Variable))
  (σ₁ σ₂ : Subst)
  (h₁ : dvOK vars dv σ₁)
  (hId : Subst.IdOn σ₂
          (List.join (dv.map (fun (v,w) =>
             varsInExpr vars (σ₁ v) ++ varsInExpr vars (σ₁ w))))) :
  dvOK vars dv (fun v => applySubst vars σ₂ (σ₁ v)) := by
  -- Placeholder; unfold `dvOK` and use `applySubst_id_on` to preserve disjointness.
  sorry

/-- Generic helper: `filterMap` preserves `Nodup`. -/
lemma filterMap_preserves_nodup {α β}
  (f : α → Option β) : ∀ {xs : List α}, xs.Nodup → (xs.filterMap f).Nodup
  | [], _ => by simpa
  | x::xs, h => by
      have h' : xs.Nodup := (List.nodup_cons.mp h).2
      have IH := filterMap_preserves_nodup f (xs := xs) h'
      cases hx : f x with
      | none => simpa [List.filterMap, hx] using IH
      | some y =>
          -- Placeholder; show `y ∉ xs.filterMap f` using `xs.Nodup` and a local inversion
          have : y ∉ xs.filterMap f := by
            sorry
          exact List.nodup_cons.mpr ⟨this, by simpa [List.filterMap, hx] using IH⟩

end Metamath.Kernel

namespace Metamath.Kernel

open Metamath.Spec

/-- Variable.mk is injective on strings. -/
lemma variable_mk_injective {a b : String} : Variable.mk a = Variable.mk b → a = b := by
  intro h; cases h; rfl

/-- If `xs` is Nodup and `f` is injective on the elements of `xs`, then `xs.map f` is Nodup. -/
lemma nodup_map_of_injective {α β} (xs : List α) (f : α → β)
  (hnd : xs.Nodup)
  (hinj : ∀ {a b}, a ∈ xs → b ∈ xs → f a = f b → a = b) :
  (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      have hcons := List.nodup_cons.mp hnd
      have h_notin : ∀ {b}, b ∈ as → a ≠ b := by
        intro b hb; exact (hcons.1) (by simpa [hb] using hb)
      have ih' : (as.map f).Nodup := ih hcons.2
      -- Show f a ∉ as.map f
      have hfa_notin : f a ∉ as.map f := by
        intro hmem
        -- ∃ b ∈ as, f b = f a
        rcases List.exists_of_mem_map hmem with ⟨b, hb, hb_eq⟩
        have : b = a := hinj (by simp) (by simpa [hb]) (hb_eq.symm)
        have : False := by exact (hcons.1) (by simpa [this] using hb)
        exact this.elim
      exact List.nodup_cons.mpr ⟨hfa_notin, ih'⟩

end Metamath.Kernel

-- Generic List fusion lemma used to avoid index-preservation proofs
namespace List
open Option

lemma filterMap_after_mapM_eq {α β γ}
  (f : α → Option β) (p : β → Option γ) :
  ∀ {xs ys}, mapM f xs = some ys → ys.filterMap p = xs.filterMap (fun x => bind (f x) p)
| [], [], h => by simpa using h
| x::xs, ys, h => by
  cases hfx : f x with
  | none =>
      simp [List.mapM, hfx] at h
  | some y =>
      cases htail : mapM f xs with
      | none => simp [List.mapM, hfx, htail] at h
      | some ys' =>
          have hcons : ys = y :: ys' := by simpa [List.mapM, hfx, htail] using h
          subst hcons
          have IH := (filterMap_after_mapM_eq (xs:=xs) (ys:=ys') htail)
          cases hp : p y with
          | none => simp [hp, IH, List.mapM, hfx, htail]
          | some z => simp [hp, IH, List.mapM, hfx, htail]

end List

/-! ### Additional small utilities used by Verify.Proofs -/

namespace Metamath.KernelExtras

open Std

/-- From xs.mapM f = some ys, extract the i-th success witness. -/
theorem mapM_index_some {α β} (f : α → Option β)
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys)
    (i : Nat) (hi : i < xs.length) :
    ∃ (y : β), f (xs.get ⟨i, hi⟩) = some y := by
  revert ys
  revert i
  induction xs with
  | nil =>
      intro i hi ys
      exact (Nat.not_lt_zero _ hi).elim
  | cons x xs ih =>
      intro i hi ys
      simp [List.mapM] at h
      cases hfx : f x with
      | none =>
          simp [List.mapM, hfx] at h
      | some y0 =>
          cases hxs : xs.mapM f with
          | none =>
              simp [List.mapM, hfx, hxs] at h
          | some ys' =>
              have hcons : ys = y0 :: ys' := by
                simpa [List.mapM, hfx, hxs] using h
              subst hcons
              cases i with
              | zero =>
                  refine ⟨y0, ?_⟩
                  simpa using hfx
              | succ i' =>
                  have hi' : i' < xs.length := by
                    have : Nat.succ i' < (List.length xs).succ := by
                      simpa [List.length] using hi
                    exact Nat.succ_lt_succ_iff.mp this
                  have htail :=
                    ih (i := i') (hi := hi') (ys := ys') hxs
                  rcases htail with ⟨y, hy⟩
                  refine ⟨y, ?_⟩
                  simp [List.get] at hy ⊢
                  exact hy

lemma mapM_mem {α β} (f : α → Option β)
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) :
    ∀ {y}, y ∈ ys → ∃ x ∈ xs, f x = some y := by
  revert ys
  induction xs with
  | nil =>
      intro ys h y hy
      simp at h
      subst h
      simpa using hy
  | cons x xs ih =>
      intro ys
      simp [List.mapM] at h
      cases hfx : f x with
      | none =>
          simp [List.mapM, hfx] at h
      | some y0 =>
          cases hxs : xs.mapM f with
          | none =>
              simp [List.mapM, hfx, hxs] at h
          | some ys' =>
              have hcons : ys = y0 :: ys' := by
                simpa [List.mapM, hfx, hxs] using h
              subst hcons
              intro y hy
              simp at hy
              cases hy with
              | inl hy0 =>
                  subst hy0
                  exact ⟨x, by simp [hfx], rfl⟩
              | inr hyTail =>
                  obtain ⟨x', hx', hf⟩ := ih hxs hyTail
                  exact ⟨x', by simp [hx'], hf⟩

/-- Length preservation for `List.mapM` into `Option`. -/
lemma mapM_length {α β} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by
      simp [List.mapM] at h
      cases h
      simp
  | x :: xs, ys, h => by
      simp [List.mapM] at h
      cases hfx : f x with
      | none =>
          simp [List.mapM, hfx] at h
      | some y =>
          cases hxs : xs.mapM f with
          | none =>
              simp [List.mapM, hfx, hxs] at h
          | some ys' =>
              have hcons : ys = y :: ys' := by
                simpa [List.mapM, hfx, hxs] using h
              subst hcons
              have hlen_tail :=
                mapM_length (f := f) (xs := xs) (ys := ys') hxs
              simp [hlen_tail, List.length]

/-- Indexed lookup for `mapM`: retrieve the exact image at position `i`. -/
lemma mapM_index_get {α β} (f : α → Option β)
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys)
    (i : Nat) (hi : i < xs.length) :
    f (xs.get ⟨i, hi⟩) =
      some (ys.get ⟨i, by
        have hlen := mapM_length (f := f) (xs := xs) (ys := ys) h
        simpa [hlen] using hi⟩) := by
  revert ys
  revert i
  induction xs with
  | nil =>
      intro i hi ys
      exact (Nat.not_lt_zero _ hi).elim
  | cons x xs ih =>
      intro i hi ys
      simp [List.mapM] at h
      cases hfx : f x with
      | none =>
          simp [List.mapM, hfx] at h
      | some y =>
          cases hxs : xs.mapM f with
          | none =>
              simp [List.mapM, hfx, hxs] at h
          | some ys' =>
              have hcons : ys = y :: ys' := by
                simpa [List.mapM, hfx, hxs] using h
              subst hcons
              cases i with
              | zero =>
                  simp [List.get, hfx]
              | succ i' =>
                  have hi_tail : i' < xs.length := by
                    have : Nat.succ i' < xs.length.succ := by
                      simpa [List.length] using hi
                    exact Nat.succ_lt_succ_iff.mp this
                  have := ih (i := i') (hi := hi_tail) (ys := ys') hxs
                  simp [List.get, hfx] at this
                  exact this

namespace List

lemma foldl_and_eq_true {xs : List α} {p : α → Bool} :
    xs.foldl (fun b x => b && p x) true = true ↔
      ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa [List.foldl, ih, Bool.and_eq_true, and_left_comm, and_assoc]

lemma foldl_all₂ {xs : List α} {ys : List β} {p : α → β → Bool} :
    xs.foldl
        (fun b x => ys.foldl (fun b' y => b' && p x y) b)
        true = true ↔
      (∀ x ∈ xs, ∀ y ∈ ys, p x y = true) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl, ih, foldl_and_eq_true, Bool.and_eq_true, and_left_comm, and_assoc]

lemma foldl_and_with_init {xs : List α} {p : α → Bool} :
    xs.foldl (fun acc x => acc && p x) b =
      (xs.foldl (fun acc x => acc && p x) true) && b := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl, ih, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

lemma foldl_filterMap_eq {xs : List α} (g : α → Option β) (f : β → γ → β)
    (init : β) :
    xs.foldl (fun acc a => match g a with
      | some b => f acc b
      | none => acc) init =
      (xs.filterMap g).foldl f init := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases h : g x with
      | none =>
      simp [List.foldl, h, ih]
      | some b =>
          simp [List.foldl, h, ih]

lemma filterMap_map {xs : List α} (g : α → β) (h : β → Option γ) :
    (xs.map g).filterMap h =
      xs.filterMap fun x => h (g x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.map, List.filterMap, ih]

lemma filterMap_filterMap {xs : List α} (g : α → Option β) (h : β → Option γ) :
    (xs.filterMap g).filterMap h =
      xs.filterMap fun x => Option.bind (g x) h := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hg : g x with
      | none =>
          simp [List.filterMap, hg, ih]
      | some y =>
          simp [List.filterMap, hg, ih]

end List

section HashMap
variable {α β : Type} [BEq α] [Hashable α] [Std.EquivBEq α] [Std.LawfulHashable α]

@[simp] lemma contains_insert_self (m : Std.HashMap α β) (a : α) (b : β) :
  (m.insert a b).contains a = true := by
  have h := Std.HashMap.contains_insert_self (m := m) (k := a) (v := b)
  simpa using h

lemma contains_mono_insert {m : Std.HashMap α β} {a k : α} {b : β} :
  m.contains a = true → (m.insert k b).contains a = true := by
  intro h
  have hcontains := Std.HashMap.contains_insert (m := m) (k := k) (a := a) (v := b)
  cases hk : k == a with
  | false =>
      have hvalue : (k == a || m.contains a) = true := by
        simp [hk, h]
      have : (m.insert k b).contains a = true := by
        calc
          (m.insert k b).contains a
              = (k == a || m.contains a) := hcontains
          _ = true := hvalue
      simpa using this
  | true =>
      have hvalue : (k == a || m.contains a) = true := by simp [hk]
      have : (m.insert k b).contains a = true := by
        calc
          (m.insert k b).contains a
              = (k == a || m.contains a) := hcontains
          _ = true := hvalue
      simpa using this

end HashMap

end Metamath.KernelExtras
