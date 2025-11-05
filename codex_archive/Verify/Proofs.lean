import Metamath.Verify
import Metamath.KernelExtras

namespace Metamath
namespace Verify
namespace Proofs

open Verify
open Metamath.KernelExtras

private theorem list_mapM_length_option {α β : Type}
    (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by
      simp [List.mapM] at h
      cases h
      rfl
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
              simp [List.mapM, hfx, hxs] at h
              cases h
              have h_len := list_mapM_length_option (f := f) (xs := xs) (ys := ys') hxs
              simp [h_len]

/-! ### Binding witnesses produced by `checkHyp` -/

section

variable {db : DB} {hyps : Array String} {stack : Array Formula}
variable {off : { off : Nat // off + hyps.size = stack.size }}

/-- Witness data recording exactly how a floating hypothesis contributed
    the mapping `v ↦ val` in the substitution. -/
structure FloatBindWitness
    (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : { off // off + hyps.size = stack.size })
    (j : Nat) (v : String) (val : Formula) : Prop where
  hj     : j < hyps.size
  k      : Fin stack.size
  hk     : off.1 + j = k.val
  f      : Formula
  lbl    : String
  find   : db.find? hyps[j] = some (.hyp false f lbl)
  var    : f[1]!.value = v
  val_eq : val = stack[k]!
  head   : (f[0]! == val[0]!) = true

private def HypBinding (j : Nat) (v : String) (val : Formula) : Prop :=
  FloatBindWitness db hyps stack off j v val

/-- Invariant on a substitution produced while scanning the first `n`
    hypotheses: every key has a floating-hyp witness with index `< n`. -/
private def HypProp (n : Nat) (σ : Std.HashMap String Formula) : Prop :=
  ∀ v val, σ[v]? = some val →
    ∃ j, j < n ∧ HypBinding (db := db) (hyps := hyps) (stack := stack) (off := off) j v val

lemma HypProp.mono {m n : Nat} {σ : Std.HashMap String Formula}
    (h : n ≤ m) : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) n σ →
    HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) m σ := by
  intro hprop v val hfind
  obtain ⟨j, hj, hbind⟩ := hprop v val hfind
  exact ⟨j, Nat.lt_of_lt_of_le hj h, hbind⟩

lemma HypProp.empty : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) 0 (∅ : Std.HashMap String Formula) := by
  intro v val hfind
  simp at hfind

lemma HypProp.insert_floating
    {i : Nat} {σ : Std.HashMap String Formula}
    {f : Formula} {lbl : String} {val : Formula}
    (hbind : HypBinding (db := db) (hyps := hyps) (stack := stack) (off := off) i (f[1]!.value) val)
    (hprop : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) i σ) :
    HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) (i + 1)
      (σ.insert (f[1]!.value) val) := by
  intro v val' hfind
  by_cases hv : v = f[1]!.value
  · subst hv
    have : (σ.insert (f[1]!.value) val)[f[1]!.value]? = some val := by
      simpa using (Std.HashMap.getElem?_insert_self (m := σ) (k := f[1]!.value) (v := val))
    have hval : val' = val := Option.some.inj <| hfind.trans this.symm
    cases' hbind with hj k hk f₀ lbl₀ find var val_eq head
    refine ⟨i, Nat.lt_succ_self i, ?_⟩
    refine FloatBindWitness.mk (db := db) (hyps := hyps) (stack := stack) (off := off)
      (j := i) (v := f[1]!.value) (val := val') ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa using hj
    · exact k
    · simpa using hk
    · exact f₀
    · exact lbl₀
    · simpa using find
    · simpa using var
    · simpa [hval] using val_eq
    · simpa using head
  · have hlookup :
      (σ.insert (f[1]!.value) val)[v]? = σ[v]? := by
        have := Std.HashMap.getElem?_insert (m := σ) (k := f[1]!.value) (a := v) (v := val)
        have hkFalse : (f[1]!.value == v) = false := by
          by_cases hk : f[1]!.value == v
          · have hk_eq : f[1]!.value = v := eq_of_beq hk
            exact False.elim (hv hk_eq.symm)
          · simpa [hk]
        simpa [hkFalse] using this
    have hσ : σ[v]? = some val' := by simpa [hlookup] using hfind
    obtain ⟨j, hj, hbind'⟩ := hprop v val' hσ
    refine ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i), hbind'⟩

lemma checkHyp_preserves_HypProp
    {i : Nat} {subst σ : Std.HashMap String Formula}
    (hi : i ≤ hyps.size)
    (hprop : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) i subst)
    (hrun : DB.checkHyp db hyps stack off i subst = .ok σ) :
    HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) hyps.size σ := by
  classical
  have main :
      ∀ (k : Nat) {i : Nat} {subst σ : Std.HashMap String Formula},
        hyps.size - i = k →
        i ≤ hyps.size →
        HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) i subst →
        DB.checkHyp db hyps stack off i subst = .ok σ →
        HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) hyps.size σ := by
    intro k
    induction k with
    | zero =>
        intro i subst σ hk hi hprop hrun
        have hi_ge : hyps.size ≤ i := Nat.sub_eq_zero_iff_le.mp hk
        have hi_eq : i = hyps.size := Nat.le_antisymm hi hi_ge
        subst hi_eq
        have hsubst : σ = subst := by
          simpa [DB.checkHyp] using hrun
        subst hsubst
        simpa using hprop
    | succ k ih =>
        intro i subst σ hk hi hprop hrun
        have hi_lt : i < hyps.size := by
          have hsum : i + (hyps.size - i) = hyps.size := Nat.add_sub_of_le hi
          have hsum' := by simpa [hk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            Nat.succ_eq_add_one] using hsum
          have : i < (i + 1) + k := by
            have : 0 < (k + 1) := Nat.succ_pos _
            have := Nat.lt_add_of_pos_right i this
            simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
          simpa [hsum'] using this
        have hlt_stack : off.1 + i < stack.size := by
          have := Nat.add_lt_add_left hi_lt off.1
          simpa [off.2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
        have hk_succ : hyps.size - (i + 1) = k := by
          have hsum : hyps.size = k + (i + 1) := by
            have hsum₀ : hyps.size = i + Nat.succ k := by
              have := Nat.add_sub_of_le hi
              simpa [hk] using this.symm
            simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum₀
          exact Nat.sub_eq_of_eq_add hsum
        have hi_succ : i + 1 ≤ hyps.size := Nat.succ_le_of_lt hi_lt
        have hrun' :=
          by
            have := hrun
            simpa [DB.checkHyp, hi_lt] using this
        -- Analyse the object retrieved from the database.
        cases hobj : db.find? hyps[i] with
        | none =>
            simp [hobj] at hrun'
        | some obj =>
            cases obj with
            | const _ =>
                simp [hobj] at hrun'
            | var _ =>
                simp [hobj] at hrun'
            | assert _ _ _ =>
                simp [hobj] at hrun'
            | hyp ess f lbl =>
                -- set the stack value used for this hypothesis
                set val := stack[off.1 + i]'hlt_stack with hval
                have hrun'' : 
                    if f[0]! == val[0]! then
                      if ess then
                        let x := do
                          let expected ← f.subst subst
                          if expected == val then
                            DB.checkHyp db hyps stack off (i + 1) subst
                          else Except.error "type error in substitution"
                        x
                      else
                        DB.checkHyp db hyps stack off (i + 1)
                          (subst.insert f[1]!.value val)
                    else
                      Except.error s!"bad typecode in substitution {hyps[i]}: {f} / {val}" =
                    .ok σ := by
                  simpa [hobj, DB.checkHyp, hi_lt, hval] using hrun'
                -- typecode comparison must succeed
                cases htc : (f[0]! == val[0]!) with
                | false =>
                    simp [htc] at hrun''
                    cases hrun''
                | true =>
                    -- handle essential vs floating cases
                    cases ess with
                    | true =>
                        -- run the substitution and equality check
                        cases hsubst : f.subst subst with
                        | error err =>
                            simpa [htc, hsubst] using hrun''
                        | ok expected =>
                            cases heq : (expected == val) with
                            | false =>
                                simpa [htc, hsubst, heq] using hrun''
                            | true =>
                                have hrun_next :
                                  DB.checkHyp db hyps stack off (i + 1) subst = .ok σ := by
                                    simpa [htc, hsubst, heq] using hrun''
                                have hprop_succ :
                                  HypProp (db := db) (hyps := hyps) (stack := stack) (off := off)
                                    (i + 1) subst :=
                                  HypProp.mono
                                    (db := db) (hyps := hyps) (stack := stack) (off := off)
                                    (h := Nat.le_succ i) hprop
                                exact ih hk_succ hi_succ hprop_succ hrun_next
                | false =>
                    -- floating hypothesis inserts a binding
                    have hrun_next :
                      DB.checkHyp db hyps stack off (i + 1)
                        (subst.insert f[1]!.value val) = .ok σ := by
                            simpa [htc] using hrun''
                    have hbind :
                      HypBinding (db := db) (hyps := hyps) (stack := stack) (off := off)
                        i (f[1]!.value) val :=
                    by
                      refine FloatBindWitness.mk (db := db) (hyps := hyps) (stack := stack) (off := off)
                        (j := i) (v := f[1]!.value) (val := val)
                        ?hj ?k ?hk ?f ?lbl ?find ?var ?valeq ?head
                      · exact hi_lt
                      · exact ⟨off.1 + i, hlt_stack⟩
                      · rfl
                      · exact f
                      · exact lbl
                      · simpa using hobj
                      · rfl
                      ·
                        have : stack[⟨off.1 + i, hlt_stack⟩]! = stack[off.1 + i]'hlt_stack := rfl
                        simpa [this]
                      · exact htc
                    have hprop_succ :
                      HypProp (db := db) (hyps := hyps) (stack := stack) (off := off)
                        (i + 1) (subst.insert f[1]!.value val) :=
                      HypProp.insert_floating (db := db) (hyps := hyps) (stack := stack)
                        (off := off) hbind hprop
                        exact ih hk_succ hi_succ hprop_succ hrun_next
  end
  have := main (hyps.size - i) (i := i) (subst := subst) (σ := σ) rfl hi hprop hrun
  simpa using this

lemma checkHyp_contains_mono
    {i : Nat} {subst σ : Std.HashMap String Formula}
    (hi : i ≤ hyps.size)
    (hrun : DB.checkHyp db hyps stack off i subst = .ok σ) :
    ∀ v, subst.contains v = true → σ.contains v = true := by
  classical
  have main :
      ∀ (k : Nat) {i : Nat} {subst σ : Std.HashMap String Formula},
        hyps.size - i = k →
        i ≤ hyps.size →
        DB.checkHyp db hyps stack off i subst = .ok σ →
        ∀ v, subst.contains v = true → σ.contains v = true := by
    intro k
    induction k with
    | zero =>
        intro i subst σ hk hi hrun v hv
        have hi_ge : hyps.size ≤ i := Nat.sub_eq_zero_iff_le.mp hk
        have hi_eq : i = hyps.size := Nat.le_antisymm hi hi_ge
        subst hi_eq
        have hσ : σ = subst := by simpa [DB.checkHyp] using hrun
        subst hσ
        simpa using hv
    | succ k ih =>
        intro i subst σ hk hi hrun v hv
        have hi_lt : i < hyps.size := by
          have hsum : i + (hyps.size - i) = hyps.size := Nat.add_sub_of_le hi
          have hsum' := by simpa [hk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            Nat.succ_eq_add_one] using hsum
          have : i < (i + 1) + k := by
            have : 0 < k + 1 := Nat.succ_pos _
            have := Nat.lt_add_of_pos_right i this
            simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
          simpa [hsum'] using this
        have hrun' :=
          by
            have := hrun
            simpa [DB.checkHyp, hi_lt] using this
        have hk_succ : hyps.size - (i + 1) = k := by
          have hsum : hyps.size = k + (i + 1) := by
            have hsum₀ : hyps.size = i + Nat.succ k := by
              have := Nat.add_sub_of_le hi
              simpa [hk] using this.symm
            simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum₀
          exact Nat.sub_eq_of_eq_add hsum
        have hi_succ : i + 1 ≤ hyps.size := Nat.succ_le_of_lt hi_lt
        cases hobj : db.find? hyps[i] with
        | none =>
            simp [hobj] at hrun'
        | some obj =>
            cases obj with
            | const _ =>
                simp [hobj] at hrun'
            | var _ =>
                simp [hobj] at hrun'
            | assert _ _ _ =>
                simp [hobj] at hrun'
            | hyp ess f lbl =>
                set val := stack[off.1 + i]'(
                  (by
                    have := Nat.add_lt_add_left hi_lt off.1
                    simpa [off.2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this))
                  with hval
                have hrun'' :
                    if f[0]! == val[0]! then
                      if ess then
                        let x := do
                          let expected ← f.subst subst
                          if expected == val then
                            DB.checkHyp db hyps stack off (i + 1) subst
                          else Except.error "type error in substitution"
                        x
                      else
                        DB.checkHyp db hyps stack off (i + 1)
                          (subst.insert f[1]!.value val)
                    else
                      Except.error s!"bad typecode in substitution {hyps[i]}: {f} / {val}" =
                    .ok σ := by
                  simpa [hobj, DB.checkHyp, hi_lt, hval] using hrun'
                cases htc : (f[0]! == val[0]!) with
                | false =>
                    simp [htc] at hrun''
                    cases hrun''
                | true =>
                    cases ess with
                    | true =>
                    cases hsubst : f.subst subst with
                    | error err =>
                        simpa [htc, hsubst] using hrun''
                    | ok expected =>
                        cases heq : (expected == val) with
                        | false =>
                            simpa [htc, hsubst, heq] using hrun''
                        | true =>
                            have hrun_next :
                              DB.checkHyp db hyps stack off (i + 1) subst = .ok σ := by
                                simpa [htc, hsubst, heq] using hrun''
                            exact ih hk_succ hi_succ hrun_next v hv
                    | false =>
                        have hrun_next :
                          DB.checkHyp db hyps stack off (i + 1)
                            (subst.insert f[1]!.value val) = .ok σ := by
                              simpa [htc] using hrun''
                        by_cases hvar : f[1]!.value = v
                        · subst hvar
                          have hcontains :
                              (subst.insert f[1]!.value val).contains v = true := by
                            simpa using
                              (Metamath.KernelExtras.contains_insert_self
                                (m := subst) (a := v) (b := val))
                          exact ih hk_succ hi_succ hrun_next v hcontains
                        · have hcontains :
                            (subst.insert f[1]!.value val).contains v = true := by
                              have := Metamath.KernelExtras.contains_mono_insert
                                (m := subst) (a := v) (k := f[1]!.value) (b := val) hv
                              simpa [hvar] using this
                          exact ih hk_succ hi_succ hrun_next v hcontains
  have hk : hyps.size - i = hyps.size - i := rfl
  have hi' := hi
  have hrun' := hrun
  intro v hv
  exact main (hyps.size - i) (i := i) (subst := subst) (σ := σ) hk hi' hrun' v hv

lemma checkHyp_domain_aux
    {i : Nat} {subst σ : Std.HashMap String Formula}
    (hi : i ≤ hyps.size)
    (hrun : DB.checkHyp db hyps stack off i subst = .ok σ) :
    ∀ label ∈ hyps.toList.drop i,
      ∀ f, db.find? label = some (.hyp false f _) →
        σ.contains (f[1]!.value) = true := by
  classical
  have main :
      ∀ (k : Nat) {i : Nat} {subst σ : Std.HashMap String Formula},
        hyps.size - i = k →
        i ≤ hyps.size →
        DB.checkHyp db hyps stack off i subst = .ok σ →
        ∀ label ∈ hyps.toList.drop i,
          ∀ f, db.find? label = some (.hyp false f _) →
            σ.contains (f[1]!.value) = true := by
    intro k
    induction k with
    | zero =>
        intro i subst σ hk hi hrun label hmem f hfind
        have hi_ge : hyps.size ≤ i := Nat.sub_eq_zero_iff_le.mp hk
        have hi_eq : i = hyps.size := Nat.le_antisymm hi hi_ge
        subst hi_eq
        have hσ : σ = subst := by simpa [DB.checkHyp] using hrun
        subst hσ
        simp at hmem
    | succ k ih =>
        intro i subst σ hk hi hrun label hmem f hfind
        have hi_lt : i < hyps.size := by
          have hsum : i + (hyps.size - i) = hyps.size := Nat.add_sub_of_le hi
          have hsum' := by simpa [hk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            Nat.succ_eq_add_one] using hsum
          have : i < (i + 1) + k := by
            have : 0 < k + 1 := Nat.succ_pos _
            have := Nat.lt_add_of_pos_right i this
            simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
          simpa [hsum'] using this
        have hrun' :=
          by
            have := hrun
            simpa [DB.checkHyp, hi_lt] using this
        have hk_succ : hyps.size - (i + 1) = k := by
          have hsum : hyps.size = k + (i + 1) := by
            have hsum₀ : hyps.size = i + Nat.succ k := by
              have := Nat.add_sub_of_le hi
              simpa [hk] using this.symm
            simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum₀
          exact Nat.sub_eq_of_eq_add hsum
        have hi_succ : i + 1 ≤ hyps.size := Nat.succ_le_of_lt hi_lt
        have hdrop : hyps.toList.drop i = hyps[i] :: hyps.toList.drop (i + 1) := by
          have hlen : i < hyps.toList.length := by
            simpa [Array.length_toList] using hi_lt
          simpa using List.drop_eq_getElem_cons (l := hyps.toList) (i := i) hlen
        have hmem_cases : label = hyps[i] ∨ label ∈ hyps.toList.drop (i + 1) := by
          have hcons : label ∈ hyps[i] :: hyps.toList.drop (i + 1) := by
            simpa [hdrop] using hmem
          exact List.mem_cons.mp hcons
        cases hobj : db.find? hyps[i] with
        | none =>
            simp [hobj] at hrun'
        | some obj =>
            cases obj with
            | const _ =>
                simp [hobj] at hrun'
            | var _ =>
                simp [hobj] at hrun'
            | assert _ _ _ =>
                simp [hobj] at hrun'
            | hyp ess f₀ lbl =>
                set val := stack[off.1 + i]'(
                  (by
                    have := Nat.add_lt_add_left hi_lt off.1
                    simpa [off.2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this))
                  with hval
                have hrun'' :
                    if f₀[0]! == val[0]! then
                      if ess then
                        let x := do
                          let expected ← f₀.subst subst
                          if expected == val then
                            DB.checkHyp db hyps stack off (i + 1) subst
                          else Except.error "type error in substitution"
                        x
                      else
                        DB.checkHyp db hyps stack off (i + 1)
                          (subst.insert f₀[1]!.value val)
                    else
                      Except.error s!"bad typecode in substitution {hyps[i]}: {f₀} / {val}" =
                    .ok σ := by
                  simpa [hobj, DB.checkHyp, hi_lt, hval] using hrun'
                cases htc : (f₀[0]! == val[0]!) with
                | false =>
                    simp [htc] at hrun''
                    cases hrun''
                | true =>
                    cases ess with
                    | true =>
                        cases hsubst : f₀.subst subst with
                        | error err =>
                            simpa [htc, hsubst] using hrun''
                        | ok expected =>
                            cases heq : (expected == val) with
                            | false =>
                                simpa [htc, hsubst, heq] using hrun''
                            | true =>
                                have hrun_next :
                                  DB.checkHyp db hyps stack off (i + 1) subst = .ok σ := by
                                    simpa [htc, hsubst, heq] using hrun''
                                cases hmem_cases with
                                | inl hlabel =>
                                    subst hlabel
                                    -- essential hypothesis cannot match floating pattern
                                    have : False := by
                                      simpa [hobj] using hfind
                                    cases this
                                | inr htail =>
                                    exact ih hk_succ hi_succ hrun_next label htail f hfind
                    | false =>
                        have hrun_next :
                          DB.checkHyp db hyps stack off (i + 1)
                            (subst.insert f₀[1]!.value val) = .ok σ := by
                              simpa [htc] using hrun''
                        cases hmem_cases with
                        | inl hlabel =>
                            subst hlabel
                            have hcontains_init :
                                (subst.insert f₀[1]!.value val).contains (f₀[1]!.value) = true := by
                              simpa using
                                (Metamath.KernelExtras.contains_insert_self
                                  (m := subst) (a := f₀[1]!.value) (b := val))
                            have : σ.contains (f₀[1]!.value) = true :=
                              checkHyp_contains_mono (db := db) (hyps := hyps) (stack := stack)
                                (off := off) (hi := hi_succ) (hrun := hrun_next)
                                (v := f₀[1]!.value) hcontains_init
                            simpa [hobj] using this
                        | inr htail =>
                            exact ih hk_succ hi_succ hrun_next label htail f hfind
  have hk : hyps.size - i = hyps.size - i := rfl
  exact main (hyps.size - i) (i := i) (subst := subst) (σ := σ) hk hi hrun


namespace

variable {db : DB}

private lemma checkHyp_stack_split_aux
  (hyps : Array String) (stack : Array Formula)
  (off : { off // off + hyps.size = stack.size })
  (i : Nat) (subst : Std.HashMap String Formula) :
  i ≤ hyps.size →
  ∀ {σ : Std.HashMap String Formula}
    {stack_spec : List Metamath.Spec.Expr},
    DB.checkHyp db hyps stack off i subst = .ok σ →
    stack.toList.mapM toExprOpt = some stack_spec →
    ∃ (hypTail remaining : List Metamath.Spec.Expr),
      hypTail.length = hyps.size - i ∧
      stack_spec = remaining ++ hypTail.reverse := by
  classical
  intro hi σ stack_spec _ h_stack
  classical
  have h_len_map :
      stack_spec.length = stack.toList.length :=
    list_mapM_length_option toExprOpt (xs := stack.toList) (ys := stack_spec) h_stack
  have h_len_stack :
      stack_spec.length = stack.size := by
    simpa [Array.length_toList] using h_len_map
  have h_total :
      stack_spec.length = off.1 + hyps.size := by
    calc
      stack_spec.length = stack.size := h_len_stack
      _ = off.1 + hyps.size := by
        simpa [Nat.add_comm] using off.2
  let prefix := stack_spec.take (off.1 + i)
  let suffix := stack_spec.drop (off.1 + i)
  have h_suffix_len :
      suffix.length = hyps.size - i := by
    have h_drop :
        suffix.length = stack_spec.length - (off.1 + i) := by
      simpa [suffix] using List.length_drop (off.1 + i) stack_spec
    have h_sub :
        stack_spec.length - (off.1 + i) = hyps.size - i := by
      have h_sub' :
          (off.1 + hyps.size) - (off.1 + i) = hyps.size - i := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Nat.add_sub_cancel_left hyps.size i off.1
      simpa [h_total] using h_sub'
    exact h_drop.trans h_sub
  refine ⟨suffix.reverse, prefix, ?_, ?_⟩
  · have h_rev_len := List.length_reverse suffix
    simpa [suffix, h_suffix_len] using h_rev_len
  ·
    have h_split := List.take_append_drop (off.1 + i) stack_spec
    simpa [prefix, suffix] using h_split

end


/-- If `checkHyp` succeeds, the converted stack splits into a prefix and a
    suffix of length `hyps.size`. -/
theorem checkHyp_stack_split_theorem
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : { off : Nat // off + hyps.size = stack.size }) (σ : Std.HashMap String Formula)
  (stack_spec : List Metamath.Spec.Expr) :
  DB.checkHyp db hyps stack off 0 ∅ = .ok σ →
  stack.toList.mapM toExprOpt = some stack_spec →
  ∃ (hypTail remaining : List Metamath.Spec.Expr),
    hypTail.length = hyps.size ∧
    stack_spec = remaining ++ hypTail.reverse := by
  classical
  intro h_run h_stack
  -- Apply the auxiliary lemma with `i = 0` and the empty initial substitution.
  have h_split :=
    checkHyp_stack_split_aux (db := db) hyps stack off 0 (Std.HashMap.empty)
      (by exact Nat.zero_le _) (σ := σ) (stack_spec := stack_spec) h_run h_stack
  simpa [Nat.sub_zero] using h_split

/-- Every binding installed by `checkHyp` converts to a spec expression. -/
theorem checkHyp_images_convert_theorem
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : { off : Nat // off + hyps.size = stack.size }) (σ : Std.HashMap String Formula)
  (stack_spec : List Metamath.Spec.Expr) :
  DB.checkHyp db hyps stack off 0 ∅ = .ok σ →
  stack.toList.mapM toExprOpt = some stack_spec →
  ∀ v, σ.contains v = true → ∃ e, toExprOpt (σ[v]!) = some e := by
  classical
  intro h_run h_stack v hv
  classical
  -- Final substitution satisfies HypProp on full list
  have hprop_final :
      HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) hyps.size σ :=
    checkHyp_preserves_HypProp (db := db) (hyps := hyps) (stack := stack) (off := off)
      (i := 0) (subst := (∅ : Std.HashMap String Formula)) (σ := σ)
      (hi := Nat.zero_le _) (hprop := HypProp.empty) h_run
  -- Interpret contains as isSome
  have hcontains :=
    Std.HashMap.contains_eq_isSome_getElem? (m := σ) (a := v)
  have h_isSome : (σ[v]?).isSome = true := by
    simpa [hcontains, hv]
  -- Extract the stored value from the substitution
  cases hlookup : σ[v]? with
  | none =>
      simp [hlookup] at h_isSome
  | some val =>
      -- Witness from HypProp gives the matching floating hypothesis
      obtain ⟨j, hj, hbind⟩ := hprop_final v val hlookup
      rcases hbind with ⟨_, k, hk, f, lbl, hfind, hvar, hval, hhead⟩
      -- Recover bounds and equality witnesses from the stored data
      have hlt : off.1 + j < stack.size := by
        have : (k : Nat) < stack.size := k.is_lt
        simpa [hk] using this
      have hlist_lt : off.1 + j < stack.toList.length := by
        simpa [Array.length_toList] using hlt
      have hk_fin :
          (⟨off.1 + j, hlt⟩ : Fin stack.size) = k := by
        ext
        simpa [hk]
      have hval_stack :
          val = stack[off.1 + j]'hlt := by
        have : stack[off.1 + j]'hlt = stack[⟨off.1 + j, hlt⟩]! := rfl
        have : stack[⟨off.1 + j, hlt⟩]! = stack[k]! := by
          simpa using congrArg (fun fin : Fin stack.size => stack[fin]!) hk_fin
        simpa [this] using hval
      obtain ⟨e, he⟩ :=
        Metamath.KernelExtras.mapM_index_some (f := toExprOpt)
          (xs := stack.toList) (ys := stack_spec) h_stack (off.1 + j) hlist_lt
      have hget :
          stack.toList.get ⟨off.1 + j, hlist_lt⟩ = stack[off.1 + j]'hlt := by
        simpa using (Array.getElem_toList (xs := stack) (i := off.1 + j) (h := hlt))
      have hbang : σ[v]! = val := by
        simp [hlookup]
      have hval_toList : stack.toList.get ⟨off.1 + j, hlist_lt⟩ = val := by
        simpa [hget, hval_stack]
      have h_conv :
          toExprOpt val = some e := by
        simpa [hval_toList]
          using he
      exact ⟨e, by simpa [hbang] using h_conv⟩

/-- Each floating hypothesis matched by `checkHyp` produces a substitution entry. -/
theorem checkHyp_domain_covers_theorem
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : { off : Nat // off + hyps.size = stack.size }) (σ : Std.HashMap String Formula)
  (stack_spec : List Metamath.Spec.Expr) :
  DB.checkHyp db hyps stack off 0 ∅ = .ok σ →
  stack.toList.mapM toExprOpt = some stack_spec →
  ∀ label ∈ hyps.toList,
    ∀ f, db.find? label = some (.hyp false f _) →
      σ.contains (f[1]!.value) = true := by
  classical
  intro h_run _ label h_mem f h_find
  have hdomain :=
    checkHyp_domain_aux (db := db) (hyps := hyps) (stack := stack) (off := off)
      (i := 0) (subst := (∅ : Std.HashMap String Formula)) (σ := σ)
      (hi := Nat.zero_le _) (hrun := h_run)
  simpa using hdomain label (by simpa using h_mem) f h_find

/-- Extracts the floating hypothesis responsible for a substitution entry. -/
theorem checkHyp_binding_witness
    (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (σ : Std.HashMap String Formula) :
  DB.checkHyp db hyps stack off 0 ∅ = .ok σ →
  ∀ v val, σ[v]? = some val →
    ∃ j f lbl (hlt : off.1 + j < stack.size),
      j < hyps.size ∧
      db.find? hyps[j] = some (.hyp false f lbl) ∧
      f[1]!.value = v ∧
      val = stack[off.1 + j]'hlt ∧
      f[0]! == val[0]! = true := by
  classical
  intro h_run v val hfind
  have hprop_final :
      HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) hyps.size σ :=
    checkHyp_preserves_HypProp (db := db) (hyps := hyps) (stack := stack) (off := off)
      (i := 0) (subst := (∅ : Std.HashMap String Formula)) (σ := σ)
      (hi := Nat.zero_le _) (hprop := HypProp.empty) h_run
  obtain ⟨j, hj, hbind⟩ := hprop_final v val hfind
  rcases hbind with ⟨_, k, hk, f, lbl, hfind', hvar, hval, hhead⟩
  have hlt : off.1 + j < stack.size := by
    have : (k : Nat) < stack.size := k.is_lt
    simpa [hk] using this
  have hk_fin :
      (⟨off.1 + j, hlt⟩ : Fin stack.size) = k := by
    ext
    simpa [hk]
  have hk_stack :
      stack[k]! = stack[⟨off.1 + j, hlt⟩]! := by
    simpa using congrArg (fun fin : Fin stack.size => stack[fin]!) hk_fin.symm
  have hval' : val = stack[off.1 + j]'hlt := by
    have : stack[off.1 + j]'hlt = stack[⟨off.1 + j, hlt⟩]! := rfl
    simpa [this] using hval.trans hk_stack
  exact ⟨j, f, lbl, hlt, hj, hfind', hvar, hval', hhead⟩

/-- Produces a converted expression for each substitution binding after `checkHyp`. -/
theorem checkHyp_image_exists
    (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : { off : Nat // off + hyps.size = stack.size })
    (σ : Std.HashMap String Formula) (stack_spec : List Spec.Expr) :
  DB.checkHyp db hyps stack off 0 ∅ = .ok σ →
  stack.toList.mapM toExprOpt = some stack_spec →
  ∀ v val, σ[v]? = some val →
    ∃ (j : Nat) (w : FloatBindWitness db hyps stack off j v val) (e : Spec.Expr),
      toExprOpt val = some e := by
  classical
  intro h_run h_stack v val hfind
  obtain ⟨j, f, lbl, hlt, hj, hfind', hvar, hval, hhead⟩ :=
    checkHyp_binding_witness (db := db) (hyps := hyps) (stack := stack)
      (off := off) (σ := σ) h_run v val hfind
  -- convert stack entry to a spec expression using the recorded index
  have hlist_lt : off.1 + j < stack.toList.length := by
    simpa [Array.length_toList] using hlt
  obtain ⟨e, he⟩ :=
    Metamath.KernelExtras.mapM_index_some (f := toExprOpt)
      (xs := stack.toList) (ys := stack_spec) h_stack (off.1 + j) hlist_lt
  have hget :
      stack.toList.get ⟨off.1 + j, hlist_lt⟩ = stack[off.1 + j]'hlt := by
    simpa using (Array.getElem_toList (xs := stack) (i := off.1 + j) (h := hlt))
  have hval_toList : stack.toList.get ⟨off.1 + j, hlist_lt⟩ = val := by
    simpa [hget, hval]
  refine ⟨j, ?_, e, ?_⟩
  · exact FloatBindWitness.mk (db := db) (hyps := hyps) (stack := stack) (off := off)
      (j := j) (v := v) (val := val) hj
      ⟨off.1 + j, hlt⟩ rfl f lbl hfind' hvar hval hhead
  · simpa [hval_toList] using he

/-- If every floating hypothesis admits a well-typed image in `σ`, then
    `Convert.toSubst` succeeds and returns a typed substitution. -/
theorem toSubst_exists_of_cover
    (fr_spec : Metamath.Spec.Frame)
    (σ_impl : Std.HashMap String Formula)
    (hnodup : ((Metamath.Bridge.floats fr_spec).map Prod.snd).Nodup)
    (hcover :
      ∀ {c v},
        (c, v) ∈ Metamath.Bridge.floats fr_spec →
        ∃ f e,
          σ_impl.find? v.v = some f ∧
          toExprOpt f = some e ∧
          e.typecode = c) :
    ∃ σ_typed : Metamath.Bridge.TypedSubst fr_spec,
      toSubst fr_spec σ_impl = some σ_typed := by
  classical
  refine Convert.toSubst_total (fr_spec := fr_spec) (σ_impl := σ_impl) hnodup ?_
  intro c v hmem
  exact hcover hmem

end Proofs
end Verify
end Metamath
