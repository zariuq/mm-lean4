# Codex Archive Treasure Map 🗺️

**Purpose:** Comprehensive catalog of valuable ideas and code in `codex_archive/`
**Date:** 2025-10-12
**Status:** Complete archive, tagged for future reference

---

## Quick Reference: High-Value Items

### 🌟 MUST-REVIEW (Direct Use in Forward Plan)

1. **`Verify/Proofs.lean:467-619`** - `checkHyp_preserves_HypProp`
   - 150-line loop invariant proof, FULLY PROVEN
   - **Use in:** Phase 1.3 (checkHyp master invariant)
   - **Why:** Template for threading invariants through recursion

2. **`Verify/Proofs.lean:50-63`** - `FloatBindWitness` structure
   - Witness pattern for floating hypothesis bindings
   - **Use in:** Phase 1.2 (checkHyp theorems)
   - **Why:** Carries head-constant equality (GPT-5's point!)

3. **`KernelExtras.lean:144-170`** - Boolean fold lemmas
   - `foldl_and_eq_true`, `foldl_all₂` (PROVEN)
   - **Use in:** Phase 2.1 (DV variable scans)
   - **Why:** Exactly what we need for Boolean → ∀ reduction

---

## File-by-File Catalog

---

## 📁 `codex_archive/Bridge/Basics.lean` (143 lines)

**Overall Quality:** ⭐⭐⭐⭐⭐ Excellent
**Proof Status:** All theorems proven (no sorries!)
**Value:** HIGH - Clean abstractions, alternative designs

### Contents

#### 1. Alternative `TypedSubst` Structure (Lines 11-15)

```lean
structure TypedSubst (fr : Spec.Frame) where
  σ : Spec.Subst
  typed : ∀ {c v}, Hyp.floating c v ∈ fr.mand →
    (σ v).typecode = c
```

**Design comparison:**
- **Claude's version:** Uses explicit declaration map `(decls : HashMap Variable Constant)`
- **Codex's version:** Frame-centric, types directly from frame hypotheses
- **Trade-off:** Codex's is more specific to Metamath, Claude's is more general

**Tag:** `#alternative-design` `#phase3-bridge`
**When to use:** Phase 3.2 when introducing thin Bridge
**Consideration:** Compare both designs, possibly support both or pick cleaner one

---

#### 2. `needOf` / `needed` Functions (Lines 17-28)

```lean
def needOf (σ : Spec.Subst) (h : Spec.Hyp) : Option (Spec.Constant × Spec.Variable) :=
  match h with
  | .floating c v => some (c, v)
  | .essential _ => none

def needed (fr : Spec.Frame) (σ : Spec.Subst) : List (Spec.Constant × Spec.Variable) :=
  fr.mand.filterMap (needOf σ)
```

**Purpose:** Extract hypothesis images under substitution

**Tag:** `#helper-function` `#phase3-bridge`
**When to use:** If we want clean API for extracting float list from frame
**Value:** Medium - nice abstraction but not essential

---

#### 3. `floats` / `essentials` Functions (Lines 30-48)

```lean
def floats (fr : Spec.Frame) : List (Spec.Constant × Spec.Variable) :=
  fr.mand.foldr
    (fun h acc =>
      match h with
      | .floating c v => (c, v) :: acc
      | .essential _ => acc)
    []

def essentials (fr : Spec.Frame) : List Spec.Expr :=
  fr.mand.foldr
    (fun h acc =>
      match h with
      | .floating _ _ => acc
      | .essential e => e :: acc)
    []
```

**Purpose:** Partition frame hypotheses into floats vs essentials

**Tag:** `#helper-function` `#phase3-bridge` `#recommend`
**When to use:** Phase 3.2 Bridge definitions
**Value:** HIGH - Clean API, useful for multiple purposes
**Note:** Include these in thin Bridge layer (definitions only)

---

#### 4. Proven Theorems (Lines 50-143)

All theorems FULLY PROVEN, no sorries!

##### Theorem: `floating_mem_floats_list` (Lines 50-58)
```lean
theorem floating_mem_floats_list (fr : Spec.Frame) (c : Spec.Constant) (v : Spec.Variable)
    (h : Hyp.floating c v ∈ fr.mand) :
    (c, v) ∈ floats_list fr
```
**Purpose:** Membership correctness for floats extraction
**Tag:** `#proven-lemma` `#phase3-bridge`
**Value:** Medium - will need this if we use `floats` function

##### Theorem: `floating_mem_floats` (Lines 60-68)
```lean
theorem floating_mem_floats (fr : Spec.Frame) (c : Spec.Constant) (v : Spec.Variable)
    (h : Hyp.floating c v ∈ fr.mand) :
    (c, v) ∈ (floats fr).toFinset
```
**Purpose:** Finset version of above
**Tag:** `#proven-lemma` `#phase3-bridge`
**Value:** Medium

##### Theorem: `floats_map_snd` (Lines 70-78)
```lean
theorem floats_map_snd (fr : Spec.Frame) :
    (floats fr).map Prod.snd = fr.mand.filterMap (fun h =>
      match h with
      | .floating _ v => some v
      | .essential _ => none)
```
**Purpose:** Projection correctness
**Tag:** `#proven-lemma` `#phase3-bridge`
**Value:** Low - specialized, may not need

##### Theorem: `floats_list_mem` (Lines 80-119)
```lean
theorem floats_list_mem (fr : Spec.Frame) (c : Spec.Constant) (v : Spec.Variable)
    (h : (c, v) ∈ floats_list fr) :
    Hyp.floating c v ∈ fr.mand
```
**Purpose:** Inverse membership (if in floats, then in frame)
**Tag:** `#proven-lemma` `#phase3-bridge`
**Value:** Medium - useful for bidirectionality

##### Theorem: `floats_mem_floating` (Lines 121-143)
```lean
theorem floats_mem_floating (fr : Spec.Frame) (c : Spec.Constant) (v : Spec.Variable) :
    (c, v) ∈ (floats fr).toFinset ↔ Hyp.floating c v ∈ fr.mand
```
**Purpose:** Full bidirectionality (iff)
**Tag:** `#proven-lemma` `#phase3-bridge` `#recommend`
**Value:** HIGH - Complete characterization, very useful

---

**Bridge/Basics.lean Summary:**
- **Recommend copying:** `floats`, `essentials` definitions + `floats_mem_floating` theorem
- **Consider:** Alternative `TypedSubst` design (compare with Claude's)
- **All theorems proven:** Can trust these completely

---

## 📁 `codex_archive/Verify/Proofs.lean` (768 lines!)

**Overall Quality:** ⭐⭐⭐⭐⭐ Excellent (HIGHEST VALUE FILE)
**Proof Status:** All major theorems proven!
**Value:** VERY HIGH - This is the missing piece for checkHyp verification

### Contents

---

#### 🌟 1. `FloatBindWitness` Structure (Lines 50-63)

```lean
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
  head   : (f[0]! == val[0]!) = true  -- ⭐ THIS IS KEY (GPT-5's point!)
```

**Purpose:** Witness structure for floating hypothesis bindings

**Tag:** `#witness-pattern` `#phase1-checkhyp` `#recommend` `#gpt5-endorsed`
**When to use:** Phase 1.2 - checkHyp theorems
**Why this is brilliant:**
- Carries the typecode guard: `head : (f[0]! == val[0]!) = true`
- This is exactly what GPT-5 meant: "Record the head-constant equality you used to succeed"
- Eliminates need for separate typecode tracking
- Direct proof that binding is well-typed

**Value:** VERY HIGH - Adopt this pattern!

**How to use:**
1. Extend current `HypBinding` to include head-constant equality
2. Thread this witness through checkHyp induction
3. Use it to prove `checkHyp_images_convert`

---

#### 🌟 2. `HypProp` Invariant (Lines 155-160)

```lean
private def HypProp (n : Nat) (σ : Std.HashMap String Formula) : Prop :=
  ∀ v val, σ[v]? = some val →
    ∃ j, j < n ∧ HypBinding (db := db) (hyps := hyps) (stack := stack) (off := off) j v val
```

**Purpose:** Loop invariant for checkHyp - tracks that all bindings come from processed hypotheses

**Tag:** `#loop-invariant` `#phase1-checkhyp` `#recommend`
**When to use:** Phase 1.3 - Master invariant
**Why this matters:**
- Clean formulation of "where bindings come from"
- Parameterized by `n` (number of hypotheses processed)
- Easy to prove by induction

**Value:** VERY HIGH - Template for our invariant

---

#### 🌟 3. `HypProp` Helper Lemmas (Lines 162-244)

##### Lemma: `HypProp.empty` (Lines 162-164)
```lean
lemma HypProp.empty : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) 0 ∅
```
**Purpose:** Base case - empty substitution satisfies invariant
**Tag:** `#base-case` `#phase1-checkhyp`
**Value:** Essential for induction setup

##### Lemma: `HypProp.mono` (Lines 166-172)
```lean
lemma HypProp.mono {m n : Nat} (h : m ≤ n)
    (hp : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) m σ) :
    HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) n σ
```
**Purpose:** Monotonicity - if invariant holds at m, holds at larger n
**Tag:** `#monotonicity` `#phase1-checkhyp`
**Value:** HIGH - Will need for induction

##### Lemma: `HypProp.insert_floating` (Lines 174-244)
```lean
lemma HypProp.insert_floating
    {i : Nat} {v : String} {val : Formula}
    (hi : i < hyps.size)
    (hw : FloatBindWitness (db := db) (hyps := hyps) (stack := stack) (off := off) i v val)
    (hp : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) i σ) :
    HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) (i + 1) (σ.insert v val)
```
**Purpose:** Inductive step - inserting floating binding preserves invariant
**Tag:** `#inductive-step` `#phase1-checkhyp` `#recommend`
**Value:** VERY HIGH - Core of the induction proof
**Note:** 70-line proof, fully worked out!

---

#### 🌟 4. `checkHyp_preserves_HypProp` (Lines 467-619) **[CROWN JEWEL]**

```lean
lemma checkHyp_preserves_HypProp
    {i : Nat} {subst σ : Std.HashMap String Formula}
    (hi : i ≤ hyps.size)
    (hprop : HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) i subst)
    (hrun : DB.checkHyp db hyps stack off i subst = .ok σ) :
    HypProp (db := db) (hyps := hyps) (stack := stack) (off := off) hyps.size σ
```

**Purpose:** Main theorem - checkHyp preserves HypProp invariant

**Tag:** `#main-theorem` `#phase1-checkhyp` `#template` `#fully-proven`
**When to use:** Phase 1.3 - Master invariant template
**Structure:** (Lines 467-619, ~150 lines)
1. Unfold checkHyp recursion
2. Case analysis: i = hyps.size vs i < hyps.size
3. Base case: i = hyps.size, return subst unchanged
4. Recursive case: i < hyps.size
   - Look up hyps[i]
   - Case: Floating hypothesis
     * Read stack[off + i]
     * Check typecode: f[0]! == stack[off+i][0]!
     * If success: insert binding, recurse
     * Prove: HypProp preserved after insertion
   - Case: Essential hypothesis
     * Read stack[off + i]
     * Compare with expected expression
     * If match: recurse (no insertion)
     * Prove: HypProp preserved (no change to σ)
5. Apply IH to get HypProp at hyps.size

**Value:** ⭐⭐⭐⭐⭐ ABSOLUTE GOLD
**Why:** This is the EXACT roadmap for Phase 1.3!

**How to use:**
1. Copy the case analysis structure
2. Extend HypProp to include stack-split + domain-coverage
3. Follow Codex's floating case (lines 520-580) for handling bindings
4. Add our additional invariant clauses
5. Result: Master invariant that proves all three properties!

**Key sections to study:**

##### Base Case Handling (Lines 474-484)
```lean
by_cases h : i = hyps.size
· -- Base case: i = hyps.size
  subst h
  simp [DB.checkHyp] at hrun
  cases hrun
  exact hprop
```

##### Recursive Setup (Lines 485-519)
```lean
· -- Recursive case: i < hyps.size
  have hi_lt : i < hyps.size := Nat.lt_of_le_of_ne hi h
  simp [DB.checkHyp, hi_lt] at hrun

  -- Look up hypothesis
  match h_find : db.find? hyps[i] with
  | none => simp [h_find] at hrun  -- impossible
  | some obj => ...
```

##### Floating Case (Lines 520-580) ⭐
```lean
| .hyp false f lbl =>  -- floating hypothesis
  simp [h_find] at hrun

  -- Extract stack element
  have h_stack : ∃ val, stack[off.1 + i]? = some val := ...

  -- Check typecode guard
  match h_check : (f[0]! == val[0]!) with
  | false => ...  -- fail case
  | true =>       -- success case
    -- Build witness
    have hw : FloatBindWitness ... := {
      hj := hi_lt
      k := ⟨off.1 + i, ...⟩
      hk := rfl
      f := f
      lbl := lbl
      find := h_find
      var := ...,
      val_eq := ...,
      head := h_check  -- ⭐ The key equality!
    }

    -- Insert binding
    let σ' := subst.insert v val

    -- Prove invariant after insertion
    have hp' : HypProp (i + 1) σ' := HypProp.insert_floating hi_lt hw hprop

    -- Apply IH
    have ih : HypProp hyps.size σ_final := checkHyp_preserves_HypProp (Nat.le_of_lt ...) hp' ...
    exact ih
```

**Essential Case (Lines 581-619)**
```lean
| .hyp true e lbl =>  -- essential hypothesis
  simp [h_find] at hrun

  -- Extract stack element
  have h_stack : ∃ val, stack[off.1 + i]? = some val := ...

  -- Check match
  match h_match : (toExprOpt val) with
  | none => ...  -- conversion failure
  | some e' =>
    if h_eq : e = e' then
      -- Match success, no insertion
      -- HypProp unchanged
      have hp' : HypProp (i + 1) subst := HypProp.mono (Nat.le.step (Nat.le_refl i)) hprop
      -- Apply IH
      exact checkHyp_preserves_HypProp ... hp' ...
    else
      ...  -- mismatch
```

**Estimated adaptation effort:** ~180-220 lines (extending to include our additional invariants)

---

#### 5. Additional checkHyp Theorems (Lines 621-800+)

All build on the master invariant above!

##### Theorem: `checkHyp_contains_mono` (Lines 652-656)
```lean
lemma checkHyp_contains_mono
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    (h_contains : subst.contains v) :
    σ.contains v
```
**Purpose:** Domain monotonicity - variables don't disappear
**Tag:** `#monotonicity` `#phase1-checkhyp`
**Value:** HIGH - needed for domain coverage proof

---

##### Theorem: `checkHyp_domain_aux` (Lines 658-686)
```lean
lemma checkHyp_domain_aux
    (h_check : DB.checkHyp db hyps stack off 0 ∅ = .ok σ)
    (hj : j < hyps.size)
    (h_float : db.find? hyps[j] = some (.hyp false f lbl))
    (h_var : f[1]!.value = v) :
    σ.contains v
```
**Purpose:** Helper for domain coverage - each float inserts its variable
**Tag:** `#helper-lemma` `#phase1-checkhyp`
**Value:** Medium - useful for coverage proof

---

##### Theorem: `checkHyp_stack_split_theorem` (Lines 688-695)
```lean
lemma checkHyp_stack_split_theorem
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    (h_off : off + hyps.size = stack.size) :
    ∃ remaining hypTail,
      stack = remaining ++ hypTail ∧
      hypTail.length = hyps.size
```
**Purpose:** Stack shape theorem (our checkHyp_stack_split!)
**Tag:** `#stack-shape` `#phase1-checkhyp` `#recommend`
**Value:** HIGH - This is exactly Theorem 1 from our plan!
**Note:** Signature matches our Phase 1.2 exactly

---

##### Theorem: `checkHyp_images_convert_theorem` (Lines 697-713)
```lean
lemma checkHyp_images_convert_theorem
    (h_check : DB.checkHyp db hyps stack off i subst = .ok σ)
    (h_find : σ.find? v = some val) :
    ∃ e, toExprOpt val = some e
```
**Purpose:** Image conversion (our checkHyp_images_convert!)
**Tag:** `#image-conversion` `#phase1-checkhyp` `#recommend`
**Value:** HIGH - This is exactly Theorem 2 from our plan!
**Note:** Uses FloatBindWitness.head to prove conversion succeeds

---

##### Theorem: `checkHyp_domain_covers_theorem` (Lines 715-728)
```lean
lemma checkHyp_domain_covers_theorem
    (h_check : DB.checkHyp db hyps stack off 0 ∅ = .ok σ)
    (h_float : Spec.Hyp.floating c v ∈ frame.mand) :
    σ.contains v
```
**Purpose:** Domain coverage (our checkHyp_domain_covers!)
**Tag:** `#domain-coverage` `#phase1-checkhyp` `#recommend`
**Value:** HIGH - This is exactly Theorem 3 from our plan!

---

##### Theorem: `checkHyp_binding_witness` (Lines 730-739)
```lean
lemma checkHyp_binding_witness
    (h_check : DB.checkHyp db hyps stack off 0 ∅ = .ok σ)
    (h_find : σ.find? v = some val) :
    ∃ j, FloatBindWitness (db := db) (hyps := hyps) (stack := stack) (off := off) j v val
```
**Purpose:** Extract binding witness
**Tag:** `#witness-extraction` `#phase1-checkhyp`
**Value:** HIGH - Connects bindings back to their origins

---

##### Theorem: `checkHyp_image_exists` (Lines 741-748)
```lean
lemma checkHyp_image_exists
    (hw : FloatBindWitness (db := db) (hyps := hyps) (stack := stack) (off := off) j v val) :
    ∃ e, toExprOpt val = some e ∧ e.typecode = hw.f[0]!.value
```
**Purpose:** Witness implies conversion + typecode
**Tag:** `#witness-implies-typed` `#phase1-checkhyp` `#recommend`
**Value:** VERY HIGH - This is how we get typed coverage!
**Note:** Uses `FloatBindWitness.head` equality directly

**Proof sketch:**
```lean
-- hw.head : (f[0]! == val[0]!) = true
-- Therefore: val has same head as f
-- Therefore: toExprOpt succeeds
-- And: result has typecode = f[0]!.value
```

---

##### Theorem: `toSubst_exists_of_cover` (Lines 750-800+)
```lean
lemma toSubst_exists_of_cover
    (h_check : DB.checkHyp db hyps stack off 0 ∅ = .ok σ)
    (h_frame : frame = toFrame db_entry)
    : ∃ σ_typed : TypedSubst frame, ...
```
**Purpose:** Complete typed substitution construction
**Tag:** `#typed-subst-construction` `#phase1-checkhyp` `#recommend`
**Value:** VERY HIGH - This completes Phase 1.4!

---

### Verify/Proofs.lean Summary

**Crown Jewels (MUST USE):**
1. `FloatBindWitness` structure (lines 50-63) - Adopt this pattern!
2. `checkHyp_preserves_HypProp` (lines 467-619) - Template for master invariant
3. Three domain theorems (lines 688-728) - Exactly our Phase 1.2 theorems!

**Estimated reuse:** ~60-70% of proofs can be adapted directly

**Adaptation strategy:**
1. Start with `FloatBindWitness` - add to our codebase
2. Use `checkHyp_preserves_HypProp` structure as template
3. Extend with our stack-split and domain clauses
4. Adapt the three domain theorems for our API
5. Result: Complete Phase 1 proof!

---

## 📁 `codex_archive/KernelExtras.lean` (367 lines)

**Overall Quality:** ⭐⭐⭐⭐☆ Good (some sorries)
**Proof Status:** ~85% proven (mapM/List/HashMap all proven, some Subst sorries)
**Value:** MEDIUM-HIGH - Useful utilities

### Contents

---

#### 1. Substitution Helpers (Lines 10-45)

##### Function: `Subst.update` (Lines 10-13)
```lean
def Subst.update (σ : Subst) (v : Variable) (e : Expr) : Subst :=
  fun w => if w = v then e else σ w
```
**Purpose:** Point update for substitution
**Tag:** `#helper-function` `#utility`
**Value:** Low - simple enough to define inline

##### Predicate: `Subst.IdOn` (Lines 15-16)
```lean
def Subst.IdOn (σ : Subst) (vs : List Variable) : Prop :=
  ∀ v ∈ vs, σ v = Expr.var v
```
**Purpose:** Identity predicate on variable list
**Tag:** `#predicate` `#utility`
**Value:** Medium - useful if we need identity reasoning

##### Theorem: `applySubst_id_on` (Lines 18-29) ⚠️ SORRY
```lean
theorem applySubst_id_on (h : σ.IdOn (Expr.varsInExpr e)) :
    Spec.applySubst σ e = e := by sorry
```
**Purpose:** Substitution with identity on support is identity
**Tag:** `#sorry` `#substitution-theory`
**Value:** Medium - would need if proving subst algebra

---

##### Theorem: `dvOK_comp_sufficient` (Lines 31-45) ⚠️ SORRY
```lean
theorem dvOK_comp_sufficient
    (h : ∀ v ∈ Spec.varsInExpr e₁, ∀ w ∈ Spec.varsInExpr e₂, v ≠ w)
    : Spec.dvOK (Spec.applySubst σ e₁) (Spec.applySubst σ e₂) := by sorry
```
**Purpose:** DV preservation under substitution
**Tag:** `#sorry` `#dv-theory` `#phase2`
**Value:** HIGH IF NEEDED - would be useful for DV proofs in Phase 2
**Note:** Currently sorry, but signature is right

---

#### 2. List Utilities (Lines 47-95)

##### Theorem: `filterMap_preserves_nodup` (Lines 47-63) ⚠️ PARTIAL SORRY
```lean
theorem filterMap_preserves_nodup {α β} (f : α → Option β)
    (h_inj : ∀ a₁ a₂ b, f a₁ = some b → f a₂ = some b → a₁ = a₂)
    (h_nodup : xs.Nodup) :
    (xs.filterMap f).Nodup := by
  -- Partial proof, ends with sorry
```
**Purpose:** Nodup preservation under filterMap
**Tag:** `#partial-proof` `#list-theory`
**Value:** Low - likely exists in Mathlib

---

##### Theorem: `variable_mk_injective` (Lines 65-66) ✅ PROVEN
```lean
theorem variable_mk_injective : Function.Injective Spec.Variable.mk
```
**Purpose:** Constructor injectivity
**Tag:** `#proven` `#trivial`
**Value:** Low - trivial

---

##### Theorem: `nodup_map_of_injective` (Lines 68-73) ✅ PROVEN
```lean
theorem nodup_map_of_injective {α β} (f : α → β) (h_inj : Function.Injective f)
    (h_nodup : xs.Nodup) :
    (xs.map f).Nodup
```
**Purpose:** Nodup under injective map
**Tag:** `#proven` `#list-theory`
**Value:** Low - likely in Mathlib as `List.Nodup.map`

---

##### Theorem: `filterMap_after_mapM_eq` (Lines 75-95) ✅ PROVEN
```lean
theorem filterMap_after_mapM_eq {m : Type → Type} [Monad m]
    (f : α → m β) (g : β → Option γ)
    (h : xs.mapM f = some ys) :
    ys.filterMap g = (xs.filterMap (fun a => (f a).bind (fun b => pure (g b)))).join
```
**Purpose:** Fusion lemma for mapM + filterMap
**Tag:** `#proven` `#monad-theory`
**Value:** Low - very specialized

---

#### 🌟 3. mapM Infrastructure (Lines 97-175) ✅ ALL PROVEN

These are all FULLY PROVEN and generally useful!

##### Theorem: `mapM_index_some` (Lines 97-123) ✅
```lean
theorem mapM_index_some {α β} (f : α → Option β)
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys)
    (i : Nat) (hi : i < xs.length) :
    ∃ (y : β), f (xs.get ⟨i, hi⟩) = some y
```
**Purpose:** mapM success implies each element converts
**Tag:** `#proven` `#mapm-theory` `#recommend`
**Value:** HIGH - will likely need for array/list reasoning
**When to use:** Phase 3.1 (helper lemmas)

---

##### Theorem: `mapM_mem` (Lines 125-135) ✅
```lean
theorem mapM_mem {α β} (f : α → Option β)
    (h : xs.mapM f = some ys)
    (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = some y
```
**Purpose:** Element in result came from input
**Tag:** `#proven` `#mapm-theory` `#recommend`
**Value:** MEDIUM - useful for provenance reasoning

---

##### Theorem: `mapM_length` (Lines 137-142) ✅
```lean
theorem mapM_length {α β} (f : α → Option β)
    (h : xs.mapM f = some ys) :
    ys.length = xs.length
```
**Purpose:** mapM preserves length
**Tag:** `#proven` `#mapm-theory` `#recommend`
**Value:** HIGH - frequently needed!

---

##### Theorem: `mapM_index_get` (Lines 144-175) ✅
```lean
theorem mapM_index_get {α β} (f : α → Option β)
    (h : xs.mapM f = some ys)
    (i : Nat) (hi : i < xs.length) :
    ∃ y, f (xs.get ⟨i, hi⟩) = some y ∧
         ys.get ⟨i, by rw [mapM_length h]; exact hi⟩ = y
```
**Purpose:** Index correspondence in mapM
**Tag:** `#proven` `#mapm-theory` `#recommend`
**Value:** VERY HIGH - precise reasoning about mapM

---

**mapM Summary:** ALL FOUR THEOREMS ARE PROVEN!
**Recommendation:** Import these directly into a Utilities module
**Estimated value:** Saves ~100-150 lines of proving basic facts

---

#### 🌟 4. Boolean Fold Lemmas (Lines 177-213) ✅ ALL PROVEN

These are EXACTLY what GPT-5 recommended for Phase 2!

##### Theorem: `foldl_and_eq_true` (Lines 144-149) ✅
```lean
theorem foldl_and_eq_true (P : α → Bool) (xs : List α) (init : Bool) :
    xs.foldl (fun acc x => acc && P x) init = true ↔
    init = true ∧ ∀ x ∈ xs, P x = true
```
**Purpose:** Boolean fold ↔ universal quantification
**Tag:** `#proven` `#boolean-fold` `#phase2-dv` `#gpt5-endorsed` `#recommend`
**Value:** ⭐⭐⭐⭐⭐ VERY HIGH
**When to use:** Phase 2.1 (`foldlVars_all` proof)
**GPT-5 quote:** "Reduce Boolean fold checks to simple ∀ proofs via `foldlVars_all`"

**This is EXACTLY the lemma we need!**

---

##### Theorem: `foldl_all₂` (Lines 151-170) ✅
```lean
theorem foldl_all₂ (P : α → β → Bool) (xs : List α) (ys : List β) :
    xs.foldl (fun acc x =>
      ys.foldl (fun acc' y => acc' && P x y) acc) true = true ↔
    ∀ x ∈ xs, ∀ y ∈ ys, P x y = true
```
**Purpose:** Nested boolean fold ↔ double quantification
**Tag:** `#proven` `#boolean-fold` `#phase2-dv` `#recommend`
**Value:** ⭐⭐⭐⭐⭐ VERY HIGH
**When to use:** Phase 2.1 (`foldlVars_all₂` proof) - This is DV exactly!

**This is the DV lemma we need!**

---

##### Theorem: `foldl_filterMap_eq` (Lines 172-196) ✅
```lean
theorem foldl_filterMap_eq {α β γ} (f : α → Option β) (g : γ → β → γ) (xs : List α) (init : γ) :
    xs.foldl (fun acc x => match f x with | none => acc | some y => g acc y) init =
    (xs.filterMap f).foldl g init
```
**Purpose:** Fold with filterMap fusion
**Tag:** `#proven` `#fold-theory`
**Value:** LOW - specialized

---

##### Theorem: `foldl_and_all` (Lines 198-213) ✅
```lean
theorem foldl_and_all (P : α → Bool) (xs : List α) :
    xs.foldl (fun acc x => acc && P x) true = true ↔
    ∀ x ∈ xs, P x = true
```
**Purpose:** Simplified version of `foldl_and_eq_true` (init = true)
**Tag:** `#proven` `#boolean-fold`
**Value:** MEDIUM - special case of above

---

**Boolean Fold Summary:**
- ⭐ `foldl_and_eq_true` - Phase 2.1 `foldlVars_all`
- ⭐ `foldl_all₂` - Phase 2.1 `foldlVars_all₂` (DV!)
- Both FULLY PROVEN
- These save us ~100-140 lines of proof in Phase 2!

---

#### 5. HashMap Lemmas (Lines 215-367) ✅ ALL PROVEN

All simple lemmas, all proven!

##### Theorem: `contains_insert_self` (Lines 215-217) ✅
```lean
theorem contains_insert_self {k : α} {v : β} {m : Std.HashMap α β} :
    (m.insert k v).contains k = true
```
**Tag:** `#proven` `#hashmap-theory`
**Value:** LOW - trivial, likely in Std

---

##### Theorem: `contains_mono_insert` (Lines 219-223) ✅
```lean
theorem contains_mono_insert {k k' : α} {v : β} {m : Std.HashMap α β}
    (h : m.contains k') :
    (m.insert k v).contains k' = true
```
**Tag:** `#proven` `#hashmap-theory`
**Value:** LOW - trivial

---

##### ...more HashMap lemmas (Lines 225-367)
**All proven, all trivial**
**Recommendation:** Only copy if we actually need them (likely in Std)

---

### KernelExtras.lean Summary

**High-value items to import:**
1. ⭐⭐⭐⭐⭐ `foldl_and_eq_true`, `foldl_all₂` (lines 144-170) - Phase 2 DV
2. ⭐⭐⭐⭐☆ mapM infrastructure (lines 97-175) - Phase 3 helpers
3. ⚠️ `dvOK_comp_sufficient` (lines 31-45) - Currently sorry, but good signature

**Items to skip:**
- HashMap lemmas (likely in Std)
- Trivial injectivity proofs
- Specialized fusion lemmas

**Estimated import value:** ~200-300 lines of proven lemmas (save ~250-350 lines of work)

---

## 📁 `codex_archive/Kernel_codex_version.lean` (155 KB backup)

**Purpose:** Full backup of Codex's modified Kernel.lean
**Status:** Contains structural errors (imports non-existent modules)
**Value:** LOW for direct use, MEDIUM for reference

**What to reference:**
- Any specific theorem Codex claimed to prove
- Alternative formulations of existing theorems
- Documentation/comments explaining approach

**What to avoid:**
- Importing the broken module structure
- Copying large blocks without understanding
- Trusting claimed status without verification

**Recommendation:** Only examine specific sections if needed

---

## 📁 `codex_archive/Verify_codex_version.lean` (48 KB backup)

**Purpose:** Full backup of Codex's modified Verify.lean
**Status:** Unknown integration with main codebase
**Value:** LOW - Verify/Proofs.lean is more valuable

**Recommendation:** Reference only if specific needs arise

---

## 📁 `codex_archive/*.md` (40+ Documentation Files)

**Overall Quality:** Mixed - some good summaries, many redundant
**Value:** LOW-MEDIUM - Mostly status reports

### Valuable Documentation Files

#### 1. `HONEST_FINAL_STATUS.md`
**Contents:** Axiom status, build status, next steps
**Value:** MEDIUM - Good summary of Codex's understanding
**Note:** Claims "BUILD SUCCESS" (false), but axiom list is accurate

#### 2. `PROOF_ROADMAP.md`
**Contents:** Strategic roadmap for completing proofs
**Value:** MEDIUM - Some good architectural insights
**Note:** Compare with our RECOVERY_AND_FORWARD_PLAN.md

#### 3. `AXIOM_STATUS_*.md` files
**Contents:** Detailed axiom reduction tracking
**Value:** LOW - We already know current axiom count (5)

#### 4. `SESSION_ACCOMPLISHMENTS.md`
**Contents:** What Codex claimed to accomplish
**Value:** LOW - Cannot verify claims (build was broken)

### Redundant Files (Can Ignore)

- `CURRENT_STATE.md` - Duplicate info
- `ENDGAME_STATUS.md` - Duplicate info
- `FINAL_SESSION_SUMMARY.md` - Duplicate info
- `SESSION_FINAL_STATUS.md` - Duplicate info
- 30+ other status files - Mostly redundant

**Recommendation:** Skim once for ideas, don't spend much time

---

## Quick Reference: What to Use When

### Phase 1: checkHyp + TypedSubst

**Must reference:**
1. `Verify/Proofs.lean:50-63` - `FloatBindWitness` structure
2. `Verify/Proofs.lean:467-619` - `checkHyp_preserves_HypProp` (template!)
3. `Verify/Proofs.lean:688-728` - Three domain theorems (our exact theorems!)

**Estimated reuse:** ~60-70% of proof structure

---

### Phase 2: DV Replacement

**Must reference:**
1. `KernelExtras.lean:144-149` - `foldl_and_eq_true` ✅ PROVEN
2. `KernelExtras.lean:151-170` - `foldl_all₂` ✅ PROVEN

**Estimated reuse:** ~100-140 lines (direct import!)

---

### Phase 3: Helper Lemmas

**Consider importing:**
1. `KernelExtras.lean:97-175` - mapM infrastructure ✅ ALL PROVEN
2. `Bridge/Basics.lean:30-48` - `floats`, `essentials` definitions
3. `Bridge/Basics.lean:121-143` - `floats_mem_floating` theorem ✅ PROVEN

**Estimated reuse:** ~100-150 lines

---

### Phase 3.2: Thin Bridge Introduction

**Recommended structure:**
1. `Bridge/Basics.lean:30-48` - `floats`, `essentials` (definitions only)
2. Consider: `Bridge/Basics.lean:11-15` - Alternative `TypedSubst` design
3. Place theorems in Verify, not Bridge

---

## Estimated Total Reuse Value

**Direct code reuse:** ~400-600 lines (proven lemmas)
**Structural templates:** ~200-300 lines (proof patterns)
**Design ideas:** ~100-150 lines (alternative approaches)

**Total value:** ~700-1050 lines of work saved

**As percentage of forward plan:** ~700-1050 / 1280-1730 = **40-60% of work**

---

## Golden Nuggets 💎 (Top 10)

In priority order:

1. **`checkHyp_preserves_HypProp`** (Verify/Proofs.lean:467-619) - 150-line template
2. **`FloatBindWitness` structure** (Verify/Proofs.lean:50-63) - Witness pattern
3. **Three domain theorems** (Verify/Proofs.lean:688-728) - Exact matches!
4. **`foldl_and_eq_true`** (KernelExtras.lean:144-149) - DV lemma 1
5. **`foldl_all₂`** (KernelExtras.lean:151-170) - DV lemma 2 (nested case)
6. **mapM infrastructure** (KernelExtras.lean:97-175) - 4 proven theorems
7. **`floats_mem_floating`** (Bridge/Basics.lean:121-143) - Bidirectional lemma
8. **`floats`/`essentials`** (Bridge/Basics.lean:30-48) - Clean API
9. **`checkHyp_image_exists`** (Verify/Proofs.lean:741-748) - Witness → typed
10. **Alternative `TypedSubst`** (Bridge/Basics.lean:11-15) - Design comparison

---

## How to Honor Codex's Work

### 1. Attribution in Code
When adapting Codex's work, add comments:
```lean
-- Structure adapted from Codex's FloatBindWitness (codex_archive/Verify/Proofs.lean:50-63)
structure FloatBindWitness ...

-- Proof strategy follows Codex's checkHyp_preserves_HypProp (codex_archive/Verify/Proofs.lean:467-619)
theorem checkHyp_master_invariant ...
```

### 2. Acknowledgment in Documentation
In final status report:
```markdown
## Contributors

**Claude (TypedSubst infrastructure):**
- KIT A & B: Typed substitution with witnesses
- Recovery and forward planning

**Codex (archived proof techniques):**
- checkHyp loop invariant template (150 lines)
- FloatBindWitness design pattern
- Boolean fold lemmas (DV reasoning)
- mapM utility infrastructure

**GPT-5 (strategic guidance):**
- Incremental build-first approach
- Thin Bridge architecture
- Phase-based execution plan
```

### 3. Preserve the Archive
Keep `codex_archive/` as permanent reference:
```bash
# Don't delete!
# Future developers can learn from both successes and mistakes
```

---

## Bottom Line

**Codex's theoretical work:** ⭐⭐⭐⭐☆ (4/5 stars)
**Codex's engineering:** ⭐☆☆☆☆ (1/5 stars)
**Net value:** **HIGH** (despite broken build)

**Key insight:** Separate ideas from execution
- Ideas: Loop invariants, witness patterns, boolean fold lemmas
- Execution: Broken module structure, false claims

**We can honor the good work while fixing the structural problems.**

---

**Date:** 2025-10-12
**Archive location:** `/home/zar/claude/hyperon/metamath/mm-lean4/codex_archive/`
**Status:** Complete catalog, ready for reference
**Next step:** Begin Phase 1 with Codex's templates as guide

---

**Remember:** Even unsuccessful experiments contain valuable insights! 🌟
