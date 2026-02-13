namespace Metamath.Spec.Frontend

/-- Abstract parser-side state for `$d` symbol admissibility. -/
structure DjvarsState where
  isVar : String → Bool
  activeVarInScope : String → Bool

/-- A consistency condition for `$d` admissibility states. -/
def DjvarsState.WellFormed (st : DjvarsState) : Prop :=
  ∀ sym, st.activeVarInScope sym = true → st.isVar sym = true

/-- Structured `$d`-gate errors used by the front-end spec layer. -/
inductive DjvarsScopeError where
  | tokenNotVariable (sym : String)
  | tokenNotInScope (sym : String) (isVarWitness : Bool) (activeInScopeWitness : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Front-end `$d` admissibility rule (SS4.2.4): symbol is active as a variable. -/
def DjvarsSymbolAdmissible (st : DjvarsState) (sym : String) : Prop :=
  st.activeVarInScope sym = true

/-- Front-end `$d` rejection rule: symbol is not declared as a variable. -/
def DjvarsSymbolMissing (st : DjvarsState) (sym : String) : Prop :=
  st.isVar sym = false

/-- Gate-fact payload for `$d` token-not-in-scope diagnostics. -/
def DjvarsTokenNotInScopeGateFacts
    (isVarWitness : Bool) (activeInScopeWitness : Bool) : Prop :=
  isVarWitness = true ∧ activeInScopeWitness = false

/-- `$d` symbol gate from the front-end spec perspective. -/
def djvarsScopeViolation? (st : DjvarsState) (sym : String) : Option DjvarsScopeError :=
  if !st.isVar sym then
    some (.tokenNotVariable sym)
  else if !st.activeVarInScope sym then
    some (.tokenNotInScope sym true false)
  else
    none

/-- The `$d` gate is complete for front-end admissibility under state consistency. -/
theorem djvarsScopeViolation?_none_iff_djvarsSymbolAdmissible
    (st : DjvarsState) (sym : String)
    (h_wf : st.WellFormed) :
    djvarsScopeViolation? st sym = none ↔ DjvarsSymbolAdmissible st sym := by
  unfold djvarsScopeViolation? DjvarsSymbolAdmissible
  by_cases h_var_true : st.isVar sym = true
  · by_cases h_active_true : st.activeVarInScope sym = true
    · simp [h_var_true, h_active_true]
    · simp [h_var_true, h_active_true]
  · have h_var_false : st.isVar sym = false := by
      cases h_is : st.isVar sym with
      | false => simp
      | true => exact False.elim (h_var_true (by simp [h_is]))
    have h_active_false : st.activeVarInScope sym = false := by
      cases h_active : st.activeVarInScope sym with
      | false => simp
      | true =>
          have h_var_from_wf : st.isVar sym = true := h_wf sym (by simp [h_active])
          exact False.elim (by simp [h_var_false] at h_var_from_wf)
    simp [h_var_false, h_active_false]

/-- The `$d` gate reports `tokenNotVariable` exactly when symbol declaration fails. -/
theorem djvarsScopeViolation?_tokenNotVariable_iff_djvarsSymbolMissing
    (st : DjvarsState) (sym : String) :
    djvarsScopeViolation? st sym = some (.tokenNotVariable sym) ↔
      DjvarsSymbolMissing st sym := by
  unfold djvarsScopeViolation? DjvarsSymbolMissing
  by_cases h_var : st.isVar sym
  · simp [h_var]
  · simp [h_var]

/-- The `$d` gate reports `tokenNotInScope` exactly at the active-variable failure branch. -/
theorem djvarsScopeViolation?_tokenNotInScope_iff
    (st : DjvarsState) (sym : String) :
    djvarsScopeViolation? st sym = some (.tokenNotInScope sym true false) ↔
      st.isVar sym = true ∧ st.activeVarInScope sym = false := by
  unfold djvarsScopeViolation?
  by_cases h_var : st.isVar sym
  · by_cases h_active : st.activeVarInScope sym
    · simp [h_var, h_active]
    · simp [h_var, h_active]
  · simp [h_var]

/-- Abstract parser-side state for formula/math symbol admissibility. -/
structure MathSymbolState where
  isSym : String → Bool

/-- Structured formula/math-symbol gate errors in the front-end spec layer. -/
inductive MathSymbolError where
  | tokenNotConstantOrVariable (sym : String) (isSymWitness : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Front-end formula/math-symbol admissibility (`$e/$a/$p` tails). -/
def MathSymbolAdmissible (st : MathSymbolState) (sym : String) : Prop :=
  st.isSym sym = true

/-- Front-end formula/math-symbol rejection (`not const/var`). -/
def MathSymbolMissing (st : MathSymbolState) (sym : String) : Prop :=
  st.isSym sym = false

/-- Gate-fact payload for token-not-constant-or-variable diagnostics. -/
def MathSymbolGateFacts (isSymWitness : Bool) : Prop :=
  isSymWitness = false

/-- Formula/math-symbol gate from the front-end spec perspective. -/
def mathSymbolViolation? (st : MathSymbolState) (sym : String) : Option MathSymbolError :=
  if st.isSym sym then
    none
  else
    some (.tokenNotConstantOrVariable sym false)

/-- Formula/math-symbol gate completeness for front-end admissibility. -/
theorem mathSymbolViolation?_none_iff_mathSymbolAdmissible
    (st : MathSymbolState) (sym : String) :
    mathSymbolViolation? st sym = none ↔ MathSymbolAdmissible st sym := by
  unfold mathSymbolViolation? MathSymbolAdmissible
  by_cases h_sym : st.isSym sym
  · simp [h_sym]
  · simp [h_sym]

/-- Formula/math-symbol gate exact rejection characterization. -/
theorem mathSymbolViolation?_tokenNotConstantOrVariable_iff_mathSymbolMissing
    (st : MathSymbolState) (sym : String) :
    mathSymbolViolation? st sym = some (.tokenNotConstantOrVariable sym false) ↔
      MathSymbolMissing st sym := by
  unfold mathSymbolViolation? MathSymbolMissing
  by_cases h_sym : st.isSym sym
  · simp [h_sym]
  · simp [h_sym]

/-- Front-end include-policy flags needed by the include directive gate. -/
structure IncludePolicy where
  allowIncludeInnerScope : Bool
  allowTokenSplicing : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Structured include gate errors at the front-end spec layer. -/
inductive IncludeDirectiveError where
  | inInnerScope (pos : Nat) (scopeDepth : Nat) (inStatement : Bool)
      (allowIncludeInnerScopeWitness : Bool)
  | insideStatement (pos : Nat) (scopeDepth : Nat) (inStatement : Bool)
      (allowTokenSplicingWitness : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Front-end include admissibility predicate. -/
def IncludeDirectiveAdmissible
    (policy : IncludePolicy) (scopeDepth : Nat) (inStatement : Bool) : Prop :=
  (!policy.allowIncludeInnerScope && scopeDepth > 0) = false ∧
    (!policy.allowTokenSplicing && inStatement) = false

/-- Gate-fact payload for include-in-inner-scope diagnostics. -/
def IncludeInInnerScopeGateFacts
    (allowIncludeInnerScopeWitness : Bool) (scopeDepth : Nat) : Prop :=
  allowIncludeInnerScopeWitness = false ∧ scopeDepth ≠ 0

/-- Gate-fact payload for include-inside-statement diagnostics. -/
def IncludeInsideStatementGateFacts
    (allowTokenSplicingWitness : Bool) (inStatement : Bool) : Prop :=
  allowTokenSplicingWitness = false ∧ inStatement = true

/-- Include directive gate from the front-end spec perspective. -/
def includeDirectiveViolation?
    (policy : IncludePolicy) (scopeDepth : Nat) (inStatement : Bool)
    (pos : Nat) : Option IncludeDirectiveError :=
  if !policy.allowIncludeInnerScope && scopeDepth > 0 then
    some (.inInnerScope pos scopeDepth inStatement policy.allowIncludeInnerScope)
  else if !policy.allowTokenSplicing && inStatement then
    some (.insideStatement pos scopeDepth inStatement policy.allowTokenSplicing)
  else
    none

/-- Include gate completeness for front-end admissibility. -/
theorem includeDirectiveViolation?_none_iff_includeDirectiveAdmissible
    (policy : IncludePolicy) (scopeDepth : Nat) (inStatement : Bool) (pos : Nat) :
    includeDirectiveViolation? policy scopeDepth inStatement pos = none ↔
      IncludeDirectiveAdmissible policy scopeDepth inStatement := by
  unfold includeDirectiveViolation? IncludeDirectiveAdmissible
  by_cases h_inner : (!policy.allowIncludeInnerScope && scopeDepth > 0) = true
  · simp [h_inner]
  · by_cases h_stmt : (!policy.allowTokenSplicing && inStatement) = true
    · simp [h_inner, h_stmt]
    · simp [h_inner, h_stmt]

/-- Front-end state for top-level `$e` admissibility. -/
structure TopLevelEssState where
  rejectToplevelEss : Bool
  scopeDepth : Nat

/-- Structured top-level `$e` front-end error. -/
inductive TopLevelEssError where
  | topLevelEssentialNotAllowed (rejectToplevelEssWitness : Bool) (scopeDepthWitness : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Front-end top-level `$e` admissibility. -/
def TopLevelEssentialAdmissible (st : TopLevelEssState) : Prop :=
  (st.rejectToplevelEss && st.scopeDepth == 0) = false

/-- Gate-fact payload for strict top-level `$e` diagnostics. -/
def TopLevelEssentialGateFacts
    (rejectToplevelEssWitness : Bool) (scopeDepthWitness : Nat) : Prop :=
  rejectToplevelEssWitness = true ∧ scopeDepthWitness = 0

/-- Top-level `$e` gate from the front-end spec perspective. -/
def topLevelEssViolation? (st : TopLevelEssState) : Option TopLevelEssError :=
  if st.rejectToplevelEss && st.scopeDepth == 0 then
    some (.topLevelEssentialNotAllowed st.rejectToplevelEss st.scopeDepth)
  else
    none

/-- Top-level `$e` gate completeness for front-end admissibility. -/
theorem topLevelEssViolation?_none_iff_topLevelEssentialAdmissible
    (st : TopLevelEssState) :
    topLevelEssViolation? st = none ↔ TopLevelEssentialAdmissible st := by
  unfold topLevelEssViolation? TopLevelEssentialAdmissible
  by_cases h_gate : (st.rejectToplevelEss && st.scopeDepth == 0) = true
  · simp [h_gate]
  · simp [h_gate]

end Metamath.Spec.Frontend
