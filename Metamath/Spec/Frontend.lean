namespace Metamath.Spec.Frontend

/-- Abstract parser-side state for `$d` symbol admissibility. -/
structure DjvarsState where
  isVar : String → Bool

/-- Structured `$d`-gate errors used by the front-end spec layer. -/
inductive DjvarsScopeError where
  | tokenNotVariable (sym : String)
  deriving DecidableEq, Repr, Inhabited

/-- Front-end `$d` admissibility rule (SS4.2.4): symbol is declared as a variable.
Per the Metamath spec, `$d` statements only require that symbols are declared
via `$v`, NOT that they have active `$f` hypotheses. -/
def DjvarsSymbolAdmissible (st : DjvarsState) (sym : String) : Prop :=
  st.isVar sym = true

/-- Front-end `$d` rejection rule: symbol is not declared as a variable. -/
def DjvarsSymbolMissing (st : DjvarsState) (sym : String) : Prop :=
  st.isVar sym = false

/-- `$d` symbol gate from the front-end spec perspective. -/
def djvarsScopeViolation? (st : DjvarsState) (sym : String) : Option DjvarsScopeError :=
  if !st.isVar sym then
    some (.tokenNotVariable sym)
  else
    none

/-- The `$d` gate is complete for front-end admissibility. -/
theorem djvarsScopeViolation?_none_iff_djvarsSymbolAdmissible
    (st : DjvarsState) (sym : String) :
    djvarsScopeViolation? st sym = none ↔ DjvarsSymbolAdmissible st sym := by
  unfold djvarsScopeViolation? DjvarsSymbolAdmissible
  by_cases h_var : st.isVar sym
  · simp [h_var]
  · simp [h_var]

/-- The `$d` gate reports `tokenNotVariable` exactly when symbol declaration fails. -/
theorem djvarsScopeViolation?_tokenNotVariable_iff_djvarsSymbolMissing
    (st : DjvarsState) (sym : String) :
    djvarsScopeViolation? st sym = some (.tokenNotVariable sym) ↔
      DjvarsSymbolMissing st sym := by
  unfold djvarsScopeViolation? DjvarsSymbolMissing
  by_cases h_var : st.isVar sym
  · simp [h_var]
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
