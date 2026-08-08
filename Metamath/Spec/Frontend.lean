namespace Metamath.Spec.Frontend

/-- Abstract parser-side state for `$d` symbol admissibility. -/
structure DjvarsState where
  /-- Is the symbol an *active* variable?  [MM §4.2.4] `$d` ranges over
  active variables; a name whose declaring block has closed is not one. -/
  isActiveVar : String → Bool

/-- Structured `$d`-gate errors used by the front-end spec layer. -/
inductive DjvarsScopeError where
  | tokenNotVariable (sym : String)
  deriving DecidableEq, Repr, Inhabited

/-- Front-end `$d` admissibility rule (SS4.2.4): the symbol is an active
variable.  `$d` requires an active `$v` declaration, NOT an active `$f`
hypothesis -- `$d` may legally precede the `$f` that types its variables. -/
def DjvarsSymbolAdmissible (st : DjvarsState) (sym : String) : Prop :=
  st.isActiveVar sym = true

/-- Front-end `$d` rejection rule: symbol is not declared as a variable. -/
def DjvarsSymbolMissing (st : DjvarsState) (sym : String) : Prop :=
  st.isActiveVar sym = false

/-- `$d` symbol gate from the front-end spec perspective. -/
def djvarsScopeViolation? (st : DjvarsState) (sym : String) : Option DjvarsScopeError :=
  if !st.isActiveVar sym then
    some (.tokenNotVariable sym)
  else
    none

/-- The `$d` gate is complete for front-end admissibility. -/
theorem djvarsScopeViolation?_none_iff_djvarsSymbolAdmissible
    (st : DjvarsState) (sym : String) :
    djvarsScopeViolation? st sym = none ↔ DjvarsSymbolAdmissible st sym := by
  unfold djvarsScopeViolation? DjvarsSymbolAdmissible
  by_cases h_var : st.isActiveVar sym
  · simp [h_var]
  · simp [h_var]

/-- The `$d` gate reports `tokenNotVariable` exactly when symbol declaration fails. -/
theorem djvarsScopeViolation?_tokenNotVariable_iff_djvarsSymbolMissing
    (st : DjvarsState) (sym : String) :
    djvarsScopeViolation? st sym = some (.tokenNotVariable sym) ↔
      DjvarsSymbolMissing st sym := by
  unfold djvarsScopeViolation? DjvarsSymbolMissing
  by_cases h_var : st.isActiveVar sym
  · simp [h_var]
  · simp [h_var]

/-- Abstract parser-side state for formula/math symbol admissibility.

Consistency facts this abstract state does *not* enforce — that a name is not
both constant and variable, and that an active variable is a declared one — are
taken as explicit hypotheses where they are needed, and discharged at the bridge
from the real registry lookup.

[MM §4.2.2] Occurrence in a math string requires an *active* symbol.  Constants
may only be declared in the outermost block, so a declared constant is always
active and `isConst` suffices for them; variables are block-scoped, so they need
`isActiveVar`.  `isVar` is retained so the two rejections stay distinguishable:
a name that was never declared is a different fault from a declared variable
whose block has been popped. -/
structure MathSymbolState where
  isConst : String → Bool
  isVar : String → Bool
  isActiveVar : String → Bool

/-- Structured formula/math-symbol gate errors in the front-end spec layer. -/
inductive MathSymbolError where
  | tokenNotConstantOrVariable (sym : String) (isSymWitness : Bool)
  | inactiveMathSymbol (sym : String)
  deriving DecidableEq, Repr, Inhabited

/-- Front-end formula/math-symbol admissibility (`$f/$e/$a/$p` tails): an active
constant or an active variable. -/
def MathSymbolAdmissible (st : MathSymbolState) (sym : String) : Prop :=
  st.isConst sym = true ∨ st.isActiveVar sym = true

/-- Front-end formula/math-symbol rejection: the name is neither a constant nor
a variable, i.e. it was never declared at all. -/
def MathSymbolMissing (st : MathSymbolState) (sym : String) : Prop :=
  st.isConst sym = false ∧ st.isVar sym = false

/-- Front-end formula/math-symbol rejection: the name *is* a declared variable,
but the block that declared it has been popped. -/
def MathSymbolInactive (st : MathSymbolState) (sym : String) : Prop :=
  st.isVar sym = true ∧ st.isActiveVar sym = false

/-- Gate-fact payload for token-not-constant-or-variable diagnostics. -/
def MathSymbolGateFacts (isSymWitness : Bool) : Prop :=
  isSymWitness = false

/-- Formula/math-symbol gate from the front-end spec perspective. -/
def mathSymbolViolation? (st : MathSymbolState) (sym : String) : Option MathSymbolError :=
  if st.isConst sym then
    none
  else if st.isActiveVar sym then
    none
  else if st.isVar sym then
    some (.inactiveMathSymbol sym)
  else
    some (.tokenNotConstantOrVariable sym false)

/-- Formula/math-symbol gate completeness for front-end admissibility. -/
theorem mathSymbolViolation?_none_iff_mathSymbolAdmissible
    (st : MathSymbolState) (sym : String) :
    mathSymbolViolation? st sym = none ↔ MathSymbolAdmissible st sym := by
  unfold mathSymbolViolation? MathSymbolAdmissible
  by_cases h_c : st.isConst sym <;> by_cases h_a : st.isActiveVar sym <;>
    by_cases h_v : st.isVar sym <;> simp [h_c, h_a, h_v]

/-- Formula/math-symbol gate exact rejection characterization: never declared. -/
theorem mathSymbolViolation?_tokenNotConstantOrVariable_iff_mathSymbolMissing
    (st : MathSymbolState) (sym : String)
    (h_active_declared : st.isActiveVar sym = true → st.isVar sym = true) :
    mathSymbolViolation? st sym = some (.tokenNotConstantOrVariable sym false) ↔
      MathSymbolMissing st sym := by
  unfold mathSymbolViolation? MathSymbolMissing
  by_cases h_c : st.isConst sym <;> by_cases h_a : st.isActiveVar sym <;>
    by_cases h_v : st.isVar sym <;> simp_all

/-- Formula/math-symbol gate exact rejection characterization: declared but the
declaring block has been popped. -/
theorem mathSymbolViolation?_inactiveMathSymbol_iff_mathSymbolInactive
    (st : MathSymbolState) (sym : String)
    (h_const_not_var : st.isConst sym = true → st.isVar sym = false) :
    mathSymbolViolation? st sym = some (.inactiveMathSymbol sym) ↔
      MathSymbolInactive st sym := by
  unfold mathSymbolViolation? MathSymbolInactive
  by_cases h_c : st.isConst sym <;> by_cases h_a : st.isActiveVar sym <;>
    by_cases h_v : st.isVar sym <;> simp_all

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
