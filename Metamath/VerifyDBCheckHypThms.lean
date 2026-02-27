import Metamath.Verify

namespace Metamath
namespace Verify
namespace DB

/-- Equation lemma: base case when `i ≥ hyps.size`. -/
@[simp] theorem checkHyp_base
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (h : ¬ i < hyps.size) :
  checkHyp db hyps stack off i σ = .ok σ := by
  unfold checkHyp
  simp [h]
  rfl

/-- Equation lemma when lookup at `hyps[i]` finds an **essential** hypothesis. -/
@[simp] theorem checkHyp_step_hyp_true
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (f : Formula) (lbl : String)
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp true f lbl)) :
  checkHyp db hyps stack off i σ
    =
  if !stack[off.1 + i]!.hasConstHead then
    .error (.proofCheck .stackFormulaNoConstantHead)
  else if !f.hasConstHead then
    .error (.proofCheck .hypothesisNoConstantHead)
  else if !formulaSymsRespectFrame db f (Frame.mk #[] hyps) then
    .error (.scopeDecl .hypothesisSymbolsNotInFrame)
  else if f[0]! == stack[off.1 + i]![0]! then
    match f.subst σ with
    | .ok s =>
        if s == stack[off.1 + i]! then
          checkHyp db hyps stack off (i+1) σ
        else
          .error (.proofCheck .typeErrorInSubstitution)
    | .error _ => .error (.proofCheck .typeErrorInSubstitution)
  else
    .error (.proofCheck
      (.badTypecodeInSubstitution
        s!"{hyps[i]}: {f} / {stack[off.1 + i]!}")) := by
  rw [checkHyp]
  simp [h_i, h_find, -beq_iff_eq]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx, -beq_iff_eq]
  rfl

/-- Equation lemma when lookup at `hyps[i]` finds a **float** hypothesis. -/
@[simp] theorem checkHyp_step_hyp_false
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (f : Formula) (lbl : String)
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp false f lbl)) :
  checkHyp db hyps stack off i σ
    =
  if !stack[off.1 + i]!.hasConstHead then
    .error (.proofCheck .stackFormulaNoConstantHead)
  else if !f.isFloatShape then
    .error (.scopeDecl .expectedConstantAndVariable)
  else if f[0]! == stack[off.1 + i]![0]! then
    if σ.contains f[1]!.value then
      .error (.proofCheck .duplicateFloatVariable)
    else
      checkHyp db hyps stack off (i+1) (σ.insert f[1]!.value (stack[off.1 + i]!))
  else
    .error (.proofCheck
      (.badTypecodeInSubstitution
        s!"{hyps[i]}: {f} / {stack[off.1 + i]!}")) := by
  rw [checkHyp]
  simp [h_i, h_find, -beq_iff_eq]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx, -beq_iff_eq]

end DB
end Verify
end Metamath
