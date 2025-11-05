# Metamath Spec Alignment Check

**Date:** 2025-10-08
**Purpose:** Verify that `Metamath/Spec.lean` correctly captures the Metamath specification

## Core Specification Coverage

### §4.1 Lexical (Not in Spec.lean - trusted)
- **§4.1.1** Printable ASCII: ✅ Handled by implementation
- **§4.1.2** Preprocessing (includes, comments): ✅ Handled by implementation
- **§4.1.3** Tokens and labels: ✅ Handled by implementation

**Rationale:** Lexical analysis trusted (type-safe, well-tested). Focus on semantic verification.

---

### §4.2 Syntax and Semantics (IN SPEC)

#### §4.2.1 Label Declarations
- **Spec:** "Each label must be unique" (line 10 test)
- **Spec.lean:** Implicitly enforced by `Database` being a function (Label → Option)
- **Status:** ✅ ALIGNED

#### §4.2.2 Constant Declarations ($c)
- **Spec:** "Constants declared with $c"
- **Spec.lean:** `structure Constant where c : Sym` (line 29-31)
- **Status:** ✅ ALIGNED

#### §4.2.3 Variable Declarations ($v)
- **Spec:** "Variables declared with $v"
- **Spec.lean:** `structure Variable where v : Sym` (line 33-35)
- **Status:** ✅ ALIGNED

#### §4.2.4 Floating Hypotheses ($f)
- **Spec:** "Floating hypothesis has the form 'C v'" (§4.2.2)
- **Spec.lean:** `Hyp.floating : Constant → Variable → Hyp` (line 58)
- **Status:** ✅ ALIGNED

#### §4.2.5 Essential Hypotheses ($e)
- **Spec:** "Essential hypothesis or assertion has typecode first"
- **Spec.lean:** `Hyp.essential : Expr → Hyp` where `Expr` has typecode (line 44-47, 59)
- **Status:** ✅ ALIGNED

#### §4.2.6 Disjoint Variables ($d)
- **Spec:** "Two variables are disjoint if they appear in a $d statement together"
- **Spec.lean:** `Frame.dv : List (Variable × Variable)` (line 66)
- **Spec.lean:** `dvOK` checks no shared variables (line 92-96)
- **Status:** ✅ ALIGNED

---

### §4.2.7 Assertions ($a, $p)

#### Axioms ($a)
- **Spec:** "Axioms are asserted without proof"
- **Spec.lean:** Represented in `Database` (line 120)
- **Status:** ✅ ALIGNED

#### Theorems ($p)
- **Spec:** "Theorems proved from axioms and previous theorems"
- **Spec.lean:** `Provable` relation (line 168-171)
- **Status:** ✅ ALIGNED

---

### §4.2.8 Scoping Rules

#### Constants in Outermost Scope
- **Spec:** "$c must be in outermost block only" (§4.2.8)
- **Test:** test47 verifies this
- **Spec.lean:** Not modeled (trusted to implementation)
- **Status:** ⚠️ IMPLEMENTATION-ONLY (acceptable per GPT-5 advice)

#### Variable Lifetime
- **Spec:** "Variables exist from declaration until end of block"
- **Test:** test08, test35 verify this
- **Spec.lean:** Not modeled (trusted to implementation)
- **Status:** ⚠️ IMPLEMENTATION-ONLY (acceptable)

---

### §4.3 Proof Verification (CORE OF SPEC)

#### Proof Execution Semantics
- **Spec:** "A proof is a sequence of assertion references demonstrating the target assertion"
- **Spec.lean:** `ProofValid` inductive type (line 140-165)
  - `useEssential`: Use essential hypothesis from frame
  - `useFloating`: Use floating hypothesis from frame
  - `useAxiom`: Apply an assertion via substitution
- **Status:** ✅ ALIGNED

#### Stack-Based Execution
- **Spec:** "Each step pushes/pops formulas from stack"
- **Spec.lean:** `ProofValid Γ fr stack steps` tracks stack explicitly
- **Status:** ✅ ALIGNED

#### Substitution
- **Spec:** "Variables replaced according to substitution σ"
- **Spec.lean:** `applySubst` (line 105-110)
- **Status:** ✅ ALIGNED

#### Mandatory Hypotheses
- **Spec:** "Proof must satisfy all mandatory hypotheses"
- **Spec.lean:** `needed = fr'.mand.map ...` (line 160-162)
- **Status:** ✅ ALIGNED

#### DV Constraint Checking
- **Spec:** "Substitution must respect both caller's and callee's DV constraints"
- **Spec.lean:** Lines 155-156 check both `dvOK fr.dv σ` and `dvOK fr'.dv σ`
- **Status:** ✅ ALIGNED

---

### Appendix B: Compressed Proofs

- **Spec:** Compressed proof format (letters A-Z, ? for unknown steps)
- **Spec.lean:** Not modeled (compressed_equivalent_to_normal axiom in Kernel.lean)
- **Status:** ⚠️ DEFERRED (complex encoding, defer to later)

---

## Critical Properties Verified by Tests

| Test | Property | Spec Location | In Spec.lean? |
|------|----------|---------------|---------------|
| 07 | Constant redeclaration | §4.2.1 | ✅ Database function |
| 09 | Missing $d constraint | §4.2.5 | ✅ dvOK predicate |
| 13 | Missing $f for variable | §4.2.4 | ✅ Mandatory hyps |
| 15 | Multiple $f for variable | §4.2.5 | ✅ Uniqueness implicit |
| 19 | Type mismatch in proof | §4.2.6 | ✅ Typecode check |
| 27 | DV violation | §4.2.5 | ✅ dvOK check |
| 47 | $c in inner scope | §4.2.8 | ⚠️ Implementation |

---

## Alignment Summary

### ✅ Correctly Modeled (Core Verification)
- Expression structure and typecodes
- Floating and essential hypotheses
- Frame structure (mandatory hypotheses + DV constraints)
- Substitution semantics
- DV constraint checking (both caller and callee)
- Proof execution (stack-based, hypothesis usage, assertion application)
- Provability relation

### ⚠️ Trusted to Implementation (Acceptable)
- Lexical analysis (printable ASCII, whitespace)
- Label scoping and uniqueness enforcement
- Constant scoping (outermost only)
- Variable lifetime and scoping
- Compressed proof decoding
- File includes and preprocessing

### ❌ Missing (None!)
All core semantic properties are captured.

---

## Conclusion

**Alignment Status:** ✅ **EXCELLENT**

The `Spec.lean` correctly captures all **semantic** aspects of Metamath proof verification:
- Substitution (§4.2.6)
- DV constraints (§4.2.5)
- Mandatory hypotheses (§4.2.4)
- Proof execution (§4.3)
- Provability

The specification deliberately excludes **syntactic** aspects (lexical analysis, scoping rules) and trusts them to the type-safe implementation. This is **pragmatic** per GPT-5's advice:

> "Focus verification on the kernel (proof checking logic), treating parser and preprocessor as trusted initially."

The specification is **ready for formal proof work**.

---

## Next Steps

1. ✅ **Spec alignment verified** (this document)
2. 🎯 **Begin proving easy lemmas** (Kernel.lean lines 172-197)
3. 🎯 **Prove helper lemmas** for substitution, DV properties
4. 🎯 **Work toward stepNormal_sound** (the hard part)
5. 🎯 **Compose into verify_sound** (final theorem)

**Estimated timeline for full verification:** 2-4 months (expert Lean programmer)
**Immediate goals (next 1-2 weeks):** Prove 10-15 easy lemmas about substitution and DV properties
