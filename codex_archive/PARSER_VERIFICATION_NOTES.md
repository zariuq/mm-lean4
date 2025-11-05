# Parser Verification - Ideas for Future Work

**Status:** DEFERRED - Not blocking MVP
**Priority:** Optional enhancement after kernel verification complete
**Effort Estimate:** 2-4 weeks

---

## Key Insight: Round-Trip Validation

**The elegant approach (user's idea):**
```lean
def DB.toMMString (db : Verify.DB) : String := ...

theorem round_trip_validates :
  parseMMFile s = some db →
  parseMMFile (db.toMMString) = some db' →
  db ≅ db'  -- Equivalent modulo whitespace

-- Test on all 42 test files:
for each test: assert (parse ∘ serialize ∘ parse) ≈ id
```

**Why this is brilliant:**
- Validates parser correctness empirically
- Catches most bugs via testing
- Much simpler than full formal verification
- Well-known technique (compilers, serialization, databases)

**Implementation:** 2-3 days, not blocking MVP

---

## Verified Parser Resources (GPT-5 Research)

### 1. Lean 4 PEG Parser Generator (Best Exemplar)
**Source:** https://project-archive.inf.ed.ac.uk/ug4/20233645/ug4_proj.pdf
**What:** Undergraduate project - formalized extensible grammars in Lean 4
**Useful for:**
- PEG parser generator with proved termination/determinism
- Patterns for stating parser invariants
- Totality proofs for grammars

**Key takeaway:** Can model Metamath's simple grammar as PEG

### 2. Lean's Parser Infrastructure
**Source:** https://leanprover-community.github.io/mathlib4_docs/Lean/Parser/Basic.html
**What:** Lean's own recursive-descent memoizing parser
**Status:** Not mechanically verified, but well-documented
**Useful for:**
- API patterns
- Combinator structure
- Engineering cues

### 3. Verified Regex in Lean (mathlib)
**Source:** https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/RegularExpressions.html
**What:** Verified regex engine with correctness proofs
**Useful for:**
- Tokenizer verification blueprint
- Connecting recognizers to languages
- Two algorithms with soundness proofs

**Key takeaway:** Can verify the tokenizer using similar techniques

### 4. TRX - Verified PEG Interpreter (Coq)
**Source:** https://lmcs.episciences.org/686
**What:** Mature verified PEG interpreter in Coq
**Useful for:**
- Soundness/completeness specifications
- Parser/grammar relation patterns
- Methods translate to Lean

**Key takeaway:** Mature reference for formal parser verification

---

## Two Pragmatic Routes

### Route A: Checker-First (Fastest - Current Plan)
```lean
-- Keep current trust boundary
axiom tokenize : String → List Token
axiom parse : List Token → Option Verify.DB

-- Implement validated checker
def checkPreprocessInvariants (db : Verify.DB) : Bool := ...

-- Prove bridge
theorem preprocess_ok_implies_WF :
  checkPreprocessInvariants db = true → WF db

-- Top-level
theorem mm_file_sound :
  parse (tokenize s) = some db →
  checkPreprocessInvariants db →
  Verify.verify db label f proof = .ok →
  Spec.Provable ...
```

**Trust boundary:**
- Lean type checker
- File I/O
- Tokenizer + parser (~200 LOC, auditable)
- **Validated by round-tripping on test suite**

**Effort:** Current plan (MVP)

### Route B: PEG-Style Verified Parser (Deeper)
```lean
-- Model Metamath grammar as PEG
inductive MMGrammar where
  | statement : MMGrammar
  | constant : MMGrammar
  | variable : MMGrammar
  | axiom : MMGrammar
  | proof : MMGrammar
  ...

-- Verified parser
def parseMMFile (s : String) : Option Verify.DB :=
  -- Follow Lean 4 PEG project patterns
  ...

-- Prove properties
theorem parser_terminates : ...
theorem parser_deterministic : ...

theorem parser_correct :
  parseMMFile s = some db →
  WellFormedTokens db ∧
  CorrectScopeStructure db ∧
  RoundTrips db

-- Top-level (minimal trust)
theorem mm_string_sound :
  parseMMFile fileContents = some db →
  Verify.verify db label f proof = .ok →
  Spec.Provable ...
```

**Trust boundary:**
- Lean type checker
- File I/O only

**Effort:** 2-4 weeks (after MVP)

---

## Metamath Grammar (Simple!)

**Why Metamath is easier than most languages:**

```
Token := Label | MathSymbol | $c | $v | $f | $e | $d | $a | $p | $. | $( | $)

Statement :=
  | $c Token+ $.                    -- constant
  | $v Token+ $.                    -- variable
  | Label $f Token Token $.         -- floating
  | Label $e Token+ $.              -- essential
  | ${ Statement* $}                -- block
  | Label $d Token Token $.         -- disjoint
  | Label $a Token+ $.              -- axiom
  | Label $p Token+ $= Proof $.     -- provable

Proof := Label* | ( Label* )       -- normal or compressed
```

**Grammar properties:**
- Context-free (actually regular for most parts)
- No operator precedence
- No left-recursion
- Simple scoping (just blocks)

**This simplicity makes verification tractable!**

---

## Minimal Trusted Lexer (~50 LOC)

**What actually needs trust:**
```lean
def classifyToken (s : String) : Token :=
  if s == "$c" then Token.constant
  else if s == "$v" then Token.variable
  else if s == "$f" then Token.floating
  else if s == "$e" then Token.essential
  else if s == "$d" then Token.disjoint
  else if s == "$a" then Token.axiom
  else if s == "$p" then Token.provable
  else if s == "$." then Token.terminator
  else if s == "${" then Token.blockOpen
  else if s == "$}" then Token.blockClose
  else if s == "$(" then Token.commentOpen
  else if s == "$)" then Token.commentClose
  else Token.symbol s

def tokenize (s : String) : List Token :=
  s.splitOn.filter (· != "").map classifyToken
```

**This is auditable by inspection!**

---

## Implementation Priority (After MVP)

**Phase 1: Round-Trip Validation (2-3 days)**
1. Implement `DB.toMMString` serializer
2. Add round-trip tests to test suite
3. Validate on all 42 test files

**Phase 2: Checker Verification (1 week)**
1. Formalize `checkPreprocessInvariants`
2. Prove `preprocess_ok_implies_WF`
3. Update top-level soundness theorem

**Phase 3: Parser Verification (Optional, 2-4 weeks)**
1. Study Lean 4 PEG project patterns
2. Model Metamath grammar formally
3. Prove parser correctness
4. Replace axiomatized parser with verified one

**Each phase is independent and optional!**

---

## Key Decisions

### For MVP (Current Plan):
- ✅ Trust tokenizer + parser (~200 LOC)
- ✅ Implement `checkPreprocessInvariants` + prove bridge to WF
- ✅ Validate via testing (existing 42 tests)
- ✅ Explicit trust boundary documented

### After MVP (Optional Enhancements):
- 🔄 Add round-trip validation (high confidence, low effort)
- 🔄 Verify parser using PEG approach (minimal trust boundary)
- 🔄 Verify tokenizer using regex approach (truly minimal TCB)

---

## Notes to Self

**Don't forget:**
1. Round-trip validation is the pragmatic sweet spot
2. Metamath grammar is simpler than most languages → tractable
3. Lean 4 PEG project is the best exemplar in ecosystem
4. Verified regex in mathlib is blueprint for tokenizer
5. This is NOT blocking MVP - defer until kernel done!

**Current priority:**
- Prove 22 axioms (1-2 weeks)
- Prove verify_impl_sound (Step 5, 1 session)
- **Then** consider parser enhancements

**Trust boundary for MVP:**
```
┌─────────────────────────────────────────┐
│ Trusted (auditable)                     │
│ - Lean type checker                     │
│ - File I/O                              │
│ - Tokenizer (~50 LOC)                   │
│ - Parser (~150 LOC)                     │
│ - Validated by tests                    │
└─────────────────────────────────────────┘
           ↓ (parse)
┌─────────────────────────────────────────┐
│ Checked (checkPreprocessInvariants)     │
│ - Scoping rules                         │
│ - Declaration validity                  │
│ - Syntactic well-formedness             │
└─────────────────────────────────────────┘
           ↓ (WF bridge)
┌─────────────────────────────────────────┐
│ VERIFIED (Lean proofs)                  │
│ - Spec soundness (stepNormal_sound)     │
│ - Bridge (stepNormal_impl_correct)      │
│ - Implementation (verify_impl_sound)    │
└─────────────────────────────────────────┘
```

---

**Status:** Ideas captured. Moving on to axiom proofs! 🚀
