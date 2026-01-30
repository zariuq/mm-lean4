/-
Formal specification of Metamath proof verification - Public API.

This file serves as the main entry point for the Metamath specification.
It imports and re-exports all specification components:

1. **Core types** (Spec/Core.lean): Fundamental data structures
   - Symbols, expressions, hypotheses, frames
   - Substitutions and disjoint variable constraints
   - Assertion database

2. **Operational semantics** (Spec/Operational.lean): Stack machine execution
   - ProofStep, ProofValid: How proofs are checked
   - Provable: Operational definition of provability
   - Theorems connecting proof execution to provability

3. **Semantic layer** (future Spec/Semantic.lean): Mario's mathematical foundation
   - Will re-export Mario Carneiro's DeclarativeSpec.Provable
   - Bridge theorems proving operational ↔ semantic equivalence

This modular structure separates:
- **What** valid proofs are (Core types)
- **How** they're checked (Operational)
- **Why** they're correct (Semantic + bridge theorems)

Per Metamath Specification Chapter 4 (SPEC_SECTION_4.txt).
-/

-- Import all components
import Metamath.Spec.Core
import Metamath.Spec.Operational

-- Re-export everything for backward compatibility
namespace Metamath.Spec

-- Core types are already in Metamath.Spec namespace from Core.lean
-- Operational definitions are already in Metamath.Spec namespace from Operational.lean
-- This file just provides the unified import point

/-! ## Specification Completeness

This specification covers:
✅ Core syntax (expressions, hypotheses, frames)
✅ Substitution semantics
✅ Disjoint variable constraints (spec §4.2.5)
✅ Operational proof execution (spec §4.3)
✅ Provability definition (operational)
✅ Soundness statement

Future additions:
🔲 Semantic layer (Mario's Provable from DeclarativeSpec.lean)
🔲 Bridge theorems (Operational ↔ Semantic)
🔲 Invariant predicates (CreuSAT-style)

Not modeled (trusted components):
- Lexical analysis (printable ASCII, whitespace)
- File I/O and includes ($[...$])
- Compressed proof decoding
- Label scoping rules

These are validated by the type-safe implementation but not
formally verified. Per GPT-5's advice: focus on the core
verification kernel first.
-/

end Metamath.Spec
