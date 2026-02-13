/-
Formal specification of Metamath proof verification - Public API.

This file serves as the main entry point for the Metamath specification.
It imports and re-exports the specification components:

1. Core types (`Spec/Core.lean`): fundamental data structures
2. Operational semantics (`Spec/Operational.lean`): proof-step execution rules
3. Front-end gate rules (`Spec/Frontend.lean`): parser-facing policy/spec predicates

This modular structure separates:
- what valid proofs are (core)
- how proofs are checked (operational)
- which front-end gate conditions are admitted/rejected (front-end)

Per Metamath Specification Chapter 4 (`SPEC_SECTION_4.txt`).
-/

import Metamath.Spec.Core
import Metamath.Spec.Operational
import Metamath.Spec.Frontend

namespace Metamath.Spec

/-! ## Specification Completeness

This specification currently covers:
- Core syntax (expressions, hypotheses, frames)
- Substitution semantics
- Disjoint variable constraints (spec SS4.2.5)
- Operational proof execution (spec SS4.3)
- Front-end gate predicates for `$d`, include directives, and top-level `$e`

Still pending for full parser-level completeness:
- Full lexical model (printable ASCII/tokenization)
- Complete include I/O semantics
- Full statement-parser soundness/completeness bridge
- Compressed-proof front-end normalization model
-/

end Metamath.Spec
