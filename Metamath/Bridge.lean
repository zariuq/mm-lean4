/-
Bridge Module: Root Import

This module provides the thin bridge layer between Spec and Kernel.

**Purpose:** Connect specification (Spec.lean) to implementation verification (Kernel.lean)
without complex proofs. All verification theorems remain in Kernel.lean.

**Design principle:** Bridge is a "definition-only" layer.
- Type definitions (TypedSubst)
- Helper functions (floats, essentials, needed)
- Simple extraction lemmas

**Usage:**
```lean
import Metamath.Bridge

open Metamath.Bridge

-- Use TypedSubst for typed substitutions
def mySubst : TypedSubst myFrame := ...

-- Use helper functions
let floatHyps := floats myFrame
let essHyps := essentials myFrame
let neededStack := needed vars myFrame σ
```

**Status:** Phase 3 - Core infrastructure complete
-/

import Metamath.Bridge.Basics

/-!
## Module Structure

```
Metamath/
├── Spec.lean           -- Specification (already exists)
├── Verify.lean         -- Implementation (already exists)
├── Bridge/
│   └── Basics.lean     -- TypedSubst + helpers (NEW!)
├── Bridge.lean         -- This file (NEW!)
└── Kernel.lean         -- Verification theorems (will import Bridge)
```

## What Bridge Provides

From Bridge/Basics.lean:
- `TypedSubst fr` - Frame-specific typed substitution
- `floats fr` - Extract floating hypotheses
- `essentials fr` - Extract essential hypotheses
- `needOf vars σ h` - Apply substitution to hypothesis
- `needed vars fr σ` - Compute needed stack elements
- Simple lemmas (floats_complete/sound, essentials_complete/sound, needed_length)

## What Bridge Does NOT Provide

Complex proofs remain in Kernel.lean:
- `toSubstTyped` implementation (uses checkHyp_produces_typed_coverage)
- `checkHyp_produces_TypedSubst` theorem (integration)
- Main verification theorems
- stepAssert updates

## Design Rationale

**Why a separate module?**
1. Clear separation: definitions vs. proofs
2. Easier to understand: thin interface layer
3. Follows best practices: keep verification separate from definitions
4. Matches Codex architecture: Bridge was a separate module

**Why keep proofs in Kernel?**
1. Verification theorems need checkHyp infrastructure
2. Complex proofs belong with their dependencies
3. Bridge stays simple and maintainable
4. No circular dependencies

## Next Steps

To complete Phase 3:
1. ✅ Create Bridge module (DONE!)
2. ⏰ Update Kernel.lean to import Bridge
3. ⏰ Add toSubstTyped to Kernel.lean
4. ⏰ Prove checkHyp_produces_TypedSubst
5. ⏰ Update stepAssert to use TypedSubst
6. ⏰ Complete main verification theorem

**Estimated remaining:** ~150-200 lines of Kernel.lean updates
-/
