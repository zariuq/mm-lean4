# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Metamath Lean 4 Verifier Soundness Proof** - A formal verification in Lean 4 that the Metamath proof checker correctly validates mathematical theorems. This is a bottom-up architecture implementing the verifier from first principles, with each phase proving the previous layer correct.

**Key Achievement**: A mathematically sound proof checker implementation with formal soundness theorem (`verify_impl_sound`) connecting runtime behavior to mathematical validity.

# Formalization Rules

- Always prove that which can be proven without using axioms.  No exceptions.
- Build a solid foundation of concretely proven theorems/lemmas (instead of writing proof sketches with sorries and moving on).
- Clean code invariants: zero warnings (beyond sorries), zero axioms, zero errors.

# Help

- Consult **how-to-lean-batteries.md** when needing help with Lean formalizations (batteries-only, no mathlib).
- Upgrade how-to-lean-batteries.md when learning something new.
- Legacy: how-to-lean.md (kept for compatibility)


## Build & Test Commands

### Resource limits (recommended for Lean builds)
```bash
ulimit -Sv 6291456        # 6GB memory cap
export LAKE_JOBS=3        # limit parallel jobs (CPU usage)
```

### Build the project
```bash
nice -n 19 lake build
```

### Build specific modules
```bash
nice -n 19 lake build Metamath.Verify           # Parser implementation
nice -n 19 lake build Metamath.KernelClean      # Main soundness proof
nice -n 19 lake build Metamath.ParserInvariants # Parser correctness theorems
```

### Check a single file for errors (without building dependencies)
```bash
nice -n 19 lean /path/to/file.lean
```

### Run the verifier executable
```bash
lake build validateDB
./.lake/build/bin/validateDB
```

### Run verification tests
```bash
lake build testParserInvariants
./.lake/build/bin/testParserInvariants
```

**What are verification tests?** Executable tests that check whether the implementation maintains the properties we're formally proving. See [Verification Testing in how-to-lean-batteries.md](how-to-lean-batteries.md#verification-testing) for details.

### View build warnings/errors
```bash
lake build 2>&1 | grep -E "^(error|warning):" | head -20
```

## Documentation Roadmap

**Status**: Build green; sorries remain. Use `rg` or `BLOCKING_SORRIES.md` for current list.

### Essential Documentation (read these!)

1. **[README.md](README.md)** - Project overview, quick start, current status
2. **[NEXT_STEPS.md](NEXT_STEPS.md)** - Clear path to completion with detailed strategies
3. **[BLOCKING_SORRIES.md](BLOCKING_SORRIES.md)** - Technical deep dive on each remaining sorry
4. **[CURRENT_STATUS.md](CURRENT_STATUS.md)** - Consolidated project status and metrics
5. **[how-to-lean-batteries.md](how-to-lean-batteries.md)** - Lean proof tactics reference (batteries-only)

### Supporting Documentation

- **[COMPLETION_ROADMAP.md](COMPLETION_ROADMAP.md)** - Strategic completion plan
- **[DEAD_CODE_CATALOG.md](DEAD_CODE_CATALOG.md)** - What was cleaned up and why
- **[WEEKS_STUCK_ROOT_CAUSE.md](WEEKS_STUCK_ROOT_CAUSE.md)** - Critical debugging insights

### Historical Documentation

See `docs_archive/` for ~80 archived files (session summaries, phase completions, historical analysis).

**Documentation cleanup (2025-12-13)**: Reduced from 100+ markdown files to 9 essential documents. All historical info preserved in docs_archive/.

## Architecture Overview

### What's Complete vs Incomplete

**Complete ✅**:
- Core specification and runtime implementation
- Bridge layer (dvOK_implies_DJ_subst fully proven, 150 LOC)
- Substitution correspondence (subst_correspondence fully proven)
- Step soundness (float/essential/assert lemmas proven)
- Main theorem for normal proofs (verify_impl_sound proven)
- All infrastructure lemmas (DBLemmas, KernelExtras, ArrayListExt)

**Incomplete ⚠️** (KernelClean sorries remain; use `rg` for exact list):
- `checkHyp_loop_alignment` - k = i case(s)
- `compressed_proof_sound`
- `verify_compressed_sound`

**Optional** (ParserInvariants sorries remain):
- Parser correctness is a separate concern; kernel uses these lemmas as inputs

### Layer Structure (Bottom-Up)

The project uses a **phased bottom-up architecture** where each layer depends only on lower layers:

**Phase 1: Core Specifications** (`Metamath.Spec`)
- Formal definition of Metamath proof state and validity
- What the verifier should achieve mathematically

**Phase 2: Runtime Implementation** (`Metamath.Verify`)
- Byte-level parser (feed function, feedTokens)
- Database operations (insertHyp, checkHyp)
- Proof checker state machine
- **Critical fact**: Feed processes bytes with error monotonicity (error once set never clears)

**Phase 3: Parser Correctness** (`Metamath.ParserInvariants`)
- **What's proven**: Parser success implies well-formed objects in database
- Float hypothesis structure: size=2, first element is const, second is var
- Float hypothesis uniqueness: no two floats bind same variable
- **Key blocking lemma**: `feedTokens_is_only_float_source` - proves floats can ONLY be added via feedTokens.float case

**Phase 4: Bridge Functions** (`Metamath.Spec.Bridge`)
- Conversion from runtime DB representation to specification frames
- Pattern extraction from Metamath objects
- **Key achievement**: dvOK_implies_DJ_subst FULLY PROVEN (150 LOC, lines 1358-1507)

**Phase 5-8: Kernel Soundness** (`Metamath.KernelClean`)
- Stepwise proof that each verifier operation maintains mathematical soundness
- Main theorem: `verify_impl_sound` - proves parser success implies valid theorem
- **Status**: Sorries remain; see `BLOCKING_SORRIES.md` or `rg -n "\\bsorry\\b"`.
