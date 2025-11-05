# Build Reproduction Guide

**Last updated:** 2025-10-13
**Project:** Metamath Verifier Soundness Proof

---

## Quick Start

```bash
# Clone the repository
git clone https://github.com/[username]/mm-lean4
cd mm-lean4

# Build the project
lake build

# Check axioms in main theorem
lake env lean scripts/check_axioms.lean
```

**Expected result:** Clean build with axiom report showing dependencies.

---

## Prerequisites

### Lean 4 Toolchain

This project uses **Lean 4.20.0-rc2** (or compatible version).

**Check your version:**
```bash
lean --version
```

**Install/update Lean:**
```bash
# Using elan (recommended)
elan install leanprover/lean4:v4.20.0-rc2
elan default leanprover/lean4:v4.20.0-rc2
```

**Toolchain file:**
The exact version is pinned in `lean-toolchain`:
```
cat lean-toolchain
```

Should show: `leanprover/lean4:v4.20.0-rc2` (or current version)

---

### Lake Build Tool

Lake comes with Lean 4. Verify:
```bash
lake --version
```

Expected: Lake version 4.0.0 or compatible

---

## Build Commands

### Full Build
```bash
lake build
```

Builds all modules:
- `Metamath.Spec` - Specification
- `Metamath.Verify` - Implementation
- `Metamath.Bridge.Basics` - TypedSubst bridge
- `Metamath.KernelExtras` - Utility lemmas
- `Metamath.Kernel` - Main soundness proof

**Time:** ~2-5 minutes on modern hardware (first build)
**Time:** ~10-30 seconds (incremental rebuilds)

---

### Build Specific Module
```bash
# Build only Spec
lake build Metamath.Spec

# Build only Kernel (depends on all others)
lake build Metamath.Kernel
```

---

### Clean Build
```bash
# Remove build artifacts
lake clean

# Fresh build
lake build
```

---

## Expected Build Output

### Successful Build

```
[1/6] Building Metamath.Spec
[2/6] Building Metamath.Verify
[3/6] Building Metamath.KernelExtras
[4/6] Building Metamath.Bridge.Basics
[5/6] Building Metamath.Kernel
[6/6] Building Metamath
Build succeeded
```

**Note:** You may see warnings about `declaration uses 'sorry'` - this is expected for work-in-progress proofs.

---

### Known Warnings (Safe to Ignore)

```
warning: unused variable `c`
```
Linter warnings - doesn't affect soundness.

```
warning: declaration uses 'sorry'
```
Incomplete proofs - see `docs/TCB.md` for status.

```
warning: `List.bind` has been deprecated: use `List.flatMap` instead
```
API deprecation - will be fixed in future refactoring.

---

### Build Errors (Problems)

If you see actual **errors** (not warnings), something is wrong:

```
error: unknown identifier 'foo'
error: type mismatch
error: failed to prove
```

**Troubleshooting:**
1. Check Lean version: `lean --version`
2. Clean and rebuild: `lake clean && lake build`
3. Check for local modifications: `git status`
4. Compare with known-good commit

---

## Axiom Audit

### Check Main Theorem Axioms

```bash
lake env lean scripts/check_axioms.lean
```

**What it does:** Runs `#print axioms` on main soundness theorems.

**Expected output:**
```
-- verify_impl_sound axioms:
quot.sound
propext
Classical.choice
[domain-specific axioms if any - see TCB.md]

-- fold_maintains_inv_and_provable axioms:
[similar]

-- stepNormal_preserves_inv axioms:
[similar]
```

**Interpretation:**
- `quot.sound`, `propext`, `Classical.choice` - Lean 4 foundations (always present)
- Any other axioms - See `docs/TCB.md` for explanation and elimination plan

---

### Automated Axiom Report

To generate a report file:
```bash
lake env lean scripts/check_axioms.lean 2>&1 | tee docs/AXIOMS_REPORT.md
```

This captures the axiom list for documentation.

---

## CI/CD Integration

### GitHub Actions Example

```yaml
name: Lean 4 Build

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install elan
        run: |
          curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH

      - name: Build
        run: lake build

      - name: Check axioms
        run: lake env lean scripts/check_axioms.lean

      - name: Fail on sorry
        run: |
          if lake build 2>&1 | grep -q "declaration uses 'sorry'"; then
            echo "ERROR: Sorries found in build"
            exit 1
          fi
```

**Notes:**
- Remove "Fail on sorry" step during development
- Re-enable it when targeting zero-sorry milestone

---

## Development Workflow

### Iterative Development

```bash
# Edit a file
vim Metamath/Kernel.lean

# Quick check (just that file)
lake build Metamath.Kernel

# If that works, full build
lake build
```

---

### LSP Integration (VS Code)

1. **Install Lean 4 extension** in VS Code
2. **Open the project:** `code .`
3. **Extension auto-detects** `lean-toolchain` and uses correct version
4. **Live feedback** as you edit - red squiggles for errors

**Tip:** Click the "∀" icon in bottom-right to see Lean info panel.

---

## Troubleshooting

### Problem: "lake: command not found"

**Solution:** Install Lean 4 + Lake via elan:
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

---

### Problem: "unknown package 'Mathlib'" or similar

**Solution:** This project doesn't use Mathlib. If you see this, check:
- Are you in the right directory? (`cd mm-lean4`)
- Is `lakefile.lean` present?

---

### Problem: Build hangs or takes forever

**Solution:**
- **First build is slow** (~2-5 min) - be patient
- **Incremental builds should be fast** (~10-30 sec)
- Try `lake clean && lake build` if stuck

---

### Problem: Type errors after Lean upgrade

**Solution:**
- **Pin to specific version** in `lean-toolchain`
- **Don't upgrade** Lean mid-project without testing
- Check compatibility with `elan show`

---

### Problem: Out of memory during build

**Solution:**
- Large projects can use lots of RAM
- Close other apps
- Increase swap space if on Linux

---

## Performance Notes

### Build Times (Approximate)

**Full build (cold cache):**
- Laptop (8GB RAM, 4 cores): ~3-5 minutes
- Workstation (32GB RAM, 16 cores): ~1-2 minutes

**Incremental build (hot cache):**
- Single file change: ~5-15 seconds
- Module change: ~30-60 seconds

---

### Speeding Up Builds

```bash
# Use more cores (if available)
lake build -j 8

# Default uses all cores
lake build
```

**Note:** Lake auto-detects CPU count.

---

## Verifying Build Integrity

### Checksum Verification

After clean build:
```bash
# Hash all .olean files
find .lake/build -name "*.olean" | sort | xargs sha256sum > build-checksums.txt
```

This creates a fingerprint of the build. Compare with known-good builds.

---

### Reproducible Builds

To ensure reproducibility:
1. **Pin toolchain:** Use exact Lean version in `lean-toolchain`
2. **Pin dependencies:** Use exact Lake package versions (if any)
3. **Clean slate:** Always test with `lake clean && lake build`

---

## Documentation Generation

### Build HTML Docs (Future)

```bash
lake build :doc
```

Generates API documentation (if configured).

---

## File Sizes

**Source code:**
- `Metamath/Spec.lean`: ~10KB (~300 lines)
- `Metamath/Verify.lean`: ~30KB (~800 lines)
- `Metamath/Bridge/Basics.lean`: ~10KB (~250 lines)
- `Metamath/Kernel.lean`: ~150KB (~3800 lines)
- **Total source**: ~200KB (~5000 lines)

**Build artifacts:**
- `.lake/build/`: ~50-100MB (compiled .olean files)

---

## Maintenance

### Updating Lean Version

```bash
# Update lean-toolchain file
echo "leanprover/lean4:v4.X.Y" > lean-toolchain

# Update toolchain
elan update

# Test build
lake clean && lake build
```

**Warning:** API changes between Lean versions can break builds. Test thoroughly!

---

### Updating Lake Dependencies

```bash
# Update package versions in lakefile.lean
vim lakefile.lean

# Fetch new dependencies
lake update

# Rebuild
lake build
```

---

## Continuous Testing

### Run Tests (If Implemented)

```bash
# Unit tests
lake test

# Smoke tests
lake env lean scripts/smoke.lean
```

---

## Benchmarking (Optional)

To track build performance over time:

```bash
# Time the build
time lake clean && time lake build

# Save results
echo "$(date): $(time lake build 2>&1 | grep real)" >> build-times.log
```

---

## Summary: One-Command Verification

**For reviewers/auditors:**

```bash
git clone https://github.com/[username]/mm-lean4
cd mm-lean4
lake build && lake env lean scripts/check_axioms.lean
```

**Expected result:**
- Build succeeds (possibly with warnings)
- Axiom report shows only Lean foundations + documented TCB

**Time:** ~5 minutes (first time), ~1 minute (incremental)

---

## Help & Support

**Lean 4 Docs:** https://lean-lang.org/lean4/doc/
**Lake Docs:** https://github.com/leanprover/lake
**Zulip Chat:** https://leanprover.zulipchat.com/

**Project Issues:** See GitHub issues page

---

**Maintained by:** Zar
**Review:** Update when build process changes
**See also:** TCB.md (axioms), BRIDGE_OVERVIEW.md (architecture)
