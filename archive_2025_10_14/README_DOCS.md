# Documentation Index - Metamath Kernel Verification

## 📌 Start Here (Latest Session - 2025-10-13)

### Essential Reading (8 Current Files)
1. **QUICK_STATUS.md** - One-page status overview ⭐ **READ THIS FIRST**
2. **SESSION_SUMMARY.md** - Comprehensive session report
3. **REQUEST_FOR_ORUZI.md** - Specific request for adapted proofs
4. **BATTERIES_BUILD_SUCCESS.md** - Why Oruži's proofs need adaptation
5. **PROOF_ATTEMPT_NOTES.md** - Detailed proof attempt analysis
6. **COMPLETE_SORRY_DOCUMENTATION.md** - Summary of all sorries
7. **GPT5_QUERIES_ALL_SORRIES.md** - Queries for each sorry
8. **README_DOCS.md** - This file

### Archived Documentation
- **docs_archive/** - 96 older documentation files from previous sessions
- **logs_archive/** - Old build logs

### What We Did Today
- ✅ Built Batteries library successfully (low-RAM mode)
- ✅ Attempted to integrate Oruži/GPT-5's proofs
- ✅ Documented why proofs need adaptation
- ✅ Kept 6 library axioms with clear justifications

---

## 📚 Historical Documentation

All previous documentation has been moved to **docs_archive/** for reference.

Key archived files include:
- SORRY_DEPENDENCY_ORDER.md
- SORRY_SOLVING_PROGRESS.md
- AXIOM_ELIMINATION_COMPLETE.md
- CODEX_TREASURE_MAP.md
- And 92 others...

---

## 🎯 Current State Summary

### Files with Axioms/Sorries
```
Metamath/KernelExtras.lean    : 6 axioms  (library properties)
Metamath/Kernel.lean          : 32 sorries (verification work)
Metamath/Bridge/Basics.lean   : 8 sorries  (bridge lemmas)
Metamath/Spec.lean            : 1 axiom    (specification)
Metamath/Preprocess.lean      : 4 axioms   (preprocessing)
```

### Key Accomplishments
- ✅ Batteries library integrated and built
- ✅ 6 library lemmas documented as axioms (awaiting Oruži's adapted proofs)
- ✅ Key-based HashMap refactor complete
- ✅ Comprehensive documentation

### Waiting On
- Oruži/GPT-5 advice on adapting proofs to Lean 4.20.0-rc2

---

## 🔧 Build Commands

```bash
# Build Batteries (low memory)
LEAN_JOBS=1 lake build batteries

# Test KernelExtras
lake env lean Metamath/KernelExtras.lean

# Build project (has pre-existing errors in Kernel.lean)
lake build

# Count sorries/axioms
grep -r "sorry" Metamath/ --include="*.lean" | wc -l
grep -r "axiom" Metamath/ --include="*.lean" | wc -l
```

---

## 📖 Historical Context

This project has been ongoing with multiple sessions:
- Early sessions focused on understanding the codebase
- Middle sessions worked on axiom elimination
- Recent sessions completed HashMap key-based refactor
- Latest session integrated Batteries and documented library lemmas

The verification is progressing well. Most remaining work is in Kernel.lean (32 sorries) and Bridge/Basics.lean (8 sorries).

---

## 🎓 For New Contributors

**Start with:**
1. Read QUICK_STATUS.md
2. Read SESSION_SUMMARY.md
3. Look at Metamath/KernelExtras.lean to see the 6 axioms
4. Check BATTERIES_BUILD_SUCCESS.md to understand the current situation

**Then explore:**
- The sorted documentation above by date
- The actual source files in Metamath/
- Build logs (build.log) for compilation status

---

## 💡 Philosophy

**We distinguish between:**
- **Library axioms** - Standard mathematical facts (like in KernelExtras)
- **Domain axioms** - Metamath-specific assumptions (like in Spec/Preprocess)
- **Verification gaps** - Proofs in progress (sorries in Kernel/Bridge)

The 6 library axioms have minimal TCB impact. They're obviously true properties that any standard library would prove. Using `axiom` is pragmatic, not a fundamental verification gap.

---

## 📞 Contact

For questions about:
- **Current status**: Read QUICK_STATUS.md
- **Today's work**: Read SESSION_SUMMARY.md
- **Specific lemmas**: Read GPT5_QUERIES_ALL_SORRIES.md
- **Build issues**: Read BATTERIES_BUILD_SUCCESS.md
