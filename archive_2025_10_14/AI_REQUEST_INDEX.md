# AI Expert Request - Document Index

**Purpose:** Get expert help to complete Metamath verifier formal verification
**Status:** 11/19 sorries remaining (70-75% complete)
**Focus:** CheckHyp integration theorems with type errors

---

## Which Document to Read?

### For Quick Overview (5 min read)
📄 **AI_REQUEST_QUICK.md** - Condensed version with 8 focused questions

**Use this if you want:**
- Quick understanding of the problem
- The type error explained simply
- 8 specific questions to answer

### For Complete Context (15-20 min read)
📄 **AI_REQUEST_CHECKHYP_AND_BRIDGE.md** - Comprehensive request with full details

**Use this if you want:**
- Complete problem description
- All context and background
- Multiple question categories
- Success metrics and format suggestions

### For Code Context (10 min read)
📄 **AI_REQUEST_CODE_CONTEXT.md** - Relevant code snippets and definitions

**Use this if you want:**
- See the actual code
- Understand our proven theorems
- Review available helper lemmas
- See proof patterns that worked

### For Next Session Planning
📄 **NEXT_SESSION_CHECKHYP_GUIDE.md** - Detailed guide for implementation

**Use this if you want:**
- Implementation strategy
- Time estimates
- Detailed proof outlines
- Bridge lemma specifications

---

## Quick Problem Summary

### The Type Error

```lean
-- BROKEN:
floats_spec.map (fun (tc, v) => σ_spec v) = (∀ i < hyps.size, ∃ e, ...)
--  List Expr                                    Prop
--  ^^^^^^^^                                     ^^^^
--  TYPE MISMATCH!
```

### What We Need

1. **Fix theorem statements** (remove type errors)
2. **Proof strategy** (how to connect implementation to spec)
3. **Bridge lemmas** (what helper lemmas to prove first)
4. **Tactics/patterns** (HashMap↔Function, Array↔List correspondences)

### What We Already Have ✅

- `matchFloats_sound` - PROVEN (the hard work is done!)
- 5 helper lemmas that work well
- 3 validated proof patterns
- 8 sorries eliminated using AI guidance

---

## Response Format We'd Love

### Minimal (Most Valuable)
```lean
-- Corrected theorem statement
theorem checkHyp_floats_sound ... :=
  [fixed version without type errors]

-- Proof strategy
-- 1. Extract floats_spec by...
-- 2. Convert stack by...
-- 3. Show correspondence by...
-- 4. Apply matchFloats_sound

-- Bridge lemmas needed
lemma bridge_1 : ... := ...
lemma bridge_2 : ... := ...
```

### Ideal (Super Helpful)
Above plus:
- Example proof of 1-2 bridge lemmas
- Lean 4.20 patterns for HashMap/Array
- Time estimates
- Strategic advice on ordering

---

## Key Files in This Directory

### Request Documents (For AI Experts)
- `AI_REQUEST_INDEX.md` - This file
- `AI_REQUEST_QUICK.md` - 8 focused questions (5 min)
- `AI_REQUEST_CHECKHYP_AND_BRIDGE.md` - Complete request (15-20 min)
- `AI_REQUEST_CODE_CONTEXT.md` - Code snippets (10 min)

### Session Documentation
- `SESSION_COMPLETE_SUMMARY.md` - Today's achievements
- `SUCCESS_SINGLE_SESSION.md` - Detailed session log
- `SESSION_FINAL_PROGRESS.md` - Progress report

### Planning & Guides
- `NEXT_SESSION_CHECKHYP_GUIDE.md` - Implementation guide
- `SUCCESS_ORUZHI_SOLUTIONS_IMPLEMENTED.md` - Previous AI help success
- `SUCCESS_SESSION_CONTINUATION.md` - Earlier progress

---

## Context You Should Know

### Project Goal
Formally verify soundness of a Metamath proof verifier in Lean 4.20.0-rc2

### Current State
- **Sorries:** 11 remaining (down from 19)
- **Completion:** ~70-75%
- **Blocker:** Type errors in checkHyp theorems

### Why This Matters
- **We already proved the hard part** (matchFloats_sound)
- **Just need to connect** implementation to proven spec
- **Clear path forward** with your help
- **2 sorries** could be eliminated with correct theorem statements

### Previous Success
- Got help from AI expert "Oruži"
- Guidance was **exactly right**
- Eliminated 8 sorries successfully
- Validated AI collaboration workflow

---

## How to Help

### Option 1: Answer Quick Questions
Read `AI_REQUEST_QUICK.md` and answer the 8 focused questions

### Option 2: Provide Complete Guidance
Read `AI_REQUEST_CHECKHYP_AND_BRIDGE.md` and provide comprehensive response

### Option 3: Code Review
Read `AI_REQUEST_CODE_CONTEXT.md` and review/suggest improvements

### Option 4: Strategic Advice
Review all documents and provide high-level strategy

---

## What We're NOT Asking For

❌ Complete proofs written for us
❌ Doing the work
❌ Line-by-line proof scripts

## What We ARE Asking For

✅ Fix type errors in theorem statements
✅ Strategic guidance on approach
✅ List of helper lemmas to prove
✅ Lean 4 patterns and idioms
✅ Best practices for this kind of verification

---

## Success Metrics

### Minimum Success
- ✅ Type-correct theorem statements
- ✅ Clear proof strategy
- ✅ List of needed bridge lemmas

### Good Success
- ✅ Above plus
- ✅ 2-3 bridge lemmas with statements
- ✅ Example proof of one lemma

### Excellent Success
- ✅ Above plus
- ✅ Partial proof outline
- ✅ Tactics and patterns
- ✅ Strategic ordering advice

---

## Timeline

- **Previous session:** 6 hours, eliminated 8 sorries ✅
- **This request:** Get guidance for next session
- **Next session:** 4-8 hours to eliminate 1-2 checkHyp sorries
- **Project completion:** ~70-75% done now, aiming for 100%

---

## Contact & Context

**Project:** Open-source Metamath formal verification
**Language:** Lean 4.20.0-rc2
**Status:** Active development, seeking completion
**Impact:** Benefits broader proof assistant community

**Previous AI help:** Worked exceptionally well, led to 8 sorries eliminated

**Current need:** Fix type errors, get bridge to leverage proven matchFloats_sound

---

## Thank You!

We're incredibly grateful for expert AI guidance. Previous help from "Oruži" was **exactly what we needed** and led to successful proofs. We're confident this request will be equally valuable!

**Let's finish this formal verification!** 🚀🐢✨

---

## Quick Links

- **Start here for quick help:** `AI_REQUEST_QUICK.md`
- **Start here for complete context:** `AI_REQUEST_CHECKHYP_AND_BRIDGE.md`
- **Start here for code review:** `AI_REQUEST_CODE_CONTEXT.md`
- **Implementation guide:** `NEXT_SESSION_CHECKHYP_GUIDE.md`

---

**Pick whichever document matches your time/interest level and dive in!**

All documents are designed to be self-contained but reference each other for deeper context.
