# Claude Verification Fixlist

This note captures every remaining axiom, `sorry`, and structural gap in the Lean 4 Metamath kernel, together with the fix path. Items flagged as **facepalm risks** are ones that would invalidate the verifier if left as-is.

## High-Risk Structural Issues
- **Fallback substitutions** (`Metamath/Kernel.lean:1299`): `toSubst` silently fabricates `⟨"wff", [v]⟩` when a binding is missing or fails to convert, and it assumes spec variables look like `"v" ++ name`. This hides domain bugs and scrambles DV names. *Fix*: drop the `"v"` prefix trick, make `toSubst` fail when a binding is absent/ill-formed, and prove totality using `checkHyp_domain_covers`.
- **DV conversion hack** (`Metamath/Kernel.lean:1332`): `convertDV` injects a `"v"` prefix instead of reusing the real symbol names from the DB. This can mismatch spec DV pairs with the actual floating hypotheses. *Fix*: look up each label’s floating hypothesis via `convertHyp` and reuse its variable string.
- **matchFloats identity typecode** (`Metamath/Kernel.lean:1057` / `Metamath/Verify.lean:408`): both spec and impl versions default unmatched variables to `⟨"wff",[v]⟩`; that ignores the actual typecode carried by the $f statement. *Fix*: thread the declared typecode from the frame when building substitutions.
- **Spec reachability axiom** (`Metamath/Spec.lean:219`): `ProofValidSeq.toProvable` is axiomatized even though `fold_maintains_inv_and_provable` never hits the bad branch. *Fix*: either weaken the statement to the empty-stack case actually used, or restructure the proof so the nil case is avoided without axioms.

Addressing these first ensures later proofs cannot mask implementation bugs.

## Kernel Axioms That Still Need Proofs

| Location | Statement | Why it matters | Suggested fix |
| --- | --- | --- | --- |
| `Metamath/Kernel.lean:177` | `subst_sound` | Core link between HashMap substitution and spec substitution. | Replace with `toExpr_subst_commutes` + `toSubst` totality, then derive this lemma. |
| `Metamath/Kernel.lean:420` | `variable_wellformed` | Assumes parsed names are non-empty/variable-like. | Pull the guarantee from the parser: prove `$v` statements enforce non-empty strings, or adjust specs to avoid the assumption. |
| `Metamath/Kernel.lean:1363` | `stepNormal_sound` | Main kernel soundness lemma. | After `checkHyp_*`, DV, and stack lemmas are proven, redo the case analysis from the commented proof sketch to eliminate the axiom. |
| `Metamath/Kernel.lean:1377` | `dvCheck_sound` | Bridges the DV for-loop with `dvOK`. | Show that the loop is exactly `dv_spec` by reusing `checkHyp_images_convert` and `matchFloats_domain`. |
| `Metamath/Kernel.lean:1892` | `checkHyp_correct` | Ensures substitution/stack are built correctly. | Prove by recursion on `i`, using an explicit loop invariant (`P i := stack splits`), then discharge with the `Nat` index arithmetic already recorded in comments. |
| `Metamath/Kernel.lean:2906` | `proof_state_has_inv` | Global invariant for arbitrary proof states. | Show any reachable state has the invariant (`proof_state_reachable_has_inv`) and rework callers to only use reachable states, or prove the general case by replaying the parser construction. |

## Kernel Lemmas Left as `sorry`

| Location | Gap | Solution sketch |
| --- | --- | --- |
| `Metamath/Kernel.lean:316` | `identity_subst_syms` | Induct on `syms`, rewrite `flatMap` cases, and use the hypothesis `σ v = [v]`. |
| `Metamath/Kernel.lean:400` | `vars_apply_subset` var-in-result branch | Decompose `σ ⟨s⟩` → `varsInExpr` using `List.mem_filterMap` and existing `matchSyms` facts. |
| `Metamath/Kernel.lean:637` | `proofValid_monotone` | Simple induction on the `ProofValid` derivation; reuse the hypothesis for the `useAssertion` branch. |
| `Metamath/Kernel.lean:880` / `897` | `matchSyms_sound` variable case | Prove `matchSyms` never rebinds a variable: track membership of `h` in the remaining hypothesis symbols (needs a `NoDup` lemma on pattern symbols). |
| `Metamath/Kernel.lean:932` | `matchExpr_sound` | Thread the `vars` parameter and reuse `matchSyms_sound` plus the typecode equality extracted earlier. |
| `Metamath/Kernel.lean:1034` | `matchHyps_sound` essential branch | Once `matchFloats_sound` exists, the two-phase approach supersedes this lemma; otherwise add DV-disjointness premise so `σ₂` leaves `e`. |
| `Metamath/Kernel.lean:1115` | `matchFloats_sound` tail agreement | Show `σ_rest` extends `σ` only on the freshly bound variable (use `matchFloats_domain`). |
| `Metamath/Kernel.lean:1562` / `1585` | `checkHyp_floats_sound`, `checkHyp_essentials_sound` | Strengthen the recursive spec of `checkHyp`, prove the loop invariant (`i` processed → suffix matched), and extract the spec substitution using the new lemmas. |
| `Metamath/Kernel.lean:2401` | `viewStack_push` | Expand `Array.toList_push`, then apply `list_mapM_append`. |
| `Metamath/Kernel.lean:2413` | `viewStack_popK` | Use `Array.toList_extract` + `List.dropLast_eq_take` and the helper `list_mapM_dropLast_of_mapM_some`. |
| `Metamath/Kernel.lean:2776` / `2780` | `frame_conversion_correct` | The `mapM` success proof needs index preservation. Prove an auxiliary lemma: `Array.toList.mapM` respects indices and length. |
| `Metamath/Kernel.lean:3015` | `formula_subst_preserves_typecode` | Execute the `for` loop explicitly: the first iteration copies the `.const` typecode; use `Array.foldlM` unfolding. |
| `Metamath/Kernel.lean:3048` / `3056` | `subst_sym_correspondence` | Constants: show `"v"` prefix never appears because only `.var` constructors add it. Variables: chase definitions in `toSubst` after the rewrite from the earlier fix. |
| `Metamath/Kernel.lean:3105` | `toExpr_subst_commutes` | After fixing `toSubst`, perform list induction on `f.toList.tail`, using `subst_sym_correspondence` for each symbol. |

Finishing these removes every remaining `sorry` in the kernel.

## Specification Gaps

| Location | Issue | Fix |
| --- | --- | --- |
| `Metamath/Spec.lean:219` | `ProofValidSeq.toProvable` axiomatized. | Restrict the statement to the non-empty execution path used in `verify_impl_sound`, or prove the nil case by constructing the trivial proof. |
| `Metamath/Spec.lean:235` | `soundness_statement` left as `sorry`. | Once `stepNormal_sound` is a theorem, replay `verify_impl_sound` to discharge this global statement. |

## Preprocessor Gaps

| Location | Issue | Fix |
| --- | --- | --- |
| `Metamath/Preprocess.lean:70` | `tokens` stub (`sorry`). | Implement a whitespace splitter (or import the parser tokenizer) so the subsequent lemmas can quantify over actual tokens. |
| `Metamath/Preprocess.lean:59` / `75` / `87` / `104` | Include-strip correctness axioms. | Prove each by structural induction on the `ByteArray`; for `stripIncludes_sound`, connect to the parser’s `expandIncludes` and show the stripped buffer yields the same `ParserState`. |

## Non-Kernel Files

- `P_NP_LEAN4_SKETCH.lean` contains exploratory `sorry`s unrelated to the verifier; safe to ignore for kernel soundness.

## Recommended Order of Attack
1. Fix the structural substitution/DV issues (`toSubst`, `convertDV`, `matchFloats` typecodes).
2. Prove the `checkHyp_*` lemmas and discharge `checkHyp_correct`.
3. Finish the view/stack lemmas to solidify `ProofStateInv`, then remove `proof_state_has_inv`.
4. Revisit `frame_conversion_correct`, followed by `toExpr_subst_commutes`.
5. With all prerequisites in place, prove `dvCheck_sound`, then `stepNormal_sound`, and finally the global spec theorems.

Once these are addressed the Lean build will be axiom-free, giving Mario a verifier he can trust.
