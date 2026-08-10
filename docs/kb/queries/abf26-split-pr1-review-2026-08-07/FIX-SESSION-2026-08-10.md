# PR #701 — fix-session record, 2026-08-10

Disposition of the 16 open findings of [`FIX-BOOTSTRAP.md`](FIX-BOOTSTRAP.md). Every fix was
made only after independently re-validating the finding at the current tip, and every fix was
validated adversarially (per-file compile with the project's real linter options, consumer
sweeps, counterexample re-derivation for kept hypotheses, full `lake build`, axiom probe).

## Group A — regressions from the second fix pass

- **A1 CLOSED.** `[Finite F]` dropped from `listDecodable_of_Lambda_le_natCast`,
  `Lambda_le_floor_of_toENNReal_le_ofReal`, `listDecodable_of_toENNReal_le_ofReal` — in each,
  the `Lambda`-bound hypothesis itself forces the point list finite
  (`Set.finite_of_encard_le_coe` / `Set.encard_ne_top_iff`). In the follow-up B3 semantic
  correction, `listDecodable` itself began recording point-list finiteness; this also made
  `Lambda_le_iff_listDecodable`, `Lambda_le_floor_iff_listDecodable`, its `ℝ≥0` variant, and
  `Lambda_le_floor_of_listDecodable` instance-free. (`ncard_closeCodewordsRel_le_Lambda`, the
  fourth original A1 lemma, was deleted under A2 instead.)
- **A2 CLOSED (all three deleted).** `Lambda_eq_iSup_encard` (literally `rfl`, zero
  consumers, was still advertised in `## Main statements`), `ncard_closeCodewordsRel_le_Lambda`
  (sole consumer had inlined `le_iSup`; its "exposed for the bridges below" docstring was
  false), `Pr_decide_eq_tsum_indicator` (self-described compatibility wrapper, zero
  consumers, against the no-alias doctrine). Consumer sweeps confirmed zero uses of each
  outside the defining file.

## Group B — labelling and honesty

- **B1 CLOSED (documentation only, definition unchanged).** `LinearCode.rate` docstring now
  defines it as the base-field-dimension rate `dim/n`, correct for ABF26 D2.5 only at
  alphabet `F` and explicitly *not* D2.5's `dim/(s·n)` over `F^s`; points at
  `subspaceDesign_tau_lower` / `frs_is_subspaceDesign_gk16` which spell the paper form out.
  Audit D2.5 row and the conventions type table carry the same caveat. The optional
  module-alphabet normalized rate was **not** added (out-of-scope list, module-alphabet
  bridge is a later split).
- **B2 CLOSED.** `mds_johnson_lambda_le` relabelled "ABF26 Corollary 3.3, field-linear
  specialization" in both the theorem docstring and the module header; audit C3.3 row now
  says **partial** with the `LinearCode ι F` scope limitation spelled out.
- **B3 CLOSED (semantic follow-up).** `listDecodable C r ℓ` now requires every point list to
  be finite *and* its `Set.ncard` to be at most the real bound `ℓ`. This preserves the existing
  STIR-facing real-valued API while preventing `Set.ncard`'s infinite-set-to-zero behavior from
  making `listDecodable` or `uniqueDecodable` vacuous over infinite alphabets. The old compiled
  examples on `Code (Fin 1) ℚ` at radius `1` and bounds `0`/`1` are therefore no longer
  provable. The explicit finiteness witness also removes all remaining `[Finite F]` assumptions
  from the `Lambda`/`listDecodable` bridges.
- **B4 CLOSED (boundary case proved).** `johnson_bound_lambda_le_ell` now assumes `1 ≤ ℓ` —
  the paper's full range. New `ℓ = 1` branch: `Jqℓ q 1 δ = J q 0 = 0` and a radius-0 list
  contains at most the centre (the predicted `DecidableEq` instance clash between
  `closeCodewordsRel`'s classical instance and the section instance was bridged with
  `convert`). `johnson_listDecodable` / `johnson_listDecodable_of_le` relaxed to `1 ≤ ℓ`
  too. The docstring's "no side condition" claim replaced by the honest three-regime
  description; `ℓ = 0` remains excluded and remains genuinely false as encoded.

## Group C — generality and placement

- **C1 CLOSED (all hypothesis drops = strengthenings).**
  `ReedSolomon.mem_map_degreeLT_one_iff_mem_code` → `[CommSemiring F]`; `frsCode`,
  `mem_frsCode_iff`, `mem_frsCode_iff_flipped`, `mem_frsCode_one_iff_mem_rsCode`,
  `frsCode_one_map_eq_rsCode` → `[CommSemiring F]` (matching `frsEvalOnPoints`);
  `Polynomial.natDegree_comp_C_mul_X_le` → `[Semiring F]`. Bonus forced by the shared
  lemma's weakening: `Multiplicity.mem_umCode_one_iff_mem_rsCode` → `[CommSemiring F]`,
  and its now-obsolete instance-clash workaround note removed. Distance / dimension /
  admissibility / Kummer keep their fields.
- **C2 CLOSED.** `reidx_hammingDist` generalized to an arbitrary equivalence and moved to
  the new `ArkLib/ToMathlib/InformationTheory/Hamming.lean` as `hammingDist_comp_equiv`
  (`e : ι' ≃ ι` ⇒ precomposition is a Hamming isometry); four call sites migrated.
  Novelty re-verified against Mathlib: the full `hammingDist` API transports the alphabet
  (`hammingDist_comp`, `hammingDist_smul`), never the coordinate index. `ArkLib.lean`
  regenerated via `scripts/update-lib.sh`.
- **C3 CLOSED.** `MvPolynomial.totalDegree_le_of_degreeOf_lt` stays in
  `Data/MvPolynomial/Degrees.lean` (its de facto generic-degree-helper home) with the
  upstream-target note restored, and is now a two-line corollary of the file's own
  `totalDegree_le_card_mul_of_mem_restrictDegree` instead of a duplicated proof.
- **C4 CLOSED.** `ExtensionFieldPresentation.coord` is now a `noncomputable abbrev`,
  matching its "abbreviation" documentation. No simpNF fallout.

## Group D — stale documentation

- **D1** Erasure.lean's `[BCGM25]` reference entry deleted (its target note was removed in
  the second fix pass; the file no longer engages BCGM25 at all).
- **D2** Audit Claim B.1 row no longer names the now-`private` helpers; describes the route
  instead.
- **D3** Audit T2.18 row: restored the 2026-07-21 correction record (`orderOf ω = |F|−1`
  restored; unguarded form false, counterexample `ω = −1` over `𝔽₁₀₁`; PAPER_REVS #13),
  recovered verbatim from git history.
- **D4** `GX13/metadata.yml`: `source_kind: inproceedings`; stale wrong-title note dropped
  (the BibTeX title is already correct).
- **D5** `papers/GW13.md`: the "stale note in SubspaceDesign.lean" parenthetical was itself
  stale — SubspaceDesign.lean records the gap correctly (missing item = multiplicity
  Wronskian analogue, not the derivative operation); rewritten accordingly.
- **D6** All seven `## References` sections rewritten to CONTRIBUTING.md's
  `* [Author Last Name, First Initial, *Title*][key]` format, titles/initials taken from
  `blueprint/src/references.bib`; scope parentheticals preserved. Audit T3.2 row also
  updated for B4's new `ℓ ≥ 1` range.

## Coverage-gap re-check (ToMathlib promotions vs Mathlib)

All eight promoted declarations re-checked via loogle/leansearch: **no Mathlib duplicate**
for any. Closest relatives: `LinearMap.finrank_range_of_inj` (global injectivity; ArkLib's
`finrank_eq_of_map_eq` needs it only on the submodule), `Polynomial.card_le_degree_of_subset_roots`
(counts roots without multiplicity), Mathlib's KummerExtension criteria (general `X^n − C a`;
ArkLib's is the finite-field `q−1`/generator instance), `Basis.extendLe` (set-indexed, not the
Fin-indexed adapted form). The determinant column-divisibility and the packaged
Frobenius-power lemmas have no upstream counterpart.

## Validation at the closing tip

- `lake build` green, 4203 jobs (the two "failed target" reports mid-session were an
  olean race between two concurrent lake builds — `failed to open BerlekampWelch.olean` —
  not code errors; the sequential rebuild is clean).
- `ArkLib/Data` and `ArkLib/ToMathlib` non-sorry warning gates: clean.
- `#print axioms` on all 25 touched/headline declarations: exactly
  `[propext, Classical.choice, Quot.sound]`.
- `validate.sh --docs`, `scripts/kb/lint.py --strict-cited-pages`,
  `scripts/check-docs-integrity.py`: pass.
- Zero added lines exceed the 100-codepoint style limit; per-file compiles with the
  project's full linter options produce zero warnings on every touched file.

## Follow-up validation after the B3 semantic correction

- Regression probes now prove
  `¬ listDecodable (Set.univ : Code (Fin 1) ℚ) 1 0` and
  `¬ uniqueDecodable (Set.univ : Code (Fin 1) ℚ) 1`; these are the exact infinite-alphabet
  examples that held under the defective definition.
- Sequential focused builds of `ListDecodability` and `JohnsonBound.Family` pass; the latter
  was run only after rebuilding the former to avoid checking against a stale `.olean`.
- `./scripts/validate.sh --docs` passes: full 4203-job project build, clean `ArkLib/Data`
  non-sorry warning gate, umbrella-import check, docs integrity, strict knowledge-base lint,
  and 8570-job API-doc build.
- `git diff --check` passes, and no generated knowledge-base files were changed.

## Still open (owner action / separate PRs)

- **I1**: push + PR-body refresh (owner edits the body; the body still advertises the
  deleted erasure API and stale sorry counts).
- Everything in FIX-BOOTSTRAP §3 (out of scope) remains untouched, including the optional
  module-alphabet rate/Johnson generalizations (B1/B2's deferred halves).
