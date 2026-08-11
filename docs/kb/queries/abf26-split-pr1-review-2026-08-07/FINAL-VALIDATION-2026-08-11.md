# PR #701 final validation — 2026-08-11

This is the final, current-candidate disposition of the adversarial review of PR #701. The
`R*.md` reports and `SOURCE-MAP-3c303efa.*` remain immutable evidence about the candidate as it
was inspected; this file records the fixes and the final verification results. The original PR
head was `3c303efa61f16dec87e7cb39856efd439374d099`, reviewed against merge base
`5fea8abf971496f54bcca2b98c029581d5b31658`.

## Verdict

No unresolved soundness, vacuity, proof-hole, accidental-universe, or silent-weakening defect
remains in the coding-theory scope claimed by this split. The contribution is `sorry`-free and
adds no non-standard axiom dependency. Statements that correct defective source formulations put
the necessary conditions explicitly in their hypotheses and document the discrepancy.

The PR is not presented as a formalization of every ABF26 section. In particular, the decoder and
cost theorem D6.4/L6.5 is not represented by a placeholder existential theorem: ArkLib does not yet
have the algorithm/cost model needed to state its deterministic decoder and
`O((s * n)^3)` running-time claim faithfully. That item is explicitly deferred rather than
weakened or made vacuous.

## Deterministic provenance inventory

The source-level declaration extractor was run on both the original PR head and an archive of its
merge base. The raw delta contained 177 names. Two were known regex-extractor namespace artefacts
and 21 were actual namespace relocations, leaving 154 genuinely new named declarations:

| Classification | Count |
| --- | ---: |
| Exact source statements | 26 |
| Supporting declarations and bridges | 100 |
| Material, sound generalizations | 8 |
| Documented source correction or partial abstraction | 6 |
| Generic infrastructure | 14 |

The complete name-by-name mapping, including source item, file, declaration kind, namespace-move
flag, and extractor-artifact flag, is in
[`SOURCE-MAP-3c303efa.json`](SOURCE-MAP-3c303efa.json); its methodology and source-page audit are
in [`SOURCE-MAP-3c303efa.md`](SOURCE-MAP-3c303efa.md). A fresh post-fix extraction found 5,423
declarations in 344 `ArkLib` files, compared with 5,396 in 343 files at the original reviewed head;
the new file is the reusable classical-Wronskian development.

## Final source coverage in this split

| Source item | Final status |
| --- | --- |
| ABF26 L2.1 | Proved through the existing arbitrary-sampling-set Schwartz–Zippel result; no duplicate proof chain. |
| D2.2, D2.4, D2.5, L2.6 | Entropy, Hamming-ball volume, alphabet-normalized linear/module rate, and Singleton/MDS bridges are present. The PR does not introduce a misleading universal finite-code `rate` API. |
| D2.8 | `Lambda` uses `Set.encard`, so infinite lists are `top`, not accidentally zero. Finite/numeric bridges are explicit. |
| D2.9, D2.13 | Generic interleaving support and interleaved RS, including exact saturated dimension, are present. |
| D2.14-D2.15 | Folded-RS admissibility, evaluation, code, transport, distance, and exact saturated dimension are present. The strengthened admissibility condition is necessary and documented. |
| D2.16, L2.17 | Subspace-design definition and the maximal valid `r >= 1` lower bound are proved with actual alphabet rate. The false printed `r = 0` case is not claimed. |
| T2.18 | Both folded-RS and univariate-multiplicity halves are proved. The FRS theorem restores the load-bearing generator/orbit hypotheses from GK16. The UM theorem uses the classical Wronskian and the source finite-field characteristic condition. |
| A.6-A.7 | Ordinary-derivative univariate-multiplicity evaluation/code and exact saturated dimension are present, with the ordinary/Hasse root-power bridge used by T2.18. |
| D2.19-D2.21 | Extension-field presentation, encoder, preserved injectivity, range/image identity, systematic encoder identity, presentation independence, and list-size equality are present. |
| DP25 Theorem 3.2 | Extension-code minimum-distance equality is proved, via the generic interleaved-code minimum-distance bridge. |
| D3.1, T3.2 | The corrected current-TeX Johnson radius and alphabet-generic Johnson list-size theorem are present, including the Plotkin corner rather than a guard that weakens the headline. |
| C3.3 | `mds_johnson_lambda_le_of_rate_distance` is alphabet- and code-generic with explicit normalized rate and the exact MDS rate-distance equation. Field-linear and RS results are thin wrappers. No provisional `generalRate`/`IsMDSGeneral` API remains. |
| Claim B.1 | A universe-polymorphic raw-indicator theorem is proved for finite `S` and arbitrary `T`, with no public `DecidableEq T`; the existing probability-notation spelling is a wrapper. |

## Corrected source defects

| Source statement | Resolution |
| --- | --- |
| ABF26 PDF D3.1 prints `ell/(ell-1)` | Lean follows the corrected author TeX `(ell-1)/ell`; the PDF formula is undefined at `ell = 1` and has the wrong behavior. |
| ABF26 D2.14 admits degenerate folded orbits | `Folded.Admissible` adds the intra-orbit injectivity required by GR08/GK16. |
| ABF26/GG25 L2.17 quantifies over `r = 0` | Lean states the maximal valid range `1 <= r`; the cited proof itself chooses a one-dimensional space. |
| ABF26/GG25 T2.18 omits generator/zero-orbit conditions | The FRS theorem exposes the necessary GK16 conditions. Compiled counterexamples show that dropping them makes the source-shaped claim false. |

None of these repairs is hidden in a proof or replaced by a weaker conclusion.

## Generality and library-integration fixes

- Accidental universe-0 binders were removed throughout Johnson, Claim B.1, MDS, and RS APIs.
- The generic C3.3 theorem is over an arbitrary finite alphabet and arbitrary code set; linear and
  Reed–Solomon facts only discharge its explicit rate-distance premise.
- `rs_lambda_le_johnson_mds` exposes only `Nonempty`; its proof constructs `Inhabited` locally.
- Claim B.1's generic core needs neither finite `T` nor `DecidableEq T`.
- The extension-code API is encoder-aware and proves its image representation instead of treating
  an image-only definition as the source encoder statement.
- The duplicate `ProximityGap.prob_uniform_congr_equiv` was removed; its consumer uses the
  canonical pre-existing `ProbabilityTheory.Pr_uniform_equiv`.
- Generic determinant, root-multiplicity, degree, finite-dimensional, and Wronskian facts live in
  reusable algebra/polynomial modules rather than in a paper-specific namespace.
- Stale paper pages, coverage labels, source metadata, citations, module inventories, and the
  blueprint declaration inventory were reconciled with the code.

## Honest remaining scope

The following are not claims of this split:

- D2.3 restricted distance and L2.10 interleaved list-size are assigned to later splits;
- T3.4-C3.5, the rest of section 3, the proximity-gap layer, and toy constructions are later work;
- D6.4/L6.5 requires an algorithm/cost model and remains explicitly missing.

The metric uniqueness theorem supporting future erasure decoding remains, but no arbitrary
function is mislabeled as a decoder and no existence theorem is true merely because its predicate
was defined to mean existence.

## Validation evidence

All checks below were run on the final pre-commit candidate:

- `./scripts/validate.sh`: passed, including the full build, the zero-warning gate for
  non-`sorry` warnings under `ArkLib/Data`, import completeness, generated-file checks, and KB lint.
- `./scripts/validate.sh --docs`: passed.
- `./scripts/validate.sh --site`: passed. The site and API documentation assembled successfully.
- `leanblueprint web` and `leanblueprint pdf`: passed independently with leanblueprint 0.0.20;
  the PDF build produced 61 pages. Existing bibliography/font/layout warnings remain unrelated.
- `lake exe checkdecls blueprint/lean_decls`: passed after regenerating the tracked declaration
  inventory from the edited blueprint sources.
- `git diff --check`: passed.
- Focused builds of `ExtensionCodes`, `JohnsonBound.Family`, `SubspaceDesign`, folded/interleaved/
  multiplicity RS, `Probability.Combinatorial`, and the affected proximity module all passed.
- `#print axioms` on 24 source-facing headline declarations reported exactly
  `[propext, Classical.choice, Quot.sound]`.
- The exhaustive compiled-environment sweep covered 8,321 declarations across 345 modules:
  416 declarations carry pre-existing baselined `sorryAx`, zero carry a non-standard axiom, and
  this PR introduces no new axiom or `sorryAx` taint.
- Added-line scans found no code-level `sorry`, `admit`, `axiom`, `unsafe`, or native-trust proof.

The repository-wide optional style lint still reports legacy errors already present on the target
branch. A changed-file/baseline comparison found no new style-lint finding in the new or materially
rewritten headline modules; the mandatory zero-warning and ordinary validation gates are clean.

The last release gate is a synthetic merge and validation against the then-current `origin/main`,
followed by the hosted PR checks. Those results belong in the final PR handoff because the target
branch can move after this document is written.
