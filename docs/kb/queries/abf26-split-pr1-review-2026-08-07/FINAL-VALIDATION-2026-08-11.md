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
in [`SOURCE-MAP-3c303efa.md`](SOURCE-MAP-3c303efa.md). The repository's final regex extraction
emitted 5,792 records in 344 `ArkLib` files; after removing its 363 known lexical false positives,
the inventory contains 5,429 actual declarations, compared with 5,396 in 343 files at the original
reviewed head. The new file is the reusable classical-Wronskian development. The final six-
declaration increase after the earlier review snapshot is exactly the private support and public
API that packages the extension encoder as an `F`-linear map.

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
| D2.19-D2.21 | Extension-field presentation, `F`-linear encoder, preserved injectivity, range/image identity, systematic encoder identity, presentation independence, and list-size equality are present. |
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
  an image-only definition as the source encoder statement; the source encoder is packaged with
  its proved `F`-linearity rather than relying on linearity of its image.
- The classical Wronskian degree bound has the definition's natural `CommRing` generality, and its
  nonvanishing criterion supports characteristic zero as well as GK16's large-positive-
  characteristic regime.
- The duplicate `ProximityGap.prob_uniform_congr_equiv` was removed; its consumer uses the
  canonical pre-existing `ProbabilityTheory.Pr_uniform_equiv`.
- Generic determinant, root-multiplicity, degree, finite-dimensional, and Wronskian facts live in
  reusable algebra/polynomial modules rather than in a paper-specific namespace.
- Stale paper pages, coverage labels, source metadata, citations, module inventories, and the
  blueprint declaration inventory were reconciled with the code.

## Low/nit follow-up disposition

- The source explicitly calls the D2.20 encoder linear, so the initially deferred encoder-
  linearity note was resolved: `extensionEncodeLinearMap` packages the existing formula as an
  `F`-linear map and is definitionally equal to `extensionEncode` on inputs.
- The classical-Wronskian API now supports characteristic zero and GK16's large-positive-
  characteristic regime; its standalone degree bound was weakened from `Field` to the natural
  `CommRing` assumption.
- No general constructor for a systematic presentation was added. ABF26 and BCFW25 define
  systematicity and use it conditionally; they do not assert an existence theorem. The condition
  is non-vacuous (the degree-one self-extension with its singleton basis is systematic), so a
  general basis-with-one-first constructor is an orthogonal convenience API.
- `alphabetRate` intentionally remains the algebraic rate for the in-scope `F`-additive alphabet
  `F^s`. A universal finite-code logarithmic rate would require separate conventions for empty,
  singleton, and infinite alphabets and would collide conceptually with the existing linear-code
  `rate`; generic C3.3 therefore accepts an explicit normalized `ρ` and exact rate-distance
  equation. No misleading `generalRate`/`IsMDSGeneral` API is retained.
- Generalized documentation now calls `Lambda` an `iSup`/supremum rather than claiming its value
  is attained outside the paper's finite-alphabet setting. Degenerate `q = 0,1` entropy bounds and
  concavity are also covered instead of carrying unnecessary lower-bound hypotheses on `q`.

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
- `#print axioms` on 25 source-facing headline declarations reported exactly
  `[propext, Classical.choice, Quot.sound]`.
- The exhaustive compiled-environment sweep covered 8,327 declarations across 345 modules:
  416 declarations carry pre-existing baselined `sorryAx`, zero carry a non-standard axiom, and
  this PR introduces no new axiom or `sorryAx` taint.
- Added-line scans found no code-level `sorry`, `admit`, `axiom`, `unsafe`, or native-trust proof.

The repository-wide optional style lint still reports legacy errors already present on the target
branch. A changed-file/baseline comparison found no new style-lint finding in the new or materially
rewritten headline modules; the mandatory zero-warning and ordinary validation gates are clean.

## Current-main merge gate

Commit `907e6dc83` was synthetically merged into `origin/main` `e052dbc93` in a clean detached
worktree. The merge had no textual conflict. `./scripts/validate.sh` then passed a clean 4,220-job
build together with the Data warning, import, documentation, and KB gates;
`lake exe checkdecls blueprint/lean_decls` and `git diff --check` also passed.

The merged exhaustive axiom sweep covered 8,426 declarations in 348 modules and found zero
non-standard-axiom-tainted declarations. Its committed-main baseline check reports exactly four
new `sorryAx`-tainted Hachi declarations:

- `ArkLib.Lattices.Ajtai.InnerOuter.mem_relNestedZeroCheck_of_nestedRoundRel`;
- `ArkLib.Lattices.Ajtai.InnerOuter.nestedSumcheckBridgePackage`;
- `ArkLib.Lattices.Ajtai.InnerOuter.sum_sumcheckPolyAlpha'`;
- `ArkLib.Lattices.Ajtai.InnerOuter.sum_sumcheckPolyZero'`.

Those files are byte-identical to `origin/main` in the synthetic merge and are not touched or
depended on by this coding-theory PR; this is target-branch baseline drift after the axiom baseline
was last updated, not a PR #701 regression. The native `axiomsweep` executable also asks Lake to
compile optional VCVio C bindings whose git submodules are absent in a cold dependency checkout;
the same sweep source was therefore run directly with `lake env lean --run scripts/AxiomSweep.lean`.

Hosted PR checks remain the final external gate because the target branch can move after this
document is written.
