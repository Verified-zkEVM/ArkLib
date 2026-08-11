# PR 701 source/provenance audit

Date: 2026-08-11. Audited head `3c303efa61f16dec87e7cb39856efd439374d099`
against PR/base merge base `5fea8abf971496f54bcca2b98c029581d5b31658`.
This audit is read-only; no repository source was edited.

## Reproducible inventory

The extractor was run once at the PR head and once on an archive of the merge base:

```text
python3 scripts/kb/extract_declarations.py --root ArkLib --out /tmp/pr701-head-decls.json
git archive 5fea8abf971496f54bcca2b98c029581d5b31658 ArkLib scripts/kb | tar -x -C <tmp-base>
python3 <tmp-base>/scripts/kb/extract_declarations.py --root <tmp-base>/ArkLib \
  --out /tmp/pr701-base-decls.json
```

The resulting declaration-level map is `/tmp/pr701-source-map.json`. It has all 177 raw names
found by the deterministic delta. Two are extractor artefacts: `_root_.Fintype.card_fun_fin_one_eq`
and `_root_.PMF.map_uniformOfFintype_of_fiber_const` occur textually inside `namespace Probability`,
which the regex extractor incorrectly prefixes even though their actual Lean names remain at root.
Of the 175 actual declaration changes, 21 are pre-existing declarations whose namespace changed,
leaving **154 genuinely new named declarations**. Category counts over those 154 are: 26 exact
source matches, 100 supporting declarations, 8 material generalisations, 6
deviations/corrections/partial abstractions, and 14 infrastructure declarations. The classification
is deliberately conservative: a theorem proving a cited item is `exact`;
private proof machinery and public bridges are `support`; a definition with broader harmless typeclass
generality is `generalization`; and a corrected source hypothesis or an image-level replacement for an
encoder-level source object is `deviation`.

The 21 namespace moves are the probability helper family
`prob_tsum_form_singleton` through `Pr_seq_le_of_forall_le`, the legacy
`prob_schwartz_zippel_mv_polynomial`, and `Pr_uniform_equiv`. They are not new paper coverage.

A syntax-aware review of the added declarations found no actual `sorry`, `admit`, or new `axiom`;
the only diff matches are explanatory prose containing those words. This is a proof-hole census,
not a substitute for the separate compiled `#print axioms`/build audit.

## Source corpus checked first-hand

- Current author TeX `/home/alh/ef-millenium/ef-millenium.tex`, especially L2.1
  (1035-1044), D2.2-D2.21 (1087-1323), D3.1-C3.3 (1340-1358), D6.4/L6.5
  (2244-2258), A.6/A.7 (3324-3346), and Claim B.1 (3351-3380).
- Supplied ABF26 PDF, physical pages 6-12, 26, 41-42. Its creation date is 2026-04-08.
- GK16: Definition 11 (PDF p7), Lemma 12 (p8), Theorem 14 (p9).
- GG25: Definition 2.15 and Lemma 2.16 (PDF p11), Definition 2.18 and Theorem 2.19
  (p12).
- GR08: Definition 2.1 (PDF p8).
- GW13: Definition 8, ordinary formal derivative code (PDF p13); KSY14 Definitions 5 and 8,
  Hasse-derivative multiplicity codes (PDF pp7-8).
- BCFW25 Appendix D.2 and Lemma D.3 (printed p70; physical PDF p71).
- Diamond-Posen preprint corresponding to DP25, Definition 3.1 and Theorem 3.2 (PDF p12).
- GX13 was checked for the historical collection-of-subspaces notion. No local Joh62 or GRS
  primary artifact was available, so claims about those two are checked via ABF26/current TeX and
  the in-tree proof/citation trail, not presented as first-hand verification of the originals.

## Declaration coverage map by cluster

| Lean declarations | Classification | Source statement and result |
|---|---|---|
| `Probability.prob_polynomial_identity_le` (`Probability/Instances.lean:589`) | exact | ABF26 L2.1, PDF p6 / TeX 1035-1044. The finite-domain generality is harmless; a finite integral domain is a field. `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le` (`:550`), `prob_eval_zero_univ_le_div` (`MvPolynomial/SchwartzZippelCounting.lean:153`), and `totalDegree_le_of_degreeOf_lt` (`MvPolynomial/Degrees.lean:210`) are sound support/generalisation. |
| `qEntropy`, `qEntropy_eq_logb_form` (`Basic/Entropy.lean:80,98`) | exact | ABF26 D2.2, PDF p7 / TeX 1087-1093. The remaining 14 declarations in this module (`:88,107-206`) transport Mathlib's entropy API and totalise the degenerate `q <= 1` cases; support, not extra paper claims. |
| `disagreementCols` and four bridges (`Basic/Distance.lean:165-255`); `eq_of_consistent_with_erased` (`Erasure.lean:52`) | support only | Metric uniqueness used by D6.4/L6.5. They do **not** express the deterministic decoder or its cost. |
| five `minRelHammingDistCode` bridges (`Basic/RelativeDistance.lean:603-659`) | support | ABF26 D2.5 minimum-relative-distance normalisation. The implementation of the pre-existing `minRelHammingDistCode` was refactored without changing its signature. |
| `LinearCode.alphabetRate` (`Basic/LinearCode.lean:279`) | exact only for the F-linear module-alphabet specialization | ABF26 D2.5, PDF p8 / TeX 1124-1130. The three bridges at `:285-299` are support. It correctly uses `finrank/(s*n)`, unlike pre-existing `rate = finrank/n`. A general finite-alphabet/nonlinear `Code.rate` is absent. |
| `singleton_bound_module` and `IsMDS_iff_rate_distance` (`Basic/LinearCode.lean:680,716`) | generalisation / exact field specialization | ABF26 L2.6, PDF p8 / TeX 1136-1143. The cardinality Singleton bound was pre-existing. The new MDS predicate bridge remains field-linear; it does not cover arbitrary alphabets or module alphabets. |
| `hammingBallVolume` (`HammingBallVolume.lean:68`) and three bridges (`:75,86,185`) | exact / support | ABF26 D2.4, PDF p8 / TeX 1110-1115. Totalisation beyond `delta in (0,1)` is explicit and harmless. |
| `ListDecodable.Lambda` (`ListDecodability.lean:136`) and 14 bridges/order/finite bounds (`:151-309`) | exact / support | ABF26 D2.8, PDF p8 / TeX 1155-1163. `encard` correctly maps infinite lists to top. The changed pre-existing `listDecodable` at `:90-92` now records point-list finiteness and removes the old infinite-alphabet `ncard = 0` vacuity; it is equivalent in ABF26's finite-alphabet regime and is a sound strengthening of the library abstraction. |
| `moduleInterleavedCodeEquiv`, `finrank_moduleInterleavedCode` (`InterleavedCode.lean:386,402`) | support | Existing `interleavedCodeSet` already represents ABF26 D2.9; the new declarations support D2.13 and later L2.10 consumers. |
| `irsCode` (`ReedSolomon/Interleaved.lean:60`) | exact | ABF26 D2.13, PDF p9 / TeX 1206-1211. `dim_irsCode` and `_of_dvd` (`:71,81`) are correct supporting facts. Natural division is a documented totalisation of the paper's intended divisible case. |
| `ReedSolomon.Folded.Admissible` (`Folded.lean:110`) | deviation/correction | ABF26 D2.14, PDF p10 / TeX 1217-1219, is defective: its distinct-pair clause admits omega=1 and zero in the domain. Lean adds the intra-orbit clause required by GR08 Definition 2.1's injective evaluation sequence. This necessarily makes downstream theorems weaker than ABF26 as printed, but avoids false statements. |
| `frsEvalOnPoints`, `frsCode`, `mem_frsCode_iff` (`Folded.lean:126,150,158`) | source-faithful generalisation | ABF26 D2.15, PDF p10 / TeX 1222-1236, and GR08 Definition 2.1, PDF p8. Lean permits any injected/admissible domain, whereas GR08 fixes the generator-ordered nonzero field domain. The remaining folded declarations (`:181-358,554-582`) correctly establish injectivity, RS transport, dimension, block minimum distance, and `s=1` collapse. |
| `IsSubspaceDesign` (`SubspaceDesign.lean:83`) | exact | ABF26 D2.16, PDF p10 / TeX 1245-1251; code-side version appearing as GG25 Definition 2.15, PDF p11. GX13 is the historical source of the collection-of-subspaces notion, not literally this code predicate. |
| `subspaceDesign_tau_lower_of_ne_bot`, `subspaceDesign_tau_lower` (`SubspaceDesign.lean:150,296`) | corrected deviation | ABF26 L2.17 / GG25 Lemma 2.16, PDF pp10/11. Both sources' all-natural-`r` statement is false at `r=0`; the source proof uses a 1-dimensional subspace. Lean gives the maximal honest range `r>=1`, correct alphabet rate `finrank/(s*n)`, and explicit nontrivial-code or nonnegative-profile guards needed at the trivial code. No unlicensed weakening was found. |
| `frs_is_subspaceDesign_gk16` (`SubspaceDesign.lean:488`) and proof helpers (`:318,342`) | corrected, FRS-only part | ABF26 T2.18, PDF p10 / TeX 1263-1276, and GK16 Theorem 14, PDF p9. Lean restores GK16's generator hypothesis and the domain-injectivity condition omitted by ABF26/GG25. Both are load-bearing; the source-shaped versions admit explicit counterexamples. The FRS half is genuinely proved for every `r`, but the UM half of T2.18 is absent. |
| `foldedWronskian` (`Polynomial/FoldedWronskian.lean:64`) and criterion (`:227,268,291`) | exact / support | GK16 Definition 11 (PDF p7) and Lemma 12 (p8), including generator and degree/cardinality guard. Degree and determinant helpers (`:69,101`, plus ToMathlib Kummer, determinant, root-multiplicity, composition-degree, adapted-basis/finrank declarations) are appropriate generic infrastructure for GK16 Theorem 14. |
| `umEvalOnPoints`, `umCode` (`ReedSolomon/Multiplicity.lean:103,120`) | exact on ABF26's intended parameters | ABF26 A.6/A.7, PDF p41 / TeX 3324-3346, and GW13 Definition 8, PDF p13: iterated **ordinary** derivatives. The bare map is harmlessly defined at `CommSemiring` generality; field finiteness and `char(F)>=k` are semantic conditions for code properties, not for forming the map. KSY14 uses Hasse derivatives, so it is only a historical multiplicity-code citation, not the exact definition being implemented. The `s=1` RS bridge (`:137`) is support. |
| `ExtensionFieldPresentation` and its coordinates/systematic predicate (`ExtensionCodes.lean:104-140`) | exact | ABF26 D2.19, PDF p11 / TeX 1286-1296. Reusing Mathlib `Algebra` and `Basis` is the right ArkLib abstraction. |
| `extensionCode` and image/submodule API (`ExtensionCodes.lean:163-371`) | deviation/partial | ABF26 D2.20 / BCFW25 Appendix D.2 is encoder-level. Lean represents only the image code. Closure, span, presentation independence, and the image-level systematic membership theorem are valid, but they do not state the source encoder nor `C_F(psi(v)) = psi(C_B(v))`. |
| `lambda_extensionCode_eq_lambda_interleaved` (`ExtensionCodes.lean:414`) | exact generalisation | ABF26 L2.21, PDF p11 / TeX 1320-1323; BCFW25 Lemma D.3, printed p70. Lean proves it for every real radius using the coordinate Hamming isometry. |
| `Jcap` (`JohnsonBound/Basic.lean:64`) and `Jqell` family (`JohnsonBound/Family.lean:94-105`) | exact current-TeX match | ABF26 D3.1, PDF p12 / TeX 1340-1347. See the PDF/TeX divergence below. |
| `johnson_bound_lambda_le_ell` (`JohnsonBound/Family.lean:536`) | exact/generalised | ABF26 T3.2, PDF p12 / TeX 1349-1352. It is correctly alphabet-generic, includes the necessary `ell>=1` guard because the paper's `ell=0` expression is undefined, and closes the radicand-negative Plotkin corner rather than weakening the theorem. Supporting cardinality/Plotkin declarations are at `:131-386`; pre-existing Johnson theorems were validly generalized from fields to arbitrary finite alphabets. |
| `mds_johnson_lambda_le` (`JohnsonBound/Family.lean:689`) | partial deviation | ABF26 C3.3, PDF p12 / TeX 1354-1358, is for all MDS codes and explicitly motivates module-alphabet interleaved RS. Lean proves only `LinearCode ι F` over the field alphabet. RS and `listDecodable` consumers (`:960,975,989`) are valid support but do not close the general statement. |
| `exists_large_image_of_pairwise_collision_bound` (`Probability/Combinatorial.lean:215`) | exact | ABF26 Claim B.1, PDF p42 / TeX 3351-3380. Its private fiber/Cauchy-Schwarz lemmas (`:52,60,132`) are support. Empty-set totalisation is harmless. |
| `Pr_map_eq`, dot-product probability equality/bound, singleton-uniform bound, tuple product bound (`Probability/Instances.lean:685-810`) | support | Correct inputs for ABF26 section 6.4.1 / Lemma 6.12. They do not themselves prove Lemma 6.12. The paper uses Claim B.1 once; the singleton step is a pigeonhole/injectivity step, which the current docstrings now state correctly. |
| Fin induction helpers, generic probability notation, Hamming transport, determinant/root/degree/finite-dimensional/Kummer helpers | infrastructure | No standalone ABF26 statement is claimed. The algebra/probability/Hamming helpers have concrete proof consumers. `Fin.induction_three` has a concrete ToyProblem consumer on the visible later-plan branch; no consumer was found for its alternate spelling `Fin.induction_three'`, so that one is a low-priority scope/library-value question rather than source coverage. No vacuous paper theorem is hidden here. |

## Modified pre-existing declarations

- `ListDecodable.listDecodable` (`ListDecodability.lean:90-92`) was semantically strengthened
  with point-list finiteness. This fixes a real infinite-alphabet vacuity and is equivalent in the
  paper's finite-alphabet setting.
- `JohnsonBound.johnson_condition_weak_implies_strong`, `johnson_bound`, and
  `johnson_bound_alphabet_free` (`JohnsonBound/Basic.lean:119,281,300`) and
  `e_ball_le_radius` / `min_dist_le_d` (`JohnsonBound/Expectations.lean:70,91`) had field
  assumptions removed. Their proofs are combinatorial; this is a justified generalisation.
- `sqrt_le_J` now spells its definitionally equal left side as `Jcap`; no mathematical change.
- `Code.minRelHammingDistCode` changed implementation to use its explicit finite-set proof;
  no signature or value change (proof irrelevance).
- `LinearCode.rate` changed documentation only, correctly warning that it is not alphabet-normalised
  for a module alphabet.
- Probability declarations listed in the JSON as namespace moves retain their statements. The new
  root placement of `PMF.map_uniformOfFintype_of_fiber_const` and
  `Fintype.card_fun_fin_one_eq` is also a namespace correction, not new mathematics.

## Printed PDF versus current author TeX

1. **D3.1 is the only current-TeX/PDF formula divergence found in this PR's mapped paper
   statements.** The April PDF p12 prints `ell/(ell-1)` inside `J_{q,ell}`. Current TeX line
   1343 uses `(ell-1)/ell`. The PDF form is mathematically wrong: it diverges at `ell=1`, gives
   the wrong monotonicity, and can make the radicand negative in the wrong regime. Lean
   `Jqell` at `JohnsonBound/Family.lean:94` correctly follows the current author TeX and the
   standard Johnson formula; it must not be changed back to the PDF.
2. **D2.14 is defective in both PDF and current TeX**, rather than a version divergence. Lean's
   explicitly documented strengthening is required for the FRS distance and subspace-design
   statements.
3. **T2.18 and the GG25 restatement omit hypotheses in both supplied sources.** Lean's generator
   and orbit-injectivity assumptions match the ultimate GK16 construction and avoid false claims.
4. **L2.17/GG25 Lemma 2.16 is false at `r=0` in both sources.** Lean's `r>=1` correction is
   the maximal range licensed by their proof.

## Material coverage gaps

### Must be resolved or explicitly accepted as outside this split

1. **T2.18 multiplicity-code half is missing.** ABF26 TeX 1263-1276 says both FRS and UM;
   only `frs_is_subspaceDesign_gk16` exists. This is explicitly documented at
   `SubspaceDesign.lean:45-52` and is not implemented on the visible `feat/abf26-plan`
   branch. It needs the multiplicity-Wronskian analogue, not a weakened theorem.
2. **D2.20 is not actually covered at encoder level.** ABF26 TeX 1301-1313 and BCFW25
   Appendix D.2 require an encoder `extensionEncode` and the systematic identity
   `C_F(psi v)=psi(C_B v)`. `extensionCode` is a valid image abstraction, but cannot express
   that statement. The coverage matrix currently labels D2.20 simply `present`; it should be
   `partial/present-but-different` until the encoder API lands.
3. **The extension minimum-distance equality is absent.** ABF26 TeX 1316 cites DP25 Theorem
   3.2; the supplied Diamond-Posen preprint states on PDF p12 that the extension code has exactly
   the base code's distance. No `minDist_extensionCode`/relative-distance equality exists.
4. **C3.3 is only a field-alphabet specialization.** The source is arbitrary-alphabet MDS and
   expressly includes interleaved RS. `mds_johnson_lambda_le` cannot state that case. A general
   finite-code rate/MDS abstraction (or at least a module-alphabet rate-distance bridge) is needed.
   No corresponding general implementation was found on the visible later-plan branch.
5. **D2.5 rate is also only partially general.** `alphabetRate` handles F-linear `F^s` alphabets,
   which is the important additive specialization, but ABF26 defines rate for every finite-alphabet
   code. This is the same abstraction gap that blocks full C3.3.
6. **D6.4/L6.5 are missing, not proved.** Current Lean contains only metric uniqueness. D6.4
   (ABF26 PDF p26 / TeX 2244-2252) requires a deterministic algorithm correct below minimum
   distance and a correction-time quantity; L6.5 (TeX 2255-2258) is the additive-code
   `O((s*n)^3)` bound. The published PR body previously claimed declarations that were deleted
   as tautological; that body must be synchronized with the current honest `missing` status.

### Verified intentional later splits

- D2.3 restricted Hamming distance is absent here and exists on `feat/abf26-plan` as
  `restrictedRelHammingDist`, next to proximity-gap consumers. The audit's current
  `present-but-different` status is nevertheless misleading for the literal paper item; use
  `deferred/missing in PR-1`.
- L2.10 interleaved list-size bound is absent here and has a later
  `ListDecoding/Interleaved.lean` target. The visible plan version is still an external `sorry`, so
  it is not completed coverage yet.
- T3.4-C3.5 and the rest of section 3, sections 4-5, and the toy constructions in section 6 are
  intentionally separated into later list-decoding, proximity-gap, and toy-problem splits. This
  PR supplies many prerequisites but should not claim the theorems themselves.
- Claim B.1's intended Lemma 6.12 consumer is later; the current support lemmas are accurately
  only inputs.

## Citation and documentation accuracy findings

1. **Stale false paper pages introduced/modified by this PR:**
   - `docs/kb/papers/GR08.md:72-81,100` says the RS-on-folded-domain bridge is absent and
     dimension was rederived; `frsCode_eq_map_rsCode` exists at `Folded.lean:252`, and dimension
     transports through it at `:323`.
   - `docs/kb/papers/GR08.md:93-94` says neither source requires coset/orbit structure. GR08
     Definition 2.1 (PDF p8) specifically takes all nonzero field elements in generator order and
     groups consecutive evaluations. Only ABF26 generalizes to arbitrary admissible `L`.
   - `docs/kb/papers/GR08.md:102-104` says the admissibility quantifier order defeats
     decidability; current `Folded.lean:78-80,120-122` intentionally reordered it and provides the
     instance.
   - `docs/kb/papers/GG25.md:94` says the all-`r>=1` Lemma 2.16 remains missing; current
     `SubspaceDesign.lean:150-156,296-303` proves it.
   - `docs/kb/papers/GK16.md:106` says Theorem 14 is instantiated only at `r=1`; current
     `frs_is_subspaceDesign_gk16` proves `IsSubspaceDesign`, whose quantifier is every `r`.
   - `docs/kb/papers/GK16.md:110-112` says the generic determinant helper remains in the
     Polynomial namespace; it is now `Matrix.pow_dvd_det_of_forall_mem_col_dvd` at
     `ToMathlib/LinearAlgebra/Matrix/Determinant.lean:19`.
   - `docs/kb/papers/ABF26.md:180-182` describes a current docstring as incorrectly applying
     Claim B.1 twice, but current docstrings explicitly say once. `:183-186` says the two cheap
     RS/Johnson integrations are unimplemented, but they now exist at
     `JohnsonBound/Family.lean:960,975,989`.
2. **Coverage labels should be made literal.** In
   `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md:32`, D2.3 is absent
   from this branch and should not be `present-but-different`. At `:49`, D2.20 should say
   `partial/present-but-different`, because the row itself acknowledges the encoder and distance
   gaps. T2.18's `present (FRS half only)` wording is sufficiently explicit.
3. **Several new source-facing docstrings violate CONTRIBUTING's machine-readable citation
   convention.** `Basic/LinearCode.lean:246,268,291,713`,
   `Basic/RelativeDistance.lean:647,653`, `Probability/Instances.lean:572,658-662,707,760,770`,
   and `JohnsonBound/Basic.lean:48,51,74` say `ABF26` in prose without `[ABF26]`; the first three
   files also do not list ABF26 in their module References section (Probability Instances has no
   References section at all). The fresh citation extraction therefore omits these real provenance
   edges. Citation keys themselves (`ABF26`, `BCFW25`, `DP25`, `GG25`, `GK16`, `GR08`, `GW13`,
   `KSY14`, `GX13`, `Joh62`, `codingtheory`) all resolve in the current BibTeX; the issue is missing
   citation syntax, not dangling keys.

## Overall source-faithfulness verdict

No new Lean theorem inspected here silently weakens a source claim merely to obtain a proof. The
Johnson, FRS-distance, folded-Wronskian, list-cardinality, extension-list-size, and Claim-B.1 statements
map soundly to their sources; generalisations are mathematically appropriate. The extra assumptions in
D2.14/L2.17/T2.18 are honest, necessary repairs to false printed statements and are documented in
hypothesis position.

The PR is **not yet source-complete or documentation-valid** as a complete ABF26 coding-theory
foundation: the six material gaps above remain (three of them are explicitly acknowledged in Lean), the
published PR body is stale about erasure coverage/sorries, and multiple committed knowledge-base pages
contain assertions contradicted by this very head. Those need resolution or an explicit, accurate split
contract before treating PR 701 as entirely validated.
