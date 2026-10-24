---
kind: paper
bibkey: Hab22
title: "Multivariate lookups based on logarithmic derivatives"
year: 2022
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2022/1530
source_metadata: ../sources/Hab22/metadata.yml
status: active-audit
related_concepts:
  - logup
related_modules:
  - ArkLib/Data/Polynomial/PartialFractions.lean
  - ArkLib/Data/Vector/Histogram.lean
  - ArkLib/Data/Vector/Lookup.lean
  - ArkLib/Data/Vector/LookupNormalization.lean
  - ArkLib/Data/Fin/ConsecutiveChunks.lean
  - ArkLib/Data/MvPolynomial/Multilinear.lean
  - ArkLib/ProofSystem/Logup/Algebra/Grouped.lean
---

# Hab22

## At A Glance

Ulrich Haböck's [ePrint 2022/1530](https://eprint.iacr.org/2022/1530) develops lookup arguments
using logarithmic derivatives. ArkLib follows the grouped construction in Protocol 2 of the
March 31, 2023 document, with explicit changes to its witnesses, sampling and error analysis.
The [source comparison](../concepts/logup.md) records pinned implementation references; the
[design](../../design/logup.md) states the complete executable protocol's remaining obligations.

## Version And Source

Statement numbers here refer to the [author-uploaded PDF](https://www.researchgate.net/profile/Ulrich-Haboeck/publication/371339784_Multivariate_lookups_based_on_logarithmic_derivatives_logUp/links/647f6b5cb3dfd73b77698c3c/Multivariate-lookups-based-on-logarithmic-derivatives-logUp.pdf),
whose title page is dated March 31, 2023. The ePrint landing page reports receipt on
November 4, 2022 and an archive update on February 20, 2025. The latter is not the document date
used for this correspondence. No comparison with the current ePrint PDF's bytes is claimed.

The author copy was inspected through web PDF extraction. Raw PDF downloads and ePrint's version
history were inaccessible during this audit, so no local PDF digest is available. The
[source metadata](../sources/Hab22/metadata.yml) records this limitation; the canonical live URL
must not be treated as a byte-pinned March 2023 artifact.

## What ArkLib Uses From This Paper

| Paper location | ArkLib connection |
| --- | --- |
| Section 2.1, Lemma 1 | The equality kernel and `MLE_eval` in [Multilinear.lean](../../../ArkLib/Data/MvPolynomial/Multilinear.lean) express a table's multilinear extension as a kernel-weighted Boolean sum. |
| Section 2.3, Lemma 4 | [PartialFractions.lean](../../../ArkLib/Data/Polynomial/PartialFractions.lean) proves distinct-pole uniqueness and finite-support weighted-fiber vanishing over arbitrary fields. |
| Section 2.3, Lemma 5; Section 3, Eq. (14) | [Histogram.lean](../../../ArkLib/Data/Vector/Histogram.lean) and [Lookup.lean](../../../ArkLib/Data/Vector/Lookup.lean) provide constructive forward weights and a converse under nonvanishing query counts. [LookupNormalization.lean](../../../ArkLib/Data/Vector/LookupNormalization.lean), `Vector.sumFiber_normalizedLookupWeights_eq_histogram`, proves aggregate correspondence with normalized weights under explicit nonzero table normalizers. |
| Section 3.1, Protocol 2 | [Grouped.lean](../../../ArkLib/ProofSystem/Logup/Algebra/Grouped.lean) supplies the executable group circuit and its polynomial and clearing correspondence. [ConsecutiveChunks.lean](../../../ArkLib/Data/Fin/ConsecutiveChunks.lean) certifies the grouping pattern. The native grouped argument remains under development. |
| Section 3.2, Theorem 4 | The printed numerical ledger is a comparison target. ArkLib derives its own bound for its actual sampling and verifier execution. |

## Main ArkLib Touchpoints

These are semantic correspondences. Supporting generic lemmas do not claim a complete
formalization of the corresponding paper protocol.

## Deliberate Differences

- The general statement is field-valued weight balance. Lookup inclusion additionally needs
  positive query counts to remain nonzero after casting; integer interpretations are separate.
- The honest multiplicities are natural histograms of supplied lookup indices, cast afterward.
  Duplicate table values are supported without division. Correspondence with the paper's
  normalized assignment requires its normalizing table counts to be nonzero; the proved
  correspondence is per-key aggregate equality, allowing different messages at duplicate positions.
- The runtime Boolean domain is `{0,1}^n`. Correspondence with the paper's `{−1,1}^n` uses the
  coordinatewise affine equivalence when two is invertible; weighted balance itself also works
  in characteristic two.
- The proposed verifier samples its scalar challenge from the whole field. This follows the
  imperfect-completeness option discussed in Remark 3; completeness must account for poles.
- Scalar soundness uses denominator-cleared regrouping at poles and one residual table selected
  before the kernel challenge. The design targets `(D+n*(ell+3))/|E|`; it does not import the
  paper's printed `K/|F|` kernel contribution.

## Completion Boundary

The reusable fraction, histogram, grouping and circuit facts are supporting mathematics. Completion still
requires the actual native grouped protocol, arbitrary-prover soundness, honest executable
Sumcheck messages, the terminal oracle check, and their execution and query theorems. Tuple and
bus compression is a separate adapter. Neither fractional GKR nor LogUp* is verified merely by
formalizing this paper's grouped construction.

## Source Access

- [Bibliography entry](../../../blueprint/src/references.bib), key `Hab22`.
- [Source metadata](../sources/Hab22/metadata.yml).
- [ePrint landing page](https://eprint.iacr.org/2022/1530).
