---
kind: paper
bibkey: Hab22
title: "Multivariate lookups based on logarithmic derivatives"
year: 2022
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2022/1530
source_metadata: ../sources/Hab22/metadata.yml
status: seeded
related_concepts:
  - logup
related_modules:
  - ArkLib/Data/Polynomial/PartialFractions.lean
  - ArkLib/Data/Vector/Histogram.lean
  - ArkLib/Data/Vector/Lookup.lean
  - ArkLib/Data/Vector/LookupNormalization.lean
  - ArkLib/Data/Fin/ConsecutiveChunks.lean
  - ArkLib/Data/MvPolynomial/Multilinear.lean
  - ArkLib/Data/MvPolynomial/BooleanSigned.lean
  - ArkLib/ProofSystem/Logup/Algebra/Grouped.lean
  - ArkLib/ProofSystem/Logup/Interaction/Protocol.lean
  - ArkLib/ProofSystem/Logup/Security/Soundness.lean
  - ArkLib/ProofSystem/Logup/Security/Completeness.lean
  - ArkLib/ProofSystem/Logup/Lookup/Tuple/Security.lean
---

# Hab22

## At A Glance

Ulrich Haböck's [ePrint 2022/1530](https://eprint.iacr.org/2022/1530) develops lookup arguments
using logarithmic derivatives. ArkLib follows the grouped construction in Protocol 2 of the
March 31, 2023 document, with explicit changes to its witnesses, sampling and error analysis.
The [source comparison](../concepts/logup.md) records pinned implementation references; the
[design](../../design/logup.md) describes the delivered complete native variants and their
precise resource and protocol boundaries.

## Version And Source

Statement numbers follow the inspected author copy dated March 31, 2023. The
[source metadata](../sources/Hab22/metadata.yml) identifies that copy and the later reported
archive revision; their byte identity has not been verified.

## What ArkLib Uses From This Paper

| Paper location | ArkLib connection |
| --- | --- |
| Section 2.1, Eq. (1) and Lemma 1 | [Multilinear.lean](../../../ArkLib/Data/MvPolynomial/Multilinear.lean) supplies the Boolean kernel and MLE. In [BooleanSigned.lean](../../../ArkLib/Data/MvPolynomial/BooleanSigned.lean), `MvPolynomial.bind₁_eqPolynomial'_halfShift` and `MvPolynomial.bind₁_MLE_halfShift` prove formal transport to the signed kernel, including its `2^(-n)` normalization, under explicit nonzero two. |
| Section 2.3, Lemma 4 | [PartialFractions.lean](../../../ArkLib/Data/Polynomial/PartialFractions.lean) proves distinct-pole uniqueness and finite-support weighted-fiber vanishing over arbitrary fields. |
| Section 2.3, Lemma 5; Section 3, Eq. (14) | [Histogram.lean](../../../ArkLib/Data/Vector/Histogram.lean) and [Lookup.lean](../../../ArkLib/Data/Vector/Lookup.lean) provide constructive forward weights and a converse under nonvanishing query counts. [LookupNormalization.lean](../../../ArkLib/Data/Vector/LookupNormalization.lean), `Vector.sumFiber_normalizedLookupWeights_eq_histogram`, proves aggregate correspondence with normalized weights under explicit nonzero table normalizers. |
| Section 3.1, Protocol 2 | [Algebra/Grouped.lean](../../../ArkLib/ProofSystem/Logup/Algebra/Grouped.lean) supplies the executable group circuit and its polynomial and clearing correspondence. [ConsecutiveChunks.lean](../../../ArkLib/Data/Fin/ConsecutiveChunks.lean) certifies the grouping pattern. [Interaction/Protocol.lean](../../../ArkLib/ProofSystem/Logup/Interaction/Protocol.lean) selects the native Sumcheck suffix and complete retained-source terminal check. |
| Section 3.2, Theorem 4 | `Logup.Interaction.uniformExecute_soundness` in [Security/Soundness.lean](../../../ArkLib/ProofSystem/Logup/Security/Soundness.lean) proves `(T*2^n+n*(ell+3))/\|E\|` for the actual complete endpoint and arbitrary whole native provers. It derives its own residual/root/batching ledger rather than importing the printed constants. |

## Main ArkLib Touchpoints

The [design](../../design/logup.md) describes ArkLib's protocol and resource contracts; the
[code-local index](../../../ArkLib/ProofSystem/Logup/README.md) locates its executable endpoints
and theorem owners. The correspondences above retain the deliberate differences below rather
than asserting that every paper variant or numerical statement is formalized unchanged.

## Deliberate Differences

- The general statement is field-valued weight balance. Lookup inclusion additionally needs
  positive query counts to remain nonzero after casting; integer interpretations are separate.
- The honest multiplicities are natural histograms of supplied lookup indices, cast afterward.
  Duplicate table values are supported without division. Correspondence with the paper's
  normalized assignment requires its normalizing table counts to be nonzero; the proved
  correspondence is per-key aggregate equality, allowing different messages at duplicate positions.
- The runtime Boolean domain is `{0,1}^n`. Correspondence with the paper's `{−1,1}^n` uses the
  executable `MvPolynomial.signedCubeEquiv` and formal substitution identities in
  [BooleanSigned.lean](../../../ArkLib/Data/MvPolynomial/BooleanSigned.lean) under explicit
  invertibility of two. Weighted balance itself also works in characteristic two.
- The verifier samples its scalar challenge from the whole field. This follows the imperfect-
  completeness option discussed in Remark 3. Honest termwise-total helpers are executable at poles;
  their acceptance theorem is off-pole, with the resulting support-size failure bound.
- Scalar soundness uses denominator-cleared regrouping at poles and one residual table selected
  before the kernel challenge. The proved bound is `(D+n*(ell+3))/|E|`; it does not import the
  paper's printed `K/|F|` kernel contribution.

## Scope

ArkLib's grouped weighted, scalar indexed and typed tuple/bus indexed arguments have complete
interactive endpoint theorems, described in the [design](../../design/logup.md). Tuple compression
adds selected-key soundness loss while preserving honest balance for every beta. Bounded cast-count
permutation recovery is algebraic; scalar inclusion plus equal lengths alone does not establish
a permutation protocol. Fractional GKR, LogUp*, heterogeneous-height AIR packing, polynomial
commitments, Fiat–Shamir, zero knowledge and cross-language program equivalence are separate
protocol developments.

## Source Access

- [Bibliography entry](../../../blueprint/src/references.bib), key `Hab22`.
- [Source metadata](../sources/Hab22/metadata.yml).
- [ePrint landing page](https://eprint.iacr.org/2022/1530).
