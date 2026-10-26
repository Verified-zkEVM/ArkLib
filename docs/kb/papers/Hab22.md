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
  - ArkLib/Data/MvPolynomial/BooleanSigned.lean
  - ArkLib/ProofSystem/Logup/Algebra/Grouped.lean
  - ArkLib/ProofSystem/Logup/Interaction/Protocol.lean
  - ArkLib/ProofSystem/Logup/Security/Weighted.lean
  - ArkLib/ProofSystem/Logup/Prover/Completeness.lean
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
| Section 2.1, Eq. (1) and Lemma 1 | [Multilinear.lean](../../../ArkLib/Data/MvPolynomial/Multilinear.lean) supplies the Boolean kernel and MLE. In [BooleanSigned.lean](../../../ArkLib/Data/MvPolynomial/BooleanSigned.lean), `MvPolynomial.bind₁_eqPolynomial'_halfShift` and `MvPolynomial.bind₁_MLE_halfShift` prove formal transport to the signed kernel, including its `2^(-n)` normalization, under explicit nonzero two. |
| Section 2.3, Lemma 4 | [PartialFractions.lean](../../../ArkLib/Data/Polynomial/PartialFractions.lean) proves distinct-pole uniqueness and finite-support weighted-fiber vanishing over arbitrary fields. |
| Section 2.3, Lemma 5; Section 3, Eq. (14) | [Histogram.lean](../../../ArkLib/Data/Vector/Histogram.lean) and [Lookup.lean](../../../ArkLib/Data/Vector/Lookup.lean) provide constructive forward weights and a converse under nonvanishing query counts. [LookupNormalization.lean](../../../ArkLib/Data/Vector/LookupNormalization.lean), `Vector.sumFiber_normalizedLookupWeights_eq_histogram`, proves aggregate correspondence with normalized weights under explicit nonzero table normalizers. |
| Section 3.1, Protocol 2 | [Grouped.lean](../../../ArkLib/ProofSystem/Logup/Algebra/Grouped.lean) supplies the executable group circuit and its polynomial and clearing correspondence. [ConsecutiveChunks.lean](../../../ArkLib/Data/Fin/ConsecutiveChunks.lean) certifies the grouping pattern. [Interaction/Protocol.lean](../../../ArkLib/ProofSystem/Logup/Interaction/Protocol.lean) selects the native Sumcheck suffix and complete retained-source terminal check. |
| Section 3.2, Theorem 4 | `Logup.Interaction.uniformExecute_soundness` in [Weighted.lean](../../../ArkLib/ProofSystem/Logup/Security/Weighted.lean) proves `(T*2^n+n*(ell+3))/\|E\|` for the actual complete endpoint and arbitrary whole native provers. It derives its own residual/root/batching ledger rather than importing the printed constants. |

## Main ArkLib Touchpoints

The [weighted execution law](../../../ArkLib/ProofSystem/Logup/Interaction/Execution.lean)
preserves the actual prefix, source routing, private continuations and final authentication.
[Prover/Completeness.lean](../../../ArkLib/ProofSystem/Logup/Prover/Completeness.lean) proves
off-pole supported acceptance, uniform failure/success bounds and total mass one. The selected
[default prover](../../../ArkLib/ProofSystem/Logup/Prover/ArithmeticStrategy.lean) constructs
formal coefficient messages directly from cached evaluation tables. Scalar and typed tuple/bus
adapters have their own complete execution, security and completeness owners under
[Lookup/](../../../ArkLib/ProofSystem/Logup/Lookup/).

These are semantic correspondences with explicit changes below, not a claim that every variant
or numerical statement in the paper has been formalized unchanged.

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

## Completion Boundary

The delivered protocols are grouped weighted balance, scalar indexed lookup, and typed tuple/bus
indexed lookup. Each has an executable terminal check, arbitrary whole-prover soundness and
honest completeness. Explicit indexed histograms construct multiplicities; measured defaults
construct helpers, cached table folds and streamed formal Sumcheck messages. Query/backend,
sampling, instruction and logical-storage accounting retain distinct metrics and explicit opaque
source/workspace boundaries; they are not machine-time or allocator-peak theorems. The
[actual packet/source laws](../../../ArkLib/ProofSystem/Logup/Interaction/Resources.lean) preserve
prefix effects and terminal authentication logs. The
[sampling consumers](../../../ArkLib/ProofSystem/Logup/Interaction/SamplingResources.lean) prove
exact supported endpoint Bool/log correspondence and named honest-default primitive totals,
without bounding arbitrary malicious private sampling or asserting losslessness.

The tuple adapter adds selected-key fingerprint soundness and preserves honest balance for every
beta. Bounded cast-count permutation recovery is algebraic; scalar inclusion plus equal lengths
alone does not establish a permutation protocol. Fractional GKR, LogUp*, heterogeneous-height AIR
packing, polynomial commitments, Fiat–Shamir, zero knowledge and cross-language program equivalence
are outside these protocol theorems. No local raw-PDF digest or byte identity with the later archive
revision is asserted.

## Source Access

- [Bibliography entry](../../../blueprint/src/references.bib), key `Hab22`.
- [Source metadata](../sources/Hab22/metadata.yml).
- [ePrint landing page](https://eprint.iacr.org/2022/1530).
