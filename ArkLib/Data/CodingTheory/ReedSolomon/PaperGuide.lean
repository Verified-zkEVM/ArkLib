/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.Basic.Distance
public import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.ExactLists
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.FixedRateExplicitGate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.MathematicalUniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Uniform
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.PairwiseJohnson
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.FixedRateExplicitGate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.MathematicalUniformRate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Branchwise
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveProfile
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.SharpCurve
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.UniformLineMca
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode

/-!
# Reader guide to the quantitative Reed--Solomon results of [DKT26]

This module maps the numbered list-decoding and mutual correlated agreement (MCA) results of
[DKT26] to the Lean declarations that prove them. It contains no declarations of its own; it
imports every owner below, so `import ArkLib.Data.CodingTheory.ReedSolomon.PaperGuide` brings the
whole set into scope. Numbers refer to the November 2026 revision of ePrint 2026/2056.

Each entry names the main owner first. Where a paper statement is a corollary of a more general
Lean statement, the entry says which hypotheses are specialized. Declarations are in namespace
`ReedSolomon` unless written in full.

The paper's efficient decoders (Theorem 1.3, Section 9, Appendix E) and its bounded-input list
recovery (Theorem 8.10) are proved in the paper only. The concrete ProveKit, ZisK, and LambdaVM
parameter certificates live outside the library import graph, in
`ArkLibExamples.ReedSolomon.PaperGuide`.

## Conventions

Messages are polynomials of degree strictly below `k`, including zero. An exact list theorem
identifies the complete finite set of polynomials with at least `A` agreements
(`closePolynomialSet`); its `Set.Finite` conclusion is substantive over an infinite field. An MCA
theorem chooses one exceptional challenge set after the received words and before both the
challenge `z` and the candidate polynomial. Outside that set, `HasExactCorrelatedPair` (lines) or
`HasExactPowerAgreement` (polynomial curves) recovers the constituent messages together with
equality of the complete agreement sets (`polynomialAgreementSet`,
`commonPolynomialAgreementSet`, and `Code.agree` on codewords). Finite-field `mcaError` theorems
divide the exceptional count by the number of challenges.

A hypothesis `(k : ℝ) + δ * n ≤ A` imposes the paper's real agreement fraction on an integer
threshold `A`; a hypothesis `k ≤ ρ * n` permits every rate at most `ρ` and does not identify `ρ`
with `k / n`.

## Field scope

All list and MCA statements below hold over an arbitrary field, finite or infinite, with distinct
evaluation points, except where an entry says otherwise. The one prime-field interface is the
packaged predicate `HasCapacityLists` and its instances `exists_rateCapacity_list`,
`uniformFirstOrder_capacity_list`, and `exists_capacity_list`, which quantify over `ZMod q` for
primes `q ≥ n`. For the arbitrary-field capacity list theorem, use
`mathematicalUniform_capacity_list_bound` together with `exists_uniformFirstOrder_list`.

## Characteristic guards

Every guard keeps the constant-code case `k = 1` free of characteristic restrictions.

* Johnson (Theorem 4.4) has no characteristic restriction.
* The first-order branchwise theorems (Theorems 1.1, 5.1, 5.2) require characteristic zero or
  larger than `max (k - 1) B`, where `B` is the derivative-degree cap of the first-order support.
  This guard depends on the parameters and must not be simplified to `k - 1`.
* The uniform first-order theorems at gap `6/25` (Theorem 5.7) and the uniform capacity list and
  line theorems (Theorems 1.2 and 8.1, and Corollary 6.3) need only characteristic zero or larger
  than `k - 1`. Their proofs handle the remaining small characteristics separately.
* Polynomial curves and powers batching (Theorem 8.5, Corollary 8.6, and the powers part of
  Theorem 8.1) keep the jet-degree guard: characteristic zero or larger than `max (k - 1) ν`,
  with `ν = capacityPowerJetBound δ`. The degree-only guard of the line theorem does not transfer
  to curves.
* The fixed-order results (Theorem 8.8) require characteristic zero or larger than the maximum
  of `k - 1`, the derivative order, and the jet cap.

## Zeroth order: the Johnson regime (Section 4)

* Theorem 4.4, list part: `closePolynomialSet_finite_and_ncard_le_pairwiseJohnson`, the exact
  integral pairwise bound `n (A - D) / (A² - n D)` for degree at most `D`, under `D + 1 ≤ A` and
  `n D < A²`.
* Theorem 4.4, MCA part, equations (36)--(39): `exists_johnson_line_exactCorrelatedPair`, with
  exceptional count `johnsonExceptionCount n D A η`; the closed estimate is
  `HiddenDerivative.johnsonExceptionCount_lt_closed`. The finite-field corollary is
  `mcaError_affineLine_johnson_le`. The weighted-certificate refinement is
  `exists_weightedJohnson_line_exactCorrelatedPair`, with error
  `mcaError_affineLine_weightedJohnson_le`.

## First order (Sections 3 and 5, Appendix C)

* Theorems 1.1, 5.1, and 5.2, equations (40)--(41):
  `FirstOrder.firstOrderBranch_finiteLength_finiteSlack_bounds` proves both the list bound and the
  exceptional-set bound above the first-order curve (Definition 3.15), in terms of the finite
  slack `η + 1/n`. `FirstOrder.firstOrderBranch_finiteLength_rate_bounds` derives the
  `O_ρ(n/η²)` and `O_ρ(n²/η⁴)` forms, and `FirstOrder.firstOrderBranch_finiteLength_mcaError_le`
  is the finite-field error. These declarations cover both branches of the curve; they also
  admit `k = 1`, which the paper treats separately.
* Lemma 5.5, equation (44), squarefree counting:
  `FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveAgreement_sharpAt` for an
  explicit pair of thresholds, and
  `FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveAgreement_sharpOptimized`,
  which minimizes the ordinary threshold independently of the regular split.
* Lemma C.1, successive derivatives with an ordinary tail:
  `exists_exceptional_exactPowerAgreement_best` recovers exact power agreement at the minimum of
  the hybrid and squarefree envelopes, and
  `exists_exceptional_exactPowerAgreement_bestOptimized` uses the independently optimized
  envelope. `bestOptimizedCurveEnvelope_le_best` shows that the optimization never worsens the
  bound.
* Theorem 5.7, uniform bounds at gap `6/25` from `n ≥ 2`: `exists_uniformFirstOrder_list` for
  the `307 n` list bound, and `exists_uniformFirstOrder_lineMca` for the `1325775 n²` exceptional
  set. Cite these specialized theorems for the small-length claim: the packaged wrappers
  `uniformFirstOrder_capacity_list` and `capacity_lineAgreement` choose larger length thresholds
  (`23` and `4`).
* Lemma 3.3, constant codes: `uniformExactPowerAgreement_constantCode`.

## Affine families, interleaving, and folds (Section 6)

* Lemma 6.2 and Corollary 6.3: `exists_affine_exceptionalSet_full_agreement_of_exactLine` lifts a
  line statement to affine families, with densities `mcaError_affineSpace_le_of_exactAgreement`.
  At capacity, `HasCapacityLineAgreement.affineAgreement` and `exists_capacity_affineAgreement`
  give the exceptional density `C n^(d+1) / (q - 1)`; the Lean statement also covers dimension
  zero.
* Lemma 6.5 and Corollary 6.6: `uniformExactInterleavedPowerAgreement_of_scalar` turns one scalar
  theorem into a width-independent exceptional set for a row-wise interleaving, over arbitrary
  finite coordinate and row types.
* Corollary 6.7: `TensorMCA.tensorFoldBad_card_le` proves the shared-level union bound, charging
  each fold level once; `fullSetLevelWitness_interleaved_of_exactAgreement` supplies its
  Reed--Solomon level witness, and `interleavedRS_tensorFoldBad_card_le_heightThree` is the
  three-level `3 e q²` bound.

## Fixed derivative order and capacity (Section 8)

* Theorem 8.8, lists and line MCA from the derivative-order condition `Γ(ρ, a, d) > 1` with
  `d ≥ 500`: `exists_ratePartition_list_bound` and
  `exists_ratePartition_line_exactCorrelatedPair_parameters`, with the gate
  `HiddenDerivative.RatePartition.rateGamma`. The explicit fixed-rate order is
  `HiddenDerivative.RatePartition.fixedRatePartitionOrder`, with
  `fixedRatePartitionOrder_list_bound_selected` and
  `fixedRatePartitionOrder_line_exactCorrelatedPair`.
* Theorems 1.2 and 8.1, equation (55), small gaps `0 < δ < 6/25`:
  `mathematicalUniform_capacity_list_bound` (lists) and
  `exists_mathematicalUniformRatePartition_line_exactCorrelatedPair` (lines), with derivative
  order `uniformDerivativeOrder δ = ⌈exp (3 / (2δ))⌉₊`, multiplicity
  `uniformMathematicalMultiplicity δ = ⌈300 d² log (6d)⌉₊`, and jet cap
  `uniformMathematicalJetBound δ = ⌈m / δ²⌉₊ - 1`. The Lean length threshold
  `uniformMathematicalCapacityLength δ` is defined as a maximum with the interpolation length;
  `HiddenDerivative.RatePartition.uniformMathematicalCapacityLength_eq_ceil` shows that it equals
  the paper's `⌈4ν/δ²⌉₊` throughout this range.
* Theorem 8.1, all gaps: `exists_rateCapacity_list` (prime fields, see above),
  `capacity_lineAgreement` and its existential form `exists_capacity_lineAgreement`, the affine
  and error forms `exists_capacity_affineAgreement` and `exists_capacity_mcaError`, and powers
  batching `capacity_powerBatchingAgreement` and `exists_capacity_powerBatchingAgreement`. The
  line statements dispatch to Theorem 5.7 from gap `6/25` on.
* Theorem 8.5 and Corollary 8.6, polynomial curves and powers batching: the predicate
  `HasCapacityPowerBatchingAgreement` and `capacity_powerBatchingAgreement`, under the jet-degree
  guard above.

## Supporting formalization lemmas

Some library lemmas support these proofs without matching a numbered statement of the paper.
For example, `ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount` counts total jet degrees
over a finite field, and the degree and incidence bounds of Lemmas A.4 and A.5 are implemented
through affine Hilbert polynomials
(`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree`) rather than transcribed
literally.

## References

* [Dao, Kominers, and Thaler, *Reed--Solomon Codes Beyond Johnson: Efficient Decoding and Smaller
  Cryptographic Proofs*][DKT26]
-/
