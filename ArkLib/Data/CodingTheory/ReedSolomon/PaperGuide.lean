/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreementArbitrary
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PaperAlgorithms
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.FixedRateCombined
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.MathematicalUniformRate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Branchwise
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveEndpoints
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveProfile
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.WeightedCertificate

/-!
# Reader guide to the quantitative Reed--Solomon results

This is the reusable-library entrypoint for the main theorems accompanying [DKTZ26]. It maps the
paper's four quantitative regimes to semantic Lean declarations and records the boundary between
mathematical existence, executable reference code, and the still-unassembled fast decoder. Import
this module when reading or checking the paper-facing theorem surface.

Concrete ProveKit, ZisK, LambdaVM, and appendix parameter instantiations live outside the reusable
library graph. They are indexed separately by `ArkLibExamples.ReedSolomon.PaperGuide`; this module
does not import `ArkLibExamples`.

## Conventions and quantifier order

Messages are polynomials of degree strictly below `k`, including zero. The physical rate is `k/n`;
the reduced degree rate used in Johnson expressions is `(k-1)/n`. At first order, the exact
finite-length slack is `finiteLengthSlack eta n = eta + 1/n`.

An exact list theorem identifies the complete finite set of qualifying polynomials. An MCA theorem
chooses one exceptional challenge set after the received words but before the challenge and
candidate polynomial. Outside that set, `ReedSolomon.HasExactCorrelatedPair` or
`ReedSolomon.HasExactPowerAgreement`
recovers the constituent messages and equality of the complete agreement set. Finite-field
`mcaError` theorems are probability corollaries of these semantic statements.

## Reading a theorem against the paper

The principal declarations linked below explain their hypotheses and conclusions inline. Start
with the declaration itself: its docstring states the mathematical bound and identifies the
paper's parameters; comments inside the statement explain each group of binders and conclusions.
For the capacity facades, also read `ReedSolomon.HasCapacityLists` or
`ReedSolomon.HasSharpCapacityLineAgreement`, which expand the quantified property being proved.

For example, `k ≤ rho * n` permits any code rate at most `rho`; it does not identify `rho`
with `k/n`. A hypothesis `(threshold + eta) * n ≤ A` imposes the paper's real agreement
fraction on the integer threshold `A`. In a list conclusion, `Set.Finite` is substantive:
Lean's `Set.ncard` alone would not establish finiteness over an infinite field. In an MCA
conclusion, the exceptional set precedes both `z` and `P`, so one set works for every candidate
at every remaining challenge. The recovered polynomials may depend on those two choices.
Equality of the full agreement sets also rules out accidental agreements outside their common set.

## Zeroth order: the Johnson regime

* `ReedSolomon.closePolynomialSet_finite_and_ncard_le_johnsonPairwise` is the complete integral
  pairwise
  Johnson list bound over an arbitrary field.
* `ReedSolomon.exists_exceptional_weightedJohnsonMCA_fullAgreement` is the weighted-certificate
  MCA theorem in
  every characteristic. `ReedSolomon.exists_exceptional_weightedJohnsonMCA` is its subset-indexed
  form.
* `ReedSolomon.exists_exceptional_johnson_lineMCA_allChar` is the simpler all-characteristic line
  theorem when
  the expanded weighted certificate is unnecessary.

These declarations correspond to the paper's zeroth-order list and MCA row. The deterministic
Johnson-radius decoder cited by the paper is external to this hidden-derivative implementation.

## First derivative

Use the three declarations in
`ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Branchwise`:

* `ReedSolomon.FirstOrder.firstOrderBranch_finiteLength_finiteSlack_bounds` gives the exact
  inverse-square list
  and inverse-fourth exceptional bounds in `s = eta + 1/n`; this is the theorem matching the
  main-results table.
* `ReedSolomon.FirstOrder.firstOrderBranch_finiteLength_rate_bounds` is the derived eta-only
  corollary with
  `O_rho(n/eta^2)` and `O_rho(n^2/eta^4)` bounds.
* `ReedSolomon.FirstOrder.firstOrderBranch_finiteLength_mcaError_le` divides the exceptional count
  by the field
  size for affine-line sampling.

The characteristic premise explicitly separates constant codes from the positive-degree branch.
Do not use `ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.RateBounds`
for the headline row: that retained theorem has the older
inverse-cubic and inverse-quintic dependence.

For polynomial-curve batching,
`ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement_best`
gives an actual recovery theorem for the minimum of the hybrid and squarefree envelopes.
`ReedSolomon.exists_baseExceptional_firstOrderCurve_optimized_with_endpoints` dispatches constant
messages and
the full code before the nontrivial characteristic-sensitive branch.

## Through derivative order d

For `0 < R < a < 1` and `500 <= d`, the paper's fixed-parameter condition is represented
directly by:

* `ReedSolomon.HiddenDerivative.ratePartitionGamma R a d`, the displayed limiting source/rank ratio;
* `ReedSolomon.exists_ratePartition_list_bound`, which chooses finite parameters from the strict
  gate
  `1 < ratePartitionGamma R a d` and proves the complete `C_L*n^d` list bound; and
* `ReedSolomon.exists_ratePartition_lineMCA_parameters`, which chooses parameters under the same
  gate and proves
  the exact `C_E*n^(d+1)` line-MCA bound.

`ReedSolomon.exists_fixedRate_capacity_bounds` is a derived eventual-small-gap specialization: it
fixes a rate
and positive exponent slack, then chooses a gap cutoff and
`d = ceil(exp((fixedRateCoefficient R + epsilon)/delta))`. It is useful for asymptotic capacity
statements, but it is not the direct fixed-`R,a,d`, `Gamma > 1` theorem.

## A fixed gap from capacity

For complete lists, `ReedSolomon.exists_rateCapacity_list` is the all-rate paper facade. It uses
the certified
first-order branch when `6/25 <= delta` and the revised 300-based mathematical branch when
`delta < 6/25`. `ReedSolomon.uniform_capacity_list_bound_300` exposes the latter branch's explicit
parameters
and sharp arbitrary-field characteristic guard.

For MCA, `ReedSolomon.sharpCapacity_lineAgreement` is the paper-aligned all-gap assembly. Its
existential form
is `ReedSolomon.exists_sharpCapacity_lineAgreement`. The piecewise functions
`ReedSolomon.sharpCapacityDerivativeOrder`,
`ReedSolomon.sharpCapacityJetBound`, `ReedSolomon.sharpCapacityLengthThreshold`, and
`ReedSolomon.sharpCapacityLineConstant` expose the
order, characteristic threshold, length cutoff, and exceptional-set constant. The theorem dispatches
the characteristic-free constant-code endpoint, the first-order large-gap theorem, and the revised
300-based small-gap theorem. Its characteristic premise is exactly `k = 1`, characteristic zero, or
`max (k-1) (sharpCapacityJetBound delta) < ringChar F`.

`ReedSolomon.sharpCapacity_affineAgreement_and_mcaError` supplies the finite-field line error,
affine-space
error, and exact affine witnesses with the same constants. The standalone facades are
`ReedSolomon.sharpCapacity_affineAgreement`, `ReedSolomon.sharpCapacity_mcaError`, and their
existential wrappers.
`ReedSolomon.sharpCapacity_powerBatchingAgreement` gives the polynomial-curve batching form under
a revised
gap selector whose characteristic guard is independent of the batching degree.

The local revised small-gap owners are
`ReedSolomon.exists_mathematicalUniformRatePartition_baseCurveMCA` and
`ReedSolomon.exists_mathematicalUniformRatePartition_lineMCA`. The older
`ReedSolomon.exists_capacity_lineAgreement` family
uses the retained 1000-based route and the stronger compatibility premise `n <= ringChar F`; it is
not the literal counterpart of the paper's branch-dependent characteristic guard.

`ReedSolomon.uniformExactInterleavedPowerAgreement_of_scalar_arbitrary` transfers scalar exact
power agreement
to the arbitrary-field interleaved setting.

## Decoder algorithms

Importing this guide also imports
`ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PaperAlgorithms`, whose module documentation
maps
the paper's named algorithms to their proved Lean endpoints. The central boundary is:

* mathematical list and MCA results above are complete semantic theorems;
* the coordinate capacity decoder is a retained correctness reference with a primitive-work ledger;
* agreement recovery is exact relative to supplied finite representations and becomes an ordinary
  `ExactOutput` theorem when constructor coverage is proved;
* the square-system decoder is conditional on an explicit torus-backend coverage contract; and
* the first-order norm components do not yet form a top-level paper decoder or whole-decoder
  bit/RAM theorem.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26].
* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26].
-/

@[expose] public section
