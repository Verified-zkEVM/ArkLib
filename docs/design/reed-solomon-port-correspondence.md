# Reed–Solomon port: source correspondence

This appendix to the [port ledger](reed-solomon-port.md) records, for each ported destination
file, how its declarations correspond to the source snapshot. The notes cover:
- source paths and old declaration names;
- statements that are unchanged, generalized, or have hypotheses dropped;
- declarations that were deferred or not ported.

The notes were moved here verbatim from the files' module and declaration docstrings, so that the
library documentation describes only the present API (see
[`docs/wiki/porting-conventions.md`](../wiki/porting-conventions.md)). "The source" is ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` unless a note names another revision.

The key `DKTZ26` in these notes refers to the manuscript revision the source cited. The library
now cites its published version, [DKT26] (Cryptology ePrint Archive, Paper 2026/2056), with
ePrint numbering. The old locators map as follows: "Appendix A.3, Lemma A.5" (Regular Taylor
chart) is DKT26 Appendix A.6, Lemma A.4; "Section 3 (local interpolation)" is DKT26 Section 3.5;
equations (39)–(40) of the source revision (`eq:band-lattice-ratio`, `eq:band-geometric-rank`)
correspond to the local-rank bound (72) of DKT26 Section 6.1 and the rank estimate (131) in its
Appendix D.2.

The notes describe each file as it was merged. Later changes to a file are recorded in its pull
request and ledger row, not here.


## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Counting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Counting.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `weightedHigherJetCount` (the
source's `weightedHigherJetTuples` filtered the same coordinate box by hand; here it is
`Finset.natWeightedSimplex`), `contactThreshold`, `multiplicity_le_add_mul_contactThreshold`,
`add_mul_lt_multiplicity_of_lt_contactThreshold`, `ambientContactCount`,
`exhibitedKernelContactCount`, `exhibitedKernelResidualCount`,
`exhibitedKernelContactCount_le_ambientContactCount`, `certifiedContactRankBudget`, and
`certifiedEnlargedRankBound`. The source assumed `r < m` in both threshold lemmas and `0 < d` in
the second; neither lemma needs `r < m`, and the second holds for every `d`. The identity
`ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound` comes from the source's
`Interpolation/Local/Rank.lean`; it is pure arithmetic and so lives here. The source's
`localCoordinateBudget` and `localResidualCoordinateBudget` come from
`Interpolation/Local/Coordinates.lean`; the denominator `(m - r) ⌈/⌉ (d + 1)` is written
`contactThreshold (d + 1) m r`, and the source's real cutoff `T` with count `⌈T - |z|⌉₊` is a
natural cutoff `B` with count `B - |z|`. `localResidualCoordinateBudget_le_localCoordinateBudget`
is new.

From the source's `Interpolation/FreeOrderDimension.lean`: `weightedHigherJetCount_mono` (now
`Finset.card_le_card` of `Finset.natWeightedSimplex_mono`), and the private
`rectangleResidual_le`, `contactThreshold_cube_le_sq`, and `certifiedContactRankBudget_cube_le`,
which fixed `m = M = d³` and `r < d³`. Here they are the public
`exhibitedKernelResidualCount_le`, `contactThreshold_le_of_le_mul` (any `m ≤ d k`, any `r`, any
`d`), and `certifiedEnlargedRankBound_le_of_le_mul`; the source's `4 d⁸` bound is its case
`m = M = d³`, `k = d²`, in `Interpolation/FreeOrderDimension.lean`.

Also from the source's `Counting.lean`: `higherJetTupleSpecializationCost`,
`exactDimensionResidual`, `exactInterpolationDimensionCount`, and `card_exactDimensionIndex`. The
source's `staircaseCount` is `Nat.staircaseCount` in `ArkLib.Data.Finset.Staircase`, and its
dependent index type `ExactDimensionIndex` is the `Finset.sigma` `exactDimensionCoordinates`, so
`card_exactDimensionIndex` becomes `card_exactDimensionCoordinates`. The source's
`higherJetSpecializationCost`, the same cost on finitely supported exponents, and
`higherJetTupleSpecializationCost_equivFunOnFinite` are not ported: the dimension count only uses
the tuple form.

Deferred to the slices that use them: the shell counts and tuple equivalences with
`HigherJetExponent`, the bookkeeping type `CertifiedEnlargedRankBudgetIndex`, and
`ExactFiniteCertificate`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Dimension.lean`

* `finrank_interpolationSpace_lowerBound`: the source's form, with `N = (K - 1) H` and
  `H₀ = H₁ = H`.

Ported from `DimensionBridge.lean` and `Global/Dimension.lean` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source of `Global/Dimension.lean` adapts Kai Zhe
Zheng's `rs-ld-mca` formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` with
permission.

From `DimensionBridge.lean`: the source's `exactExponentCoordinatesEquiv` into
`ℕ × ((ℕ × ℕ) × HigherJetTuple d)`, built from `Finsupp.optionEquiv` and a split of `Fin (d + 1)`,
is `jetExponentCoordinatesEquiv` into `ℕ × ℕ × ℕ × (Fin (d - 1) → ℕ)`, written out directly like
`localExponentCoordinatesEquiv`; its `_x`, `_y₀`, `_y₁`, and `_higher` lemmas are
`jetExponentCoordinatesEquiv_apply`. The source's `sum_jet_eq_y₀_add_y₁_add_higher` is private
here and feeds the new `weight_eq_coordinates` for any weight, from which
`firstJetExponent_eq_coordinate`, `fullHigherJetWeight_eq_coordinate`,
`exactInterpolationMonomialWeight_eq_coordinates` (here
`weight_differentialWeight_eq_coordinates`), `totalJetDegree_eq_coordinates`, and
`fullHigherJetDegree_eq_coordinates` follow. The source's predicate
`ExactDimensionCoordinatesEligible` is unfolded in
`exactInterpolationEligibleExponent_iff_coordinates`. The chain of equivalences
`exactEligibleExponentCoordinateEquiv`, `exactCoordinateDimensionIndexEquiv`,
`exactInterpolationIndexEligibleEquiv`, and `exactInterpolationIndexEquivExactDimensionIndex` is
replaced by one `Finset.card_equiv` onto `exactDimensionCoordinates`, which gives
`card_exactInterpolationExponents_eq_exactInterpolationDimensionCount` (here
`card_exactInterpolationExponents`) and
`finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount`.

From `Global/Dimension.lean`: `card_globalEligibleExponents_lowerBound` and
`finrank_interpolationSpace_lowerBound`. The source split the `X` exponent as `r + (K - 1) s`
with `r < K - 1` and `s < H`, and used one side length `H` for `s`, `b₀`, and `b₁`. Here the `X`
exponent ranges over `x < N` directly and the side lengths `N`, `H₀`, `H₁` are independent; the
source's hypotheses are the case `N = (K - 1) H`, `H₀ = H₁ = H`, where
`N + (K - 1)(C + 2H) = (K - 1)(C + 3H)`. The source's index embeddings `jetZeroIndex`,
`jetOneIndex`, `higherJetIndexEmbedding`, the exponents `rectangleJetExponent` and
`globalRectangleExponent` with their evaluation lemmas, `GlobalRectangleIndex`,
`globalRectangleEmbedding`, and `card_globalRectangleIndex` are replaced by the inverse of
`jetExponentCoordinatesEquiv` on a product `Finset`. The source's
`finrank_interpolationSpace_eq_card` is `finrank_interpolationSpace_eq_card` of
`Interpolation/Space.lean`.

`card_goodHigherExponents_mul_le_finrank_exactInterpolationSpace` is the dimension step of the
source's `n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace` in
`Interpolation/FreeOrderDimension.lean`, which fixed `D = K - 1` and `m = d³` and assumed a
jet-degree budget `B` with `C + 2H ≤ B`; neither assumption is needed.

`finrank_interpolationSpace_lowerBound`: /-- The source's rectangular lower bound:

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/CurveCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveSymbolic.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`FirstOrderCurveCertificate` keeps its name, mathematical fields, and specialization contract. Its interpolant field uses the destination API's `SourceColumn.interpolant`. No declarations were omitted.

The matching `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder.lean` remains unchanged and covers first-order support, interpolation, rank, and shifted-height cases. No example was added for this data-only declaration.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveFinite.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_finite_firstOrder_curve_certificate_of_heightSlotCount` keeps its name, assumptions, and conclusion. The theorem is consolidated into the existing `FirstOrder.CurveCertificate` owner rather than a parallel module. Its proof uses the existing weighted-degree global multiplicity theorem. No public source declaration is omitted.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/FiniteCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount` keeps its name, assumptions, and conclusion. It specializes the existing finite curve-certificate constructor at curve degree one and transfers specialization soundness to affine combinations of two received words while preserving the support, coefficient-height, primitivity, and local-constraint fields. The received-line degree bound uses `natDegree_receivedLine_le` in the destination API. No declarations are omitted.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveTransfer.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_of_regular_stage_bounds_of_factors` keeps its name. The theorem combines regular-stage exceptional sets into a finite set bounded by the first-order curve envelope. It drops the unused assumptions `0 < k` and `k ≤ L`. The exponent-specialized `exists_exceptional_of_regular_stage_bounds_of_exponent` was not ported because it is a direct-ratio specialization of the factors theorem, and the ratio lower bound follows from the existing incidence estimate.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FirstOrder/FirstOrderHybridList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `FirstOrderCurveCertificate.jetDegree_one_le`, a public certificate degree bound. The two `exists_hybridDescent` certificate bridges are in `HybridAgreementCounting`; both remove the unused challenge-height parameter. The first retains the actual-degree characteristic guard, and the second uses the public derivative-cap guard.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/CurveHeightCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveHeightCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`firstOrderExponentDimensionIndex_totalJetDegree` is renamed to `firstOrderCoordinatesEquiv_totalJetDegree` and adapted to the support-coordinate equivalence. The shifted source and row slot counts, their exact counting identities, the numerical row-slot bound, the surplus predicate, weighted slot identities, and both first-order interpolant constructors keep their names. The row counts use `firstOrderOriginGradedRank`; the omitted `firstOrderGradedRank` alias is not needed. The generic constructor `CurveColumnHeight.exists_primitive_interpolant_of_shifted_height` is renamed to `ReedSolomon.HiddenDerivative.exists_primitive_interpolant_of_shifted_height` in `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ColumnHeight.lean` and generalized to per-column total-jet-degree shifts.

`firstOrderCurveShiftedRowSlotBound_eq_sumRangeFrom` and `firstOrderCurveShiftedHeightSlotCount_eq_sumRangeFrom` were not ported because each only unfolds `Finset.sumRangeFrom` at start zero and neither has a consumer. `firstOrderCurveShiftedRowSlotBound_le_of_rankBound` was not ported because it has no consumer; a needed concrete profile comparison can be proved directly from finite-sum monotonicity.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveHeightCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`firstOrderCurveShiftedRowSlotBound_le_of_rankBound` keeps its name and proves the shifted row-slot sum is bounded by any pointwise upper bound on the graded-rank profile. No declaration from this source file was omitted.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/CurveRank.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveRank.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The graded row indices, constraint matrices, source columns, target exponents, origin slice and selected matrices, rank profile, numerical bound, and translation theorem retain their source names. `localJetDegree_one` becomes `weight_localJetDegreeWeight_one_eq`, and `localJetDegree_firstOrderGradedTargetExponent` becomes `weight_localJetDegreeWeight_one_firstOrderGradedTargetExponent`; both are stated directly through the existing weight API. The finite-matrix degree bound drops its unused weight hypothesis, and its zero-entry bound drops the unused bound on received-curve degrees.

The compressed-matrix declarations are retired because `firstOrderOriginGradedBaseSelectedMatrix` provides the needed interface and they have no consumers. `firstOrderGradedRowCount` is omitted because it has no consumers. `firstOrderGradedRank` is a redundant alias of `firstOrderOriginGradedRank`. The fixed-field `firstOrderOriginGradedSliceMatrix` abbreviation is omitted in favor of `firstOrderOriginGradedSliceMatrixOver`. `firstOrderLocalSliceWeight` is omitted because it duplicates `localTWeight 1`; the private first-jet and source-slice weights use `jetFirstWeight` and `localTWeight 1`. `firstOrderLocalJetDegree` is omitted as a fixed-argument alias of `e.weight (localJetDegreeWeight 1)`, and the low-contact-index weight formula is omitted as a specialization of the target-exponent formula. `SourceColumn.firstJetExponent_exponent` follows from the coordinate membership and exponent successor lemmas; the source-column exact interpolation weight exponent follows from `SourceColumn.weight_exponent`. The basis-application lemmas are supplied directly by `MvPolynomial.coe_basisRestrictSupport_apply`. `map_localConstraintAt` is owned by `Local.ConstraintMap`, while `firstOrderColumns` and its exponent, injectivity, and eligibility lemmas are owned by `FirstOrder.HeightCounting`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Dimension.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Counting.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `firstOrder_x_lt_residual_iff` is
now `firstOrderWeight_lt_iff_lt_residual`, `card_firstOrderExponents_eq_dimensionCount` is now
`card_firstOrderExponents`, and `finrank_firstOrderSpace_eq_dimensionCount` is now
`finrank_firstOrderSpace_eq_firstOrderDimensionCount`. `card_firstOrderDimensionIndex` is now
`card_firstOrderDimensionCoordinates`, over the `Finset` `firstOrderDimensionCoordinates` in
place of the type `FirstOrderDimensionIndex`. `FirstOrderCoordinatesEligible`,
`firstOrderEligibleCoordinateEquiv`, `firstOrder_weight_add_firstJet_eq`,
`FirstOrderDimensionIndex`, `FirstOrderFlatDimensionEligible` and the four `firstOrder…Equiv`
definitions are not ported; one `Finset.card_nbij'` proof replaces them.
`exists_nonzero_firstOrder_interpolant_of_dimensionCount` moved to
`Interpolation/FirstOrder/Interpolant.lean`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/HeightCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/HeightCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Namespace: `ReedSolomon.HiddenDerivative`.

`firstOrderColumnSlotCount`, `firstOrderHeightSlotCount`, `firstOrderY₀Weight`,
`firstOrder_y₀_le_μ`, `firstOrderColumnSlotCount_add_y₀Weight`,
`firstOrderCertificateHeight`, `firstOrder_rowTotal_mul_height_lt_columnSlotCount`,
`firstOrderColumnSlotCount_eq_heightSlotCount`, and
`firstOrder_rowTotal_mul_height_lt_heightSlotCount` keep their names. The height is defined using
the generic `Finset.slotSurplusHeight` API added to `ArkLib/ToMathlib/BigOperators/LinearBudget.lean`;
the strict slot bound uses `Finset.rows_mul_slotSurplusHeight_add_one_lt_sum_tsub`.

`sum_firstOrderDimensionIndex_height` → `sum_firstOrderDimensionCoordinates_height`; its sum is
reindexed over the existing dimension-coordinate Finset.
`ReedSolomon.HiddenDerivative.SymbolicWeightedSupportInterpolation.firstOrderColumns` →
`ReedSolomon.HiddenDerivative.firstOrderColumns`; the matching `_exponent`, `_injective`, and
`_eligible` declarations keep their suffixes under the new namespace and use `SourceColumn.ofExponent`.

The dimension module receives `firstOrderCoordinatesEquiv` and its coordinate API from the source
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Counting.lean`:
`firstOrderExponentDimensionIndex_y₀` → `firstOrderCoordinatesEquiv_y₀`. The exponent constructor
and its coordinate and reconstruction theorems are public there. `card_firstOrderExponents` keeps
its statement and uses the equivalence. These facts are now owned by
`ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Dimension.lean`.

No listed unit statement was omitted. The source's dependent `FirstOrderDimensionIndex`
representation is not recreated; its coordinate statements use the dimension module's existing
finite coordinate set.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Interpolant.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Interpolation.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, together with
`exists_nonzero_firstOrder_interpolant_of_dimensionCount` from `FirstOrder/Counting.lean`. No
theorem assumes `1 < D`. `firstOrderGlobalConstraint` is now `firstOrderGlobalConstraintMap`,
and `finrank_firstOrderGlobalConstraint_le` is now `finrank_firstOrderGlobalConstraintMap_le`.
`exists_nonzero_firstOrder_interpolant_with_multiplicity` is now
`exists_nonzero_firstOrder_interpolant_X_sub_C_pow_dvd`: the interpolant is chosen before the
polynomial `P`, and each divisibility needs agreement only at its own point. The test derives
the source form. The rank bound and the interpolant use `LinearMap.finrank_range_pi_le_sum` and
`LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt` from P3 slice 10.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/ListBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/SharpListBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`firstOrder_finite_agreement_solutions_card_le_tight` → `firstOrder_finite_agreement_solutions_card_le_tight_of_exponent` adds a bound for any sufficient Taylor exponent. `firstOrder_finite_agreement_solutions_card_le_tight` → `firstOrder_finite_agreement_solutions_card_le_tight`, `firstOrder_finite_agreement_solutions_card_le_sharp` → `firstOrder_finite_agreement_solutions_card_le_sharp`, `finite_firstOrder_list_bound_of_heightSlotCount_sharp` → `finite_firstOrder_list_bound_of_heightSlotCount_sharp`, and `finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight` → `finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight` all drop `K ≤ n` and express finite-domain agreement with the equivalent `Set.ncard` condition. The source-named tight bounds retain exponent `2 * K - 3`. No declarations were omitted.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Profile.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Profile.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`LineProfile` and its count definitions and accessors are ported. Source `LineProfile.D` is renamed to `LineProfile.candidateDegree`, with unchanged mathematics. `LineProfile.Verification` omits its `degree_le` projection, and `CurveVerification` omits the matching tautological conjunct; both state `k ≤ k - 1 + 1`. `support_card_eq`, `columnY₀Weight_eq`, and symbolic certificate construction are generalized to the weaker verification predicate, deriving the degree condition internally. `CurveVerification.exists_certificate` likewise derives it internally. The declarations live under `ReedSolomon.HiddenDerivative.CurveProfile`.

The automatic recipe bridge is not ported: `automaticFirstOrderThreshold_eq_firstOrderRateThreshold`, `automaticBeta_eq_firstOrderRateBeta`, `automaticDerivativeCapRaw_eq_firstOrderRateDerivativeCap`, `automaticJetDegree_eq_firstOrderRateJetDegree`, `automaticSourceCount_eq_firstOrderRateSourceCount`, `automaticRankCount_eq_firstOrderRateRankCount`, and `automaticChallengeHeight_eq_firstOrderRateChallengeDegree` are recipe-specific names absent from the current API; generic rate declarations already live in `Parameters.FirstOrder` and `FirstOrderFiniteRateParameters`. `automaticSourceCount_le_dimensionCount` is covered by `firstOrderSourceCount_mul_le_firstOrderDimensionCount`, and `certifiedEnlargedRankBound_one_eq_automaticRankCount` by `certifiedEnlargedRankBound_one_eq_firstOrderRankCount`. `automaticFirstOrderFiniteRateParameters` and `exists_automaticFirstOrder_symbolicCertificate` require the unavailable `automaticMultiplicity_pos` and `automaticRankCount_lt_sourceCount` results. The generic finite-rate certificate remains the supported construction boundary.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveFinite.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/FiniteCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The profile reuses the current first-order curve-certificate engine to construct polynomial-curve certificates, and constructs symbolic certificates through the finite first-order certificate API.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/RateCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/RateCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`FirstOrderFiniteRateParameters.rankCount_mul_lt_dimensionCount` and `exists_firstOrderRate_symbolicCertificate` keep their names. `FirstOrderFiniteRateParameters.kernelHeight_le_challengeDegree` keeps its name and drops the unnecessary `0 < n` hypothesis. `FirstOrderSymbolicCertificate.toCurve` keeps its name and is placed in the canonical `FirstOrder.CurveCertificate` owner. The new shared theorem `differentialSpecialization_eq_zero_of_firstOrderSpace` derives specialization vanishing from first-order support and local constraints and is used by both first-order curve-certificate constructors.

`firstOrderExponents_subset_degree_two` was not ported because the destination rank theorem accepts arbitrary degree and agreement parameters directly. `firstOrder_rate_curve_matrix_rank_le` was not added because `rank_firstOrderLocalConstraintMatrix_le`, together with the existing first-order rank-count identity, covers it.

The existing `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder.lean` acceptance file checks strict dimension surplus and the kernel-height bound for concrete two-point rate parameters, constructs a rate certificate over `ZMod 5` and converts it to a curve certificate, and applies the shared specialization theorem to that certificate.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/LowRateSemantics.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `exists_firstOrder_symbolicCertificate_of_rank_and_height`, a shared rank-and-height constructor extracted from the interpolation-to-certificate proofs for the general-rate, automatic finite-length, and low-rate selectors. Selector-specific count arguments remain with those theorems. The helper is public so the selector modules can import it.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Space.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Basic.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, with the same names.
`firstOrderSpace_le_exactInterpolationSpace` holds for every higher-jet budget `W`. The embedding
`firstOrderSpace_le_exactInterpolationSpace_of_le` into an exact space with a larger degree bound
and agreement threshold is new, as are `monomial_mem_firstOrderSpace`, the `Module.Finite`
instance, `jetTotalDegree_le_of_mem_firstOrderSpace` and
`weight_differentialWeight_le_add_mul_totalJetDegree`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Symbolic.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Symbolic.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`FirstOrderSymbolicCertificate` retains its name, fields, and specialization-soundness contract. `interpolant_mem_firstOrderSpace` is generalized from fields to commutative semirings. The coefficient-height declaration is placed beside the generic source-column interpolant in `ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn` as `SourceColumn.coeff_interpolant_natDegree_le`, generalized to every derivative order and commutative semirings.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/SymbolicRank.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/SymbolicRank.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Namespace: `ReedSolomon.HiddenDerivative`.

`firstOrder_symbolic_matrix_rank_le` → `rank_firstOrderLocalConstraintMatrix_le`. The rank bound now accepts arbitrary finite point and column types instead of `Fin` indices and no longer assumes `1 < D`; it holds for every degree parameter `D`. The proof uses the local coefficient-change and matrix-entry declarations ported to their existing owner modules: `map_localConstraintAt` keeps its name in `Local/ConstraintMap`, and `matrix_entry_eq_coeff_localConstraintAt` → `localConstraintMatrix_apply_eq_localConstraintAt_coeff` in `Symbolic/ConstraintMatrix`. The supporting `map_projectLowContact` and `map_unscaledLocalSubstitution` lemmas also keep their names in `Local/ConstraintMap`; the latter moved from `Symbolic/Soundness` and was already public on main.

No source declarations were left out.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveRank.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`firstOrder_curve_matrix_rank_le` becomes `rank_firstOrderLocalConstraintMatrix_le`. The theorem is generalized from received lines to arbitrary received polynomials and from `Fin n` to arbitrary finite point and column types; its bound uses `Fintype.card ι`. This generalized result owns the rank proof, so no separate curve-matrix rank theorem is ported.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FreeOrderDimension.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FreeOrderDimension.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which adapts Kai Zhe Zheng's
`rs-ld-mca` formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` with permission;
the free-order extension was contributed by Pratyush Mishra.

* `weightedHigherJetCount_mono` is in `Interpolation/Counting.lean`, from
  `Finset.natWeightedSimplex_mono`. The private `rectangleResidual_le`,
  `contactThreshold_cube_le_sq`, and `certifiedContactRankBudget_cube_le` become the general
  `exhibitedKernelResidualCount_le`, `contactThreshold_le_of_le_mul`, and
  `certifiedEnlargedRankBound_le_of_le_mul` there.
  `certifiedEnlargedRankBound_le_four_mul_d_pow_eight` is the case `m = M = d³`, `k = d²` and no
  longer assumes `0 < d`.
* `shellExponent` is unchanged. `shellExponent_add_rankSavingExponent` assumed `0 < θ`; it needs
  only `θ ≠ -5`.
* `rankShellBound_lt_interpolationBox` assumed `0 < θ`, `0 < d`, and `0 < n`; each follows from
  the rank comparison, whose right side is `0` or negative otherwise.
* `n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace` assumed `0 < d`, a
  jet-degree budget `B` with `C + 2H ≤ B`, and took the field implicitly. The field is explicit,
  as in `Interpolation/Dimension.lean`. `B` is not needed, because the exact space has no
  jet-degree budget (`card_goodHigherExponents_mul_le_finrank_exactInterpolationSpace`), and
  `0 < d` follows from the scalar inequality, whose right side is `0` when `H ≤ d³ = 0`.
* `localRankBound_lt_interpolationSpace_of_shell_bounds` drops `0 < θ`, `0 < d`, `0 < n`, `B`, and
  `C + 2H ≤ B` for the same reasons.

Deferred: the shell estimate `Λ_d(W + d³) ≤ R #(goodHigherExponents d W C)` with
`R ≤ 2 d^((5 - θ) / (5 + θ))`, which the source also leaves as a hypothesis, and the choice of
`W` that makes it hold.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Index.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, with the pieces of
`Interpolation/Space.lean` and `HiddenDerivative/Variables.lean` it uses. The exponent-level
jet weights `firstJetExponent` and `fullHigherJetWeight` of `Space.lean` are now
`Finsupp.weight` of the pointwise weights `jetFirstWeight` and `jetHigherWeight`, following
the pattern of `PolynomialDifferential.jetDegreeWeight`; the source's `totalJetDegree` is
`PolynomialDifferential.totalJetDegree` and `exactInterpolationMonomialWeight D u` is
`Finsupp.weight (differentialWeight D) u`, so no second jet weight is introduced. The source's
`degreeOf_jet_le_floor_of_mem_exactInterpolationSpace` is stated through `jetDegree`, and a
polynomial-level `jetTotalDegree` bound is added. Deferred: the support-first rectangular space
(`GlobalEligibleExponent`, `interpolationSpace` and its coordinates), the higher-jet exponent sets
of `Space.lean`, and the comparison `interpolationSpace_le_exactInterpolationSpace`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/CertifiedRankBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Rank.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d:
`finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound` and
`finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound`, with the same hypotheses
(`0 < d` and `d < D`) and the same conclusion. The second is proved as an instance of
`finrank_range_exactLocalConstraintAt_le_sub` rather than by the source's direct factorization.

Deferred: the consumers of the bound (the free-order dimension count and rate rounding), and any
treatment of `d = 0`, where the intermediate space is still finite-dimensional but its dimension
formula and the contact threshold both change.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ConstraintKernel.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/ConstraintKernel.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `hiddenErrorFactor`, the
`rewriteUToE` evaluation lemmas, `exhibitedKernelFactor`, `rewriteUToE_exhibitedKernelFactor`,
`exhibitedKernelMultiplier`, `exhibitedKernelMultiplier_mem_ker`,
`canonicalExhibitedKernelMultiplier_mem_ker` (here
`exhibitedKernelMultiplier_mem_ker_contactThreshold`, without the source's hypothesis `r < m`),
and `exhibitedKernelMultiplier_injective` (here over a domain instead of a field). The source's
monomial computation `projectLowContact_T_pow_mul_E_pow_mul_eq_zero`, `contactKernelExponent`,
and its private contact-order monotonicity lemma are replaced by
`MvPolynomial.mul_mem_restrictWeightedOrder` and `MvPolynomial.weightedTruncation_eq_zero_iff`;
for the same reason `contactKernelExponent`, its two lemmas, and `T_pow_mul_E_pow_eq_monomial`
are not ported. Nothing else in the source file is deferred.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ConstraintMap.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/
ConstraintMap.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, whose support
arguments were adapted from Kai Zhe Zheng's `rs-ld-mca` formalization at commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. Changes:

* `filterLocalMonomials`, `coeff_filterLocalMonomials`, and `filterLocalMonomials_eq_zero_iff`
  are now the general `MvPolynomial.filterSupport` lemmas, and `truncateLocalT` and
  `projectLowContact` are instances of `MvPolynomial.weightedTruncation`.
* The private support-weight lemmas and the negated integer weights `negTWeight` and
  `negContactWeight` behind `enlargedLocalConstraintMap_truncateLocalT` are replaced by the
  natural-number weighted-order lemmas in `ArkLib.Data.MvPolynomial.WeightedOrder`; the only
  local input is `rewriteUToEImage_mem_restrictWeightedOrder`.
* `lowContactCoefficients`, `LowContactIndex`, `projectLowContact_eq_zero_iff`,
  `lowContactCoefficients_eq_zero_iff`,
  `projectLowContact_eq_zero_iff_lowContactCoefficients_eq_zero`,
  `enlargedLocalConstraintMap`, `translatedLocalTruncation`, `localConstraintAt`,
  `localConstraintCoordinatesAt`, `SatisfiesLocalConstraints`,
  `satisfiesLocalConstraints_iff_coordinates_eq_zero`,
  `localConstraintAt_eq_enlarged_comp_translated`,
  `localConstraintAt_apply_eq_enlarged_translated`, `exactLocalConstraintAt`,
  `exactCoefficientLocalConstraintAt`, and `exactCoefficientLocalConstraintAt_single` keep their
  source statements.
* `globalExactCoefficientConstraintMap` and its `_apply` lemma no longer assume `[Fintype ι]`.
* `coeff_truncateLocalT`, `coeff_projectLowContact`,
  `satisfiesLocalConstraints_iff_coeff_eq_zero`, and `exactLocalConstraintAt_eq_enlarged_comp`
  are new.

Deferred: the normalized substitution and its constraint maps, the local backward-error identity
of `Interpolation/Local/Identity.lean`, and the certified intermediate spaces that consume these
maps.

`LowContactIndex`: /-- Exponents of contact order below `m`. For `d > 0` this type is finite; for `d = 0` the
error variable has contact weight zero and the type is infinite. -/ [corrected: the claim is false
for `d > 0` and `m > 0`, since the visible jets have contact weight zero]

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Contact.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Contact.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `X_pow_dvd_localPolynomialEvaluation_of_lowContact`,
  `X_pow_dvd_shiftedJetSubstitution_of_contact` and
  `X_sub_C_pow_dvd_differentialSpecialization_of_contact` keep their statements.
* `pow_dvd_eval₂Hom_of_lowContact_coeff_zero` and its private helper
  `localContactOrder_pow_dvd_monomialSpecialization` are generalized to any weight and any
  commutative semiring as `MvPolynomial.pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder` in
  `ArkLib.Data.MvPolynomial.WeightedOrder`.
* `coeff_unscaledLocalSubstitution_eq_zero_of_satisfiesLocalConstraints` is one direction of the
  existing `satisfiesLocalConstraints_iff_coeff_eq_zero`, and
  `X_pow_dvd_taylor_differentialSpecialization_of_contact` is
  `X_pow_dvd_shiftedJetSubstitution_of_contact` rewritten by
  `taylor_differentialSpecialization`; neither is restated.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Coordinates.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Coordinates.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source's `unscaled_support_weight_le`
(integer weights `localWeight`/`sourceWeight` of a fixed shape) is
`unscaledLocalSubstitution_mem_restrictWeightAtMost`, for arbitrary weights with values in an
ordered additive commutative monoid; the source's private `support_weight_*` lemmas are replaced by
`ArkLib.Data.MvPolynomial.WeightAtMost`. The source's `unscaledLocal_error_le_t`,
`unscaledLocal_higher_weight_le`, `unscaledLocal_derivativeJetWeight_le`,
`unscaledLocal_jet_degree_le`, `unscaled_jet_degree_lt_of_support`,
`localConstraint_support_of_derivative_weight`, and `localConstraint_support_of_weight_bounds` are
the lemmas above. The source's `reachableLocalJetDegree e` is `e.weight (localJetDegreeWeight d)`,
and its `reachableLocalJetDegree_eq_coordinates` and `localContact_eq_coordinates` are
`weight_localJetDegreeWeight` and `localContactOrder_eq` in `HiddenDerivative/Variables.lean`.
The source's real cutoff `T` in the strict jet-degree bound and in `localResidualCoordinateBudget`
is replaced by a natural cutoff `B`; for real `T` take `B = ⌈T⌉₊`, since `n < T ↔ n < ⌈T⌉₊`
(the tests derive the source statement this way). The source's `LocalResidualCoordinateIndex`,
`localResidualExponent`, `LocalCoordinateBudgetIndex`, and their cardinality lemmas are replaced by
the `Finset.sigma` in `localResidualExponents`; `localCoordinateBudget` and the residual budget
are in `Interpolation/Counting.lean`. The finrank bounds are added here.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/GradedRank.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/GradedRank.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `sourceJetDegreeWeight` is P1's `jetDegreeWeight`, so `sourceJetDegreeWeight_eq_totalJetDegree`
  is the definition of `totalJetDegree`. `localJetDegreeWeight` is already in
  `ArkLib.Data.CodingTheory.HiddenDerivative.Variables`, and the source's `localJetDegree e` is
  written `e.weight (localJetDegreeWeight d)`.
* `localCorrection_isWeightedHomogeneous` is unchanged. The source's
  `unscaledLocalSubstitution_zero_Y_zero_isWeightedHomogeneous`,
  `unscaledLocalSubstitution_zero_X_isWeightedHomogeneous`,
  `unscaledLocalSubstitution_zero_monomial_isWeightedHomogeneous`,
  `unscaledLocalSubstitution_zero_sourceMonomial_isWeightedHomogeneous`,
  `localConstraintAt_zero_sourceMonomial_isWeightedHomogeneous` and
  `localConstraintAt_zero_isWeightedHomogeneous` fixed the center to zero; here the center is
  arbitrary, the generator statement is `unscaledLocalImage_isWeightedHomogeneous`, and the
  monomial and polynomial statements are `unscaledLocalSubstitution_isWeightedHomogeneous` and
  `localConstraintAt_isWeightedHomogeneous`, instances of the generic
  `MvPolynomial.IsWeightedHomogeneous.bind₁` and
  `MvPolynomial.IsWeightedHomogeneous.weightedTruncation`. The source-monomial forms are derived
  in the acceptance tests.
* `sourceJetGrade` and `localJetGrade` are unchanged; `gradedLocalConstraintAtZero` is
  `gradedLocalConstraintAt m 0`.
* `gradedImageCoordinateEquiv`, `gradedImageCoordinateMap` and
  `gradedImageCoordinateMap_eq_zero_iff` are generic linear algebra and are
  `LinearMap.rangeCoordinates` and `LinearMap.rangeCoordinates_eq_zero_iff` in
  `ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional`, over a division ring.
* `coeff_localConstraintAt_zero_sourceMonomial_eq_zero` is kept as the source-shaped instance of
  the new `coeff_localConstraintAt_eq_zero_of_weight_ne`.
* `totalJetDegree_le_of_mem_globalPointTranslation_support` is unchanged in statement and is an
  instance of `globalPointTranslation_mem_restrictWeightAtMost`.

`gradedLocalConstraintAt`: The source's `gradedLocalConstraintAtZero m t` is `gradedLocalConstraintAt m 0 t`.

`coeff_localConstraintAt_zero_sourceMonomial_eq_zero`: Source shape:

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Identity.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Identity.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `localPolynomialEvaluation` with its
three generator lemmas, `localPolynomialEvaluation_localCorrection`,
`localPolynomialEvaluation_comp_unscaled_backwardError`,
`localPolynomialEvaluation_unscaled_backwardError`, `reducedHiddenTaylorError`,
`X_pow_mul_reducedHiddenTaylorError`, `X_pow_succ_mul_reducedHiddenTaylorError`,
`localPolynomialEvaluation_comp_normalized_reducedError`, and
`localPolynomialEvaluation_normalized_reducedError`. The source's one-directional
`localPolynomialEvaluation_comp_unscaled_of_reconstruction` and
`localPolynomialEvaluation_comp_normalized_of_reconstruction` are the reverse directions of
`localPolynomialEvaluation_comp_unscaled_eq_iff` and
`localPolynomialEvaluation_comp_normalized_eq_iff`, which are in turn instances of the new
algebra-valued criteria. The source's `X_pow_dvd_hiddenTaylorError` restated
`Polynomial.X_pow_dvd_normalizedBackwardTaylorError` and is not repeated. The shifted-jet
substitution and `taylor_differentialSpecialization` are in
`ArkLib.Data.Polynomial.Differential.ShiftedJet`. Nothing is deferred.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/IntermediateSpace.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/IntermediateSpace.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d:
`LocalIntermediateEligibleExponent`, `localIntermediateSpace`,
`finrank_localIntermediateSpace`, `KernelSliceSourceEligibleExponent`, `kernelSliceSourceSpace`,
`tDegree_eq_zero_of_mem_kernelSliceSourceSpace`, `finrank_kernelSliceSourceSpace`,
`translatedLocalTruncation_mem_localIntermediateSpace`,
`truncate_exhibitedKernelMultiplier_mem_localIntermediateSpace` (here
`truncateLocalT_exhibitedKernelMultiplier_mem_localIntermediateSpace`), `boundedExhibitedKernelMap`,
`intermediateConstraintMap`, and `intermediateConstraintMap_boundedExhibitedKernelMap_eq_zero`.
The weights `localFirstJetWeight` and `localHigherJetWeight` and the coordinate equivalence
`localExponentCoordinatesEquiv` are in `HiddenDerivative/Variables.lean`. The source
defined both spaces by explicit finite exponent sets built from coordinate equivalences, and so
required `0 < d` in the definitions; here the spaces are defined by their support predicates for
every `d`, and `0 < d` is assumed only in the dimension formulas. The source's hypothesis `r < m`
on the exhibited map is dropped, since the truncation alone keeps the product in the space. The
source's private signed support-weight lemmas are replaced by
`ArkLib.Data.MvPolynomial.WeightAtMost`. The source's `translatedExactLocalTruncation` and
`exactLocalConstraintAt_eq_intermediate_comp_translated` are already in
`Interpolation/Local/Rank.lean`, stated there for an arbitrary space `S`.

Not ported: the source's `LocalIntermediateIndex`, `localIntermediateExponents`,
`localIntermediateSpaceBasis`, and the kernel-slice analogues. The dimension formulas here do not
need them, and no consumer in the source uses them.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/KernelSliceIndependence.lean`

Ported from `Interpolation/Local/KernelSliceIndependence.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d: `localTCoefficient` (here a linear map over a
commutative ring), `localTCoefficient_truncateLocalT`,
`localTCoefficient_zero_injective_on_tFree` (here `eq_zero_of_localTCoefficient_zero_eq_zero`),
`localTCoefficient_zero_localJetSum`, `localTCoefficient_zero_hiddenErrorFactor`,
`localTCoefficient_zero_hiddenErrorFactor_ne_zero`,
`localTCoefficient_exhibitedKernelFactor_mul_eq_zero_of_lt` (here
`localTCoefficient_exhibitedKernelFactor_mul_of_lt`), `ExhibitedKernelFamilySource`,
`finrank_exhibitedKernelFamilySource`, `exhibitedKernelFamilyMap`,
`exhibitedKernelFamilyKernelMap`, and their injectivity theorems. The source's
`localTCoefficient_exhibitedKernelFactor_mul_eq_zero_iff` is replaced by the exact formula
`localTCoefficient_exhibitedKernelFactor_mul_self`, and its strong induction
`truncateLocalT_sum_exhibitedKernelFactor_mul_eq_zero_iff` by
`LinearMap.injective_sum_comp_proj_of_triangular`. The source's predicate `IsLocalTFree` is
written out as a hypothesis on the support. Injectivity of the family map is proved over a domain
instead of a field and without the source's hypothesis `0 < d`; the constant coefficient of the
hidden error is nonzero for every `d`. The source's `localTCoefficient_zero`, `_add`, and `_sum`
are `map_zero`, `map_add`, and `map_sum` for the linear map.

Nothing in the source file is deferred. Only the exhibited part of the kernel is counted; no
reverse inclusion or rank equality is claimed, here or in the source.

`exhibitedKernelFamilyMap_injective`: The source assumed `0 < d` and a field.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Rank.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Rank.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source's two linear-algebra
lemmas `finrank_range_le_sub_finrank_of_injective_to_ker` and `finrank_range_comp_le_outer` are
now `LinearMap.finrank_range_le_sub_of_injective_ker` and `LinearMap.finrank_range_comp_le_left`
in `ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional`. The source's
`finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound` and
`finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound` are stated for one specific space
(`localIntermediateSpace`), one specific kernel family, and the explicit count
`certifiedEnlargedRankBound d m M W`; `finrank_range_exactLocalConstraintAt_le_sub` is their
common form for an arbitrary finite-dimensional `S` and an arbitrary injection into the kernel.

Deferred to the next slice: the intermediate space `localIntermediateSpace` and the proof that it
contains the translated truncations (`Interpolation/Local/IntermediateSpace.lean`), the exhibited
kernel family and its injectivity (`ConstraintKernel.lean`, `KernelSliceIndependence.lean`), the
dimension counts (`Counting.lean`), and
`ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound`. With those, the source theorems are
instances of `finrank_range_exactLocalConstraintAt_le_sub`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/RankBudget.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/RankBudget.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which follows equations (39)–(40) of
[DKTZ26].

* `localRank_ceilDiv_le` is unchanged and is derived from the generic
  `Nat.cast_ceilDiv_le_div_add_one`.
* `localRank_geometric_sum_le`, `localRank_weighted_geometric_sum_le`,
  `localRank_linear_geometric_sum_le`, `localRank_exp_geometric_ratio_le`,
  `localRank_exp_weighted_geometric_ratio_le` and `localRank_linear_exp_sum_le` contain no coding
  theory; they are generalized in `ArkLib.ToMathlib.Analysis.SpecificLimits.GeometricBounds`, and
  the source shape of `localRank_linear_exp_sum_le` is derived in the acceptance tests.
* `localRank_weightedHigherJetCount_le_exp` is `weightedHigherJetCount_le_exp`, with the same
  statement. The source used the scaled-lattice lemma
  `scaledExponentCount_mul_factorial_sq_le_pow`; here the upper half of
  `Finset.natWeightedSimplex_succ_sandwich` replaces it.
* `localRank_contact_exp_sum_le` is `sum_contactThreshold_mul_exp_le`, with the ceiling written as
  `contactThreshold (d + 1) m r` (definitionally `(m - r) ⌈/⌉ (d + 1)`).
* `localCoordinateBudget_le_geometric`, `localCoordinateBudget_le_kappa` and
  `localCoordinateBudget_div_volume_mul_cube_le` are unchanged.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/RemainderMap.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/RemainderMap.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `normalizeLocalExponent` and its `_apply_T`, `_apply_E`, `_apply_Y` and `_injective` lemmas are
  unchanged. The private `normalizeLocalExponent_single_*` lemmas are not needed.
* `normalizeErrorByExponent` is `MvPolynomial.mapExponents (normalizeLocalExponent d)`, so
  `normalizeError_eq_normalizeErrorByExponent` is `normalizeError_eq_mapExponents`, and the private
  `normalizeError_monomial` is public. `normalizeError_injective` is unchanged in statement and
  is an instance of `MvPolynomial.mapExponents_injective`.
* `normalizeLocalExponent_T_eq_contact` is unchanged; `weight_normalizeLocalExponent` restates it
  as the weight identity used by `MvPolynomial.weightedTruncation_mapExponents`.
* The private `filterLocalMonomials_monomial` is the generic `MvPolynomial.filterSupport_monomial`.
* `truncateLocalT_normalizeError`, `normalizedLocalConstraintAt`,
  `normalizedLocalConstraintAt_eq_normalize_localConstraintAt`,
  `normalizedLocalConstraintAt_eq_zero_iff`,
  `normalizedLocalConstraintAt_ker_eq_localConstraintAt` and
  `normalizedLocalConstraintAt_ker_eq_coordinates` are unchanged.

Deferred: `X_sub_C_pow_dvd_differentialSpecialization_of_normalizedLocalConstraint`, which needs
`X_sub_C_pow_dvd_differentialSpecialization_of_contact` from the source's
`Interpolation/Local/Contact.lean`, not yet ported.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Translation.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Translation.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `globalPointTranslation` with its
three generator lemmas, `globalPointTranslation_support_weight_le` (here the submodule form
`globalPointTranslation_mem_restrictWeightAtMost`, proved by
`MvPolynomial.bind₁_mem_restrictWeightAtMost` instead of the source's private support-weight
lemmas), `globalPointTranslation_neg_comp`,
`unscaledLocalSubstitution_zero_comp_globalPointTranslation`, and
`localConstraintAt_eq_zero_comp_globalPointTranslation` (here
`localConstraintAt_eq_zero_globalPointTranslation`). The source's statements at the zero point
are the special cases of the new composition laws `globalPointTranslation_comp`,
`unscaledLocalSubstitution_comp_globalPointTranslation`, and
`localConstraintAt_globalPointTranslation`; the normalized analogue is new. Deferred: the
source's `Matrix.rank_map_algebraMap_le`, a base-change bound on matrix rank that does not
concern translation; its only source consumer is `Interpolation/Symbolic/LocalRank.lean`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport/CurveCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Certificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `ratePartitionColumns`, `ratePartitionColumns_exponent`, `ratePartitionColumns_injective`, and `ratePartitionColumns_eligible` to `partitionSupportColumns`, `partitionSupportColumns_exponent`, `partitionSupportColumns_injective`, and `partitionSupportColumns_eligible`. Renamed `exists_ratePartition_certificate` to `exists_partitionSupport_curve_certificate` and adapted it to `PartitionSupportEligible`, `localDerivativeCoordinateBudget`, and `SymbolicReceivedCurve.Certificate`. Its challenge height retains the exact natural-number formula. The generic finite-support enumeration and its exponent, injectivity, and membership theorems are provided by `SourceColumn.enumerate`; weighted-support and first-order column families also use this API while retaining their names and statements.

The source helper bounds `monomial_local_matrix_rank_le` and `finiteConstraintMatrix_rank_le_partition` were not ported because `main` provides more general local-coordinate and supported-matrix rank theorems. The partition-support acceptance case checks the certificate from a strict dimension surplus.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport/FiniteSurplus.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Ratio.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ratePartition_dimension_gt_ratio_of_moment` corresponds to
`partitionSupport_finiteRatio_surplus`. The theorem uses the current partition-support space and
coordinate-budget APIs and omits the redundant `0 < n` hypothesis, which follows from the other
hypotheses. The floor bound supplies the moment rescaling condition, and the finite ratio cancels
the exponential coordinate-budget envelope exactly. The acceptance case at order `500`, rate and
agreement `1`, and multiplicity `6` is in the matching `ArkLibTest` aggregate. No public source
declaration is unported.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Bound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Kept `partitionSupport_finiteRatio_surplus` with its existing statement and second-moment lower-bound hypothesis. Renamed `ratePartition_dimension_gt_finiteRatio` to `partitionSupport_largeOrder_finiteRatio_surplus`. The large-order theorem applies for `d ≥ 500`, generalizes the cutoff to any natural `L` satisfying the level bound, and states the strict comparison using the finrank of the partition-support space and its local coordinate budget. Private lemmas share the floor-budget scale bound and finite-ratio geometric-envelope conversion. No source declaration is unported.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport/RateBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/PartitionSupport/RateBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ratePartition_totalJetDegree_le` is renamed `partitionSupport_totalJetDegree_le_rateJetCap`; the theorem bounds total jet degree under the ambient degree lower bound, using the renamed eligibility predicate and degree cap.

No declarations were left unported from this source file.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/PartitionSupport/RateBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `partitionSupport_totalJetDegree_le_of_ambient_lower_bound`, which bounds eligible exponents by `⌈m / δ²⌉₊ - 1` for any multiplicity from the ambient lower bound and `A ≤ n`. The rate-dependent bound reuses a private positive-denominator comparison lemma shared with the gap-dependent bound; their ceiling steps remain separate.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport/Dimension.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Area.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`RatePartitionSlot` is renamed `PartitionSupportAreaSlot` and is expressed with the destination weighted-simplex tuple and its coordinate sum. `ratePartitionSlotExponent`, `ratePartitionSlotExponent_eligible`, and `ratePartitionSlotExponent_injective` are renamed `partitionSupportAreaSlotExponent`, `partitionSupportAreaSlotExponent_eligible`, and `partitionSupportAreaSlotExponent_injective`; their mathematics is unchanged.

Not ported: `ratePartition_dimension_ge_quadratic_sum`, which is covered by the existing `partitionSupport_dimension_ge_quadratic_sum_real` together with `finrank_partitionSupportSpace_eq_card`. The source-shaped cardinal inequality is checked in the matching acceptance module. No other source declaration is omitted.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport/FloorTransfer.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Integral.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ratePartition_floor_integral` → `partition_floor_square_integral`, specialized to the whole weighted simplex. The existing `Finset.setIntegral_le_sum_natWeightedSimplex` handles the generic arbitrary-subset floor-transfer result, so no specialized arbitrary-subset version was added.

`ratePartition_dimension_ge_integral` → `partitionSupport_dimension_ge_integral_on` and `ratePartition_dimension_ge_rate_integral` → `partitionSupport_dimension_ge_rate_integral_on`. Both bounds now allow real cutoffs and subsets specified by inclusion in the weighted simplex; the dimension is expressed as `finrank`. The rate form has no separate integrability hypotheses.
## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ZeroOrder.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/OrderZero/LocalImage.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`zeroLocalExponent`, `zeroLocalExponent_reconstruct`, `zeroLocalExponents`, and
`mem_zeroLocalExponents` are renamed to `zeroOrderLocalExponent`,
`zeroOrderLocalExponent_reconstruct`, `zeroOrderLocalExponents`, and
`mem_zeroOrderLocalExponents`. The exponent set remains the triangular set characterized by
`E ≤ T < m`. `localConstraint_zero_support`, `range_localConstraint_zero_le`,
`finite_localConstraint_zero_range`, `card_zeroLocalExponents_le`,
`finrank_localConstraint_zero_le`, and `finrank_localConstraint_zero_domRestrict_le` are renamed
to their `zeroOrder` or `At_zeroOrder` names; their support statements and rank bounds are
unchanged. The support argument uses the general local-constraint and local-substitution support
results, together with the general contact-order result.

Not ported: `unscaled_zero_support` is covered by `localE_le_localT_of_mem_support` in
`Local/Coordinates.lean`, which holds at every derivative order. `localContactOrder_zero` is
covered by `localContactOrder_eq` in `Variables.lean`. `ZeroLocalIndex` and `card_zeroLocalIndex`
are not separate public declarations; the finite Sigma index and its cardinality calculation are
kept internal.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport/RateCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Adapter.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_ratePartitionFinite_certificate` to `exists_partitionSupport_curve_certificate_of_finiteRatio`; generalized it by removing `0 < n`, which follows from `0 < D`, `D ≤ rate * n`, and `0 < rate`. Renamed `exists_ratePartitionRate_certificate` to `exists_partitionSupport_curve_certificate_of_paddedRateBlockThreshold` and `exists_ratePartitionMathematical_certificate` to `exists_partitionSupport_curve_certificate_of_rateBlockThreshold`; both are mathematically unchanged and use the renamed threshold and finite-parameter APIs. No public source declarations were omitted. Acceptance cases in `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport.lean` check a concrete finite-ratio certificate and certificates from both block-length thresholds.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/MathematicalUniform.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/UniformEnvelope.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Generalized `MathematicalRatePartitionEnvelope.exists_curve_certificate` and `UniformRatePartitionEnvelope.exists_curve_certificate` to the shared `RatePartitionEnvelope.exists_curve_certificate`, covering qualifying scales with total-jet cap `⌈m / δ²⌉₊ - 1` and challenge height 150 times that cap. Once an envelope is supplied, its ambient lower bound gives the jet-degree estimate, so the source block-length premise is unnecessary. Both source certificate declarations are covered by this theorem.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/SourceMonomial.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/SourceMonomial.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `sourceMonomial`, over a
commutative semiring instead of a commutative ring. The homogeneity lemmas are new; the source
proved the jet-degree case only after the local substitution, inside
`unscaledLocalSubstitution_zero_sourceMonomial_isWeightedHomogeneous` of
`Interpolation/Local/GradedRank.lean`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Space.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Space.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d (adapted there from Kai Zhe Zheng's
`rs-ld-mca` formalization): `HigherJetExponent`, `higherJetWeight`, `higherJetDegree`,
`GoodHigherExponent`, `goodHigherExponentSet`, `goodHigherExponentSet_finite`,
`goodHigherExponents`, `mem_goodHigherExponents`, `firstJetExponent_le_totalJetDegree`,
`fullDerivativeJetWeight`, `fullHigherJetWeight_le_fullDerivativeJetWeight`,
`fullHigherJetDegree`, `GlobalEligibleExponent`, `globalEligibleExponentSet`,
`globalEligibleExponentSet_finite`, `globalEligibleExponents`, `mem_globalEligibleExponents`,
`interpolationSpace`, `mem_interpolationSpace_iff`, `monomial_mem_interpolationSpace`, and
`interpolationSpaceBasis`. `firstJetExponent`, `totalJetDegree`, `fullHigherJetWeight`, and
`exponentDegree_eq_x_add_totalJetDegree` (here `degree_eq_add_totalJetDegree`) are already in
`Interpolation/Index.lean` and `PolynomialDifferential`. As there, `fullDerivativeJetWeight` and
`fullHigherJetDegree` are `Finsupp.weight` of the pointwise weights `jetDerivativeWeight` and
`jetHigherDegreeWeight`.

From the source's `Interpolation/Index.lean`:
`GlobalEligibleExponent.toExactInterpolationEligibleExponent`,
`interpolationSpace_le_exactInterpolationSpace`, and
`finrank_interpolationSpace_le_exactInterpolationSpace`. The source fixed `K = D + 1`; here any
`K` with `D < K` is allowed. The finrank comparison is proved from the inclusion of the exponent
sets, which also gives `globalEligibleExponents_subset_exactInterpolationExponents`.

From the source's `Interpolation/Counting.lean`: `goodHigherExponents_self_eq_weighted_count`,
here `card_goodHigherExponents_of_le` for every `C ≥ W`, with the source statement at `C = W`
recovered in the tests.

The source's lower bound `finrank_interpolationSpace_lowerBound` is in
`Interpolation/Dimension.lean`. Deferred: the shell counts.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/CurveSupportCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/CurveSupportCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_certificate_of_fixed_margin`, `exists_weightedSupport_certificate_of_rate`, and `exists_prescribed_certificate` retain their source names. `exists_certificate_of_fixed_margin` is generalized from `Fin n` points to any finite point type. The rate and prescribed constructors preserve the curve statement and use the current harmonic API. `exists_prescribed_certificate` omits the unused positive message-dimension premise.

`Certificate` is already represented by `SymbolicReceivedCurve.Certificate` in `CurveCertificate.lean`; no theorem from this unit was left out.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/JohnsonCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Ordinary/JohnsonCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`JohnsonColumnIndex`, `JohnsonLocalRowIndex`, `JohnsonRowIndex`, `johnsonColumns`, `johnsonColumns_y₀`, `johnsonColumns_x`, `johnsonColumns_totalJetDegree`, `johnsonColumns_injective`, `johnsonLocalRow`, `johnsonConstraintMatrix`, `johnsonFinMatrix`, `johnsonFinRowWeight`, `card_johnsonColumnIndex`, `sum_johnsonColumns_slots`, `sum_johnsonFinRowWeight_slots`, `johnsonConstraintMatrix_kernel_iff`, `johnsonFinMatrix_kernel_iff`, `johnsonConstraintMatrix_degree_le`, `JohnsonSymbolicCertificate`, and `johnsonInterpolant_jetDegree_le` retain their names. `johnsonLocalRow_localJetDegree` is generalized to the current local jet-degree weight interface. The matrix vanishing results remove the received-polynomial degree bound, and `johnsonFinMatrix_degree_le` removes an unused row-weight premise. `exists_johnson_symbolic_certificate` removes the unused agreement-at-most-one and threshold-at-most-length assumptions.

The generic `SourceColumn.coeff_interpolant_natDegree_le` covers `coeff_johnsonInterpolant_natDegree_le`; `interpolant_mem_weightedSupportSpace` covers `interpolant_mem_johnsonWeightedSupport`; and the jet-degree bound follows from `SourceColumn.interpolant_totalJetDegree_le`, so `support_johnsonInterpolant_subset_range` is not needed. The source `TaylorHeight` import is unnecessary because its coefficient-height API is not used by the certificate proof. The weighted-support and specialization soundness declarations are in the existing `Symbolic/Soundness.lean` owner.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedJohnsonCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Ordinary/Weighted.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The declarations `WeightedJohnsonLocalRowIndex`, `WeightedJohnsonRowIndex`, `weightedJohnsonLocalRowIndexToJohnson`, `weightedJohnsonLocalRowIndexToJohnson_errorGrade`, `weightedJohnsonConstraintMatrix`, `weightedJohnsonFinMatrix`, `weightedJohnsonFinRowWeight`, `sum_weightedJohnsonFinRowWeight_slots`, `weightedJohnsonConstraintMatrix_kernel_iff`, `weightedJohnsonFinMatrix_kernel_iff`, `weightedJohnsonFinMatrix_degree_le`, `weightedJohnsonFinMatrix_eq_zero_of_grade_lt`, `exists_weighted_johnson_symbolic_certificate`, and `IsJohnsonWeightedCertificate.exists_symbolic` keep their source names. The two matrix kernel theorems no longer require the redundant received-polynomial degree bound; `weightedJohnsonFinMatrix_degree_le` no longer takes an unused row-weight premise. `exists_johnson_symbolic_certificate_of_shifted_surplus` is added in the existing Johnson certificate owner as the shared construction used by ordinary and weighted constructors. The shifted-height constructor `exists_primitive_interpolant_of_shifted_height` now requires only that matrix-kernel vectors satisfy the local constraints, and its first-order caller uses that implication. The symbolic acceptance file checks ordinary and weighted certificate construction and a truncated weighted-kernel instance with multiplicity two and cutoff `0 < 2 - 1`. No source declarations were omitted.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedSupportCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/ReceivedLine.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/ReceivedCurve.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`SymbolicReceivedInterpolation.Certificate` is covered by
`SymbolicReceivedCurve.Certificate` at `ℓ = 1` with
`w i = receivedLine (f i) (g i)`; no separate certificate type is needed.
`exists_weightedSupport_certificate_of_fixed_margin` and
`exists_weightedSupport_certificate_of_rate` construct this certificate for finite point types.
`exists_prescribed_symbolic_weightedSupport_certificate` drops the unused positive-message-
dimension premise. The source strict coefficient-degree bound
`coeff_interpolant_natDegree_lt` is covered by
`SourceColumn.coeff_interpolant_natDegree_le` at cutoff `B - 1`. The weighted-support degree
wrappers `totalJetDegree_interpolant_le_two_mul_sub_one`,
`jetTotalDegree_map_interpolant_le_two_mul_sub_one`, `totalJetDegree_interpolant_le_pred`, and
`jetTotalDegree_map_interpolant_lt` are covered by
`SourceColumn.interpolant_totalJetDegree_le` and
`SourceColumn.map_interpolant_jetTotalDegree_le`, together with
`totalJetDegree_le_pred_of_weightedSupportEligible`. The unused
`map_interpolant_mem_weightedSupportSpace` helper was not retained; its result follows from
`SourceColumn.map_interpolant` and `interpolant_mem_weightedSupportSpace`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ChallengeDegree.lean`

From the challenge-degree part of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/ReceivedLine.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The private closure lemmas of the
local correction, image and substitution are public `_mem_restrictJointDegree` lemmas.
`sourceMonomial_curve_unscaled_gradedCoeffDegreeLE` is now
`SourceColumn.unscaledLocalSubstitution_mem_restrictJointDegree_localJetDegree`;
`sourceMonomial_curve_unscaled_coeffDegreeLE` and `sourceMonomial_unscaled_coeffDegreeLE` are now
`SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le`; the `_coeff_natDegree_le_shift` form
is now `SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le_sub`; and the
`_coeff_eq_zero_of_weight_gt` form is now
`SourceColumn.coeff_unscaledLocalSubstitution_eq_zero_of_lt`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ColumnHeight.lean`

Ported from `Symbolic/ColumnHeight.lean` and the first theorem of `Symbolic/CurveColumnHeight.lean`
under `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
`exists_symbolic_received_line_interpolant_of_column_height` is now
`exists_primitive_receivedLine_interpolant_of_column_height`, and
`CurveColumnHeight.exists_primitive_interpolant_of_column_height` is now
`exists_primitive_interpolant_of_column_height`, concluding `v j ∈ degreeLT F (h + 1 - ℓ * y₀)`
in place of `natDegree ≤ h`. `CurveColumnHeight.exists_primitive_interpolant_of_shifted_height`
is not ported here.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ConstraintMatrix.lean`

From the matrix part of `Symbolic/ReceivedLine.lean` and `Symbolic/ReceivedCurve.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The line matrix `matrix` and the curve matrix
`constraintMatrix` are one `localConstraintMatrix`. `matrix_entry_eq_coeff_localConstraintAt` is
now `localConstraintMatrix_apply`, `matrix_mulVec_apply` is now
`localConstraintMatrix_mulVec_apply`, and `matrix_mulVec_eq_zero_iff` and
`constraintMatrix_kernel_iff` are now `localConstraintMatrix_mulVec_eq_zero_iff`. `activeRows`
and `supportedRows` are now `localConstraintSupportedRows`, with
`mem_activeRows_of_matrix_entry_ne_zero` strengthened to `mem_localConstraintSupportedRows_iff`.
`activeMatrix`, `finMatrix` and `finiteConstraintMatrix` are now
`supportedLocalConstraintMatrix`, with `finiteConstraintMatrix_kernel_iff` as
`supportedLocalConstraintMatrix_mulVec_eq_zero_iff` and `finMatrix_rank_le_matrix_rank` as the
equality `rank_map_supportedLocalConstraintMatrix` for any ring hom into a field.
`matrix_entry_natDegree_le_y₀` and `constraintMatrix_degree_le` are now
`natDegree_localConstraintMatrix_le`, `constraintMatrix_degree_le_grade_shift` is now
`natDegree_localConstraintMatrix_le_sub`, and
`constraintMatrix_eq_zero_of_source_grade_lt_row_grade` is now
`localConstraintMatrix_eq_zero_of_lt`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/CurveCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/CurveStages.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/RankCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`Certificate`, `Certificate.Q`, `Certificate.totalJetDegree_le`, and `Certificate.specialization_sound` retain their names; `challengeHeight_le` is represented by `challengeDegree_le`. `Certificate.nonzero` retains its name and result, derived from specialization soundness. `jetWeight_le` is replaced by `Certificate.jetTotalDegree_le`, a supporting bound for the current separant-chain API. `Certificate.exists_separant_chain` is renamed `Certificate.exists_separantChain` and generalized to the destination `SeparantChain` API. `Certificate.exists_exceptional_stage_coverage` is generalized to arbitrary finite point types and the destination separant-chain representation. The monomial-rank constructor is generalized from finite ordinals to arbitrary finite point and column types, and from the rational-function-field map to an injective ring homomorphism into any field; the rank constructor uses that monomial-rank constructor.

The interpolant total-jet-degree bounds are moved to `SourceColumn` and generalized to arbitrary finite column types; coefficient maps for the mapped bound target commutative semirings. The existing `SourceColumn.coeff_interpolant_natDegree_le` is generalized from `Fin N` to any finite column type and reused by the rank-based constructor. `SatisfiesLocalConstraints.map` is added to transport local constraints through coefficient maps. Separate `challengeHeight_le` and `jetWeight_le` aliases are not added because their bounds are available through `challengeDegree_le` and `jetTotalDegree_le`. `Matrix.kernel_height_lt_div_margin` is deferred to the RateHeight port because it has no consumer in this branch. Source support-certificate and jet-prefix imports are replaced by existing received-curve, source-column, and separant-chain APIs.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/PartitionRank.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/RatePartitionMatrix.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`mapped_curve_block_eq_local_matrix` became `localConstraintMatrix_map`, generalizing the algebra-map block identity to entrywise base change of the full matrix along any ring homomorphism. `monomial_local_matrix_rank_le` became `localConstraintCoordinates_rank_le_of_derivative_weight`, generalizing from monomial columns to arbitrary finite families of differential polynomials whose support has derivative-order weight at most `W`. The old symbolic weighted-support `Matrix.rank_prod_rows_le_sum` became a generic product-row rank bound in `ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank`. `finiteConstraintMatrix_rank_le_partition` became `rank_map_supportedLocalConstraintMatrix_le_of_derivative_weight`, using the existing supported-row matrix and `localDerivativeCoordinateBudget` to bound rank by the number of points times the local budget.

The separate `mapped_curve_block_eq_local_matrix` wrapper and `monomial_local_matrix_rank_le` theorem were not ported because the generalized theorems cover them. The `Matrix.rowBlock` helper was not ported because its row-block lambda is inlined into the generic product-row rank theorem.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ReceivedCurve.lean`

From `Symbolic/ReceivedLine.lean` and `Symbolic/ReceivedCurve.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, with the namespaces `SymbolicReceivedInterpolation`
and `SymbolicReceivedCurve` flattened into `ReedSolomon.HiddenDerivative`.
`receivedLine_natDegree_le` is now `natDegree_receivedLine_le`.
`exists_symbolic_received_line_interpolant_of_rank_le` is now
`exists_primitive_receivedLine_interpolant_of_rank_le`, and
`SymbolicReceivedCurve.exists_primitive_interpolant_of_rank_le` is now
`exists_primitive_interpolant_of_rank_le`. The rank hypothesis is on the full matrix after any
injective ring hom into a field, nonvanishing holds for every ring hom into a nontrivial semiring,
and the line theorem drops the `M *ᵥ v = 0` conjunct. `Symbolic/Soundness.lean` is not ported
here.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/Soundness.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/WeightedSupportInterpolant.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`map_interpolant_mem_weightedSupportSpace` is unchanged. It proves that coefficient specialization preserves the weighted-support bound, using the canonical source-column and weighted-support APIs. The support index uses `weightedSupportExponents` directly; no `WeightedSupportIndex` alias is retained.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/SourceColumn.lean`

From the source-column part of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/ReceivedLine.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `SourceColumn`, its exponent lemmas
and `interpolant` keep their names; `map_interpolant_ne_zero` holds for any ring hom in place of
`eval₂`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Symbolic.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`coeff_interpolant_natDegree_le` becomes `SourceColumn.coeff_interpolant_natDegree_le`, beside the generic source-column interpolant. It is generalized to every derivative order and commutative semirings, preserving coefficient height and support during source-column assembly.

The consolidated acceptance cases, including this port's coefficient-height, support-assembly, symbolic-rank, translated-kernel, rank-profile, weighted-degree, and zero-entry examples, are in `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder.lean`. The concrete `X^2` rank-bound case uses the generalized rank theorem. The per-module `SymbolicRank` test was removed. The test file adds no public ArkLib declaration.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedSupport.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/WeightedSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`SourceColumn.ofExponent` and `SourceColumn.exponent_ofExponent` keep their names and move to the existing `Symbolic/SourceColumn` owner. `noBand_kernel_height_lt` → `kernel_height_lt_twelve_mul_of_margin`; the renamed theorem describes its margin hypothesis and height bound. `localConstraintBlock_rank_le_base_actual` gives the point-block rank bound for arbitrary received polynomials, and `receivedLine_block_rank_le_base_actual` is derived as its received-line specialization. The full symbolic matrix rank bound uses `Matrix.rank_prod_rows_le_sum`.

The private `map_unscaledLocalImage` helper is subsumed by the existing `map_unscaledLocalSubstitution`. The private `localConstraintCoordinatesAt_monomial_map` helper is generalized to `map_localConstraintCoordinatesAt`, which handles every differential polynomial. `WeightedSupportIndex` is replaced by the subtype of the existing `weightedSupportExponents`; `to` appears only in overview prose and is not a declaration.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/FloorTransfer.lean`

Ports, from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `WeightedSupportParameters.floor_remaining` and `WeightedSupportParameters.floor_cubic`
  (`FloorTransfer.lean`). The hypothesis `0 ≤ g * m` of `floor_cubic` is dropped, since for
  `g * m < 0` the left side is nonpositive.
* `WeightedSupportParameters.weighted_floor_integral` (`FloorTransfer.lean`). The source's
  `weightedHigherJetTuples d W` is `Finset.natWeightedSimplex (fun i : Fin (d - 1) ↦ i.val + 1) W`
  and its `higherJetTupleDegree c` is `∑ i, c i`; the dimension `d - 1` is a free `n`. The
  pointwise hypotheses `hu` and `hW` become `T ⊆ Set.weightedSimplex _ W`, the hypothesis
  `hgm0 : 0 ≤ g * m` is dropped with that of `floor_cubic`, and the cell argument is
  `Finset.setIntegral_le_sum_natWeightedSimplex`.
* `weighted_residual_sum_le_integral` and `residual_le_on_floorCell` (`CubeTransfer.lean`). The
  integrability hypothesis `hint` is dropped: the integrand is continuous and the enlarged simplex
  is compact. The cell argument is `Finset.sum_natWeightedSimplex_le_setIntegral`.
* `coordinateWeight_sum` (`CubeTransfer.lean`) becomes `sum_fin_succ_eq_choose_two`, stated in `ℕ`
  with `n + 1` in place of `d`.

Deferred: `WeightedSupportParameters.weighted_dimension_integral`, which needs the support space
`weightedSupportSpace` and its dimension bound, not yet ported.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/MomentBounds.lean`

Ports `weightedSupport_variance_factor_gt`, `weightedSupport_third_factor_le` and
`weightedSupport_third_factor_numeric` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`MomentBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The dimension
hypotheses are weakened to what the arithmetic needs: `10000 ≤ d` becomes `150 < d`, which is sharp,
and `48000 ≤ d` becomes `1 ≤ d`. The acceptance tests derive the source statements.

The moment identities that produce these factors (`normalizedRadius` and its first three moments)
are in `ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments`, which
also combines them with these bounds in `normalizedRadius_contribution_lower`. Deferred: the
harmonic-sum bounds that supply `H`, `H₂` and `H₃`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/Moments.lean`

Ports declarations of `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`WeightedSupport/` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

* `Moments.lean`. The source's probability measure `weightedSimplexProbabilityMeasure n W` is
  the conditional measure `volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W]`, whose
  integrals are set averages (Mathlib's `setAverage_eq'`); the moments are stated as set
  averages. `normalizedRadius` is the source's definition with `weightedRadius u` written as
  `∑ i, u i` and `harmonicPowerSum n 1` as `harmonic n`; `continuous_normalizedRadius` is the
  source's. `integral_normalizedRadius`, `integral_normalizedRadius_sq` and
  `integral_normalizedRadius_cube` become `setAverage_normalizedRadius`, `_sq`, `_cube`,
  specializations of the general centered moments in
  `ArkLib.ToMathlib.Analysis.Simplex.CenteredMoments`. The budget hypothesis `0 < W` is dropped
  for the mean and weakened to `0 ≤ W` for the other two, and `t` is arbitrary (for `t = 0` both
  sides are `0`). `integrable_weighted_probability` is `MeasureTheory.IntegrableOn.integrable_cond`
  composed with `ContinuousOn.integrableOn_weightedSimplex`.
* `Cubic.lean`. `cubic_numeric` and `contribution_integral_lower` (namespace
  `WeightedSupportParameters`) become `cubic_contribution_numeric` and
  `contribution_integral_lower` here, and `positive_cube_moments` with `cubic_le_positive_cube`
  is `MeasureTheory.le_integral_max_sub_zero_pow_three`. The integrability hypotheses for `z ^ 2`
  and for the positive-part cube are dropped because they follow from those of `z` and `z ^ 3`.
* `Estimate.lean`. `normalizedRadius_contribution_lower` drops the hypothesis
  `48000 ≤ n + 1`: `150 < n + 1`, which the moment factor `weightedSupport_variance_factor_gt`
  needs, already follows from the harmonic hypotheses, and the third-moment factor needs only
  `1 ≤ n + 1`. The hypothesis `0 < t` is weakened to `0 ≤ t`.

Deferred: `weighted_dimension_probability` and `weighted_dimension_lower` of `Estimate.lean`
(they need `weightedSupportSpace`), `Margin.lean`, `RankIntegral.lean`, `NormalizedRank.lean`,
and `positive_cube_tangent`, `positive_cube_jensen`, `positive_cube_convex` of `Cubic.lean`,
which have no consumer yet.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/RankIntegral.lean`

Ports `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

* The source's `weightedHigherJetTuples d W` is `natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W`
  and its `higherJetTupleDegree c` is `∑ i, c i`, with `n` for `d - 1`, following
  `ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer`. The
  source's `harmonicPowerSum (d - 1) 1` is `harmonic n`, and `harmonicPowerSum (d - 1) 2` is
  written out as a sum.
* `weighted_residual_sum_le_volume_mul_mean_variance` and
  `weighted_residual_sum_le_volume_mul_harmonic_variance` are specializations of
  `Finset.sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le` and
  `Finset.sum_natWeightedSimplex_max_sub_add_one_le`. The hypotheses `1 ≤ d` and
  `0 < W + choose d 2` are dropped, and the variance is a set average instead of an integral
  against `weightedSimplexProbabilityMeasure`.
* `weightedSimplex_centeredRadius_sq_le_harmonic` specializes
  `MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean_sq_le`. The hypotheses `1 ≤ d` and
  `0 < W'` are dropped.
* `volume_weightedSimplex_add_choose_le_exp` specializes
  `MeasureTheory.volume_real_weightedSimplex_add_le_mul_exp`.

Deferred: the consumers `NormalizedRank.lean` and `Margin.lean`. They need the weighted local
constraint map `weightedSupportLocalConstraint`, its rank bound, the contact geometric sum
`localRank_contact_exp_sum_le`, the rounding estimates of `Parameters/RankRounding.lean` and
`Parameters/WeightedSupport/`, and the support space `weightedSupportSpace`, none of which is
ported yet.

## `ArkLib/Data/CodingTheory/HiddenDerivative/NormalizedSubstitution.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Substitution.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `normalizeError`, `normalizeError_T`,
`normalizeError_E`, `normalizeError_Y`, `normalizeError_localCorrection`,
`normalizedLocalImage`, `normalizedLocalSubstitution`, its three generator lemmas, and
`normalizedLocalSubstitution_eq_normalize_comp_unscaled`, unchanged in content. The generator
images of `normalizeError` are named (`normalizeErrorImage`), as for the other substitutions of
`ArkLib.Data.CodingTheory.HiddenDerivative.Substitution`. Deferred: the weighted-degree
preservation lemmas `normalizedLocalSubstitution_mem` and
`normalizedLocalSubstitution_mem_differentialFormula`, which belong with their local-rank
consumers.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/Basic.lean`

* `coarseListBound`: the source's list-size expression `q ^ (4 d + 6)`, as a definition only.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/Basic.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which adapts Kai Zhe Zheng's
`rs-ld-mca` formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` with permission;
the free-order extension was contributed by Pratyush Mishra. All eight definitions
(`multiplicity`, `agreementThreshold`, `ambientDimension`, `interpolationDegreeBudget`,
`interpolationWeightBudget`, `higherJetDegreeBudget`, `interpolationBoxWidth`,
`coarseListBound`) are ported unchanged, with the same formulas and constants.

`coarseListBound`: /-- The source's coarse list-size expression `q ^ (4 d + 6)` over a field of size `q`. This is
parameter data only: no theorem here or in the source proves that it bounds a list, since that
needs a root-counting theorem of Kopparty that is not formalized. -/

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/AgreementCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FirstOrder/FirstOrderList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`firstOrderListWeight`, `firstOrderTightListWeight`, `firstOrderTightListWeight_nonneg`, `firstOrderTightListWeight_two_mul_le`, and `finite_firstOrder_agreement_solutions_card_le_sharp` keep their names. `finite_firstOrder_agreement_solutions_card_le_tight_of_exponent` also keeps its name and has the unused premise `K ≤ n` removed; the sharp-count theorem likewise drops that premise. Added `boundedSolution_card_le_separantChainStageSum` to `ArkLib/Data/Polynomial/Differential/RecursiveCount.lean` as a generic composition theorem for stage-dependent regular-branch costs along an explicit separant chain, representing the source-local regular-stage estimate and recursive induction. No public source declaration was left out. The first-order acceptance example exercises the exact count, sharp count, uniform comparison, and charge nonnegativity; the differential-polynomial acceptance example checks the `Y₁` stage charge and applies the stage-sum theorem to a nonempty bounded-solution set along `challengeChain`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FirstOrder/FirstOrderList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent` now has one public proof stated with filter cardinality; its internal ncard caller converts through the agreement-cardinality equivalence. `finite_regular_agreement_solutions_card_le_identityPair` was moved beside it. The identity-pair theorem retains its degree-one identity-pair incidence bound.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/AutomaticBounds.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/AutomaticBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Ported the rate-gap, surplus-slope, multiplicity, jet-degree, height, moment, and exception constants and the bounds for automatic parameters and closed list and exception constants. Renamed `automaticHybridEnvelopeConstant` to `automaticRateEnvelopeConstant`, `automaticLambdaBoundConstant` to `automaticListBoundConstant`, and `automaticHybridT_le_inv_eta_cube` to `automaticStaircaseMoment_le_inv_eta_cube`. Renamed the hybrid-envelope inequalities to name the rate envelope, and renamed the closed list, exception, and combined bounds to name their mathematical quantities. The slack comparison theorems drop unused rate, positivity, or agreement guards as reported. A private helper proves repeated rate, ratio, jet, and staircase premises once. The unused private `automaticSourceLowerCount` helper and later challenge-height applications were not ported; existing first-order threshold, count, surplus, residual, and scaled-height results cover the needed facts.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/AutomaticBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `automaticRateIncidenceJetBounds`, a shared theorem collecting the rate-envelope, incidence-ratio, and jet-degree bounds used by both automatic-envelope proofs. No declarations from the source unit were omitted.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/AutomaticParameters.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/AutomaticParameters.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Ported the first-order automatic agreement, surplus, multiplicity, derivative cap, jet degree, source and rank counts, challenge height, and density definitions. Renamed `automaticBeta` to `automaticDerivativeRatio`; the associated derivative-ratio theorems use the new name. The first derivative-ratio positivity theorem drops unused rate and threshold guards, and the upper-bound theorems drop an unused agreement upper guard. Generalized `automatic_sourceDensity_sub_rankDensityEnvelope` by dropping unused agreement assumptions. Reused the generic counts from `RoundedCounts`. The source threshold, recipe-specific count and surplus results, and scaled-height floor result are covered by existing first-order declarations; unused recipe helpers and challenge-height applications were not exposed.

Ported from `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/AutomaticParameters.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The automatic parameter-record construction formerly local to `finite_automaticFirstOrder_hybrid_agreement_solutions_card_le` is now the shared owner-layer definition `automaticFiniteRateParameters`. The new projection identities are `automaticFiniteRateParameters_jetDegree` and `automaticFiniteRateParameters_derivativeCap`. The consumers' agreement-budget calculation is factored into `automaticAgreement_mul_le`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/DerivativeCappedCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/DerivativeCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finite_regularHighCutJets_card_le_derivativeCapped_of_exponent` is specialized from the generic `card_le_of_firstOrderHighTaylorCuts_of_agreement_capped` theorem in `ArkLib.Data.Polynomial.Differential.TaylorChartIncidence`, using the first-order stage caps. It drops the global separant and positive `j` and `k` assumptions and expresses agreement counts with `Set.ncard`. The source `degreeOf_initialJetSeparant_firstOrder_le` is covered by the existing generalized `degreeOf_initialJetSeparant_le`. The private positivity helper is unnecessary because regularity on each set member supplies the needed nonzero equation, and the private two-jet cap-membership helper is replaced by a private general capped-degree helper. No public source declaration remains unported.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/FiniteRateParameters.lean`

Ported from `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/FiniteRateParameters.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `ReedSolomon.HiddenDerivative`.

`firstOrderRateDerivativeCap`, `firstOrderRateJetDegree`, `FirstOrderFiniteRateTest`,
`firstOrderNormalizedSourceCount`, `firstOrderNormalizedRankCount`,
`firstOrderRateChallengeDegree`, `FirstOrderFiniteRateParameters` and its
`derivativeCap`, `jetDegree`, `rankCount`, `sourceCount`, `challengeDegree`, and
`sourceCount_gt_rankCount` declarations keep their names. The two existence theorems,
`exists_firstOrderFiniteRateParameters_of_tendsto` and
`exists_firstOrderFiniteRateParameters_of_rate_limits`, and the rational declarations
`firstOrderRationalSourceCount`, `FirstOrderRationalFiniteTest`, and its decidability instance
also keep their names. The certificate's count fields use the existing generic
`firstOrderRankCount` and `firstOrderSourceCount`.

The dimension bound is placed in `RoundedCounts.lean` and renamed from
`firstOrderRateSourceCount_le_dimensionCount` to
`firstOrderSourceCount_mul_le_firstOrderDimensionCount`; it is generalized to the generic count
API.

Not ported: `firstOrderRateSourceCount` and `firstOrderRateRankCount` are covered by
`firstOrderSourceCount` and `firstOrderRankCount`. The cubic rank upper bound and its rate-count
corollary are covered by the existing `firstOrderRankCubicUpperCount` and
`firstOrderRankCount_le_cubicUpperCount`. The certified enlarged-rank bound is covered by the
existing `certifiedEnlargedRankBound_one_eq_firstOrderRateRankCount`, generalized to every
higher-jet budget. The scaled kernel-height bound follows from the stronger
`scaledKernelHeight_le_floor`; the source-shaped max-one bound is derived in the acceptance test.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/HybridAgreementCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FirstOrder/FirstOrderHybridList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`HasOrderZeroTailListBound`, `hasOrderZeroTailListBound_of_nonzero`, `FirstOrderFieldDescent` and its fields, `exists_firstOrderFieldDescent`, and `FirstOrderFieldDescent.root_coverage` retain their names. The field descent tail uses `JetPrefixPresentation`. The symbolic `FirstOrderHybridDescent`, its fields, `exists_firstOrderHybridDescent`, and `FirstOrderHybridDescent.root_coverage` retain their names; the descent drops the unused coefficient-height parameter, represents its tail with `JetPrefixPresentation`, and root coverage is generalized to commutative semiring coefficients.

`FirstOrderCurveCertificate.exists_hybridDescent` retains its name and actual-degree characteristic guard. `FirstOrderCurveCertificate.exists_hybridDescent_of_derivativeCap_lt_ringChar` retains its name and uses the public derivative-cap guard; both omit the unused challenge-height parameter. `finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_tail`, `finite_firstOrder_hybrid_agreement_solutions_card_le_optimized_of_tail`, `finite_firstOrder_field_hybrid_agreement_solutions_card_le_raw`, `finite_firstOrder_field_hybrid_agreement_solutions_card_le_optimized`, `finite_firstOrder_field_hybrid_agreement_solutions_card_le`, and `finite_automaticFirstOrder_hybrid_agreement_solutions_card_le` retain their names and bounds. The optimized symbolic and field bounds share a private charge, ceiling, and closed-bound helper.

Ported from `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/HybridAgreementCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The local symbolic-certificate construction in the automatic hybrid and squarefree bounds is factored into the shared theorem `exists_automaticFirstOrder_symbolicCertificate`. Both automatic consumers use this bridge.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/HybridConstants.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/HybridConstants.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, with names that describe the
quantities. Stage sums and the staircase: `hybridTau` is now `regularTaylorExponent`, `hybridB1`
and `hybridJ1` are now `regularFiberStageSum` and `regularJointStageSum`, `hybridMoment` is now
`stageStaircaseSum`, and `hybridT` is now `stageStaircase`. `hybridMoment_cast_eq_hybridT` is now
`cast_stageStaircaseSum`, without `M ≤ μ`; `hybridMoment_eq_stage_sum` is now
`stageStaircaseSum_eq_sum_stages`; the two `…StageOne_le_hybridEnvelope` lemmas are now
`firstOrderCurveFiberStageOne_regularTaylorExponent_le` and
`firstOrderCurveJointStageOne_regularTaylorExponent_le`; `hybridB1_le_moment` and
`hybridJ1_le_moment` are now `regularFiberStageSum_le` and `regularJointStageSum_le`;
`hybridB1_add_one_le_succ` is now `regularFiberStageSum_add_one_le_succ`; `hybridT_mono` is now
`stageStaircase_mono`; and `hybridB1_cast_le_closed` and `hybridJ1_cast_le_closed` are now
`regularFiberStageSum_cast_le` and `regularJointStageSum_cast_le`.

List constants: `hybridListRaw` is now `firstOrderListCharge`, `hybridLambdaClosed` is now
`firstOrderListConstant`, `hybridListRaw_le_succ` and `hybridListRaw_mono` are now
`firstOrderListCharge_le_succ` and `firstOrderListCharge_mono`, and `hybridListRaw_le_closed` and
`hybridListRaw_le_lambdaClosed` are both `firstOrderListCharge_le_firstOrderListConstant`, which
holds for any `θ ≥ 1`. The ordinary tail `hybridOrdinaryRaw` is now `ordinaryTailCharge`, and
`hybridOrdinaryRaw_mono_to_top` is now `ordinaryTailCharge_le`, without `1 ≤ μ`.

Ratios and the balanced split: `hybridTheta` is now `agreementIncidenceRatio`,
`hybridLambdaOne` and `hybridLambdaTwo` are now `retainedCoordinateRatio` and
`fixedCoordinateRatio`, and `hybridBalancedL` is now `balancedSplit`. `hybridBalancedL_bounds`
is now `lt_balancedSplit` and `balancedSplit_le`, the latter needing only `D ≤ A`;
`hybridBalancedL_eq_add_ceil` is now `balancedSplit_eq_add_ceil`; and
`hybridBalancedL_retention` is now `retainedCoordinateRatio_balancedSplit_le` (with `D < n` in
place of `A ≤ n`), `fixedCoordinateRatio_balancedSplit_le` (with no hypotheses) and
`sub_balancedSplit_le`. `hybridTheta_one_le` is now `one_le_agreementIncidenceRatio`.
`hybridBalancedL_denominators_pos` is not ported; it follows by `omega` from the split bounds.

Exception constants: `hybridERaw` is now `firstOrderExceptionCharge`, `hybridEClosed` is now
`firstOrderExceptionConstant`, and `hybridERaw_balanced_le_closed` is now
`firstOrderExceptionCharge_balancedSplit_le`, without `1 ≤ μ`. The optimized constants
`hybridListOptimizedRaw` and `hybridListOptimizedCeil` are now `maxFirstOrderListCharge` and
`firstOrderListBound`; `hybridERawAtDegree` is now `minFirstOrderExceptionCharge`; and
`hybridEOptimizedRaw` and `hybridEOptimizedCeil` are now `maxMinFirstOrderExceptionCharge` and
`firstOrderExceptionBound`. `hybridListOptimizedRaw_le_closed` and `_le_lambdaClosed` are now
`maxFirstOrderListCharge_le_firstOrderListConstant`, the private
`hybridERawAtDegree_le_balanced` is now the public `minFirstOrderExceptionCharge_le`, and
`hybridEOptimizedRaw_le_closed` is now
`maxMinFirstOrderExceptionCharge_le_firstOrderExceptionConstant`, without `1 ≤ μ`. The aggregate
retains concrete checks of the agreement-incidence ratio and optimized exception bounds.

New, with no source counterpart: `stageStaircase_nonneg`, `firstOrderListCharge_le_max` and
`minFirstOrderExceptionCharge_le_maxMin`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/HybridConstants.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `hybridT_le_three_mul_cube` to `stageStaircase_le_three_mul_cube`. The statement is unchanged, and the theorem is owned by the staircase API.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/HybridRateEnvelope.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/HybridRateEnvelope.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `hybridTheta_le_rate_gap` is now
`agreementIncidenceRatio_le_one_div_sub`, `hybridLambdaClosed_le_rate_envelope` is now
`firstOrderListConstant_le_cubic`, and `hybridEClosed_le_rate_envelope` is now
`firstOrderExceptionConstant_le_quintic`. The two envelope theorems no longer take the
nonnegativity of the staircase as a hypothesis, since `stageStaircase_nonneg` supplies it.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/RoundedCounts.lean`

Ported from the recipe-independent part of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/AutomaticRecipe.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `automaticSourceCountAt` is now
`firstOrderSourceCount`, `automaticRankCountAt` is now `firstOrderRankCount`,
`automaticRankCubicUpperCount` is now `firstOrderRankCubicUpperCount`, and
`automaticRankCountAt_le_cubicUpperCount` is now `firstOrderRankCount_le_cubicUpperCount`.
`automaticSourceLowerCount` is a private helper. The generic cores of
`automaticRankCount_le_densityEnvelope_add_rounding`,
`automaticSourceDensity_mul_cube_le_sourceCount` and `automaticFiniteSurplusEstimate` are
`firstOrderRankCount_floor_le`, `cube_mul_sourceDensity_le_firstOrderSourceCount` and
`cube_mul_densityGap_sub_le_sourceCount_sub_rankCount`, stated at `M = ⌊β m⌋₊` for any `β` in
range and without `0 < m`. `automatic_source_residual_le_public` is now
`mul_max_rateResidual_le_max_residual`, which takes `D ≤ R n` directly; when `D = k - 1` and
`k ≤ R n`, the degree bound follows from `Nat.sub_le`.
`scaledKernelHeight_le_of_source_surplus` is now `scaledKernelHeight_le_floor`, bounding by the
floor rather than `max 1 …` and without `0 < n`.
`certifiedEnlargedRankBound_one_eq_firstOrderRateRankCount`, from `RateRounding.lean` in the same
source directory, is now `certifiedEnlargedRankBound_one_eq_firstOrderRankCount` for every `W`.
The threshold- and `β`-dependent definitions and theorems of `AutomaticRecipe.lean` are not ported
here.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/AllMRankRounding.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`firstOrderRateRankCount_floor_le_density_add_rounding_upper` → `firstOrderRankCount_floor_le_density_add_rounding_upper` and `firstOrderRateRankCount_floor_le_density_add_rounding` → `firstOrderRankCount_floor_le_density_add_rounding`. Their hypotheses and bounds are unchanged, using the already-ported rank-count name. The upper-branch theorem uses the sharper linear density with rounding loss `(2β + 3)m²`; the uniform theorem combines it with the existing cubic-envelope bound below `β = 1/2`.

Not ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/AllMSourceRounding.lean`: `firstOrderSourceDensity_mul_cube_le_rateSourceCount` is covered by `cube_mul_sourceDensity_le_firstOrderSourceCount`, generalized to any `mu` above the floor cutoff and to `m = 0`. Taking `mu = ⌈m a / R⌉₊` gives the corresponding ceiling-cap bound whenever the source theorem's numeric hypotheses hold.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/FiniteLengthSelectors.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added the generic theorem `firstOrderRankCount_le_two_mul_cube`. It has no source declaration; it replaces the selector-specific `finiteLengthRankCount_le_two_mul_cube`, since the height proof can use the generic result directly.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/StageCharges.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/StageCharges.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The `firstOrderCurve*` and
`firstOrderTaylor*` names are unchanged, except that `firstOrderCurveFiberStageOne_le_full` is now
`firstOrderCurveFiberStageOne_le_mul_totalCap`. `firstOrderCurveFiberStageOne` and
`firstOrderCurveJointStageOne` are defined through `cappedDegreeMixedVolume` and
`cappedBidegreeMixedVolume`, and their monotonicity follows from the mixed-volume lemmas.
`firstOrderCurveJointZero` drops its unused `K` argument. The `_mono_total` lemmas no longer need
`r ≤ j`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/StageComparison.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/StageComparison.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `curveStageZero` and
`curveStageOne` are now `orderZeroCurveStageCharge` and `orderOneCurveStageCharge`, and
`orderZeroCurveStageCharge` drops its unused `K` argument. `curveStageZero_nonneg` is now
`orderZeroCurveStageCharge_nonneg`, `curveStageOne_nonneg_of_factors` is now
`orderOneCurveStageCharge_nonneg`, `curveStageZero_mono_of_exponent` is now
`orderZeroCurveStageCharge_mono`, `curveStageOne_mono_total_of_factors` and
`curveStageOne_mono_derivative_of_factors` are now `orderOneCurveStageCharge_mono_total` (without
`r ≤ v`) and `orderOneCurveStageCharge_mono_derivative`, and `curveStageZero_le_one_of_factors`
is now `orderZeroCurveStageCharge_le_orderOne`, with `0 ≤ s` in place of `1 ≤ s`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/StageSum.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/StageSum.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `firstOrderCurveIncidenceRatio` as the common ratio for nested coordinate-set sizes; the joint, fiber, and direct ratio declarations are defined through it. Ported the stage charge, direct-ratio comparison, and cap identity. Renamed `SymbolicSeparantChain.Chain.sum_firstOrderCurveStageCharge_add_height_le_of_factors` to `PolynomialDifferential.SeparantChain.sum_firstOrderCurveStageCharge_add_height_le_of_factors`, and renamed the exponent-specialized sum theorem to `sum_firstOrderCurveStageCharge_add_height_le_of_directRatio`. Both sum theorems are generalized from fields to commutative semirings and drop unused `0 < k` and `k ≤ L` guards. The three role-specific ratio lower-bound wrappers were omitted because the chain proofs apply `one_le_incidenceFactor` directly with `b = 1`. The exponent cap identity was omitted as an unused specialization of the factors identity.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/Uniform.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/Uniform.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The source declarations map into the destination namespace as follows: `ReedSolomon.uniformFirstOrderGradedRankProfile` → `ReedSolomon.HiddenDerivative.uniformFirstOrderGradedRankProfile`; `ReedSolomon.firstOrderGradedRankBound_le_uniformFirstOrderProfile` → `ReedSolomon.HiddenDerivative.firstOrderGradedRankBound_le_uniformFirstOrderProfile`; `ReedSolomon.uniformFirstOrderHeightWeightSum`, `ReedSolomon.uniformFirstOrderHeightTotalDegreeSum`, `ReedSolomon.uniformFirstOrderHeightFirstJetSum`, and `ReedSolomon.uniformFirstOrderRowWeightSum` → the same names under `ReedSolomon.HiddenDerivative`; the four corresponding `_eq` theorems → the same names under `ReedSolomon.HiddenDerivative`; `ReedSolomon.uniformFirstOrder_parameters` → `ReedSolomon.HiddenDerivative.uniformFirstOrder_parameters`. `uniformFirstOrder_parameters` drops the unnecessary `2 ≤ n` and `A ≤ n` premises; `2 ≤ k` and `25 * k + 6 * n ≤ 25 * A` suffice. The fixed profile values, sum, and weighted sum are checked in acceptance examples rather than exported as library theorems because they have no production consumers.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/UniformMca.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/UniformMCA.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `uniformFirstOrderMCASplit` to `uniformFirstOrderMcaSplit`, `uniformFirstOrderMCASplit_bounds` to `uniformFirstOrderMcaSplit_bounds`, `uniformFirstOrderMCASplit_lambdaOne_le` to `uniformFirstOrderMcaSplit_retainedCoordinateRatio_le`, `uniformFirstOrderMCASplit_lambdaTwo_le` to `uniformFirstOrderMcaSplit_fixedCoordinateRatio_le`, `uniformFirstOrderMCA_D_mul_theta_le` to `uniformFirstOrderMca_degree_mul_agreementIncidenceRatio_le`, `uniformFirstOrderMCA_heightSlotCount` to `uniformFirstOrderMca_heightSlotCount`, `uniformFirstOrderMCA_hybridB1_four` and `uniformFirstOrderMCA_hybridB1_four_one` to `uniformFirstOrderMca_regularFiberStageSum_four` and `uniformFirstOrderMca_regularFiberStageSum_four_one`, `uniformFirstOrderMCA_hybridJ1_four` and `uniformFirstOrderMCA_hybridJ1_four_one` to `uniformFirstOrderMca_regularJointStageSum_four` and `uniformFirstOrderMca_regularJointStageSum_four_one`, `uniformFirstOrderMCA_hybridEOptimizedRaw_le_ceiling` to `uniformFirstOrderMca_optimizedExceptionCharge_le_ceiling`, `uniformFirstOrderMCA_hybridERaw_le` and `uniformFirstOrderMCA_hybridERaw_le_ceiling` to `uniformFirstOrderMca_exceptionCharge_le` and `uniformFirstOrderMca_exceptionCharge_le_ceiling`, `uniformFirstOrderMCA_parameters` to `uniformFirstOrderMca_parameters`, and `uniformFirstOrderMCA_theta_le` to `uniformFirstOrderMca_agreementIncidenceRatio_le`. The fixed-coordinate ratio, shifted-height certificate, parameter certificate, and agreement-incidence ratio bounds drop the unused `A ≤ n` premise. The support `(12, 4, 23)` is certified at height `276`; the split and numerical bounds use the destination stage-sum API. The legacy `firstOrderCurveFiberStageOne_le_four_mul` theorem is not ported because `firstOrderCurveFiberStageOne_regularTaylorExponent_le` is stronger and the four-factor estimate is derived locally.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FreeOrder.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FreeOrder.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which adapts Kai Zhe Zheng's
`rs-ld-mca` formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` with permission;
the free-order extension was contributed by Pratyush Mishra. Every source declaration is ported
under its source name, except as follows.

* `ambientDimension_lt_blockLength` assumed `0 < ε < 1` and `0 < θ < 1`; it needs only
  `(1 - θ) ε < 1` and `0 < n`. `le_ambientDimension_iff` assumed `0 ≤ ε` and `θ ≤ 1`; it needs
  only `0 ≤ (1 - θ) ε`.
* `interpolationDegreeBudget_pos` no longer assumes `0 < n`, which follows from `d < K`.
* `multiplicity_mul_agreementThreshold_le_budget_mul_denominator` assumed `0 < d < K`; it needs
  only `0 < K - 1`, and it is one direction of the new `interpolationDegreeBudget_le_iff`. The
  source's `le_interpolationDegreeBudget_of_mul_denominator_lt` assumed `t (K - 1) < m A`; the
  non-strict `le_interpolationDegreeBudget_of_mul_denominator_le` replaces it.
* `boxFamily_weightedBudget_lt` assumed `0 < θ < 1`; it needs only `0 ≤ θ`.
  `interpolationBoxWidth_le_multiplicity` assumed `0 < θ < 1`; it needs only `θ ≤ 16`.
  `freeGlobalDimensionSlacks` assumed `0 < θ < 1` and `0 < n`; it needs `0 ≤ θ`, and `θ < 1`
  and `0 < n` follow from `d < K` (`lt_one_of_ambientDimension_pos`,
  `blockLength_pos_of_order_lt_ambientDimension`).
* `half_interpolationBoxWidthTarget_le_cast` assumed `2 ≤ θ m / 16`; `1 ≤ θ m / 16` suffices.
* `exists_orderThreshold_for_boxWidth` gave the explicit threshold `⌈32 / θ⌉` for the bound `2`;
  here it is a corollary of `tendsto_interpolationBoxWidthTarget`, for every real bound `c`.
  `exists_freeOrderRankThreshold` and `exists_freeOrderElementaryThreshold` are corollaries of
  `eventually_freeOrderRankComparison` and `eventually_freeOrderElementary`.
* `half_rate_le_ambientDimension_sub_one_div` and `freeOrder_rank_comparison` assumed
  `2 ≤ d < K`; they need only `3 ≤ K`, and the second needs `0 ≤ θ` instead of `0 < θ`.

`exists_orderThreshold_for_boxWidth`: The source stated this
for `c = 2`, with the explicit threshold `⌈32 / θ⌉`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/FixedRateGate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/FixedRateGate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`fixedRatePartitionMultiplicity`, `fixedRatePartitionMultiplicity_spec`, and `fixedRatePartitionFiniteParameters` retain their names. `exists_fixedRatePartitionFiniteParameters` is not ported: its `Nonempty` conclusion is `⟨fixedRatePartitionFiniteParameters hrate hgap⟩`. The selector uses the main branch's `rateMultiplicity` and `rateMultiplicity_spec` to package positive finite weight budget and ratio greater than one in `PartitionFiniteParameters`.

A separate `leastPartitionFiniteMultiplicity` family is not ported because `rateMultiplicity`, `rateMultiplicity_spec`, and `rateMultiplicity_minimal` already provide the generic selector API.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/Gate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/Gate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ratePartitionExponent_eq` is renamed `fixedRateCoefficient_eq`. `ratePartitionGamma_gt_one_of_log_bound` and `ratePartitionGamma_gt_one_of_exponent_margin` are renamed `rateGamma_gt_one_of_log_bound` and `rateGamma_gt_one_of_exponent_margin`; their mathematics is unchanged.

Not ported: `log_ratePartitionGamma` is covered by the existing, more general `log_rateGamma`; `ratePartitionExponent` and `ratePartitionExponent_pos` are covered by `fixedRateCoefficient` and the existing, more general `fixedRateCoefficient_pos`; `ratePartition_fixedRate_eventually` is covered by `exists_small_gap_rate_gate`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Gate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ratePartitionGamma_factorization` is now `rateGamma_factorization`. The factor-six bounds `ratePartitionGamma_ge_one_add_inv_of_factor_six` and `ratePartitionGamma_gt_one_of_factor_six` are now `rateGamma_ge_one_add_inv_of_factor_six` and `rateGamma_gt_one_of_factor_six`. The factorization allows any real rate while retaining positive agreement and derivative-order hypotheses. The fixed-rate declarations retain their names: `fixedRatePartitionOrder`, `fixedRatePartitionOrder_ge_500`, `fixedRatePartition_cutoff_eq`, and `fixedRatePartitionGamma_gt_one` is now `fixedRateGamma_gt_one`. `rateGamma_eq_exponential` is a new public identity, with no direct source declaration.

`ratePartitionGamma_eq_rateGamma` is not ported because `rateGamma` is the destination's canonical limiting ratio. The weight-budget and finite-ratio bridge equalities are also unnecessary because the destination directly uses `partitionWeightBudget` and `partitionFiniteRatio`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/MathematicalUniform.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/MathematicalUniform.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `uniformRatePartitionMathematicalMultiplicity`, `uniformRatePartitionMathematicalJetBound`, `uniformRatePartitionMathematicalLength`, `uniformRatePartitionMathematicalLength_eq_ceil`, `uniformRatePartitionOrder_ge_519`, `uniformRatePartitionOrder_le_mathematicalJetBound`, `uniformRatePartitionMathematical_integer_guards`, `uniformRatePartitionMathematical_totalJetDegree_le`, `uniformRatePartitionMathematical_low_ratio_gt`, and `uniformRatePartitionMathematical_high_ratio_gt` to their `uniformMathematical...` or `uniformDerivativeOrder...` destination names. `uniformDerivativeOrder_ge_519` is stated in `UniformGamma.lean`, where it replaces the weaker order bound. `exists_mathematicalRatePartitionEnvelope` keeps its name and specializes the shared `RatePartitionEnvelope` at `uniformMathematicalMultiplicity δ`. The total-jet bound uses the equivalent `PartitionSupportEligible` predicate, and the scale-300 ratio proofs share one finite-ratio argument and reuse the generalized gamma bounds.

`uniformCapacityLengthThreshold300` is deferred because this unit has no consumer; its first consumers are in the ListDecodability and MutualCorrelatedAgreement mathematical-uniform capacity units. `ratePartitionMathematicalMultiplicity_ge_order` is covered by the stronger generic `add_two_le_closedMultiplicity`, which needs only scale at least 3 and order at least 1.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/MathematicalUniform.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`uniformMathematical_totalJetDegree_le` now uses `partitionSupport_totalJetDegree_le_of_ambient_lower_bound`; its statement and name are unchanged. The acceptance cases in `ArkLibTest/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition.lean` check the mathematical-uniform parameter examples.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/Moment.lean`

Ported from the moment part of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/Moment.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, stated over the weighted simplex with
weights `i + 1`. `simplexMaximumExpectation_affine_sq` is now
`setAverage_weightedSimplex_succ_sub_mul_sum_sq`, for general `a`, `b` and `W > 0`;
`weightedSimplexMoment_gt` is now `setAverage_weightedSimplex_succ_lowerTail_sq_gt`; and the
Reed–Solomon half of `simplexMaximumExpectation_upperTail_sq_le` is
`setAverage_weightedSimplex_succ_upperTail_sq_le`, for every `d`. `log_six_gt`,
`log_five_hundred_lt`, `affineMoment_strict_lower`, `simplexMaximum_lowerTail_sq_gt` and the
`paperMomentError*` lemmas are private; `simplexMaximumExpectation_lowerTail_eq` is folded into the
lower-tail proof; the unused `momentErrorPolynomial`/`momentErrorRatio` variant is not ported.
## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/BlockLength.lean`

Ported from `BlockLength.lean` and the definitions of `Parameters.lean` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

From `Parameters.lean`: `ratePartitionJetBound` is now
`rateJetCap`, `ratePartitionMathematicalLength` is now `rateBlockThreshold`,
`ratePartitionLength` is now `paddedRateBlockThreshold`, and `ratePartitionHeight` is now
`marginHeight`. `ratePartition_mathematical_length_guards` is now `rateBlockThreshold_guards`,
without the source's `0 < d`; `ratePartition_length_guards` is now
`paddedRateBlockThreshold_guards`, which proves `2m < n` where the source proved `2m ≤ n`.
`ratePartitionHeight_uniform`, the case `k = 150`, is now `marginHeight_one_add_inv` for every
positive `k`.

From `BlockLength.lean`: `rateJetCap` and `rateJetCap_pos` keep their names. The source's
`rateBlockThreshold` is the padded threshold, so it is now `paddedRateBlockThreshold`, not main's
`rateBlockThreshold`. `rateBlockThreshold_guards` and `rateBlockThreshold_ambient` are now
`paddedRateBlockThreshold_guards`, which states the derived guards instead of the source's real
inequalities. `rateHeight` is not a definition: it is
`marginHeight (rateJetCap rate multiplicity) (partitionFiniteRatio rate agreement order multiplicity)`.
`partitionSupport_totalJetDegree_le_rateJetCap` keeps its name in
`HiddenDerivative/Interpolation/PartitionSupport/RateBound.lean`. `rate_ceil_agreement_bounds` is
not ported; it combines the guards with `Nat.le_ceil` and `Nat.ceil_le`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/ClosedMultiplicity.lean`

Merges `RoundingLoss.lean`, `ClosedRatio.lean` and `Rounding300.lean` from the same source
directory. `closedMultiplicity C d` covers `ratePartitionClosedMultiplicity` (`C = 1000`) and
`ratePartitionMathematicalMultiplicity` (`C = 300`). `ratePartition_closed_floor_bounds` and
`ratePartition_mathematical_floor_bounds` are now `partitionWeightBudget_closedMultiplicity_pos`
and `partitionInverseRadius_closedMultiplicity_le`; `ratePartition_closed_ratio_gt` and
`ratePartition_mathematical_ratio_gt` are now `partitionFiniteRatio_closedMultiplicity_gt` with
`closedMultiplicityLoss_thousand_lt` or `closedMultiplicityLoss_three_hundred_lt`; the scalar
lemmas `ratePartition_rounding_loss_lt`, `ratePartition_rounding_loss_lt_300` and
`mathematical_rounding_numeric` are now `partitionRoundingLoss_closedMultiplicity_le` with the two
numeric lemmas. `ratePartitionClosedMultiplicity_ge_order`, which assumed `500 ≤ d`, is now
`add_two_le_closedMultiplicity` for `3 ≤ C` and `1 ≤ d`. Where the source used
`ratePartitionGamma`, the limit is written out as `(27/20) R (d + 1) exp(-(R/a) log(6d))`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/FiniteRatio.lean`

Merges `FiniteRatio.lean`, `Convergence.lean` and `FiniteParameters.lean` from the same source
directory, with the matching definitions of `Parameters.lean`. In `FiniteRatio.lean`,
`partitionWeightBudget` keeps its name, `partitionLambda` is now `partitionInverseRadius`,
`finiteGamma` is now `partitionFiniteRatio`, `rateGamma_eq_exp` is now `rateGamma_eq_exponential`
in `Gate.lean`, `tendsto_partitionLambda` and `tendsto_finiteGamma` are now
`tendsto_partitionInverseRadius` and `tendsto_partitionFiniteRatio`, and
`exists_finiteGamma_gt_one` is now `exists_partitionFiniteRatio_gt` for any bound. In
`Parameters.lean`, `ratePartitionWeight` is now `partitionWeightBudget` and
`ratePartitionFiniteRatio` is now `partitionFiniteRatio`. `ratePartitionFiniteRatio_eq` is now
`partitionFiniteRatio_eq_weightBudget`, `tendsto_ratePartitionFiniteRatio` and the Convergence
lemmas are now `tendsto_partitionWeightBudget_div`, `tendsto_partitionInverseRadius` and
`tendsto_partitionFiniteRatio`, and
`exists_positive_weight_multiplicity_of_ratePartitionGamma_gt` and
`exists_multiplicity_of_ratePartitionGamma_gt` are now `exists_partitionFiniteRatio_gt`.
`RatePartitionFiniteParameters` is now `PartitionFiniteParameters`, and
`exists_ratePartitionFiniteParameters` is now `PartitionFiniteParameters.nonempty`.
`partitionWeightBudget_level_le` is not ported.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/Recipe.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/Recipe.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_partitionFiniteParameters_of_rateGamma_gt_one` is new and bridges the strict limiting gate to the existing finite-ratio existence theorem. `rateMultiplicity`, `rateMultiplicity_spec`, and `rateMultiplicity_minimal` keep their names and choose and characterize the least multiplicity with positive weight budget and finite ratio above one, using `partitionFiniteRatio` in place of `finiteGamma`.

No declarations were left unported from this source file.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/UniformEnvelope.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/UniformEnvelope.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.HiddenDerivative.UniformRatePartitionEnvelope` → `ReedSolomon.HiddenDerivative.RatePartition.UniformRatePartitionEnvelope` and `ReedSolomon.HiddenDerivative.exists_uniformRatePartitionEnvelope` → `ReedSolomon.HiddenDerivative.RatePartition.exists_uniformRatePartitionEnvelope`; names are unchanged, and both declarations are placed in the `RatePartition` namespace. The gap determines the derivative order, multiplicity, and block threshold, while the ambient degree and scalar parameters may depend on the actual message dimension. The existence theorem supplies parameters for that dimension and the actual agreement count. The consolidated acceptance module adds a concrete envelope existence example at `δ = 1/5`, with `n = 50m`, `k = 2m`, and `A = 12m`, where `m = uniformMultiplicity (1/5)`.

No declarations from the designated source file were left unported. The generalized Gamma bounds and their uniform-order specializations are supplied by `main`'s `UniformGamma` module. The proof uses the existing `rateGamma_eq_exponential` identity; the redundant branch-local `rateGamma_eq_exp` alias was removed.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/UniformEnvelope.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `UniformRatePartitionEnvelope` to `RatePartitionEnvelope` and generalized the record with an explicit interpolation multiplicity parameter. Added `exists_ratePartitionEnvelope` for the common branch construction. `exists_uniformRatePartitionEnvelope` keeps its name and now specializes that theorem at the executable `uniformMultiplicity δ`.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/UniformGamma.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/UniformGamma.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`uniformRatePartitionOrder_ge_500` is covered by the stronger `uniformDerivativeOrder_ge_519`, which has the same hypotheses and lives in this file. The four uniform-order theorems `uniformRatePartitionGamma_low_base_gt`, `uniformRatePartitionGamma_low_gt`, `uniformRatePartitionGamma_high_base_gt`, and `uniformRatePartitionGamma_high_gt` are now `uniformRateGamma_low_base_gt`, `uniformRateGamma_low_gt`, `uniformRateGamma_high_base_gt`, and `uniformRateGamma_high_gt`. The corresponding arbitrary-order bounds are generalized to positive orders satisfying the logarithmic lower bound and are named `rateGamma_low_base_gt`, `rateGamma_low_gt`, `rateGamma_high_base_gt`, and `rateGamma_high_gt`. The bounds cover low- and high-rate margins, with and without the finite-multiplicity factor.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/UniformGamma.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added the public numerical bound `log_forty_ninths_lt_d9`, used to prove the scale-300 finite-ratio margin.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/UniformParameters.lean`

Ported from `UniformParameters.lean` of the same source directory. `uniformRatePartitionOrder`,
`uniformRatePartitionMultiplicity`, `uniformRatePartitionLength` and
`uniformRatePartitionJetBound` are now `uniformDerivativeOrder`, `uniformMultiplicity`,
`uniformBlockThreshold` and `uniformJetCap`. `uniformRatePartition_integer_guards` is now
`uniformBlockThreshold_guards`, without `0 < m` and with `δ ≤ 1` in place of `δ < 1`.
`uniformRatePartition_high_ambient_of_m_le` is now `high_rate_ambient_guards`, without
`0 < δ < 1`; `uniformRatePartition_low_ambient_of_m_le` is now `low_rate_padded_ambient_guards`,
with `δ ≤ 1/2` in place of `δ < 6/25`. The corresponding source-shaped high-rate and padded
low-rate ambient bounds follow by specializing these guards to the uniform order and multiplicity.
`uniformRatePartition_totalJetDegree_le` is deferred: it needs `RatePartitionEligible` (#977).

## `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/WeightedSupport/Capacity.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TaylorCutoff.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.prescribed_geometric_parameters` keeps its name. It gives the prescribed order, multiplicity, Taylor cutoff, ambient dimension, and agreement bounds, dropping the unused `0 < k` assumption and using the current harmonic and agreement-threshold APIs.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Substitution.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Substitution.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `localJetSum`, `localCorrection`,
`T_mul_localJetSum`, `translateToU`, `rewriteUToE`, `unscaledLocalImage`,
`unscaledLocalSubstitution`, its three generator lemmas, and
`unscaledLocalSubstitution_eq_rewrite_comp_translate`. The generator images of `translateToU`
and `rewriteUToE` are now named (`translateToUImage`, `rewriteUToEImage`), so that weight bounds
can be stated for them. Deferred: the normalized substitution (`normalizeError`,
`normalizedLocalSubstitution`) and the weighted-degree preservation lemmas
(`unscaledLocalSubstitution_mem` and the `differentialFormula` variants), which belong with the
local-rank consumers.

## `ArkLib/Data/CodingTheory/HiddenDerivative/Variables.lean`

The definitions are ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/
Variables.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `LocalVariable`,
`LocalPolynomial`, `localT`, `localAux`, `localU`, `localE`, `localY`, `localContactWeight`,
`localContactOrder`, `localTWeight`, `localHigherJetWeight`, and `localDerivativeJetWeight`, with
their evaluation lemmas. The global weight `jetHigherWeight` of the source is in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index`. The source's substitution caps
`localSubstitutionSourceWeight` are not ported: the weight bounds they served are proved in
`Interpolation/Local/Coordinates.lean` for arbitrary weights.

From the source's `Interpolation/Local/IntermediateSpace.lean`: `localFirstJetExponent` (here the
weight `localFirstJetWeight`) and the private `localExponentCoordinatesEquiv`, made public here;
its `sum_localJet_eq_first_add_higher`, `localFirstJetExponent_eq_coordinate`, and
`localHigherJetWeight_eq_coordinate` are `weight_localFirstJetWeight` and
`weight_localHigherJetWeight`. From the source's `Interpolation/Local/Coordinates.lean`:
`reachableLocalJetDegree` (here the weight `localJetDegreeWeight`),
`reachableLocalJetDegree_eq_coordinates` (here `weight_localJetDegreeWeight`), and
`localContact_eq_coordinates` (here `localContactOrder_eq`, which needs no coordinates).

## `ArkLib/Data/CodingTheory/InterleavedCode/ExactAgreement.lean`

* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26], Corollary 4.5, for the row-functional argument.
* ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, under
  `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/`:
  - `PowerAgreement.lean`: the private predicate `powerProjectionBad` becomes
    `IsProjectionBad` for an arbitrary batching map and module code. The private
    `scalar_powerProjectionBad_card_le` becomes
    `not_isProjectionBad_of_forall_hasExactAgreement` and
    `encard_setOf_isProjectionBad_le_of_uniformExactAgreement`, with Reed–Solomon polynomials
    replaced by codewords. The private `interleaved_powerProjectionBad_card_le` (finite field)
    becomes `encard_setOf_isProjectionBad_moduleInterleavedCode_le`. The exactness half of
    `uniformExactInterleavedPowerAgreement_of_scalar` becomes
    `hasExactAgreement_of_not_isProjectionBad`, with the Reed–Solomon hypothesis `k ≤ agreement`
    replaced by `DeterminedByAgreement`. The public `interleavedCodeword_eq_of_agree_on` is
    `DeterminedByAgreement.moduleInterleavedCode` applied to
    `ReedSolomon.determinedByAgreement_code`.
  - `PowerAgreementArbitrary.lean`: `powerProjectionBadArbitrary` is the same predicate as
    `powerProjectionBad`. The private `scalar_powerProjectionBadArbitrary_mem_exceptional` is
    `not_isProjectionBad_of_forall_hasExactAgreement`; the private
    `interleaved_powerProjectionBadArbitrary_finset_card_le` is
    `exists_forall_isProjectionBad_of_interleaved`; the private
    `interleaved_powerProjectionBadArbitrary_exceptional` is the infinite-field case of
    `encard_setOf_isProjectionBad_moduleInterleavedCode_le`; and the private
    `exactInterleavedPowerAgreement_of_not_projectionBad` is
    `hasExactAgreement_of_not_isProjectionBad`.

  The source split the argument into a finite-field and an infinite-field proof, both for
  `z ↦ (1, z, …, z^ℓ)` over Reed–Solomon codes, and assumed a positive row width. Here one proof
  covers every field, every batching map, every module code, and every finite row type,
  including an empty one. The Reed–Solomon statements
  `uniformExactInterleavedPowerAgreement_of_scalar(_arbitrary)` are derived in
  `ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement`.

Deferred: the shared-level fold and tensor-tight transfer of `TensorFoldAgreement.lean`, the
anchored statements of `AnchoredAgreement.lean` and `AnchoredReconstruction.lean`, and the
field-size-weighted transfer of [Jo26] for seed spaces larger than the field when `e ≥ |F|`.

## `ArkLib/Data/CodingTheory/InterleavedCode/Projection.lean`

* ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` uses this row-functional
  argument in the private declarations `interleaved_powerProjectionBad_card_le`,
  `interleaved_powerProjectionBadArbitrary_finset_card_le`, and
  `interleaved_lineProjectionBad_card_le` under `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/`.

`exists_rowFunctional_forall_notMem`: This is the row-projection step of [Jo26] Corollary 4.5, stated without a generator or a seed
type;

`exists_rowFunctional_forall_notMem`: The finite-field avoidance theorem from #912 itself works over a division ring.

## `ArkLib/Data/CodingTheory/ListDecodability/AgreementRadius.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AnchoredAgreement.lean`: `candidateSet_finite`
and `candidateFamily_card_le` bound anchored candidates through
`ReedSolomon.relHammingDist_le_capacityRadius_iff_capacityAgreementThreshold_le` at the radius
`capacityRadius delta n k = 1 - k / n - delta`, with the agreement threshold
`k + ⌈delta * n⌉ ≤ a`. That threshold implies `1 - a / n ≤ capacityRadius delta n k`, so the
statements here, at the radius `1 - a / n` and for an arbitrary code, imply the source ones by
`Code.Lambda_mono`. The Reed–Solomon consumers are in
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement`.

## `ArkLib/Data/CodingTheory/ListDecodability/Capacity/WeightedSupport.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/WeightedSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_weightedSupport_hiddenDerivativeConstruction`, `weightedSupport_capacity_list_bound_four_mul`, and `weightedSupport_capacity_list_bound` keep their names and mathematical statements. The construction theorem specializes the existing prescribed construction result. The pointwise list bound uses the destination's order-indexed multiplicity API and gives prefactor `4m` with exponent `2d`, refined to `d` under the large-field condition. The packaged theorem provides `WeightedSupportListBound` using the existing multiplicity positivity characterization. The generic `CapacityGapCertificate.ofPointwiseBound` helper was added to the existing capacity owner file; it has no source declaration and turns pointwise finite-list bounds into exact decoder certificates over arbitrary finite coordinate types. `weightedSupportMultiplicity_pos` was not ported because `weightedSupportMultiplicity_pos_iff` together with `capacityDerivativeOrder_lower` covers it.

The acceptance cases in `ArkLibTest/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean` check the construction contract, the pointwise bound constructor, and the packaged theorem at the prescribed sample parameters. The samples put the zero polynomial in the agreement list at a threshold no greater than the block length, and the pointwise-bound case supplies a positive finite list bound.

## `ArkLib/Data/CodingTheory/ListDecodability/SymbolMap.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AgreementBounds.lean`: the proof of
`lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound` injects every finite subset of an
interleaved point list into a scalar point list over `RatFunc F`. That injection is stated here
for arbitrary alphabets, codes and injective symbol maps.

## `ArkLib/Data/CodingTheory/ProximityGenerator/BinaryTensorFoldAgreement.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `ArkLib/Data/CodingTheory/ProximityGenerator/BinaryTensorFoldAgreement.lean`: the definitions
  `fullAgreementSet`, `binaryLineFold`, `binaryEqualityGenerator`, `binaryTensorFold`,
  `familyAgreementSet`, `FullSetLevelWitness`, `HasFullTensorDecomposition`, `levelExceptional`,
  `TensorFoldFamilyGood`, `TensorFoldGood`, `tensorFoldFamilyBad`, `tensorFoldBad`, and the
  theorems `binaryTensorFold_eq_tensorGeneratorPi`, `levelExceptional_card_le`,
  `levelExceptional_good`, `hasFullTensorDecomposition_of_good`, `tensorFoldBad_card_le`,
  `tensorFoldBad_eq_empty_height_zero`, `hasFullTensorDecomposition_of_not_mem_bad`, are ported
  with the coordinate, field and alphabet types in arbitrary universes and the field weakened to
  a ring outside the transfer section. `FullSetLevelWitness` no longer requires the family type
  to be nonempty; the empty family is covered by every proof here. The private
  `HasFullTensorFamilyDecomposition`, `hasFullTensorFamilyDecomposition_of_good` and
  `tensorFoldFamilyBad_card_le` are public intermediate results here.
* `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/TensorFoldAgreement.lean`: the private
  `lineProjectionBad` is `Code.IsProjectionBad binaryEqualityGenerator`. The private
  `interleaved_lineProjectionBad_card_le` is
  `Code.encard_setOf_isProjectionBad_moduleInterleavedCode_le`. The private
  `exists_exceptional_fullSetLine_interleaved_of_exactAgreement` and the packing argument of
  `fullSetLevelWitness_interleaved_of_exactAgreement` become
  `fullSetLevelWitness_of_uniformExactAgreement` and `FullSetLevelWitness.moduleInterleavedCode`
  for an arbitrary module code, with the Reed–Solomon hypothesis `k ≤ agreement` replaced by
  `Code.DeterminedByAgreement` and the width hypothesis dropped. The private
  `scalar_lineProjectionBad_card_le` changes the line parametrization; its code-level form is
  `isProjectionBad_binaryEqualityGenerator_iff`. The Reed–Solomon statements are in
  `ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement`.

The probability form of the count (`BinaryTensorFoldProbability.lean` at the same revision) is in
`ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldProbability`.

## `ArkLib/Data/CodingTheory/ProximityGenerator/BinaryTensorFoldProbability.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ProximityGenerator/BinaryTensorFoldProbability.lean`:

* `tensorFoldBad_probability_le` is ported with the field weakened to a finite ring and the
  coordinate and alphabet types in arbitrary universes. Its proof is the special case
  `β = Unit` of the new family statement `tensorFoldFamilyBad_probability_le`.
* `tensorFoldBad_probability_height_three` is ported unchanged.
* `prob_not_hasFullTensorDecomposition_le` is new; it states the conclusion the source obtains by
  combining the probability bound with `hasFullTensorDecomposition_of_not_mem_bad`.

## `ArkLib/Data/CodingTheory/ProximityGenerator/Interleaving.lean`

* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26], Corollary 4.5, the exact transfer when the seed space has at most as many
  elements as the field.
* ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` proves this row-projection argument
  three times, as private declarations under `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/`:
  `interleaved_powerProjectionBad_card_le` in `PowerAgreement.lean` (univariate powers over a
  finite field), `interleaved_powerProjectionBadArbitrary_finset_card_le` in
  `PowerAgreementArbitrary.lean` (univariate powers over an arbitrary field), and
  `interleaved_lineProjectionBad_card_le` in
  `TensorFoldAgreement.lean` (the binary line fold). Their shared row-functional avoidance step
  is supplied by `Code.exists_rowFunctional_forall_notMem`. The integer-threshold transfer and
  the exact-agreement conclusions of the first two are in
  `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement`; the seedwise transfer here is derived
  from `Code.exists_forall_isProjectionBad_of_interleaved` through `isMCA_iff_isProjectionBad`.

Not covered here: the field-size-weighted transfer bound of [Jo26] for seed spaces larger than the
field.

`mcaError_moduleInterleavedCode_le_of_card_le`: This generalizes [Jo26] Corollary 4.5 (one direction) and `ProximityGap.mcaError_interleaved_le`,
which is the affine-line case.

`mcaError_moduleInterleavedCode_le_of_card_le`: For larger seed spaces [Jo26]
proves a weaker, field-size-weighted bound, which is not formalized here.

`mcaError_moduleInterleavedCode_eq_of_card_le`: This is [Jo26] Corollary 4.5 for an arbitrary generator and module code. It combines

## `ArkLib/Data/CodingTheory/ReedSolomon/AgreementList.lean`

`exists_constantCode_list` from
`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ConstantCode.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` is now
`exists_closePolynomial_finset_one_card_le_div`, for any received word in place of a batched
word, with the `ncard` form `closePolynomialSet_one_ncard_le_div`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/AgreementList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `closePolynomialSet_card_le_of_differential_equation`, a thin specialization of the generic finite-family theorem to finite sets of differential-equation solutions in `closePolynomialSet`.

## `ArkLib/Data/CodingTheory/ReedSolomon/AgreementThreshold.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/AgreementThreshold.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, with the same formulas. Source
`agreementThreshold` maps to `ReedSolomon.capacityAgreementThreshold`, and source
`agreementThreshold_le_iff_real` maps to
`ReedSolomon.capacityAgreementThreshold_le_iff_real`; `capacityRadius` is unchanged. Source
`relHammingDist_le_capacityRadius_iff_agreementThreshold_le` maps to
`ReedSolomon.relHammingDist_le_capacityRadius_iff_capacityAgreementThreshold_le`, which holds for
any finite coordinate type
in place of `Fin blockLength`, and goes through the new `Code.relHammingDist_le_one_sub_div_iff`
of `ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius`.
## `ArkLib/Data/CodingTheory/ReedSolomon/Agreement.lean`

`ReedSolomon.polynomialAgreementSet_map` is the private `agreementSet_map` of
`PolynomialCurve/ExtensionDescent.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, made public and stated over semirings for any
injective ring hom.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/SolutionExtension.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`mapped_agreement_count` is now `card_polynomialAgreement_map`. It applies to any finite indexed domain, including domains with repeated evaluation points, and lives in the Reed–Solomon agreement API.

Not ported: `card_image_polynomial_map` follows from `Finset.card_image_of_injective` and `Polynomial.map_injective`; the acceptance test derives the source-shaped count.

## `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AgreementBounds.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AgreementBounds.lean`:

* `tupleRatFunc` is ported, defined directly as the sum `∑ j, a j * Z ^ j` in `RatFunc F`; the
  auxiliary `tuplePolynomial` is not needed. `tupleRatFunc_injective` is ported.
* `packRowPolynomials`, `packRowPolynomials_eval` and `packRowPolynomials_degree_lt` are replaced
  by `comp_mem_code_map` and `pack_comp_mem_code_map`: the packed row polynomial is a
  `K`-linear combination of the mapped row polynomials, so its membership in the code over `K`
  follows from closure of the code under `K`-linear combinations, for an arbitrary packing and an
  arbitrary injective ring homomorphism.
* `lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound` is generalized to
  `Lambda_interleaved_le_of_injective_pack` and `Lambda_interleaved_le_ratFunc`: an arbitrary
  radius replaces `capacityRadius delta n k`, an arbitrary finite coordinate type replaces
  `Fin n`, an arbitrary finite width type and injective packing replace `Fin t` and `F(Z)`, and
  the conclusion is an inequality between `Lambda` values rather than a transfer of a
  finite-family agreement bound. The source hypothesis is a bound on the scalar list over `F(Z)`,
  which is exactly an upper bound on the right-hand side.
* `ringChar_ratFunc` is not ported: it is `ringChar.eq (RatFunc F) (ringChar F)`, using Mathlib's
  `CharP` instance on `RatFunc F`.

Deferred: `mcaError_interleaved_le_of_exactAgreement` needs `LineExactAgreementBound` and
`mcaError_affineLine_le_of_exactAgreement` from `MutualCorrelatedAgreement/LineToAffine.lean`, and
`lambda_rs_le_of_finite_polynomial_agreement_bound` needs `capacityRadius`,
`ReedSolomon.capacityAgreementThreshold`
and `lambda_le_of_forall_agreeingPolynomials_encard_le` from
`ListDecodability/Capacity/CodewordBound.lean` and its imports. None of these is on main. The
interleaving step of the first is already `ProximityGap.mcaError_interleaved_eq`.

## `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AnchoredAgreement.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AnchoredAgreement.lean`:

* `tupleEvaluation` is `Polynomial.evalTuple domain`, with `Fin n` and `Fin width` generalized to
  finite types `ι` and `κ`. `tuple_eq_of_evaluation_eq` and `candidateSet_injective` are
  `injOn_evalTuple_of_degree_lt`, without the source's `0 < k`.
* `CandidateSet domain received T A` is `candidateSet domain received (T + 3) A`: the degree
  bound `K` is a parameter instead of `T + 3`.
* `candidateSet_finite`, `candidateFamily`, `mem_candidateFamily` and `candidateFamily_card_le`
  are replaced by `encard_candidateSet_le_Lambda` and `finite_candidateSet_of_Lambda_le`, which
  bound the set itself instead of a `Finset` built from a finiteness proof. The source's radius
  `capacityRadius delta n (T + 3)` with the threshold
  `ReedSolomon.capacityAgreementThreshold delta n (T + 3) ≤ A`
  is replaced by the radius `1 - A / n`, which is at most the source radius under that
  threshold; the conversion is `Code.encard_setOf_le_agree_encode_le_Lambda`. The hypotheses
  `0 ≤ delta` and `0 < n` are not needed.
* `badAnchorPairs`, `badAnchorRate`, `badAnchorRate_eq`,
  `not_mem_collisionSet_of_sampled_of_not_mem_badAnchorPairs`, `badAnchorRate_le` and
  `candidateFamily_badAnchorRate_le` are replaced by the event
  `¬ Set.InjOn (evalTuple ![s₁, s₂]) (candidateSet …)` and its probability bounds
  `prob_not_injOn_candidateSet_le` (any finite sample space of anchor tuples) and
  `prob_not_injOn_candidateSet_offDiag_le` (the source's space of ordered distinct pairs outside
  the domain, with the source's denominator). The source's rate
  `choose L 2 * ((T + 2) / (q - n - 1)) ^ 2` is at least the bound here,
  `choose L 2 * (T + 2) ^ 2 / ((q - n) (q - n - 1))`.
  `natDegree_le_add_two_of_degree_lt_add_three` is the step `degree < K → natDegree ≤ K - 1`
  inside `prob_not_injOn_candidateSet_le`.
* `twoAnchorValues` is `evalTuple ![s₁, s₂]`, and `twoAnchorValues_injOn_of_good` and
  `eq_of_claimed_twoAnchorValues_of_good` are the separation event itself.
* `cubicQuotientWord`, `cubicResidualWord` and `cubicReconstructedTuple_agreement` are
  generalized to any divisor `D` in `agree_evalTuple_mul_add`, which is an equality.
  `cubicReconstructedTuple` is `fun j ↦ cubicAnchorReconstruct s₁ s₂ z (q j) (I j)`.
* `LaterCubicReconstruction`, `SuccessfulCubicReconstruction` and
  `successfulCubicReconstruction_mem_and_values` are replaced by the unbundled hypotheses of
  `exists_selected_before_reconstruction` and `exists_selectedCandidate_before_later`. The
  source's conditions `s₁ ≠ s₂`, `z ≠ s₁`, `z ≠ s₂`, the claimed value at `z`, and `0 < T` are
  not used by the conclusion and are dropped.
* `exists_selectedCandidate_before_later` is ported with the separation event as hypothesis in
  place of the sampled-pair and bad-set hypotheses, and with an `↔` characterization of the
  selected option. Its list-size and threshold hypotheses are not needed, since separation is a
  hypothesis.
* `traceRemainderTuple`, `traceRemainderTuple_degree_lt`, `traceRemainderTuple_eval_eq` and
  `exists_selectedTrace_before_later` are not ported as declarations: the remainder of a tuple is
  `fun j ↦ Q j %ₘ (X ^ T - C 1)`, its properties are `ReedSolomon.traceRemainder_degree_lt` and
  `ReedSolomon.traceRemainder_eval_eq` in each coordinate, and the trace statement follows by
  applying `Option.map` to `exists_selectedCandidate_before_later`.

The source file `ArkLib/Data/Probability/TwoPointPolynomialCollision.lean` is covered by
`ArkLib.Data.Polynomial.PointCollision`.

Deferred: the application-level statements of the source's consumers, which combine these
results with a concrete list-size bound for `Lambda`.

## `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AnchoredReconstruction.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AnchoredReconstruction.lean`:

* `cubicAnchorDivisor` and `cubicAnchorReconstruct` are ported unchanged, over a commutative ring
  instead of a field.
* `cubicAnchorReconstruct_degree_lt`, `cubicAnchorReconstruct_eval_anchors` and
  `cubicAnchorReconstruct_eval_of_quotient` are ported as specializations of
  `Polynomial.degree_mul_add_lt`, `Polynomial.eval_mul_add_of_eval_eq_zero` and
  `Polynomial.eval_mul_add_of_eval_mul_eq_sub`. The degree bound drops the source hypothesis
  `0 < k`, which is not needed.
* `traceRemainder_degree_lt` and `traceRemainder_eval_eq` are ported with the divisor
  `X ^ T - 1` generalized to `X ^ T - c`, over a nontrivial commutative ring. The value statement
  is `Polynomial.eval₂_modByMonic_eq_self_of_root` and needs no hypothesis on `T`.

Deferred: the consumers in `AnchoredAgreement.lean` at the same revision.

## `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/PowerAgreement.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `ReedSolomon/Interleaved/PowerAgreement.lean`: the definitions
  `interleavedPolynomialAgreementSet`, `interleavedCommonPowerAgreementSet`,
  `interleavedPowerBatchedWord`, `HasExactInterleavedPowerAgreement`,
  `UniformExactInterleavedPowerAgreement`, `padFin`, `paddedPowerValues`, and the theorems
  `sum_padFin`, `interleavedPowerBatchedWord_padded_apply`,
  `exactNestedPowerAgreement_of_interleaved`, and `nestedPowerAgreement_sharedInner` are ported
  with `Fin n` columns generalized to a finite type `ι` and, in the definitions, `Fin width` rows
  generalized to a finite type `κ`. The theorem `uniformExactInterleavedPowerAgreement_of_scalar`
  (hypotheses `[Finite F]`, `0 < width`, `k ≤ agreement`) is generalized to the theorem of the
  same name here, which has neither `[Finite F]` nor a width hypothesis. The private counting
  lemmas `scalar_powerProjectionBad_card_le` and `interleaved_powerProjectionBad_card_le`, and the
  public `interleavedCodeword_eq_of_agree_on`, are replaced by the code-level statements of
  `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement` and
  `ReedSolomon.determinedByAgreement_code`.
* `ReedSolomon/Interleaved/PowerAgreementArbitrary.lean`:
  `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary` removed the hypothesis
  `[Finite F]` from the previous theorem by a second, infinite-field proof. Here a single proof
  covers both cases, so it is the theorem `uniformExactInterleavedPowerAgreement_of_scalar`
  itself. Its private lemmas are covered as described in
  `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement`.
* `ReedSolomon/MutualCorrelatedAgreement/NestedPowerAgreement.lean`:
  `HasExactNestedPowerAgreement`, with `Fin n` generalized to `ι`. The arithmetic lemma
  `nestedPowerAgreement_probability_bound` (a set of at most `|F| * E` pairs has rational density
  at most `E / |F|` in `F × F`) is replaced by `nestedPowerAgreement_probability_le`, which bounds
  the probability of the failure event itself as a native event `Pr{let p ← $ᵗ (F × F)}[…]`.

Deferred: the shared-level fold and tensor-tight statements of
`ReedSolomon/Interleaved/TensorFoldAgreement.lean` and the concrete Reed–Solomon
endpoints that supply the scalar guarantee.

## `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/TensorFoldAgreement.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/TensorFoldAgreement.lean`:

* `fullSetLevelWitness_interleaved_of_exactAgreement` assumed `LineExactAgreementBound domain k
  agreement exceptionalCount`, `0 < width` and `k ≤ agreement`, for `Fin n` columns and
  `Fin width` rows. Here the scalar hypothesis is `UniformExactPowerAgreement` at `ℓ = 1`, which
  states the same line guarantee with the challenge set counted in `ℕ` (the source's
  `LineExactAgreementBound` is not ported); columns are any finite type, rows any finite type
  including an empty one, and there is no width hypothesis. The proof is
  `TensorMCA.fullSetLevelWitness_of_uniformExactAgreement` followed by
  `TensorMCA.FullSetLevelWitness.moduleInterleavedCode`.
* `interleavedRS_tensorFoldBad_card_le_heightThree`: the same statement over the new witness.
* The private `lineProjectionBad`, `scalar_lineProjectionBad_card_le`,
  `interleaved_lineProjectionBad_card_le` and
  `exists_exceptional_fullSetLine_interleaved_of_exactAgreement` are covered by the generic
  results listed in `ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement`, and
  `scalar_lineProjectionBad_card_le` by `uniformExactAgreement_binaryEqualityGenerator_of_line`.

Deferred: scalar providers of the line guarantee (list-decoding and curve-counting results) and
the probability form of the count.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/CodewordBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/CodewordBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`agreeingPolynomials_encard_le_closePolynomialSet`, `lambda_le_ceil_of_closePolynomialSet_bound`, and `prescribed_geometric_lambda_bound` keep their names and results. The transfer uses the current `Fintype.card_fin` representation. The geometric bound uses the canonical `xi` and `harmonic` parameters in place of the source's explicit `27/10` and `harmonicNumber` parameters. No public declaration was omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/CurveCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/CurveCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_closePolynomial_list_of_curve_certificate_actualStages`, `close_list_bound_of_curve_certificate_directJetCoarse`, and `close_list_bound_of_curve_certificate_of_jetCharacteristic` keep their names and results. The proofs use the current `SymbolicReceivedCurve.Certificate`, `SeparantChain`, agreement-list, and direct-jet APIs. No public declaration was omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/ExactLists.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The module moved to `Capacity/ExactLists.lean` so it sits with the other capacity modules and does not look like an umbrella for `Capacity/*`. `capacityLengthThreshold` and `capacityListBound` are unchanged, written with main's `weightedSupportMultiplicity (capacityDerivativeOrder δ)`. `HasCapacityLists` drops the premise `A ≤ 2 * n`, which no proof used, so the property is stronger; it keeps the conjunct `n < A → list = ∅`. `HasCapacityLists.mono`, `CapacityListBounds` and `uniformFirstOrder_capacity_list` are unchanged. `exists_capacity_list` drops `δ < 1`, since main's `exists_field_bounded_capacity_list` does not need it. `rateCapacityLengthThreshold` (using `uniformMathematicalCapacityLength`), `rateCapacityListBound` (using `mathematicalUniformListConstant`) and `exists_rateCapacity_list` are unchanged. The source names `capacityLengthThreshold`, `capacityListBound` and `exists_capacity_list` are kept for the weighted-support family, and `rateCapacity*` for the all-rate family. The long source docstring was rewritten to describe only the API present on main. The private helpers are ported as private declarations.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/FiniteField.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/FiniteField.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_field_bounded_capacity_list` keeps its name. It drops the unused assumptions `delta < 1` and `A ≤ 2 * n`, and states the derivative order and multiplicity through the canonical capacity parameter definitions. No declarations were left unported.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/FixedRateExplicitGate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/RatePartition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`fixedRatePartitionOrder_list_bound_selected` and `fixedRatePartitionOrder_list_bound` retain their names and mathematical guarantees, using the destination parameter and threshold APIs. The destination names `RatePartition.rateBlockThreshold` and `RatePartition.rateJetCap` replace `ratePartitionMathematicalLength` and `ratePartitionJetBound`; their definitions match. Both proofs specialize `ratePartition_close_list_bound`. Both public source declarations are covered; no declarations were omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/GeometricBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/GeometricBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`prescribed_geometric_finite_list_bound` and `prescribed_geometric_close_list_bound` keep their names. They use the current prescribed weighted-support parameters and symbolic certificate APIs to give geometric bounds for finite sublists and the complete close-polynomial set. The geometric ratio/counting lemmas, parameters, certificate, and characteristic/cast facts are reused from their current owners. No public source declaration from this module was omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/MathematicalUniformRate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/MathematicalUniformRate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`mathematicalUniformRatePartition_close_list_bound` keeps its statement apart from main's parameter names (`uniformMathematicalLength`, `uniformMathematicalJetBound`, `uniformDerivativeOrder`). Its proof now goes through main's `close_list_bound_of_curve_certificate_of_jetCharacteristic` instead of the coarse direct-jet bound plus `geometric_ratio_le`. `uniformCapacityListConstant300` → `mathematicalUniformListConstant` with the same definition under main's parameter names. `uniform_capacity_list_bound_300` → `mathematicalUniform_capacity_list_bound`; its threshold is main's `uniformMathematicalCapacityLength`, which is the source's `uniformCapacityLengthThreshold300`. The conclusion is written directly instead of through `let d`/`let C`, and the Johnson branch uses the new public gap theorem `closePolynomialSet_finite_and_ncard_le_pairwiseJohnson_of_gap` in `ListDecodability/PairwiseJohnson.lean`. That theorem generalizes the source's private `uniformCapacity_close_list_bound_johnson`: the hypotheses `⌈4ν/δ²⌉₊ ≤ n` and `k ≤ ν` become `4 (k - 1) ≤ δ² n`, and `A ≤ n` and `DecidableEq F` are dropped.

Not ported: `mathematicalUniformRatePartition_close_list_bound_of_length_characteristic`, a compatibility wrapper with no consumer that only weakens the characteristic guard to `n ≤ char F`.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/RatePartition.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/RatePartition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ratePartition_close_list_bound` and `exists_ratePartition_list_bound` keep their source names and mathematical statements. Their proofs use the current partition-parameter API, curve-certificate construction, and close-list bound. Neither declaration was deferred or left unported.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/UniformRate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/UniformRate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`uniformRatePartition_close_list_bound` and `uniform_capacity_list_bound` keep their source names and mathematical statements. Their proofs use the current uniform parameter names, generalized envelope certificate, curve-certificate construction, and close-list bound. Neither declaration was deferred or left unported.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/WeightedSupportInterpolant.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/WeightedSupportInterpolant.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_weightedSupport_interpolant_of_fixed_margin`, `exists_prescribed_weightedSupport_construction_core`, `exists_prescribed_weightedSupport_construction`, and `HiddenDerivativeInterpolationCertificate.agreeingPolynomials_encard_le_totalJetDegree` retain their mathematical guarantees using the destination weighted-support, harmonic, parameter, certificate, and root-count APIs. The first theorem specializes the symbolic kernel construction at challenge zero; the prescribed construction uses the existing capacity parameters. The final theorem uses the solution embedding and bounded-solution root count to obtain the extension-field list bound `4 * m * q ^ (e * d)`.

The symbolic height bound was renamed from `noBand_kernel_height_lt` to `kernel_height_lt_twelve_mul_of_margin`. The matrix block rank argument uses the range embedding and finite-dimensional rank bound. `map_projectLowContact` and `map_unscaledLocalSubstitution` are supplied by the existing local-constraint API. `WeightedSupportIndex` is not retained as an alias; support uses `weightedSupportExponents`. The three differential-specialization agreement lemmas are outside the unit's main statements, since the list bound uses the existing solution embedding and bounded-solution root count.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TaylorCutoff.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The weighted-support construction now uses `jetDegreeCastsNeZero_of_jetTotalDegree_charGuard` instead of repeating the proof of the jet-degree cast condition.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/DirectJetList.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Counting/DirectJetList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The declarations map to themselves: `directJetAgreementSolutions` → `directJetAgreementSolutions`, `directJetStageCharge` → `directJetStageCharge`, `directJetCommonOrderSum` → `directJetCommonOrderSum`, `finite_actualStage_regularSolutions_card_le_dimensionSensitive` → `finite_actualStage_regularSolutions_card_le_dimensionSensitive`, `finset_card_le_directJetStageCharge_sum` → `finset_card_le_directJetStageCharge_sum`, `directJetAgreementSolutions_finite_and_ncard_le_chain` → `directJetAgreementSolutions_finite_and_ncard_le_chain`, `directJetStageCharge_sum_le_commonOrderSum` → `directJetStageCharge_sum_le_commonOrderSum`, `directJetCommonOrderSum_le_coarse` → `directJetCommonOrderSum_le_coarse`, `exists_chain_directJetAgreementSolutions_finite_and_ncard_le` → `exists_chain_directJetAgreementSolutions_finite_and_ncard_le`, and `exists_directJetList_actualStages_and_bounds` → `exists_directJetList_actualStages_and_bounds`. The stage charge now expresses `jetWeight` and `SymbolicSeparantChain.Stage` as `jetTotalDegree` and `SeparantStage`; the chain bound uses the current `SeparantChain` API. The regular-stage theorem derives its degree and equation hypotheses from agreement-set membership and uses the current `closePolynomialSet` API.

Did not port `directJetAgreementSolutions_finite_and_ncard_le_coarse`, since it follows from `closePolynomialSet_finite` and `closePolynomialSet_card_le_of_differential_equation`. The characteristic-zero declarations are covered by existing general theorems: `separant_ne_zero` with `JetDegreeCastsNeZero`, `card_le_of_regular_solutions_agreement`, `boundedSolution_card_le_sq_totalJetDegree`, and `finite_solutions_card_le_sq_totalJetDegree_of_agreement` with the Reed–Solomon close-polynomial specialization.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Bounds.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Bounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`automaticFirstOrder_closePolynomialSet_finite_and_card_le`, `automatic_first_order_list_bound`, `automatic_first_order_list_bound_of_slack`, `automaticFirstOrder_closePolynomialSet_at_ceil_finite_and_card_le`, and `automatic_first_order_squarefree_list_bound_of_slack` keep their names. The private close-set membership equivalence is restated using the destination agreement-set API. No advertised declaration from the unit was omitted.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/FiniteLengthList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one` and `closePolynomialSet_finite_and_card_le_inv_eta_of_dimension_le_one` retain their names. `closePolynomialSet_finite_and_card_le_finiteLength_of_certificate` retains its name and conclusion, and derives `2 ≤ n` and `k ≤ n` from the certificate hypotheses. `closePolynomialSet_finite_and_card_le_inv_eta_of_certificate` retains its name and uses the finite-length certificate bound with the same derived inequalities. The inverse-eta results are retained as weaker-denominator bounds. The module reuses the existing agreement-membership equivalence.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/LowRateSemantics.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`closePolynomialSet_finite_and_card_le_finiteLength_of_bounded_certificate` keeps its name and finite-length conclusion. The list-bounds owner now derives `k ≤ n` from `k ≤ A ≤ n`.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/FiniteLengthParameters.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/FiniteLengthParameters.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finiteLengthSlack`, `finiteLengthSlack_pos`, `eta_le_finiteLengthSlack`, `finiteLengthSlack_inv_le_length`, `div_finiteLengthSlack_sq_le_div_eta_sq`, `div_finiteLengthSlack_four_le_div_eta_four`, and `squarefreeListExpression_le_finiteLength` retain their names. The positivity, slack comparison, and inverse-power comparison declarations were generalized by dropping `0 < n`; the inverse-length bound retains that premise. The squarefree theorem uses `regularTaylorExponent` in place of the source parameter `hybridTau`.

`finiteLengthMCAEnvelope`, `finiteLengthMCAEnvelope_le_rateEnvelope`, `finiteLengthMCAEnvelope_le`, and `finiteLengthMCAEnvelope_le_inv_eta` were renamed to `finiteLengthMcaEnvelope`, `finiteLengthMcaEnvelope_le_rateEnvelope`, `finiteLengthMcaEnvelope_le`, and `finiteLengthMcaEnvelope_le_inv_eta` to match ArkLib's `Mca` casing. The public rate-envelope theorem was included although it was omitted from the source declaration inventory. All 11 public source declarations are represented; none were left unported.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/FiniteLengthSelectors.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/FiniteLengthSelectors.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The declarations `automaticSurplusSlope_mul_finiteLengthSlack_le_margin`, `finiteLengthCertifiedAgreement`, `finiteLengthChallengeHeight`, `finiteLengthChallengeHeight_le_common_inv_slack_sq`, `finiteLengthChallengeHeight_le_inv_slack_sq`, `finiteLengthChallengeHeight_le_inv_slack_sq_of_count_gap`, `finiteLengthDensityMargin`, `finiteLengthDensityMargin_pos`, `finiteLengthDerivativeCap`, `finiteLengthDerivativeCap_le_inv_slack`, `finiteLengthDerivativeCap_le_jetDegree`, `finiteLengthDerivativeRatio`, `finiteLengthHeightBoundConstant`, `finiteLengthJetBoundConstant`, `finiteLengthJetDegree`, `finiteLengthJetDegree_le_inv_slack`, `finiteLengthMultiplicity`, `finiteLengthMultiplicityBoundConstant`, `finiteLengthMultiplicity_le_inv_slack`, `finiteLengthMultiplicity_pos`, `finiteLengthParameterBoundConstant`, `finiteLengthRankCount`, `finiteLengthRankRoundingConstant`, `finiteLengthRate`, `finiteLengthRate_eq`, `finiteLengthRate_lt_rate`, `finiteLengthRate_pos`, `finiteLengthSlack_lt_one_of_rate`, `finiteLengthSourceCount`, `finiteLength_count_gap`, `finiteLength_fixedRateMargin_eq_surplus`, `finiteLength_multiplicity_derivativeCap_jetDegree_bounds`, `length_pos_of_two_le_rate_mul_length`, and `sourceDensity_gain_at_finiteLengthRate` retain their names. `finiteLengthDerivativeCap_le_multiplicity`, `finiteLengthRankCount_le_density_add_three_mul_sq`, and `half_rate_le_finiteLengthRate` were generalized by dropping `0 < rho`, `0 < eta`, and `2 ≤ rho * n`; `finiteLengthSourceDensity_mul_cube_le_sourceCount` drops the derivative-ratio bound `≤ 1 / 2`.

`finiteLengthRankCount_le_two_mul_cube` is covered by `firstOrderRankCount_le_two_mul_cube` in `RoundedCounts`. The weakening `finiteLengthChallengeHeight_le_common_inv_slack_sq_of_count_gap` was not ported because its common-constant comparison is inlined in the final common-height theorem. `one_le_finiteLengthParameterBoundConstant` follows from the outer `max 1`, so it was not added. The private rounded-count proof block was unnecessary after using the existing generic rounded-count estimates.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/LowRateFiniteLength.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/LowRateFiniteLength.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`lowRateEtaSlope` → `lowRateAgreementSlackSlope` and `lowRateEtaSlope_mul_eta_le_fixed_margin` → `lowRateAgreementSlackSlope_mul_slack_le_fixed_margin` use agreement-slack naming. `lowRateFiniteLengthCertifiedAgreement`, `lowRateFiniteLengthCertifiedAgreement_ge_half_slack`, `lowRateFiniteLengthCertifiedAgreement_lt_one`, `lowRateFiniteLengthCertifiedAgreement_pos`, `lowRateFiniteLengthDensityMargin`, `lowRateFiniteLengthDerivativeCap`, `lowRateFiniteLengthJetDegree`, `lowRateFiniteLengthMultiplicity`, `lowRateFiniteLengthRankCount`, `lowRateFiniteLengthRankRoundingConstant`, `lowRateFiniteLengthSlope`, `lowRateFiniteLengthSourceCount`, and `lowRateInverseLengthSlope` retain their names and statements. `lowRateFiniteLengthDensityMargin_pos`, `lowRateFiniteLengthMultiplicity_pos`, `lowRateFiniteLengthSlope_mul_slack_le_margin`, `lowRateFiniteLengthSlope_pos`, `lowRateFiniteLengthSourceDensity_mul_cube_le_sourceCount`, and `lowRateFiniteLength_count_gap` drop the `rho < 1` premise. `lowRateInverseLengthSlope_div_length_le_gain` drops `rho < 1` and the low-rate branch premise. The first-order acceptance cases in `ArkLibTest/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder.lean` check slope positivity and the margin, source-count, generic rank-rounding, and count-gap bounds at `rho = 1/16`, `eta = 1/8`, and `n = 64`.

The source declaration `lowRateFiniteLengthRankCount_le_density_add_rounding` is covered by `firstOrderRankCount_floor_le_density_add_rounding`, which is applied directly in `lowRateFiniteLength_count_gap`. The source-count rounding application uses the generic `cube_mul_sourceDensity_le_firstOrderSourceCount` result.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/LowRateFiniteLengthBounds.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/LowRateFiniteLengthBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The declarations `lowRateFiniteLengthChallengeHeight`, `lowRateMultiplicityBoundConstant`, `lowRateDerivativeCapBoundConstant`, `lowRateJetBoundConstant`, `lowRateRankBoundConstant`, `lowRateHeightBoundConstant`, `lowRateParameterBoundConstant`, `lowRateFiniteLengthSlack_lt_one`, `lowRateFiniteLengthMultiplicity_le_inv_slack`, `lowRateFiniteLengthDerivativeCap_le_inv_slack`, `lowRateFiniteLengthDerivativeCap_le_jetDegree`, `lowRateFiniteLengthJetDegree_le_inv_slack`, `lowRateFiniteLengthChallengeHeight_le_inv_slack_sq`, and `lowRateFiniteLength_parameter_bounds` keep their names. The low-rate slack and inverse-slack bounds no longer assume `rho < 1`. The derivative-cap/jet-degree theorem also drops unused `rho < 1` and low-rate branch assumptions. The shared threshold slack comparison in `FiniteLengthSelectors.lean` derives rate positivity from the length guard. The generic selector derivative-cap/jet-degree theorem drops its unused threshold-plus-slack upper bound.

The generic floor-to-ceiling comparison is shared in `RoundedCounts.lean`. In `Ratio.lean`, `natCeil_mul_div_le_inv_slack` is generalized from `ℝ` to ordered fields with a floor structure and renamed `Nat.cast_ceil_mul_div_le_inv_slack`; `maxOneFloor_mul_div_le_inv_slack_sq` receives the same generalization and is renamed `Nat.cast_max_one_floor_mul_div_le_inv_slack_sq`. The low-rate challenge-height proof reuses the shared rank-count rounding estimate instead of adding a low-rate wrapper.

`one_le_lowRateParameterBoundConstant` is not ported because the outer `max 1` gives the inequality directly and no main statement uses it. An acceptance case in the matching `ArkLibTest` file checks the slack bound, derivative-cap/jet-degree comparison, all four individual parameter bounds, and the shared parameter bound at `rho = 1/16`, `eta = 1/8`, and `n = 64`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/LowRateSemantics.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`lowRateFiniteLengthSlack_lt_one_of_one_le_rate_mul_length` keeps its name and moves to the low-rate finite-length bounds owner. Its unused `rho < 1` premise was dropped.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Profile.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Profile.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`tightListEnvelope`, `squarefreeListEnvelope`, `finiteListBound_of_profile`, and `finiteSquarefreeListBound_of_profile` keep their names. The finite-list theorems drop the redundant `p.k ≤ p.n` assumption. Their agreement condition uses the equivalent set-cardinality formulation. The squarefree theorem also drops `0 < p.firstDerivativeCap` and retains `p.firstDerivativeCap ≤ p.totalJetCap`; its envelope uses the destination regular Taylor exponent API.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Uniform.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Uniform.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_uniformFirstOrder_list` keeps its name and statement. The internals use main's names: `regularTaylorExponent` for `hybridTau` and `MvPolynomial.cappedDegreeMixedVolume` for `AffineHilbert.fixedFiberDerivativeImageDegree`. They also use main's argument order for `firstOrder_finite_agreement_solutions_card_le_squarefree`, main's `closePolynomialSet_finite_and_ncard_le_pairwiseJohnson` (`Code.pairwiseJohnsonListBound`), and `exists_closePolynomial_finset_one_card_le_div` for `k = 1`. The private helpers are ported as private declarations, except that `uniformFirstOrder_ordinaryEnvelope_eq` is inlined.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/HiddenDerivativeBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/HiddenDerivativeBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`agreeingPolynomialsToBoundedSolution`, `agreeingPolynomialToBoundedSolution`, and `exists_boundedSolution_polynomial_eq` keep their names and no longer require a positive interpolation budget. `agreeingPolynomials_encard_le_boundedSolution_natCard` and `agreeingPolynomials_encard_le_of_boundedSolution_natCard_le` also keep their names and remove that assumption. `agreeingPolynomials_encard_le_two_mul_pow_of_exactInterpolant` keeps its name and bound; it takes jet-cast and binomial hypotheses and derives the positive budget from nonzero exact-space membership. `differentialSpecialization_eq_zero_of_agreeingPolynomial` specializes exact-interpolation vanishing to the canonical agreement list. The new `agreeingPolynomialsToBoundedSolution_polynomial` and `agreeingPolynomialToBoundedSolution_polynomial` preserve the underlying polynomial.

In `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/SolutionEmbedding.lean`, the general form `agreeingPolynomialsToBoundedSolution` → `solutionEmbeddingOf` accepts any root proof on list members; `agreeingPolynomialToBoundedSolution_polynomial` → `solutionEmbeddingOf_polynomial` gives its polynomial-preservation law. The new subtype projection theorem `agreeingPolynomial_boundedSolution_polynomial` supports this direct construction.

No source public declarations were omitted. The generic `boundedSolutionOfPolynomial` constructor and its preservation theorem were removed; callers construct the bounded-solution subtype directly.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Only the sharp interface is ported, and it drops the `sharp` prefix. The parameter definitions are named `capacityLine*` and `capacityPower*` because a bare `capacityDerivativeOrder` would clash with `HiddenDerivative.capacityDerivativeOrder`.

- `sharpCapacityDerivativeOrder` → `capacityLineDerivativeOrder`, unchanged.
- `sharpCapacityLengthThreshold` → `capacityLineLength`. The branch for `δ ≥ 6/25` is `4` instead of `max 4 23`, because the first-order theorem needs only `2 ≤ n`.
- `sharpCapacityLineConstant` → `capacityLineConstant`, unchanged. Small gaps use `mathematicalUniformLineAgreementConstant`, formerly `uniformCapacityLineConstant300`.
- `sharpCapacityLengthThreshold_ge_four` → `four_le_capacityLineLength`; `one_le_sharpCapacityLineConstant` → `one_le_capacityLineConstant`, with `δ` explicit.
- `HasSharpCapacityLineAgreement` → `HasCapacityLineAgreement`. The hypothesis `k ≤ n` is dropped because no proof uses it. The conclusion is `LineExactAgreementBound domain k A (E n)`, equivalent to the source's per-`(f, g)` `HasExactCorrelatedPair` form. The guard becomes `ringChar F = 0 ∨ k - 1 < ringChar F`, equivalent to the source's because `ringChar F ≠ 1`.
- `sharpCapacity_lineAgreement` → `capacity_lineAgreement`, with `δ` implicit. The adapter `lineExactAgreementBound_sharpCapacity` is absorbed.
- `exists_sharpCapacity_lineAgreement` → `exists_capacity_lineAgreement`; it also covers the old `exists_capacity_lineAgreement`.
- `HasSharpCapacityAffineAgreement` → `HasCapacityAffineAgreement`. The hypothesis `1 ≤ s` is dropped, the guard is simplified as for lines, and the threshold is written `k + δ n ≤ card`.
- `sharpCapacity_affineAgreement` and the witness part of `sharpCapacity_affineAgreement_and_mcaError` → `HasCapacityLineAgreement.affineAgreement`, proved for any line predicate at any gap `0 ≤ δ`.
- `sharpCapacity_mcaError` and the error part of `sharpCapacity_affineAgreement_and_mcaError` → `HasCapacityLineAgreement.mcaError_le`, for any line predicate with no sign condition on `δ`. The radius is `capacityRadius δ n k`. The affine-space bound holds for every `s`. It adds `[SampleableType F]`, which `mcaError` requires.
- `exists_sharpCapacity_affineAgreement` → `exists_capacity_affineAgreement`; `exists_sharpCapacity_mcaError` → `exists_capacity_mcaError`, which also adds `[SampleableType F]`, drops `1 ≤ s` and uses `capacityRadius δ n k`.
- `sharpCapacityPowerGap`, `sharpCapacityPowerDerivativeOrder`, `sharpCapacityPowerJetBound`, `sharpCapacityPowerLengthThreshold` → `capacityPowerGap`, `capacityPowerDerivativeOrder`, `capacityPowerJetBound`, `capacityPowerLength`, unchanged.
- `sharpCapacityPowerConstant` → `capacityPowerConstant`, defined as `max C 1` instead of `C + 1`, which is no larger.
- `sharpCapacityPowerLengthThreshold_ge_four` → `four_le_capacityPowerLength`; `one_le_sharpCapacityPowerConstant` → `one_le_capacityPowerConstant`, which no longer needs `0 < δ`.
- `HasSharpCapacityPowerBatchingAgreement` → `HasCapacityPowerBatchingAgreement`. The characteristic bound `ν` is a parameter `(δ N ν E)` instead of being fixed to `sharpCapacityPowerJetBound δ`, and `k ≤ n` is dropped.
- `sharpCapacity_powerBatchingAgreement` → `capacity_powerBatchingAgreement`, with `ν := capacityPowerJetBound δ`.
- `exists_sharpCapacity_powerBatchingAgreement` → `exists_capacity_powerBatchingAgreement`, with `ν` also existential: `∃ N d ν C, 4 ≤ N ∧ ν < N ∧ 0 < C ∧ …`. The conjunct `ν < N` lets a caller who knows only `n ≤ char F` discharge the characteristic guard.

Not ported:
- The old 1000-based `HasCapacityLineAgreement`, `exists_capacity_lineAgreement`, `HasCapacityAffineAgreement`, `exists_capacity_affineAgreement`, `exists_capacity_affineAgreement_and_mcaError`, `exists_capacity_mcaError`, `HasCapacityPowerBatchingAgreement` and `exists_capacity_powerBatchingAgreement`, with guard `ringChar F = 0 ∨ n ≤ ringChar F`. The sharp versions subsume them, since `n ≤ char F` implies `k - 1 < char F` and the new power theorem records `ν < N ≤ n`.
- `uniformFirstOrder_capacity_lineAgreement`, covered by `capacity_lineAgreement` at `δ ≥ 6/25` and by `exists_uniformFirstOrder_lineMca`.
- `HasHalfGapLineAgreement`, `halfGap_lineAgreement`, `halfGap_capacity_lineAgreement`, covered by the more general `exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le`, which works over any `Fintype ι` and needs neither `0 < k`, `k ≤ n` nor `A ≤ n`.
- `sharpCapacityJetBound`, because no statement uses it; `sharpCapacityDerivativeOrder_pos`, because the `k = 1` branch is handled inside the line sub-theorems.
- `sharpCapacityLineConstant_pos`, `sharpCapacityPowerConstant_pos`, one step from the `one_le_*` lemmas.
- `lineExactAgreementBound_sharpCapacity`, because the line predicate now concludes `LineExactAgreementBound` directly.
- `sharpCapacity_affineAgreement_and_mcaError`, `sharpCapacity_affineAgreement`, `sharpCapacity_mcaError`, which are `(capacity_lineAgreement hδ).affineAgreement hδ.le` and `(capacity_lineAgreement hδ).mcaError_le …`; a named wrapper would only fix arguments.
- The private `constantCurveExceptionalBound_le_power`, inlined, since the constant-code bound `ℓ * (n.choose 2) / max (A - 1) 1` needs no case split.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/CertificateBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/CertificateBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_curveMCA_of_certificate` to `exists_exceptional_exactPowerAgreement_of_certificate` and `exists_curveMCA_of_certificate_of_jetCharacteristic` to `exists_exceptional_exactPowerAgreement_of_certificate_of_jetCharacteristic`. Both declarations remove `[DecidableEq E]`; the block-length endpoint also removes the redundant `0 < n` premise, derives the jet-characteristic guard, and applies the jet-characteristic endpoint. Both public declarations are ported.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/FixedRateExplicitGate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/FixedRateExplicitGate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `fixedRatePartitionOrder_lineMCA` to `fixedRatePartitionOrder_line_exactCorrelatedPair`. The mathematical guarantee is unchanged; the theorem specializes the existing general rate-partition line theorem using the current fixed-rate parameter selector and order bound. It uses the destination parameters `RatePartition.rateBlockThreshold`, `rateJetCap`, `marginHeight`, and `partitionFiniteRatio`, together with `polynomialCurveProductAgreementConstant`. Nothing was deferred or not ported.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/MathematicalUniformRate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/MathematicalUniformRate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

- `exists_mathematicalUniformRatePartition_curveMCA` → `ReedSolomon.exists_mathematicalUniformRatePartition_curve_exactPowerAgreement`. It drops the unused `[DecidableEq E]`. It uses main's names `polynomialCurveProductAgreementConstant`, `uniformMathematical*` and `uniformDerivativeOrder`, and states the mapped domain as `domain.trans ⟨iota, _⟩`, as in `UniformRate`.
- `exists_mathematicalUniformRatePartition_baseCurveMCA` → `ReedSolomon.exists_mathematicalUniformRatePartition_baseCurve_exactPowerAgreement`, unchanged. Descent goes through main's `uniformExactPowerAgreement_of_extension`.
- `uniformCapacityLineConstant300` → `ReedSolomon.mathematicalUniformLineAgreementConstant`, unchanged.
- `exists_mathematicalUniformRatePartition_lineMCA` → `ReedSolomon.exists_mathematicalUniformRatePartition_line_exactCorrelatedPair`, unchanged. The constant-message branch uses main's `uniformExactPowerAgreement_constantCode`, whose bound `choose 2 / max (A-1) 1` replaces the source's `if A = 1`, so the source's positivity side condition on `A` is gone. The two power-to-line conversions share one private helper, `exists_line_exactCorrelatedPair_of_powerAgreement`. When the curve characteristic guard fails, the line theorem uses the Johnson gap bound, so it needs only `char F = 0 ∨ k - 1 < char F`.

The curve theorems keep the source's sharp guard `max (k - 1) ν < char F` and do not use main's `UniformRate` form `n ≤ char F`. The private `exists_uniformCapacity_lineMCA_johnson` moved to the Johnson owner as `exists_johnson_line_exactCorrelatedPair_of_gap`. No source declaration was left out.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/Parameters.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/Parameters.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_prescribed_correlated_parameters` keeps its name and is generalized by dropping the source hypothesis `0 < k`. It uses the current `SymbolicReceivedCurve.Certificate` and `receivedLine` APIs. The theorem gives a symbolic received-line certificate, size and agreement bounds, and all binomial pivots below the block length from the characteristic bound. A concrete rational acceptance case checks that the certificate conclusion is inhabited. The `prescribed_correlated_extension_pivots` wrapper was not ported: its base-field pivot statement is the final conjunct of the parameter theorem, and extension-field nonvanishing follows by injectivity of the field homomorphism at existing use sites, so no generic wrapper was added.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/PrescribedCurve.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/PrescribedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_prescribedCurveMCA_exact` to `exists_exceptional_exactPowerAgreement_with_prescribed_stageBounds` and `exists_prescribedCurveMCA` to `exists_exceptional_exactPowerAgreement_of_prescribedCurve`. The stage-bounds declaration removes `[DecidableEq F]` and `[DecidableEq E]`; the prescribed-curve declaration removes `[DecidableEq E]`. Both public declarations are ported.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/PrescribedLine.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/PrescribedLine.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_prescribedLineMCA` to `exists_prescribedLine_exactCorrelatedPair`. The theorem drops the decidable-equality assumptions and uses the prescribed-curve and power-to-line APIs. Its acceptance case checks a zero line and zero candidate.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/ProductBounds.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/ProductBounds.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `ReedSolomon`.

`correlatedProductCutoff`, `correlatedProductCutoff_bounds`, `evaluation_incidence_factor_le`,
`evaluation_incidence_product_le`, `correlatedProductCutoff_jointRatio_le`,
`correlatedProductCutoff_fiberFactor_le`, `correlatedProductCutoff_fiberProduct_le`, and
`correlatedProductCutoff_fiberProduct_lt_three` keep their names. The two evaluation incidence
bounds are proved as specializations of reusable declarations added to
`ArkLib/ToMathlib/Combinatorics/Enumerative/IncidenceProduct.lean`:
`evaluation_incidence_factor_le` → `natCast_shiftedRatio_le_one_div`, generalized to arbitrary
natural inputs and linearly ordered fields with strict ordered-ring structure under
`0 < δ ≤ 1` and `δ * x ≤ y`; `evaluation_incidence_product_le` →
`dimensionSensitiveIncidenceProduct_le_one_div_pow_of_gap`, generalized to linearly ordered fields
with strict ordered-ring structure under `0 < δ ≤ 1`, `k ≤ A ≤ n`, and `k + δ * n ≤ A`.

Not ported: None. All eight source public declarations are represented.
## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/Basic.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/Basic.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`polynomialListBound`, `CapacityGapCertificate`, `CapacityGapCertificate.ofDecoderCertificate`,
`PointwiseListBound`, `CapacityGapCertificate.pointwiseListBound`,
`UniformPrimeFieldCapacityListBound`, `QuarterGapListBound`, and
`WeightedSupportListBound` keep their names. The source
`UniformPrimeFieldCapacityListBound.exists_uniform_pointwise_bound` is omitted: apply
`CapacityGapCertificate.pointwiseListBound` to the certificate supplied by
`UniformPrimeFieldCapacityListBound`. The certificate and
pointwise-list APIs generalize from `Fin n` over `ZMod q` to arbitrary finite coordinate types and
semiring alphabets where applicable. The all-rate prime-field specifications remain over `Fin n`.
`WeightedSupportListBound` uses the destination weighted-support parameter names.

Also ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/Radius.lean` at
the same ArkLib revision, `closeCodewordsRel_eq_eval_image_agreeingPolynomials`,
`lambda_le_of_forall_agreeingPolynomials_encard_le`, and
`CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound` retain their names and move here
from `Capacity/Radius`; they are generalized to arbitrary finite coordinate types.

Not ported from the separate `Capacity/Radius` module: `CapacityGapCertificate.ofPointwiseBound`,
which is outside this unit and is not needed by its endpoints. The deferred
`agreeingPolynomials_eq_empty_of_card_lt` API is not duplicated because pointwise emptiness follows
from `DecoderCertificate.decoder_eq_empty_of_card_lt`.

## `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/QuarterGap.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/QuarterGap.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`agreeingPolynomials_encard_le_one_of_half`,
`agreeingPolynomials_encard_lt_blockLength_of_quarter`, and `quarter_gap_list_bound` keep their
names. The two counting theorems generalize from `Fin n` to arbitrary finite coordinate types.
`quarter_gap_list_bound` keeps its quantitative specification and uses the generic pairwise-agreement
estimates with the exact-decoder and pointwise-bound factory from `Capacity/Basic`.

No public declaration from this source module was omitted. The separate
`agreeingPolynomials_eq_empty_of_card_lt` API is not duplicated; pointwise emptiness follows from
`DecoderCertificate.decoder_eq_empty_of_card_lt`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/ProductCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/ProductCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `polynomialCurveProductMCAConstant` to `polynomialCurveProductAgreementConstant`, `prescribedMCAConstant` to `prescribedProductAgreementConstant`, `prescribedMCAConstant_pos` to `prescribedProductAgreementConstant_pos`, `regularSymbolicCurveMCASharpBound_product_le_stage` to `regularPowerBatchedAgreementSharpBound_product_le_stage`, and `regularSymbolicCurveMCASharp_product_finiteStage_le` to `regularPowerBatchedAgreementSharp_product_finiteStage_le`. The product scalar formula and prescribed coefficient are unchanged. The prescribed coefficient uses the current equivalent `xi` and `harmonic` definitions. The regular-stage statements use the current power-batched API and existing generalized degree-cap bounds to supply exponent bounds. `polynomialCurveProductStageBound`, `product_stage_bound`, `polynomialCurveProductStageBound_le_uniform`, and `product_stages_aggregate` keep their names; the product cutoff estimate bounds each regular stage, uniformizes its order, and aggregates a finite family under one height cap.

Did not port `sourceCurveCutJetDegree_le_uniformCaps_of_exponent`, which is covered by `regularPowerBatchedCutJetDegree_le_two_mul` after deriving `τ ≤ 2*n` from `τ ≤ 2*K` and `K ≤ n`. Did not port `sourceCurveInitialMixedDegree_le_uniformCaps_of_exponent`, which is covered by `regularPowerBatchedInitialMixedDegree_le_uniformCaps` with the same derived exponent bound.

Acceptance cases for `product_stage_bound`, stage uniformization, scalar aggregation, the regular-stage bound, the finite-stage bound, and prescribed-coefficient positivity were appended to `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/RatePartition.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/RatePartition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_ratePartition_curveMCA` to `exists_ratePartition_curve_exactPowerAgreement`; it uses the current finite-parameter, block-length, and certificate APIs. Renamed `exists_ratePartition_baseCurveMCA` to `exists_ratePartition_baseCurve_exactPowerAgreement`; its mathematical statement is unchanged and uses the current extension-descent API. Renamed `exists_ratePartition_lineMCA` to `exists_ratePartition_line_exactCorrelatedPair` and `exists_ratePartition_lineMCA_parameters` to `exists_ratePartition_line_exactCorrelatedPair_parameters`; their mathematical statements are unchanged and specialize the base-field curve guarantee through power-to-line, with the parameter theorem selecting finite parameters from the strict rate gate. The acceptance cases retain each exceptional-set bound and apply its guarantee to a zero candidate and zero received word at a challenge outside the exceptional set.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/SharpCountingBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/SharpCountingBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Kept `correlatedMidpoint_ratios_le_two_div`, `polynomialCurveSharpStageBound`, and `polynomialCurveSharpStageBound_le_uniform`. Renamed `polynomialCurveSharpMCAConstant` to `polynomialCurveSharpAgreementConstant`, `regularSymbolicCurveMCASharpBound_midpoint_le_stageBound` to `regularPowerBatchedAgreementSharpBound_midpoint_le_stageBound`, and `regularSymbolicCurveMCASharp_finiteStage_uniform_le` to `regularPowerBatchedAgreementSharp_finiteStage_uniform_le`; the agreement theorems use the current power-batched API. `polynomialCurveSharpUniformStageBound` is not ported as a separate definition because `polynomialCurveSharpStageBound δ n ℓ v h d` supplies that bound at cap `d`. The capacity acceptance cases check midpoint ratios, the midpoint stage bound, uniformization from order `1` to cap `2`, and the finite-family bound.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/UniformRate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/UniformRate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_uniformRatePartition_curveMCA` to `exists_uniformRatePartition_curve_exactPowerAgreement`. It drops the extension decidable-equality assumption and uses the current uniform envelope and certificate APIs. Renamed `exists_uniformRatePartition_baseCurveMCA` to `exists_uniformRatePartition_baseCurve_exactPowerAgreement`; its mathematical statement is unchanged and descends the extension-field guarantee. Renamed `exists_uniformRatePartition_lineMCA` to `exists_uniformRatePartition_line_exactCorrelatedPair`; its mathematical statement is unchanged and specializes the base-field curve guarantee through power-to-line. The acceptance cases retain each exceptional-set bound and apply its guarantee to a zero candidate and zero received word at a challenge outside the exceptional set.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/ComponentDimension.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ComponentDimension.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Ported the chart and source coefficient maps, localization lemmas, prime degree bounds, hereditary component bounds, and finite hybrid incidence theorem. Renamed `chart_prime_hilbertPolynomial_natDegree_le_of_agreements_of_exponent` to `chart_prime_affineHilbertPolynomial_natDegree_le_of_agreements_of_exponent`, and renamed `symbolicSource_prime_hilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent` to `symbolicSource_prime_affineHilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent`. The chart bound now removes the `c ≤ k` premise. The polynomial source kernel theorem removes primality and separant nonvanishing assumptions. The finite incidence theorem removes `A ≤ n` and the unused initial separant nonvanishing premise.

The local symbolic source equation and numerator definitions now use `jointInitialJetEquation`, `jointInitialJetSeparant`, `jointCommonTaylorNumerator`, and `jointTaylorAgreementEquation`. The chart and source localization arguments share a private comparison proof. Principal-open and agreement-index helpers were replaced by direct zero-locus/set membership and `Set.ncard` expressions. `symbolicSource_prime_hilbertPolynomial_natDegree_le_of_agreements_of_exponent` was not ported: it specializes the polynomial-valued bound to affine received lines, and after the component proof was routed through the polynomial-valued theorem it has no caller. The affine kernel specialization was omitted as unused; the component-or-excluded interface was omitted because no theorem in the unit uses it; the separate source prime Hilbert-degree wrapper is covered by the existing generic `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_mem` theorem.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/EquationDescent.lean`

Ported from `HiddenDerivative/RootFinding/MutualCorrelatedAgreement/EquationDescent.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d:

`exists_exceptional_equation_correlatedAgreement_descend` keeps its name and statement under the current specialization and embedding APIs. It transfers equation-restricted agreement while preserving the exceptional-set size bound.

Not ported: `ChallengeHeightLE` as a separate predicate, because main already provides `MvPolynomial.CoeffNatDegreeLE`. The standalone exceptional correlated-agreement wrapper is also omitted because this theorem performs that exceptional-set pullback directly.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_equation_powerAgreement_descend` is new. It is the power-batched analogue of `exists_exceptional_equation_correlatedAgreement_descend`, over any finite index type, and replaces the inline pullback that the two source base-field theorems repeated.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/ExtensionDescent.lean`

Ported from `HiddenDerivative/RootFinding/MutualCorrelatedAgreement/ExtensionDescent.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d:

`HasExactCorrelatedPair.descend` keeps its name and statement. `HasExactCorrelatedPair` keeps its name and mathematical meaning; its mapped evaluation domain is expressed as an embedding composition. The definition was moved from `HiddenDerivative/RootFinding/MutualCorrelatedAgreement/Symbolic/RegularEquation.lean`.

Not ported: the standalone exceptional correlated-agreement wrapper from this dependency; the equation-descent theorem performs the exceptional-set pullback directly.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/AutomaticHybrid.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/AutomaticHybrid.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Bounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_firstOrder_hybrid`, `exists_automaticFirstOrder_hybridEquation`, `exists_automaticFirstOrder_hybridEquation_base` and `automatic_first_order_line_agreement` keep their names. The height premise `ChallengeHeightLE Q h` became `CoeffNatDegreeLE Q h`, `jetWeight` became `jetTotalDegree`, and `mappedDomain domain iota` became `domain.trans ⟨iota, _⟩`. The bounds were renamed: `hybridEOptimizedRaw` → `maxMinFirstOrderExceptionCharge`, `hybridEOptimizedCeil` → `firstOrderExceptionBound`, `hybridEClosed` → `firstOrderExceptionConstant`, `hybridTheta` → `agreementIncidenceRatio`, `hybridOrdinaryRaw` → `ordinaryTailCharge`, `hybridT` → `stageStaircase`, and `automaticFirstOrderThreshold` → `firstOrderRateThreshold`. The unused hypothesis `1 ≤ mu` was dropped. The theorems take `[DecidableEq F]` and `[DecidableEq E]` instead of `open Classical in`. Degree premises and conclusions are stated with `P.degree < k` and `HasExactPowerAgreement … k`, where the source used `D + 1` with `D = k - 1`. `exists_automaticFirstOrder_hybridEquation_base` states its conclusions along the line `fun i ↦ f i + z * g i` with `HasExactCorrelatedPair`, instead of `powerBatchedWord ![f, g] z` with `HasExactPowerAgreement`. `automatic_first_order_line_agreement` was moved here from `Bounds.lean`.

New declarations: `exists_exceptional_firstOrder_hybrid_base`, the base-field version through an algebraic-closure mapping and `exists_exceptional_equation_correlatedAgreement_descend`, which replaces the argument the source repeated in `exists_automaticFirstOrder_hybridEquation_base` and `exists_uniformFirstOrder_squarefree_lineMCA_of_two_le`; and `FirstOrderSymbolicCertificate.exists_exceptional_hybrid`, the base-field bound for the equation of any symbolic line certificate (`k = D + 1`). Private helpers `certificate_equation_facts`, `exists_automaticFirstOrder_equation` and `automaticFirstOrder_degree_bounds` are shared by both automatic theorems, which duplicated them inline in the source. The source's private `jetWeight_map_eq` is not ported because main has `jetTotalDegree_map_eq`.

Not ported: `automaticFirstOrder_list_and_lineMCA`, which is a conjunction of main's `automaticFirstOrder_closePolynomialSet_finite_and_card_le` and the line part of `exists_automaticFirstOrder_hybridEquation_base`, and `automatic_first_order_line_agreement_of_slack`, which is `automatic_first_order_line_agreement` at `a = firstOrderRateThreshold ρ + η₁` with `lt_add_of_pos_right _ hη₁`. The slack form with the rate envelope is `automaticFirstOrder_rate_bounds`. `Bounds.lean` therefore has no destination file.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/AutomaticMcaError.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/AutomaticHybridProbability.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`automaticFirstOrder_hybrid_mcaError_le` keeps its name and adds `[SampleableType F]`, which main's `mcaError` requires. The three line bounds go through the new `lineExactAgreementBound_of_exactCorrelatedPair` (in `PowerToLine.lean`) instead of three copies of the conversion. The module was renamed from `AutomaticHybridProbability` because the source module name is 101 characters and cannot be imported within the 100-character limit.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Branchwise.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Branchwise.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finiteLengthDerivativeRatio_le_half_of_rateSwitch_le` and `firstOrderBranchFiniteLengthDerivativeCap` keep their names. `firstOrderBranchFiniteLengthMCAConstant` → `firstOrderBranchFiniteLengthMcaConstant` and `one_le_firstOrderBranchFiniteLengthMCAConstant` → `one_le_firstOrderBranchFiniteLengthMcaConstant` use ArkLib capitalization.

`firstOrderBranch_finiteLength_finiteSlack_bounds` and `firstOrderBranch_finiteLength_rate_bounds` keep their names and conclusions. `firstOrderBranch_finiteLength_mcaError_le` keeps its name and adds `[SampleableType F]` for the current MCA probability API. The facade selects low-rate or automatic bounds at the rate switch and retains the source citation `[DKTZ26]`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/CurveAgreement.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrderCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Ported `exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent`, `exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_of_exponent`, `exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent`, and `exists_baseExceptional_firstOrderCurve_of_heightSlotCount_of_exponent` under the same names. Generalized each theorem by removing the `0 < k` assumption. The extension-field bounds come from a finite curve certificate or a strict shifted-height surplus, and the base-field bounds follow by uniform exact-agreement descent. The two height-slot tight wrappers were not ported because each only specializes its exponent theorem to `2K - 3`; the acceptance case uses the exponent theorem directly.
## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/FiniteLengthMca.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/FiniteLengthMCA.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finiteLengthMCAParameterConstant` → `finiteLengthMcaParameterConstant` and `one_le_finiteLengthMCAParameterConstant` → `one_le_finiteLengthMcaParameterConstant` keep their bounds with the destination `Mca` casing. The new `square_le_finiteLengthMcaExceptionBudget` gives the shared constant-code endpoint bound for any envelope constant at least one and finite-length slack at most one. `Squarefree.retainedSquarefreeLineMCAEnvelope_eq_finiteLengthMCAEnvelope` → `Squarefree.retainedSquarefreeLineAgreementEnvelope_eq_finiteLengthMcaEnvelope` uses the existing squarefree envelope, and `hybridEClosed_zero_eq_finiteLengthMCAEnvelope` → `firstOrderExceptionConstant_zero_eq_finiteLengthMcaEnvelope` uses the current hybrid constant.

`exists_finiteLengthFirstOrder_symbolicCertificate` keeps its name and mathematical certificate, using current rank and first-order interpolation APIs. `exists_exceptional_exactLineMCA_one` → `exists_exceptional_exactLineMca_one` keeps the constant-code result. `finiteLengthSelectorMCAEnvelope_le` → `finiteLengthSelectorMcaEnvelope_le` and `finiteLengthSelectorMCAEnvelope_le_inv_eta` → `finiteLengthSelectorMcaEnvelope_le_inv_eta` drop the unused `2 ≤ k` premise. `finiteLengthSelectorJetDegree_le_listEnvelope` keeps its name and bound.

`closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate` keeps its name and bound, using the existing generic positive-cap certificate theorem. `exists_exceptional_finiteLengthMCA_of_selector_certificate` → `exists_exceptional_finiteLengthMca_of_selector_certificate` and `exists_exceptional_finiteLengthMCA_of_selector_certificate_inv_eta` → `exists_exceptional_finiteLengthMca_of_selector_certificate_inv_eta` retain exact agreement and the inverse-fourth and eta-only bounds. `finiteLength_completeList_and_exceptionalMCA_of_selector_certificates` → `finiteLength_completeList_and_exceptionalMca_of_selector_certificates` and `finiteLength_completeList_and_exceptionalMCA_of_selector_certificates_inv_eta` → `finiteLength_completeList_and_exceptionalMca_of_selector_certificates_inv_eta` retain the joint list and exception results.

The zero derivative-cap proof uses the current symbolic-certificate hybrid theorem. Source names for `hybridTheta`, `hybridEClosed`, the threshold, and retained lines are expressed through the current `agreementIncidenceRatio`, `firstOrderExceptionConstant`, `firstOrderRateThreshold`, and retained squarefree line APIs. The private close-set membership helper was not ported because unfolding `closePolynomialSet` and `polynomialAgreementSet` suffices. The two private mapped-degree helpers and line coefficient-degree helper were not ported because `jetTotalDegree_map_le` and `jetDegree_map_le` in `PolynomialDifferential` cover them.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/LowRateSemantics.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_firstOrderMCA_zero_derivative_of_certificate` → `exists_exceptional_firstOrderMca_zero_derivative_of_certificate` drops the unused algebraic-closure field, embedding, and positive jet-degree premise. `exists_exceptional_firstOrderMCA_of_bounded_certificate` → `exists_exceptional_firstOrderMca_of_bounded_certificate` keeps its mathematical conclusion. Both are generic certificate bridges in the finite-length MCA owner, and the automatic selector proofs reuse them. The original zero-derivative descent proof is covered by `FirstOrderSymbolicCertificate.exists_exceptional_hybrid`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/FiniteLengthRateBounds.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/FiniteLengthRateBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`automaticFirstOrder_finiteLength_finiteSlack_bounds` and `automaticFirstOrder_finiteLength_rate_bounds` keep their names and respective finite-slack and eta-only list and line bounds. `automaticFirstOrder_finiteLength_mcaError_le` keeps its name and error bound, with the current affine-line API's `[SampleableType F]` instance. The automatic-rate results construct the symbolic certificates internally.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveProfile.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveProfile.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`CurveCertificate.hybridOptimizedCurveEnvelope` → `ReedSolomon.hybridOptimizedCurveEnvelope`, `CurveCertificate.bestCurveEnvelope` → `ReedSolomon.bestCurveEnvelope`, and `CurveCertificate.bestOptimizedCurveEnvelope` → `ReedSolomon.bestOptimizedCurveEnvelope` keep the profile quantities using current profile fields, including `candidateDegree`. `CurveCertificate.bestOptimizedCurveEnvelope_le_best` → `ReedSolomon.bestOptimizedCurveEnvelope_le_best` keeps its comparison.

`exists_exceptional_exact_powerAgreement_hybrid_optimized` → `exists_exceptional_exactPowerAgreement_hybridOptimized` drops `2 ≤ k`, which profile verification implies. `exists_exceptional_exact_powerAgreement_best_optimized` → `exists_exceptional_exactPowerAgreement_bestOptimized` drops that premise and the unnecessary `k < n` hypothesis. `exists_exceptional_exact_powerAgreement_best` → `exists_exceptional_exactPowerAgreement_best` drops the implied `2 ≤ k` premise. The recovery statements use profile verification to establish the message-dimension lower bound.

`CurveCertificate.bestCurveEnvelope_le_hybrid` and `CurveCertificate.bestCurveEnvelope_le_squarefree` were not ported because `bestCurveEnvelope` is a minimum and Mathlib's `min_le_left` and `min_le_right` give these projections directly.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveRecovery.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveRecovery.lean`, `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveBase.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, merged into one module:

- `exists_exceptional_firstOrder_hybridCurve_optimized` keeps its name. It drops `hDn`, renames `jetWeight` to `jetTotalDegree`, states the height premise as `CoeffNatDegreeLE Q h`, takes `DecidableEq` instances, and uses the domain `domain.trans ⟨iota, _⟩`.
- `exists_exceptional_firstOrder_hybridCurve_base_optimized` → `exists_baseExceptional_firstOrder_hybridCurve_optimized`. Renamed to main's `exists_baseExceptional_*` convention and drops `hDn`. The proof uses main's `exists_exceptional_equation_powerAgreement_descend` instead of a hand-written preimage argument.
- `exists_exceptional_firstOrder_hybridCurve_base_including_fullDimension` → `exists_baseExceptional_firstOrder_hybridCurve_including_fullDimension`. Renamed the same way; the statement is otherwise unchanged apart from main's conventions.
- `exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized_fullAgreement` → `exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized`. This is the agreement-set form under the shorter name, with `[DecidableEq F]` added.

Not ported: the source `exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized` in its "every agreeing index set" form. Any `indices` with `A ≤ indices.card` on which `P` agrees is a subset of `polynomialAgreementSet`, so the ported agreement-set form covers it; the downstream `HybridCurveEndpoints.lean` will need that subset step when ported. `therefore` in the unit's declaration list is a word from a source docstring, not a declaration.

The curve tail theorem `HiddenDerivative.FirstOrderHybridDescent.hasOrdinaryCurveTailTransfer` from `HybridCurveRecovery.lean` was ported to `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/OrdinaryTail.lean` as `ReedSolomon.HiddenDerivative.FirstOrderHybridDescent.exists_exceptional_ordinaryCurveTail`, next to the pair version. Renamed because there is no curve-transfer predicate. It drops `hDn : D + 2 ≤ n` and `hAn : A ≤ n`, takes the height as `CoeffNatDegreeLE Q h` on the starting equation, and takes `[DecidableEq F] [DecidableEq E]` instead of `open Classical`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveTransfer.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveTransfer.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `hybridCurveJ1` to `hybridCurveJointStageSum` and `regularSymbolicCurveMCADerivativeBoundTwo_eq_hybrid_curve_stage` to `regularPowerBatchedDerivativeCappedBoundTwo_eq_hybridCurveStage` to match the current summation and power-batched APIs. The declarations `curveRetentionMinimum`, `curveRetentionMinimum_le`, `exists_curveRetentionMinimum`, `hybridCurveTail`, `hybridCurveRegular`, `hybridCurveAtDegree`, `hybridCurveOptimized`, `hybridCurveAtDegree_le_pair`, `hybridCurveAtDegree_le_optimized`, `exists_exceptional_firstOrder_regularCurveStages`, `exists_exceptional_firstOrder_hybridCurve_of_tail`, and `exists_exceptional_firstOrder_hybridCurve_optimized_of_tail` keep their names. The exception theorems use the height-free descent API and derive the coefficient-height bound from `Q`. No public source declarations were left out. The private characteristic helper was removed because `natCast_ne_zero_of_ringChar_eq_zero_or_lt` supplies the general result.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridTransfer.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridTransfer.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`HasOrdinaryTailTransfer` keeps its name and packages the order-zero exceptional-set guarantee using `ordinaryTailCharge` and the mapped-domain API. `exists_exceptional_firstOrder_hybrid_raw_of_tail` keeps its name and combines the ordinary tail with the regular first-order stages at a fixed split, bounding the exceptional set by `firstOrderExceptionCharge`; its coefficient degree is derived from `Q`. `exists_exceptional_firstOrder_hybrid_optimized_of_tail` keeps its name and drops `1 ≤ μ`, weakens the characteristic guard to `ringChar F = 0 ∨ D < ringChar F`, and gives the current optimized charge, ceiling, and closed-constant bounds.

The source `exists_exceptional_firstOrder_regularStages` is covered by the existing more general `exists_exceptional_firstOrder_regularCurveStages`; `exists_hybridERaw_eq_hybridERawAtDegree` by `exists_curveRetentionMinimum`; `hybridERawAtDegree_le_hybridEOptimizedRaw` by `HiddenDerivative.minFirstOrderExceptionCharge_le_maxMin`; and `regularSymbolicCurveMCADerivativeBoundTwo_eq_hybrid_stage` by `regularPowerBatchedDerivativeCappedBoundTwo_eq_hybridCurveStage`. `ringChar_eq_of_injective_fieldHom` remains a local proof step in the existing generalized regular-stage theorem, with no consumer needing a separate public helper.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/LowRateSemantics.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/LowRateSemantics.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_lowRateFiniteLengthFirstOrder_symbolicCertificate`, `lowRate_closePolynomialSet_finite_and_card_le_finiteLength`, `lowRate_closePolynomialSet_finite_and_card_le_inv_eta`, `lowRateFiniteLengthJetDegree_pos`, `lowRate_finiteLength_rate_bounds`, and `lowRate_finiteLength_mcaError_le` keep their names and drop unused `rho < 1`. The list and rate conclusions and the rate theorem's quantifier order are unchanged. The finite-field MCA error theorem adds `[SampleableType F]` for the current probability API. The positive-cap theorem retains the algebraic-closure parameter used for squarefree descent.

`lowRateHybridEnvelopeConstant` keeps its name. `lowRateFiniteLengthMCAParameterConstant` → `lowRateFiniteLengthMcaParameterConstant` and `one_le_lowRateFiniteLengthMCAParameterConstant` → `one_le_lowRateFiniteLengthMcaParameterConstant` use ArkLib capitalization. `lowRate_hybridTheta_le_parameterConstant` → `lowRate_agreementIncidenceRatio_le_parameterConstant` follows the current incidence-ratio API and drops unused `rho < 1`.

`exists_exceptional_lowRateFiniteLengthMCA` → `exists_exceptional_lowRateFiniteLengthMca`, `exists_exceptional_lowRateFiniteLengthMCA_inv_eta` → `exists_exceptional_lowRateFiniteLengthMca_inv_eta`, `lowRate_finiteLength_completeList_and_exceptionalMCA` → `lowRate_finiteLength_completeList_and_exceptionalMca`, and `lowRate_finiteLength_completeList_and_exceptionalMCA_inv_eta` → `lowRate_finiteLength_completeList_and_exceptionalMca_inv_eta`. These keep their conclusions and drop unused `rho < 1`.

The public `lowRate_closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one` and `exists_exceptional_lowRateFiniteLengthMCA_one` were not ported. Both only fixed the envelope constant for generic theorems, and their sole consumer was the low-rate facade. It instead uses `closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one` with `C := lowRateFiniteLengthMcaParameterConstant rho` and `one_le_lowRateFiniteLengthMcaParameterConstant rho`, or `exists_exceptional_exactLineMca_one` with `square_le_finiteLengthMcaExceptionBudget`. The private `lowRate_specialized_weightedTotalDegree_map_le`, `lowRate_specialized_degreeOf_map_le`, and `lowRate_line_degreeOf_extendSymbolicCoefficients_le` are covered by existing jet-degree map lemmas.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/OrdinaryTail.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/OrdinaryTail.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`FirstOrderHybridDescent.hasOrdinaryTailTransfer` keeps its name. It proves that for every first-order hybrid descent of a symbolic equation `Q`, the order-zero tail satisfies `HasOrdinaryTailTransfer`, with coefficient height `coeffNatDegree Q` and charge `ordinaryTailCharge` at the residual jet budget `μ - e`. The proof splits on the budget: a positive budget uses `exists_exceptional_ordinaryEquation`, and a zero budget uses `PolynomialDifferential.exists_exceptional_jet_independent_content`.

Adapted to the height-free descent `FirstOrderHybridDescent Q μ M`. The height parameter is removed and fixed to `coeffNatDegree Q`. `Q` is implicit because the descent determines it. The theorem takes arbitrary `[DecidableEq F] [DecidableEq E]` instances instead of the source's `open Classical in` statement, and replaces them internally by the classical ones via `Subsingleton.elim`. The source's `hybridOrdinaryRaw` and `hybridTheta` become `ordinaryTailCharge` and `agreementIncidenceRatio`. The tail premise of the raw and optimized first-order hybrid transfer theorems now follows from `1 ≤ D < A ≤ n` alone.

`FirstOrderHybridDescent.tail_rootDegree_le` keeps its name but is placed in `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/HybridAgreementCounting.lean`, the owner of `FirstOrderHybridDescent`, and is listed in that module's `## Main statements`. The statement uses `jetDegree … 0`, which is definitionally `degreeOf (some 0)`, and the proof uses `jetDegree_le_total`, `JetPrefixPresentation.jetTotalDegree_equation` and `stage_jetTotalDegree_le`.

The source's coefficient-height induction through iterated jet derivatives is replaced by the new general lemma `MvPolynomial.CoeffNatDegreeLE.iterate_pderiv` in `ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean`. It also replaces an identical inline induction in `exists_exceptional_firstOrder_regularCurveStages` in `HybridCurveTransfer.lean`.

Not ported: `FirstOrderHybridDescent.tail_challengeHeight_le`, because the descent has no height field; the height bound comes from `CoeffNatDegreeLE.iterate_pderiv` and `JetPrefixPresentation.natDegree_coeff_equation_le`. `exists_exceptional_ordinaryContent` is not ported because `PolynomialDifferential.exists_exceptional_jet_independent_content` is used directly.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Profile.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Sharp.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, in namespace `ReedSolomon` instead of `ReedSolomon.CurveCertificate`:

- `squarefreeSharpCurveEnvelope` keeps its name and is now `ℝ`-valued, defined as the sharp charge at `L₀ = D + 1`. `ordinaryUnifiedPowerFactorAt_succ_eq` shows it equals the source's `(n - D)/(A - D)` expression whenever `D + 1 ≤ A ≤ n`.
- `squarefreeSharpOptimizedCurveEnvelope` keeps its name and is now `ℝ`-valued instead of `ℚ`.
- `squarefreeSharpOptimizedCurveEnvelope_le_fixed` keeps its name and drops `A ≤ n`.
- `exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized` → `exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized`. Drops `k < n` and takes `[DecidableEq F]` instead of `open Classical in`.
- Not ported: `exists_exceptional_exact_powerAgreement_squarefree_sharp` (fixed threshold) is covered by the optimized profile theorem plus `squarefreeSharpOptimizedCurveEnvelope_le_fixed`, and `exists_exceptional_exact_powerAgreement_squarefree_sharp_le` is a `hcard.trans hbound` wrapper.
## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/RateBounds.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/RateBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`automaticFirstOrder_rate_bounds` and `automaticFirstOrder_rate_mcaError_le` keep their names. `automaticLambdaBoundConstant` was renamed `automaticListBoundConstant`. `automaticFirstOrder_rate_bounds` is proved directly from main's `automaticFirstOrder_closePolynomialSet_finite_and_card_le`, `exists_automaticFirstOrder_hybridEquation_base` and `automaticClosedListAndExceptionBounds`. `automaticFirstOrder_rate_mcaError_le` adds `[SampleableType F]`. The source's `automaticFirstOrder_rate_constants_pos`, a conjunction, was split into `automaticListBoundConstant_pos` and `automaticExceptionBoundConstant_pos` and moved to `HiddenDerivative/Parameters/FirstOrder/AutomaticBounds.lean`, the owner of the constants.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Certificates.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CertificateList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`firstOrder_finite_agreement_solutions_card_le_squarefree` keeps its name and is generalized to direct degree and agreement conditions, dropping redundant `k ≤ n` and `0 < M` hypotheses. The module applies the shared `firstOrderSymbolicCertificate_specialization_at_zero` API, which specializes a symbolic certificate at zero challenge and provides its nonzero equation, jet-degree bounds, and agreement-solution soundness for both squarefree and tight list bounds.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CurveMCA.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CurveMCA.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `retainedOrdinaryMCARaw` to `retainedOrdinaryCurveAgreementCharge`, `retainedSquarefreeCurveMCARaw` to `retainedSquarefreeCurveAgreementCharge`, `HasRetainedOrdinaryCurveTransfer` to `HasRetainedOrdinaryCurveAgreementTransfer`, and `exists_exceptional_retainedSquarefreeCurveMCA_of_tail` to `exists_exceptional_retainedSquarefreeCurveAgreement_of_tail`. The exceptional-set theorem uses the current power-batched derivative-capped API, regular Taylor exponent, coefficient-height API, and power-agreement API; its degree-one case uses the identity-pair result. The source `hybridTau` and `hybridTheta` are represented by `regularTaylorExponent` and `agreementIncidenceRatio`.

Added `PolynomialDifferential.positiveCurveEquation_coeffNatDegreeLE_of_input` in the existing `PolynomialDifferential.RetainedCurve` owner. It generalizes the retained positive equation's coefficient-height bound to conclude it stays within the input equation's height. No public source declaration was omitted. The private characteristic helper is replaced by `natCast_ne_zero_of_ringChar_eq_zero_or_lt`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CurveUnified.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`hasRetainedOrdinaryCurveTransfer_of_unified` → `hasRetainedOrdinaryCurveAgreementTransfer_singularCurveEquation`, dropping `Q ≠ 0` and weakening the characteristic guard from `max D M < ringChar F` to `M < ringChar F`. `exists_exceptional_retainedSquarefreeCurveMCA_unified` → `exists_exceptional_retainedSquarefreeCurveAgreement`, unchanged mathematically. `ordinaryUnifiedPowerFactorRaw_le_retainedOrdinaryMCARaw` is replaced by `ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw` in `Ordinary/FactorBudget.lean`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Certificate.lean`: `exists_extensionExceptional_retainedSquarefreeCurveMCA_of_certificate` → `exists_extensionExceptional_retainedSquarefreeCurveAgreement_of_certificate`, unchanged. `exists_baseExceptional_retainedSquarefreeCurveMCA_of_certificate` → `exists_baseExceptional_retainedSquarefreeCurveAgreement_of_certificate`, dropping the `[DecidableEq E]` argument that its statement does not use. The `_of_tail` variants of both are not ported because the tail premise is always discharged by `hasRetainedOrdinaryCurveAgreementTransfer_singularCurveEquation` and nothing else in the source uses them. The private helper `degreeOf_extendSymbolicCoefficients_le` is covered by main's `jetDegree_map_le`. `family` is not a declaration of this source file.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CurveBounds.lean`: `retainedSquarefreeLineMCAEnvelope` → `retainedSquarefreeLineAgreementEnvelope`, unchanged. `retainedSquarefreeCurveMCARaw_balanced_line_le` → `retainedSquarefreeCurveAgreementCharge_balancedSplit_le`, unchanged.

The file now also imports `Ordinary.Equation`, `CurveCertificate` and `HybridCurveTransfer`, the last for `regularPowerBatchedDerivativeCappedBoundTwo_eq_hybridCurveStage`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/LineCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` and extended with the shared certificate and union lemmas:

- `exists_exceptional_retainedSquarefreeCurveAgreement_of_singularTail` is new. It generalizes `exists_exceptional_retainedSquarefreeCurveAgreement_of_tail` to an arbitrary tail bound `tailBound : ℝ`; its body is the old `_of_tail` proof, and `_of_tail` is now a one-line instance. It replaces the duplicated regular-plus-tail union proofs in the source's sharp theorems.
- `FirstOrderCurveCertificate.map_Q_ne_zero`, `map_Q_specialization_eq_zero`, `jetTotalDegree_map_Q_le`, `degreeOf_map_Q_le` and `exactPowerAgreement_of_map_Q` are new. They factor out the certificate-to-equation step (nonvanishing, degree caps, root soundness and the `k - 1 + 1 = k` recovery transfer), which the curve certificate theorem did inline and the source repeated in each `_of_certificate` theorem.
- `exists_extensionExceptional_retainedSquarefreeLineMCA_of_certificate` → `exists_extensionExceptional_retainedSquarefreeLineAgreement_of_certificate`, and `exists_baseExceptional_retainedSquarefreeLineMCA_of_certificate` → `exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate`. Renames: `hybridTheta` → `agreementIncidenceRatio`, `retainedSquarefreeLineMCAEnvelope` → `retainedSquarefreeLineAgreementEnvelope`, `mappedDomain domain iota` → `domain.trans ⟨iota, _⟩`. The extension theorem concludes `HasExactCorrelatedPair domain f g iota k z P` instead of `HasExactPowerAgreement domain ![f, g] iota k z P`; the two are equivalent through `exactCorrelatedPair_of_powerAgreement_one` and `powerAgreement_one_of_exactCorrelatedPair`. It specializes the curve certificate theorem at `ell = 1` and `L = balancedSplit (k - 1) A`, followed by `retainedSquarefreeCurveAgreementCharge_balancedSplit_le`. The base theorem specializes the base-field curve certificate theorem instead of re-running the descent inline.
- Not ported: `exists_extensionExceptional_retainedSquarefreeLineMCA_of_certificate_of_tail` and `exists_baseExceptional_retainedSquarefreeLineMCA_of_certificate_of_tail`, because the tail is always discharged by `hasRetainedOrdinaryCurveAgreementTransfer_singularCurveEquation`, as slice 82 decided for the curve `_of_tail` certificate theorems. The private helpers `line_degreeOf_extendSymbolicCoefficients_le` and `hasRetainedOrdinaryLineTransfer_of_certificate` are covered by `jetDegree_map_le` and the curve theorem.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Factorwise.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/FactorwiseList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`FixedWordSingularTail`, `finite_factorwise_agreement_solutions_card_le_actual`, and `finite_factorwise_agreement_solutions_card_le` keep their names. The actual-degree theorem no longer requires the unused `hQ`, `hjet`, and `hderiv` assumptions. The module was renamed from `FactorwiseList` to `Factorwise` so its generated root import stays within 100 characters. The source wrappers `positiveEquation` and `rootFirst` are not introduced; the existing `radicalPrimPart` API supplies the positive-degree factor product.

The source's private `positiveRootProduct_eq_one_of_rootDegree_eq_zero'` argument is covered by the public `MvPolynomial.radicalPrimPart_eq_one_of_degreeOf_eq_zero`, generalized to any selected coordinate in `ArkLib/ToMathlib/MvPolynomial/RadicalSplit.lean`. The regular Taylor estimate `finite_regular_agreement_solutions_card_le_regularTaylor` combines the existing identity-pair and derivative-capped estimates in `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/AgreementCounting.lean`; the hybrid counting proof also uses it. No public declaration from the unit was omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/RetainedTail.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/RetainedTail.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The retained-tail API keeps the challenge as a polynomial coordinate and constructs the retained content-times-derivative-resultant equation. The unchanged-role declarations are `flattenedContentCoefficient`, `flattenedSingularPolynomial`, `remainingCoordinateEquiv`, `remainingCoordinateEquiv_natDegree`, `retainedContentAsPolynomial`, `retainedPositiveAsPolynomial`, `flattenedContentCoefficient_ne_zero`, `retainedPositiveAsPolynomial_natDegree`, `remainingCoordinateEquiv_flattenedSingularPolynomial`, `retainedContent_yZeroDegree_le`, `retainedPositive_yZeroCoefficientTriangle`, `flattenedSingularPolynomial_yZeroDegree_le`, `degreeOf_flattenedContentCoefficient_le`, `retainedPositive_degreeX_le`, `flattenedSingularPolynomial_challengeDegree_le`, `singularCoordinateEquiv`, `singularCurveEquation`, `ordinaryFlatten_singularCurveEquation`, `singularCurveEquation_degree_le`, `singularCurveEquation_ne_zero`, `retainedSpecializationHom`, `retainedRootSpecializationHom`, `retainedRootSpecializationHom_eq_eval_rootPolynomial`, `retainedRootSpecializationHom_flattenedContent`, `retainedRootSpecializationHom_flattenedRootFirst`, `positiveCurveEquation_specialization_eq`, `positiveCurveSeparant_specialization_eq`, `retainedSpecializationHom_flattenedSingularPolynomial`, and `singularCurveEquation_routes_nonregular`.

`flattenedContent_add_positive_jetWeight_le` is now `retainedContent_add_positiveJetDegree_le`, using canonical jet degree and removing the unnecessary nonzero-input hypothesis. `singularCurveEquation_challengeHeightLE` is now `singularCurveEquation_coeffNatDegreeLE`. `flattenedRootFirst_positiveCurveEquation` and `flattenedRootFirst_separant_positiveCurveEquation` are now `challengeRetainingRootFirst_positiveCurveEquation` and `challengeRetainingRootFirst_separant_positiveCurveEquation`, respectively. The map from flattened root-first coordinates is exposed as `challengeRetainingRootFirst_fromFlattenedRootFirst`, and its derivative law is exposed for `Y₁` as `challengeRetainingRootFirst_pderiv`.

The root-first multiplication identity, repeated in the source retained-tail module, is shared from the retained-curve owner as `jetTotalDegree_fromFlattenedRootFirst_mul`. The generic coefficient-degree bound is owned by `OptionWeightedDegree` as `degreeOf_coeff_optionEquivLeft_add_le_weight`; it generalizes the coefficient-degree argument to `Option σ` weights with the distinguished and selected coordinates positively weighted. The coefficient-variable derivative transport is owned by `PolynomialCoefficients` as `optionEquivRight_symm_pderiv` and generalizes to arbitrary variable types and commutative semirings. The arbitrary-coordinate `flattenChallenge_pderiv` law is not exposed; the needed `Y₁` case lives in the retained-curve owner. `flattenedSingularPolynomial_map_eq_zero_of_content_or_commonRoot` is generalized from domain targets to commutative-ring targets. `flattenedPositiveRootProduct_eq_one_of_rootDegree_eq_zero` is covered by the existing `MvPolynomial.radicalPrimPart_eq_one_of_degreeOf_eq_zero`. `retainedRootJetWeight` remains private coordinate-view bookkeeping, `flattened_content_add_positive_challengeDegree_le` remains a private helper, and the private `flattenChallenge_specialization` helper is inlined into `retainedRootSpecializationHom_flattenedRootFirst`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/SharpCurveMCA.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Sharp.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

- `retainedSquarefreeOrdinaryCurveMCAAt` → `retainedSquarefreeOrdinaryCurveChargeAt`, `retainedSquarefreeCurveMCASharpRawAt` → `retainedSquarefreeCurveSharpChargeAt`, and `retainedSquarefreeCurveMCASharpOptimizedRaw` → `retainedSquarefreeCurveSharpOptimizedCharge`. All three are now `ℝ`-valued (the cast of the `ℚ` free-retention charge), like main's curve charges. The ordinary part of the optimized charge is `curveRetentionMinimum D A (retainedSquarefreeOrdinaryCurveChargeAt n D ell · A B M H)`.
- `retainedSquarefreeCurveMCASharpOptimizedRaw_le_fixed` → `retainedSquarefreeCurveSharpOptimizedCharge_le_chargeAt`. Generalized from `L₀ = D + 1` to any admissible `D < L₀ ≤ A`, and drops `A ≤ n`.
- `exists_exceptional_retainedSquarefreeCurveMCA_sharp_at` → `exists_exceptional_retainedSquarefreeCurveAgreement_sharpAt`. Drops `D + 2 ≤ n` and takes `[DecidableEq F] [DecidableEq E]` instead of `open Classical in`.
- `exists_exceptional_retainedSquarefreeCurveMCA_sharp_optimized` → `exists_exceptional_retainedSquarefreeCurveAgreement_sharpOptimized`. Drops `D + 2 ≤ n`.
- `exists_extensionExceptional_retainedSquarefreeCurveMCA_sharp_optimized_of_certificate` → `exists_extensionExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate`, and `exists_baseExceptional_retainedSquarefreeCurveMCA_sharp_optimized_of_certificate` → `exists_baseExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate`. Both drop `k < n`.
- Not ported: `retainedSquarefreeOrdinaryCurveMinimum`, `retainedSquarefreeOrdinaryCurveMinimum_le` and `exists_retainedSquarefreeOrdinaryCurveMinimum`, because main's `curveRetentionMinimum`, `curveRetentionMinimum_le` and `exists_curveRetentionMinimum` cover them. The fixed-threshold (`L₀ = D + 1`) forms `retainedSquarefreeOrdinaryCurveMCARaw`, `retainedSquarefreeCurveMCASharpRaw`, `retainedSquarefreeCurveMCASharpRawAt_succ_eq`, `exists_exceptional_retainedSquarefreeCurveMCA_sharp` and `exists_{extension,base}Exceptional_retainedSquarefreeCurveMCA_sharp_of_certificate` are each an instance of the `_sharpAt` or charge-at-`D + 1` forms, one `ordinaryUnifiedPowerFactorAt_succ_eq` rewrite away, or the optimized theorem followed by `retainedSquarefreeCurveSharpOptimizedCharge_le_chargeAt`; they would be wrappers. The private helpers `natCast_ne_zero_of_sharp_char_guard`, `exists_exceptional_positiveCurveEquation_regular` and `degreeOf_extendSymbolicCoefficients_le` are covered by the regular branch inside `_of_singularTail` and by `jetDegree_map_le`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/TailBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/TailBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`rootFirst` and `fromRootFirst` became `firstOrderRootCoordinates` and `fromFirstOrderRootCoordinates`; the coordinate round trips and the root-degree identity were added. `fromRootFirst_rootJetWeight` became the more general `fromFirstOrderRootCoordinates_weightedTotalDegree`, stated using `jetTotalDegree`. `positiveEquation` became `positiveJetFactor`, the root-coordinate radical positive factor. New bounds cover its total jet degree and `Y₁` degree. The specialization theorems `rootFirst_separant_positiveEquation`, `positiveEquation_specialization_eq`, and `positiveSeparant_specialization_eq` became `firstOrderRootCoordinates_separant_positiveJetFactor`, `positiveJetFactor_specialization_eq`, and `positiveJetFactor_separant_specialization_eq`.

The singular equation and polynomial declarations retain their names except for `singularEquation_ne_zero`, which no longer requires a nonzero-input premise. The construction uses radical content and the derivative resultant of the positive-jet factor, proves the equation nonzero and within the ordinary-degree envelope, and routes content roots and singular positive-factor roots. `finite_squarefree_agreement_solutions_card_le` specializes the generic capped count and drops unused positivity premises. The order-zero presentation declarations were moved to `PolynomialDifferential` in `ArkLib/Data/Polynomial/Differential/OrderZeroPresentation.lean` and generalized there.

`positiveResultant_ne_zero` is covered by `Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial`; `positiveRootProduct_eq_one_of_rootDegree_eq_zero` is covered by `MvPolynomial.radicalPrimPart_eq_one_of_degreeOf_eq_zero`. The `positiveRootProduct_rootJetWeight` wrapper is unnecessary because `fromFirstOrderRootCoordinates_weightedTotalDegree` provides the general identity. `singularAsPolynomial_eval` is covered by `remainingSpecializationHom_eq_eval` and has no separate wrapper. The factorwise additions are in `Factorwise.lean`: they introduce `FixedWordRegularTail` and actual-degree and capped counts for a chosen regular equation, while retaining the radical-part APIs as a specialization.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/UniformLineMca.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/UniformLineMCA.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_uniformFirstOrder_squarefree_lineMCA_of_two_le` → `exists_uniformFirstOrder_lineMca_of_two_le`. The statement is mathematically unchanged, and the proof is now a specialization of `FirstOrderSymbolicCertificate.exists_exceptional_hybrid` plus `uniformFirstOrderMca_optimizedExceptionCharge_le_ceiling`. The proof uses no squarefree API, so `squarefree` was dropped from the name and `MCA` became `Mca`, following main's `uniformFirstOrderMca_*`. The `_of_two_le` suffix is kept because the source's later `Capacity/UniformFirstOrder.lean` has a general `exists_uniformFirstOrder_lineMCA`. The module moved out of `Squarefree/` because it uses only the uniform `(12, 4, 23, 276)` parameters, which main already moved to `HiddenDerivative/Parameters/FirstOrder/UniformMca.lean`, and the old path is 100 characters. The private `squarefreeJetWeight_map_eq` is not ported because main has `jetTotalDegree_map_eq`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusAdmissibility.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusAdmissibility.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Ported `IsAdmissibleFrobeniusPair`, its projections `degree_left`, `degree_right`, `initial`, `regular`, `sparse`, and `sample`, `exists_admissibleFrobeniusPair_of_symbolic_prime_sample`, `IsAdmissibleFrobeniusPair.specialize`, and `IsAdmissibleFrobeniusPair.eq_of_initialGraph_eq` without renaming. Generalized them from `Fin n` to arbitrary embedded index types `ι`. The sample condition groups sample values and Frobenius root equations, and root equations are required only on the interpolation sample. No other public source declaration from this file was left out.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/GraphCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`admissibleFrobeniusPairs_card_le_degreeOf` keeps its name. It bounds the cardinality of any finite family of admissible Frobenius pairs by the degree of the nonzero joint initial-jet equation in the graph coordinate. The theorem generalizes the source index type from `Fin n` to an arbitrary embedded type `ι`; a global Frobenius-root premise is unnecessary because reconstruction uniqueness uses roots on each admissible sample. It reuses the existing joint initial-jet equation and generic polynomial graph root count. No source declarations were left unported.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusComponentRecognition.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`frobeniusInitialGraph` keeps its name and is generalized from a `Fin 1` jet-coordinate function to `Option (Fin 1)`, with the challenge coordinate mapped to `X`, and from fields to commutative semirings. `exists_frobeniusGraph_of_symbolic_prime_sample` keeps its name and is generalized from `Fin n` to an arbitrary embedded type `ι`; Frobenius roots are required only at sampled indices. The theorem is derived from the two-term case of `exists_frobeniusPowerGraph_of_symbolic_prime_sample`.

`symbolicSourceFrobeniusAgreement` is not added because the existing `jointTaylorAgreementEquation` in `PolynomialDifferential.TaylorChartAlgebra` covers it. An acceptance case in `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` recognizes the zero pair on a positive-dimensional prime component from a one-point sparse sample cut.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusIncidence.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/Incidence.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `sourceFrobeniusSparseCuts` to `frobeniusSparseTaylorCuts` and `sourceFrobeniusGraphLocus` to `admissibleFrobeniusPairGraphLocus`; their content is unchanged. Renamed `principalOpen_subset_sourceFrobeniusGraphLocus` to `principalOpen_subset_admissibleFrobeniusPairGraphLocus`, expressing cut counts with `Set.ncard`. Renamed `finite_sourceFrobenius_points_off_graphs_card_le` to `finite_frobeniusChartPoints_off_admissiblePairGraphs_card_le`. This finite bound uses the current coefficient-height and agreement-count APIs and omits the unnecessary premise `A ≤ n`.

Did not port `symbolicSourceFrobeniusAgreement_mem_restrictBidegree`: the existing `jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent` covers it, and the finite theorem uses that result with local degree conversions, so no public specialization was added. The current consolidated suite retains a principal-open theorem instance on the shared component fixture; the earlier finite-incidence acceptance case is historical.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusRetainedFamily.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/RetainedFamily.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`frobeniusRetainedPairFamily`, `mem_frobeniusRetainedPairFamily_iff`, `frobeniusRetainedPairFamily_card_le`, and `exists_exceptional_frobeniusRetainedPairFamily` retain their names. They are generalized from `Fin n` to any finite embedded coordinate type. The retained family is expressed as a filter of the existing correlated-pair family. The cardinality bound uses the joint initial equation; a global root premise is unnecessary because root equations are included in each admissible pair's sample witness. The exceptional-set theorem specializes the existing exceptional-set theorem for correlated pairs.

Historical acceptance cases in `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` exhibited a nonempty retained family and checked its graph-coordinate degree bound, then exhibited a retained pair and an exceptional set of size zero for a one-point domain with a one-point sample. The current consolidated suite has no retained-family example. No public source declarations were omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Certificate.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_johnsonMCA` (Certificate) and `exists_exceptional_johnson_lineMCA_allChar` (Agreement) were the same statement with the arguments in a different order. They become `ReedSolomon.exists_johnson_line_exactCorrelatedPair`. The unused hypothesis `johnsonAgreement n D eta ≤ 1` is dropped, since main's `exists_johnson_symbolic_certificate` no longer needs it. `johnsonE0` is renamed `johnsonExceptionCount`. `exists_exceptional_johnson_lineMCA_at_ceil` becomes `exists_johnson_line_exactCorrelatedPair_ceil`, unchanged apart from making `n D eta` implicit and reordering the arguments.

The source's private `exists_uniformCapacity_lineMCA_johnson` (in `Capacity/MathematicalUniformRate`) becomes the public `exists_johnson_line_exactCorrelatedPair_of_gap`, because it is a general Johnson statement and the line theorem uses it. Its hypotheses `⌈4ν/δ²⌉₊ ≤ n` and `k ≤ ν` (with `ν` the mathematical jet cap) are generalized to the parameter-free `4 (k - 1) ≤ δ² n`, and the `DecidableEq F` argument is dropped.

Not ported: `exists_exceptional_johnson_lineMCA_allChar` as a separate declaration, because it would duplicate `exists_johnson_line_exactCorrelatedPair`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`johnson_mcaError_le` (Probability) and `johnson_lineMCA_probability` (Agreement) become one theorem, `ReedSolomon.mcaError_affineLine_johnson_le`. It is unchanged except that it adds `[SampleableType F]`, which main's `mcaError` requires. The module is kept separate from `Johnson/Agreement` so the capacity module does not import `LineToAffine`.

Not ported: `johnson_lineMCA_probability` as a separate declaration, because it has the same statement as `mcaError_affineLine_johnson_le`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/BaseEquation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Equations/BaseEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_ordinaryEquation_base` keeps its name and mathematical content. For a nonzero ordinary equation over an arbitrary field, it gives one finite exceptional set of challenges, of size at most `ordinaryFactorRaw ((n - D) / (A - D)) n D mu h`, outside which every base-field root of degree at most `D` that agrees with the line on at least `A` points has an exact correlated-pair witness. The height premise is `CoeffNatDegreeLE Q h` instead of the source's `ChallengeHeightLE Q h`, matching main's `exists_exceptional_ordinaryEquation`. The theorem takes `[DecidableEq F]` as an instance argument instead of the source's `open Classical in`, so `polynomialAgreementSet` and `HasExactCorrelatedPair` in the conclusion work with any decidable-equality instance. The proof uses `convert` to match the classical instances that come from `exists_exceptional_ordinaryEquation`. Nothing was left unported: the source file has one declaration. It is a separate module rather than part of `Ordinary/Equation.lean`, which would otherwise need `EquationDescent` and `AlgebraicClosure` as extra imports.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

No new declarations. `exists_exceptional_ordinaryEquation_base`, which came from main, keeps its statement and is now the `ℓ = 1`, `L = D + 1` case of `exists_baseExceptional_ordinaryPowerEquation`. Its imports shrink to `Ordinary.Equation` plus a private `PowerToLine` import.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Equation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Equations/Equation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.exists_exceptional_ordinaryEquation` → `ReedSolomon.exists_exceptional_ordinaryEquation`. The theorem retains its mathematical content and replaces the `ChallengeHeightLE` premise with the equivalent `CoeffNatDegreeLE` coefficient-height premise. No declarations were omitted. The matching `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary.lean` acceptance case uses a reducible `Y₀²` equation, obtains an exceptional set of size at most two, and exhibits an outside challenge with an exact correlated-pair witness.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Equation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_ordinaryPowerEquation_freeRetention` → `exists_exceptional_ordinaryPowerEquation_unifiedAt`, renamed to match the `ordinaryUnifiedPowerFactorAt` charge. It drops the unused `D + 2 ≤ n` and `A ≤ n`. `exists_exceptional_ordinaryPowerEquation` keeps its name and statement apart from `CoeffNatDegreeLE` and the embedding-composition domain; its proof is now the `L = D + 1` specialization of `_unifiedAt` plus the charge comparison. `exists_exceptional_ordinaryEquation` is now the `ℓ = 1` case of it.

`exists_exceptional_ordinaryPowerEquation_base_freeRetention_allDegrees`, `_base_freeRetention`, `_base_zeroDegree` and `_base_unified` → `exists_baseExceptional_ordinaryPowerEquation`. It drops `D + 2 ≤ n` and `A ≤ n` and takes `[DecidableEq F]` instead of classical decidability. It charges root degree zero by its height.

Not ported: `exists_exceptional_ordinaryPowerEquation_unified` and `_unifiedAt_succ` (`L := D + 1` cases), `exists_exceptional_ordinaryPowerFactorAssembly_unifiedAt` and `_unified` (covered by main's `exists_exceptional_ordinaryUnifiedPowerFactorAssembly`), and `exists_exceptional_ordinaryPowerEquation_freeRetention_of_certificates` (the `ν = Unit` instance of `exists_geometricTransfer_exceptional`, with only its own acceptance test as a user; deferred pending a maintainer decision).

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/FactorAssembly.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Assembly.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_ordinaryPowerFactorAssembly` became `exists_exceptional_ordinaryCurveFactorAssembly`. Generalized it from the fixed `none` variable and field coefficients to an arbitrary selected variable and unique-factorization-domain coefficients, using the existing radical factor split and evaluator interface. The curve specialization shares a private charge-independent helper with the existing assembly variants. No declaration was omitted; source imports resolve to the existing `Ordinary.FactorAssembly` and `Ordinary.FactorBudget` modules.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/FactorBudget.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/FactorBudget.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `ordinaryFrobeniusPowerMixedDegree` to `ordinaryFrobeniusCurveMixedDegree` and generalized it with the polynomial curve degree `ell`. Renamed and generalized `ordinaryFrobeniusPowerMixedDegree_eq` and `ordinaryFrobeniusPowerMixedDegree_le` to give its exact form and coarse upper bound; the exact form also covers `b = 0`. Renamed `ordinaryPowerFactorRaw` to `ordinaryCurveFactorRaw`, `ordinaryFrobeniusPower_charge_le` to `ordinaryFrobeniusCurve_charge_le`, and `ordinaryPowerFactorRaw_le_mul` to `ordinaryCurveFactorRaw_le_line_mul`. `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary.lean` checks the exact and coarse degree bounds, the Frobenius curve charge, and the curve-to-line charge comparison at positive parameters.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Assembly.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ordinaryPowerFactorRaw_sum_le` became `ordinaryCurveFactorRaw_sum_le`. Added `ordinaryCurveFactorRaw_le_linear` and `ordinaryCurveFactorRaw_eq_linear` as the linear bound and equality used by the summation result. The line-charge linear, equality, and summation results specialize the polynomial-curve results at `ell = 1`. The source charge is already present as `ordinaryCurveFactorRaw`; its source import resolves to the existing `Ordinary.FactorBudget` module. The unused source argument `0 < ell` was omitted.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ordinaryFrobeniusPowerMixedDegree_le_unified` → `ordinaryFrobeniusCurveMixedDegree_le_unified`, following main's `ordinaryFrobeniusCurveMixedDegree`. The hypotheses `1 ≤ D`, `1 ≤ s` and `1 ≤ b` are dropped. `ordinaryFrobeniusPower_charge_le_unifiedAt` → `ordinaryFrobeniusCurve_charge_le_unifiedAt`, dropping `1 ≤ D` and `1 ≤ b`. `ordinaryFrobeniusPower_charge_le_unified` is not ported because it is the `L := D + 1` case of the `unifiedAt` theorem, via `ordinaryUnifiedPowerFactorRaw_eq_rawAt`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CurveUnified.lean`: `ordinaryUnifiedPowerFactorRaw_le_retainedOrdinaryMCARaw` → `ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw`. It is a comparison with the curve-factor charge and drops the hypothesis `1 ≤ B`. The singular-tail proof now goes through `exists_exceptional_ordinaryPowerEquation`, whose charge is exactly `retainedOrdinaryCurveAgreementCharge` at `b = B(2M+1)`, `h = H(2M+1)`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/IrreducibleEquation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Factors/IrreducibleEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Ported `exists_exceptional_irreducibleOrdinaryEquation` under the same name, using the current `CoeffNatDegreeLE` interface. The theorem gives a bounded exceptional set for sufficiently agreeing, low-degree solutions of an irreducible ordinary equation and an exact correlated-pair representation outside that set in every characteristic. Nothing was omitted. The acceptance case in `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary.lean` applies it to `Y₀` over `ℂ`, obtains an exceptional set of size at most one, and exhibits a point outside it with an exact correlated-pair witness.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Irreducible.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_irreducibleOrdinaryPowerEquation` → `exists_exceptional_irreducibleOrdinaryPowerEquation`. The theorem is mathematically unchanged and uses `CoeffNatDegreeLE`, `ordinaryCurveFactorRaw`, and the current exact-power-agreement interface. The existing two-message correlated-pair theorem now specializes this tuple theorem at `ℓ = 1`, using the power-batched word identity, the exact-agreement conversion, and equality of the curve and line charges. Nothing was deferred or left unported.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_irreducibleOrdinaryPowerEquation_unifiedAt`, with the same name, dropping the unused `A ≤ n`. The existing `exists_exceptional_irreducibleOrdinaryPowerEquation` keeps its statement and is now proved from it. `exists_exceptional_irreducibleOrdinaryPowerEquation_unified` is not ported for the same reason as the Frobenius factor version.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedAdmissibility.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/GraphAdmissibility.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The graph restriction, specialized jet, Taylor coefficient, admissibility structure and its fields, evaluation identities, and specialization theorem keep their names. `exists_admissibleChartTuple_of_symbolic_prime_agreements_of_exponent` is renamed to `exists_admissibleChartTuple_of_primeTaylorComponent_agreements`; its mathematical result is unchanged and uses the existing prime-component graph theorem and joint equations. The symbolic equation names are supplied by the existing joint Taylor-chart API. No public declarations from the source unit were left out.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedCertificate.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Certificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_exceptional_symbolicCurveMCA_sharp` to `Certificate.exists_exceptional_powerBatchedAgreement_sharp_of_exponent`. The theorem now uses the current certificate and power-batched APIs and charges each stage by its actual jet degree. The `eval₂_powerBatchedCoordinate_eq_powerBatchedWord` equality remains a private proof bridge because no public consumer needs a separate theorem for it.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedComponentAgreement.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ComponentAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`commonAgreement_of_curveCut_mem_prime_of_exponent` became `commonCurveAgreement_of_jointTaylorAgreementEquation_mem_prime`. It uses the current joint Taylor cut and applies to every constituent of an arbitrary power-batched tuple.

`exists_polynomialGraph_of_symbolic_prime_agreements_of_exponent` became `exists_polynomialGraph_of_primeTaylorComponent_agreements`. It handles any index set of size `L` with `k ≤ L`, chooses the interpolation sample internally, and returns the graph and ideal restriction facts.

`symbolicSourceCurveAgreement_eq_zero_iff_of_exponent` was not ported because `PolynomialDifferential.aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent` covers it generically. The current consolidated suite includes a compact positive-dimensional prime-component example constructing a degree-bounded tuple with a nonempty common-agreement set. The earlier separate constituent-agreement and two-entry tuple-extraction examples remain historical.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedComponentRecognition.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `exists_polynomialGraph_of_symbolic_prime_sample_of_exponent` to `exists_polynomialGraph_of_primeTaylorComponent`. It uses the destination joint Taylor cuts and recognizes a graph for tuples of arbitrary length. Added `powerBatchedJetGraphMap`. The result also proves ideal vanishing on the graph and nonvanishing of the restricted separant. The wrapper declarations `symbolicSourceCurveAgreement_of_exponent` and `symbolicSourceCurveAgreement` were not ported: their cut polynomial is `jointTaylorAgreementEquation`, and the default-exponent case follows by taking exponent `2 * K`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`frobeniusPowerInitialGraph`, `exists_frobeniusPowerGraph_of_symbolic_sample`, and `exists_frobeniusPowerGraph_of_symbolic_prime_sample` keep their names; `frobeniusPowerGraphMap` is new. The initial graph is generalized from fields to commutative semirings. Both recognition theorems are generalized from `Fin n` to any embedded index type and require Frobenius roots only on the sample. The prime-component result uses the current joint Taylor and `aeval` APIs to express its symbolic cuts and graph restrictions. The proof reuses `exists_frobeniusPowerGraph_polynomials_of_sample` for interpolation and sparse expansion.

`symbolicSourceFrobeniusPowerAgreement` was not ported because `jointTaylorAgreementEquation` in `TaylorChartAlgebra.lean` covers it without a wrapper. Historical acceptance cases gave a concrete symbolic chart example and a regular prime-component example; neither is in the current consolidated suite.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedDerivativeImage.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/DerivativeImage.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `finite_sourceCurve_points_off_tuples_card_le_derivativeCapped_of_exponent` to `finite_powerBatched_regular_points_off_graphs_card_le_derivativeCapped_of_exponent` and generalized it to the admissible-graph API, removing the unused `A ≤ n` premise. Renamed `regularSymbolicCurveMCADerivativeBoundTwo` to `regularPowerBatchedDerivativeCappedBoundTwo`; its mathematical bound is unchanged in the power-batched API. Renamed `finite_sourceCurve_bad_challenges_card_le_derivativeCapped_of_exponent`, `finite_regularSymbolicCurveBadChallenges_card_le_derivativeCapped_of_exponent`, and `exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent` to their `powerBatched` / `regularPowerBatched` names and removed the unused `0 < k` premise from the finite bound and the propagated premise from the regular-family bound and exceptional-set result. Renamed the identity-pair finite challenge bound, regular-family bound, and exceptional-set result to `finite_powerBatchedBadChallenges_card_le_identityPair`, `finite_regularPowerBatchedBadChallenges_card_le_identityPair`, and `exists_exceptional_regularPowerBatchedAgreement_identityPair`; these mathematical conclusions are unchanged in the current API.

The four `_specialize` evaluation bridges remain private and reuse the existing `TaylorChartAlgebra` lemmas. The shared fixed-center tuple-bound theorem was extracted into the sharp power-batched agreement module for use by both sharp and derivative-capped challenge bounds.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedExceptionalChallenges.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ExceptionalChallenges.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `finite_sourceCurve_bad_challenges_card_le` to `finite_powerBatchedChart_badChallenges_card_le`. The theorem uses the destination chart and height APIs and bounds finite bad-challenge sets using off-graph incidence and exact-agreement exceptions. No declarations from this source file were omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedFrobeniusFamily.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedFrobeniusFamily.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`frobeniusRetainedPowerTupleFamily` → `frobeniusRetainedPowerTupleFamily`,
`mem_frobeniusRetainedPowerTupleFamily_iff` → `mem_frobeniusRetainedPowerTupleFamily_iff`,
`frobeniusRetainedPowerTupleFamily_card_le` → `frobeniusRetainedPowerTupleFamily_card_le`, and
`exists_exceptional_frobeniusRetainedPowerTupleFamily` →
`exists_exceptional_frobeniusRetainedPowerTupleFamily` keep their names. The retained-family
API and its bounds now accept any finite coordinate type instead of only `Fin n`. The
cardinality theorem uses `jointInitialJetEquation` for the current initial-equation API; the
exceptional-set theorem specializes the generic exact-power-agreement family bound.

No declarations from this source file were left out. The related source wrapper
`uniformExactPowerAgreement_descend` is covered by the existing
`uniformExactPowerAgreement_of_extension` theorem in `PowerAgreement`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedGeometricTransfer.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/GeometricTransfer.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`geometricTransferBound` keeps its name and budget, and uses `dimensionSensitiveIncidenceProduct` directly. `exists_geometricTransfer_exceptional` keeps its name, generalizes `Fin n` to any finite coordinate type, and removes unused algebraic-closure and parameter-bound hypotheses. `exists_geometricTransfer_baseField_semantic` keeps its name and generalizes `Fin n` to any finite coordinate type while preserving the exceptional-set bound.

`geometricTransferIncidenceProduct` and `geometricTransferIncidenceProduct_zero` were not ported because `dimensionSensitiveIncidenceProduct` covers them at degree one and its zero case. Source `ExtensionDescent` functionality is supplied by `HasExactPowerAgreement.descend` in `PowerAgreement.lean`. A historical acceptance case checked geometric transfer for a retained zero tuple; it is not in the current consolidated suite. The exact-line transfer case remains covered under `PowerToLine`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedGraphCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/GraphCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`admissibleChartTupleFamilyAtExponent`, `mem_admissibleChartTupleFamilyAtExponent_iff`, `admissibleChartTuples_card_le_of_exponent`, and `admissibleChartTupleFamilyAtExponent_card_le` retain their names and statements. The family characterization and count use the generalized tuple-family API.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedIncidence.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Incidence.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.sourceCurveTupleLocus` and `ReedSolomon.sourceCurveTupleLocus_of_exponent` become `ReedSolomon.admissibleChartTupleGraphLocus`. `ReedSolomon.principalOpen_subset_sourceCurveTupleLocus_of_exponent` becomes `ReedSolomon.principalOpen_subset_admissibleChartTupleGraphLocus`, and `ReedSolomon.finite_sourceCurve_points_off_tuples_card_le` becomes `ReedSolomon.finite_admissibleChartTupleIncidence_off_graphs`, under the current Taylor-chart and graph-locus API. The high-cut helper predicates and their membership wrappers are not ported because the statements use explicit high-cut predicates directly. `sourceCurveTupleLocus_of_exponent_two_mul_eq` is not ported because the finite incidence theorem uses exponent `2 * K` directly.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedPointRecognition.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/PointRecognition.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`commonCurveAgreementSet_map` and `exists_exceptional_powerBatched_extension` keep their names; both are generalized from `Fin n` to any finite coordinate type, and the exceptional bound uses `Fintype.card α`. `powerBatchedJetGraph` and `polynomialJet_powerBatched` keep their names and statements. `exists_polynomialGraph_of_symbolic_sample_of_exponent` keeps its name and is generalized to an arbitrary embedded coordinate type without requiring it to be finite. Its regularity, high-cut, and agreement premises use the field-valued Taylor-chart API after specialization at each challenge.

No declarations from the source were left out. The intermediate over-algebra bridge statements are not duplicated; the main theorem specializes `ReedSolomon.exists_polynomialGraph_of_sample` from `PowerAgreement` and uses the available field-valued Taylor-chart results. The source import `TaylorChart.PointRecognition` is unavailable in this checkout, so its helper bridge layer was replaced by that API.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ExceptionalSet.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_exactPowerAgreement` and `exists_exceptional_exactPowerAgreement_family` keep their names and are generalized from `Fin n` coordinates to any finite coordinate type. The family result delegates to `exists_exceptional_powerBatched_family` on the mapped polynomial family and uses each original tuple as its exact-agreement witness.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedPointRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.exists_frobeniusPowerGraph_polynomials_of_sample` keeps its name. It is generalized from `Fin n` to any embedded coordinate type `α`, and its root condition is restricted to the sample.

Did not port `exists_exceptional_frobeniusPower_challenges_of_sample` because `ReedSolomon.exists_exceptional_exactPowerAgreement` in `PowerBatchedPointRecognition` already covers it: sample agreement proves the required common-agreement lower bound, and specialization to `Fin n` gives the source bound.

The singleton-sample characteristic-two acceptance case in `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` checked the zero sparse Frobenius pullback and both recognition conclusions; it is historical. The current suite retains the separate symbolic sample case over `ZMod 3` with a nonzero second word component.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/GraphLineComponent.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_graphLine_pair_of_symbolic_sample_of_exponent` is specialized as `exists_graphLine_pair_of_joint_taylor_chart` for flattened challenge and initial-jet coordinates. `exists_graphLine_pair_of_symbolic_prime_sample_of_exponent` is renamed and reformulated as `exists_graphLine_pair_of_regular_component`; it gives a joint-coordinate conclusion parametrized by the affine-pair curve on the regular locus of a positive-dimensional component. `exists_graphLine_pair_of_symbolic_prime_sample` is not added as a separate default-exponent wrapper because the component theorem accepts any sufficient exponent.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ComponentAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`symbolicSourceAgreement_eq_zero_iff_of_exponent` and `symbolicSourceAgreement_eq_zero_iff` → `aeval_jointTaylorAgreementEquation_eq_zero_iff`; the two forms are combined into a theorem for every sufficient exponent `τ`, using the joint chart API. `commonAgreement_of_symbolicSourceAgreement_mem_prime_of_exponent` and `commonAgreement_of_symbolicSourceAgreement_mem_prime` → `commonAgreement_of_jointTaylorAgreementEquation_mem_prime`; it uses any sufficient exponent and the current affine-pair curve parametrization. `exists_graphLine_pair_of_symbolic_prime_agreements_of_exponent` and `exists_graphLine_pair_of_symbolic_prime_agreements` → `exists_graphLine_pair_of_regular_component_agreements`; it uses any sufficient exponent and returns the regular-component parametrization and restriction identities with the common-agreement bound. No source declarations are unported; the default-exponent forms are covered by the exponent-general statements and have no separate wrappers.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The graph-line component result now uses the shared `aeval_jointInitialJetSeparant`, `aeval_jointCommonTaylorNumerator`, and `aeval_jointTaylorAgreementEquation` results from `TaylorChartAlgebra`, and `regular_principalOpen_graph_restriction` from `PrincipalOpenParametrization`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedRegularEquation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/RegularEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `regularSymbolicCurveBadChallenges` to `regularPowerBatchedBadChallenges` and `regularSymbolicCurveMCABound` to `regularPowerBatchedAgreementBound`; the predicate and rational formula are unchanged, with the current exact-power-agreement API and agreement meaning. Renamed `finite_regularSymbolicCurveBadChallenges_card_le` to `finite_regularPowerBatchedBadChallenges_card_le`, `regularSymbolicCurveBadChallenges_finite` to `regularPowerBatchedBadChallenges_finite`, and `exists_exceptional_regularSymbolicCurveMCA` to `exists_exceptional_regularPowerBatchedAgreement`. Generalized the degree and height premises of these three theorems to `jetTotalDegree` and `CoeffNatDegreeLE`. No public declarations were omitted. The common-center and Taylor-reconstruction helpers use `PolynomialDifferential.exists_forall_jetEvaluation_ne_zero_of_family` and `rationalTaylorPolynomial_polynomialJet`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedSharpRegularAgreement.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/SharpRegularEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `sourceCurveCutChallengeDegree`, `sourceCurveCutJetDegree`, `sourceCurveInitialMixedDegreeTwo`, and `regularSymbolicCurveMCASharpBoundTwo` to `regularPowerBatchedCutChallengeDegree`, `regularPowerBatchedCutJetDegree`, `regularPowerBatchedInitialMixedDegreeTwo`, and `regularPowerBatchedAgreementSharpBoundTwo`, respectively, retaining their formulas. The common Taylor numerator bidegree results (`commonTaylorNumeratorOver_mem_sourceCurveCutBidegree_of_exponent` and `symbolicSourceNumerator_mem_sourceCurveCutBidegree[_of_exponent]`) are covered by `jointCommonTaylorNumerator_mem_regularPowerBatchedCutBidegree_of_exponent`; this is generalized to arbitrary differential order, sufficient Taylor exponents, and the joint chart API. The agreement-equation bidegree result `symbolicSourceCurveAgreement_mem_sourceCurveCutBidegree[_of_exponent]` is covered by `jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent`, generalized to the joint chart API and sufficient Taylor exponents.

Renamed `finite_sourceCurve_points_off_tuples_card_le_hybrid_two_of_exponent` to `finite_powerBatched_regular_points_off_admissible_graphs_card_le_firstOrder_of_exponent` and generalized it through generic bidegree incidence. Renamed `finite_sourceCurve_bad_challenges_card_le_of_source_bound_of_exponent` and `finite_sourceCurve_bad_challenges_card_le_hybrid_two_of_exponent` to `finite_powerBatchedBadChallenges_card_le_of_off_graph_bound_of_exponent` and `finite_powerBatchedBadChallenges_card_le_firstOrder_of_exponent`. Generalized the fixed-center and first-order bad-challenge bounds to sufficient Taylor exponents, and renamed them `finite_regularPowerBatchedBadChallenges_card_le_of_fixed_center_of_exponent` and `finite_regularPowerBatchedBadChallenges_card_le_firstOrder_of_exponent`. Renamed `exists_exceptional_regularSymbolicCurveMCA_hybrid_two_of_exponent` to `exists_exceptional_regularPowerBatchedAgreement_firstOrder_of_exponent`, generalized to sufficient Taylor exponents and the current agreement API. Historical acceptance cases in the shared Reed–Solomon test file checked the incidence bound, finite bad-challenge bound, and exceptional-set conclusion for this sharp API; the current suite does not directly test this module.

The order-zero declarations `sourceCurveInitialMixedDegreeOne` and `regularSymbolicCurveMCASharpBoundOne` were not ported because the source proves no bound about them and no consumer uses them. The initial-equation rectangle is covered by `initialJetEquation_mem_restrictBidegree`; initial-equation and separant cut rectangles follow from `initialJetEquation_mem_restrictBidegree` and `initialJetSeparant_mem_restrictBidegree` with `mem_restrictBidegree_mono`. The high-cut result is covered by the generalized common Taylor numerator theorem. Paired declarations without `_of_exponent` are the `τ = 2 * K` cases of their exponent theorems. Private helpers `set_finite_of_finset_card_le_rational` and `span_singleton_ne_top_of_aeval_eq_zero` are replaced by `Set.finite_of_forall_finset_card_le` and `Ideal.span_singleton_ne_top`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/SharpGeneralEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `sourceCurveInitialMixedDegree` to `regularPowerBatchedInitialMixedDegree` and `regularSymbolicCurveMCASharpBound` to `regularPowerBatchedAgreementSharpBound`. Generalized the incidence theorem to the joint chart API with `k ≤ A` and explicit terminal graph recognition as `finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_terminal_recognition`; derived `finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_exponent` for the internally recognized `k ≤ L` case. Generalized the finite bad-challenge bound and exceptional-set theorem to arbitrary derivative order and the current power-batched API as `finite_powerBatchedBadChallenges_card_le_sharp_of_exponent`, `finite_regularPowerBatchedBadChallenges_card_le_sharp_of_exponent`, and `exists_exceptional_regularPowerBatchedAgreement_sharp_of_exponent`.

Did not port `sourceCurveCutDerivativeDegree` because the generic capped-bidegree theorem supplies its cap. The common Taylor numerator, high cuts, agreement equation, and initial equation bounds are covered by generic capped-bidegree theorems. No joint Reed–Solomon separant wrapper is retained because the generic initial-separant support theorem covers it.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/SharpGeneralEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `sourceCurveCutJetDegree_le` to `regularPowerBatchedCutJetDegree_le_two_mul`, `sourceCurveCutChallengeDegree_mul_le` to `regularPowerBatchedCutChallengeDegree_le_three_mul`, and `sourceCurveInitialMixedDegree_le_uniformCaps` to `regularPowerBatchedInitialMixedDegree_le_uniformCaps`. These bounds generalize to an explicit `τ ≤ 2*n`; the challenge-degree bound also takes `H ≤ ℓ*h`. Renamed `regularSymbolicCurveMCASharpBound_mono_exponent` to `regularPowerBatchedAgreementSharpBound_mono_exponent` and placed it in the module that owns the agreement budget. Historical acceptance cases checked all three degree bounds and exponent monotonicity from `τ = 0` to `τ' = 1`; they are not in the current consolidated suite.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerToLine.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/PowerToLine.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exactCorrelatedPair_of_powerAgreement_one` keeps its name and turns exact degree-one power agreement for two constituents into an exact correlated-pair witness, preserving the degree bounds and full agreement-set equality. `lineExactAgreementBound_of_powerAgreement_one` keeps its name and is generalized from a rational budget and finite field to a real budget over any field. Both source public declarations are ported. The current suite retains one concrete degree-one power-agreement instance from an exact correlated-pair witness; historical cases for the reverse bridge and line-bound conversion were removed.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/PowerToLine.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`powerBatchedWord_pair_eq` names the identity between the degree-one power-batched word and the correlated line. `powerAgreement_one_of_exactCorrelatedPair` adds the converse from an exact correlated-pair witness to exact degree-one power agreement. No declarations from this source file were omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Admissible.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`Ordinary.PolynomialCurve.Admissible.IsAdmissibleFrobeniusPowerTuple` → `ReedSolomon.IsAdmissibleFrobeniusPowerTuple`, `Ordinary.PolynomialCurve.Admissible.IsAdmissibleFrobeniusPowerTuple.specialize` → `ReedSolomon.IsAdmissibleFrobeniusPowerTuple.specialize`, and `Ordinary.PolynomialCurve.Admissible.IsAdmissibleFrobeniusPowerTuple.eq_of_initialGraph_eq` → `ReedSolomon.IsAdmissibleFrobeniusPowerTuple.eq_of_initialGraph_eq`. The structure, specialization theorem, and uniqueness theorem are generalized from a `Fin n` domain to an arbitrary embedded coordinate type. Specialization is adapted to the current graph API. Uniqueness uses `iterateFrobenius_inj` and reuses `polynomialTuple_eq_of_infinite_specializations`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Counting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`Ordinary.PolynomialCurve.Counting.admissibleFrobeniusPowerTuples_card_le_degreeOf` → `ReedSolomon.admissibleFrobeniusPowerTuples_card_le_degreeOf`, generalized from `Fin n` to an arbitrary embedded coordinate type. No declarations from the counting source were left out. The imported adapter `Ordinary.PolynomialCurve.Admissible.exists_admissibleFrobeniusPowerTuple_of_symbolic_prime_sample` is not added because constructing admissible tuples from prime components is outside this counting unit.

Historical acceptance cases used a concrete zero tuple for specialization and singleton tuple counting. A zero-pair witness covered admissible-pair counting, retained-family nonemptiness and its cardinality bound. The exceptional-family example stated `exceptional.card ≤ 0` and equality of affine and common agreement sets for every retained pair; the standalone tuple admissibility and simplification-only uniqueness examples were also removed. The current consolidated suite has no direct example for this module.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleIncidence.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Incidence.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `sourceFrobeniusPowerSparseCuts` to `frobeniusPowerSparseTaylorNumerators`; its mathematical content is unchanged and it uses the joint Taylor numerator API. Generalized `sourceFrobeniusPowerGraphLocusAt` and `sourceFrobeniusPowerGraphLocus` as `admissibleFrobeniusPowerTupleGraphLocus`, with finite embedded coordinate types, `Set.ncard`, and a free agreement threshold. Generalized `commonAgreement_of_frobeniusPowerCut_mem_prime` from `Fin n` to arbitrary coordinate types and renamed it `commonAgreement_of_frobeniusPowerAgreementEquation_mem_prime`. Generalized `principalOpen_subset_sourceFrobeniusPowerGraphLocusAt` and `principalOpen_subset_sourceFrobeniusPowerGraphLocus` to finite embedded coordinate types and a free agreement threshold, under `principalOpen_subset_admissibleFrobeniusPowerTupleGraphLocus`. The finite bound combines `finite_sourceFrobeniusPower_points_off_graphs_card_le_at` and `finite_sourceFrobeniusPower_points_off_graphs_card_le` as `finite_frobeniusPowerTupleIncidence_off_graphs_card_le`; it uses the free threshold and `Set.ncard`, and drops the source assumption `A ≤ n`.

The default locus and principal-open wrappers are covered at `L = k`, as is the default finite bound. `symbolicSourceFrobeniusPowerAgreement_mem_restrictBidegree` is covered by the existing generalized `jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent`, so no source-specific wrapper was added.

Historical acceptance cases included concrete instances for the common-agreement theorem, principal-open graph inclusion, a finite incidence bound, high-cut jets, and chart-prime dimension. They are not in the current consolidated suite. The principal-open Frobenius-pair graph instance retained in the suite is described above.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleRegularBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/RegularBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finite_frobeniusPowerRegularBadWitnesses_card_le_at` and `finite_frobeniusPowerRegularBadWitnesses_card_le` → `finite_frobeniusPowerRegularBadChallenges_card_le`. The new arbitrary-threshold theorem is generalized to the current joint Taylor and degree interfaces and drops the `A ≤ n` assumption. Its specialization at `L = k` covers the source default-threshold theorem, so no fixed-threshold wrapper was added. No mathematical result was left out. A historical acceptance case imported the module and checked a nonempty singleton challenge set at zero over a two-point complex domain; it is not in the current consolidated suite.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/RegularChart.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finite_frobeniusPowerRegularBadWitnesses_card_le_of_separant_at` and `finite_frobeniusPowerRegularBadWitnesses_card_le_of_separant` are covered by `finite_frobeniusPowerRegularBadChallenges_card_le_of_separant_at`. The quantitative claim is unchanged; the theorem uses the current coefficient-height, jet-degree, and mapped-domain interfaces and drops the source assumption `A ≤ n`. Specializing at `L = k` covers the default-threshold statement, so it has no separate declaration. The private helper `ordinary_source_initial_ne_zero_of_regular` is covered by `jointInitialJetEquation_ne_zero_of_regular`. A historical acceptance case invoked the theorem on a nonempty singleton challenge set over a two-point complex domain; it is not in the current consolidated suite.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Regular.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_frobeniusPowerRegularSolutions_at` keeps its name. It now uses `CoeffNatDegreeLE` and `jetTotalDegree`, and does not require `A ≤ n`. A historical acceptance example specialized the arbitrary-threshold theorem over `ℂ` and showed that zero lies in an exceptional set of cardinality at most one; it is not in the current consolidated suite. The fixed-threshold `exists_exceptional_frobeniusPowerRegularSolutions` is covered by the theorem at `L = k`; no wrapper was added.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleRegularBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `finite_frobeniusRegularBadWitnesses_card_le` to `finite_frobeniusRegularBadChallenges_card_le`. This public specialization states the two-message correlated-pair bound, omits the redundant `A ≤ n` assumption, and uses current API interfaces.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/RegularChart.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `finite_frobeniusRegularBadWitnesses_card_le_of_separant` to `finite_frobeniusRegularBadChallenges_card_le_of_separant`. The theorem uses `CoeffNatDegreeLE` and `jetTotalDegree`, and drops the unnecessary source assumption `A ≤ n`. It selects a common regular center and specializes the arbitrary-tuple bound at tuple length two and retained threshold `k`. The private center-selection and ideal-properness helpers are covered by `exists_forall_jetEvaluation_ne_zero_of_family`, `jointInitialJetEquation_ne_zero_of_regular`, and the existing singleton-span properness argument. A private helper shares the two-message conversion between the supplied-center and center-free bounds.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/RegularSolutions.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_frobeniusRegularSolutions` keeps its name. It is generalized to `CoeffNatDegreeLE` and `jetTotalDegree` and no longer requires `A ≤ n`. The proof specializes the power-batched exceptional-set theorem to `ℓ = 1` and `L = k`, then converts exact power agreement to exact correlated-pair agreement. No declarations were omitted.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleSeparableBound.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Separable.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_frobeniusPowerSeparableSolutions_at` → `exists_exceptional_frobeniusPowerSeparableSolutions_at`, generalized to the current `CoeffNatDegreeLE` and `jetTotalDegree` interfaces and with the source assumption `A ≤ n` dropped. The separate `exists_exceptional_frobeniusPowerSeparableSolutions` wrapper was not ported because the arbitrary-threshold theorem covers it at `L = k` with `k ≤ A`.

The consolidated acceptance example applies the theorem to the concrete linear equation `Y₀`, checks the exceptional-set bound, and shows that zero belongs to the set for the nonconstant regular-bound fixture.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleSeparableBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_frobeniusPowerFactorSolutions` retains its name and specializes the arbitrary-threshold separable bound at threshold `D + 1`, expressing the exceptional-set cardinality bound with `ordinaryCurveFactorRaw` and the current coefficient-height and jet-degree interfaces. It uses `exists_exceptional_frobeniusPowerSeparableSolutions_at`. The consolidated acceptance example also checks the factor bound on the constant zero-word fixture, selects a challenge outside the exceptional set, and establishes exact agreement there. All seven source declarations have counterparts; none were omitted.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_exceptional_frobeniusPowerFactorSolutions_unifiedAt`, with the same name. It uses `CoeffNatDegreeLE` and `jetTotalDegree` and drops the unused `A ≤ n`. The existing `exists_exceptional_frobeniusPowerFactorSolutions` keeps its statement and is now proved from it. `exists_exceptional_frobeniusPowerFactorSolutions_unified` is not ported because it is the `L := D + 1` case followed by a rewrite with `ordinaryUnifiedPowerFactorAt_succ_eq`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/SingularTail.lean`

Merges `FirstOrder/Squarefree/Bounds.lean` and `FirstOrder/Squarefree/SingularTail.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, keeping the namespace
`ReedSolomon.FirstOrder.Squarefree`. `ordinaryDegreeEnvelope_ge_total` is now
`self_le_ordinaryDegreeEnvelope` and `ordinaryDegreeEnvelope_ge_resultant` is now
`mul_sub_sq_le_ordinaryDegreeEnvelope`. `content_add_resultantDegree_le` drops `0 < r` and
`r ≤ j`, and `content_add_resultantChallenge_le` weakens `0 < r` to `0 < M`. `singularTail` is
`U * resultant A A.derivative r (r - 1)` in main's argument order, equal to the source's
`separableResultant` form by `resultant_comm_sub_one`. `natDegree_singularTail_le` drops `0 < r`,
`r ≤ j` and `A.natDegree = r`, and `singularTail_map_eq_zero_of_common_root` drops both `IsDomain`
assumptions.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/DerivativeTupleCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/DerivativeTupleCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`admissibleChartTuples_card_le_derivativeCapped_of_exponent` and `admissibleChartTupleFamilyAtExponent_card_le_derivativeCapped` keep their names and conclusions, with the source hypothesis `0 < k` dropped. The bounds transport total and derivative degree bounds through the coefficient-map lemmas and retain the sharp agreement ratio `(n-k+1)/(L-k+1)`. The shared specialization theorem `exists_regularHighCutJetImage_of_admissibleChartTuples` is in `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedGraphCounting.lean`; it gives an equal-cardinality image of regular high-cut Taylor jets with inherited agreement equations.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ExceptionalChallenges.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ExceptionalChallenges.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `ReedSolomon.finite_sourceChart_bad_challenges_card_le` to `ReedSolomon.finite_symbolicTaylorChart_badChallenges_card_le`. The mathematical bound is unchanged; it uses destination joint-chart equations, `CoeffNatDegreeLE`, and current set-cardinality APIs. The source height predicate was replaced, the mapped domain uses `domain.trans ⟨iota, iota.injective⟩`, the incidence boundary condition is derived from existing bounds, and the unused assumption `0 < v` was removed. No public source declaration was omitted. Private source evaluation helpers are handled by joint-chart evaluation APIs or remain private proof steps; `source_initial_ne_zero_of_regular` is represented by private `jointInitial_ne_zero_of_regular`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/Incidence.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/Incidence.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `sourceChartHighCuts` to `jointTaylorHighCutList`, `symbolicSourceNumerator_mem_sourceChartHighCuts` to `jointCommonTaylorNumerator_mem_jointTaylorHighCutList`, `sourceChartPairLocus` to `admissibleChartPairGraphLocus`, `principalOpen_subset_sourceChartPairLocus` to `principalOpen_subset_admissibleChartPairGraphLocus`, `finite_sourceChart_points_off_pairs_card_le` to `finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le`, and `finite_sourceChart_points_off_pairs_card_le_of_source` to `finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le_of_jetDegree`.

The graph-locus inclusion uses `Set.ncard` cut counts and the explicit exponent `2 * K`. The finite incidence bound uses `L ≤ A` and `A - L + 1 ≤ n`, counts agreement indices with `Set.ncard`, and drops the unnecessary positive cut-degree premise. Its specialization uses `jetTotalDegree` and `CoeffNatDegreeLE` and drops the positive jet-degree premise. No public source declarations were omitted; finite index-set encodings are expressed directly with `Set.ncard`.

The matching acceptance module `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart.lean` replaces the high-cut membership example with two concrete singleton-set examples, one for each finite incidence bound.
Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/SingularTail.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `automaticSquarefreeListBoundConstant` and `automaticSquarefreeListExpression_le` with their source names. The theorem specializes the automatic first-order recipe to a rate-only constant times `n / eta²`, using the shared premise theorem from `AutomaticBounds.lean`. No declarations from the source unit were omitted. The matching acceptance file checks the singular-tail zero case and an automatic bound instance at rate `2 / 49`, slack `1 / 100`, and parameters `n = 100`, `D = 1`, `A = 20`.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PairCounting.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PairCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`chartPairPullback` → `chartPairPullback`, `chartPairJet` → `chartPairJet`, `IsAdmissibleChartPair` → `IsAdmissibleChartPair`, `eval_chartPairPullback_symbolic` → `eval_chartPairPullback_symbolic`, `degree_correlatedPairSpecialization_lt` → `degree_correlatedPairSpecialization_lt`, `coeff_taylor_correlatedPairSpecialization` → `coeff_taylor_correlatedPairSpecialization`, `IsAdmissibleChartPair.specialize` → `IsAdmissibleChartPair.specialize`, `admissibleChartPairs_card_le` → `admissibleChartPairs_card_le`, `admissibleChartPairFamily` → `admissibleChartPairFamily`, `mem_admissibleChartPairFamily_iff` → `mem_admissibleChartPairFamily_iff`, and `admissibleChartPairFamily_card_le` → `admissibleChartPairFamily_card_le`.

The chart numerator exponent defaulted to `2*K` in the source and is explicit in the destination API. Generalized `admissibleChartPairs_card_le` and `admissibleChartPairFamily_card_le` to remove the positive-`k` premise: for `k > 0` they retain the source incidence estimate, and for `k = 0` the degree conditions force every pair to zero, yielding a singleton bound.

The private source helper `jetDegree_pos_of_initialSeparant_ne_zero` was not ported because the destination incidence theorem handles regular-jet counting without its positivity premise. The existing acceptance file `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart.lean` retains the degree-specialization example and adds a concrete admissible-pair example covering specialization and both cardinal bounds.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PairCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`admissibleChartPairs_card_le_sharp` and `admissibleChartPairFamily_card_le_sharp` keep their source names. Both bounds now allow `k = 0`, where the degree constraints force every admissible pair to be zero and the count is at most one. For positive `k`, they use the factor `v * (((n - k + 1) * (1 + 2 * K * (v - 1)) / (L - k + 1)) ^ r)`. The proof specializes the generic sharp high-cut incidence theorem after choosing a challenge that preserves pair injectivity. No public source declaration was omitted. The source-private `jetDegree_pos_of_initialSeparant_ne_zero_sharp` was not ported because the current generic sharp incidence theorem has no positive jet-degree premise.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PairCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Promoted the private chart-pullback evaluation helper to the public identity `ReedSolomon.eval_chartPairPullback_joint`. The source report lists no public declaration for this identity.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PointRecognition.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PointRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.exists_graphLine_pair_of_symbolic_sample` keeps its name and mathematical statement. It recovers a base-field polynomial pair from the sample constraints and shows that every compatible regular symbolic chart reconstructs their affine combination, its initial jet, and its cleared Taylor coefficients. The current theorem uses the explicit `2 * K` exponent API. No declaration from the source file was omitted; the TaylorCuts bridge declarations are supplied by the current `TaylorChartAlgebra` API.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_graphLine_pair_of_symbolic_sample_of_exponent` keeps its name and mathematical substance in the canonical point-recognition owner. It supplies recognition for every sufficient exponent.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/TaylorChart.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_frobeniusGraphLine_of_symbolic_sample` keeps its name. It is generalized from `Fin n` to an arbitrary embedded coordinate type and requires root equations only on the sample, as used by interpolation. The source file's only public declaration is covered; its interpolation and Taylor-cut helpers already live in the current `GraphLine` and `TaylorChartAlgebra` APIs, so nothing is deferred or unported.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/RegularEquation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/RegularEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`regularSymbolicMCABound` was renamed to `regularSymbolicAgreementBound`, and `exists_exceptional_regularSymbolicLineMCA` was renamed to `exists_exceptional_regularSymbolicCorrelatedAgreement`. The rational bound formula and uniform exceptional-set conclusion are unchanged. `regularSymbolicBadChallenges`, `finite_regularSymbolicBadChallenges_card_le`, and `regularSymbolicBadChallenges_finite` keep their names. The cardinality bound, finiteness theorem, and exceptional-set theorem drop the unused `0 < v` assumption. The bad-challenge predicate uses the current embedding-composition domain API, and the bound uses `CoeffNatDegreeLE`.

The common-center argument uses `Polynomial.exists_forall_eval_ne_zero`, added to the public polynomial API and owned by `SpecializationAvoidance`. `exists_forall_jetEvaluation_ne_zero_of_family` replaces `exists_common_symbolicWitness_center` and generalizes it to a finite indexed family of differential equations and solution polynomials. The existing `exists_forall_jetEvaluation_ne_zero` statement is unchanged and specializes the family theorem.

`HasExactCorrelatedPair` was already defined in `MutualCorrelatedAgreement/ExtensionDescent.lean` with the exact polynomial and agreement-set conditions, so it was not redeclared. No other public declaration from the unit was omitted. `ArkLibTest/Data/Polynomial/Differential.lean` checks a common center for two distinct equations. `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart.lean` checks the exceptional-set theorem, a nonempty singleton in the finite-family bound, and finiteness of the full bad-challenge set.

## `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TupleSpecialization.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Specialization.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, with the ring hom named `φ`.
`powerBatchedCoordinate_injective` moved to `ReedSolomon/PowerAgreement.lean`.

## `ArkLib/Data/CodingTheory/ReedSolomon/PowerAgreement.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, under
`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/`:

* `PolynomialCurve/Agreement.lean`: `powerBatchedWord`, `powerBatchedPolynomial`,
  `powerBatchedPolynomial_degree_lt`, `powerBatchedPolynomial_eval`, and
  `commonCurveAgreementSet`, ported with the coordinate type `Fin n` generalized to a finite
  type `ι`, and with decidable equality on `F` in place of classical decidability in
  `commonCurveAgreementSet`.
* `PolynomialCurve/FullAgreement.lean`: `HasExactPowerAgreement`, with the source's
  `mappedDomain domain ι` written out as `domain.trans ⟨φ, φ.injective⟩`.
* `UniformPowerAgreement.lean`: `UniformExactPowerAgreement`, with the same quantifier order.

The code-level characterizations are new. They let the counting and transfer theorems of
`ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement` apply to Reed–Solomon statements.
The interleaved statements are in `ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement`.
Scalar providers of `UniformExactPowerAgreement` (list-decoding and curve-counting results) are
not ported here.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/GraphCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`polynomialTupleFamily`, `mem_polynomialTupleFamily_of_commonAgreement`, `polynomialTupleFamily_card_le`, and `mem_polynomialTupleFamily_iff` retain their names and are generalized from `Fin n` to finite embedded coordinate types.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/PowerAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`frobeniusPowerCoordinate`, `frobeniusPowerCoordinate_eval`, and `frobeniusPowerCoordinate_natDegree_le` keep their names. The sparse coordinate is defined by expanding `powerBatchedCoordinate`; all three declarations are generalized from fields to commutative semirings. The acceptance case in `ArkLibTest/Data/CodingTheory/ReedSolomon.lean` checks evaluation at `2` and the degree bound for three values with scale `2`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/PowerAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added the shared `eval₂_powerBatchedCoordinate_eq_powerBatchedWord` identity with a commutative-semiring source. It replaces the private copies used by the certificate and first-order curve modules.

## `ArkLib/Data/CodingTheory/ReedSolomon/PowerAgreement/ConstantCode.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ConstantCode.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, for any finite `ι` in place of
`Fin n`. `uniformExactPowerAgreement_constantCode` now holds for every `A`, with the bound
`ℓ * (card ι).choose 2 / max (A - 1) 1` in place of the `if` on `A = 1` and without `0 < A`.
`uniformExactPowerAgreement_constantCode_of_two_le` keeps its name.
`uniformExactPowerAgreement_constantCode_one` is not ported; it is the case `A = 1` of the
general theorem. The private `hasExactPowerAgreement_constant_of_same` is now the iff
`hasExactPowerAgreement_constant_iff`. The private collision machinery
(`constantCodeCollisionPolynomial`, `constantCodeOrderedPairs`, `constantCodeCollisionIncidence`,
`constantCodeCollisionMultiplicity`, `constantCodeCollisionChallenges`,
`constantCodeIncreasingPairs`, `constantCodeCollisionChallengesHalf` and their lemmas) is now
`exists_exceptional_powerBatchedWord_collision` with private helpers.
`uniformExactPowerAgreement_singleton` of
`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/UniformPowerAgreement.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` is ported with the same name, for any
finite coordinate type in place of `Fin n`.
Also from the same source directory:

* `PolynomialCurve/Agreement.lean`: `powerBatchedCoordinate` (over a `CommSemiring`, with the new
  `_eq_ofFn`, `_coeff` and `_eq_zero_iff`), `curveDiscrepancy` (defined as the
  `powerBatchedCoordinate` of the constituent discrepancies),
  `exists_exceptional_powerBatched_agreement` and `exists_exceptional_powerBatched_family` (the
  count `ℓ * (n - L)` is
  `ℓ * (Fintype.card ι - L)`), `exists_polynomialTuple_interpolating` (`samples.card ≤ k` in place
  of `= k`), `polynomialTuple_eq_of_common_samples` (`k ≤ samples.card` in place of `= k`) and
  `exists_polynomialGraph_of_sample`.
* `PolynomialCurve/FullAgreement.lean`: `powerBatchedWord_map` and `powerBatchedPolynomial_map`.
* `PolynomialCurve/ExtensionDescent.lean`: `HasExactPowerAgreement.descend`, and
  `exists_exceptional_powerAgreement_descend` as `uniformExactPowerAgreement_of_extension`, whose
  conclusion unfolds to the source's.

## `ArkLib/Data/Finset/Staircase.lean`

Generalizes `staircaseCount`, `StaircaseIndex`, `card_staircaseIndex`, `staircaseIndexEquiv`, and
`card_staircasePairs` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Counting.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source counted a dependent index type
`Σ b : Fin L, Fin (L - D * b)` and transported it by an explicit equivalence; here the pairs form
a filtered product `Finset`, its cardinality needs no hypothesis on `D`, and only the comparison
with the unbounded subtype assumes `D > 0`.

## `ArkLib/Data/Finset/WeightedSimplex.lean`

Generalizes `ordinaryToExact`, `ordinarySimplexEquivSym`, and `card_ordinarySimplex` from
`ToMathlib/Combinatorics/DiscreteSimplex/Basic.lean`, and `ordinaryToScaledWithResidue`,
`scaledWithResidueToOrdinary`, and `scaledExponentCount_factorial_sq_sandwich` from
`HiddenDerivative/Parameters/Lattice/ScaledLattice.lean`, all at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source adapts `kz99/rs-ld-mca`
revision `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` with permission.
`weightedHigherJetTuples`, `weightedHigherJetShell`, and their `Finsupp` bridges motivate the
finite sets and shell decomposition; `ratePartitionTupleCount_le_volume` motivates the
ordered-field bound. Continuous volumes, floor cells, moments, and Reed--Solomon-specific adapters
are deferred.

## `ArkLib/Data/Finset/WeightedSimplex/FloorTransfer.lean`

Generalizes, from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, the generic parts of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`:

* `WeightedSupportParameters.floor_higher_mem` (`FloorTransfer.lean`) becomes
  `natFloor_mem_natWeightedSimplex`, for any finite index type, positive natural weights, and a
  real budget, instead of `Fin (d - 1)` with weights `i + 1` and a natural budget.
* The covering and cell argument of `WeightedSupportParameters.weighted_floor_integral`
  (`FloorTransfer.lean`) becomes `setIntegral_le_sum_natWeightedSimplex`, with an arbitrary
  integrand and cellwise bound in place of the cubic positive part.
* `floorCell_subset_weightedSimplex` (`CubeTransfer.lean`) becomes
  `natFloorCell_subset_weightedSimplex`, and the cell argument of
  `weighted_residual_sum_le_integral` becomes `sum_natWeightedSimplex_le_setIntegral`, with an
  arbitrary integrand and cellwise bound in place of the residual.

The source-shaped cubic and residual statements are thin specializations in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer`.

## `ArkLib/Data/Finset/WeightedSimplex/Moments.lean`

Generalizes, at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, the declarations of
`ToMathlib/Combinatorics/DiscreteSimplex/Moments.lean`: `splitCoordinate`, `mergeCoordinate` and
`simplexCoordinateSplitEquiv` become `natSimplexSplit` and
`sum_natWeightedSimplex_one_sum_range_split`, a reindexing of Finset sums rather than an
equivalence of subtypes; `ordinarySimplex_coordinate_le` becomes `le_of_mem_natWeightedSimplex`
for arbitrary weights; `sum_simplex_coordinate_succ`, `simplex_first_moment`,
`sum_simplex_mixed_succ`, `sum_simplex_factorial_succ`, `simplex_mixed_moment`, and
`simplex_factorial_moment` become the theorems listed above. The source's `OrdinarySimplex r S`
over `Fin r` is the case `σ = Fin r` of `natWeightedSimplex (fun _ ↦ 1) S`, and the statements
hold over any finite index type. From `ToMathlib/Combinatorics/DiscreteSimplex/Variance.lean` at
the same revision, `simplex_weighted_sum` and `simplex_weighted_square_sum` are generalized from
`ℝ` to any commutative ring, and the private `coordinate_product_moment` is made public. Moments of
simplices with non-unit weights, which have no comparable closed form, are not treated.

## `ArkLib/Data/Finset/WeightedSimplex/RankIntegral.lean`

Generalizes, from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`WeightedSupport/RankIntegral.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `ReedSolomon.HiddenDerivative.weighted_residual_sum_le_volume_mul_mean_variance` becomes
  `sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le`, for any finite index type,
  positive natural weights and nonnegative coefficients instead of `Fin (d - 1)`, weights `i + 1`
  and coefficients `1`. The source's hypotheses `1 ≤ d` and `0 < W + choose d 2` are dropped: the
  degenerate case `W' = 0` forces `σ` to be empty, where the bound is checked directly. The
  variance is a set average instead of an integral against `weightedSimplexProbabilityMeasure`.
* `ReedSolomon.HiddenDerivative.weighted_residual_sum_le_volume_mul_harmonic_variance` becomes
  `sum_natWeightedSimplex_max_sub_add_one_le`.

The source-shaped statements are thin specializations in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral`.

## `ArkLib/Data/Finset/WeightedSimplex/Variance.lean`

Generalizes, at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, the declarations of
`ToMathlib/Combinatorics/DiscreteSimplex/Variance.lean` from `OrdinarySimplex r S` over `Fin r`
and real weights to `natWeightedSimplex (fun _ ↦ 1) S` over any finite index type, with weights in
any field of characteristic zero for the identities and any ordered field for the inequalities.
`simplexAverage` is replaced by Mathlib's `Finset.expect`, and `simplexWeightedStatistic` by the
explicit sum `∑ i, w i * c i`. `card_ordinarySimplex_pos` becomes `natWeightedSimplex_nonempty` in
`ArkLib.Data.Finset.WeightedSimplex.Moments`. `simplexWeightedMean` and `simplexWeightedVariance`
become `natSimplexWeightedMean` and `natSimplexWeightedVariance`; `simplex_average_weighted`,
`simplex_average_weighted_square`, `simplex_average_centered_square`, and
`simplexWeightedVariance_nonneg` become the theorems above. `simplex_upper_tail_count`, stated for
an arbitrary subset of the upper tail, becomes
`sq_mul_card_filter_mean_add_le_le_card_mul_variance` for the full upper tail, and is derived from
the two-sided `sq_mul_card_filter_le_abs_sub_le_card_mul_variance`. The source's unnamed example
with variance `5 / 12` is an acceptance case. The sharper one-sided Cantelli bound, continuous
simplex moments, and a comparison between the finite and continuous variances are not treated.

## `ArkLib/Data/MvPolynomial/JointDegree.lean`

`MvPolynomial.restrictJointDegree` covers `CoeffDegreeLE` (zero weight) and `GradedCoeffDegreeLE`
(`ℓ`-scaled weight) of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/ReceivedLine.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`; their private closure lemmas are the
public `_mem_restrictJointDegree` lemmas here.
## `ArkLib/Data/MvPolynomial/FrobeniusContraction.lean`

Ported from `ArkLib/ToMathlib/MvPolynomial/FrobeniusFactor.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, over a commutative ring without zero divisors in
place of a field, and without `Fact p.Prime`. `exists_frobeniusFactor` is now
`exists_irreducible_frobeniusContraction` for `CharP R p`, and `exists_frobeniusFactor_expChar`
is now `exists_irreducible_frobeniusContraction_expChar`. These two return the root expansion, the
nonzero partial derivative, the degree identity, positive degree, irreducibility and the
per-variable degree bounds. The fraction-field parts are now
`irreducible_map_optionEquivLeft_fractionRing`, `separable_map_optionEquivLeft_fractionRing` and
`exists_frobeniusContraction_fractionRing`, over a unique factorization domain. The primitivity,
mapped-derivative and mapped-degree parts of the source's ten-part statements are not stated. The
consolidated suite now retains a concrete two-variable `ZMod 2` contraction and a fraction-ring
irreducibility/separability instance, but no generic ten-part derivation.
`inverseFrobeniusTwist_preserves_factor` and its `_expChar` form are not
ported; their component statements are the P6 slice 1 results. The
`frobeniusFactor_coefficient_canary` example was removed with the per-module suite.

## `ArkLib/Data/MvPolynomial/MapExponents.lean`

This generalizes `normalizeErrorByExponent`, `normalizeError_injective` and
`truncateLocalT_normalizeError` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/RemainderMap.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which treated the single relabelling
`E ↦ T^d E` of local variables over a commutative ring. The private
`filterLocalMonomials_monomial` of that file is `filterSupport_monomial`.

## `ArkLib/Data/MvPolynomial/RadicalSplit/Separable.lean`

Ported from `ArkLib/ToMathlib/MvPolynomial/OrdinaryFactorSeparable.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

`ordinaryRootPolynomial` and `natDegree_ordinaryRootPolynomial` keep their names, generalize from
field coefficients to UFD coefficients, and use `radicalPrimPart none`. The degree statement is
expressed using `radicalPrimPart`.

`ordinaryRootPolynomial_map_fraction_separable` →
`ordinaryRootPolynomial_map_fractionRing_separable`; it generalizes to UFD coefficients and
arbitrary fraction-field presentations, and no longer requires `Q ≠ 0`. The new public theorem
`radicalPrimPart_map_optionEquivLeft_fractionRing_separable` states the result for any
distinguished variable; the ordinary-root theorem is its `none` specialization.

`MvPolynomial.paddedDerivativeResultant_ordinaryRootPolynomial_ne_zero` →
`Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial`. It specializes the existing
generic fraction-field resultant theorem using the ordinary-root polynomial's natural degree.

Not ported: no public declarations were omitted. The source's private derivative and factor-degree
helpers are replaced by `pderiv_ne_zero_of_natCast_ne_zero` and the radical split degree bound.
The source padded-resultant wrapper is replaced by the existing generic separable-map resultant
theorem. The source nonzero-polynomial hypothesis is unnecessary because the current radical
primitive part of zero is `1`.

## `ArkLib/Data/MvPolynomial/WeightAtMost.lean`

The `M`-valued support-weight lemmas generalize the private lemmas `support_weight_mul_le`,
`support_weight_pow_le`, `support_weight_prod_le`, and `support_weight_bind₁_le` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/IntermediateSpace.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source stated them for single
support exponents over an ordered additive commutative monoid; here they are stated as closure
properties of a submodule, and `finrank_restrictSupport_finset` replaces the source's
per-space basis cardinality computations.

Nothing is deferred.

## `ArkLib/Data/MvPolynomial/WeightedHomogeneous.lean`

These generalize the monomial-by-monomial homogeneity arguments inside
`ReedSolomon.HiddenDerivative.unscaledLocalSubstitution_zero_monomial_isWeightedHomogeneous` and
`ReedSolomon.HiddenDerivative.localConstraintAt_zero_isWeightedHomogeneous` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/GradedRank.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which treated one substitution and
one truncation into local variables with natural weights.

## `ArkLib/Data/MvPolynomial/WeightedOrder.lean`

The truncation argument generalizes the private support lemmas behind
`ReedSolomon.HiddenDerivative.enlargedLocalConstraintMap_truncateLocalT` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/ConstraintMap.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which were adapted from Kai Zhe
Zheng's `rs-ld-mca` formalization. The source proved the special case of one change of local
variables using integer-valued negated weights; here the statement is for arbitrary variable
types, arbitrary natural weights, and an arbitrary commutative semiring. The source's
`filterLocalMonomials` is `filterSupport` for local polynomials.

`pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder` generalizes the source's
`pow_dvd_eval₂Hom_of_lowContact_coeff_zero` and its private helper
`localContactOrder_pow_dvd_monomialSpecialization` in
`.../HiddenDerivative/Interpolation/Local/Contact.lean` at the same revision from the local
contact weight to an arbitrary weight, and from commutative rings to commutative semirings.

## `ArkLib/Data/Polynomial/Differential/BaseChange.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/SolutionExtension.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`mapped_regular_solution_family` is now `map_regularSolutionFamily`. It is generalized from fields to commutative semirings with an explicit injective coefficient map, and from the last separant to any jet coordinate. `map_differentialSpecialization_ne_zero_iff` is a new reusable lemma that proves an injective coefficient map preserves nonvanishing of differential specialization.

Not ported: `map_separant` already exists as `PolynomialDifferential.map_separant` in this module. `map_binomial_pivots` follows from naturality of `Nat.cast` under an injective ring hom; the acceptance test derives the field form.
Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/CoefficientExtension.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`jetWeight_extendSymbolicCoefficients_le` → `PolynomialDifferential.jetTotalDegree_map_le`, generalized from polynomial-coefficient field extensions to any ring homomorphism between commutative semirings, including noninjective maps. `challengeHeightLE_extendSymbolicCoefficients` was not ported because `MvPolynomial.CoeffNatDegreeLE.map_coefficients` already provides the result through `ChallengeHeightLE`; `separant_extendSymbolicCoefficients` is covered by the existing `PolynomialDifferential.map_separant`.

## `ArkLib/Data/Polynomial/Differential/Basic.lean`

The definitions and laws are ported from `ArkLib/Data/Polynomial/Differential/Basic.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

## `ArkLib/Data/Polynomial/Differential/ContentExceptions.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Factors/ContentExceptions.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.HiddenDerivative.exists_exceptional_ordinaryContent` is renamed to `PolynomialDifferential.exists_exceptional_jet_independent_content` and generalized from fields to commutative integral domains. Its coefficient-height bound uses `MvPolynomial.CoeffNatDegreeLE`. The theorem bounds challenges where a nonzero equation independent of its jet specializes to zero; outside the exceptional set, every polynomial input has nonzero specialization.

The acceptance case in `ArkLibTest/Data/Polynomial/Differential.lean` uses a height-one nonconstant coefficient equation that vanishes at challenge zero and checks that zero belongs to an exceptional set of cardinality at most one. Nothing was deferred or left unported.

## `ArkLib/Data/Polynomial/Differential/DerivativeDescent.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TaylorCutoff.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.HiddenDerivative.geometric_characteristic_components` became `PolynomialDifferential.characteristic_bounds_of_max`. It generalizes the field result to commutative semirings and drops the unnecessary `0 < K` assumption. `ReedSolomon.geometric_below_characteristic` became `PolynomialDifferential.jetDegreeCastsNeZero_of_jetTotalDegree_charGuard`. It generalizes to any commutative semiring and the current `JetDegreeCastsNeZero` contract, without the unused message-dimension and block-length parameters. The source-shaped `IsBelowCharacteristic (k - 1) Q` result is not recreated because that bundled predicate is absent from the current API; the jet-degree consequence is supplied in the operational cast form, and ambient-cutoff bounds remain separate in the current certificate API.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/HybridDescent.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`PolynomialDifferential.root_reaches_tail_or_regular_stage` retains its name and is now owned by the generic derivative-descent module. Added `PolynomialDifferential.jetTotalDegree_jetDerivative_le_sub`, a coefficient-generic total-degree bound on iterated jet derivatives; both descent constructors use it.

## `ArkLib/Data/Polynomial/Differential/DirectRegularLift.lean`

This file ports the semantic content of `RootFinding/Regular/DirectRegularCoefficient.lean` and
`RootFinding/Regular/DirectRegularIteration.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source defined executable versions over a field,
on `CompPoly` polynomials, and compared them with an exhaustive scan over a finite field. Here the
definitions are noncomputable, on `Polynomial`, over a commutative ring, and a unit slope replaces
the nonzero slope:

* `effectiveDirectRegularCoefficient` (`none` for a zero slope, otherwise `-β / σ`) corresponds to
  `regularLiftCoefficient`, which uses `Ring.inverse` and is correct whenever `σ` is a unit.
  `effectiveDirectRegularCoefficient_sound_unique` corresponds to
  `coeff_shiftedJetSubstitution_add_hassePerturbation_eq_iff`.
* `effectiveResidualCoeff_affine` and `effectiveRegularSlope_eq` are
  `coeff_shiftedJetSubstitution_add_hassePerturbation` in
  `ArkLib.Data.Polynomial.Differential.RegularLift`.
* `directRegularIteration` corresponds to `regularIterate`; its degree bound
  `directRegularIteration_natDegree_le` to `natDegree_regularIterate_le`.
* `directRegularSolution_eq_some_iff` corresponds to `solution_iff_eq_regularIterate`, with unit
  slopes in place of `IsRegularJet` and `D < ringChar F`, and without `Finite F`.

Deferred: the `CompPoly` definitions, the two-evaluation slope recovery, and the comparison with
the exhaustive coefficient scan (`effectiveRegularCoefficients_eq_singleton_of_direct`,
`effectiveDirectRegularCoefficient_exists_of_survivor`,
`directRegularIteration_eq_some_and_candidates`, `directRegularSolution_toFinset_eq`). They
depend on the executable root-finding layer `ReedSolomon/Computation/RootFinding/Lifting/`, which
is not ported.

## `ArkLib/Data/Polynomial/Differential/FrobeniusEquation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/Equation.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `ReedSolomon.HiddenDerivative`.

`flatVariableEquiv`, `rootFirstEquiv`, `baseVariableEquiv`, `baseFlatten`, `ordinaryFlatten`, and `ordinaryUnflatten` keep their names in `PolynomialDifferential`. The flattening, evaluation, derivative, unflattening, and degree-transport declarations also keep their names, except `ordinaryFlatten_Y`, renamed `ordinaryFlatten_root` to identify the root coordinate. These APIs are generalized from fields to commutative semirings, with `Nontrivial` assumptions where degree bounds require them.

`challengeHeightLE_ordinaryUnflatten_monomial` and `challengeHeightLE_ordinaryUnflatten_of_degreeOf_le` become `coeffNatDegreeLE_ordinaryUnflatten_monomial` and `coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le`, using the existing `MvPolynomial.CoeffNatDegreeLE` predicate. `differentialSpecialization_map_eq_eval₂_flatten`, `eval_differentialSpecialization_map_eq_flatten`, and `expand_differentialSpecialization_map_eq_eval₂_flatten` keep their names and generalize from fields to commutative semirings. `frobeniusSpecialization_pow` keeps its name and generalizes from perfect fields to commutative rings with `ExpChar` and `PerfectRing`. `frobeniusSpecialization_eq_zero` and `exists_frobeniusEquation` keep their names and generalize to commutative rings without zero divisors with `ExpChar` and `PerfectRing`. The existence theorem also requires `[Nontrivial E]`; zero transport does not.

`map_rootExpansion` and `eval₂_rootExpansion` become `MvPolynomial.map_rootExpansion` and `MvPolynomial.eval₂_rootExpansion`. They are generalized to commutative semirings and placed with the generic root-expansion API. The existing Frobenius contraction and inverse-twist preservation APIs replace the source fraction-ring aggregate API.

Not ported: `ordinaryFlatCases_one` remains a private proof helper because it is a `Fin.cases` computation, not a reusable domain API. `frobeniusEquation_nonconstant_coefficient_canary` is restated as an acceptance-test example. The two source `ChallengeHeightLE` lemmas are represented by the renamed `CoeffNatDegreeLE` lemmas. No declaration was blocked or left without a proof.

## `ArkLib/Data/Polynomial/Differential/FrobeniusTaylorWitness.lean`

Ported from `ArkLib/Data/Polynomial/Differential/FrobeniusTaylorWitness.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `symbolicFrobeniusWitness_equations` to `frobeniusExpansion_satisfies_jointTaylorCuts`. The canonical theorem uses the joint Taylor-chart API and a flattened joint point. The sufficient-exponent wrapper `frobeniusTaylorExponentSufficient` is covered by `taylorExponentSufficient_two_mul_sub_three` at `K = D * s + 1`; no wrapper was added. The reconstruction wrapper `symbolicFrobeniusWitness_reconstruction` is covered by `rationalTaylorPolynomial_polynomialJet` at order zero; no wrapper was added. No other public source declaration from this file was left out.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Witness.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `symbolicFrobeniusPowerWitness_equations` to `PolynomialDifferential.frobeniusExpansion_satisfies_jointTaylorCuts` and generalized its agreement characterization from a two-term Frobenius power curve to any polynomial-valued curve. Specializing the curve to `ReedSolomon.frobeniusPowerCoordinate` recovers the source agreement result using its evaluation lemma. The theorem retains its initial equation, regularity, and sparse-cut conclusions. The source reconstruction wrapper `symbolicFrobeniusPowerWitness_reconstruction` is covered by `PolynomialDifferential.rationalTaylorPolynomial_polynomialJet` at order zero and was not added.

## `ArkLib/Data/Polynomial/Differential/JetDegree.lean`

The core definitions and specialization bounds are ported from the differential and
specialization modules at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
The total-jet-degree API is extracted from
`HiddenDerivative/RootFinding/Counting/TotalJetDegreeRootCount.lean` at the same revision.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`degreeOf_initialJetEquationOver_firstOrder` became `PolynomialDifferential.degreeOf_initialJetEquation_le`. The bound now applies at arbitrary differential order over a nontrivial commutative semiring.

## `ArkLib/Data/Polynomial/Differential/JetPrefix.lean`

Ported from ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

From `ArkLib/Data/Polynomial/Differential/Basic.lean`: `DependsOnJet`, `activeJets`,
`mem_activeJets`, `highestActiveJet`, `IsHighestActiveJet`, `highestActiveJet_eq_some_max`,
`isHighestActiveJet_of_highestActiveJet_eq_some`, `highestActiveJet_eq_none_iff`,
`IsRegularJet`, `RegularJet`, `BoundedSolution`, `BoundedSolution.polynomial`,
`BoundedSolution.equation` and `BoundedSolution.degree_le` keep their statements. The rest of
that source file is in `ArkLib.Data.Polynomial.Differential.Basic` and
`ArkLib.Data.Polynomial.Differential.JetDegree`.

From `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Regular/JetPrefix.lean`:
`jetPrefixEmbedding` (now built from `Fin.castLEEmb`), `jetPrefixEmbedding_none`,
`jetPrefixEmbedding_top` (here `jetPrefixEmbedding_some_last`), `restrictJet`,
`restrictJet_polynomialJet`, `vars_subset_range_jetPrefixEmbedding`,
`exists_prefixDifferentialPolynomial`, `differentialSpecialization_rename_jetPrefixEmbedding`,
`jetEvaluation_rename_jetPrefixEmbedding`, `separant_rename_jetPrefixEmbedding` and
`isRegularJet_rename_jetPrefixEmbedding_iff`. The source stated them over a field in the
namespace `ReedSolomon.HiddenDerivative`; none mentions a Reed–Solomon object, so they are stated
here over a commutative semiring in `PolynomialDifferential`. The source's
`existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet` is
`existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet` in
`ArkLib.Data.Polynomial.Differential.RegularIteration`, with a unit hypothesis instead of a
`ringChar` bound. `jetPrefixEmbedding_some` and `jetEvaluation_separant_rename_jetPrefixEmbedding`
are new.

`IsRegularJet` keeps the source's condition that the separant value is nonzero. Over a field this
is what the lifting theorems need; over a general commutative ring they instead assume that the
slope, a binomial coefficient times that value, is a unit or left-regular.

## `ArkLib/Data/Polynomial/Differential/JetPrefixPresentation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FirstOrder/FirstOrderHybridList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_firstOrderFieldTailPresentation` became `exists_jetPrefixPresentation_firstOrder_of_jetDegree_zero`, generalized to commutative semirings. Added `exists_jetPrefixPresentation_of_vars_subset_range`, which constructs a prefix presentation from variable-support inclusion. The `FirstOrderFieldTailPresentation` wrapper and its `nonzero`, `specialization`, and `jetWeight` results use the generic `JetPrefixPresentation` nonzero, differential-specialization, and total-degree methods instead.

## `ArkLib/Data/Polynomial/Differential/OrderZeroPresentation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/TailBound.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Moved `orderZeroVariableEquiv`, `orderZeroAsPolynomial`, `orderZeroOfPolynomial`, `orderZeroAsPolynomial_orderZeroOfPolynomial`, and `orderZeroAsPolynomial_eval` into the generic differential-polynomial owner. Generalized the presentation and evaluation laws from fields to commutative semirings. Renamed `orderZeroOfPolynomial_jetWeight` to `orderZeroOfPolynomial_jetTotalDegree` and generalized it to commutative semirings and canonical `jetTotalDegree`. No listed source declaration was omitted from this presentation; the separate `singularAsPolynomial_eval` wrapper remained unnecessary because `remainingSpecializationHom_eq_eval` covers its use.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Factors/IrreducibleEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `ordinary_jetWeight_eq_degreeOf` to `jetTotalDegree_eq_jetDegree_zero`. The identity is stated through the canonical jet-degree API in the existing `OrderZeroPresentation` owner and replaces a duplicate local calculation. The acceptance case in `ArkLibTest/Data/Polynomial/Differential.lean` computes the jet degree of `orderZeroOfPolynomial (X ^ 2 + 1)` using this theorem.

## `ArkLib/Data/Polynomial/Differential/RationalTaylor.lean`

[DKTZ26], Appendix A.3, Lemma A.5. The declarations are ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/Numerator.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `TaylorExponentSufficient`, `TaylorExponentSufficient.mono`,
  `taylorExponentSufficient_two_mul`, `taylorExponentSufficient_two_mul_sub_three`, and
  `taylorExponentSufficient_firstOrder_tight` are unchanged, except that the source hypothesis
  `2 ≤ K` of `taylorExponentSufficient_two_mul_sub_three` is removed. The source's
  `firstOrder_tight_exponent_le_legacy` (`2 * D - 3 ≤ 2 * D - 1`) is not ported; it is `omega`.
* `initialJetSeparant`, `aeval_initialJetSeparant`, `rationalTaylorNumerator`,
  `rationalTaylorCoefficient`, `rationalTaylorCoefficient_initial`, and
  `rationalTaylorCoefficient_residual` are unchanged in content. `initialJetSeparant` is defined
  over any commutative semiring.
* `totalDegree_initialJetSeparant_le` and `totalDegree_rationalTaylorNumerator_le` are stated with
  the core `jetTotalDegree`. The source hypothesis `0 < jetTotalDegree Q` of the numerator bound is
  removed: when it fails the residual coefficients are constants and the bound still holds.
* `eq_rationalTaylorCoefficient_of_residual` is the induction inside the source's
  `rationalTaylorCoefficient_eq_solution`, separated from the fact that an actual polynomial
  solution satisfies the affine equations.
* `rationalTaylorCoefficient_residual_prefix` is new; it combines
  `rationalTaylorCoefficient_residual` with `aeval_universalTaylorResidual_coeff`.

* `solution_taylorCoefficient_residual` keeps the source statement over a commutative ring
  instead of a field. It is the case `Q(X, P, ...) = 0` of the new
  `taylorCoefficient_residual_eq`, which holds for every polynomial `P`.
* `rationalTaylorCoefficient_eq_solution` keeps the source statement; its proof is
  `eq_rationalTaylorCoefficient_of_residual` applied to the Taylor coefficients of `P`.

`eq_rationalTaylorCoefficient_of_residual`: The source applied this argument only to the Taylor coefficients of an actual solution; the
statement here isolates the algebra from the solution property.

## `ArkLib/Data/Polynomial/Differential/RationalTaylorAlgebra.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorNumerator.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`ReedSolomon.HiddenDerivative`; the new namespace is `PolynomialDifferential`.
`initialJetSeparantOver` is main's `initialJetSeparant`, and `map_initialJetSeparantOver` is
`map_initialJetSeparant` in `RationalTaylor.lean`. `map_universalTaylorJet`,
`map_universalTaylorResidual` and `map_universalTaylorResidual_coeff` are in
`TaylorResidual.lean`, and `map_optionEquivLeft` is in
`ToMathlib/MvPolynomial/RootContraction.lean`, re-exported through
`ToMathlib/MvPolynomial/PolynomialCoefficients.lean`; all of these need only a `CommSemiring`.
`commonTaylorNumeratorOver` takes the exponent `τ` explicitly, with no default `2K`, and no
longer takes `K`; `l` is a natural number instead of an element of `Fin K`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorSpecialization.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`map_rationalTaylorNumeratorOver_eq` keeps its name and mathematical contract in the destination owner module; it also handles polynomial evaluation as a field-valued algebra-map specialization.

## `ArkLib/Data/Polynomial/Differential/RationalTaylorBidegree.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorBidegree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`initialJetEquationOver_mem_restrictBidegree` and `initialJetSeparantOver_mem_restrictBidegree` become `initialJetEquation_mem_restrictBidegree` and `initialJetSeparant_mem_restrictBidegree` for the current `initialJetEquation` and `initialJetSeparant` APIs. The exponent and default-exponent forms of `commonTaylorNumeratorOver_mem_restrictBidegree` and `taylorAgreementEquationOver_mem_restrictBidegree` are each represented by one explicit-exponent theorem with a sufficiency proof. The agreement bound is stated for a received polynomial over `F[X]`. Separate coefficient-degree and jet-degree bounds support the rectangle results; the jet bounds use `jetTotalDegree`. Default-exponent wrappers are covered using `taylorExponentSufficient_two_mul`, and `flattenChallenge_jetDegree_le` is covered by `MvPolynomial.totalDegree_optionEquivRight`. The agreement-equation definition is supplied by main and retained unchanged; no source theorem remains blocked.

The shared coefficient and bidegree results are generalized in `ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean` and `ArkLib/ToMathlib/RingTheory/MvPolynomial/Bidegree.lean`: `source_mem_restrictBidegree_mono` becomes `mem_restrictBidegree_mono` for arbitrary `MvPolynomial` coefficients; private `challengeHeightLE_clearedSubstitution` becomes `CoeffNatDegreeLE.clearedSubstitution`, generalized to commutative semirings; and `flattenChallenge_challengeDegree_le` becomes `weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le`, generalized to arbitrary variable types and nontrivial commutative semirings. `flattenChallenge_mem_restrictBidegree` is likewise generalized to those variable and semiring assumptions. The acceptance cases are in `ArkLibTest/Data/Polynomial/Differential.lean`, `ArkLibTest/ToMathlib/MvPolynomial.lean`, and `ArkLibTest/ToMathlib/RingTheory/MvPolynomial.lean`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`initialJetEquationOver_mem_restrictDerivativeBidegree` became `PolynomialDifferential.initialJetEquation_mem_restrictCappedBidegree`. It now applies at arbitrary differential order and uses the destination capped-bidegree API.

`commonTaylorNumeratorOver_mem_restrictDerivativeBidegree` became `PolynomialDifferential.commonTaylorNumeratorOver_mem_restrictCappedBidegree`. It states the same mathematical bounds with the destination degree and membership APIs.

`degreeOf_taylorAgreementEquationOver_firstOrder` retains its name as `PolynomialDifferential.degreeOf_taylorAgreementEquationOver_firstOrder`. It keeps the same degree bound for arbitrary polynomial centers and evaluation points.

`taylorAgreementEquationOver_mem_restrictDerivativeBidegree` became `PolynomialDifferential.taylorAgreementEquationOver_mem_restrictCappedBidegree`. It states the same mathematical bounds with the destination degree and membership APIs.

`derivativeWeight_eq_piSingle` was not ported because it is a source-specific encoding helper. The destination capped-bidegree API bounds an indexed coordinate directly, and the existing `weightedTotalDegree_indexWeight_eq_jetDegree_one` supplies the needed first-order weighted-degree fact.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/DerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Generalized `symbolicSourceSeparant_mem_sourceCurveCutDerivativeBidegree` as `initialJetSeparant_mem_restrictCappedBidegree` for arbitrary differential order, with an explicit highest-jet degree cap.

## `ArkLib/Data/Polynomial/Differential/RationalTaylorDerivativeDegree.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeDegree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `degreeOf_initialJetSeparantOver_firstOrder` to `degreeOf_initialJetSeparant_le` and generalized it from fields to nontrivial commutative semirings. Added `degreeOf_rationalTaylorNumeratorOver_le` and `degreeOf_commonTaylorNumeratorOver_le` for arbitrary positive differential order over fields. `degreeOf_rationalTaylorNumeratorOver_firstOrder` and `degreeOf_commonTaylorNumeratorOver_firstOrder` keep their names as first-order specializations.

`flattenChallenge_degreeOf_le` was not given a wrapper because the existing weighted-degree identities already provide the coordinate-degree identity. The redundant `degreeOf_optionEquivRight_symm_le` declaration and its constant-coefficient test were removed.

## `ArkLib/Data/Polynomial/Differential/RationalTaylorJointDegree.lean`

Ported from `Symbolic/TaylorHeight.lean` and `Symbolic/TaylorDegree.lean` under the same source
directory. The `challengeHeightLE_*` lemmas are now `coeffNatDegreeLE_initialJetSeparant`,
`coeffNatDegreeLE_universalTaylorJet` and `coeffNatDegreeLE_universalTaylorResidual`, and
`universalTaylorResidual_coeff_natDegree_le` is now
`coeffNatDegreeLE_universalTaylorResidual_coeff`. `jointTotalDegree_initialJetSeparantOver_le`
is now `jointTotalDegree_initialJetSeparant_le`, and `totalDegree_initialJetSeparantOver_le` is main's
`totalDegree_initialJetSeparant_le`; the first takes the hypothesis `jetTotalDegree Q ≤ v` in
place of a bound on `Q.weightedTotalDegree (i.elim 0 1)`. The suffixes `_of_coeff_height` and
`_of_source` are now `_le_of_natDegree_coeff_le` and `_le_of_coeffNatDegreeLE`.
`jointTotalDegree_commonTaylorNumeratorOver_le_of_exponent` is now
`jointTotalDegree_commonTaylorNumeratorOver_le`, with hypothesis `2 * (l - r) - 1 ≤ τ`, and
`_of_source_and_exponent` is now `_le_of_coeffNatDegreeLE`. The hypothesis `0 < v` is dropped.
The default-exponent corollaries `jointTotalDegree_commonTaylorNumeratorOver_le` (at `2K`) and
`…_of_source` are derived in the acceptance test through `taylorExponentSufficient_two_mul`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Degree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The caller of `CoeffNatDegreeLE.clearedSubstitution` is adapted to pass the same parameter bound for both `h` and the new independent coefficient bound `a`. The source `totalDegree_rationalTaylorNumeratorOver_le` is covered by the generalized `totalDegree_rationalTaylorNumeratorOver_le_of_jet` theorem.

## `ArkLib/Data/Polynomial/Differential/RecursiveCount.lean`

Ported from `ArkLib/Data/Polynomial/Differential/RecursiveCount.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`RegularBranchRatBudget`, `boundedSolution_recursive_counting_totalJetDegree`, and `boundedSolution_card_le_sq_totalJetDegree` keep their names. The regular-branch budget and recursive counting theorems use explicit per-jet cast nonvanishing, and the square-bound corollary uses the current explicit cast contract.

## `ArkLib/Data/Polynomial/Differential/RegularIteration.lean`

Ported from ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, where the statements were
over a field in the namespace `ReedSolomon.HiddenDerivative`. They mention no Reed–Solomon object
and are stated here over a commutative ring in `PolynomialDifferential`.

From `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Regular/Iteration.lean`:

* `hasseCoeffAt_add_order_eq_of_regular_solutions_of_eq_below` becomes
  `taylor_coeff_eq_of_taylor_coeff_eq_of_isLeftRegular`. The source assumed that `P` and `P'`
  solve `Q = 0`, that `S(P) ≠ 0`, and that `k + r ≤ D < ringChar F`. Here the two `k`-th residual
  coefficients are assumed equal and the slope `(k + r choose r) S(P)` left-regular. The proof uses
  the affine law directly instead of the uniqueness of the one-step lift, so a left-regular slope
  suffices where the lift needs a unit. The exact identity behind it,
  `coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq`, is new.
* `eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq` becomes
  `eq_of_polynomialJet_eq_of_isLeftRegular`: equal residuals replace the two solution hypotheses,
  and left-regular slopes for `r < k + r ≤ D` replace `IsRegularJet` and `D < ringChar F`.
* `eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq_of_isHighestActiveJet` and
  `BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet` are generalized in the same way.
* The congruence lemmas were ported in `ArkLib.Data.Polynomial.Differential.RegularLift`.

From `.../RootFinding/Regular/JetPrefix.lean`:
`existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet` keeps its name; a unit slope
replaces `IsRegularJet` and `k + s ≤ D < ringChar F`. The perturbation is written
`P + hassePerturbation center γ (k + s)`, as in `RegularLift`.

The field forms with `IsRegularJet` and a characteristic bound are derived in the acceptance tests
from `Polynomial.natCast_choose_ne_zero_of_lt_charP`.

## `ArkLib/Data/Polynomial/Differential/RegularLift.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Regular/` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, where everything was stated over a field in
the namespace `ReedSolomon.HiddenDerivative`. None of it mentions a Reed–Solomon object, so it is
stated here over a commutative ring in the namespace `PolynomialDifferential`, next to
`shiftedJetSubstitution`.

From `Lifting.lean`:

* `shiftedJetValues`, `regularLiftIncrement`, `shiftedJetSubstitution_eq_eval₂Hom`,
  `X_pow_succ_dvd_regularLiftIncrement_of_ne_top` (here `_of_ne_last`) and
  `regularLiftIncrement_top` (here `_last`) keep their statements.
* The source's `regularLiftCandidate center γ k r P` is not defined; statements use
  `P + hassePerturbation center γ (k + r)` directly. Accordingly
  `shiftedJetValues_regularLiftCandidate`,
  `X_pow_succ_dvd_shiftedJetSubstitution_regularLiftCandidate_sub`,
  `coeff_shiftedJetSubstitution_regularLiftCandidate` and
  `X_pow_dvd_shiftedJetSubstitution_regularLiftCandidate` become the `_add_hassePerturbation`
  statements. The last one no longer assumes `0 < k`.
* `existsUnique_regularLiftCoefficient` replaces the two field hypotheses
  `(k + r choose r) ≠ 0` and `S ≠ 0` by the single hypothesis that their product is a unit.
  `existsUnique_regularLiftCoefficient_centered` is the source's `_centered` form.
* `eval_zero_shiftedJetSubstitution_separant` is `coeff_zero_shiftedJetSubstitution` in
  `ArkLib.Data.Polynomial.Differential.ShiftedJet`; `X_pow_dvd_regularLiftIncrement_top` is
  inlined; `X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd` and
  `X_pow_dvd_taylor_iff_X_sub_C_pow_dvd` are in `ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting`.
* The `ringChar` wrappers `existsUnique_regularLiftCoefficient_of_le_of_lt_ringChar`,
  `existsUnique_regularLiftCoefficient_centered_of_le_of_lt_ringChar` and the wrappers taking
  `IsRegularJet` are not ported. `Polynomial.natCast_choose_ne_zero_of_lt_charP` gives the
  binomial hypothesis below a prime characteristic.

From `Iteration.lean`: `X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd` and
`X_sub_C_pow_dvd_differentialSpecialization_sub_of_X_sub_C_pow_add_dvd` keep their statements;
its private evaluation lemma is `MvPolynomial.dvd_eval₂Hom_sub_eval₂Hom`. The uniqueness theorems
of `Iteration.lean` are deferred; they need `IsRegularJet`, `IsHighestActiveJet` and
`BoundedSolution` from `RootFinding/Regular/JetPrefix.lean` and the root-finding core.

`coeff_shiftedJetSubstitution_eq_centeredCoefficientPrefix_add` is the argument of the source's
`solution_taylorCoefficient_residual` (`RootFinding/Taylor/Numerator.lean`) without the
assumption that `P` is a solution.

`existsUnique_regularLiftCoefficient`: The regular one-step lift of [Kop15, Theorem 4.4].

## `ArkLib/Data/Polynomial/Differential/RetainedCurve.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/RetainedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Moved the retained positive-factor equation API into the `PolynomialDifferential` namespace. Renamed `flattenedRootFirst (flattenFirstOrderChallenge Q)` to `challengeRetainingRootFirst`, and renamed `flattenChallenge_fromFlattenedRootFirst` to `flattenedCoordinates_fromFlattenedRootFirst`. The coordinate recovery function, `positiveCurveEquation`, `positiveCurveEquation_ne_zero`, `curveJetReindex`, `curveJetView`, and `curveJetView_totalDegree` keep their names. Renamed `positiveCurveEquation_jetWeight` to `positiveCurveEquation_jetTotalDegree_eq_curveJetView`, and generalized its view-degree identity to canonical `jetTotalDegree` after coordinate recovery. Added the public round-trip theorem `fromFlattenedRootFirst_rootFirstChallenge` from the source coordinate recovery and flattening identity. Renamed `positiveCurveEquation_jetWeight_le` to `positiveCurveEquation_jetTotalDegree_le` and removed its nonzero-input assumption. The `positiveCurveEquation_yOneDegree` equality keeps its name; `positiveCurveEquation_yOneDegree_le` was generalized by removing its nonzero-input assumption. Renamed `positiveCurveEquation_challengeHeightLE` to `positiveCurveEquation_coeffNatDegreeLE` without changing the coefficient-height bound.

Did not port `flattenChallenge_weightedTotalDegree_eq` because the generic `weightedTotalDegree_optionEquivRight` result supplies that wrapper directly. Did not port `flattenedRootJetWeight` because `curveJetView_totalDegree` expresses the weight through canonical `jetTotalDegree`.

## `ArkLib/Data/Polynomial/Differential/RootPresentation.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Factors/RootPresentation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `ReedSolomon.HiddenDerivative`.

`ordinaryRootPresentation`, `natDegree_ordinaryRootPresentation`, `ordinaryRootPresentation_ne_zero`, `irreducible_ordinaryRootPresentation`, `derivative_ordinaryRootPresentation`, `ordinaryRootPresentation_monomial`, `degreeX_ordinaryRootPresentation_le`, `eval_ordinaryRootPresentation`, `ordinary_separant_ne_zero_of_resultant_eval_ne_zero`, and `exists_exceptional_ordinary_separant` keep their names in namespace `PolynomialDifferential`.

`separableResultant_ordinaryRootPresentation_ne_zero` is renamed to `resultant_derivative_ordinaryRootPresentation_ne_zero` and generalized to the generic padded derivative resultant; it no longer needs a separate positive-degree assumption. The challenge-height bound uses `MvPolynomial.CoeffNatDegreeLE`.

Nothing was deferred or left unported. The source separable-resultant declaration is covered by the renamed theorem using the current padded resultant API, so no duplicate wrapper was added.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Factors/RootPresentation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ordinaryRootPresentation`, `natDegree_ordinaryRootPresentation`, `ordinaryRootPresentation_ne_zero`, `irreducible_ordinaryRootPresentation`, `derivative_ordinaryRootPresentation`, `ordinaryRootPresentation_monomial`, `degreeX_ordinaryRootPresentation_le`, and `eval_ordinaryRootPresentation` keep their names and are generalized from fields to commutative rings. The resultant and separant statements retain their field assumptions.

## `ArkLib/Data/Polynomial/Differential/ShiftedJet.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Identity.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `shiftedJetSubstitution`,
`shiftedJetSubstitution_X`, `shiftedJetSubstitution_Y_zero`, `shiftedJetSubstitution_Y_succ`,
`taylorAlgHom_comp_differentialSpecializationHom`, and `taylor_differentialSpecialization`. The
source stated them over a commutative ring in the namespace `ReedSolomon.HiddenDerivative`; they
mention no Reed–Solomon object, so they are stated here over a commutative semiring, next to the
differential specialization they translate. Nothing is deferred.

`coeff_zero_shiftedJetSubstitution` generalizes the source's
`eval_zero_shiftedJetSubstitution_separant` in
`.../HiddenDerivative/RootFinding/Regular/Lifting.lean` from the separant over a field to any
differential polynomial over a commutative semiring.

## `ArkLib/Data/Polynomial/Differential/TaylorChart.lean`

Merges `Taylor/Chart.lean` and `Taylor/Cuts.lean` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `ReedSolomon.HiddenDerivative`; the new
namespace is `PolynomialDifferential`. The common exponent `τ` is always an explicit argument
with no default `2K`, and `commonTaylorNumerator` no longer takes `K`. Each source pair of a
default-exponent theorem and an `_of_exponent` theorem is one theorem taking
`TaylorExponentSufficient r K τ` or `2 * (l - r) - 1 ≤ τ`; the `2K` case is
`taylorExponentSufficient_two_mul`. `totalDegree_commonTaylorNumerator_le` drops the source's
`0 < v` hypothesis. Renamed: `initialJetEquation_ne_zero_of_separant_ne_zero` (from
`Geometry/InitialGeometry.lean`) to `initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero`,
`initialJetEquation_solution` to `aeval_initialJetEquation_polynomialJet`,
`commonTaylorNumerator_solution` to `aeval_commonTaylorNumerator` together with
`rationalTaylorCoefficient_eq_solution`,
`rationalTaylorMap_eq_solution` to `rationalTaylorMap_polynomialJet`,
`degree_rationalTaylorPolynomial_lt_of_high_cuts` to `degree_rationalTaylorPolynomial_lt`,
`taylorAgreementEquation_solution` to `aeval_taylorAgreementEquation` together with
`rationalTaylorPolynomial_polynomialJet`,
`polynomialJet_agreement_cut_iff` (from `Geometry/SolutionGeometry.lean`) to
`taylorAgreementEquation_eq_zero_iff` together with `rationalTaylorPolynomial_polynomialJet`,
`eq_of_high_cuts_and_agreement_cuts` to `eq_of_highTaylorCuts_of_agreement`, which takes
`Set.InjOn domain T` and `k ≤ T.card` instead of an embedding `Fin n ↪ F` with `T.card = k`.
`rationalTaylorCutDegreeBound` comes from `Geometry/HighCutGeometry.lean` with `τ` in place of
`2K`.

## `ArkLib/Data/Polynomial/Differential/TaylorChartBaseChange.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/SolutionExtension.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_common_regular_center_extension` is now `exists_forall_jetEvaluation_ne_zero_map`. It is generalized to a commutative semiring source, an infinite domain target, an explicit injective map, and any jet coordinate. The theorem maps the finite family and applies the existing infinite-domain geometry result.

Not ported: `exists_common_regular_center_algebraicClosure` is an algebra-map specialization of the generic theorem; the acceptance test checks that form.
Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorSpecialization.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`commonTaylorNumeratorOver_eq` is a new bridge identifying the algebra-valued common numerator with the field-valued definition. `map_commonTaylorNumeratorOver_eq` keeps its name and is generalized to the destination's natural Taylor index and arbitrary exponent, without a finite-index bound; it also handles polynomial evaluation as a field-valued algebra-map specialization.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/SolutionEmbedding.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`exists_regular_solution_jet_family_of_exponent` keeps its name and is generalized from `Fin n` to any finite coordinate type and from base-field pivots to pivots over the chart field. The theorem embeds bounded-degree regular solution families into an infinite extension field while preserving cardinality, the initial equation, high Taylor cuts, and received-word agreement lower bounds. It reuses ArkLib's regular-solution map and agreement-count results.

`exists_regular_solution_jet_family` is not ported because its default-`2K` exponent is a thin wrapper; use `exists_regular_solution_jet_family_of_exponent` with `taylorExponentSufficient_two_mul` when that exponent is needed. `totalJetDegree_map_eq` is covered by `PolynomialDifferential.jetTotalDegree_map_eq` in `BaseChange.lean`. `exists_forall_jetEvaluation_ne_zero_map` is retained in the combined module as the common-center theorem, but has no corresponding declaration in this unit's source snapshot.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/RegularCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finite_regular_solutions_card_le` → `card_le_of_regular_solutions_agreement`. The result allows any algebraically closed field extension and an explicit sufficient Taylor exponent, uses the sharp numerator `n - k + 1` and `jetTotalDegree`, and drops the positive-degree and positive-`k` assumptions.

Ported from `ArkLib/Data/Polynomial/Differential/TaylorChartBaseChange.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`regularBranchRatBudget_of_agreement` keeps its name and now accepts any predicate characterized by degree and agreement constraints. `finite_agreement_solutions_card_le` was generalized to that predicate form and renamed `finite_solutions_card_le_sq_totalJetDegree_of_agreement`; the finite-family argument is owned by the generic differential layer.

`IsAgreementSolution` is represented by the existing `ReedSolomon.closePolynomialSet` membership condition and the generic agreement predicate. `jetTotalDegree_eq_weightedTotalDegree_elim` was not ported because it restates the existing weighted-degree API. `jetTotalDegree_le_of_reflTransGen_singularStep` and `jetTotalDegree_rename_jetPrefixEmbedding` were not ported because they already exist in `RecursiveCount.lean` and `PolynomialDifferential.JetPrefixPresentation`, respectively.

## `ArkLib/Data/Polynomial/Differential/TaylorChartAlgebra.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorCuts.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

`map_initialJetEquationOver` and `map_initialJetEquationOver_eq` → `map_initialJetEquation`, and
`aeval_map_initialJetEquationOver` → `aeval_map_initialJetEquation`; these generic mapping and
evaluation lemmas are placed in the existing `TaylorChart` module. These mappings were
generalized to commutative semirings and arbitrary ring maps, and the evaluation theorem to maps
between commutative semirings.

The declarations `taylorAgreementEquationOver`, `map_taylorAgreementEquationOver`,
`map_taylorAgreementEquationOver_eq`, `aeval_map_taylorAgreementEquationOver_of_exponent`,
`aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent`,
`degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent`, and
`aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent` keep their general statements.
The default-exponent twins were removed; callers pass `τ` and its sufficiency proof. The
agreement equation keeps the same mathematics and uses the destination common-exponent API.

Not ported: `initialJetEquationOver` is covered by the existing, more general `initialJetEquation`
in `TaylorChart`; `map_initialJetSeparantOver_eq` is covered by the existing
`map_initialJetSeparant` specialization theorem. Common-numerator field-specialization theorems
were already present in `TaylorChart`, so duplicate copies were removed from this module.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/FrobeniusCuts.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorCutDegree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`challengeHeightLE_initialJetEquationOver` becomes `coeffNatDegreeLE_initialJetEquation`, using the existing `CoeffNatDegreeLE` API. `jointTotalDegree_initialJetEquationOver_le` becomes `jointTotalDegree_initialJetEquation_le`, with the center generalized from a constant to any polynomial. `jointTotalDegree_initialJetEquationOver_le_of_source` becomes `jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE`, generalized to `CoeffNatDegreeLE` and `jetTotalDegree`.

The general agreement bound `jointTotalDegree_taylorAgreementEquationOver_le_of_exponent` keeps its name. The default-exponent specialization was removed; callers pass `τ := 2 * K` with `taylorExponentSufficient_two_mul` when they need that exponent. `jointTotalDegree_taylorAgreementEquationOver_le_of_source_and_exponent` becomes `jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE_and_exponent`; the source default-exponent bound was removed. These use `jetTotalDegree` and `CoeffNatDegreeLE` and require no positive-degree premise. `sparse_rationalTaylorPolynomial_of_symbolic_cuts` keeps its name and uses main's common-numerator reconstruction identity.

`totalDegree_initialJetEquationOver_le` is not ported because the existing, more general `PolynomialDifferential.totalDegree_initialJetEquation_le` covers it. The source `taylorAgreementEquationOver` definition and `aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent` are supplied by main under those destination names.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`symbolicSourceInitialEquation`, `symbolicSourceSeparant`, `symbolicSourceNumerator`, `symbolicSourceAgreement`, and `symbolicSourceReconstructionError` move to the `PolynomialDifferential` owner as `jointInitialJetEquation`, `jointInitialJetSeparant`, `jointCommonTaylorNumerator`, `jointTaylorAgreementEquation`, and `jointTaylorReconstructionError`. The equations keep their substance; the common numerator takes the exponent explicitly. `jointTaylorAgreementEquation` combines the two source agreement declarations and is defined using `taylorAgreementEquationOver`. `affinePairCurve` adds a polynomial-valued parametrization of the affine pair graph. The initial equation and separant use only a commutative semiring, and the affine-pair curve uses only a semiring.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Moved the joint-cut evaluation results into the polynomial differential owner and renamed `eval_jointInitialJetSeparant`, `eval_jointCommonTaylorNumerator`, and `eval_jointTaylorAgreementEquation` to `aeval_jointInitialJetSeparant`, `aeval_jointCommonTaylorNumerator`, and `aeval_jointTaylorAgreementEquation`, respectively. They specialize the challenge before evaluating the jet.

## `ArkLib/Data/Polynomial/Differential/TaylorChartGeometry.lean`

Ported from `Geometry/AgreementGeometry.lean`, `Geometry/SolutionGeometry.lean` and part of
`Geometry/InitialGeometry.lean` under the same source directory. Membership in a principal open
is written as `jet ∈ zeroLocus F I` together with `aeval jet S ≠ 0`.
`exists_common_regular_center` is now `exists_forall_jetEvaluation_ne_zero`, for any
differential polynomial over an infinite domain instead of the separant over a field.
`initialJetPrimeFamily_prime_open` is split into `isPrime_of_mem_initialJetPrimeFamily` and
`initialJetSeparant_notMem_of_mem_initialJetPrimeFamily`.
`eq_of_mem_principalOpen_of_highCuts_of_agreementFinset` is now
`eq_of_mem_zeroLocus_of_highTaylorCutsIdeal_le`,
`polynomialJet_injective_on_regular_solutions` is now `injOn_polynomialJet`,
`card_image_polynomialJet_regular` is now `card_image_polynomialJet`,
`polynomialJet_mem_highTaylorCuts` is now `polynomialJet_mem_zeroLocus_highTaylorCutsIdeal`, and
`polynomialJet_mem_regular_solution_locus` is now
`polynomialJet_mem_zeroLocus_initialJetEquation_sup_highTaylorCutsIdeal`.

Deferred: `Geometry/SolutionExtension.lean` and `Geometry/SolutionEmbedding.lean`, which need the
coefficient-map lemmas for differential specialization.

The Hilbert-degree statements of `Geometry/InitialGeometry.lean`:
`initialJetPrimeFamily_hilbertPolynomial_natDegree` is now
`natDegree_affineHilbertPolynomial_of_mem_initialJetPrimeFamily`,
`sum_initialJetPrimeFamily_affineDegree_mul_pow_le` is now
`sum_affineDegree_mul_pow_initialJetPrimeFamily_le`, and its `_le_totalJetDegree` variant is now
`sum_affineDegree_mul_pow_initialJetPrimeFamily_le_jetTotalDegree`. The first two drop the
source's `initialJetEquation ≠ 0` hypothesis, since a member of the family does not contain the
separant, and the third drops the nonzero-separant hypothesis. The helper
`initialJetEquation_ne_zero_of_initialJetSeparant_notMem` is new.

## `ArkLib/Data/Polynomial/Differential/TaylorChartIncidence.lean`

Ported from `Geometry/HighCutGeometry.lean` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, except `rationalTaylorCutDegreeBound`, which is in
`TaylorChart.lean`. The exponent `τ` is explicit, and each source pair of a default-exponent
theorem and an `_of_exponent` theorem is one theorem under `TaylorExponentSufficient r K τ`.

`highTaylorCutList` is `(List.range' k (K - k)).map (commonTaylorNumerator center Q τ)` in place
of the source's `toList` over the subtype `{l : Fin K // k ≤ l}`.
`commonTaylorNumerator_mem_highTaylorCutList` is now the characterization
`mem_highTaylorCutList`, `highTaylorCutsIdeal_le_of_highTaylorCutList_le` is now the equality
`span_setOf_mem_highTaylorCutList`, and `highTaylorCutList_totalDegree_le{,_of_exponent}` is
`totalDegree_le_of_mem_highTaylorCutList`, without `0 < v`.

`highTaylorPrimeFamily` is `Ideal.iteratedRetainedCutFamily` of `initialJetPrimeFamily` by the
cut list. `highTaylorPrimeFamily_spec` is split into `isPrime_of_mem_highTaylorPrimeFamily`,
`initialJetSeparant_notMem_of_mem_highTaylorPrimeFamily`,
`initialJetEquation_mem_of_mem_highTaylorPrimeFamily`,
`highTaylorCutsIdeal_le_of_mem_highTaylorPrimeFamily` and
`exists_mem_highTaylorPrimeFamily_of_regular`, the last for jets over any extension field.
`highTaylorPrimeFamily_hilbertPolynomial_natDegree_le` is now
`natDegree_affineHilbertPolynomial_le_of_mem_highTaylorPrimeFamily`, without
`initialJetEquation ≠ 0`, and `sum_highTaylorPrimeFamily_affineDegree_mul_pow_le{,_of_exponent}`
is `sum_affineDegree_mul_pow_highTaylorPrimeFamily_le`, without the nonzero-separant and `0 < v`
hypotheses. The source's `sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le` is main's
`sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le`.

`finite_regularHighCutJets_card_le{,_of_exponent}` is now `card_le_of_highTaylorCuts_of_agreement`.
It is main's `card_le_of_agreement_off_excluded_of_hypersurface` with no excluded set and
threshold `k`, in place of the source's `componentPoints`, `agreementIndices` and
`affineAgreementIncidence_bound`. The domain is an injective `ι → F` on any `Fintype ι` in place
of `Fin n ↪ F`, the agreement count is `Set.ncard`, `A ≤ n` is weakened to `A - k + 1 ≤ #ι`, and
`0 < k`, the nonzero-separant hypothesis and `0 < v` are dropped. The terminal step is the new
`ncard_setOf_taylorAgreementEquation_mem_lt`: over an algebraically closed field, a
positive-dimensional prime containing the high cuts and not containing the separant contains
fewer than `k` agreement equations at distinct points. The test derives the source statement,
with `Fin n ↪ F`, `τ = 2K`, `0 < k ≤ A ≤ n` and the subtype cut list, and shows that `r < K` and
`A - k + 1 ≤ #ι` are needed.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/SharpCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`finite_regularHighCutJets_card_le_sharp_of_exponent` and `finite_regularHighCutJets_card_le_sharp` are covered by `card_le_of_highTaylorCuts_of_agreement_sharp`. The theorem accepts any finite index type and an explicit sufficient Taylor exponent, uses `jetTotalDegree`, and does not require positive degree, positive `k`, or a global nonzero-separant hypothesis; regularity remains an assumption for each jet. The fixed `2 * K` case is covered by `taylorExponentSufficient_two_mul`, so `finite_regularHighCutJets_card_le_sharp` is not a separate declaration.

## `ArkLib/Data/Polynomial/Differential/TaylorIndexWeight.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/IndexWeight.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`ReedSolomon.HiddenDerivative`. `universalTaylorJet_indexWeight` is now
`universalTaylorJet_supportWeightOffset`, `universalTaylorResidual_indexWeight` is now
`universalTaylorResidual_supportWeightOffset`, and `firstOrder_jetIndexDegree` is now
`weightedTotalDegree_indexWeight_eq_jetDegree_one`. `indexWeight` and
`indexWeight_le_of_mem_universalTaylorResidual_coeff` keep their names.

## `ArkLib/Data/Polynomial/Differential/TaylorResidual.lean`

The support bounds are [DKTZ26], Appendix A.3, Lemma A.5. The declarations are ported from ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `universalTaylorJet`, `optionEquivLeft_universalTaylorJet`,
  `universalTaylorJet_mem_supportWeightLE`, `universalTaylorResidual`,
  `universalTaylorResidual_mem_supportWeightLE`, `weight_le_of_mem_universalTaylorResidual_coeff`,
  `weightedTotalDegree_universalTaylorJet_le`, `weightedTotalDegree_universalTaylorResidual_le`,
  and `totalDegree_universalTaylorResidual_coeff_le` from
  `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/Support.lean`. The
  source's `universalTaylorPolynomial` is not a separate definition; the jet identity states the
  explicit sum. Degree bounds use the core `jetTotalDegree`.
* `denominator_weight_le_of_mem_universalTaylorResidual_coeff` from
  `.../RootFinding/Taylor/Denominator.lean`, with the source's `0 < h` removed and the length
  `r + h` relaxed to any `K ≤ r + h`. The arithmetic step is `Finsupp.weight_two_mul_sub_one_le`.
* `map_optionEquivLeft_universalTaylorResidual` and `aeval_universalTaylorResidual_coeff` replace
  `specializeTaylorCoefficients_universalTaylorResidual` from `.../Taylor/SupportEvaluation.lean`
  and `aeval_universalTaylorResidual_coeff` from `.../Taylor/Numerator.lean`. The source stated
  them with `shiftedJetSubstitution` from `.../Interpolation/Local/Identity.lean`; here the target
  is `taylor a (differentialSpecialization Q P)`, which that file proves equal
  (`taylor_differentialSpecialization`), and the prefix is `Polynomial.centeredCoefficientPrefix`.

## `ArkLib/Data/Polynomial/Differential/Types.lean`

The definitions are adapted, with permission, from `kz99/rs-ld-mca` at revision
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` and were developed in the Reed--Solomon
beyond-Johnson source snapshot at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

## `ArkLib/Data/Polynomial/DivisorReconstruction.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AnchoredReconstruction.lean`: the theorems
`cubicAnchorReconstruct_degree_lt`, `cubicAnchorReconstruct_eval_anchors` and
`cubicAnchorReconstruct_eval_of_quotient` are stated there for the cubic divisor
`(X - s₁) (X - s₂) (X - z)` over a field. They are generalized here to an arbitrary divisor over
a semiring, commutative semiring and ring respectively, and the degree bound no longer assumes
`0 < k`. The cubic statements are in
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredReconstruction`.

## `ArkLib/Data/Polynomial/FrobeniusContraction.lean`

Merges `ArkLib/ToMathlib/Polynomial/FrobeniusContraction.lean` and
`ArkLib/ToMathlib/Polynomial/FrobeniusContractionFractionRing.lean` from the source. The hypotheses
`Fact p.Prime` and `p ≠ 0` are dropped; characteristic zero is handled in the proof.
`exists_frobeniusContraction_fractionRing` keeps six of the source's nine conjuncts; the dropped
ones are `Irreducible.isPrimitive`, `derivative_map` with `Polynomial.map_ne_zero_iff`, and
`natDegree_map_eq_of_injective`, and the acceptance test re-derives the nine-conjunct statement.
`irreducible_separable_map_fractionRing` is folded into that theorem.
`not_exists_expand_primePow_succ_of_derivative_ne_zero` is not ported.

`exists_irreducible_frobeniusContraction_expChar` is the univariate form of
`exists_frobeniusFactor_expChar` from `ArkLib/ToMathlib/MvPolynomial/FrobeniusFactor.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

## `ArkLib/Data/Polynomial/PointCollision.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/Probability/TwoPointPolynomialCollision.lean`:

* `collisionSet` and its separator machinery (`CandidatePair`, `pairLeft`, `pairRight`,
  `separatingCoordinate`, `separator`, `twoPointRootPairs`) are replaced by the event
  `¬ Set.InjOn (evalTuple x) S`. The source's set is a superset of this event chosen through a
  separating coordinate per pair; the event itself needs no choice and is the quantity used by the
  consumer. `card_twoPointRootPairs_le` and `card_collisionSet_le` are generalized to
  `card_le_of_evalTuple_eq` and `card_le_of_not_injOn_evalTuple`: any finite index type of points
  replaces the two points, any domain replaces the field, and any finite set of point tuples
  replaces the product of root sets. `mem_collisionSet_of_agree` and
  `eq_of_agree_of_not_mem_collisionSet` are the definition of `Set.InjOn`.
* `outsideDomain`, `card_outsideDomain`, `orderedDistinctPairs`, `card_orderedDistinctPairs`,
  `card_orderedDistinctPairs_outsideDomain`, `collisionRate` and `collisionRate_le` are replaced by
  `prob_not_injOn_evalTuple_le` (in `ArkLib.Data.Polynomial.PointCollisionProbability`), which
  holds for every finite sample space mapped injectively into point tuples. The ordered distinct
  outside-domain pairs are Mathlib's `Finset.offDiag` of the complement of the domain; that
  specialization, with the source's denominator, is
  `ReedSolomon.AnchoredAgreement.prob_not_injOn_candidateSet_offDiag_le`.

## `ArkLib/Data/Polynomial/PointCollisionProbability.lean`

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/Probability/TwoPointPolynomialCollision.lean`: these replace `collisionRate` and
`collisionRate_le`; see the module docstring of `ArkLib.Data.Polynomial.PointCollision`.

## `ArkLib/Data/Polynomial/ResultantDegree.lean`

`degreeX_derivative_le` of `ArkLib/ToMathlib/Polynomial/SeparableResultant.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` is `Polynomial.Bivariate.degreeX_derivative_le`.
`natDegree_separableResultant_le` is `natDegree_resultant_le_degreeX`, and
`natDegree_separableResultant_le_of_height` is `natDegree_resultant_derivative_padded_le`, which
bounds by `degreeX P` and needs no `0 < b`; the acceptance test derives both source forms.

## `ArkLib/Data/Polynomial/ResultantSpecialization.lean`

## Relation to the source definitions

The source defines `separableResultant A b := resultant A.derivative A (b - 1) b` for
`A : R[X][X]`, and `paddedDerivativeResultant A b` by the same formula for `A : R[X]`. This file
uses neither definition and writes `resultant f f.derivative m (m - 1)`, the argument order used
elsewhere on ArkLib main. The two orders give the same value: `resultant_comm` introduces the sign
`(-1) ^ (m * (m - 1))`, and `m * (m - 1)` is even (`resultant_comm_sub_one`). A source statement
about `separableResultant A b` at a point `w` is the case `R := F[X]`, `f := A`, `m := b`,
`φ := evalRingHom w` of the statements here.

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `ArkLib/ToMathlib/Polynomial/SeparableResultant.lean`:
  `eval_derivative_ne_zero_of_separableResultant_eval_ne_zero`,
  `eval_derivative_ne_zero_of_separableResultant_map_ne_zero` and
  `specialization_separable_of_separableResultant_eval_ne_zero`;
* `ArkLib/ToMathlib/Polynomial/PaddedDerivativeResultantCommonRoot.lean`:
  `paddedDerivativeResultant_map_eq_zero_of_common_root`;
* `ArkLib/ToMathlib/Polynomial/DerivativeResultantDegree.lean`:
  `separableResultant_map_eq_zero_of_common_root`.

The source states these results separately for `R[X]` and `R[X][X]` and assumes `IsDomain` for
the rings involved. The statements here hold over any commutative rings and for any declared
degrees.

Not ported in this file: the total-degree bounds `natDegree_separableResultant_add_sq_le*` and
`natDegree_separableResultant_le_totalDegree*` of `DerivativeResultantDegree.lean`, which are in
`ArkLib.Data.Polynomial.ResultantDegree`; the entry point
`separableResultant_ne_zero_of_irreducible`, which is
`resultant_derivative_ne_zero_of_irreducible` in `ArkLib.Data.Polynomial.FractionFieldResultant`;
and the consumers `Ordinary/Factors/RootPresentation.lean` and `ContentExceptions.lean`.

`resultant_comm_sub_one`: Consequently the source definition
`separableResultant A b = resultant A.derivative A (b - 1) b` equals
`resultant A A.derivative b (b - 1)`.

## `ArkLib/Data/Polynomial/SpecializationAvoidance.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Polynomial/SeparableResultant.lean`:

* `finite_polynomial_specializations_eq_zero_card_le` is the case `R := F[X]`, `x := C` of
  `card_le_natDegree_of_injOn_of_eval_eq_zero`;
* `exists_map_evalRingHom_ne_zero_avoiding` and `exists_map_evalRingHom_ne_zero` are ported
  with their source statements and are derived here from the finite candidate form.

`exists_map_evalRingHom_ne_zero_avoiding`: This is the source statement.

`Polynomial.exists_exceptional_evaluation_family` from
`ArkLib/ToMathlib/Polynomial/SimultaneousRoots.lean` at the same revision is now
`Polynomial.exists_card_le_forall_eval_eq_zero_iff`, over a domain and for any index type with a
support finset in place of a field, `Fin n` and a count of zero members.

## `ArkLib/Data/Polynomial/TaylorPrefix.lean`

These declarations are ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/Numerator.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.  The owner here is independent of Reed--Solomon
codes and differential root finding.

## `ArkLib/ToMathlib/Algebra/Order/Floor/RelativeError.lean`

New. `Nat.one_sub_inv_mul_le_floor` and `Nat.div_floor_le_div_sub_one` factor out the floor-error
step of the source's `*_floor_bounds` lemmas.

## `ArkLib/ToMathlib/Analysis/ExponentialStaircase.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Analysis/ExponentialStaircase.lean`: `Real.sum_staircase_mul_exp_le`, with the
same statement. Its source consumer (`RatePartition/RankEstimate.lean`) is not yet ported.

## `ArkLib/ToMathlib/Analysis/Simplex/CenteredMoments.lean`

Generalizes the centered moments of `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/`
`Interpolation/WeightedSupport/Moments.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source's `integral_normalizedRadius`,
`integral_normalizedRadius_sq` and `integral_normalizedRadius_cube` state these moments for the
weights `1, …, n` and coefficients `1`, scaled by `1 / t`; here the weights and coefficients are
arbitrary, the index type is any `Fintype`, and the budget hypothesis is weakened from `0 < W`.
The source's `integrable_weighted_probability` is `IntegrableOn.integrable_cond` composed with
`ContinuousOn.integrableOn_weightedSimplex`. The hidden-derivative specializations are in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments`.

`setAverage_weightedSimplex_linearForm_sub_mean_sq_le` generalizes
`ReedSolomon.HiddenDerivative.weightedSimplex_centeredRadius_sq_le_harmonic` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at the same revision. The source states the case of weights `i + 1` on
`Fin n` and coefficients `1`; here the weights are arbitrary positive reals, the coefficients are
arbitrary, and there is no budget hypothesis. The specialization keeps the source name in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral`.

## `ArkLib/ToMathlib/Analysis/Simplex/MaxCoordinate.lean`

Ported from the largest-coordinate part of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/Moment.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, with `simplexMaximum` written as
`univ.sup' univ_nonempty x` and `simplexMaximumExpectation` as a set average.
`volume_standardSimplex_coordinate_ge` is now `volume_real_standardSimplex_inter_le_apply`;
`volume_centeredSimplexMaximum_gt` is now
`volume_real_standardSimplex_one_inter_lt_mul_sup'_sub_log_le`, for every `t`;
`simplexMaximumExpectation_id` and `simplexMaximumExpectation_sq` are now
`setAverage_standardSimplex_sup'` and `setAverage_standardSimplex_sup'_sq`; and the general half
of `simplexMaximumExpectation_upperTail_sq_le` is
`setAverage_standardSimplex_one_max_mul_sup'_sub_log_sub_sq_le`, for every `a`.
`centeredSimplexMaximum`, `centeredMaximumUpperTail` and its continuity lemma are written out.

## `ArkLib/ToMathlib/Analysis/Simplex/Moments.lean`

Ports the declarations of `ArkLib/ToMathlib/Analysis/Simplex/Moments.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, generalized as follows.

* `integral_standardSimplex_linearForm`, `integral_standardSimplex_linearForm_sq`, and
  `integral_standardSimplex_linearForm_cube` (degrees `1`, `2`, `3` over `Fin n`) are the
  cases `k = 1, 2, 3` of `integral_standardSimplex_linearForm_pow`, for any `Fintype` and any
  degree; the source's power-sum forms follow with `MvPolynomial.two_mul_eval_hsymm_two` and
  `MvPolynomial.six_mul_eval_hsymm_three`. The private coordinate integrals
  `integral_coordinate`, `integral_coordinate_mul`, `integral_coordinate_mul_mul` and the
  multiplicity counts `sum_pair_multiplicity`, `sum_triple_multiplicity` are replaced by the
  multinomial theorem and Mathlib's `hsymm`.
* `integral_weightedSimplex_radius`, `_sq`, `_cube` (weights `i + 1`, coefficients `1`) are the
  cases of `integral_weightedSimplex_linearForm_pow`, for arbitrary positive weights and
  coefficients.
* `weightedSimplexExpectation_radius`, `_sq`, `_cube` are `setAverage_weightedSimplex_succ_sum`,
  `_sum_sq`, `_sum_cube`, specializations of `setAverage_weightedSimplex_linearForm_pow`. The
  source's `weightedSimplexExpectation n W f` is Mathlib's set average
  `⨍ u in weightedSimplex w W, f u`, so no new definition is introduced.
* `weightedSimplexFiniteMeasure`, `weightedSimplexProbabilityMeasure`,
  `weightedSimplexFiniteMeasure_ne_zero`, and `weightedSimplexExpectation_eq_integral_probability`
  are replaced by Mathlib's conditional measure `volume[|weightedSimplex w W]`, with
  `isProbabilityMeasure_cond_weightedSimplex`; the source's expectation-as-integral lemma is
  Mathlib's `setAverage_eq'`.
* `simplexLinearForm`, `coefficientPowerSum`, `harmonicCoefficient`, `harmonicPowerSum`, and
  `weightedRadius` are written out as sums in the statements. `harmonicPowerSum_one` becomes
  Mathlib's `harmonic` in `setAverage_weightedSimplex_succ_sum`, and `harmonicPowerSum_eq_range`
  is `Fin.sum_univ_eq_sum_range`.
* `weightedRadius_standardToWeighted`, `continuous_weightedRadius`,
  `Continuous.integrableOn_weightedSimplex_posPart`, and `integrableOn_weightedRadius`, `_sq`,
  `_cube` are not ported. The first is the substitution inside `setIntegral_weightedSimplex`;
  the continuity and integrability lemmas are deferred to the slice that consumes them.

Deferred to later slices: centered moments (the variance of the linear form), the discrete
analogues in `ToMathlib/Combinatorics/DiscreteSimplex/{Moments,Variance}.lean`, and the
floor-cell transfers from these continuous moments to discrete counts.

`setAverage_weightedSimplex_succ_sum`: This is the source's
`weightedSimplexExpectation_radius`.

`setAverage_weightedSimplex_succ_sum_sq`: This is the source's
`weightedSimplexExpectation_radius_sq`.

`setAverage_weightedSimplex_succ_sum_cube`: This is the source's
`weightedSimplexExpectation_radius_cube`.

## `ArkLib/ToMathlib/Analysis/Simplex/MonomialIntegral.lean`

Ports `SimplexIntegration.integral_pow_mul_sub_pow` from
`ArkLib/ToMathlib/Analysis/Simplex/MonomialIntegral.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source assumed `0 ≤ L` and applied
`Complex.betaIntegral_scaled` directly; here the unit-interval case is a separate public theorem
and the scaling step `intervalIntegral.mul_integral_comp_mul_left` removes the sign hypothesis.
The source's repeated integral `monomialIntegral` and its formula `monomialIntegral_eq` are not
ported: the Fubini recurrence `MeasureTheory.setIntegral_standardSimplex_succ` evaluates the
Lebesgue integral directly, so the list-indexed intermediate has no remaining use.

## `ArkLib/ToMathlib/Analysis/Simplex/OrderedSimplex.lean`

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/OrderedSimplex.lean`
and the maximum part of `RatePartition/Moment.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `orderedSimplex` and `isCompact_orderedSimplex` keep
their names. `cumulativeCoordinates_nonnegative_iff` is now `nonneg_antitone_sum_Ici_iff`,
`sum_cumulativeCoordinates` is now `sum_sum_Ici_eq`, `weightedSimplex_eq_cumulative_preimage` is
now `weightedSimplex_succ_eq_preimage_orderedSimplex`, and
`integral_weightedSimplex_comp_cumulative` is now
`setIntegral_weightedSimplex_succ_comp_suffixSum`. `cumulativeMatrix`, `cumulativeCoordinates`,
`cumulativeLinearEquiv`, `permuteCoordinates`, `permutationChamber` and their lemmas are private.
`simplexMaximum_eq_zero_of_antitone` is now `sup'_univ_eq_apply_zero_of_antitone`,
`simplexMaximum_permute` is now `sup'_univ_comp_perm`, `integral_standardSimplex_maximum` is now
`setIntegral_standardSimplex_comp_sup'`, `simplexMaximumExpectation_eq_weightedRadius` is now
`setAverage_standardSimplex_comp_sup'`, and `weightedSimplexExpectation_eq_orderedHead` is now
`setAverage_weightedSimplex_succ_sum_eq_orderedSimplex`. `continuous_simplexMaximum`,
`simplexMaximum_le_iff` and `le_simplexMaximum` are `Continuous.finset_sup'_apply`,
`Finset.sup'_le_iff` and `Finset.le_sup'`.

## `ArkLib/ToMathlib/Analysis/Simplex/VolumeIntegral.lean`

Ports `SimplexIntegration.standardSimplex`, `isClosed_standardSimplex`,
`isCompact_standardSimplex`, `integrableOn_simplexMonomial`, `integral_standardSimplex_succ`,
`integral_standardSimplex_eq_monomialIntegral`, `integral_standardSimplex_eq`, and
`volume_standardSimplex` from `ArkLib/ToMathlib/Analysis/Simplex/VolumeIntegral.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source indexed coordinates by `Fin n`;
here the index type is any `Fintype`, with `Fin (n + 1)` kept only for the Fubini recurrence.
The source's recurrence was specific to monomials; `setIntegral_standardSimplex_succ` holds for
any integrable function and needs no sign condition on `L`. Compactness also holds for `L < 0`.
The source's `simplexMonomial` is written out in the statement, `integrableOn_simplexMonomial`
becomes the general `ContinuousOn.integrableOn_standardSimplex`, and
`integral_standardSimplex_eq_monomialIntegral` is not ported because the Dirichlet integral is
proved without the repeated-integral intermediate. The ENNReal volume
`volume_standardSimplex` is new. Deferred to later slices: linear-form moments, weighted radius,
and expectations (`Simplex/Moments.lean`), the ordered-simplex and moment files under
`HiddenDerivative/Parameters/RatePartition/`, and the floor-cell transfers
(`Interpolation/*/FloorTransfer.lean`).

## `ArkLib/ToMathlib/Analysis/Simplex/WeightedVolume.lean`

Ports `SimplexIntegration.coordinateWeight`, `weightedSimplex`, `weightedToStandard`,
`standardToWeighted`, `weightedStandardLinearEquiv`, `weightedSimplex_eq_preimage`,
`weightedSimplex_eq_image`, `isCompact_weightedSimplex`, `Continuous.integrableOn_weightedSimplex`,
`ContinuousOn.integrableOn_weightedSimplex`, `weightedToStandard_det`,
`integral_weightedSimplex_eq_standardSimplex`, and `volume_weightedSimplex` from
`ArkLib/ToMathlib/Analysis/Simplex/AffinePushforward.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source fixed the index type `Fin n` and the
weights `coordinateWeight i = i + 1`; here the index type is any `Fintype` and the weights are
any positive reals, so the Jacobian is `∏ i, w i` instead of `n!`. The source's
`volume_weightedSimplex` is the specialization `volume_real_weightedSimplex_succ`. The diagonal
maps and their determinant are private: the public change-of-variables theorem writes the inverse
map `t ↦ (t i / w i)ᵢ` explicitly. `Continuous.integrableOn_weightedSimplex` follows from
`ContinuousOn.integrableOn_weightedSimplex` by `Continuous.continuousOn`. The weighted Dirichlet
integral and the ENNReal volume are new. The file name records that the change of variables is
diagonal linear, not affine. Deferred to later slices: the weighted-radius moments and
expectations in `Simplex/Moments.lean`, which consume `setIntegral_weightedSimplex`.

`volume_real_weightedSimplex_add_le_mul_exp` is the general form of the volume estimate inside the
source's `ReedSolomon.HiddenDerivative.volume_weightedSimplex_add_choose_le_exp` (in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at the same revision), which enlarges the budget by `r + (n + 1).choose 2` for
the weights `i + 1`. Here the weights are arbitrary positive reals and `r` is any real number.

`volume_real_weightedSimplex_succ`: This is the source's `volume_weightedSimplex`.

`weightedSimplexExpectation_scale` of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/Moment.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` is replaced by
`setAverage_weightedSimplex_mul`, with `Set.smul_weightedSimplex`,
`setIntegral_weightedSimplex_mul` and `volume_real_weightedSimplex_mul`, for arbitrary weights.

## `ArkLib/ToMathlib/Analysis/SpecificLimits/GeometricBounds.lean`

These generalize lemmas of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/RankBudget.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which were stated over `ℝ`:

* `localRank_geometric_sum_le` and `localRank_weighted_geometric_sum_le` are
  `sum_range_pow_succ_le_div_one_sub` and `sum_range_natCast_succ_mul_pow_succ_le`, over a
  linearly ordered field and proved by closed forms instead of `tsum`.
* `localRank_linear_geometric_sum_le` is `sum_range_linear_mul_pow_succ_le` at `a = 1 / d`,
  `b = 1`, stated for arbitrary nonnegative `a` and `b`.
* `localRank_exp_geometric_ratio_le` and `localRank_exp_weighted_geometric_ratio_le` are
  `Real.exp_neg_div_one_sub_exp_neg_le` and `Real.exp_neg_div_one_sub_exp_neg_sq_le`, without the
  hypothesis `0 < x`.
* `localRank_linear_exp_sum_le` is `Real.sum_range_linear_mul_exp_neg_pow_succ_le` at `a = 1 / d`,
  `b = 1`.
* The ceiling estimate inside `localRank_ceilDiv_le` is `Nat.cast_ceilDiv_le_div_add_one`.
* The exponential envelope inside `localRank_weightedHigherJetCount_le_exp` is
  `Real.add_pow_le_pow_mul_exp`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/GeometricCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Renamed `geometric_ratio_le` to `agreementGap_geometricRatio_le` and `geometric_count_le_manuscript_bound` to `geometricCount_le_of_agreementGap`. Generalized both conclusions from `ℝ` to any linearly ordered field; the count theorem retains its rational count premise. The characteristic-based binomial pivot condition is covered by `PolynomialDifferential.natCast_choose_ne_zero_of_ringChar`, specialized at each index and combined with binomial symmetry, so it was not ported. No Reed–Solomon wrapper was added because the numerical statements have no Reed–Solomon-specific data.

## `ArkLib/ToMathlib/BigOperators/Intervals.lean`

The source's private sums `automatic_sum_range_cast` and `automatic_sum_range_sq_cast` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder/AutomaticRecipe.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` are now
`Finset.sum_range_natCast_mul_two` and `Finset.sum_range_natCast_sq_mul_six` over any commutative
ring.

## `ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean`: `CubicStaircase.count`,
`CubicStaircase.Slot`, `CubicStaircase.card_slot`, `CubicStaircase.Slot.exponents`,
`CubicStaircase.Slot.exponents_injective`, `CubicStaircase.Slot.weighted_degree_lt`,
`CubicStaircase.six_mul_sum` and `CubicStaircase.count_ge_cubic` are ported with the same
statements. `CubicStaircase.cube_div_six_le_sum` drops the source hypothesis `0 < L`. The
source's consumer is the weighted-support dimension bound (`WeightedSupport/Dimension.lean`),
which is not yet ported. The converse `CubicStaircase.Slot.exists_of_weighted_degree_lt` (every
triple below the cutoff comes from a slot) has no consumer in the source and is not ported. This
file is unrelated to the natural-number staircase `Finset.staircase` of
`ArkLib.Data.Finset.Staircase`, which counts pairs below a natural cutoff.

`CubicStaircase.cube_div_six_le_sum`: The source version assumes `0 < L`; that hypothesis is dropped here.

## `ArkLib/ToMathlib/Combinatorics/Enumerative/DoubleCounting.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `AffineHilbert.finiteAgreementIncidence_lower_sharp`
  (`ArkLib/ToMathlib/AlgebraicGeometry/Incidence/SharpRatio.lean`) is
  `Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow` with the index type `Fin n`
  generalized to an arbitrary finite type; its sum over `univ.filter (· ∉ Bad)` is written here as
  a sum over `Badᶜ`. `Finset.card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff` further replaces
  `univ` by an arbitrary `t : Finset β`.
* `AffineHilbert.finiteAgreementIncidence_lower`
  (`ArkLib/ToMathlib/Combinatorics/FiniteAgreementIncidence.lean`) is
  `Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow`, with the same generalization.
  The source proved it by repeating the sharp argument; here it is a corollary of the sharp form.

Deferred: `AffineHilbert.goodCuts_div_agreements_le` and the rest of the sharp-ratio layer, and
all consumers of these bounds (for example
`AffineHilbert.affineAgreementIncidence_bound_aux` in `Incidence/Agreement.lean`), which stay in
the source.

## `ArkLib/ToMathlib/Combinatorics/Enumerative/IncidenceProduct.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/DimensionSensitive.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`: the arithmetic of the incidence products.
`dimensionSensitiveIncidenceProduct` with `_succ`, `_nonneg` and `_eq_pow_mul` keep their names and
statements; they move from the namespace `AffineHilbert` to the root namespace. The hybrid product
is now the corresponding `incidenceProduct` specialization, so its boundary, one-factor,
two-factor and nonnegativity cases reduce through the general product and Mathlib's
`Finset.prod_empty` and `Finset.prod_range_succ`. `one_le_incidenceFactor` drops `T ≤ A`,
`dimensionSensitiveIncidenceProduct_le_one` drops `k ≤ A`, and
`hybridDimensionSensitiveIncidenceProduct_mono_dimension` and
`hybridDimensionSensitiveIncidenceProduct_le_two` drop `L ≤ A` and `k ≤ A`; truncated subtraction
makes these unnecessary. The theorem statements retain the displayed hypotheses `A ≤ n` and
`0 < b` for the corresponding incidence bounds.

`goodCuts_div_agreements_le_dimension` (from `DimensionSensitive.lean`) and
`goodCuts_div_agreements_le` (from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/SharpRatio.lean`,
listed as deferred in the section for `DoubleCounting.lean`) are not ported; both are
`natCast_sub_div_natCast_sub_le`, which compares `(n - m) / (A - m) ≤ (n - m') / (A - m')` for
`m ≤ m' < A ≤ n` in any linearly ordered field. The consolidated suite retains concrete
instances of the generic and shifted-ratio bounds; it no longer derives the two source-shaped
statements or includes hypothesis-necessity cases.

New, with no source counterpart: `incidenceProduct n A b T d`, the product over `t < d` of the
factor `((n - T t + 1) * b) / (A - T t + 1)` for a threshold function `T : ℕ → ℕ`, with
`incidenceProduct_nonneg`, `_const` and `_mono_dimension`. The empty-product, successor and
threshold-congruence cases use `Finset.prod_empty`, `Finset.prod_range_succ` and
`Finset.prod_congr` directly;
`dimensionSensitiveIncidenceProduct_eq_incidenceProduct` (thresholds `k - t`, under `d ≤ k + 1`,
`k ≤ A` and `A ≤ n`) and
`hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct` (thresholds
`if t = 0 then L else k + 1 - t`, unconditional); and `natCast_sub_mul_le_incidenceFactor_mul`,
the inequality `(n - j) * b ≤ ((n - T + 1) * b / (A - T + 1)) * (A - j)` for `j < T ≤ A ≤ n`,
which makes the incidence factor an admissible ratio in
`card_le_prod_of_agreement_off_excluded`. Its private helper `sub_mul_sub_add_one_le` is the
private lemma of the same name from PR #1008's `AgreementIncidence.lean`, moved here with its
variables renamed to `T` and `j`.

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/ProductBounds.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `AffineHilbert`.

`dimensionSensitiveIncidenceProduct_mono_dimension` keeps its name and is generalized from a
pairwise `r ≤ s` comparison to the `Monotone` property. `dimensionSensitiveIncidenceProduct_le_first_pow`
and `hybridDimensionSensitiveIncidenceProduct_min_le` keep their names and statements.
`hybridDimensionSensitiveIncidenceProduct_eq_factor_mul` keeps its name and is generalized from
`s ≤ k` to `s ≤ k + 1`. Nothing was deferred or left unported.

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/ProductBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `natCastRatio_le_div_of_scaled_lower_bound`, a general ordered-field ratio bound that replaces the private `midpoint_ratio_le_two_div` helper. The enumerative acceptance case checks it with `δ = scale = 1`, `n = 2`, `N = 1`, and `D = 2`.

## `ArkLib/ToMathlib/Combinatorics/Enumerative/MonomialCount.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/MonomialCounting.lean`, namespace
`MonomialHilbertCounting`: `degreeBall` becomes `Finsupp.degreeLEFinset`, `card_degreeBall` becomes
`Finsupp.card_degreeLEFinset`, `upperConeInBall` and `card_upperConeInBall` become
`Finsupp.card_filter_le_degreeLEFinset`, `standardExponentFinset` and its private
inclusion–exclusion lemma become `Finsupp.card_filter_forall_not_le_degreeLEFinset`,
`countingPolynomial` becomes `Finsupp.coneAvoidancePoly`, `countingPolynomial_eval_eq_card`
becomes `Finsupp.eval_coneAvoidancePoly`, and `exists_eventual_standardExponent_countingPolynomial`
becomes `Finsupp.exists_eval_eq_ncard_forall_not_le`. The source worked over `ℚ` with the
threshold `forbiddenThreshold B`, the largest degree of `T.sup id` over `T ⊆ B`; here the
coefficient field is any field of characteristic zero and the threshold is the single value
`degree (B.sup id)`, which bounds all of those degrees. The source's `forbiddenSup`,
`standardExponentSet` and the finset-level existence statement are not kept as separate
declarations.

## `ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean`: `QuadraticStaircase.count`,
`QuadraticStaircase.Slot`, `QuadraticStaircase.card_slot`, `QuadraticStaircase.Slot.exponents`,
`QuadraticStaircase.Slot.exponents_injective`, `QuadraticStaircase.Slot.weighted_degree_lt`,
`QuadraticStaircase.two_mul_sum` and `QuadraticStaircase.count_ge_quadratic` are ported with the
same statements. `QuadraticStaircase.square_div_two_le_sum` weakens the source hypothesis `0 < L`
to `0 ≤ L`. The source file imported `CubicStaircase` without using it; that import is dropped.
The source consumers (`RatePartition/Area.lean` and `PartitionSupport/Dimension.lean`) are not yet
ported.

## `ArkLib/ToMathlib/Finset/SumRangeFrom.lean`

The module retains no shifted-sum declarations. Use Mathlib's `Finset.sum_Ico_eq_sum_range` for
the interval form and `Finset.sum_range_add` for adjacent chunks; four- and two-chunk forms follow
by repeated splitting. The acceptance file is removed because it tested only these wrappers, and
there were no production consumers.

## `ArkLib/ToMathlib/LinearAlgebra/Matrix/InvertibleCombination.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/EvaluationDimension.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:
`coeff_mem_subalgebra_of_vandermonde_evaluations` is now `Submodule.mem_of_forall_sum_pow_smul_mem`,
stated for a submodule of any module over a field, with an injective `α : Fin c → K` in place of
an embedding `α : Fin c ↪ F` and `algebraMap` coefficients in a subalgebra. It is a corollary of
the new `Submodule.mem_of_forall_sum_smul_mem`, for any matrix with unit determinant over a
commutative ring. The consolidated suite retains a concrete `2 × 2` invertible-matrix instance
of `Submodule.mem_of_forall_sum_smul_mem`; it no longer derives the subalgebra statement or tests
determinant and point-separation boundary cases.

## `ArkLib/ToMathlib/LinearAlgebra/Matrix/PrimitiveKernel.lean`

The results are extracted and generalized from `ArkLib.ToMathlib.LinearAlgebra` at immutable
source revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. That revision proves
`Matrix.exists_primitive_kernel_vector_preserving_zero` and `Matrix.exists_primitive_kernel_vector`
in `PrimitivePolynomialKernel.lean`, and `Matrix.exists_primitive_kernel_vector_degreeLT` in
`ShiftedDegreeKernel.lean`, for polynomial matrices over a field with `Fin` indices. Each of them
bundles the gcd normalization with coordinate-wise degree, zero-preservation, and specialization
conclusions. Here the normalization holds over any Bézout ring with a normalized gcd and any row
index type, and the other conclusions are derived from `v = g • u` and from
`Ideal.comp_ne_zero_of_span_range_eq_top`. The degree-budget form of the normalization is
`Matrix.exists_primitive_kernel_vector_degreeLT` in
`ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight`.

The shifted and column families of the same revision,
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT` and
`Matrix.exists_primitive_mulVec_eq_zero_of_shifted_surplus` in `ShiftedDegreeKernel.lean`, and
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT`,
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank`, and
`Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus` in `ColumnDegreeKernel.lean`, are
ported in `ArkLib.ToMathlib.LinearAlgebra.ShiftedPolynomialKernelHeight`.

## `ArkLib/ToMathlib/LinearAlgebra/Matrix/RowBasis.lean`

The row selector is extracted and generalized from
`ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight` at immutable source revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, where it was named
`Matrix.exists_rows_fin_rank` and specialized both index types to `Fin`. The kernel transfer
replaces the span-induction argument inside
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` at the same revision, which was
specialized to polynomial matrices, `Fin` indices, and the rational function field.

## `ArkLib/ToMathlib/LinearAlgebra/Matrix/RowBlocks.lean`

Ported from the matrix rank argument in `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/WeightedSupport.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`Matrix.rank_prod_rows_le_sum` is a new generic rank bound for matrices whose row indices are products. It bounds the full matrix rank by the sum of the ranks of the blocks at each first-coordinate index. The generic helper is newly added for the weighted-support curve rank proof; there is no source declaration to leave out.

## `ArkLib/ToMathlib/LinearAlgebra/Matrix/SupportedRows.lean`

New general lemmas used for the supported-row restriction of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Symbolic/ReceivedLine.lean`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

## `ArkLib/ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean`

`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` is the exact natural-degree
  interface of the source theorem.

The theorem family is extracted and generalized from `ArkLib.ToMathlib.LinearAlgebra` at
immutable source revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The row-count theorem
generalizes `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` in
`PolynomialKernelHeight.lean`. The rank forms generalize
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in the same file and
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in
`PrimitivePolynomialKernel.lean`. Those source theorems fix the rank to be exactly `s`, measure it
over `RatFunc F`, and use `Fin` indices, so a caller with only `rank ≤ r` had to prove the
monotonicity of the bound itself. The source's row-count primitive theorem
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le` is the primitive rank form with
`s := Fintype.card rows` and the rank bound `Matrix.rank_le_card_height`.
`Matrix.exists_primitive_kernel_vector_degreeLT` generalizes the lemma of the same name in
`ShiftedDegreeKernel.lean` from `Fin` indices to arbitrary index types and drops its
specialization clause, which follows from `Ideal.comp_ne_zero_of_span_range_eq_top`.

The shifted and column families of the same revision,
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT` and
`Matrix.exists_primitive_mulVec_eq_zero_of_shifted_surplus` in `ShiftedDegreeKernel.lean`, and
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT`,
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank`, and
`Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus` in `ColumnDegreeKernel.lean`, are
ported in `ArkLib.ToMathlib.LinearAlgebra.ShiftedPolynomialKernelHeight`.

`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`: The immutable source states primitivity together with the specialization clause
`∀ {E} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0`. That clause follows from
the unit-ideal conclusion: apply `Ideal.comp_ne_zero_of_span_range_eq_top` with
`φ := Polynomial.eval₂RingHom ι z`, whose target `E` is nontrivial.

The row-count primitive form of the source,
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le`, is the case
`s := Fintype.card rows` with `hrank := Matrix.rank_le_card_height (M.map φ)`, which needs a
`Fintype` instance on the rows. -/

## `ArkLib/ToMathlib/LinearAlgebra/ShiftedPolynomialKernelHeight.lean`

This is the
  bridge from the source's two entry hypotheses to the single entry hypothesis used here.

  `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le` takes the source's
  hypotheses `hdegree` and `hzero` instead.
* `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT` and its source-shaped form
  `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le` add the

The theorems are extracted and generalized from `ArkLib.ToMathlib.LinearAlgebra` at immutable
source revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

* `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT` in `ShiftedDegreeKernel.lean` uses
  `Fin` indices and the two hypotheses `hdegree` (natural degree at most the weight difference
  when it is nonnegative) and `hzero` (zero when it is negative). Here the indices are arbitrary
  finite types and the two hypotheses are replaced by the single `degreeLT` entry hypothesis,
  required only for columns of weight at most `h`. The source-shaped hypotheses are accepted by
  `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le`.
* `Matrix.exists_primitive_mulVec_eq_zero_of_shifted_surplus` in the same file becomes
  `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT` (and its `_of_natDegree_le`
  form). Its specialization clause
  `∀ {E} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0` is dropped, as in
  `ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight`: it follows from the unit-ideal
  conclusion by `Ideal.comp_ne_zero_of_span_range_eq_top` with `Polynomial.eval₂RingHom ι z`.
* `Matrix.exists_primitive_kernel_vector_degreeLT` in the same file is now in
  `ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight`, for arbitrary index types.
* `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT` in `ColumnDegreeKernel.lean` keeps its
  name and statement, with arbitrary finite index types.
* `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank` in the same file measures the
  exact rank over `RatFunc F` inside the surplus. It becomes
  `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`, with any injective
  `φ : F[X] →+* K` and an upper bound `s` on the rank.
* `Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus` in the same file concludes only
  `(v j).natDegree ≤ h`, losing the individual column budgets. It becomes
  `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`, which keeps
  `v j ∈ degreeLT F (h + 1 - weight j)`; the source bound follows because this budget is at most
  `h + 1`.

`Polynomial.mem_degreeLT_add_one_sub_iff`: conditions used by the source

`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le`: /-- Source-shaped form of `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`.

The entry hypothesis is given as the two conditions of the immutable source: `hdegree` bounds the
natural degree of `M i j` by `columnWeight j - rowWeight i` when `rowWeight i ≤ columnWeight j`,
and `hzero` says `M i j = 0` when `columnWeight j < rowWeight i`. By
`Polynomial.mem_degreeLT_add_one_sub_iff` these two conditions together are equivalent to
`M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i)`. The `hzero` condition cannot be dropped:
without it a nonzero constant in a position of negative weight difference would satisfy the
natural-degree bound. On `Fin` indices this is the source theorem
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`. -/

`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le`: /-- Source-shaped form of `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT`,
with the entry hypothesis split into `hdegree` and `hzero` as in
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le`. On `Fin` indices this
is the source theorem `Matrix.exists_primitive_mulVec_eq_zero_of_shifted_surplus` without its
specialization clause, which follows from `Ideal.comp_ne_zero_of_span_range_eq_top` applied to
`Polynomial.eval₂RingHom ι z`. -/

`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`: keeps its individual budget `degreeLT F (h + 1 - weight j)`. The source theorem
`Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus` concluded only `natDegree ≤ h` after
normalization; that bound follows from this one since `h + 1 - weight j ≤ h + 1`. -/

## `ArkLib/ToMathlib/LinearAlgebra/TriangularInjective.lean`

This generalizes the `T`-adic induction in
`ReedSolomon.HiddenDerivative.truncateLocalT_sum_exhibitedKernelFactor_mul_eq_zero_iff`, in
`Interpolation/Local/KernelSliceIndependence.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source proved it for the coefficients of powers
of one variable over a field, indexed by `Fin m`; here the index is any finite linear order,
the test maps are arbitrary, and the scalars form a ring.

Nothing is deferred.

## `ArkLib/ToMathlib/MeasureTheory/Integral/NatFloorCells.lean`

Ports, from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,

* `integral_biUnion_le_sum_of_cell_measure_le_one` and `sum_le_integral_of_unit_cells` from
  `ArkLib/ToMathlib/MeasureTheory/Integral/FiniteCells.lean`, as
  `setIntegral_biUnion_le_sum` and `sum_le_setIntegral_of_measure_eq_one`. The first now assumes
  the one-sided bound `f x ≤ w i` instead of `‖f x‖ ≤ w i`, so `f` may be arbitrarily negative.
  The second assumes `0 ≤ f` only on `S`, together with measurability of `S`, instead of on the
  whole space.
* `natFloorCell`, `measurableSet_natFloorCell`, `volume_natFloorCell`, `mem_natFloorCell_iff`, and
  `disjoint_natFloorCell` from `ArkLib/ToMathlib/MeasureTheory/Integral/NaturalFloorCells.lean`.
  Disjointness is stated as `Pairwise (Disjoint on natFloorCell)`.
* The first half of `sum_natFloor_bounds` from the same file, in the weighted cell form
  `sum_mul_le_sum_mul_of_mem_natFloorCell`; its second half becomes
  `sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell` with coefficients.

`bounded_region_eq_union_natFloorCells` and `integral_bounded_region_le_natFloor_sum` are not
ported: the weighted-simplex transfers in `ArkLib.Data.Finset.WeightedSimplex.FloorTransfer` index
the cells by the lattice points of the simplex directly.

## `ArkLib/ToMathlib/MeasureTheory/Integral/PositivePart.lean`

Ports `ReedSolomon.HiddenDerivative.positivePart_pointwise` and
`ReedSolomon.HiddenDerivative.positivePart_mean_variance` from `WeightedSupport/PositivePart.lean`
in `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The pointwise bound is generalized from `ℝ` to any
ordered field, and the finite-average form is new; the probability-measure statement is the
source's, renamed. Neither statement uses coding theory, so both leave the Reed–Solomon namespace.

`le_integral_max_sub_zero_pow_three` ports
`ReedSolomon.HiddenDerivative.WeightedSupportParameters.positive_cube_moments` from
`WeightedSupport/Cubic.lean` at the same revision, together with the pointwise
`cubic_le_positive_cube` used in its proof. The source's integrability hypotheses for `z ^ 2` and
for `(max (b - z) 0) ^ 3` are dropped: both follow from the integrability of `z` and `z ^ 3`.
The rest of `Cubic.lean` (`positive_cube_tangent`, `positive_cube_jensen`,
`positive_cube_convex`) has no consumer in the port so far and is not ported.

`setIntegral_max_sub_zero_le` is the step of the source's
`ReedSolomon.HiddenDerivative.weighted_residual_sum_le_volume_mul_mean_variance` (in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at the same revision) that applies `positivePart_mean_variance` to the
conditional measure on the weighted simplex and multiplies back by its volume. Here it is stated
for any measure and any set, including sets of measure `0` or `∞`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/Integral.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ratePartition_triangle_rate_lower` → `max_sub_zero_sq_scaled_le`. The scalar comparison is generalized from real numbers to linearly ordered fields, and rate positivity follows from the other hypotheses.

## `ArkLib/ToMathlib/MvPolynomial/ClearedSubstitution.lean`

Ported from `ArkLib/ToMathlib/MvPolynomial/ClearedSubstitution.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d` (declarations `clearedSubstitution`,
`ringHom_clearedSubstitution`, `clearedSubstitution_map`, `map_clearedSubstitution`, and
`totalDegree_clearedSubstitution`). The target ring of the construction and the coefficient ring of
the degree bound are generalized from commutative rings to commutative semirings.

## `ArkLib/ToMathlib/MvPolynomial/CompleteHomogeneous.lean`

These identities replace the private index-case computations `sum_pair_multiplicity` and
`sum_triple_multiplicity` in `ArkLib/ToMathlib/Analysis/Simplex/Moments.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source expanded a squared or cubed linear form
over pairs and triples of indices and counted coincident indices by hand, over `Fin n` and `ℝ`.
Here the multiplicities are absorbed into Mathlib's `hsymm`, the index type is any `Fintype`, and
the coefficients lie in any commutative semiring. Higher Newton identities are not needed by the
simplex moments and are not proved.

## `ArkLib/ToMathlib/MvPolynomial/FirstOrderTaylor.lean`

Ported from `ArkLib/ToMathlib/MvPolynomial/FirstOrderTaylor.lean` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `firstOrderIncrement`, `firstOrderIncrement_add`,
  `eval₂Hom_add_sub_firstOrderIncrement_mem_sq`,
  `eval₂Hom_add_sub_firstOrderIncrement_univ_mem_sq`,
  `pow_succ_dvd_eval₂Hom_add_sub_firstOrderIncrement` and `pow_succ_dvd_eval₂Hom_add_sub_pderiv`
  keep their statements. The source required both `R` and `S` to be commutative rings; here `R`
  is a commutative semiring throughout and `firstOrderIncrement` also allows a semiring `S`.
* `exists_mem_sq_eval₂Hom_add_eq` is new: the subtraction-free form over commutative semirings,
  from which the source statement follows.
* `eval₂Hom_sub_eval₂Hom_mem` and `dvd_eval₂Hom_sub_eval₂Hom` generalize the private
  `pow_dvd_eval₂Hom_sub_of_forall_pow_dvd_sub` of
  `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Regular/Iteration.lean`
  from a modulus `u ^ m` to any ideal or element, and from a ring `R` to a semiring.

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.4, uses this
  linearization with `I` generated by a power of `T - α`.

## `ArkLib/ToMathlib/MvPolynomial/OptionRoots.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/OneJetGraphCounting.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `oneJetRootPolynomial` is Mathlib's
`MvPolynomial.optionEquivLeft`, and `natDegree_oneJetRootPolynomial` is
`natDegree_optionEquivLeft`. `eval_oneJetRootPolynomial` is now
`eval_map_aeval_optionEquivLeft`, and `polynomialGraphs_card_le_degreeOf` is now
`card_le_degreeOf_some_of_aeval_eq_zero`, over any domain, with the general root count
`card_le_degreeOf_none_of_aeval_eq_zero`. The old `polynomialGraphs_frobenius_canary` case was
dropped; the consolidated suite retains a concrete two-graph root-count instance.
## `ArkLib/ToMathlib/MvPolynomial/FrobeniusPullback.lean`

Merges `ArkLib/ToMathlib/MvPolynomial/FrobeniusPullback.lean` and
`ArkLib/ToMathlib/MvPolynomial/FrobeniusPullbackDerivative.lean` from the source. The hypotheses
weaken from `Field` and `PerfectField` to `CommSemiring`, `ExpChar` and `PerfectRing`.
`degreeOf_map_ringEquiv` is now `degreeOf_map_of_injective`, and
`Irreducible.map_inverseFrobeniusTwist` is now `irreducible_inverseFrobeniusTwist_iff`. Not ported,
with their replacements: `pow_primePow_injective` (`(iterateFrobeniusEquiv K p e).injective`),
`existsUnique_pow_eq_primePow` (`(iterateFrobeniusEquiv K p e).bijective.existsUnique`),
`pderiv_map_ringEquiv` (`MvPolynomial.pderiv_map`), `pderiv_map_ringEquiv_ne_zero_iff` (`pderiv_map`
with `map_ne_zero_iff`), and `pderiv_inverseFrobeniusTwist_ne_zero` (the `.mpr` of
`pderiv_inverseFrobeniusTwist_ne_zero_iff`). The Fin-3 definitions `rootVariableExponent` and
`basePowerSubstitution` and the `*_canary` examples were dropped; the consolidated suite retains a
concrete characteristic-two inverse-twist expansion case.

## `ArkLib/ToMathlib/MvPolynomial/OptionWeightedDegree.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Flattening.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The unit-specific flattening alias and helper weight are retired. The flattened polynomial is expressed directly as `(optionEquivRight F (JetVariable 1)).symm Q`, with weight `fun v ↦ v.elim 0 w`. The total weighted-degree bound follows from `weightedTotalDegree_optionEquivRight` and `AlgEquiv.apply_symm_apply`; no first-order wrapper is added.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/RetainedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Promoted the source-local `flattenChallenge_degreeOf_eq` result to the reusable generic theorem `MvPolynomial.degreeOf_optionEquivRight`, generalized to arbitrary `σ` and commutative semirings.

## `ArkLib/ToMathlib/MvPolynomial/PDeriv.lean`

This file ports and generalizes `ArkLib/ToMathlib/MvPolynomial/PDeriv.lean` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `degreeOf_pderiv_le_sub_one` and `degreeOf_pderiv_le` are ported unchanged.
* `pderiv_ne_zero_of_degreeOf_pos_of_lt_ringChar` and
  `degreeOf_pderiv_eq_sub_one_of_lt_ringChar` are replaced by
  `pderiv_ne_zero_of_natCast_ne_zero` and `degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero`. The
  source hypotheses `0 < degreeOf i p`, `degreeOf i p < ringChar R`, and `[Nontrivial R]` become
  the single hypothesis `(degreeOf i p : R) ≠ 0`, which implies positivity and nontriviality and
  also holds in characteristic zero. The same generalization appears in the source as the nested
  theorem `MvPolynomial.pderiv_ne_zero_and_degreeOf_eq_sub_one_of_natCast_ne_zero` inside the
  namespace `ReedSolomon.HiddenDerivative`, in
  `HiddenDerivative/Interpolation/FirstOrder/HybridDescent.lean`; that conjunction is the pair
  of theorems here, and its `hpos` and `[Nontrivial R]` hypotheses are dropped because the cast
  hypothesis implies them.
* The source definition `iteratePDeriv i a p` is replaced by Mathlib's `(pderiv i)^[a] p`, the
  spelling Mathlib uses for iterated univariate derivatives. The source lemmas
  `iteratePDeriv_zero` and `iteratePDeriv_succ` become `Function.iterate_zero_apply` and
  `Function.iterate_succ_apply'`.
* `degreeOf_iteratePDeriv_le` becomes `degreeOf_iterate_pderiv_le`.
* `degreeOf_iteratePDeriv_eq_sub_of_lt_ringChar` and `iteratePDeriv_ne_zero_of_lt_ringChar`
  become `degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero` and
  `iterate_pderiv_ne_zero_of_natCast_ne_zero`. Their cast hypothesis names only the `a` degrees
  actually differentiated, and it implies `a ≤ degreeOf i p`, so the source hypothesis `ha` is
  dropped. The source positivity hypothesis in the nonvanishing theorem is replaced by `p ≠ 0`,
  which is what the order-zero case needs.
* `coeff_pderiv_sub_single_one`, `degreeOf_iterate_pderiv_le_sub`,
  `iterate_pderiv_eq_zero_of_degreeOf_lt`, and `natCast_ne_zero_of_ringChar_eq_zero_or_lt` are
  new.

The weighted-degree bounds for `pderiv` live in `ArkLib.Data.MvPolynomial.WeightedDegree`. The
source's `_of_lt_ringChar` wrappers are not ported; their consumers combine the cast-hypothesis
theorems with `natCast_ne_zero_of_ringChar_eq_zero_or_lt`.

## `ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean`

Ported from the coefficient-height and joint-degree parts of `Symbolic/TaylorHeight.lean` and
`Symbolic/TaylorDegree.lean`, over a `CommSemiring` instead of a field. `flattenChallenge` is
`(optionEquivRight R σ).symm`, with the simp lemmas `optionEquivRight_symm_X` and
`optionEquivRight_symm_C`. `ChallengeHeightLE` is now `CoeffNatDegreeLE`, and its private
closure lemmas are public. `jointTotalDegree_scalar` is now `jointTotalDegree_C_C`,
`jointTotalDegree_le_coeff_degree_add` is now `jointTotalDegree_le_of_natDegree_coeff_le`, and
`jointTotalDegree_clearedSubstitution` is now `jointTotalDegree_clearedSubstitution_le`.
The source-shaped acceptance example for `jointTotalDegree_affine_le` was removed; the public
theorem survives in this module, as recorded below.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/CoefficientExtension.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`specialize_extendSymbolicCoefficients` → `MvPolynomial.eval_map_coefficients`, generalized from field extensions to arbitrary commutative semirings, variable types, coefficient maps, and target evaluation points. `extendSymbolicCoefficients` was not ported because it is an alias for `MvPolynomial.map` with `Polynomial.mapRingHom`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorCutDegree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `MvPolynomial.jointTotalDegree_affine_le`, the affine-polynomial degree bound in the general polynomial coefficient owner. No source declaration was renamed for this addition.

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/GraphPullback.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`aeval_map_optionEquivRight` and `aeval_optionEquivRight_symm` keep their names and are generalized from fields to commutative semiring algebras.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `MvPolynomial.optionEquivRight_symm_mem_restrictCappedBidegree`. It combines coefficient, total-degree, and coordinate bounds after flattening, using the existing weighted-degree identity for the coordinate bound.
Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Flattening.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`flattenFirstOrderChallenge_challengeDegree_le` is retired in favor of `weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le`; use `weightedTotalDegree_piSingle` for the `degreeOf none` form. The first-order coefficient-degree wrapper is not added.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Degree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`challengeHeightLE_clearedSubstitution` becomes `CoeffNatDegreeLE.clearedSubstitution`. The generic theorem takes an independent coefficient bound `a`, concludes `H * h + a`, and restricts the coefficient bound to `Q.support`, weaker than the source's all-coefficient hypothesis. The source `ChallengeHeightLE` predicate and its `mono`, `const`, `mul_bound`, `pow_bound`, and `sum_bound` lemmas are represented by `CoeffNatDegreeLE` and its existing closure lemmas. The source `prod_bound` helper is not promoted because no public result in this unit needs it; the finite-product estimate is handled internally. The private copy in `TaylorBidegree.lean` is subsumed and needs no separate entry.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveTransfer.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Generalized `ReedSolomon.challengeCoefficientHeight` to `MvPolynomial.coeffNatDegree`, the maximum degree of the polynomial coefficients for arbitrary variable types and commutative semiring coefficients. Renamed `ReedSolomon.coeffNatDegreeLE_challengeCoefficientHeight` to `MvPolynomial.coeffNatDegreeLE_coeffNatDegree`; this proves that the computed bound applies to every coefficient. The exception results derive this height from the equation `Q` instead of requiring it as an input.

## `ArkLib/ToMathlib/MvPolynomial/PowerMomentGeometry.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Incidence.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.powerMomentWeight`, `powerMomentMap_weightedTotalDegree_le`, `powerMomentIdeal_hilbertFunction_le_weightedFinrank`, `powerMomentWeight_exponent_ncard_le`, `powerMomentIdeal_hilbertFunction_le`, `powerMomentIdeal_affineDegree_le`, `powerMomentPoint`, `powerMomentSourcePoint`, `powerMomentSourcePoint_powerMomentPoint`, `aeval_powerMomentPoint`, `powerMomentPoint_mem_zeroLocus`, and `aeval_eq_aeval_powerMomentMap_of_mem_zeroLocus` move into the `MvPolynomial` namespace under their destination names, using the existing `PowerMomentIndex` API. `ReedSolomon.powerMoment_incidence_off_source_excluded` becomes `MvPolynomial.powerMomentMap_incidence_off_excluded` and is generalized. The Hilbert-polynomial degree results are not ported because existing generic affine-Hilbert-polynomial theorems cover them.

## `ArkLib/ToMathlib/MvPolynomial/PowerMomentLift.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Degree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.PowerLiftIndex` becomes `MvPolynomial.PowerMomentIndex`. `ReedSolomon.powerMomentMap` and `ReedSolomon.powerMomentIdeal` become `MvPolynomial.powerMomentMap` and `MvPolynomial.powerMomentIdeal`. The API is generalized from fields to commutative semirings. `powerMomentIdeal_isPrime`, `powerMomentMap_surjective`, `coefficientPowerLift`, `powerMomentMap_coefficientPowerLift`, `polynomialPowerLift`, `powerMomentMap_polynomialPowerLift`, `coefficientPowerLift_totalDegree_le_one`, and `polynomialPowerLift_totalDegree_le` keep their names under the MvPolynomial owner. Primality is generalized to additively cancellative commutative semirings with a domain structure; the degree bounds require nontriviality. `polynomialPowerLift` uses `CoeffNatDegreeLE`, and its map theorem recovers `(optionEquivRight R σ).symm P`.

The source rational Taylor numerator coefficient bound is covered by `PolynomialDifferential.coeffNatDegreeLE_rationalTaylorNumeratorOver`; the exponent-aware common Taylor numerator bound and its default form are covered by `coeffNatDegreeLE_commonTaylorNumeratorOver_le`. The source total-degree bound is covered by `totalDegree_rationalTaylorNumeratorOver_le_of_jet` in `PolynomialDifferential.RationalTaylorJointDegree`. The common Taylor numerator and Taylor curve agreement bidegree bounds, including exponent-aware forms, are covered by stronger rectangle-membership theorems in `PolynomialDifferential.RationalTaylorBidegree`. The common Taylor denominator bidegree bounds are not given paired wrappers because existing separant coefficient-degree, power, and jet-degree bounds suffice.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ChunkedPowerLift.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.chunkedCoefficientPowerLift` became `MvPolynomial.chunkedCoefficientPowerLift`, generalized from fields to commutative semirings. `ReedSolomon.powerMomentMap_chunkedCoefficientPowerLift` became `MvPolynomial.powerMomentMap_chunkedCoefficientPowerLift` with the same generalization.

`ReedSolomon.chunkedPolynomialPowerLift` became `MvPolynomial.chunkedPolynomialPowerLift`, generalized from fields and `ChallengeHeightLE` to commutative semirings and `CoeffNatDegreeLE`. `ReedSolomon.powerMomentMap_chunkedPolynomialPowerLift` became `MvPolynomial.powerMomentMap_chunkedPolynomialPowerLift` with the same generalization; flattening uses `optionEquivRight`.

`ReedSolomon.chunkedCoefficientPowerLift_totalDegree_le` became `MvPolynomial.chunkedCoefficientPowerLift_totalDegree_le`, generalized to nontrivial commutative semirings. `ReedSolomon.chunkedPolynomialPowerLift_totalDegree_le` became `MvPolynomial.chunkedPolynomialPowerLift_totalDegree_le`, generalized to nontrivial commutative semirings and `CoeffNatDegreeLE`.

All six public declarations are represented. The existing `PowerMomentIndex`, `powerMomentMap`, coefficient-height predicate, and flattening equivalence are reused; nothing was omitted.

## `ArkLib/ToMathlib/MvPolynomial/RootContraction.lean`

Ported from `ArkLib/ToMathlib/MvPolynomial/RootContraction.lean` at the source revision. The
hypotheses weaken from `IsDomain` to `CommSemiring`, and to `NoZeroDivisors` for
`degreeOf_rootContraction_none_mul`, which now takes `pderiv none P = 0` instead of the univariate
derivative hypothesis.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/Equation.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

`map_rootExpansion` and `eval₂_rootExpansion` become `MvPolynomial.map_rootExpansion` and `MvPolynomial.eval₂_rootExpansion`, generalized to coefficient maps and evaluation into commutative semirings. `MvPolynomial.map_optionEquivLeft` is relocated from `ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean` with its name and statement preserved; `PolynomialCoefficients` publicly imports `RootContraction` to retain its visibility.

No declaration was left unported. The `PolynomialCoefficients` change is the import needed to expose the relocated declaration.

## `ArkLib/ToMathlib/MvPolynomial/SupportWeight.lean`

These declarations are ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
`supportWeightLE`, `monomial_mem_supportWeightLE`, `aeval_mem_supportWeightLE`,
`weight_le_of_mem_coeff_optionEquivLeft`, and `weightedTotalDegree_coeff_optionEquivLeft_le` come
from `ArkLib/ToMathlib/MvPolynomial/SupportWeight.lean`; `supportWeightLE` is now built from
Mathlib's `MvPolynomial.restrictSupport`, whose multiplicativity lemma `restrictSupport_add`
supplies closure under products. `Finsupp.weight_two_mul_sub_one_le` generalizes
`taylor_denominator_weight_le` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/Denominator.lean`: the
index type is arbitrary instead of `Fin (r + h)`, the weight `t` is arbitrary instead of
`l ↦ l - r`, and the source hypothesis `0 < h` is removed.

## `ArkLib/ToMathlib/NumberTheory/Harmonic/Thresholds.lean`

`harmonic_sub_log_lt` and `harmonicPowerSum_two_gt` of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/Moment.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` are `Real.harmonic_sub_log_lt` and
`Real.lt_sum_fin_one_div_add_one_sq`, from the thresholds `180` and `203` in place of `200` and
`500`.

## `ArkLib/ToMathlib/Polynomial/EventualGrowth.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`AffineHilbert`: `polynomial_eq_of_eval_nat_ge` from
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Polynomial.lean`, and `backwardDifference`,
`natDegree_backwardDifference_le`, `coeff_backwardDifference_pred_natDegree`,
`backwardDifference_natDegree_eq_and_leadingCoeff`, the private
`leadingCoeff_nonneg_of_eventually_eval_nat_nonneg` and
`natDegree_le_of_eventually_eval_nat_le` from
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/Degree.lean`. The source worked over `ℚ` with a
natural shift `b`. Here equality on a tail holds over any commutative domain of characteristic
zero; the backward-difference algebra holds over any commutative ring with a shift in the ring,
and the coefficient identity needs no positivity of the degree; the order statements hold over
any Archimedean ordered normed field with the order topology. The comparison lemma
`natDegree_le_of_eventually_eval_natCast_le` no longer assumes `Q ≠ 0`. The final lemma is the
polynomial half of the source's `principalCut_eventualPolynomial_degree_and_coeff`, separated from
the Hilbert-function inequality. It needs neither a sign condition on `b` nor the eventual
positivity of `P`, which the source took from the Hilbert function, and its conclusion also holds
for `Q = 0`, so the source's disjunction with `Q = 0` is not needed.

From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PolynomialGrowthRescaling.lean`:
`natDegree_comp_C_mul_X`, `natDegree_le_of_eventually_eval_nat_le_rescaled` and
`natDegree_eq_of_eventually_eval_nat_sandwich`; from
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PolynomialGrowthAffine.lean`:
`natDegree_le_of_eventually_eval_nat_le_mul_affine`. The source stated these over `ℚ` with natural
constants `m, c > 0` and `d`, and assumed the compared polynomials nonzero. Here the constants are
arbitrary elements of the field and no nonzero or positivity hypothesis is needed, since
`C m * P.comp (C c * X + C d)` has natural degree at most that of `P` in every case; the
rescaling-only form is `d = 0`, `m = 1`. The sandwich needs only the eventual nonnegativity of the
lower polynomial, and `natDegree_comp_C_mul_X` becomes `natDegree_comp_C_mul_X_add_C` over any
semiring without zero divisors.

From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PrimeFamilyCoefficient.lean`:
`coeff_nonneg_of_natDegree_le_of_eventually_eval_nat_nonneg`,
`coeff_le_of_natDegree_le_of_eventually_eval_nat_le` and `coeff_taylor_eq_of_natDegree_le`. The
source stated them over `ℚ`; the first two hold over any Archimedean ordered normed field with the
order topology, as the other order statements here, and the Taylor lemma over any commutative
semiring. Mathlib has `Polynomial.coeff_taylor_natDegree` for the degree `natDegree P` itself;
`coeff_taylor_of_natDegree_le` extends it to every larger degree.

## `ArkLib/ToMathlib/Polynomial/HasseTaylor/Lifting.lean`

Ported from `ArkLib/ToMathlib/Polynomial/HasseTaylor/Lifting.lean` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `hassePerturbation`, `taylor_hassePerturbation`, `hasseCoeffAt_hassePerturbation`,
  `hasseCoeffAt_add_hassePerturbation{,_of_lt,_self}`, `hasseJet_add_hassePerturbation_of_le`,
  `hasseCoeffAt_hasseDeriv_add_hassePerturbation_of_lt`, and
  `natCast_choose_ne_zero_of_lt_charP` keep their source statements.
* `hasseDeriv_hassePerturbation` and `hasseDeriv_add_hassePerturbation` state the right-hand side
  as a `hassePerturbation` instead of unfolding it.
* `hasseCoeffAt_hasseDeriv_add_hassePerturbation` drops the source hypothesis `s ≤ i`.
* The source's field-valued statements
  `hasseCoeffAt_hasseDeriv_add_hassePerturbation_injective_of_choose_ne_zero`
  and `existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq_of_choose_ne_zero` become
  `hasseCoeffAt_hasseDeriv_add_hassePerturbation_injective` and
  `existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq`, over a commutative ring, with
  hypotheses `IsLeftRegular (i choose s : R)` and `IsUnit (i choose s : R)` and without `s ≤ i`.
  Over a field both hypotheses are `(i choose s : F) ≠ 0`.
* The source's `ringChar` forms (`natCast_choose_ne_zero_of_lt_ringChar`,
  `isUnit_natCast_choose_of_lt_ringChar`, `isUnit_natCast_choose_of_le_of_lt_ringChar`, and the
  former `_injective` and `_eq` statements with hypothesis `i < ringChar F`) are not ported.
  Consumers state the cast hypothesis `(i choose s : R) ≠ 0` and discharge it with
  `natCast_choose_ne_zero_of_lt_charP` when needed.
* `X_pow_dvd_taylor_iff_X_sub_C_pow_dvd` and `X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd` come
  from `.../HiddenDerivative/RootFinding/Regular/Lifting.lean`, where they were stated over a field;
  here over a commutative ring and a semiring.
* `X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd` comes from
  `.../HiddenDerivative/RootFinding/Regular/Iteration.lean`, where the derivative order was a
  `Fin (r + 1)` and the ring a field; here it is any `s : ℕ` over a commutative ring.

## `ArkLib/ToMathlib/Polynomial/RectangleDifference.lean`

Merges `ArkLib/ToMathlib/Polynomial/RectangleDifference.lean` and
`ArkLib/ToMathlib/Polynomial/RectangleDifferenceGeneral.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `rectangleDifference` and its degree, coefficient and
evaluation lemmas are stated for general `s`; the source's `rectangleDifferenceOne` and
`rectangleDifferenceTwo` and their lemmas are not ported, and the acceptance test computes the
`s = 0, 1, 2` coefficients from the general statement.

## `ArkLib/ToMathlib/RingTheory/Ideal/HeightUnder.lean`

Extracted from `AffineHilbert.normalization_contraction_height_one` in
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/NoetherNormalizationHeightOne.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source proved these facts inside one
theorem, for a finite injective map from `MvPolynomial (Fin d) F` into a finite-type domain over
a field `F`, and packaged them in the structure `NormalizationHeightOneData`. Here the
commutative-algebra content is stated for an arbitrary integral extension: the base needs to be
an integrally closed domain for the height statement and a unique factorization domain for the
generator, and the extension a domain. The finiteness and injectivity of the induced map of
quotients are Mathlib instances and lemmas (`Ideal.quotientMap_injective'`, the
`Module.Finite` instance on quotients), so the structure is not reintroduced.

## `ArkLib/ToMathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean`

This file is extracted from ArkLib at source revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `Ideal.minimalPrimesFinset` and
`Ideal.mem_minimalPrimesFinset` replace `AffineHilbert.minimalPrimesFinset` and
`AffineHilbert.mem_minimalPrimesFinset` in
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/ComponentCoefficient.lean`, which were stated
only for `MvPolynomial σ F` over a field with `Finite σ`; here the ring is any Noetherian
commutative semiring. `Ideal.retainedMinimalPrimes` and `Ideal.mem_retainedMinimalPrimes` replace
the declarations of the same names in `ArkLib/ToMathlib/AlgebraicGeometry/PrincipalOpen/Cuts.lean`,
which built the retained family as a second, independent `toFinset` of the same finite set. Here
the retained family is a filter of `Ideal.minimalPrimesFinset`, so a single representation serves
both, and `Ideal.retainedMinimalPrimes_subset` relates them. The source membership law took
`I P s` as explicit arguments; here they are implicit and the law is a `simp` lemma.

The principal-cut Krull-dimension consequences of this finite family are in
`ArkLib.ToMathlib.RingTheory.Ideal.PrincipalCut`.

## `ArkLib/ToMathlib/RingTheory/Ideal/PrincipalCut.lean`

These declarations are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalOpen/Cuts.lean`. The first two declarations preserve
the source's effective generality: the source placed them in a Noetherian section but explicitly
omitted that instance from both statements.

The height statements are ported from
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/Dimension.lean` at the same revision.
`map_quotient_ne_bot_of_lt` no longer assumes that `P` is prime, since
`J.map (Ideal.Quotient.mk P) = ⊥` exactly when `J ≤ P`.
`map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span` and
`exists_principalCut_component_relative_codimension_one` keep the source hypotheses, with the
primality of `P` as an instance argument as elsewhere in this file; the existence statement drops
the conjunct `J.IsPrime`, which follows from minimal-prime membership. The source's
`principalCut_minimalPrime_relative_codimension_one` was the conjunction of `Ideal.IsPrime`,
`lt_of_mem_minimalPrimes_sup_span` and the height statement, and is not repeated.

From `ArkLib/ToMathlib/AlgebraicGeometry/CutFamily/Finite.lean` at the same revision:
`AffineHilbert.mem_retainedCutChildren` is `of_mem_retainedMinimalPrimes_sup_span`. The source
stated it for `retainedCutChildren P s f`, which is `{P}` when `f ∈ P` and the retained minimal
primes of `P ⊔ span {f}` otherwise, over `MvPolynomial σ F` with `P` prime and `s ∉ P`. Here it is
stated for the retained minimal primes of the cut of any ideal of a Noetherian ring, and
`retainedMinimalPrimes_sup_span_of_mem` shows that the two families agree when `P` is prime and
`s ∉ P`, so `retainedCutChildren` is not introduced.

## `ArkLib/ToMathlib/RingTheory/Ideal/Separator.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The separator
construction is the first half of
`AffineHilbert.exists_separators_sum_shifted_hilbertFunction_le_iInf` in
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PrimeFamily.lean`, where it was stated for ideals of
`MvPolynomial σ F` together with a Hilbert-function inequality. Here it is a statement about prime
ideals of any commutative semiring, and the Hilbert-function half is
`MvPolynomial.exists_sum_affineHilbertFunction_le_iInf` in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComponents`. The incomparability of minimal
primes is the private `minimalPrime_pairwise_incomparable` of
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/ComponentCoefficient.lean`, stated for an
arbitrary commutative semiring.

## `ArkLib/ToMathlib/RingTheory/Ideal/SurjectiveMap.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/TwoJet.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `Ideal.map_prime_principalOpenData_of_surjective` as a generic helper. It transports prime ideal and comap data, principal-open avoidance, generator membership, and membership of lifted cuts along a surjective ring map. The helper has no direct source declaration; it factors the shared ideal transport used by both capped incidence proofs.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineDegree.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Degree.lean`, namespace `AffineHilbert`:
`affineDegree`, `affineDegree_nonneg`, `affineDegree_pos`, `affineDegree_bot`,
`affineDegree_eq_finrank` and `affineDegree_span_singleton`. The definition is unchanged except
that it is stated for `MvPolynomial.affineHilbertPolynomial`. `affineDegree_span_singleton` no
longer assumes that `span {f}` is proper: for a nonzero constant `f` both sides are `0`. The
characterization `affineDegree_pos_iff`, the value `affineDegree_top`, the constant-polynomial
form `affineDegree_of_natDegree_eq_zero` and the comparison `affineDegree_le_of_le` are new.
The source's `finite_zeroLocus_and_ncard_le_affineDegree` is in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial`.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbert.lean`

The definitions and the principal-cut inequality are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Function.lean`: `AffineHilbert.quotientDegreeLE`,
`AffineHilbert.hilbertFunction` (renamed `affineHilbertFunction`),
`AffineHilbert.exists_finset_generators_totalDegree_le` and
`AffineHilbert.principalCut_hilbertFunction_add_le`. The source assumed that `I` is prime and
`f ∉ I`; the general form assumes only that multiplication by the class of `f` is injective on the
quotient, which is what the proof uses, and the source statement is the corollary
`principalCut_affineHilbertFunction_add_le_of_isPrime`. The monotonicity statements,
`quotientDegreeLE_eventually_top` and `one_le_hilbertFunction` of the source files
`Hilbert/Polynomial.lean` and `PrincipalCut/Degree.lean` at the same revision are included here,
since they concern only the Hilbert function. The field is named `k` and the declarations live in
the `MvPolynomial` namespace, as in `ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient`.
The source namespace `AffineHilbert` is not kept: the objects are attached to an ideal of
`MvPolynomial σ k`, and the prefix `affine` in `affineHilbertFunction` separates this function from
Mathlib's graded `Polynomial.hilbertPoly`.

The multiplicativity lemmas for the filtration are used for comparisons along algebra maps in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom`. The Hilbert polynomial of `I` and
the principal-cut statement on its degree are in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial`.

`MvPolynomial.principalCut_affineHilbertFunction_add_le_of_isPrime`: This is the source statement.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertAlgHom.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `AffineHilbert`.
From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/FiniteAlgebraGrowth.lean`:
`hilbertFunction_le_rescaled_of_injective_algHom` (here
`exists_affineHilbertFunction_le_of_injective`, with the explicit-constant form
`affineHilbertFunction_le_of_injective`, which needs neither injectivity for the filtration step
nor finiteness of `τ`), `hilbertPolynomial_natDegree_le_of_injective_algHom`,
`hilbertPolynomial_natDegree_le_of_surjective_algHom` and
`hilbertFunction_le_mul_rescaled_of_finite`. From
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/FiniteExtensionDegree.lean`:
`hilbertPolynomial_natDegree_eq_of_finite_injective_algebraMap` and
`hilbertPolynomial_natDegree_eq_of_finite_injective_algHom`.

Changes from the source. The finite case is stated for an algebra map `g` with `g.Finite` rather
than for an `Algebra` instance with `IsScalarTower` and `Module.Finite`; the instance form is
`RingHom.finite_algebraMap` applied to `IsScalarTower.toAlgHom`, and the two source equality
statements become one. The source's finite bound was `H(I, N) ≤ m * H(J, c * (N + 1))`; with
`1` in the generating set the constant term lands in degree `0`, giving `H(J, c * N)`. The
surjective case is a corollary of the finite case rather than a separate kernel argument, so it
no longer assumes `I ≠ ⊤`; the injective and equality statements no longer assume `J ≠ ⊤` or
`I ≠ ⊤`, because `Polynomial.natDegree_le_of_eventually_eval_natCast_le` does not need a nonzero
polynomial. The source's private `totalDegree_eval₂_le` is replaced by the multiplicativity of the
filtration and `aeval_mem_of_forall_mul_mem`.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertBidegree.lean`

Ported from the ideal and Hilbert-function part of
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Bidegree.lean`. `bidegreeIdeal` is
`RingHom.ker (bidegreeMap σ k a b)`, prime by `RingHom.ker_isPrime`, and
`bidegreeIdeal_hilbertPolynomial_natDegree` is now
`natDegree_affineHilbertPolynomial_ker_bidegreeMap`. `bidegreeCutMap` and
`bidegreeHypersurfaceIdeal` are `(Ideal.span {g}).comap (bidegreeMap σ k a b)`;
`bidegreeCutMap_surjective` is not ported. `bidegreeHypersurface_hilbertPolynomial_natDegree` is
now `natDegree_affineHilbertPolynomial_comap_bidegreeMap` for any ideal, with the
`_span_singleton` case. `bidegreeHypersurfaceIdeal_eq_sup_of_map_eq` is now
`comap_bidegreeMap_span_singleton`; the lift-based ideal equality applies this general form with
`bidegreeMap_bidegreeLift`. `quotientBidegreeLE_finrank_add_le` and
`quotientBidegreeLE_finrank_le` are now `finrank_quotientBidegreeLE_span_singleton_add_le` and
`finrank_quotientBidegreeLE_span_singleton_le`. `bidegreeHypersurface_hilbertFunction_le` is now
`affineHilbertFunction_comap_bidegreeMap_le`, for any ideal and without positivity of `a` and
`b`; `bidegreeHypersurface_hilbertFunction_le_rectangleDifference` is a step of the affine-degree
proof. `bidegreeHypersurface_affineDegree_le`, stated for `Fin (r + 1)`, is now
`affineDegree_comap_bidegreeMap_span_singleton_le` for any finite `σ` and without the properness
hypothesis. `bidegreeHypersurface_sum_minimalPrimes_affineDegree_le` is now
`sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le`, without the nonvanishing and
properness hypotheses. The acceptance test derives the source's `_one` and `_two` forms.
Gains two declarations with no source counterpart by name:
`natDegree_affineHilbertPolynomial_le_card_of_surjective` and
`natDegree_affineHilbertPolynomial_le_card_of_adjoin_eq_top`. A quotient `MvPolynomial σ k ⧸ I`
generated by `Nat.card τ` elements has affine Hilbert polynomial of natural degree at most
`Nat.card τ`. The source's `EvaluationDimension.lean` proved this step inside
`polynomialCoefficientEvaluation_hilbertPolynomial_natDegree_le` and
`fixedCoefficientEvaluation_hilbertPolynomial_natDegree_le`, by a surjection from a polynomial ring
onto the quotient; `CoefficientEvaluation.lean` uses the lemmas instead. The test checks the
generator form on `ℚ[x₀, x₁] ⧸ (x₁)` and recovers `natDegree_affineHilbertPolynomial_le` from the
quotient map.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertCappedBidegree.lean`

Ported from the Hilbert-function and affine-degree part of
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/DerivativeBidegree.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `derivativeBidegreeHypersurface_hilbertFunction_le`
and `_le_rectangleDifference` are now
`affineHilbertFunction_comap_cappedBidegree_span_singleton_add_le`, for any finite `σ`.
`derivativeBidegreeHypersurface_affineDegree_le_two_of_lt` is now
`affineDegree_comap_cappedBidegree_span_singleton_le`, without `r ≤ j`, properness or `c < b`,
with the bound `cappedBidegreeMixedVolume h j r a b c`.
`derivativeBidegreeHypersurface_sum_minimalPrimes_affineDegree_le_two_of_lt` is now
`sum_affineDegree_minimalPrimes_comap_cappedBidegree_span_singleton_le`.
`cappedRectangleDifferenceTwo` and its coefficient, evaluation and degree lemmas are not ported
as declarations. `mixedDerivativeImageDegree` and `fixedFiberDerivativeImageDegree` are
`cappedBidegreeMixedVolume` and `cappedDegreeMixedVolume` (see the sections for
`CappedBidegree.lean` and `CappedDegree.lean`).

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertCappedDegree.lean`

Ported from the Hilbert-function and affine-degree part of
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/TwoJetDegree.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `twoJetHypersurface_hilbertFunction_le` is now
`affineHilbertFunction_comap_cappedDegree_span_singleton_add_le`, for any finite `σ` and cap
coordinate `i`. `twoJetHypersurface_affineDegree_le` is now
`affineDegree_comap_cappedDegree_span_singleton_le`, without `c ≤ b` or properness and with the
bound `cappedDegreeMixedVolume j r b c`, and
`twoJetHypersurface_affineDegree_le_of_shift` is a private lemma.
`twoJetHypersurface_sum_minimalPrimes_affineDegree_le_bound` is now
`sum_affineDegree_minimalPrimes_comap_cappedDegree_span_singleton_le`, without `c ≤ b`,
properness or the second membership hypothesis.
`twoJetHypersurface_sum_minimalPrimes_affineDegree_le` is
`sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective`.
`twoJetHypersurface_hilbertPolynomial_natDegree` is
`natDegree_affineHilbertPolynomial_comap_of_surjective`, and
`twoJetHypersurfaceIdeal_eq_sup` follows from `Ideal.comap_span_singleton_of_surjective` and
`monomialMap_monomialLift`. `twoJetDifference` and its degree, coefficient and evaluation lemmas
are not ported as declarations; the bound is written out in the statements.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertComap.lean`

General statements used by
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/DerivativeBidegree.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `quotientDerivativeBidegreeLE_finrank_add_le` and
`_finrank_le` are now `Submodule.finrank_map_mkₐ_span_singleton_add_le`;
`derivativeBidegreeHypersurfaceIdeal_eq_sup` is now `Ideal.comap_span_singleton_of_surjective`;
`derivativeBidegreeIdeal_hilbertPolynomial_natDegree` is now
`MvPolynomial.natDegree_affineHilbertPolynomial_ker_of_surjective`; the hypersurface degree lemma is
now `natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective`; and
`derivativeBidegreeHypersurface_sum_minimalPrimes_affineDegree_le` is now
`sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective`, without the nonvanishing,
properness and degree hypotheses. `quotientDerivativeBidegreeLE` is not ported.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertComponents.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`AffineHilbert`.

From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PrimeFamily.lean`: `familySeparatorLift`,
`filteredFamilySeparatorLift`, `separatorFamilyMap` and `separatorFamilyMap_injective` were proof
devices for `sum_shifted_hilbertFunction_le_iInf`; they are private here, and the public result is
`sum_affineHilbertFunction_le_iInf`. The source assumed that each `I i` is prime and `s i ∉ I i`;
here it is enough that the class of `s i` is a non-zero-divisor on the quotient by `I i`, which is
what the injectivity uses. `exists_separators_sum_shifted_hilbertFunction_le_iInf` is
`exists_sum_affineHilbertFunction_le_iInf`, with the separator construction moved to
`Ideal.exists_separators_of_pairwise_not_le` in `ArkLib.ToMathlib.RingTheory.Ideal.Separator`, and
with the source's threshold `N ≥ Finset.univ.sup (totalDegree ∘ s)` written as
`∀ i, totalDegree (s i) ≤ N`.

From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PrimeFamilyCoefficient.lean`:
`sum_hilbertPolynomial_coeff_le_iInf` is `sum_coeff_affineHilbertPolynomial_le_iInf`, a corollary
of `sum_coeff_affineHilbertPolynomial_le_of_separators`. The source's hypothesis that every
component has natural degree at most `d` is dropped: it follows from the bound for `⨅ i, I i`,
because the Hilbert polynomial decreases in degree along inclusions. The three `ℚ[X]` lemmas of
that file are `Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg`,
`Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le` and
`Polynomial.coeff_taylor_of_natDegree_le` in `ArkLib.ToMathlib.Polynomial.EventualGrowth`.

From `ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/ComponentCoefficient.lean`:
`principalCut_sum_minimalPrime_coeff_le` is
`principalCut_sum_coeff_affineHilbertPolynomial_minimalPrimes_le` and
`principalCut_sum_minimalPrime_factorial_le` is
`principalCut_sum_factorial_mul_leadingCoeff_minimalPrimes_le`. The source assumed that `P` is
prime and `f ∉ P`; here the class of `f` is a non-zero-divisor on the quotient, as in
`MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le`. The source's case
split on `P ⊔ span {f} = ⊤` is not needed. The general statement for the minimal primes of any
ideal, `sum_coeff_affineHilbertPolynomial_minimalPrimes_le`, is new. The source's
`minimalPrimesFinset` and `mem_minimalPrimesFinset` are `Ideal.minimalPrimesFinset` and
`Ideal.mem_minimalPrimesFinset`, its private `minimalPrime_pairwise_incomparable` is
`Ideal.not_le_of_mem_minimalPrimes`, and its private `iInf_minimalPrimes_eq_radical` is
Mathlib's `Ideal.sInf_minimalPrimes`.

The factorial statement keeps the source's hypothesis that every minimal prime of the cut has
natural degree exactly `natDegree P - 1`. For polynomial rings over a field this purity holds,
but its proof needs the equality of the Hilbert-polynomial degree with the Krull dimension, which
is not formalized here.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertPolynomial.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`AffineHilbert`. From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Polynomial.lean`:
`hilbertPolynomial` (renamed `affineHilbertPolynomial`), `hilbertPolynomial_natDegree_le`,
`hilbertPolynomial_eventually`, `hilbertPolynomial_eventually_eval`, `hilbertPolynomial_unique`,
`hilbertPolynomial_eq_constant`, `hilbertPolynomial_ne_zero`,
`hilbertPolynomial_degree_and_leadingCoeff_antitone`,
`moduleFinite_of_hilbertPolynomial_natDegree_zero` and
`principalCut_hilbertPolynomial_zero_or_degree_and_coeff`. From
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/Degree.lean`:
`principalCut_eventualPolynomial_degree_and_coeff` and
`principalCut_eventualPolynomial_zero_or_degree_and_coeff`, whose polynomial half is
`Polynomial.natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference` in
`ArkLib.ToMathlib.Polynomial.EventualGrowth`. From
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/Polynomial.lean`: `hilbertPolynomial_bot`,
`hilbertPolynomial_bot_natDegree`, `hilbertPolynomial_span_singleton`,
`hilbertPolynomial_span_singleton_natDegree_add_one` and
`totalDegree_pos_of_span_singleton_ne_top`.

Changes from the source. The principal cut assumes that multiplication by the class of `f` is
injective on the quotient, as `MvPolynomial.principalCut_affineHilbertFunction_add_le` does; the
source's prime ideal with `f ∉ I` is the corollary `..._of_isPrime`. The source concluded
`Q = 0 ∨ (degree and coefficient bounds)`; the bounds hold for `Q = 0` as well, so the disjunction
is dropped. The comparison along inclusions no longer assumes that the larger ideal is proper, and
the converse of `moduleFinite_of_hilbertPolynomial_natDegree_zero` is added. The source's
`preHilbertPoly_eq_taylor`, `countingPolynomial_singleton` and
`hilbertPolynomial_span_singleton_natDegree` are replaced by a direct count of the exponents above
the leading exponent of `f`. The source's `quotientDegreeLE_eventually_top`,
`hilbertFunction_antitone`, `quotientDegreeLE_mono` and `standardExponents_span_singleton` are in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbert` and
`ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials`.

The source's `finite_zeroLocus_and_ncard_le_hilbertPolynomial` is in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial`, and the finite-algebra
comparisons of `Hilbert/FiniteAlgebraGrowth.lean` and `Hilbert/FiniteExtensionDegree.lean` are in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom`. The affine degree of
`Hilbert/Degree.lean` is in `ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree`, and the
radical comparison of `Hilbert/RadicalDegree.lean` is in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertRadical`.

`MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime`: This is the source statement
without its disjunction with `Q = 0`.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertPurity.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`AffineHilbert`.

From `ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/NoetherNormalizationHeightOne.lean`: the
commutative algebra of `normalization_contraction_height_one` is `Ideal.height_under_eq_one` and
`Ideal.exists_prime_under_eq_span_singleton` in `ArkLib.ToMathlib.RingTheory.Ideal.HeightUnder`.
The structure `NormalizationHeightOneData`, the maps `normalizationBotMap`,
`normalizationPrincipalQuotientMap`, `normalizationChildMap`, `parentComponentQuotientEquiv`
(Mathlib's `DoubleQuot.quotQuotEquivQuotOfLEₐ`) and their finiteness and injectivity lemmas, and
the existence statements `exists_normalization_contraction_height_one`,
`principalCut_component_exists_normalization_contraction` and
`principalCut_component_exists_coordinate_normalization` were packaging for the purity proof;
they are not ported, and the maps are built inside the proof of
`natDegree_affineHilbertPolynomial_add_one_of_height_eq_one`.

From `ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/Purity.lean`:
`principalCut_component_hilbertPolynomial_natDegree_add_one` is
`principalCut_natDegree_affineHilbertPolynomial_add_one`, a corollary of the height-one statement
`natDegree_affineHilbertPolynomial_add_one_of_height_eq_one`, which is new and applies to every
prime of height one above `P`, not only to minimal primes of a principal cut. The parent
computation `natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective` is also new.

From `ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/Bezout.lean`:
`principalCut_sum_affineDegree_le` is `principalCut_sum_affineDegree_minimalPrimes_le`, with the
same hypotheses.

From `ArkLib/ToMathlib/AlgebraicGeometry/CutFamily/Finite.lean`:
`sum_retainedCutChildren_affineDegree_mul_pow_le` is
`sum_affineDegree_mul_pow_retainedMinimalPrimes_le`. The source summed over
`retainedCutChildren P s f`, defined as `{P}` when `f ∈ P` and as
`(P ⊔ span {f}).retainedMinimalPrimes s` otherwise. For a prime `P` with `s ∉ P` the two agree
(`Ideal.retainedMinimalPrimes_sup_span_of_mem`), so the retained minimal primes are used directly
and no new definition is introduced. The hypotheses `s ∉ P` and `1 ≤ b` of the source are dropped:
the bound holds without them. The source's `mem_retainedCutChildren` is
`Ideal.of_mem_retainedMinimalPrimes_sup_span`, and its
`exists_mem_retainedCutChildren_of_mem_zeroLocus` is the forward direction of
`MvPolynomial.mem_zeroLocus_and_cut_iff_retained`.

Primality of `P` is used throughout: it makes the quotient a domain, which Noether normalization
and the height-one contraction need. Without it purity fails: for `P = (xy, xz)` in three
variables, the union of a plane and a line, and `f = x - 1`, which is regular modulo `P`, the only
component of the cut is the point `(1, 0, 0)`, of dimension `0` rather than `1`.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertRadical.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/RadicalDegree.lean`, namespace `AffineHilbert`. The
source's `exponentDiv t e`, with `exponentDiv_apply` and `exponentDiv_le`, is Mathlib's floor
division `e ⌊/⌋ t` on `σ →₀ ℕ` (`Finsupp.floorDiv_apply`, `Nat.floorDiv_eq_div`), so it has no
new definition; `exponentDiv_le` is `Finsupp.floorDiv_le_self`. The source's
`exponentDiv_mem_standardExponents` is `MonomialOrder.floorDiv_mem_standardExponents`, stated for
every monomial order instead of `degLex` and without the hypothesis `0 < t`: for `t = 0`,
`J ^ 0 ≤ I` forces `I = ⊤`, which has no standard exponents. The source's
`hilbertFunction_le_mul_of_pow_le` is `affineHilbertFunction_le_pow_mul_of_pow_le`, with the
factor `t ^ Nat.card σ` on the left, for finite `σ` without a chosen `Fintype` or `LinearOrder`,
and again without `0 < t`. The source's `hilbertPolynomial_radical_natDegree` is
`natDegree_affineHilbertPolynomial_radical`, a corollary of the comparison
`natDegree_affineHilbertPolynomial_le_of_pow_le` for arbitrary `J ^ t ≤ I` and of the equality
`natDegree_affineHilbertPolynomial_eq_of_le_of_le_radical` for every `I ≤ J ≤ I.radical`.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/Bidegree.lean`

Ported from the exponent and monomial-map part of
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Bidegree.lean`. The source's `challengeWeight` and
`jetWeight` are the weights `fun v ↦ v.elim 1 fun _ ↦ 0` and `fun v ↦ v.elim 0 fun _ ↦ 1`, with
the simp lemmas `Finsupp.weight_elim_one_zero` and `Finsupp.weight_elim_zero_one` in
`OptionWeightedDegree.lean`. `BidegreeIndex a b σ` is the subtype of `bidegreeExponents σ a b`,
and `bidegreeExponentSet_finite` is the instance `bidegreeExponents.finite`.
`restrictBidegree` now works over a `CommSemiring`, and `finrank_restrictBidegree` over a
`CommRing` with `StrongRankCondition`. `bidegreeMap_challengeDegree_le` and
`bidegreeMap_jetDegree_le` are now `bidegreeMap_mem_restrictBidegree`, and
`bidegreeLift_totalDegree_le_one` is now `totalDegree_bidegreeLift_le_one`.
`affineDegree_le_of_eventually_hilbertFunction_le` is now
`affineDegree_le_of_eventually_affineHilbertFunction_le` in `AffineDegree.lean`, without the
parameter `c`, and `sum_minimalPrimes_affineDegree_le_of_equidimensional` is now
`sum_affineDegree_minimalPrimes_le` in `AffineHilbertPurity.lean`, with the filtered form
`sum_affineDegree_minimalPrimes_filter_le`.
## `ArkLib/ToMathlib/RingTheory/MvPolynomial/CoefficientEvaluation.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/EvaluationDimension.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The definitions
`fixedCoefficientEvaluation`, `polynomialCoefficientEvaluation` and
`affineCoefficientEvaluation` keep their names; the coefficient count `k` is now `m`, the field
`F` is now `k`, and `hilbertPolynomial` is `affineHilbertPolynomial` throughout.
`fixedCoefficientEvaluation_totalDegree_le_one` is now `totalDegree_fixedCoefficientEvaluation_le`.
`fixedCoefficientEvaluation_hilbertPolynomial_natDegree_le` is now
`natDegree_affineHilbertPolynomial_le_of_fixedCoefficientEvaluation_mem`, without `J ≠ ⊤` or
`c ≤ k`. `polynomialCoefficientEvaluation_hilbertPolynomial_natDegree_le` is now
`natDegree_affineHilbertPolynomial_le_of_polynomialCoefficientEvaluation_mem`, and
`coefficientEvaluation_hilbertPolynomial_natDegree_le` is now
`natDegree_affineHilbertPolynomial_le_of_affineCoefficientEvaluation_mem`; both drop `J ≠ ⊤` and
keep `c ≤ m`, which the test shows is needed. The three bounds are specializations of the new
`natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det`, which bounds the dimension of an
ideal containing polynomials `p i` such that `p i - ∑ j, A i j • X (v j)` involves no variable
`v j`, for a matrix `A` of unit determinant, and of its Vandermonde case
`natDegree_affineHilbertPolynomial_le_card_sub_of_sum_pow_mul_X_sub_mem`. The test shows that
distinct evaluation points are needed.

`retainedPrime_hilbertPolynomial_natDegree_le_of_coefficientLocalization` is not ported; it is
main's `natDegree_affineHilbertPolynomial_le_of_surjective_away_away` followed by the dimension
bound on `J`, and the test derives the source statement.

From the source's `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/DimensionSensitive.lean`:
`fixedCoefficientEvaluation_dimensionSensitive_component` is now
`natDegree_affineHilbertPolynomial_add_ncard_le_of_fixedCoefficientEvaluation`, stating
`natDegree + #{i | fixedCoefficientEvaluation m (α i) (y i) ∈ P} ≤ m` for positive dimension in
place of the conjunction `natDegree ≤ k ∧ #(cutsInIdeal P cuts) ≤ k - natDegree`, without
primality, and counting with `Set.ncard` instead of the source's `cutsInIdeal` Finset. The test
derives the conjunction and shows that positive dimension is needed.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ComponentDimension.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `MvPolynomial.natDegree_affineHilbertPolynomial_add_ncard_le_of_polynomialCoefficientEvaluation`, a generic bound for the affine Hilbert degree plus the size of a set of polynomial-evaluation equations contained in an ideal of dimension greater than one. The source unit had no declaration with this name; this theorem provides the set-indexed count bound used by the source component theorem.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean`

Ported from the index and submodule part of
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/DerivativeBidegree.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, for any `σ` and cap coordinate `some i` in place of
`Fin 2` and `some 1`. `DerivativeBidegreeIndex` is the subtype of `cappedBidegreeExponents`, and
`derivativeWeight` is the condition `m (some i) ≤ c`. `restrictDerivativeBidegree` is now
`restrictCappedBidegree`, `finrank_restrictDerivativeBidegree` is now
`finrank_restrictCappedBidegree`, and `derivativeBidegreeMap_surjective` is now
`monomialMap_cappedBidegreeExponents_surjective`. `twoJetMonomialCount`,
`natCard_cappedTwoJetIndex` and `cast_twoJetMonomialCount` are now
`two_mul_ncard_cappedDegreeExponents_fin_two` in `CappedDegree.lean`, and `CappedTwoJetIndex` and
`cappedTwoJetEquiv` are `cappedDegreeExponents (Fin 2) 1 b c` and
`cappedDegreeExponentsFinTwoEquiv`. `derivativeBidegreeIdeal` is
`RingHom.ker (monomialMap k (cappedBidegreeExponents σ i a b c))`. `twoJetMonomialCount_mono` is
not ported.

`mixedDerivativeImageDegree` from
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/DerivativeBidegree.lean`
at the same revision is now `cappedBidegreeMixedVolume`, defined as
`h * cappedDegreeMixedVolume b c b c + 2 * a * cappedDegreeMixedVolume j r b c`, with the source
formula as `cappedBidegreeMixedVolume_eq` under `c ≤ b`; `mixedDerivativeImageDegree_mono_source`
is now `cappedBidegreeMixedVolume_mono_left`. New, with no source counterpart:
`cappedBidegreeMixedVolume_mono_right`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`mem_restrictDerivativeBidegree_of_bidegree` became `MvPolynomial.mem_restrictCappedBidegree_of_mem_restrictBidegree`. It applies to an arbitrary indexed coordinate and turns a bidegree rectangle plus a coordinate-degree bound into a capped bidegree bound.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean`

Ported from the exponent and submodule part of
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/TwoJetDegree.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, for any `σ` and cap coordinate `i` in place of
`Fin 2` and `1`. `restrictTwoJet` is now `restrictCappedDegree`, with `mem_restrictTwoJet`,
`mul_mem_restrictTwoJet` and `finrank_restrictTwoJet` now `mem_restrictCappedDegree`,
`mul_mem_restrictCappedDegree` and `finrank_restrictCappedDegree` (the source's closed form
follows from `two_mul_ncard_cappedDegreeExponents_fin_two`). `twoJetMap` is
`monomialMap k (cappedDegreeExponents (Fin 2) 1 b c)`, and `twoJetMap_surjective` is now
`monomialMap_cappedDegreeExponents_surjective`. `twoJetMap_totalDegree_le` and
`twoJetMap_derivativeDegree_le` are now `monomialMap_mem_restrictCappedDegree`. `twoJetLift` and
its lemmas are `monomialLift`, `monomialMap_monomialLift` and `totalDegree_monomialLift_le_one`;
`twoJetIdeal` is `RingHom.ker` of the monomial map, prime by `RingHom.ker_isPrime`, and
`twoJetIdeal_hilbertPolynomial_natDegree` is `natDegree_affineHilbertPolynomial_ker_of_surjective`.
`quotientTwoJetLE` is a `Submodule.map` along the quotient map, and
`quotientTwoJetLE_finrank_add_le` is `Submodule.finrank_map_mkₐ_span_singleton_add_le`.
`twoJetCutMap` and `twoJetCutMap_surjective` are not ported: the kernel of the composite is the
comap.

`fixedFiberDerivativeImageDegree` from
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/DerivativeBidegree.lean`
at the same revision is now `cappedDegreeMixedVolume`, with `fixedFiberDerivativeImageDegree_eq`,
`_mono_source` and `_mono_map` now `cappedDegreeMixedVolume_eq`, `_mono_left` and `_mono_right`,
and `le_fixedFiberDerivativeImageDegree` now `le_cappedDegreeMixedVolume`.
`cappedTriangleDegree_le` and `b_le_cappedTriangleDegree` are derived in the test from
`cappedDegreeMixedVolume_self`. New, with no source counterpart: `cappedDegreeMixedVolume_comm`
and `cappedDegreeMixedVolume_self`.

`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/TwoJetPoints.lean` at the same revision is the case
`S = cappedDegreeExponents (Fin 2) 1 b c` of
`ArkLib/ToMathlib/RingTheory/MvPolynomial/MonomialMap.lean`: `twoJetPoint` is `monomialPoint`,
`twoJetPoint_injective` is `monomialPoint_injective`, `aeval_twoJetPoint` is
`aeval_monomialPoint`, `aeval_twoJetLift_iff` and `twoJetLift_linear_cut` follow from
`aeval_monomialPoint`, `monomialMap_monomialLift` and `totalDegree_monomialLift_le_one`,
`mem_zeroLocus_twoJetHypersurfaceIdeal_iff` and its `_source` form are
`monomialPoint_mem_zeroLocus_comap_iff`, and
`exists_twoJetPoint_of_mem_zeroLocus_twoJetIdeal` is
`exists_monomialPoint_eq_of_mem_zeroLocus_ker`. The `CappedDegreePoints` section of the test
exercises this case.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/MonomialMap.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/BidegreePoints.lean` and the lift of
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/DerivativeBidegree.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, for any exponent set `S`. `bidegreePoint` is now
`monomialPoint`, `bidegreePoint_injective` is now `monomialPoint_injective`,
`aeval_bidegreePoint` is now `aeval_monomialPoint`, `aeval_bidegreeLift_iff` follows from
`aeval_monomialPoint` and `monomialMap_monomialLift`, and
`mem_zeroLocus_bidegreeHypersurfaceIdeal_iff` and its `_source` form are now
`monomialPoint_mem_zeroLocus_comap_iff` for any ideal.
`exists_bidegreePoint_of_mem_zeroLocus_bidegreeIdeal` is now
`exists_monomialPoint_eq_of_mem_zeroLocus_ker`. `derivativeBidegreeLift` and
`bidegreeLift_linear_cut` are now `monomialLift`, `monomialMap_monomialLift` and
`totalDegree_monomialLift_le_one`.

`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/DerivativeBidegreePoints.lean` at the same revision is
the case `S = cappedBidegreeExponents σ i a b c`. `derivativeBidegreePoint` is `monomialPoint`;
`aeval_derivativeBidegreePoint` and `aeval_derivativeBidegreeLift_iff` follow from
`aeval_monomialPoint` and `monomialMap_monomialLift`;
`mem_zeroLocus_derivativeBidegreeHypersurfaceIdeal_iff` is
`monomialPoint_mem_zeroLocus_comap_iff`;
`exists_derivativeBidegreePoint_of_mem_zeroLocus_derivativeBidegreeIdeal` is
`exists_monomialPoint_eq_of_mem_zeroLocus_ker`; and `derivativeBidegreePoint_injective` is
`monomialPoint_injective`.

## `ArkLib/ToMathlib/RingTheory/MvPolynomial/StandardMonomials.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/StandardMonomials.lean`, namespace `AffineHilbert`:
`standardExponents`, `standardSpace`, `eq_zero_of_mem_standardSpace_of_mem_ideal`,
`exists_standard_representative`, `standard_representative_unique`, `standardQuotientMap` with
`standardQuotientMap_bijective` (now the equivalence `standardQuotientEquiv`),
`standardDegreeLE` with `standardFilteredMap_bijective` (now `standardDegreeLEEquiv`),
`hilbertFunction_eq_standard_count`, `standardExponents_lower` and
`exists_finset_forbidden_standardExponents`. The source fixed the order `degLex`, which required
`LinearOrder σ` and `WellFoundedGT σ` in every statement. Here the definitions and the
unfiltered statements hold for every monomial order, and the filtered statements for every graded
one; the source statements are the `degLex` specializations. `standardExponents_span_singleton` is
from `PrincipalCut/Polynomial.lean`, and `exists_eval_eq_affineHilbertFunction` is the existence
half of `exists_hilbertPolynomial` in `Hilbert/Polynomial.lean`, at the same revision, with
coefficients in any field of characteristic zero instead of `ℚ`.

Deferred to the Hilbert-polynomial slice (`Hilbert/Polynomial.lean` at the same revision): the
chosen `hilbertPolynomial` and its uniqueness, its value for finite-dimensional quotients and for
`⊥`, its nonvanishing for proper ideals, the converse from degree zero to finite dimension, and the
principal-cut statement on its degree and leading coefficient.

`MvPolynomial.affineHilbertFunction_eq_standard_count`: This is the source statement.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz.lean`

This file is extracted from ArkLib at source revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalOpen/Cuts.lean`. The theorems
`MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus`,
`MvPolynomial.mem_zeroLocus_and_eval_ne_zero_iff_retained` and
`MvPolynomial.mem_zeroLocus_and_cut_iff_retained` keep the source names and statements, with the
coefficient field and extension renamed to `k` and `K` to match
`Mathlib.RingTheory.Nullstellensatz`. The source proved the ideal-sum description of the cut
inline; here it is the public lemma `MvPolynomial.mem_zeroLocus_sup_span_singleton_iff`, derived
from `MvPolynomial.zeroLocus_sup`. The prime-ideal step is the generic
`Ideal.exists_mem_retainedMinimalPrimes_le`.

Finite-quotient point counts are in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient`. Deferred: the Krull-dimension drop of
the same source file and every result that needs algebraic closedness or the affine Hilbert
polynomial.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/AffineHilbertPolynomial.lean`

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:
`AffineHilbert.finite_zeroLocus_and_ncard_le_hilbertPolynomial` in
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Polynomial.lean`, stated here for
`MvPolynomial.affineHilbertPolynomial`. The source assumed Krull dimension zero; the bound is
also stated under the `Module.Finite` hypothesis that its proof uses, with the source statement
as `finite_zeroLocus_and_ncard_le_affineHilbertPolynomial`.

From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Degree.lean` at the same revision:
`AffineHilbert.finite_zeroLocus_and_ncard_le_affineDegree`, which assumed that the Hilbert
polynomial has natural degree zero. That statement is kept, and the bound is also stated under
the equivalent `Module.Finite` hypothesis as `ncard_zeroLocus_le_affineDegree`. Both are derived
from `ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial`.

`MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree`: This is the source
statement.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/AgreementIncidence.lean`

The sharp bounds of `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/SharpExcluded.lean`,
`SharpCutFamily.lean` and `SharpPrimeFamily.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `affineAgreementIncidence_bound_off_excluded_sharp`
is now `card_le_of_agreement_off_excluded_sharp`, through the new
`card_le_of_agreement_off_excluded_of_ratio`, without `0 < b`, `A ≤ card ι` or `s ∉ P`. `affineAgreementIncidence_bound_sharp` is now
`card_le_of_agreement_of_subsingleton_sharp`. `iteratedRetainedCutFamily_incidence_sharp` is now
`card_le_mul_pow_of_iteratedRetainedCutFamily`, through the new
`card_le_mul_pow_of_forall_mem_zeroLocus`, and
`iteratedRetainedCutFamily_incidence_off_excluded_sharp` is now
`card_le_of_agreement_off_excluded_sharp_of_iteratedRetainedCutFamily`, with high cuts of degree
at most `h` and dimension at most `d`. `retainedPrimeFamily_incidence_bound_sharp` is not ported;
it follows from `card_le_mul_pow_of_forall_mem_zeroLocus` and
`card_le_of_agreement_of_subsingleton_sharp`.

This file already holds the ports of the source's `Incidence/Agreement.lean`,
`Incidence/Excluded.lean`, the hypersurface bounds, and PR #1008's sharp bounds. This branch adds
one induction and one covering lemma, and derives the existing bounds from them.

`card_le_prod_of_agreement_off_excluded` is now the only induction in the file. It takes a
threshold function `T : ℕ → ℕ` and ratios `R : ℕ → ℚ` with `T t ≤ A`, `0 ≤ R t` and
`(n - j) * b ≤ R t * (A - j)` for `j < T t` and `t < natDegree`, and bounds the points by
`affineDegree P * ∏ t < natDegree, R t`. It replaces the three private inductions of the source's
`DimensionSensitive.lean` (`affineAgreementIncidence_bound_dimensionSensitive_aux`,
`affineAgreementIncidence_bound_dimensionSensitive_off_excluded_aux` and
`affineAgreementIncidence_bound_hybrid_off_excluded_aux`) and the induction that PR #1008 placed
in `card_le_of_agreement_off_excluded_of_ratio`.
`card_le_incidenceProduct_of_agreement_off_excluded` and
`finite_and_ncard_le_incidenceProduct_of_agreement_off_excluded` are its instance with the
incidence factors, bound `affineDegree P * incidenceProduct n A b T natDegree`; the constant,
dimension-sensitive and hybrid bounds of the source are the thresholds `fun _ ↦ L`,
`fun t ↦ m - t` and `fun t ↦ if t = 0 then L else m + 1 - t`. The test checks the core theorem
on three parallel lines with `T = R = 2`, and the iterated form on the line `x = 0` of the plane
after the fixed cut `X 0`.

`card_le_sum_of_forall_mem_zeroLocus` bounds a finite set covered by the zero loci of a finite
family of ideals by the sum of bounds on each member. It replaces the unions written out in the
source's `iteratedRetainedCutFamily_incidence_off_excluded_hybrid{,_two}`.
`card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily` is the incidence
bound on the iterated retained cut family of a family `Ps` by fixed cuts of degree at most
`h ≥ 1`, for any threshold function, with bound `V * incidenceProduct n A b T D` under
`∑ P ∈ Ps, affineDegree P * h ^ natDegree ≤ V` and a dimension bound `D` on the primes met. The
source's convention, `∑ P ∈ Ps, affineDegree P ≤ V` with members of dimension `d` and the fixed
cuts contributing `B ^ d`, is derived in the test by `sum_affineDegree_mul_pow_le` and
`card_le_incidenceProduct_of_iteratedRetainedCutFamily_of_sum_affineDegree_le`, and a test shows
that `1 ≤ h` is needed.

Relative to PR #1008 (head `69c8e7f24`), no public declaration is dropped or renamed, and no public
type changes. `card_le_of_agreement_off_excluded` names its instance binder `[hP : P.IsPrime]` as on
main, where #1008 wrote `[P.IsPrime]`. The private `sub_mul_sub_add_one_le` moved to
`IncidenceProduct.lean`, and a private `le_fintypeCard_of_le_ncard` is added. Only proofs change:
`card_le_of_agreement_off_excluded_of_ratio` is the core theorem with constant `T` and `R`;
`card_le_of_agreement_off_excluded_sharp` goes through
`card_le_incidenceProduct_of_agreement_off_excluded` and `incidenceProduct_const`;
`card_le_mul_pow_of_forall_mem_zeroLocus` and `card_le_sum_of_agreement_off_excluded` go through
`card_le_sum_of_forall_mem_zeroLocus`; and
`card_le_of_agreement_off_excluded_sharp_of_iteratedRetainedCutFamily` is the iterated incidence
bound with threshold `fun _ ↦ L` and `D = d`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Incidence.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`ReedSolomon.primeBaseHypersurface_incidence_off_excluded` is generalized as `MvPolynomial.card_le_of_agreement_off_excluded_of_principalCut`.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/BidegreeIncidence.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/BidegreeExcluded.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `AffineHilbert`.

`bidegreeHypersurface_source_incidence_off_excluded_sharp` is renamed to
`MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp` and generalized by removing the
`A ≤ n` premise. `bidegreeHypersurface_source_incidence_off_excluded_hybrid` and
`bidegreeHypersurface_source_incidence_off_excluded_hybrid_two` are renamed to
`MvPolynomial.bidegreeHypersurface_incidence_off_excluded_hybrid` and
`MvPolynomial.bidegreeHypersurface_incidence_off_excluded_hybrid_two`, respectively; the
two-coordinate theorem drops its unused `A ≤ n` premise. The `_sharp_one` and `_sharp_two` source
declarations are renamed to
`MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_one` and
`MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_two`; both are generalized by
removing `A ≤ n`. Nothing was deferred or left unported.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/CappedBidegreeIncidence.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/DerivativeBidegreeExcluded.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`derivativeBidegreeHypersurface_source_incidence_off_excluded_hybrid_two_of_lt` and `derivativeBidegreeHypersurface_source_incidence_off_excluded_hybrid_two` are covered by `MvPolynomial.cappedBidegreeHypersurface_incidence_off_excluded_hybrid_two`. The destination theorem is generalized to every positive `c` and drops the assumptions `r ≤ j` and `A ≤ n`. Neither source theorem is omitted.

Acceptance cases in `ArkLibTest/ToMathlib/RingTheory/Nullstellensatz.lean` include a rational point on a positive-dimensional coordinate line, with `n = 4`, `A = 2`, `L = 1`, and `k = 0`. The merged acceptance file retains its principal-open, affine-Hilbert, and zero-locus examples.

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/TwoJet.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The capped-bidegree incidence proof now uses `Ideal.map_prime_principalOpenData_of_surjective` for its prime ideal, comap, generator, principal-open, and lifted-cut transport. No public declaration was renamed or removed.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/CappedDegreeIncidence.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/TwoJet.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

`AffineHilbert.twoJetHypersurface_source_incidence_sharp` → `MvPolynomial.cappedDegreeHypersurface_incidence_sharp`. The theorem removes the assumptions `0 < k`, `c ≤ b`, and properness of `span {g}`, and states agreement counts using `Set.ncard`. No source declaration was deferred or omitted.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/DimensionSensitiveIncidence.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/DimensionSensitive.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`: the incidence bounds. Throughout, points lie
in any field extension `K` of `k`, cuts are indexed by any `Fintype ι` instead of `Fin n`, counts
are `Set.ncard` of set-builder sets instead of the source's `cutsInIdeal` and `agreementIndices`
Finsets, `principalOpenZeroLocus` is written out, primality is an instance, the coefficient count
`k` is `m`, and `s ∉ P` and `A ≤ n` are dropped. Every bound is a corollary of
`card_le_incidenceProduct_of_agreement_off_excluded`; the only private declaration is
`hybrid_terminal`. The dimension-sensitive budget `natDegree Q ≤ k ∧ #bad ≤ k - natDegree Q` is
written `natDegree Q + #bad ≤ m`. The hybrid budget, which the source required for every
positive-dimensional `Q` as `natDegree Q ≤ k + 1 ∧ (1 < natDegree Q → #bad ≤ k + 1 - natDegree Q)`,
is required only as `1 < natDegree Q → natDegree Q + #bad ≤ m + 1`, a weaker hypothesis; the test
lemma `add_le_of_hybridBudget` converts the source form.

`affineAgreementIncidence_bound_dimensionSensitive` is now
`card_le_dimensionSensitiveIncidenceProduct_of_agreement`.
`affineAgreementIncidence_bound_dimensionSensitive_off_excluded` is now
`card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded`; the source's
`natDegree Q ≤ k ∧ (#bad ≤ k - natDegree Q ∨ U(Q) ⊆ excluded)` is weakened to
`natDegree Q + #bad ≤ m ∨ U(Q) ⊆ excluded`. `affineAgreementIncidence_bound_hybrid_off_excluded`
is now `card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded`. The
`Fin n`-indexed source statements are derived in the test as
`card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded_fin` and
`card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded_fin`.
`finite_agreementLocus_and_ncard_le_dimensionSensitive`,
`finite_agreementLocus_off_excluded_and_ncard_le_dimensionSensitive` and
`finite_agreementLocus_off_excluded_and_ncard_le_hybrid` are now
`finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_agreement`,
`finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded` and
`finite_and_ncard_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded`, with
the same changes. `finite_agreementLocus_off_excluded_and_ncard_le_hybrid_two` is not ported; the
test derives it from the hybrid locus bound and `hybridDimensionSensitiveIncidenceProduct_le_two`.
`m ≤ A` and `L ≤ A` are kept and tested necessary.

`iteratedRetainedCutFamily_incidence_off_excluded_hybrid` is now
`card_le_hybridDimensionSensitiveIncidenceProduct_of_iteratedRetainedCutFamily`. It relaxes
`natDegree P = d` to `≤ d`, drops `s ∉ P` for members and `A ≤ n`, allows cuts of degree at most
`b` with `0 < b` instead of degree one, and replaces `0 < B` and `∑ P, affineDegree P ≤ V` by
`1 ≤ h` and `∑ P, affineDegree P * h ^ natDegree P ≤ V`, so the conclusion has no `B ^ d`
factor. The product length `min (d - 1) k + 1` becomes `min d (m + 1)`, which is equal for
`d ≥ 1` and no larger for `d = 0`. `iteratedRetainedCutFamily_incidence_off_excluded_hybrid_two`
is now `card_le_hybridDimensionSensitiveIncidenceProduct_two_of_iteratedRetainedCutFamily`, with
the same changes, `natDegree P = 2` relaxed to `≤ 2`, and the two factors scaled by `b`. The test
derives the source statement of the first (members of dimension exactly `d`, `s` off every
member, degree-one cuts, the source budget, `V * B ^ d` and length `min (d - 1) m + 1`) and the
`V * B ^ 2` form of the second with degree-one cuts, both through `sum_affineDegree_mul_pow_le`.

`finite_fixedCoefficientAgreementLocus_and_ncard_le_dimensionSensitive` is now
`finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation`, without
`s ∉ P` or `A ≤ n`; `m ≤ A` is tested necessary (the locus is infinite without it).
`finite_fixedCoefficientAgreementLocus_and_ncard_le_firstOrderFiberRatio` is not ported; the
test derives it with `dimensionSensitiveIncidenceProduct_le_one`.

`finite_biUnion_and_ncard_le_sum` and `retainedPrimeFamily_finite_biUnion_and_ncard_le` are not
ported: they have no consumer in the source, and they follow from Mathlib's
`Finset.set_ncard_biUnion_le` and `Set.Finite.biUnion`. The test derives both. The arithmetic of
the source file is in `IncidenceProduct.lean`, and
`fixedCoefficientEvaluation_dimensionSensitive_component` is in `CoefficientEvaluation.lean`.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/FiniteQuotient.lean`

These declarations are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/ZeroLocus/ZeroDimensional.lean`. Their statements are unchanged
apart from renaming the fields to `k` and `K` to match `Mathlib.RingTheory.Nullstellensatz`.
`finite_zeroLocus_and_ncard_le_of_krullDimLE_zero` is from the same file and keeps the source
statement.

Hilbert-polynomial interpretations belong to later geometry layers.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/FiniteZeroLocus.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/ZeroLocus/Finite.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `AffineHilbert`.

`zeroLocusEvaluation_injective` keeps its name and radical hypothesis; the points may now lie in
any algebraically closed extension `K` of `k` rather than in `k` itself.
`moduleFinite_of_finite_zeroLocus` and `finite_zeroLocus_iff_hilbertPolynomial_natDegree_zero`
(here `finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero`) no longer assume that `I`
is radical: the radical has the same zero locus (`zeroLocus_radical`, new) and a Hilbert
polynomial of the same natural degree (`natDegree_affineHilbertPolynomial_radical`).
`finite_zeroLocus_iff_moduleFinite` is new.

Deferred: the forward direction for points in a proper algebraically closed extension `K` of `k`.
Its proof needs the finitely many maximal ideals of the quotient, since the functions from a
finite set to `K` do not form a finite-dimensional `k`-space.

## `ArkLib/ToMathlib/RingTheory/Nullstellensatz/PrincipalOpenParametrization.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `regular_principalOpen_graph_restriction`, which gives ideal restriction and cut nonvanishing when a polynomial graph covers the regular principal open of a positive-dimensional prime component. This shared result is used by both component-recognition results.

## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveFinite.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example uses `D = 1`, `A = m = 2`, `M = 0`, `μ = 1`, `k = 2`, `n = 2`, and `ℓ = h = 1`, with distinct centers in `ZMod 5` and zero received curves. It computes the strict slot surplus `10 < 11` and constructs the certificate with an agreement threshold matching the number of centers.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/FiniteCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

A `ZMod 5` shifted-surplus acceptance example uses `n = 2`, two distinct centers, and `A = 2`, so the two positions can meet the agreement threshold.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/Profile.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check a concrete profile with support dimension `7`, local rank `3`, height slots `11`, and shifted row bound `10`. They verify the support-cardinality and column-weight identities and construct symbolic line and polynomial-curve certificates over `ZMod 5`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/CurveTransfer.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example uses the rate certificate to obtain a curve certificate, constructs a separant chain, and shows that any agreeing degree-<2 candidate for the two-point zero word is zero. It then selects a challenge outside the finite exceptional set in an infinite extension field.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FirstOrder/FirstOrderHybridList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example invokes `FirstOrderCurveCertificate.jetDegree_one_le` on a concrete curve certificate.

## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder.lean`

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/FirstOrder.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Extended the existing acceptance file with a concrete five-part `automaticParameterBounds` case at rate `1/2` and slack `1/8`, concrete closed list and exception envelope cases, a one-stage direct-ratio separant-chain bound, and the cap identity through `firstOrderCurveStageCap_add_height_eq_of_factors`. Removed the redundant ratio restatement; no separate acceptance module was added.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FirstOrder/FirstOrderHybridList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

A nonempty singleton solution family exercises both root-coverage theorems, the regular derivative-capped and identity-pair counts, symbolic raw and optimized counts, field raw and optimized counts, the direct field theorem, and the automatic theorem. Descent examples cover characteristic zero at degree zero and characteristic two at actual degree one with total cap three. A concrete finite-characteristic curve certificate invokes both characteristic-guarded certificate bridges.

## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition.lean`

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases use the shared envelope record for the scale-1000 recipe and check the scale-300 order bound, length equality, jet and integer guards, total-jet bound, low- and high-rate ratio branches, and envelope existence.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/RatePartition/MathematicalUniform.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check the mathematical-uniform parameter examples.

## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition.lean` — fixed-rate gate cases

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/FixedRateGate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The aggregate keeps a concrete strict gate at rate `1/2` and gap `1/4`, together with the selected multiplicity's finite checks and finite-parameter existence. The zero-gap boundary case was removed because the theorem's positive-gap hypothesis states the restriction directly.

## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition.lean` — uniform rate-gamma cases

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/UniformGamma.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance cases check concrete low- and high-rate base bounds and margins for arbitrary and uniform derivative orders, the uniform order's lower bound, and boundary cases for the small-gap and positive-order hypotheses.
## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport.lean`
The aggregate keeps concrete low- and high-rate base bounds and margins for the uniform derivative order, together with its lower bound.

Ported from `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added a concrete order-500 finite-ratio surplus acceptance case. The example uses a natural cutoff satisfying the level bound. The old nested test path was removed; the acceptance case is in this consolidated test file.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/PartitionSupport/RateCertificate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance case checks a concrete scale-300 curve certificate at `δ = 1/5`.

## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Interpolation/PartitionSupport/MomentSource.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/RatePartition/SourceEstimate.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The aggregate includes a concrete `d = 500`, `W = 1` instance of `partitionSupport_dimension_gt_moment`, using the lower-tail second-moment bound at logarithm `log 3000`. It checks the numeric rate and scale hypotheses and exercises the dimension conclusion without generic theorem restatements. The source-specific wrapper is not needed because the existing theorem covers it.
## `ArkLibTest/Data/CodingTheory/HiddenDerivative/Parameters/WeightedSupport.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TaylorCutoff.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example checks a concrete small-gap block against both the Taylor cutoff bound `2 * m - 1 < n` and the ambient-dimension bound.
## `ArkLibTest/Data/CodingTheory/ReedSolomon.lean`

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added a concrete nonvacuity example over `ℚ` for one degree-`< 1` solution agreeing at one coordinate, checking the Reed–Solomon specialization.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/ListDecodability.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Counting/DirectJetList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Added `ZMod 5` acceptance examples showing the zero polynomial as an agreeing root, applying the regular-stage estimate, and obtaining the finite actual-chain, common-order, and coarse bounds from the final theorem.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Profile.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/Bounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check the exact-ceiling and closed cardinality bounds, finite-set and explicit-envelope automatic bounds, both slack bounds, and tight and squarefree profile bounds on a concrete singleton family over `ℚ`.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean`

**Historical port-time test notes, not current suite coverage.** The following descriptions record
acceptance cases that existed at earlier port revisions. The consolidated suite currently retains
15 concrete examples: extension descent, exact-line transfer, graph-line recognition and its
exceptional bound, tuple collision and avoiding specialization; on the shared positive-dimensional
prime-component fixture, graph parametrization, common-agreement extraction, admissible chart-tuple
construction, principal-open chart-graph inclusion, admissible Frobenius-pair construction, and
principal-open Frobenius-graph inclusion; symbolic point recognition with a nonzero second tuple
component; and derivative-capped challenge, exceptional-set, and first-order incidence bounds.

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The earlier joint-chart acceptance case reusing the shared concrete equation and numerator identity remains historical. The former `K = 2`, `k = 1` component graph case is covered by the current shared fixture: it uses the returned graph proof to show the zero regular point lies on the recognized graph. Current coverage is summarized above.

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

A historical acceptance example used the algebraic-closure prime-component fixture to check a degree-bounded pair and a nonzero common-agreement count. The current suite retains a compact component-agreement case on the shared fixture, producing a degree-bounded tuple with at least one common agreement.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ComponentRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Historical acceptance cases checked a positive-dimensional prime component's sample interpolation, graph coverage, and nonzero restricted separant, along with single-tuple and finite-family exact-agreement bounds. The current suite keeps a compact graph-pair instance with the regular zero point on the returned graph; the shared fixture also supports the component-agreement, chart-admissibility, and incidence examples summarized above.

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Historical acceptance cases checked polynomial-valued source-prime bounds, a degree-zero chart prime, chart/source/first-order component bounds, and finite incidence counts. Those broader bounds remain historical; the current suite includes principal-open chart-graph inclusion and Frobenius-graph inclusion instances on the shared component fixture.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/GraphCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

A historical acceptance case applied `admissibleFrobeniusPairs_card_le_degreeOf` to a singleton family containing an admissible pair from the concrete component fixture; that specific cardinal-bound example remains historical, and the production theorem is unchanged. The current suite checks a concrete admissible Frobenius pair and the zero point's membership in its graph.

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

A historical acceptance example applied `exists_admissibleChartTuple_of_primeTaylorComponent_agreements` to the component ideal, agreement cuts, and separant fixtures. The current suite retains a compact instance of this theorem, constructing an admissible tuple and using its returned graph proof to place the zero regular point on that tuple's graph.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/SharpGeneralEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Historical acceptance cases invoked the sharp fixed-center and terminal-recognition bounds and checked finite regular and exceptional bad-challenge sets. The current consolidated suite retains one nonempty derivative-capped bad-challenge bound instance, as summarized above.

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Kept the nonempty two-message ordinary regular-bound instance. Added concrete checks applying `finite_powerBatchedBadChallenges_card_le_derivativeCapped_of_exponent`, `exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent`, and `exists_exceptional_frobeniusPowerSeparableSolutions_at`, with their cardinal bounds, to the challenge set `{0}` over `ℂ`. Removed the standalone finite polynomial-tuple collision example to meet the shared file limit; the stronger root-avoiding specialization example remains.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/RegularChart.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance examples apply the supplied-center theorem and the new center-free theorem to the existing nonempty singleton challenge set over the two-point field fixture. Each example verifies `card ≤ 2`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/RegularSolutions.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example checks a concrete two-message instance and shows that challenge zero belongs to an exceptional set of size at most two.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/SeparableSolutions.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance example specializes the existing `exists_exceptional_frobeniusPowerSeparableSolutions_at` at `ℓ = 1` and `L = k`, checks the exceptional-set cardinality, and exhibits a challenge outside the set with an exact correlated pair using `exactCorrelatedPair_of_powerAgreement_one`. Both declarations are already on `main`, so there are no renamed or generalized declarations. The source wrapper `exists_exceptional_frobeniusSeparableSolutions` is not added because the existing bound and exact-agreement conversion cover its statement; the source file has no other declarations.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/FactorSolutions.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The source declaration `exists_exceptional_frobeniusFactorSolutions` is covered by `exists_exceptional_frobeniusPowerFactorSolutions`, generalized from a single line to polynomial curves with arbitrary tuple length and the current coefficient-height and jet-degree interfaces. The acceptance example checks the tuple-length-one conversion from exact power agreement to an exact correlated pair using `exactCorrelatedPair_of_powerAgreement_one`. No source declaration is left uncovered. A separate single-line wrapper was omitted because the generalized theorem and conversion theorem already provide its statement.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean`

Acceptance examples at `δ = 1/5` and `n = uniformMathematicalCapacityLength (1/5)`, with the gap hypothesis derived from the integer guards. There is one example each for the extension-field curve, base-field curve and line theorems, over `ℚ` (and `AlgebraicClosure ℚ`). Each exhibits a challenge outside the exceptional set with an exact witness for the zero candidate.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder.lean`

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check the base-field height theorem at the tight exponent, the base-field certificate theorem, and the extension-field height and certificate theorems. Both certificate cases reuse a certificate for the same one-point zero curve over `ℚ`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Sharp.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example builds a concrete profile with derivative cap `1`, checks that it is curve-verified by `decide`, and applies `exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized` to get a base-field challenge with exact power agreement for `0`.
Acceptance examples appended for the new declarations:

- `exists_exceptional_firstOrder_hybrid` and `exists_exceptional_firstOrder_hybrid_base` on the equation `Y₁` over `ℂ` with `n = 2`, `D = 1`, `A = 2`, `h = 0`, `μ = M = 1`, with all hypotheses discharged by computation.
- `exists_automaticFirstOrder_hybridEquation` (`ℚ → ℂ`), `exists_automaticFirstOrder_hybridEquation_base` and `automatic_first_order_line_agreement` (over `ℚ`) at `ρ = 1/2`, `a = 3/4`, `n = 4`, `k = 2`, `A = 3`, with the threshold inequality `a₁(1/2) < 3/4` proved.
- `automaticFirstOrder_rate_bounds` over `ℚ` at `ρ = 1/2`, `η₁ = 1/8`.
- `automaticFirstOrder_hybrid_mcaError_le` and `automaticFirstOrder_rate_mcaError_le` over `ZMod 2749`, where the characteristic guard is discharged by bounding the automatic derivative cap at `ρ = 1/2`, `η₁ = 1/8` below `2749` via `automaticDerivativeCap_le_inv_eta`.
- `exists_uniformFirstOrder_lineMca_of_two_le` over `ℚ` at `n = 3`, `k = 2`, `A = 3`, which also exercises `FirstOrderSymbolicCertificate.exists_exceptional_hybrid`.
Ported from the new declarations above; the source revision has no matching examples. Acceptance examples:

- `exists_exceptional_firstOrder_hybridCurve_optimized` over `ℂ` for the equation `Y₁` (`n = 2`, `D = 1`, `A = 2`, `h = 0`, `mu = M = 1`), with every hypothesis discharged concretely. This also exercises `exists_exceptional_ordinaryCurveTail`.
- `exists_baseExceptional_firstOrder_hybridCurve_optimized` on the same instance, with `ℂ` as the base field.
- `exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized` over `ℚ` at three points (`D = 1`, `A = n = 3`, `ell = 1`, `m = 1`, `M = 0`, `mu = 1`, `h = 1`). The slot surplus (6 < 8) is checked by `norm_num`, and the example finds a challenge outside the exceptional set where the zero candidate has full agreement and exact power agreement. This also goes through `exists_baseExceptional_firstOrder_hybridCurve_including_fullDimension`.
- The three existing examples for the changed `HybridCurveTransfer` theorems now pass `coeffNatDegreeLE_coeffNatDegree _`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/LowRateSemantics.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Branchwise.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance examples check the low-rate symbolic certificate, complete-list and exact correlated-agreement rate bounds, and finite-field MCA error at concrete `1/16`-rate parameters. They also check branchwise finite-slack bounds, rate bounds, and finite-field MCA error at concrete `1/2`-rate parameters.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/FactorwiseList.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check singleton instances of `finite_factorwise_agreement_solutions_card_le_actual` and `finite_factorwise_agreement_solutions_card_le`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Certificate.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CurveBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example builds a finite first-order curve certificate at recovery degree `1` for the zero line over the file's two-point domain `factorwiseDomain`, and applies `exists_baseExceptional_retainedSquarefreeCurveAgreement_of_certificate` to exhibit a base-field challenge with exact power agreement. This also exercises the extension theorem, the tail-free theorem and the tail discharge. A second example is one concrete instance of `retainedSquarefreeCurveAgreementCharge_balancedSplit_le`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/LineCertificate.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Sharp.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example takes a concrete rational symbolic line certificate (`n = k = A = 2`, `M = B = 1`) and uses `exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate` to get a challenge at which `0` has an exact correlated pair with the zero line. A second example uses the concrete curve certificate `certificateCurve` with `exists_baseExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate` to get exact power agreement. The existing `_of_tail` example still passes and exercises the refactored general theorem with the ordinary-tail charge.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary.lean`

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example checks an exceptional set of size at most one and exact power agreement at a challenge outside it for zero messages over `ℂ`.
Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Equations/BaseEquation.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example takes the equation `Y₀²` over `ℚ` on a two-point domain, with `f = g = 0`, `D = 1`, `h = 0`, `mu = 2` and `A = 2`. It gets an exceptional set of size at most 2 from `exists_exceptional_ordinaryEquation_base`, picks a challenge in `{0, 1, 2}` outside that set, and derives an exact correlated-pair witness for the zero root, so the conclusion is not vacuous.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example applies `exists_baseExceptional_ordinaryPowerEquation` over `ℚ` to the reducible equation `Y₀²` on a three-point domain, with `n = 3`, `D = 1`, `ℓ = 1`, `h = 0`, `B = 2` and `L = A = 3`. The retention threshold `L = D + 2` lies in the free-retention regime that the fixed-split theorems do not reach. The charge `ordinaryUnifiedPowerFactorAtOrHeight 3 1 1 2 0 3 3` simplifies to `2`, and the example exhibits a challenge outside the exceptional set at which the zero root has exact power agreement with the zero word. Main's existing example for `exists_exceptional_ordinaryEquation_base` is unchanged and covers the fixed split.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart.lean`

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PointRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance cases consolidate default and exponent-aware point recognition with `K = 2`, `k = 1`, sample values `(0, 1)`, challenge `2`, and the high cut at `l = 1`; the exponent-aware case uses `τ = 1`. The new shared fixture declarations are `quadraticJetSampleEquation` and `quadraticJetSampleEquation_highNumerator_eq`. The equation has order-one numerator `−(Y₀ − 2)²`, which vanishes at the selected jet and is proved nonzero by evaluation at `Y₀ = 0`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/TaylorChart.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance case adds a concrete characteristic-two example with a nonzero one-point sample and checks the Frobenius chart reconstruction.

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance examples check both sharp bounds on a concrete nonempty admissible-pair set and its filtered family at `r = 0`; each bound evaluates to one.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/ExceptionalChallenges.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example checks a concrete nonempty singleton challenge set, its regular chart, three agreements, the absence of an exact degree-bounded pair, and the resulting bound of 12.

## `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PointRecognition.lean`

Ported from `ArkLibTest/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PointRecognition.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance cases check the zero case and a sample with second received value `1`, challenge `2`, `K = 2 > k = 1`, and a satisfied cut at `l = 1`. They check the reconstructed affine polynomial, jet, and cleared coefficient conclusions.
## `ArkLibTest/Data/Polynomial/Differential.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/FrobeniusCuts.lean` and `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorCutDegree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance module retains main's coefficient-map and regular-jet examples, high-cut and common-numerator checks. Added cases exercise the initial-equation joint-degree bound at a nonconstant center, a positive-length agreement cut with nonconstant numerator and separant, and sparsity for jet `(1, 0)`, preserving the allowed constant coefficient `1` while forcing the excluded linear coefficient to `0`. No public ArkLib declaration is added by this file.


Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/SolutionEmbedding.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance cases check `exists_regular_solution_jet_family_of_exponent` on `Y₀ = 0` over `ℚ` with `K = 2`, `k = 1`, and `τ = 4`, including the one-element family, initial equation, nonzero separant, the cut at order one, and agreement at two positions. They also check `exists_forall_jetEvaluation_ne_zero_map` for a nonempty regular family over `ZMod 2` and its algebraic closure.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Concrete `recursiveEq` examples check the initial-equation cap and degree, the common-numerator cap, and the Taylor-agreement cap and degree.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/RetainedCurve.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Moved the retained-curve acceptance cases to the differential directory test. They check `positiveCurveEquation 0 = 1` and concrete nonzero instances of the view degree identity, jet-degree bound, `Y₁` degree bound, and coefficient-height bound. The view case uses the public round-trip theorem `fromFlattenedRootFirst_rootFirstChallenge`.
Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/PolynomialCurve/Witness.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance case checks the generalized agreement characterization with a concrete characteristic-two solution and a cubic received curve.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/SharpCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

A singleton-jet case exercises `card_le_of_highTaylorCuts_of_agreement_sharp`.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Geometry/RegularCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The shared acceptance example applies `exists_regular_solution_jet_family_of_exponent` to the nonempty singleton family `{0}` for `Q = Y₀` over `ℚ`, and applies `card_le_of_regular_solutions_agreement` to the same family with one evaluation point.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TaylorCutoff.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance examples exercise the total-degree cast theorem and check `characteristic_bounds_of_max` over `ZMod 5` with `K = 5` and `ν = 3`, yielding the pivot bound at equality.
Ported from `ArkLibTest/Data/Polynomial/Differential.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The singleton `Y₀ = 0` example instantiates `card_mul_le_jetTotalDegree_mul`, the rational recursive count, its square-bound corollary, the agreement-derived regular-branch budget, the generic finite agreement theorem, and the sharp regular-agreement count. The standalone `Y₀ + Y₁` degree illustration was removed to keep the file under 1,500 lines while retaining the main theorem examples.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Counting/TaylorCharZeroSolutions.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

No library declarations were added. `separant_ne_zero_of_dependsOnJet_charZero` is covered by `PolynomialDifferential.separant_ne_zero`, using `jetDegreeCastsNeZero_of_ringChar` and `JetDegreeCastsNeZero.natCast_jetDegree_ne_zero`. `regularSolutions_card_le_of_agreement_charZero` is covered by `PolynomialDifferential.card_le_of_regular_solutions_agreement` together with `regularBranchRatBudget_of_agreement`, which allows general agreement predicates and a sufficient Taylor exponent. `boundedSolution_card_le_sq_totalJetDegree_charZero` is covered by `PolynomialDifferential.boundedSolution_card_le_sq_totalJetDegree`, using the characteristic-zero cast condition and the agreement-derived regular-branch budget. `finite_agreement_solutions_card_le_charZero` is covered by `PolynomialDifferential.finite_solutions_card_le_sq_totalJetDegree_of_agreement`; the Reed–Solomon close-polynomial specialization is `ReedSolomon.closePolynomialSet_card_le_of_differential_equation`.

An acceptance example checks generic separant nonvanishing for `Y₀ = 0` over `ℚ`, deriving the cast condition from characteristic zero. Existing examples in this file cover the generic square, finite-agreement, and regular-branch bounds. No production declarations were ported because the source results are covered by these more general APIs.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Semantic.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

No library declarations were added. The acceptance example computes that `Y₁` specializes to zero over `ℚ` at the zero polynomial, then applies `MvPolynomial.map_radicalContent_mul_radicalPrimPart_eq_zero_iff` with `differentialSpecializationHom` to establish the radical-factor zero disjunction. This records the proof recipe for the future `TailBound` port.

`root_content_or_positive` is covered by that generic theorem, followed by `map_mul`, `mul_eq_zero`, and `differentialSpecializationHom_apply`. The root-first declarations `contentEquation`, `positiveEquation`, `fromRootFirst`, `rootFirst_fromRootFirst`, `fromRootFirst_rootFirst`, `fromRootFirst_mul`, `rootFirstSpecializationHom`, `rootFirstSpecializationHom_rootFirst`, and `rootFirstSpecializationHom_fromRootFirst` are not ported; the root-first presentation remains outside the P6 slice 6 API boundary. The nonvanishing, divisibility, and degree declarations are covered by the corresponding existing generic `MvPolynomial` APIs listed in the report. The former direct theorem-application example for retained-curve degree bounds was replaced by this computed split example.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/FirstOrder/HybridDescent.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance examples check a supported `Y₁` polynomial at its proper depth-one prefix, a `Y₀` polynomial at prefix depth zero through the degree-zero constructor, and the finite-stage split at endpoint one for the identity sequence. The test uses the shared generic hybrid-variable degree fact directly.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/DerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example checks the generic initial-separant cap on the recursive equation fixture.

## `ArkLibTest/Data/Probability/Uniform.lean`

Ported from `ArkLib/Data/Probability/Notation.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The source uniform-sample event calculation corresponds to
`SampleableType.prEvent_uniformSample`; `Pr_uniform_equiv` corresponds to
`SampleableType.prEvent_uniformSample_equiv`. The acceptance cases check the finite native-measure
event sum and the uniform-sampling statements. No public ArkLib declaration is added.

`Pr_eq_tsum_indicator` is retired with the PMF-valued `Pr_{…}[…]` notation. Its scalar
compatibility calculation is covered by VCVio's `probOutput_true_eq_probEvent` followed by
`probEvent_eq_tsum_indicator` or its finite variants, so ArkLib adds no wrapper. The three-sample
PMF computation is not added, and `$ᵖ` plus `Pr_{…}[…]` remain retired syntax.

## `ArkLibTest/ToMathlib/Analysis/SpecificLimits.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/GeometricCounting.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance examples check the ratio bound at `n = K = A = 2`, `k = 1`, `ν = 2`, and `δ = 1/2`, and the count bound for `L = 20`, `m = d = 1`.

## `ArkLibTest/ToMathlib/MvPolynomial.lean`

Ported from `ArkLibTest/ToMathlib/MvPolynomial.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check both evaluation directions using nonconstant polynomials and distinct values for the distinguished and remaining variables.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance case checks that flattening preserves a separate cap on a polynomial variable.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/PositiveProduct.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

No public declarations were added. The acceptance case checks the composed challenge-degree budget for `t * Y₀ + Y₁` at height one, using `CoeffNatDegreeLE`, option-equivalence flattening, and a local `renameEquiv` swap.

`flattenedRootFirstEquiv` and `flattenedRootFirst` have no named replacements; the test uses option-equivalence flattening followed by the local variable swap. `flattenedRootFirst_ne_zero_iff` follows from injectivity of those equivalences, and `flattenedRootFirst_rootDegree_le` is derived locally from `weightedTotalDegree_optionEquivRight` and degree transport under renaming.

`flattenedContent` and `flattenedPositiveRootProduct` use `MvPolynomial.radicalContent none` and `MvPolynomial.radicalPrimPart none`. Their nonzero and root-degree facts are covered by `MvPolynomial.degreeOf_radicalContent`, `MvPolynomial.radicalContent_ne_zero`, and `MvPolynomial.radicalPrimPart_ne_zero`. `flattened_split_zero_iff` is covered by `MvPolynomial.map_radicalContent_mul_radicalPrimPart_eq_zero_iff`, generalized to arbitrary supported homomorphisms and variable coordinates.

`flattened_factorRootDegrees_le` is covered by `MvPolynomial.sum_degreeOf_positiveDegreeFactorClasses_le`, with its source-coordinate cap derived locally. `flattened_content_add_factorChallengeDegrees_le` is covered by `MvPolynomial.add_sum_degreeOf_positiveDegreeFactorClasses_le`; its challenge-height premise uses `CoeffNatDegreeLE`, and its coordinate bound follows from `weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le`.

`flattenedPositiveRootProduct_map_fraction_separable` is covered by `MvPolynomial.ordinaryRootPolynomial_map_fractionRing_separable` and the more general `MvPolynomial.radicalPrimPart_map_optionEquivLeft_fractionRing_separable`. `flattenedPositiveRootProduct_resultant_ne_zero` is covered by `Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial`. These first-order names are omitted because the existing generic APIs cover their mathematics, not because of proof gaps.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/Degree.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check a concrete degree-one power-moment map and its prime kernel over `ℚ`, coefficient-lift evaluation, polynomial-lift flattening, and both lifted-degree bounds. A cleared-substitution example with `h = 0` and `a = 1` attains coefficient degree one.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/ChunkedPowerLift.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

Acceptance cases check a coefficient lift through degree two and its total-degree bound, plus a multivariate lift with a degree-two coefficient and a jet variable. The multivariate case checks that the power-moment map recovers the flattening and that the lift has total degree at most three.

## `ArkLibTest/ToMathlib/RingTheory/MvPolynomial.lean`

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Symbolic/TaylorDerivativeSupport.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance case checks capped-bidegree membership from a bidegree rectangle and a separate variable-degree bound.

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Flattening.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The existing acceptance example exercises `weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le`. The unit-specific acceptance file was removed; no replacement first-order acceptance file is added.

Ported from `ArkLibTest/ToMathlib/RingTheory/MvPolynomial.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

The acceptance case checks the generic count theorem on a dimension-two coordinate ideal containing one evaluation equation.

## `ArkLibTest/ToMathlib/RingTheory/Nullstellensatz.lean`

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/Incidence/TwoJet.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

An acceptance example checks the point `(1, 0)` on `X 1 = 0` with concrete cuts and computed hypotheses for `MvPolynomial.cappedDegreeHypersurface_incidence_sharp`.
