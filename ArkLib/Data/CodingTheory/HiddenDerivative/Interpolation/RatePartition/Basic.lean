/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting

/-!
# The rate-partition support at a real cutoff

The rate-dependent construction of the hidden-derivative decoder interpolates in the space of
differential polynomials whose exponents have derivative-order weight `∑_j j b_j ≤ W` and coarse
weight `x + D ∑_j b_j < L`. This is exactly the partition support space
`partitionSupportSpace F D d W L hD` of `PartitionSupport/Basic.lean`, so no new space is defined
here. This file adds the facts about that space which the rate-dependent construction uses and
which do not follow from the natural-cutoff statements alone.

The cutoff `L` of the construction is real. A natural number `n` satisfies `n < L` exactly when
`n < ⌈L⌉₊`, so the space at the real cutoff `L` is the space at the natural cutoff `⌈L⌉₊`, and the
exact dimension count `partitionSourceCount` of `PartitionSupport/Counting.lean` applies at
`⌈L⌉₊`. The constant monomial is eligible exactly when `0 < L`, and every exponent has
nonnegative coarse weight, so the space is nonzero exactly when `0 < L`, for every `W`, including
`W = 0`. Finally, the coarse cutoff bounds the total jet degree by `L / D`.

## Main statements

* `partitionSupportEligible_natCeil_iff`, `partitionSupportExponents_natCeil` and
  `partitionSupportSpace_natCeil`: the real cutoff `L` and the natural cutoff `⌈L⌉₊` give the
  same support.
* `finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil`: the exact dimension at a real
  cutoff.
* `card_partitionSupportExponents_pos_iff` and `finrank_partitionSupportSpace_pos_iff`: the space
  is nonzero exactly when `0 < L`.
* `totalJetDegree_lt_of_partitionSupportEligible`: eligible exponents have total jet degree below
  `L / D`.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`RatePartition/Basic.lean` and `RatePartition/Dimension.lean` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d.

The source's `RatePartitionEligible` has the same definition as its `PartitionSupportEligible`,
which is already ported. Accordingly the source's rate-partition names are covered by existing
declarations:

* `RatePartitionEligible`, `RatePartitionEligible.weightedSupport`, `ratePartitionExponents`,
  `mem_ratePartitionExponents`, `ratePartitionSpace`, `mem_ratePartitionSpace_iff` and
  `finrank_ratePartitionSpace_eq_card` are `PartitionSupportEligible`,
  `PartitionSupportEligible.toWeightedSupportEligible`, `partitionSupportExponents`,
  `mem_partitionSupportExponents`, `partitionSupportSpace`, `mem_partitionSupportSpace_iff` and
  `finrank_partitionSupportSpace_eq_card` of `PartitionSupport/Basic.lean`. The source defined
  `ratePartitionExponents` by filtering `weightedSupportExponents`; the two finite sets have the
  same members.
* `ratePartition_localConstraint_support` is `partitionSupport_localConstraint_support` of
  `PartitionSupport/LocalRank.lean`.
* From `RatePartition/Dimension.lean`: `ratePartitionSourceExponent`,
  `ratePartitionSourceExponent_none`, `ratePartitionSourceExponent_coordinates`,
  `totalJetDegree_ratePartitionSourceExponent` and
  `fullDerivativeJetWeight_ratePartitionSourceExponent` are `partitionSourceExponent`,
  `partitionSourceExponent_none`, `partitionSourceExponent_eta`,
  `totalJetDegree_eq_zero_add_sum_succ` and `fullDerivativeJetWeight_eq_sum_succ` of
  `PartitionSupport/Counting.lean`. The dependent index `RatePartitionDimensionIndex`,
  `card_ratePartitionDimensionIndex`, `ratePartitionDimensionExponent` and its lemmas
  `_injective`, `_eligible` and `exists_ratePartitionDimensionExponent` are replaced by the
  bijection in the proof of `card_partitionSupportExponents`. The source's
  `ratePartitionDimensionCount` sums the `Y₀` exponent over `range (L + 1)`, while
  `partitionSourceCount` sums over `range L`; for `0 < D` the extra term `L - D (L + ∑_i c_i)` is
  zero, and the acceptance tests derive `card_ratePartitionExponents_eq_dimensionCount` in the
  source's form from `card_partitionSupportExponents`.
* `card_ratePartitionExponents_pos` becomes the equivalence
  `card_partitionSupportExponents_pos_iff`, with the finrank form
  `finrank_partitionSupportSpace_pos_iff`.
* `totalJetDegree_lt_of_ratePartitionEligible` becomes
  `totalJetDegree_lt_of_partitionSupportEligible`, derived from
  `totalJetDegree_lt_of_weightedSupportEligible`.
* `partitionSupportEligible_natCeil_iff`, `partitionSupportExponents_natCeil`,
  `partitionSupportSpace_natCeil` and
  `finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil` are new; they extend the
  natural-cutoff dimension count to the real cutoffs of the source.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Finset

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} {d D W : ℕ} {L : ℝ}

/-! ### Real and natural cutoffs -/

/-- Eligibility at the natural cutoff `⌈L⌉₊` is eligibility at the real cutoff `L`, since the coarse
weight is a natural number and `n < ⌈L⌉₊ ↔ n < L` for natural `n`. For `L ≤ 0` both sides are
false. -/
theorem partitionSupportEligible_natCeil_iff {u : JetVariable d →₀ ℕ} :
    PartitionSupportEligible D d W (⌈L⌉₊ : ℝ) u ↔ PartitionSupportEligible D d W L u := by
  simp only [PartitionSupportEligible, Nat.cast_lt, Nat.lt_ceil]

/-- The eligible exponents at the natural cutoff `⌈L⌉₊` are those at the real cutoff `L`. -/
theorem partitionSupportExponents_natCeil (hD : 0 < D) :
    partitionSupportExponents D d W (⌈L⌉₊ : ℝ) hD = partitionSupportExponents D d W L hD := by
  ext u
  simp only [mem_partitionSupportExponents, partitionSupportEligible_natCeil_iff]

/-- The partition support space at the natural cutoff `⌈L⌉₊` is the space at the real cutoff
`L`. -/
theorem partitionSupportSpace_natCeil [CommSemiring F] (hD : 0 < D) :
    partitionSupportSpace F D d W (⌈L⌉₊ : ℝ) hD = partitionSupportSpace F D d W L hD := by
  rw [partitionSupportSpace, partitionSupportSpace, partitionSupportExponents_natCeil]

/-- For `0 < D`, the dimension of the partition support space at the real cutoff `L` over a field
is `partitionSourceCount D d W ⌈L⌉₊`. For `L ≤ 0` both sides are zero. -/
theorem finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil (F : Type*) [Field F]
    (hD : 0 < D) (L : ℝ) :
    Module.finrank F (partitionSupportSpace F D d W L hD) = partitionSourceCount D d W ⌈L⌉₊ := by
  rw [← partitionSupportSpace_natCeil, finrank_partitionSupportSpace_eq_partitionSourceCount]

/-! ### Nonemptiness -/

/-- The constant monomial is partition-support eligible exactly when `0 < L`: its derivative-order
weight `0` is at most every `W`, and its coarse weight is `0`. -/
theorem partitionSupportEligible_zero_iff :
    PartitionSupportEligible D d W L (0 : JetVariable d →₀ ℕ) ↔ 0 < L := by
  simp [PartitionSupportEligible, fullDerivativeJetWeight, totalJetDegree]

/-- For `0 < D`, some exponent is partition-support eligible exactly when `0 < L`, for every
derivative budget `W`. If `0 < L` the constant monomial is eligible; conversely every coarse
weight is a nonnegative number below `L`. -/
theorem card_partitionSupportExponents_pos_iff (hD : 0 < D) :
    0 < #(partitionSupportExponents D d W L hD) ↔ 0 < L := by
  rw [card_pos]
  constructor
  · rintro ⟨u, hu⟩
    exact (Nat.cast_nonneg _).trans_lt (mem_partitionSupportExponents.mp hu).2
  · intro hL
    exact ⟨0, mem_partitionSupportExponents.mpr (partitionSupportEligible_zero_iff.mpr hL)⟩

/-- For `0 < D`, the partition support space over a field is nonzero exactly when `0 < L`. -/
theorem finrank_partitionSupportSpace_pos_iff [Field F] (hD : 0 < D) :
    0 < Module.finrank F (partitionSupportSpace F D d W L hD) ↔ 0 < L := by
  rw [finrank_partitionSupportSpace_eq_card, card_partitionSupportExponents_pos_iff]

/-! ### Degree bound -/

/-- A partition-support eligible exponent has total jet degree strictly below `L / D`, since
`D * totalJetDegree u` is at most the coarse weight. The hypothesis `0 < D` makes the division
meaningful. This is `totalJetDegree_lt_of_weightedSupportEligible` through the inclusion of the
partition support into the weighted support. -/
theorem totalJetDegree_lt_of_partitionSupportEligible (hD : 0 < D) {u : JetVariable d →₀ ℕ}
    (hu : PartitionSupportEligible D d W L u) : (totalJetDegree u : ℝ) < L / D :=
  totalJetDegree_lt_of_weightedSupportEligible hD hu.toWeightedSupportEligible

end ReedSolomon.HiddenDerivative
