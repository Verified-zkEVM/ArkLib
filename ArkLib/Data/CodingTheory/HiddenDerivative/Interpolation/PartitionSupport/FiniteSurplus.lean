/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.MomentSource
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.LocalRank
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RankBudget

/-!
# The dimension of the partition support space exceeds a multiple of the local rank

The local constraint map of order `m` on the partition support space has rank at most
`localDerivativeCoordinateBudget d m W` (`finrank_partitionSupportLocalConstraint_le`), and for
`0 < d` and `0 < W` that budget is at most the envelope

```text
E(d, m, W) = (W ^ d / (d!) ^ 2) * exp ((d / W) * (m + (d + 1).choose 2))
               * (1 / ((d + 1) * (d / W) ^ 2) + 1 / (d / W))
```

(`localDerivativeCoordinateBudget_le_geometric`). The moment bound
`partitionSupport_dimension_gt_moment` gives
`μ / 2 * n * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2) < dim`. So for every `γ ≥ 0` with
`γ * E(d, m, W) ≤ μ / 2 * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2)`, the dimension of the partition
support space exceeds `γ * n` times the coordinate budget, and hence `γ * n` times the rank of the
local constraint map.

## Main statements

* `finrank_partitionSupportLocalConstraint_le_geometric`: the rank of the local constraint map is
  at most `E(d, m, W)`.
* `partitionSupport_surplus`: `γ * n * localDerivativeCoordinateBudget d m W < dim`.
* `partitionSupport_localConstraint_surplus`: the same with the rank of the local constraint map.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`PartitionSupport/FiniteSurplus.lean` and `PartitionSupport/RankBound.lean` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `RankBound.lean` mentions the partition support space nowhere. Its `partition_contact_exp_sum_le`,
  `partition_ceilDiv_le`, `localRank_linear_exp_sum_le`, `localRank_weightedHigherJetCount_le_exp`
  and `partitionLocalRankBound_le_geometric` are covered by `sum_contactThreshold_mul_exp_le_slots`,
  `Nat.cast_ceilDiv_le_div_add_one`, `Real.sum_range_linear_mul_exp_neg_pow_succ_le`,
  `weightedHigherJetCount_le_exp` and `localDerivativeCoordinateBudget_le_geometric` in
  `Interpolation/Local/RankBudget.lean` and its imports. `partition_count_le_volume` is the upper
  half of `Finset.natWeightedSimplex_succ_sandwich` divided by `(d!) ^ 2`; the acceptance tests
  derive it. The new `finrank_partitionSupportLocalConstraint_le_geometric` combines the
  geometric bound with the rank bound of `PartitionSupport/LocalRank.lean`.
* `partition_choose_two_real` is Mathlib's `Nat.cast_choose_two` at `d + 1`; the acceptance tests
  derive it.
* `partitionSupport_finiteGamma_surplus` is stated for the specific ratio `finiteGamma`, weight
  budget `partitionWeightBudget`, moment constant `27 / 10` and logarithm `log (6 d)` of the
  source's `Parameters/RatePartition/FiniteRatio.lean`, which is not yet ported.
  `partitionSupport_surplus` is the same argument for any `γ ≥ 0` satisfying the envelope
  inequality, any budget `W`, moment bound `μ` and logarithm; the source hypothesis `0 < m` is not
  needed, and `0 < n` and `0 < rate` follow from `0 < D ≤ rate * n`.

Deferred to the port of `Parameters/RatePartition/FiniteRatio.lean`: `finiteGamma_mul_rankEnvelope`,
which shows that `finiteGamma` satisfies the envelope inequality with equality for `μ = 27 / 10`,
and the source-shaped `partitionSupport_finiteGamma_surplus`, which is then
`partitionSupport_surplus` with the source's parameters.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Finset MeasureTheory

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

/-- For `0 < d` and `0 < W`, the local constraint map of order `m` on the partition support space
has rank at most
`(W ^ d / (d!) ^ 2) * exp ((d / W) * (m + (d + 1).choose 2)) *
(1 / ((d + 1) * (d / W) ^ 2) + 1 / (d / W))` over every field, for every cutoff `L`. -/
theorem finrank_partitionSupportLocalConstraint_le_geometric {F : Type*} [Field F] {m : ℕ}
    {L : ℝ} (hD : 0 < D) (hd : 0 < d) (hW : 0 < W) (center received : F) :
    (Module.finrank F (LinearMap.range
      (partitionSupportLocalConstraint (d := d) (W := W) (L := L) m hD center received)) : ℝ) ≤
      ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W)) :=
  (Nat.cast_le.mpr (finrank_partitionSupportLocalConstraint_le hD center received)).trans
    (localDerivativeCoordinateBudget_le_geometric d m W hd hW)

/-- The surplus of the partition support space over the local coordinate budget. Under the
hypotheses of `partitionSupport_dimension_gt_moment`, let `γ ≥ 0` satisfy
`γ * E ≤ μ / 2 * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2)`, where `E` is the geometric envelope of
`localDerivativeCoordinateBudget_le_geometric`. Then
`γ * n * localDerivativeCoordinateBudget d m W` is strictly less than the dimension of the
partition support space at the natural cutoff `L`. The hypothesis `0 ≤ γ` is used to multiply the
budget bound by `γ * n`; `m` is arbitrary. -/
theorem partitionSupport_surplus (F : Type*) [Field F] {n L m : ℕ}
    {rate level logarithm μ γ : ℝ} (hD : 0 < D) (hd : 0 < d) (hW : 0 < W)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L)
    (hscale : rate * W / d * logarithm ≤ level)
    (hmoment : μ < ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2)
    (hγ : 0 ≤ γ)
    (henvelope : γ * (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) ≤
      μ / 2 * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2)) :
    γ * n * localDerivativeCoordinateBudget d m W <
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  have hbudget := mul_le_mul_of_nonneg_left
    (localDerivativeCoordinateBudget_le_geometric d m W hd hW) (mul_nonneg hγ (Nat.cast_nonneg n))
  have hscaled := mul_le_mul_of_nonneg_left henvelope (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hdim := partitionSupport_dimension_gt_moment F hD hd hW hupper hlevel hscale hmoment
  calc γ * n * localDerivativeCoordinateBudget d m W
      ≤ γ * n * (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
          Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
            (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) := hbudget
    _ ≤ n * (μ / 2 * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2)) := by
      linarith
    _ = μ / 2 * n * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by ring
    _ < _ := hdim

/-- Under the hypotheses of `partitionSupport_surplus`, the dimension of the partition support
space at the natural cutoff `L` exceeds `γ * n` times the rank of the local constraint map of
order `m` at any `(center, received)`. -/
theorem partitionSupport_localConstraint_surplus (F : Type*) [Field F] {n L m : ℕ}
    {rate level logarithm μ γ : ℝ} (hD : 0 < D) (hd : 0 < d) (hW : 0 < W)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L)
    (hscale : rate * W / d * logarithm ≤ level)
    (hmoment : μ < ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2)
    (hγ : 0 ≤ γ)
    (henvelope : γ * (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) ≤
      μ / 2 * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2))
    (center received : F) :
    γ * n * Module.finrank F (LinearMap.range
      (partitionSupportLocalConstraint (d := d) (W := W) (L := (L : ℝ)) m hD center received)) <
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  refine lt_of_le_of_lt ?_
    (partitionSupport_surplus F hD hd hW hupper hlevel hscale hmoment hγ henvelope)
  exact mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (finrank_partitionSupportLocalConstraint_le hD center received))
    (mul_nonneg hγ (Nat.cast_nonneg n))

end ReedSolomon.HiddenDerivative
