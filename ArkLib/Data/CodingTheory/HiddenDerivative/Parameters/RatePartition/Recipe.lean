/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Gate

/-!
# The least multiplicity passing the finite partition gate

When the limiting rate ratio is strictly above one, some positive multiplicity has a positive
weight budget and finite ratio above one. This module chooses the least such multiplicity and
records its acceptance conditions.

## Main statements

* `rateMultiplicity`: the least multiplicity with positive budget and finite ratio above one.
* `rateMultiplicity_spec`, `rateMultiplicity_minimal`: acceptance and minimality properties.
* `exists_partitionFiniteParameters_of_rateGamma_gt_one`: a strict limiting gate gives a finite
  multiplicity passing the finite gate.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- A strict limiting gate gives a positive multiplicity with positive weight budget and finite
ratio above one. -/
theorem exists_partitionFiniteParameters_of_rateGamma_gt_one {rate agreement : ℝ} {order : ℕ}
    (hagreement : 0 < agreement)
    (hgate : 1 < rateGamma rate agreement order) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  have horder : 0 < order := by
    by_contra hnot
    have hzero : order = 0 := by omega
    by_cases hrate : rate = 0
    · norm_num [rateGamma, hzero, hrate] at hgate
    · have hexponent : rate / agreement ≠ 0 := div_ne_zero hrate hagreement.ne'
      norm_num [rateGamma, hzero, Real.zero_rpow hexponent] at hgate
  obtain ⟨p⟩ := PartitionFiniteParameters.nonempty hagreement horder
    (by rwa [← rateGamma_eq_exponential horder])
  exact ⟨p.multiplicity, p.multiplicity_pos, p.weightBudget_pos, p.one_lt_finiteRatio⟩

/-- The first multiplicity with positive weight budget and finite ratio above one. -/
def rateMultiplicity {rate agreement : ℝ} {order : ℕ}
    (hagreement : 0 < agreement)
    (hgate : 1 < rateGamma rate agreement order) : ℕ := by
  classical
  exact Nat.find
    (exists_partitionFiniteParameters_of_rateGamma_gt_one hagreement hgate)

/-- The selected multiplicity has positive weight budget and finite ratio above one. -/
theorem rateMultiplicity_spec {rate agreement : ℝ} {order : ℕ}
    (hagreement : 0 < agreement)
    (hgate : 1 < rateGamma rate agreement order) :
    let multiplicity := rateMultiplicity hagreement hgate
    0 < multiplicity ∧ 0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  classical
  simpa only [rateMultiplicity] using
    Nat.find_spec
      (exists_partitionFiniteParameters_of_rateGamma_gt_one hagreement hgate)

/-- No smaller multiplicity has positive weight budget and finite ratio above one. -/
theorem rateMultiplicity_minimal {rate agreement : ℝ} {order candidate : ℕ}
    (hagreement : 0 < agreement)
    (hgate : 1 < rateGamma rate agreement order)
    (hcandidate : 0 < candidate ∧
      0 < partitionWeightBudget rate agreement order candidate ∧
      1 < partitionFiniteRatio rate agreement order candidate) :
    rateMultiplicity hagreement hgate ≤ candidate := by
  classical
  simpa only [rateMultiplicity] using Nat.find_min'
    (exists_partitionFiniteParameters_of_rateGamma_gt_one hagreement hgate)
    hcandidate

end ReedSolomon.HiddenDerivative.RatePartition
