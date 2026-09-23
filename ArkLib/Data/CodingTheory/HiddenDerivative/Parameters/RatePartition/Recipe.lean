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
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  have hlimit := show
      1 < (27 / 20 : ℝ) * rate * (order + 1) *
        Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) from by
    rw [← rateGamma_eq_exponential horder]
    exact hgate
  exact exists_partitionFiniteRatio_gt hrate hagreement horder hlimit

/-- The first multiplicity with positive weight budget and finite ratio above one. -/
def rateMultiplicity {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) : ℕ := by
  classical
  exact Nat.find
    (exists_partitionFiniteParameters_of_rateGamma_gt_one hrate hagreement horder hgate)

/-- The selected multiplicity has positive weight budget and finite ratio above one. -/
theorem rateMultiplicity_spec {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) :
    let multiplicity := rateMultiplicity hrate hagreement horder hgate
    0 < multiplicity ∧ 0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  classical
  simpa only [rateMultiplicity] using
    Nat.find_spec
      (exists_partitionFiniteParameters_of_rateGamma_gt_one hrate hagreement horder hgate)

/-- No smaller multiplicity has positive weight budget and finite ratio above one. -/
theorem rateMultiplicity_minimal {rate agreement : ℝ} {order candidate : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order)
    (hcandidate : 0 < candidate ∧
      0 < partitionWeightBudget rate agreement order candidate ∧
      1 < partitionFiniteRatio rate agreement order candidate) :
    rateMultiplicity hrate hagreement horder hgate ≤ candidate := by
  classical
  simpa only [rateMultiplicity] using Nat.find_min'
    (exists_partitionFiniteParameters_of_rateGamma_gt_one hrate hagreement horder hgate)
    hcandidate

end ReedSolomon.HiddenDerivative.RatePartition
