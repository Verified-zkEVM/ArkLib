/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.BlockLength

/-!
# The strict-margin finite parameter recipe

Search multiplicities in increasing order until the positive derivative budget
and exact finite Gamma gate pass. Convergence proves termination for every strict
limiting gate, without assuming the stronger margin of the uniform construction.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The first multiplicity passing the exact finite gate. -/
def rateMultiplicity {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) : ℕ := by
  classical
  exact Nat.find (exists_finiteGamma_gt_one hrate hagreement horder hgate)

/-- All finite search acceptance checks hold at the chosen multiplicity. -/
theorem rateMultiplicity_spec {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) :
    let multiplicity := rateMultiplicity hrate hagreement horder hgate
    0 < multiplicity ∧ 0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < finiteGamma rate agreement order multiplicity := by
  classical
  exact Nat.find_spec (exists_finiteGamma_gt_one hrate hagreement horder hgate)

/-- No smaller multiplicity passes all of the finite checks. -/
theorem rateMultiplicity_minimal {rate agreement : ℝ} {order candidate : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order)
    (hcandidate : 0 < candidate ∧ 0 < partitionWeightBudget rate agreement order candidate ∧
      1 < finiteGamma rate agreement order candidate) :
    rateMultiplicity hrate hagreement horder hgate ≤ candidate := by
  classical
  exact Nat.find_min' (exists_finiteGamma_gt_one hrate hagreement horder hgate) hcandidate

end ReedSolomon.HiddenDerivative.RatePartition
