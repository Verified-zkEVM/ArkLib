/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.SupportGuards

/-!
# Rate-partition support guard acceptance tests

A concrete eligible exponent satisfies the rate-dependent jet cap, while an exponent above that
cap fails the partition-support cutoff.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- For `R = 1/2`, `D = 2`, `m = 1`, and `n = A = 4`, the eligible exponent `Y₀` has jet degree
one, below the cap four. -/
example :
    totalJetDegree (Finsupp.single (some 0 : JetVariable 1) 1) ≤ rateJetCap (1 / 2) 1 := by
  apply partitionSupport_totalJetDegree_le_rateJetCap (D := 2) (W := 1) (m := 1) (n := 4)
    (A := 4) (rate := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp [PartitionSupportEligible, fullDerivativeJetWeight, totalJetDegree,
    jetDerivativeWeight, Finsupp.weight_single]
  norm_num

/-- With cutoff `2`, an exponent of total jet degree `3` is not partition-support eligible. -/
example :
    ¬ PartitionSupportEligible 1 1 3 2
      (Finsupp.single (some 0 : JetVariable 1) 3) := by
  simp [PartitionSupportEligible, fullDerivativeJetWeight, totalJetDegree,
    jetDerivativeWeight, Finsupp.weight_single]
  norm_num

end ReedSolomon.HiddenDerivative.RatePartition
