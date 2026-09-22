/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.LocalRank

/-!
# Partition support local rank acceptance tests

* The source's `partitionLocalRankBound` formula, with `(m - s) ⌈/⌉ (d + 1)`, is
  `localDerivativeCoordinateBudget` by definition.
* At `d = 1`, `m = 2`, `W = 0` the budget is `1 · 1 + 1 · 2 = 3`, so the local rank on every
  partition support space with these parameters is at most `3`, whatever `0 < D` and `L` are.
* At `d = 0` every polynomial has derivative-order weight `0`, so the general bound
  `finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight` applies to the whole
  space: the local constraint map of order `3` has rank at most `3 + 2 + 1 = 6`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Source shape: `partitionLocalRankBound d m W`. -/
example (d m W : ℕ) : localDerivativeCoordinateBudget d m W =
    ∑ s ∈ Finset.range m, ((m - s) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + s) :=
  rfl

example : localDerivativeCoordinateBudget 1 2 0 = 3 := by decide

/-- At `d = 1`, `m = 2`, `W = 0` the local rank on the partition support space is at most `3`,
for every `0 < D` and `L`. -/
example (D : ℕ) (hD : 0 < D) (L : ℝ) (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range (partitionSupportLocalConstraint (d := 1) (W := 0)
      (L := L) 2 hD center received)) ≤ 3 :=
  (finrank_partitionSupportLocalConstraint_le hD center received).trans (by decide)

example : localDerivativeCoordinateBudget 0 3 0 = 6 := by decide

/-- At `d = 0` the derivative-order weight vanishes, so the local constraint map of order `3` on
the whole space of differential polynomials has rank at most `6`. -/
example (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range
      ((localConstraintAt (d := 0) 3 center received).domRestrict ⊤)) ≤ 6 := by
  refine (finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight 3 0 center received
    ⊤ fun _ _ u _ => ?_).trans (by decide)
  simp [fullDerivativeJetWeight, Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
    jetDerivativeWeight]
