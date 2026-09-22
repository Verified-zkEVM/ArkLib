/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Counting

/-!
# Certified-rank count acceptance tests

Concrete values of the counts, including the exact interpolation dimension count, and the case
`d = 0` where the threshold does not reach the multiplicity.
-/

open ReedSolomon.HiddenDerivative

/-- The exponents `(c₂, c₃)` with `c₂ + 2 c₃ ≤ 2` are `(0,0), (1,0), (2,0), (0,1)`. -/
example : weightedHigherJetCount 3 2 = 4 := by decide

/-- With at most one visible jet there are no higher jets, and the count is `1`. -/
example (W : ℕ) : weightedHigherJetCount 1 W = 1 := by
  simp [weightedHigherJetCount, Finset.natWeightedSimplex]

/-- `⌈5 / 2⌉ = 3`. -/
example : contactThreshold 2 5 0 = 3 := by decide

/-- For `d = 0` the threshold is `0` and `m ≤ r + d h` fails, so
`multiplicity_le_add_mul_contactThreshold` needs `0 < d`. -/
example : contactThreshold 0 2 0 = 0 ∧ ¬ 2 ≤ 0 + 0 * contactThreshold 0 2 0 := by decide

/-- For `d = 1, m = 2, M = 1, W = 0`: the residuals are `2 - 0` at `r = 0` (threshold `2`) and
`4 - 1` at `r = 1` (threshold `1`). -/
example : certifiedEnlargedRankBound 1 2 1 0 = 5 := by decide

/-- The identity with the ambient and exhibited sums, at the same parameters. -/
example : (∑ r ∈ Finset.range 2, weightedHigherJetCount 1 (0 + r) * ambientContactCount r 1) -
      ∑ r ∈ Finset.range 2, weightedHigherJetCount 1 (0 + r) *
        exhibitedKernelContactCount r 1 (contactThreshold 1 2 r) = 5 := by
  rw [ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound]
  decide

/-- With `D = 2`, `A = 2`, `d = 1`, `m = 1`, `M = 1`, `W = 0`: the residuals are `2` at `b₁ = 0`
and `1` at `b₁ = 1`, with staircase counts `2` and `1`. -/
example : exactInterpolationDimensionCount 2 2 1 1 1 0 = 3 := by decide

/-- With `D = 3`, `A = 3`, `d = 2`, `m = 1`, `M = 1`, `W = 1`: the higher-jet exponent `c ∈ {0, 1}`
of `Y₂` costs `c`, and `Y₁` costs `2 b₁`, so the residuals `3, 1, 2, 0` contribute `3 + 1 + 2 + 0`.
-/
example : exactInterpolationDimensionCount 3 3 2 1 1 1 = 6 := by decide

/-- The count is the number of its coordinate tuples. -/
example : (exactDimensionCoordinates 3 3 2 1 1 1).card = 6 := by
  rw [card_exactDimensionCoordinates]
  decide

/-- The residual is truncated: once `(D - 1) b₁` exceeds `m A`, nothing is left for `X` and `Y₀`. -/
example : exactDimensionResidual (d := 1) 3 1 2 2 (fun _ => 0) = 0 := by decide
