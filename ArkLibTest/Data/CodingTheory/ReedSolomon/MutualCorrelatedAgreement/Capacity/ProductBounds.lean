/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductBounds

/-!
# Acceptance tests for correlated-agreement product bounds

For `δ = 1 / 2`, `n = 10`, `k = 2`, and `A = 7`, the cutoff at `d = 2` is `5`. The tests check
the factor and product bounds at the original threshold and the joint and fiber bounds at the
cutoff. Boundary examples show that the cutoff range needs `k ≤ A`, the joint bound needs `k > 0`,
the original factor bound needs its gap condition, and the fiber factor bound needs `d > 0`.
-/

namespace ReedSolomon.ProductBoundsTest

/-- The cutoff with `d = 2`, `k = 2`, and `A = 7` is `5`. -/
example : correlatedProductCutoff 2 2 7 = 5 := by
  rw [correlatedProductCutoff]
  have hf : Nat.floor
      (((2 : ℕ) : ℝ) * ((7 - 2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1)) = 3 := by
    rw [(Nat.floor_eq_iff (by norm_num) :
      ⌊((2 : ℕ) : ℝ) * ((7 - 2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1)⌋₊ = 3 ↔ _)]
    constructor <;> norm_num
  rw [hf]

/-- With `k = 2 ≤ A = 7`, the cutoff lies between `2` and `7`. -/
example : 2 ≤ correlatedProductCutoff 2 2 7 ∧ correlatedProductCutoff 2 2 7 ≤ 7 :=
  correlatedProductCutoff_bounds 2 2 7 (by norm_num)

/-- At the original threshold the factor is `9 / 6 ≤ 2` for `δ = 1 / 2`. -/
example : ((10 - 2 + 0 + 1 : ℕ) : ℝ) / (7 - 2 + 0 + 1 : ℕ) ≤ 1 / (1 / 2 : ℝ) :=
  evaluation_incidence_factor_le (1 / 2) 10 2 7 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The Reed–Solomon factor form follows from the shifted-ratio bound. -/
example (δ : ℝ) (n k A j : ℕ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hkA : k ≤ A)
    (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) :
    ((n - k + j + 1 : ℕ) : ℝ) / (A - k + j + 1 : ℕ) ≤ 1 / δ := by
  have hkn : k ≤ n := hkA.trans hAn
  have hgap' : δ * ((n - k : ℕ) : ℝ) ≤ ((A - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkn, Nat.cast_sub hkA]
    nlinarith [mul_nonneg hδ.le (show (0 : ℝ) ≤ (k : ℝ) by positivity)]
  exact natCast_shiftedRatio_le_one_div δ hδ hδone (n - k) (A - k) j hgap'

/-- Through dimension two the original-threshold incidence product is at most `4`. -/
example :
    (dimensionSensitiveIncidenceProduct 10 7 2 1 2 : ℝ) ≤ (1 / (1 / 2 : ℝ)) ^ 2 :=
  evaluation_incidence_product_le (1 / 2) 10 2 7 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The cutoff joint factor is `2 ≤ 6` for `d = 2` and `δ = 1 / 2`. -/
example :
    let L := correlatedProductCutoff 2 2 7
    ((10 - L + 1 : ℕ) : ℝ) / (7 - L + 1 : ℕ) ≤
      ((2 : ℝ) + 1) / (1 / 2 : ℝ) := by
  simpa using correlatedProductCutoff_jointRatio_le (1 / 2) 10 2 7 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The intermediate factor is at most `3` for `d = 2`, `j = 0`, and `δ = 1 / 2`. -/
example :
    let L := correlatedProductCutoff 2 2 7
    ((10 - 2 + 0 + 1 : ℕ) : ℝ) / (L - 2 + 0 + 1 : ℕ) ≤
      (1 + 1 / (2 : ℝ)) / (1 / 2 : ℝ) := by
  simpa using correlatedProductCutoff_fiberFactor_le (1 / 2) 10 2 7 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Through dimension two the intermediate-cutoff product is at most `9`. -/
example :
    (dimensionSensitiveIncidenceProduct 10 (correlatedProductCutoff 2 2 7) 2 1 2 : ℝ) ≤
      ((1 + 1 / (2 : ℝ)) / (1 / 2 : ℝ)) ^ 2 :=
  correlatedProductCutoff_fiberProduct_le (1 / 2) 10 2 7 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Since `r = d = 2`, the intermediate-cutoff product is less than `12`. -/
example :
    (dimensionSensitiveIncidenceProduct 10 (correlatedProductCutoff 2 2 7) 2 1 2 : ℝ) <
      3 * (1 / (1 / 2 : ℝ)) ^ 2 :=
  correlatedProductCutoff_fiberProduct_lt_three (1 / 2) 10 2 7 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ### The hypotheses are needed -/

/-- `k ≤ A` is needed for the cutoff upper bound: with `k = 2 > A = 1`, the cutoff is `2`. -/
example : ¬ correlatedProductCutoff 1 2 1 ≤ 1 := by
  norm_num [correlatedProductCutoff]

/-- `k > 0` is needed for the joint bound: when `n = k = A = 0`, the ratio is `1 > 1 / 2`. -/
example :
    ¬ ((0 - correlatedProductCutoff 0 0 0 + 1 : ℕ) : ℝ) /
        (0 - correlatedProductCutoff 0 0 0 + 1 : ℕ) ≤ (0 + 1) / (2 : ℝ) := by
  norm_num [correlatedProductCutoff]

/-- The gap condition is needed: at `δ = 1`, `n = 10`, `k = 1`, and `A = 5`, the factor is `2`. -/
example :
    ¬ ((10 - 1 + 0 + 1 : ℕ) : ℝ) / (5 - 1 + 0 + 1 : ℕ) ≤ (1 : ℝ) := by
  norm_num

/-- `d > 0` is needed for the fiber factor: when `d = 0`, the left side is `9` and the bound is
`2`. -/
example :
    ¬ ((10 - 2 + 0 + 1 : ℕ) : ℝ) /
        (correlatedProductCutoff 0 2 7 - 2 + 0 + 1 : ℕ) ≤
      (1 + 1 / (0 : ℝ)) / (1 / 2 : ℝ) := by
  norm_num [correlatedProductCutoff]

end ReedSolomon.ProductBoundsTest
