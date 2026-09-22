/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.Enumerative.IncidenceProduct

/-!
# Acceptance tests for products of incidence ratios

The examples evaluate both products for `n = 10`, `A = 5`, `k = 3` in dimension two, where each
equals `6`, and separate the degree factor `b ^ d`. They derive the comparison of
`(n - m) / (A - m)` with the factor at a threshold `T > m`, and its form at dimension `d` with
threshold `k - d + 1`.

The boundary examples show the hypotheses are needed: `A ≤ n` and `m' < A` in the ratio
comparison, and `0 < b` in `one_le_incidenceFactor` and in monotonicity in the dimension.
-/

namespace IncidenceProductTest

/-- With `n = 10`, `A = 5`, `k = 3`, `b = 1`, the factors in dimensions one and two are `8 / 3`
and `9 / 4`, with product `6`. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 1 2 = 6 := by
  norm_num [dimensionSensitiveIncidenceProduct]

/-- With `n = 10`, `A = 5`, `L = 2`, `k = 3`, `b = 1`, the factors in dimensions one and two
are `9 / 4` (threshold `2`) and `8 / 3` (threshold `3`), with product `6`. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 2 = 6 := by
  norm_num [hybridDimensionSensitiveIncidenceProduct_two]

/-- With degree bound `b = 2`, the product in dimension two gains the factor `2 ^ 2`. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 2 2 = 24 := by
  rw [dimensionSensitiveIncidenceProduct_eq_pow_mul]
  norm_num [dimensionSensitiveIncidenceProduct]

/-- If fewer than `T` equations vanish, with `T ≤ A ≤ n`, the ratio `(n - m) / (A - m)` is at
most the factor `(n - T + 1) / (A - T + 1)`. -/
example {n A T m : ℕ} (hm : m < T) (hTA : T ≤ A) (hAn : A ≤ n) :
    ((n - m : ℕ) : ℚ) / ((A - m : ℕ) : ℚ) ≤
      ((n - T + 1 : ℕ) : ℚ) / ((A - T + 1 : ℕ) : ℚ) := by
  have h := natCast_sub_div_natCast_sub_le (K := ℚ) (m := m) (m' := T - 1) (by omega) (by omega) hAn
  rwa [show n - (T - 1) = n - T + 1 by omega, show A - (T - 1) = A - T + 1 by omega] at h

/-- At dimension `0 < d ≤ k` with `k ≤ A ≤ n`, at most `k - d` vanishing equations give the
ratio bound by the factor `(n - k + d) / (A - k + d)`. -/
example {n A k d m : ℕ} (hd : 0 < d) (hdk : d ≤ k) (hm : m ≤ k - d) (hkA : k ≤ A)
    (hAn : A ≤ n) :
    ((n - m : ℕ) : ℚ) / ((A - m : ℕ) : ℚ) ≤ ((n - k + d : ℕ) : ℚ) / ((A - k + d : ℕ) : ℚ) := by
  have h := natCast_sub_div_natCast_sub_le (K := ℚ) (m' := k - d) hm (by omega) hAn
  rwa [show n - (k - d) = n - k + d by omega, show A - (k - d) = A - k + d by omega] at h

/-- The dimension-sensitive product in dimension at most one is bounded by its first factor. -/
example :
    dimensionSensitiveIncidenceProduct 10 5 3 1 0 ≤ ((10 - 3 + 1 : ℕ) : ℚ) / (5 - 3 + 1 : ℕ) :=
  dimensionSensitiveIncidenceProduct_le_one (by norm_num) (by norm_num) (by norm_num)

/-- The hybrid product in dimension one is at most the product of the first two factors. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 1 ≤
    ((((10 - 2 + 1) * 1 : ℕ) : ℚ) / ((5 - 2 + 1 : ℕ) : ℚ)) *
      ((((10 - 3 + 1) * 1 : ℕ) : ℚ) / ((5 - 3 + 1 : ℕ) : ℚ)) :=
  hybridDimensionSensitiveIncidenceProduct_le_two (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) one_pos

/-! ### The hypotheses are needed -/

/-- `A ≤ n` is needed in the ratio comparison: `(1 - 0) / (2 - 0) = 1 / 2` exceeds
`(1 - 1) / (2 - 1) = 0`. -/
example : ¬ ((1 - 0 : ℕ) : ℚ) / ((2 - 0 : ℕ) : ℚ) ≤ ((1 - 1 : ℕ) : ℚ) / ((2 - 1 : ℕ) : ℚ) := by
  norm_num

/-- `m' < A` is needed in the ratio comparison: for `m' = A = 2` the right side divides by zero. -/
example : ¬ ((3 - 0 : ℕ) : ℚ) / ((2 - 0 : ℕ) : ℚ) ≤ ((3 - 2 : ℕ) : ℚ) / ((2 - 2 : ℕ) : ℚ) := by
  norm_num

/-- `0 < b` is needed in `one_le_incidenceFactor`: with `b = 0` the factor is zero. -/
example : ¬ (1 : ℚ) ≤ ((((3 - 1 + 1) * 0 : ℕ) : ℚ) / ((2 - 1 + 1 : ℕ) : ℚ)) := by
  norm_num

/-- `0 < b` is needed for monotonicity in the dimension: with `b = 0` the product drops from `1`
in dimension zero to `0` in dimension one. -/
example : ¬ Monotone (hybridDimensionSensitiveIncidenceProduct 3 2 1 1 0) := fun h ↦ by
  have := h (zero_le_one : (0 : ℕ) ≤ 1)
  norm_num at this

end IncidenceProductTest
