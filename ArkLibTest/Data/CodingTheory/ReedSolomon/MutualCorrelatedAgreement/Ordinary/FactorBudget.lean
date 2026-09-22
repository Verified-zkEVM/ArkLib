/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget

/-!
# Acceptance tests for ordinary factor budgets

The examples evaluate the mixed chart degree and the unified coefficient at small parameters.
For `D = h = 1` and `s = b = 2` the mixed degree is `14`: the unified bound `14` is attained,
while the sharp bound `12` fails, so `b ≤ D` is needed in
`ordinaryFrobeniusMixedDegree_le_sharp`. Further examples show that `ordinaryPsi_eq_sharp`,
`ordinaryPsi_le_four_mul`, `ordinaryFrobenius_charge_le` and the summation theorems need their
hypotheses, aggregate the charges of a two-factor polynomial, and derive the source statements,
with their extra positivity hypotheses, from the general ones.
-/

open scoped BigOperators

namespace ReedSolomon.FactorBudgetTest

/-! ### Concrete values -/

example : ordinaryFrobeniusMixedDegree 1 1 2 2 = 14 := by decide

example : ordinaryPsi 2 3 = 16 := by decide

/-- Beyond root degree `2 * D + 1` the positive part is active: `ordinaryPsi 1 5 = 10 + 4`. -/
example : ordinaryPsi 1 5 = 14 ∧ 1 + (2 * 1 - 1) * (2 * 5 - 1) = 10 := by decide

/-- The unified bound is attained at `D = h = 1`, `s = b = 2`. -/
example : ordinaryFrobeniusMixedDegree 1 1 2 2 = 2 * 2 + 1 * ordinaryPsi 1 (2 * 2) := by decide

/-- The unified bound, computed by the theorem, at a larger instance. -/
example : ordinaryFrobeniusMixedDegree 3 5 4 7 ≤ 4 * 7 + 5 * ordinaryPsi 3 (4 * 7) :=
  ordinaryFrobeniusMixedDegree_le_unified 3 5 4 7

/-- A free-retention charge: `(2 * 3 - 1) * 2 + 1 * (1 * 3 + 2 * 16) + 1 * ((10 - 4) * 3)`. -/
example : ordinaryUnifiedPowerFactorRawAt 1 10 2 1 3 2 4 = 63 := by
  norm_num [ordinaryUnifiedPowerFactorRawAt, ordinaryPsi]

/-! ### Boundary cases -/

/-- `b ≤ D` is needed in `ordinaryFrobeniusMixedDegree_le_sharp`: here `b = 2 > D = 1`. -/
example :
    ¬ ordinaryFrobeniusMixedDegree 1 1 2 2 ≤ 1 + 2 * 2 + (2 * 1 - 1) * 1 * (2 * (2 * 2) - 1) := by
  decide

/-- `b ≤ D` is needed in `ordinaryFrobenius_sharp_factor`. -/
example : ¬ (2 * 1 * 2 - 1) * (2 * 2 - 1) ≤ (2 * 1 - 1) * (2 * (2 * 2) - 1) := by decide

/-- `B ≤ 2 * D + 1` is needed in `ordinaryPsi_eq_sharp`. -/
example : ordinaryPsi 0 2 ≠ 1 + (2 * 0 - 1) * (2 * 2 - 1) := by decide

/-- Both positivity hypotheses are needed in `ordinaryPsi_le_four_mul`. -/
example : ¬ ordinaryPsi 0 1 ≤ 4 * 0 * 1 ∧ ¬ ordinaryPsi 1 0 ≤ 4 * 1 * 0 := by decide

/-- The unified coefficient comparison holds in the degenerate case `D = 0`. -/
example (s b : ℕ) : 1 + (2 * 0 * s - 1) * (2 * b - 1) ≤ ordinaryPsi 0 (s * b) :=
  ordinaryFrobenius_unified_factor 0 s b

/-- `1 ≤ s` is needed in `ordinaryFrobenius_charge_le`: for `s = 0`, `b = h = 1`, `theta = 0`
and `n = D = 0` the left side is `1` and the right side is `0`. -/
example :
    ¬ ((((2 * 1 - 1) * 1 : ℕ) : ℚ) + 0 * ordinaryFrobeniusMixedDegree 0 1 0 1 +
        ((0 - 0 - 1) * 1 : ℕ) ≤ ordinaryFactorRaw 0 0 0 (0 * 1) 1) := by
  norm_num [ordinaryFactorRaw]

/-- `1 ≤ mu` is needed in `ordinaryFactorRaw_sum_le`: with no factors, content height `1`,
`H = 1` and `mu = 0`, the total charge is `0`. -/
example : ¬ ((1 : ℚ) + ∑ i ∈ (∅ : Finset ℕ), ordinaryFactorRaw 0 0 0 i i ≤
    ordinaryFactorRaw 0 0 0 0 1) := by
  norm_num [ordinaryFactorRaw]

/-- `1 ≤ B` is needed in `ordinaryUnifiedPowerFactorRawAt_sum_le`. -/
example : ¬ ((1 : ℚ) + ∑ i ∈ (∅ : Finset ℕ), ordinaryUnifiedPowerFactorRawAt 0 0 0 0 i i 0 ≤
    ordinaryUnifiedPowerFactorRawAt 0 0 0 0 0 1 0) := by
  norm_num [ordinaryUnifiedPowerFactorRawAt]

/-! ### Aggregation -/

/-- A polynomial with content height `1` and two root factors, of root degrees `1` and `2` and
heights `3` and `4`, fits the total charge with `mu = 3` and `H = 8`. -/
example :
    (1 : ℚ) + ∑ i ∈ Finset.range 2, ordinaryFactorRaw (1 / 2) 16 3 (i + 1) (i + 3) ≤
      ordinaryFactorRaw (1 / 2) 16 3 3 8 :=
  ordinaryFactorRaw_sum_le (Finset.range 2) (fun i ↦ i + 1) (fun i ↦ i + 3) (1 / 2) 16 3 3 8 1
    (by norm_num) (by norm_num) (by decide) (by decide)

/-- The same factors under the fixed-split unified charge with two rows. -/
example :
    (1 : ℚ) + ∑ i ∈ Finset.range 2, ordinaryUnifiedPowerFactorRaw 2 16 3 2 (i + 1) (i + 3) ≤
      ordinaryUnifiedPowerFactorRaw 2 16 3 2 3 8 :=
  ordinaryUnifiedPowerFactorRaw_sum_le (Finset.range 2) (fun i ↦ i + 1) (fun i ↦ i + 3) 2 16 3 2
    3 8 1 (by norm_num) (by norm_num) (by decide) (by decide)

/-- At threshold `D + 1 = 4`, agreement threshold `A = 6` and block length `n = 12`, the
free-retention budget is the fixed-split charge with ratio `(12 - 3) / (6 - 3)`. -/
example :
    ordinaryUnifiedPowerFactorAt 12 3 1 2 5 6 4 =
      ordinaryUnifiedPowerFactorRaw (9 / 3) 12 3 1 2 5 := by
  simpa using ordinaryUnifiedPowerFactorAt_succ_eq 12 3 1 2 5 6 (by norm_num) (by norm_num)

/-! ### Source-shaped statements -/

/-- The source form of `ordinaryFrobeniusMixedDegree_eq`, with its hypothesis `1 ≤ b`. -/
example (D h s b : ℕ) (_hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b = h + s * b + (2 * D * s - 1) * h * (2 * b - 1) :=
  ordinaryFrobeniusMixedDegree_eq D h s b

/-- The source form of `ordinaryFrobeniusMixedDegree_le_sharp`. -/
example {D s b : ℕ} (h : ℕ) (hD : b ≤ D) (_hs : 1 ≤ s) (_hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b ≤ h + s * b + (2 * D - 1) * h * (2 * (s * b) - 1) :=
  ordinaryFrobeniusMixedDegree_le_sharp h hD

/-- The source form of `ordinaryFrobeniusMixedDegree_le_unified`. -/
example {D s b : ℕ} (h : ℕ) (_hD : 1 ≤ D) (_hs : 1 ≤ s) (_hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b ≤ s * b + h * ordinaryPsi D (s * b) :=
  ordinaryFrobeniusMixedDegree_le_unified D h s b

/-- The source form of `ordinaryFrobenius_charge_le`. -/
example (theta : ℚ) (n D h s b : ℕ) (htheta : 0 ≤ theta) (hs : 1 ≤ s) (_hb : 1 ≤ b) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusMixedDegree D h s b +
        ((n - D - 1) * b : ℕ) ≤ ordinaryFactorRaw theta n D (s * b) h :=
  ordinaryFrobenius_charge_le theta n D h s b htheta hs

/-- The source form of `ordinaryFrobenius_sharp_difference`, over `ℤ`. -/
example (D s b : ℤ) :
    (2 * D - 1) * (2 * (s * b) - 1) - (2 * D * s - 1) * (2 * b - 1) = 2 * (s - 1) * (D - b) :=
  ordinaryFrobenius_sharp_difference D s b

end ReedSolomon.FactorBudgetTest
