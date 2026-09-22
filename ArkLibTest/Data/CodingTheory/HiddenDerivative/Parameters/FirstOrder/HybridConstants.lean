/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants

/-!
# First-order constant acceptance tests

Stage sums and the staircase at small parameters, the balanced split and its ratios, the
exception constant at a parameter set where it is not an integer, the unfolded forms of the
comparisons, and cases showing that the hypotheses `1 ≤ θ`, `A ≤ n`, `D < A`, `D < n` and
`0 ≤ θ` are needed.
-/

namespace ReedSolomon.HiddenDerivative

/-! ### Stage sums and the staircase at `D = 2`, `μ = 3`, `e = 2` -/

/-- The regular exponent is `2 D - 3`, and `0` at `D = 1`. -/
example : regularTaylorExponent 2 = 1 ∧ regularTaylorExponent 1 = 0 := ⟨rfl, rfl⟩

/-- The staircase is `1 · 3 + 2 · 4 = 11`. -/
example : stageStaircaseSum 3 2 = 11 := rfl

/-- Its descending form is `2 · 4 + 1 · 3`. -/
example : ∑ i ∈ Finset.range 2, (2 - i) * (2 * (3 - i) - (2 - i)) = stageStaircaseSum 3 2 :=
  (stageStaircaseSum_eq_sum_stages (by norm_num)).symm

/-- The closed form is `1 · 2 · 3 + 2 · 3 · 5 / 6 = 11`. -/
example : stageStaircase 3 2 = 11 := by
  rw [← cast_stageStaircaseSum]
  norm_num [stageStaircaseSum]

/-- The fixed-fiber degrees of the two order-one stages are `9` and `4`. -/
example : regularFiberStageSum 2 3 2 = 13 := by decide

/-- The joint degrees of the two order-one stages at `h = 1` are `45` and `20`. -/
example : regularJointStageSum 2 1 3 2 = 65 := by decide

/-- The fiber sum is at most `2 D T = 44`. -/
example : regularFiberStageSum 2 3 2 ≤ 2 * 2 * stageStaircaseSum 3 2 :=
  regularFiberStageSum_le (by norm_num) (by norm_num)

/-- The joint sum is at most `(12 D² h + 4 D) T = 616`. -/
example : regularJointStageSum 2 1 3 2 ≤ (12 * 2 ^ 2 * 1 + 4 * 2) * stageStaircaseSum 3 2 :=
  regularJointStageSum_le (by norm_num) (by norm_num)

/-! ### The balanced split -/

/-- For `A - D = 3` and `A - D = 4` the balanced split adds `2`. -/
example : balancedSplit 1 4 = 3 ∧ balancedSplit 1 5 = 3 := ⟨rfl, rfl⟩

/-- The ceiling form at `A - D = 3`. -/
example : balancedSplit 1 4 = 1 + ⌈((3 : ℕ) : ℝ) / 2⌉₊ := balancedSplit_eq_add_ceil 1 4

/-- At `n = 10`, `D = 1`, `A = 4`: `θ = 3`, and the ratios at `L = 3` are `8 / 2 = 4` and
`9 / 2`, both at most `2 θ = 6`. -/
example : agreementIncidenceRatio 10 1 4 = 3 ∧ retainedCoordinateRatio 10 4 3 = 4 ∧
    fixedCoordinateRatio 10 1 3 = 9 / 2 := by
  norm_num [agreementIncidenceRatio, retainedCoordinateRatio, fixedCoordinateRatio]

/-! ### The exception constant at a nonintegral value -/

/-- At `n = 4`, `D = 1`, `A = 3`, `h = 1`, `μ = 2` and `M = 0`, `θ = 3/2`, the staircase is `0`,
and the exception constant is the ordinary-tail charge `3 + 3/2 · 11 + 2 · 2 = 47/2`. -/
theorem firstOrderExceptionConstant_eq_forty_seven_halves :
    firstOrderExceptionConstant (agreementIncidenceRatio 4 1 3) 4 1 1 2 0 = 47 / 2 := by
  norm_num [firstOrderExceptionConstant, ordinaryTailCharge, agreementIncidenceRatio,
    stageStaircase]

/-- Its ceiling `24` is strictly larger, so a real bound is not interchangeable with its
ceiling. -/
example : ⌈firstOrderExceptionConstant (agreementIncidenceRatio 4 1 3) 4 1 1 2 0⌉₊ = 24 := by
  rw [firstOrderExceptionConstant_eq_forty_seven_halves, Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-! ### Unfolded forms -/

/-- The list charge at `e ≤ M` is at most `2 D θ T + μ - M`. -/
example {θ : ℝ} {D μ e M : ℕ} (hθ : 1 ≤ θ) (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    firstOrderListCharge θ D μ e ≤ 2 * D * θ * stageStaircase μ M + (μ - M : ℕ) :=
  firstOrderListCharge_le_firstOrderListConstant hθ hD heM hMμ

/-- The optimized list charge at `θ = (n - D) / (A - D)` is at most `Λ`. -/
example {n D A μ M : ℕ} (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ) :
    maxFirstOrderListCharge (agreementIncidenceRatio n D A) D μ M ≤
      2 * D * agreementIncidenceRatio n D A * stageStaircase μ M + (μ - M : ℕ) :=
  maxFirstOrderListCharge_le_firstOrderListConstant (one_le_agreementIncidenceRatio hDA hAn) hD
    hMμ

/-- The balanced split satisfies `D < L ≤ A`, and the three denominators `A - L + 1`, `L - D` and
`A - D` are positive. -/
example {D A : ℕ} (hDA : D < A) :
    0 < A - balancedSplit D A + 1 ∧ 0 < balancedSplit D A - D ∧ 0 < A - D := by
  have := lt_balancedSplit hDA
  have := balancedSplit_le hDA.le
  omega

/-! ### Boundary cases -/

/-- `one_le_agreementIncidenceRatio` needs `A ≤ n`: at `n = 2`, `D = 1`, `A = 4`, `θ = 1/3`. -/
example : agreementIncidenceRatio 2 1 4 = 1 / 3 := by norm_num [agreementIncidenceRatio]

/-- `firstOrderListCharge_le_succ` needs `1 ≤ θ`: at `θ = 0`, `D = 1`, `μ = 2` the list charge
drops from `2` at `e = 0` to `1` at `e = 1`. -/
example : firstOrderListCharge 0 1 2 0 = 2 ∧ firstOrderListCharge 0 1 2 1 = 1 := by
  norm_num [firstOrderListCharge]

/-- `lt_balancedSplit` needs `D < A`: the split at `A = D` is `D`. -/
example : balancedSplit 2 2 = 2 := rfl

/-- `balancedSplit_le` needs `D ≤ A`: the split at `D = 2`, `A = 1` is `2`. -/
example : balancedSplit 2 1 = 2 := rfl

/-- `sub_balancedSplit_le` needs `D < A`: at `n = 3`, `D = A = 1`, `n - L = 2` and
`n - D - 1 = 1`. -/
example : 3 - balancedSplit 1 1 = 2 := rfl

/-- `retainedCoordinateRatio_balancedSplit_le` needs `D < n`: at `n = D = 1`, `A = 3`, the ratio
at `L = 2` is `1/2` while `θ = 0`. -/
example : retainedCoordinateRatio 1 3 (balancedSplit 1 3) = 1 / 2 ∧
    agreementIncidenceRatio 1 1 3 = 0 := by
  norm_num [retainedCoordinateRatio, balancedSplit, agreementIncidenceRatio]

/-- `ordinaryTailCharge_le` needs `0 ≤ θ`: at `θ = -10` the charge at `μ = 1` is `-10`, below the
charge `0` at `b = 0`. -/
example : ordinaryTailCharge (-10) 0 0 0 0 = 0 ∧ ordinaryTailCharge (-10) 0 0 0 1 = -10 := by
  norm_num [ordinaryTailCharge]

end ReedSolomon.HiddenDerivative
