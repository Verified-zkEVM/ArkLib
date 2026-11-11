/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.BigOperators.Intervals
import ArkLib.ToMathlib.BigOperators.LinearBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for cast power sums and linear budgets
-/

open Finset
open scoped BigOperators

/-- The sum of `0, 1, 2, 3` satisfies the doubled formula in `ℚ`. -/
example : (∑ i ∈ range 4, (i : ℚ)) * 2 = 4 * (4 - 1) :=
  sum_range_natCast_mul_two (R := ℚ) 4

/-- The sum of squares through `4` satisfies the formula multiplied by `6` in `ℚ`. -/
example : (∑ i ∈ range 5, (i : ℚ) ^ 2) * 6 = 5 * (5 - 1) * (2 * 5 - 1) :=
  sum_range_natCast_sq_mul_six (R := ℚ) 5

/-- Four charges `i`, each bounded by `1 + i`, fit within the two concrete budgets. -/
example : 2 + ∑ i ∈ range 4, i ≤ 1 * 6 + 1 * 6 :=
  Finset.add_sum_le_mul_add_mul_of_le (range 4) (h := fun _ ↦ 1) (a := fun i ↦ i)
    (Nat.zero_le _) le_rfl (Nat.zero_le _) (fun i _ ↦ by omega) (by decide) (by decide)

/-- The coefficient slots and weights sum to `3 * 2` for weights `0, 1, 0`. -/
example :
    (range 3).sum (fun i ↦ 2 - i % 2) + (range 3).sum (fun i ↦ i % 2) =
      (range 3).card * 2 :=
  Finset.sum_tsub_add_sum_eq_card_mul (range 3) (fun i ↦ i % 2) 1
    (by intro i hi; omega)

/-- With weights `0, 1, 0`, one row has strict slot surplus at height `1`. -/
example :
    Finset.slotSurplusHeight (range 3) (fun i ↦ i % 2) 1 1 = 1 ∧
      1 * (Finset.slotSurplusHeight (range 3) (fun i ↦ i % 2) 1 1 + 1) <
        (range 3).sum (fun i ↦
          Finset.slotSurplusHeight (range 3) (fun i ↦ i % 2) 1 1 + 1 - i % 2) := by
  refine ⟨by decide, ?_⟩
  exact Finset.rows_mul_slotSurplusHeight_add_one_lt_sum_tsub (range 3) (fun i ↦ i % 2) 1 1
    (by decide) (by intro i hi; omega)
