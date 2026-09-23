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
