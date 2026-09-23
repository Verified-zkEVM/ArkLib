/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.BigOperators.LinearBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for summing charges bounded by two budgets

The first examples apply `Finset.add_sum_le_mul_add_mul_of_le` in `ℕ` and in `ℚ`, where the
charges are not themselves of the form `c * h i + e * a i`. The last two show that `0 ≤ r` and
`1 ≤ c` are needed: in each, every other hypothesis holds and the conclusion fails.
-/

open scoped BigOperators

namespace LinearBudgetTest

/-- In `ℕ`: charges `i` on `range 4`, bounded by `1 * 1 + 1 * i`; heights total `4` and the
second shares total `6`, so `2 + ∑ i < 4, i ≤ 1 * 6 + 1 * 6`. -/
example : 2 + ∑ i ∈ Finset.range 4, i ≤ 1 * 6 + 1 * 6 :=
  Finset.add_sum_le_mul_add_mul_of_le (Finset.range 4) (h := fun _ ↦ 1) (a := fun i ↦ i)
    (Nat.zero_le _) le_rfl (Nat.zero_le _) (fun i _ ↦ by omega) (by decide) (by decide)

/-- In `ℚ`: charges `i ^ 2 / 2` on `range 3`, bounded by `2 * 1 + (1 / 2) * i ^ 2`. -/
example : (1 : ℚ) + ∑ i ∈ Finset.range 3, (i : ℚ) ^ 2 / 2 ≤ 2 * 4 + (1 / 2) * 5 :=
  Finset.add_sum_le_mul_add_mul_of_le (Finset.range 3) (h := fun _ ↦ (1 : ℚ))
    (a := fun i ↦ (i : ℚ) ^ 2) (c := 2) (e := 1 / 2) zero_le_one (by norm_num) (by norm_num)
    (fun i _ ↦ by linarith)
    (by norm_num) (by simp [Finset.sum_range_succ]; norm_num)

/-- `0 ≤ r` is needed: with `s = ∅`, `r = H = -1`, `c = 2`, `e = B = 0`, the remaining
hypotheses hold and `r + ∑ ≤ c * H + e * B` reads `-1 ≤ -2`. -/
example :
    (1 : ℤ) ≤ 2 ∧ (0 : ℤ) ≤ 0 ∧
      (-1 : ℤ) + ∑ _i ∈ (∅ : Finset ℕ), (0 : ℤ) ≤ -1 ∧
      ∑ _i ∈ (∅ : Finset ℕ), (0 : ℤ) ≤ 0 ∧
      ¬ ((-1 : ℤ) + ∑ _i ∈ (∅ : Finset ℕ), (0 : ℤ) ≤ 2 * (-1) + 0 * 0) := by
  norm_num

/-- `1 ≤ c` is needed: with `s = ∅`, `r = H = 1`, `c = 0`, `e = B = 0`, the remaining
hypotheses hold and the conclusion reads `1 ≤ 0`. -/
example :
    (0 : ℚ) ≤ 1 ∧ (1 : ℚ) + ∑ _i ∈ (∅ : Finset ℕ), (0 : ℚ) ≤ 1 ∧
      ¬ ((1 : ℚ) + ∑ _i ∈ (∅ : Finset ℕ), (0 : ℚ) ≤ 0 * 1 + 0 * 0) := by
  norm_num

/-- The weights `0, 1, 0` give height `1`, five slots, and a strict surplus for one row. -/
example :
    Finset.slotSurplusHeight (Finset.range 3) (fun i ↦ i % 2) 1 1 = 1 ∧
      Finset.sum (Finset.range 3) (fun i ↦
        Finset.slotSurplusHeight (Finset.range 3) (fun j ↦ j % 2) 1 1 + 1 - i % 2) = 5 ∧
      2 < 5 := by
  have hheight : Finset.slotSurplusHeight (Finset.range 3) (fun i ↦ i % 2) 1 1 = 1 := by
    decide
  have hslots : Finset.sum (Finset.range 3) (fun i ↦
      Finset.slotSurplusHeight (Finset.range 3) (fun j ↦ j % 2) 1 1 + 1 - i % 2) = 5 := by
    rw [hheight]
    decide
  have hsurplus :
      1 * (Finset.slotSurplusHeight (Finset.range 3) (fun i ↦ i % 2) 1 1 + 1) <
        Finset.sum (Finset.range 3) (fun i ↦
          Finset.slotSurplusHeight (Finset.range 3) (fun j ↦ j % 2) 1 1 + 1 - i % 2) :=
    Finset.rows_mul_slotSurplusHeight_add_one_lt_sum_tsub (Finset.range 3)
      (fun i ↦ i % 2) 1 1 (by decide) (by intro i hi; omega)
  refine ⟨hheight, hslots, ?_⟩
  rw [hslots, hheight] at hsurplus
  change 2 < 5 at hsurplus
  exact hsurplus

/-- With as many rows as columns, the zero-denominator height can provide no strict surplus. -/
example :
    ¬ (1 * (Finset.slotSurplusHeight ({0} : Finset ℕ) (fun _ ↦ 0) 0 1 + 1) <
      ({0} : Finset ℕ).sum (fun _ ↦
        Finset.slotSurplusHeight ({0} : Finset ℕ) (fun _ ↦ 0) 0 1 + 1)) := by
  norm_num [Finset.slotSurplusHeight]

end LinearBudgetTest
