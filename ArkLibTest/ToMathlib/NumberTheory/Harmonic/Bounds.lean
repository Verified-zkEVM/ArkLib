/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds

/-!
# Acceptance cases for explicit harmonic estimates

Both bounds at their thresholds and beyond, and the threshold `203` for the partial sums of
`∑ 1 / k ^ 2` shown to be sharp by an exact rational evaluation at `202`.
-/

/-- The logarithmic bound at its threshold `n = 180`. -/
example : (harmonic 180 : ℝ) - Real.log 180 < 29 / 50 :=
  Real.harmonic_sub_log_lt le_rfl

/-- The logarithmic bound at `n = 500`. -/
example : (harmonic 500 : ℝ) - Real.log 500 < 29 / 50 :=
  Real.harmonic_sub_log_lt (by norm_num)

/-- The lower bound on the partial sums at its threshold `n = 203`. -/
example : (41 / 25 : ℝ) < ∑ i : Fin 203, 1 / ((i : ℝ) + 1) ^ 2 :=
  Real.lt_sum_fin_one_div_add_one_sq le_rfl

/-- The threshold `203` is sharp: the sum of the first `202` terms is at most `41 / 25`. -/
example : ∑ i : Fin 202, 1 / ((i : ℝ) + 1) ^ 2 ≤ 41 / 25 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1) ^ 2) 202]
  norm_num [Finset.sum_range_succ]
