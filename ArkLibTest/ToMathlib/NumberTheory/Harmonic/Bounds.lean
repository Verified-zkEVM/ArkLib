/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds

/-!
# Acceptance cases for the explicit harmonic bounds

The source's statements, with their dimension thresholds and summands `(1 / (i + 1)) ^ k`, derived
from the general ones; numerical consequences at small and large indices; and the sharpness of the
threshold `8 ≤ n` in `Real.reciprocal_square_sum_gt`.
-/

open Finset Real

/-! ### Source-shaped statements -/

/-- The source's `Real.harmonic_pred_le_log_add_three_fifths`, with its unused hypothesis
`33 ≤ d`. -/
example (d : ℕ) (_hd : 33 ≤ d) : (harmonic (d - 1) : ℝ) ≤ log d + 3 / 5 :=
  (harmonic_pred_lt_log_add_three_fifths d).le

/-- The source's `Real.harmonic_le_log_add_three_fifths`. -/
example (n : ℕ) (hn : 32 ≤ n) : (harmonic n : ℝ) ≤ log n + 3 / 5 :=
  (harmonic_lt_log_add_three_fifths hn).le

/-- The source's `WeightedSupportParameters.harmonic_square_bound` at `H = harmonic (d - 1)`: its
hypothesis `H ≤ log d + 3 / 5` is discharged. -/
example (d : ℕ) (hd : 10000 ≤ d) : (harmonic (d - 1) : ℝ) ^ 2 ≤ d / 100 := by
  have h := harmonic_sq_le_succ_div_hundred (n := d - 1) (by omega)
  rwa [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, sub_add_cancel] at h

/-- The source's `Real.reciprocal_square_sum_gt`, with summand `(1 / (i + 1)) ^ 2`. -/
example {n : ℕ} (hn : 8 ≤ n) : (38 / 25 : ℝ) < ∑ i ∈ range n, (1 / (i + 1 : ℝ)) ^ 2 := by
  simpa only [div_pow, one_pow] using reciprocal_square_sum_gt hn

/-- The source's `Real.reciprocal_square_sum_lt`, with summand `(1 / (i + 1)) ^ 2`. -/
example (n : ℕ) : (∑ i ∈ range n, (1 / (i + 1 : ℝ)) ^ 2) < 329 / 200 := by
  simpa only [div_pow, one_pow] using reciprocal_square_sum_lt n

/-- The source's `Real.reciprocal_cube_sum_lt`, with summand `(1 / (i + 1)) ^ 3`. -/
example (n : ℕ) : (∑ i ∈ range n, (1 / (i + 1 : ℝ)) ^ 3) < 12021 / 10000 := by
  simpa only [div_pow, one_pow] using reciprocal_cube_sum_lt n

/-! ### Numerical consequences -/

/-- Together with Mathlib's lower bound, `1 / 2 < γ < 3 / 5`. -/
example : 1 / 2 < eulerMascheroniConstant ∧ eulerMascheroniConstant < 3 / 5 :=
  ⟨one_half_lt_eulerMascheroniConstant, eulerMascheroniConstant_lt_three_fifths⟩

/-- At `d = 3`, `harmonic 2 = 3 / 2 < log 3 + 3 / 5` gives `9 / 10 < log 3`. The bound needs no
lower threshold on `d`. -/
example : (9 / 10 : ℝ) < log 3 := by
  have h := harmonic_pred_lt_log_add_three_fifths 3
  norm_num [harmonic, sum_range_succ] at h
  linarith

/-- At `x = 10000`, `log 10000 + 3 / 5 ≤ 10`. -/
example : log 10000 + 3 / 5 ≤ (10 : ℝ) := by
  have h := log_add_three_fifths_le_sqrt_div_ten (x := 10000) le_rfl
  have hs : √(10000 : ℝ) = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  rw [hs] at h
  linarith

/-- At `n = 9999`, `harmonic 9999 ^ 2 ≤ 100`, so `harmonic 9999 ≤ 10`. -/
example : (harmonic 9999 : ℝ) ≤ 10 := by
  have h := harmonic_sq_le_succ_div_hundred (n := 9999) le_rfl
  have h0 : (0 : ℝ) ≤ harmonic 9999 := by
    exact_mod_cast (sum_nonneg fun i _ ↦ by positivity : (0 : ℚ) ≤ harmonic 9999)
  generalize (harmonic 9999 : ℝ) = H at h h0
  have h' : H ^ 2 ≤ 100 := by
    have h9 : ((9999 : ℕ) : ℝ) = 9999 := by norm_num
    rw [h9] at h
    linarith
  nlinarith

/-- The square sums are below `π ^ 2 / 6` already at `n = 0`, where the sum is empty. -/
example : ∑ i ∈ range 0, 1 / ((i : ℝ) + 1) ^ 2 < π ^ 2 / 6 :=
  sum_range_one_div_succ_sq_lt_pi_sq_div_six 0

/-! ### Sharpness -/

/-- The threshold `8 ≤ n` of `Real.reciprocal_square_sum_gt` is sharp: the first seven terms sum
to about `1.5118 < 38 / 25`. -/
example : ¬ (38 / 25 : ℝ) < ∑ i ∈ range 7, 1 / ((i : ℝ) + 1) ^ 2 := by
  norm_num [sum_range_succ]
