/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Harmonic estimates from explicit thresholds

Numerical bounds on the harmonic numbers and on the partial sums of `∑ 1 / k ^ 2`, uniform in
the number of terms from an explicit threshold on.

* The sequence `harmonic n - log n` decreases to the Euler–Mascheroni constant `γ ≈ 0.5772`, so
  one exact evaluation at the threshold bounds every later term.
* The partial sums of `∑ 1 / k ^ 2` increase, so one exact evaluation at the threshold bounds every
  later partial sum from below.

Both thresholds are the least ones for which the stated bound holds.

## Main statements

* `Real.harmonic_sub_log_lt`: `harmonic n - log n < 29 / 50` for `180 ≤ n`.
* `Real.lt_sum_fin_one_div_add_one_sq`: `41 / 25 < ∑ i < n, 1 / (i + 1) ^ 2` for `203 ≤ n`.
-/

@[expose] public section

open scoped BigOperators

namespace Real

/-- For `180 ≤ n`, `harmonic n - log n < 29 / 50`. The sequence `harmonic n - log n` is
decreasing, and its value at `n = 180` is below `29 / 50`; at `n = 179` it is not. -/
theorem harmonic_sub_log_lt {n : ℕ} (hn : 180 ≤ n) :
    (harmonic n : ℝ) - log n < 29 / 50 := by
  have hlog : log (180 : ℝ) = 2 * log 2 + 2 * log 3 + log 5 := by
    calc
      log (180 : ℝ) = log ((2 : ℝ) ^ 2 * (3 : ℝ) ^ 2 * 5) := by norm_num
      _ = 2 * log 2 + 2 * log 3 + log 5 := by
        rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
          log_pow, log_pow]
        norm_num
  have hbase : eulerMascheroniSeq' 180 < 29 / 50 := by
    rw [eulerMascheroniSeq']
    norm_num only [OfNat.ofNat_ne_zero, ↓reduceIte]
    rw [hlog]
    have htwo := log_two_gt_d9
    have hthree := log_three_gt_d9
    have hfive := log_five_gt_d9
    norm_num [harmonic, Finset.sum_range_succ] at *
    linarith
  have hmono := (strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt hbase
  have hn0 : n ≠ 0 := by omega
  simpa only [eulerMascheroniSeq', hn0, ↓reduceIte] using hmono

/-- For `203 ≤ n`, `41 / 25 < ∑ i : Fin n, 1 / (i + 1) ^ 2`. The partial sums increase, and the
sum of the first `203` terms exceeds `41 / 25`; the sum of the first `202` does not. -/
theorem lt_sum_fin_one_div_add_one_sq {n : ℕ} (hn : 203 ≤ n) :
    (41 / 25 : ℝ) < ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1) ^ 2) n]
  have hbase : (41 / 25 : ℝ) < ∑ i ∈ Finset.range 203, 1 / ((i : ℝ) + 1) ^ 2 := by
    norm_num [Finset.sum_range_succ]
  exact hbase.trans_le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
    fun _ _ _ ↦ by positivity)

end Real
