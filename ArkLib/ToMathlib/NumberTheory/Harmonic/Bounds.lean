/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.ZetaValues

/-!
# Explicit bounds on harmonic numbers and power sums

This file proves explicit numerical bounds on the harmonic numbers `harmonic n` and on the partial
sums `∑ i ∈ Finset.range n, 1 / (i + 1) ^ k` for `k = 2, 3`.

The logarithmic bound comes from the Euler–Mascheroni constant. Mathlib proves that
`harmonic n - log (n + 1)` increases strictly to `γ` and that `harmonic n - log n` decreases
strictly to `γ`. Evaluating the second sequence at `n = 32`, where `log 32 = 5 * log 2`, gives
`γ < 3 / 5`, and then `harmonic n < log (n + 1) + 3 / 5` for every `n`. A comparison of
`log (√x / 100)` with `√x / 100 - 1` turns this into `harmonic n ^ 2 ≤ (n + 1) / 100` for
`n ≥ 9999`. The ratio `(log x + b) / √x` decreases for `x ≥ exp 2` and `b ≥ 0`; at `x = 48000`
this gives `log x + 3 / 5 ≤ (19 / 365) √x`.

The partial sums of `1 / (i + 1) ^ 2` are below `π ^ 2 / 6 < 329 / 200` by Mathlib's
`hasSum_zeta_two`. For the third power there is no closed form; the partial sums are bounded by
twelve exact terms plus the telescoping tail bound
`1 / (k + 1) ^ 3 + 2 / (2 * k + 3) ^ 2 ≤ 2 / (2 * k + 1) ^ 2`.

## Main statements

* `Real.eulerMascheroniConstant_lt_three_fifths`: `γ < 3 / 5`.
* `Real.harmonic_lt_log_succ_add_three_fifths`: `harmonic n < log (n + 1) + 3 / 5` for every `n`,
  and its shifted form `Real.harmonic_pred_lt_log_add_three_fifths`.
* `Real.harmonic_lt_log_add_three_fifths`: `harmonic n < log n + 3 / 5` for `n ≥ 32`.
* `Real.log_add_three_fifths_le_sqrt_div_ten`: `log x + 3 / 5 ≤ √x / 10` for `x ≥ 10000`.
* `Real.harmonic_sq_le_succ_div_hundred`: `harmonic n ^ 2 ≤ (n + 1) / 100` for `n ≥ 9999`, and the
  form `Real.sq_le_div_hundred_of_le_log_add_three_fifths` for any `H ≤ log x + 3 / 5`.
* `Real.log_le_harmonic_pred`: `log d ≤ harmonic (d - 1)` for every natural `d`.
* `Real.log_add_le_mul_sqrt_of_le` and `Real.log_add_three_fifths_le_nineteen_div_365_mul_sqrt`:
  `log x + b ≤ ((log x₀ + b) / √x₀) √x` for `exp 2 ≤ x₀ ≤ x`, and its case `x₀ = 48000`.
* `Real.sum_range_one_div_succ_sq_lt_pi_sq_div_six`, `Real.reciprocal_square_sum_lt`,
  `Real.reciprocal_square_sum_gt`, `Real.reciprocal_cube_sum_lt`: bounds on the partial sums of
  `1 / (i + 1) ^ 2` and `1 / (i + 1) ^ 3`.
-/

@[expose] public section

open Finset

namespace Real

/-- `harmonic n - log n` at `n = 32` is below `3 / 5`; its value is about `0.5927`. -/
private theorem eulerMascheroniSeq'_thirtyTwo_lt : eulerMascheroniSeq' 32 < 3 / 5 := by
  have hlog : log (32 : ℝ) = 5 * log 2 := by
    have h := log_pow (2 : ℝ) 5
    norm_num at h
    exact h
  rw [eulerMascheroniSeq']
  norm_num only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [hlog]
  have htwo := log_two_gt_d9
  norm_num [harmonic, sum_range_succ] at *
  linarith

/-- The Euler–Mascheroni constant is below `3 / 5`. Its value is about `0.5772`. The bound is the
value of the decreasing sequence `harmonic n - log n` at `n = 32`. -/
theorem eulerMascheroniConstant_lt_three_fifths : eulerMascheroniConstant < 3 / 5 :=
  (eulerMascheroniConstant_lt_eulerMascheroniSeq' 32).trans eulerMascheroniSeq'_thirtyTwo_lt

/-- For every `n`, `harmonic n < log (n + 1) + 3 / 5`. The sequence `harmonic n - log (n + 1)`
increases strictly to `γ < 3 / 5`. For `n = 0` both harmonic number and logarithm are `0`. -/
theorem harmonic_lt_log_succ_add_three_fifths (n : ℕ) :
    (harmonic n : ℝ) < log (n + 1) + 3 / 5 := by
  have h := (eulerMascheroniSeq_lt_eulerMascheroniConstant n).trans
    eulerMascheroniConstant_lt_three_fifths
  rw [eulerMascheroniSeq] at h
  linarith

/-- For every `d`, `harmonic (d - 1) < log d + 3 / 5`. This is
`harmonic_lt_log_succ_add_three_fifths` at `n = d - 1`; for `d = 0` it reads `0 < 3 / 5`, since
`log 0 = 0` in Mathlib. -/
theorem harmonic_pred_lt_log_add_three_fifths (d : ℕ) :
    (harmonic (d - 1) : ℝ) < log d + 3 / 5 := by
  rcases d with _ | d
  · norm_num
  · simpa using harmonic_lt_log_succ_add_three_fifths d

/-- For `n ≥ 32`, `harmonic n < log n + 3 / 5`. The sequence `harmonic n - log n` decreases
strictly, and its value at `32` is below `3 / 5`. The inequality also holds for `22 ≤ n < 32`,
which this statement does not cover, and fails for `n = 21`, where `harmonic n - log n` is about
`0.6008`. -/
theorem harmonic_lt_log_add_three_fifths {n : ℕ} (hn : 32 ≤ n) :
    (harmonic n : ℝ) < log n + 3 / 5 := by
  have h := (strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt eulerMascheroniSeq'_thirtyTwo_lt
  have hn0 : n ≠ 0 := by omega
  simp only [eulerMascheroniSeq', hn0, ↓reduceIte] at h
  linarith

/-- `log 10 ≤ 47 / 20`, from the first ten terms of the exponential series at `47 / 20`. -/
private theorem log_ten_le : log 10 ≤ (47 / 20 : ℝ) := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 47 / 20) 10
  norm_num [sum_range_succ] at h
  apply (log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).mpr
  linarith

/-- For `x ≥ 10000`, `log x + 3 / 5 ≤ √x / 10`. Applying `log y ≤ y - 1` to `y = √x / 100`
gives `log x ≤ √x / 50 + 2 * log 100 - 2`, and `√x ≥ 100` absorbs the constant. The inequality
fails at `x = 9530`, so the threshold cannot be lowered much. -/
theorem log_add_three_fifths_le_sqrt_div_ten {x : ℝ} (hx : 10000 ≤ x) :
    log x + 3 / 5 ≤ √x / 10 := by
  have hx0 : 0 < x := by linarith
  have hs : 100 ≤ √x := by
    rw [le_sqrt (by norm_num) hx0.le]
    linarith
  have h := log_le_sub_one_of_pos (show 0 < √x / 100 by positivity)
  rw [log_div (by positivity) (by norm_num), log_sqrt hx0.le] at h
  have h100 : log 100 ≤ (47 / 10 : ℝ) := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, log_pow]
    nlinarith [log_ten_le]
  linarith

/-- For `n ≥ 9999`, `harmonic n ^ 2 ≤ (n + 1) / 100`. This combines
`harmonic_lt_log_succ_add_three_fifths` with `log_add_three_fifths_le_sqrt_div_ten` at
`x = n + 1`. -/
theorem harmonic_sq_le_succ_div_hundred {n : ℕ} (hn : 9999 ≤ n) :
    (harmonic n : ℝ) ^ 2 ≤ (n + 1) / 100 := by
  have hn' : (10000 : ℝ) ≤ n + 1 := by
    have : (9999 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hH := (harmonic_lt_log_succ_add_three_fifths n).le.trans
    (log_add_three_fifths_le_sqrt_div_ten hn')
  have hH0 : (0 : ℝ) ≤ harmonic n := by
    exact_mod_cast (sum_nonneg fun i _ ↦ by positivity : (0 : ℚ) ≤ harmonic n)
  have hsq := sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
  nlinarith [sqrt_nonneg ((n : ℝ) + 1)]

/-- For `x ≥ 10000`, `H ≥ 0` and `H ≤ log x + 3 / 5`, `H ^ 2 ≤ x / 100`. This is
`log_add_three_fifths_le_sqrt_div_ten` squared; `0 ≤ H` is needed to square the inequality. -/
theorem sq_le_div_hundred_of_le_log_add_three_fifths {x H : ℝ} (hx : 10000 ≤ x) (hH0 : 0 ≤ H)
    (hH : H ≤ log x + 3 / 5) : H ^ 2 ≤ x / 100 := by
  have h := hH.trans (log_add_three_fifths_le_sqrt_div_ten hx)
  have hs := sq_sqrt (show 0 ≤ x by linarith)
  nlinarith [sqrt_nonneg x]

/-- For every natural `d`, `log d ≤ harmonic (d - 1)`. This is Mathlib's
`log_add_one_le_harmonic` at `n = d - 1`; for `d = 0` both sides are `0`. -/
theorem log_le_harmonic_pred (d : ℕ) : log d ≤ (harmonic (d - 1) : ℝ) := by
  rcases d with _ | d
  · simp
  · simpa using log_add_one_le_harmonic d

/-- For `b ≥ 0` and `exp 2 ≤ x₀ ≤ x`, `log x + b ≤ ((log x₀ + b) / √x₀) √x`. Both `log x / √x`
(Mathlib's `log_div_sqrt_antitoneOn`) and `b / √x` decrease on `[exp 2, ∞)`. The hypothesis
`exp 2 ≤ x₀` is where `log x / √x` starts to decrease, and `0 ≤ b` makes `b / √x` decrease. -/
theorem log_add_le_mul_sqrt_of_le {b x₀ x : ℝ} (hb : 0 ≤ b) (h₀ : exp 2 ≤ x₀) (hx : x₀ ≤ x) :
    log x + b ≤ (log x₀ + b) / √x₀ * √x := by
  have hx₀ : 0 < x₀ := (exp_pos 2).trans_le h₀
  have hs₀ : 0 < √x₀ := sqrt_pos.2 hx₀
  have hs : 0 < √x := sqrt_pos.2 (hx₀.trans_le hx)
  have hlog : log x / √x ≤ log x₀ / √x₀ := log_div_sqrt_antitoneOn h₀ (h₀.trans hx) hx
  have hconst : b / √x ≤ b / √x₀ := div_le_div_of_nonneg_left hb hs₀ (sqrt_le_sqrt hx)
  rw [← div_le_iff₀ hs, add_div, add_div]
  linarith

/-- For `x ≥ 48000`, `log x + 3 / 5 ≤ (19 / 365) √x`. This is `log_add_le_mul_sqrt_of_le` at
`x₀ = 48000`, with `log 48000 < 54 / 5` and `√48000 > 219`, since
`(54 / 5 + 3 / 5) / 219 = 19 / 365`. -/
theorem log_add_three_fifths_le_nineteen_div_365_mul_sqrt {x : ℝ} (hx : 48000 ≤ x) :
    log x + 3 / 5 ≤ 19 / 365 * √x := by
  have hexp2 : exp 2 ≤ (48000 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hsqrt : (219 : ℝ) < √48000 := by
    rw [lt_sqrt (by norm_num)]
    norm_num
  have hlog : log 48000 < (54 / 5 : ℝ) :=
    (log_lt_iff_lt_exp (by norm_num)).mpr fortyEightThousand_lt_exp_fiftyFour_div_five
  have hlog0 : 0 ≤ log (48000 : ℝ) := log_nonneg (by norm_num)
  have hratio : (log 48000 + 3 / 5) / √48000 ≤ 19 / 365 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine (log_add_le_mul_sqrt_of_le (by norm_num) hexp2 hx).trans ?_
  gcongr

/-- Every partial sum `∑ i ∈ range n, 1 / (i + 1) ^ 2` is strictly below `π ^ 2 / 6`, the sum of
the series (Mathlib's `hasSum_zeta_two`). The inequality is strict because the omitted terms are
positive. -/
theorem sum_range_one_div_succ_sq_lt_pi_sq_div_six (n : ℕ) :
    ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 2 < π ^ 2 / 6 := by
  have hshift (k : ℕ) : ∑ i ∈ range k, 1 / ((i : ℝ) + 1) ^ 2 =
      ∑ i ∈ range (k + 1), 1 / ((i : ℕ) : ℝ) ^ 2 := by
    rw [sum_range_succ']
    simp
  have hle := sum_le_hasSum (range (n + 2)) (fun i _ ↦ by positivity) hasSum_zeta_two
  rw [← hshift, sum_range_succ] at hle
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2 := by positivity
  linarith

/-- Every partial sum `∑ i ∈ range n, 1 / (i + 1) ^ 2` is below `329 / 200 = 1.645`. It is below
`π ^ 2 / 6`, which is about `1.64493`, and `π < 3.1416`. -/
theorem reciprocal_square_sum_lt (n : ℕ) :
    ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 2 < 329 / 200 := by
  have hπ := pi_lt_d4
  have hπ0 := pi_pos
  have h := sum_range_one_div_succ_sq_lt_pi_sq_div_six n
  nlinarith

/-- For `n ≥ 8`, `38 / 25 < ∑ i ∈ range n, 1 / (i + 1) ^ 2`. The first eight terms sum to about
`1.5274`. The hypothesis `8 ≤ n` is sharp: the first seven terms sum to about `1.5118`. -/
theorem reciprocal_square_sum_gt {n : ℕ} (hn : 8 ≤ n) :
    (38 / 25 : ℝ) < ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 2 := by
  have hsum : ∑ i ∈ range 8, 1 / ((i : ℝ) + 1) ^ 2 ≤ ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (range_mono hn) fun _ _ _ ↦ by positivity
  have h : (38 / 25 : ℝ) < ∑ i ∈ range 8, 1 / ((i : ℝ) + 1) ^ 2 := by
    norm_num [sum_range_succ]
  exact h.trans_le hsum

/-- The telescoping step `1 / (k + 1) ^ 3 + 2 / (2 * k + 3) ^ 2 ≤ 2 / (2 * k + 1) ^ 2`. -/
private theorem reciprocal_cube_tail_step (k : ℕ) :
    1 / ((k : ℝ) + 1) ^ 3 + 2 / (2 * ((k : ℝ) + 1) + 1) ^ 2 ≤ 2 / (2 * (k : ℝ) + 1) ^ 2 := by
  have h₁ : (0 : ℝ) < k + 1 := by positivity
  have h₂ : (0 : ℝ) < 2 * ((k : ℝ) + 1) + 1 := by positivity
  have h₃ : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [show (0 : ℝ) ≤ (k : ℝ) ^ 2 by positivity, show (0 : ℝ) ≤ (k : ℝ) ^ 3 by positivity,
    show (0 : ℝ) ≤ (k : ℝ) ^ 4 by positivity]

/-- Every partial sum `∑ i ∈ range n, 1 / (i + 1) ^ 3` is below `12021 / 10000`; the full series
is `ζ(3)`, about `1.20206`. The proof adds twelve exact terms and the telescoping tail bound
`2 / (2 * n + 1) ^ 2` for the terms from index `n` on. -/
theorem reciprocal_cube_sum_lt (n : ℕ) :
    ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 3 < 12021 / 10000 := by
  have hinit : ∑ i ∈ range 12, 1 / ((i : ℝ) + 1) ^ 3 + 2 / (2 * (12 : ℝ) + 1) ^ 2 <
      12021 / 10000 := by
    norm_num [sum_range_succ]
  rcases le_or_gt 12 n with hn | hn
  · have hbound : ∀ k, 12 ≤ k →
        ∑ i ∈ range k, 1 / ((i : ℝ) + 1) ^ 3 + 2 / (2 * (k : ℝ) + 1) ^ 2 ≤
          ∑ i ∈ range 12, 1 / ((i : ℝ) + 1) ^ 3 + 2 / (2 * (12 : ℝ) + 1) ^ 2 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [sum_range_succ]
        push_cast
        linarith [reciprocal_cube_tail_step k]
    have hp : (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) ^ 2 := by positivity
    linarith [hbound n hn]
  · have hsum : ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 3 ≤ ∑ i ∈ range 12, 1 / ((i : ℝ) + 1) ^ 3 :=
      sum_le_sum_of_subset_of_nonneg (range_mono hn.le) fun _ _ _ ↦ by positivity
    have hp : (0 : ℝ) < 2 / (2 * (12 : ℝ) + 1) ^ 2 := by positivity
    linarith

end Real
