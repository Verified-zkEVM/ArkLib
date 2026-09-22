/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.MaxCoordinate
public import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The squared lower tail of the coordinate sum on the weighted simplex

Let `u` be a uniform point of the weighted simplex `weightedSimplex (fun i : Fin d ↦ i + 1) W`.
Its coordinate sum `∑ i, u i`, divided by `W`, has the law of the largest coordinate of a uniform
point of the standard simplex of budget `1`
(`MeasureTheory.setAverage_standardSimplex_comp_sup'`), so `d * (∑ i, u i) / W - log d`
concentrates near the Euler–Mascheroni constant. This file proves that for `500 ≤ d` and
`0 < W` the squared lower tail below `log 6` has average more than `27 / 10`:
`27 / 10 < ⨍ u in weightedSimplex (i + 1) W, max (log (6 * d) - d * (∑ i, u i) / W) 0 ^ 2`.

The proof reduces to `W = 1` by dilation and writes the positive part below `log 6` as the full
square `(log 6 + log d - d * ∑ i, u i) ^ 2` minus the positive part above `log 6`.

* The full square is a quadratic in `∑ i, u i`, whose average is exact in terms of the harmonic
  number `H = harmonic d` and `Q = ∑ i < d, 1 / (i + 1) ^ 2`.
* The positive part above `log 6` has squared average at most `2 * exp (-log 6) = 1 / 3`, by the
  exponential tail of the largest coordinate.
* The numerical bounds `H - log d < 29 / 50`, `41 / 25 < Q`, `179 / 100 < log 6` and
  `log 500 < 311 / 50` finish the estimate; the error term is a quadratic in `log d` divided by
  `d`, which decreases in `d`.

## Main statements

* `setAverage_weightedSimplex_succ_sub_mul_sum_sq`: the average of `(a - b * ∑ i, u i) ^ 2`.
* `setAverage_weightedSimplex_succ_upperTail_sq_le`: the squared upper tail above `log 6` has
  average at most `1 / 3`.
* `setAverage_weightedSimplex_succ_lowerTail_sq_gt`: the squared lower tail below `log 6` has
  average more than `27 / 10`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative.RatePartition

/-! ### Numerical facts -/

private theorem log_six_gt : (179 / 100 : ℝ) < Real.log 6 := by
  have hlog : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [hlog]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private theorem log_five_hundred_lt : Real.log 500 < (311 / 50 : ℝ) := by
  have hlog : Real.log (500 : ℝ) = 2 * Real.log 2 + 3 * Real.log 5 := by
    calc
      Real.log (500 : ℝ) = Real.log ((2 : ℝ) ^ 2 * (5 : ℝ) ^ 3) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log ((5 : ℝ) ^ 3) := by
        rw [Real.log_mul] <;> positivity
      _ = 2 * Real.log 2 + 3 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
  rw [hlog]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

/-- The harmonic number as a sum over `Fin n`. -/
private theorem harmonic_eq_sum_fin (n : ℕ) :
    (harmonic n : ℝ) = ∑ i : Fin n, 1 / ((i : ℝ) + 1) := by
  rw [harmonic, Rat.cast_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1)) n]
  push_cast
  simp [one_div]

/-- The error quadratic `q(y) = y ^ 2 - (15721 / 12525) y + 4829141 / 1252500` gives a function
`q (log x) / x` that decreases on `[500, ∞)`. -/
private theorem antitoneOn_errorQuadratic_log_div :
    AntitoneOn (fun x : ℝ ↦
      (Real.log x ^ 2 - 15721 / 12525 * Real.log x + 4829141 / 1252500) / x) (Ici 500) := by
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ ↦
      (Real.log x ^ 2 - 15721 / 12525 * Real.log x + 4829141 / 1252500) / x)
      ((2 * Real.log x - 15721 / 12525 -
        (Real.log x ^ 2 - 15721 / 12525 * Real.log x + 4829141 / 1252500)) / x ^ 2) x := by
    intro x hx
    have hlog := Real.hasDerivAt_log hx.ne'
    convert (((hlog.pow 2).sub (hlog.const_mul (15721 / 12525))).add_const
      (4829141 / 1252500)).div (hasDerivAt_id' x) hx.ne' using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, Pi.sub_apply]
    field_simp
  refine antitoneOn_of_deriv_nonpos (convex_Ici 500) ?_ ?_ ?_
  · exact fun x hx ↦
      (hderiv x (by linarith [mem_Ici.1 hx])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hderiv x (by linarith [mem_Ioi.1 hx])).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := by linarith [mem_Ioi.1 hx]
    have hlog : 0 < Real.log x := Real.log_pos (by linarith [mem_Ioi.1 hx])
    rw [(hderiv x hx0).deriv]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg x)
    nlinarith [sq_nonneg (Real.log x - 163 / 100)]

/-- For `500 ≤ d`, the error term `q (log d) / d` is at most `q (311 / 50) / 500`. -/
private theorem errorQuadratic_log_div_le {d : ℕ} (hd : 500 ≤ d) :
    (Real.log d ^ 2 - 15721 / 12525 * Real.log d + 4829141 / 1252500) / d ≤
      ((311 / 50 : ℝ) ^ 2 - 15721 / 12525 * (311 / 50) + 4829141 / 1252500) / 500 := by
  have hdR : (500 : ℝ) ≤ d := by exact_mod_cast hd
  have hanti := antitoneOn_errorQuadratic_log_div (mem_Ici.2 le_rfl) (mem_Ici.2 hdR) hdR
  have hlog500 : (0 : ℝ) < Real.log 500 := Real.log_pos (by norm_num)
  have hu := log_five_hundred_lt
  refine hanti.trans (div_le_div_of_nonneg_right ?_ (by norm_num))
  nlinarith

/-- The numerical core of the lower-tail estimate: with `D = d`, `H = harmonic d`,
`Q = ∑ i < d, 1 / (i + 1) ^ 2`, `L = log d` and `A = log 6`, the exact average of
`(A + L - D * ∑ i, u i) ^ 2` exceeds `(121 / 100) ^ 2 + 41 / 25` minus an error term. -/
private theorem lt_affine_moment_of_bounds
    {D H Q L A : ℝ} (hD : 500 ≤ D) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hHupper : H - L < 29 / 50) (hQ : 41 / 25 < Q) (hA : 179 / 100 < A) :
    (121 / 100 : ℝ) ^ 2 + 41 / 25 -
        ((L + 29 / 50) ^ 2 -
          2 * (121 / 100) * (500 / 501) * (L + 29 / 50) +
          3 * (41 / 25)) / D <
      (A + L) ^ 2 - 2 * (A + L) * D * (H / (D + 1)) +
        D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) := by
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D + 1 := by linarith
  have hD2 : 0 < D + 2 := by linarith
  have ht : 0 < L + 29 / 50 := by linarith
  have hHu : H < L + 29 / 50 := by linarith
  have hres : (121 / 100 : ℝ) + (L + 29 / 50) / (D + 1) <
      A + L - D * H / (D + 1) := by
    field_simp
    nlinarith
  have hratio : (500 / 501 : ℝ) * (L + 29 / 50) / D ≤
      (L + 29 / 50) / (D + 1) := by
    field_simp
    nlinarith
  have hbias : (121 / 100 : ℝ) ^ 2 +
      2 * (121 / 100) * (500 / 501) * (L + 29 / 50) / D <
        (A + L - D * H / (D + 1)) ^ 2 := by
    have hres' : (121 / 100 : ℝ) + (500 / 501) * (L + 29 / 50) / D <
        A + L - D * H / (D + 1) := by linarith
    have hleft : 0 ≤ (121 / 100 : ℝ) + (500 / 501) * (L + 29 / 50) / D := by positivity
    have hsquares := (sq_lt_sq₀ hleft (hleft.trans_lt hres').le).2 hres'
    calc
      (121 / 100 : ℝ) ^ 2 + 2 * (121 / 100) * (500 / 501) * (L + 29 / 50) / D ≤
          (121 / 100 + (500 / 501) * (L + 29 / 50) / D) ^ 2 := by
        have hr := sq_nonneg ((500 / 501) * (L + 29 / 50) / D)
        have hexp : (121 / 100 + (500 / 501) * (L + 29 / 50) / D) ^ 2 =
            (121 / 100 : ℝ) ^ 2 + 2 * (121 / 100) * (500 / 501) * (L + 29 / 50) / D +
              ((500 / 501) * (L + 29 / 50) / D) ^ 2 := by ring
        linarith
      _ < (A + L - D * H / (D + 1)) ^ 2 := hsquares
  have hcoefQ : 1 - 3 / D < D ^ 2 / ((D + 1) * (D + 2)) := by
    field_simp
    nlinarith
  have hcoefH : D ^ 2 / ((D + 1) ^ 2 * (D + 2)) ≤ 1 / D := by
    field_simp
    nlinarith
  have hvcoef : (41 / 25 : ℝ) * (1 - 3 / D) < Q * (D ^ 2 / ((D + 1) * (D + 2))) := by
    have hone : 0 < 1 - 3 / D := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hD0).2
      linarith
    nlinarith
  have hHsq : H ^ 2 < (L + 29 / 50) ^ 2 := by nlinarith
  have hHterm : D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) ≤ (L + 29 / 50) ^ 2 / D := by
    have hcoefH0 : 0 ≤ D ^ 2 / ((D + 1) ^ 2 * (D + 2)) := by positivity
    calc
      D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) = (D ^ 2 / ((D + 1) ^ 2 * (D + 2))) * H ^ 2 := by
        ring
      _ ≤ (D ^ 2 / ((D + 1) ^ 2 * (D + 2))) * (L + 29 / 50) ^ 2 :=
        mul_le_mul_of_nonneg_left hHsq.le hcoefH0
      _ ≤ (1 / D) * (L + 29 / 50) ^ 2 := mul_le_mul_of_nonneg_right hcoefH (sq_nonneg _)
      _ = (L + 29 / 50) ^ 2 / D := by ring
  have hvariance : (41 / 25 : ℝ) * (1 - 3 / D) - (L + 29 / 50) ^ 2 / D <
      D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) - (D * H / (D + 1)) ^ 2 := by
    have hid : D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) - (D * H / (D + 1)) ^ 2 =
        Q * (D ^ 2 / ((D + 1) * (D + 2))) - D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) := by
      field_simp
      ring
    rw [hid]
    linarith
  have hdecomp :
      (A + L) ^ 2 - 2 * (A + L) * D * (H / (D + 1)) +
          D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) =
        (A + L - D * H / (D + 1)) ^ 2 +
          (D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) - (D * H / (D + 1)) ^ 2) := by ring
  rw [hdecomp]
  ring_nf at hbias hvariance ⊢
  nlinarith

/-! ### Moments on the weighted simplex -/

/-- The average of a square of an affine function of the coordinate sum on the weighted simplex
with weights `1, …, n`: for `0 < W` and all `a b`, with `H = harmonic n` and
`Q = ∑ i < n, 1 / (i + 1) ^ 2`,
`⨍ u in weightedSimplex (i + 1) W, (a - b * ∑ i, u i) ^ 2 =
  a ^ 2 - 2 * a * b * (W * H / (n + 1)) + b ^ 2 * (W ^ 2 * (H ^ 2 + Q) / ((n + 1) * (n + 2)))`. -/
theorem setAverage_weightedSimplex_succ_sub_mul_sum_sq (n : ℕ) {W : ℝ} (hW : 0 < W) (a b : ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, (a - b * ∑ i, u i) ^ 2 =
      a ^ 2 - 2 * a * b * (W * harmonic n / (n + 1)) +
        b ^ 2 * (W ^ 2 * ((harmonic n : ℝ) ^ 2 + ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) /
          ((n + 1) * (n + 2))) := by
  have hw : ∀ i : Fin n, 0 < (i : ℝ) + 1 := fun i ↦ by positivity
  have hI : ∀ f : (Fin n → ℝ) → ℝ, Continuous f →
      IntegrableOn f (weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W) :=
    fun f hf ↦ hf.continuousOn.integrableOn_weightedSimplex hw
  have hvol : volume (weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W) ≠ 0 := by
    rw [volume_weightedSimplex hw hW.le, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have hprod : 0 < ∏ i : Fin n, ((i : ℝ) + 1) := prod_pos fun i _ ↦ hw i
    positivity
  have he : (fun u : Fin n → ℝ ↦ (a - b * ∑ i, u i) ^ 2) =
      fun u ↦ (a ^ 2 - (2 * a * b) * ∑ i, u i) + b ^ 2 * (∑ i, u i) ^ 2 := by
    funext u
    ring
  rw [he, setAverage_fun_add (hI _ (by fun_prop)) (hI _ (by fun_prop)),
    setAverage_fun_sub (hI _ continuous_const) (hI _ (by fun_prop)), average_const_mul,
    average_const_mul, setAverage_const hvol (volume_weightedSimplex_lt_top hw W).ne,
    setAverage_weightedSimplex_succ_sum n hW, setAverage_weightedSimplex_succ_sum_sq n hW,
    harmonic_eq_sum_fin]

/-- The squared upper tail of the coordinate sum above `log 6`: for every `d`,
`⨍ u in weightedSimplex (i + 1) 1, max (d * ∑ i, u i - log d - log 6) 0 ^ 2 ≤ 1 / 3`.
For `d = 0` the integrand is `0`. -/
theorem setAverage_weightedSimplex_succ_upperTail_sq_le (d : ℕ) :
    ⨍ u in weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) 1,
      max (d * ∑ i, u i - Real.log d - Real.log 6) 0 ^ 2 ≤ 1 / 3 := by
  rcases eq_or_ne d 0 with rfl | hd
  · have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
    simp only [Nat.cast_zero, zero_mul, Real.log_zero, sub_zero, zero_sub,
      max_eq_right (neg_nonpos.2 hlog6.le)]
    norm_num
  have : NeZero d := ⟨hd⟩
  have hlaw := setAverage_standardSimplex_comp_sup' (n := d) 1
    fun m ↦ max (d * m - Real.log d - Real.log 6) 0 ^ 2
  beta_reduce at hlaw
  rw [← hlaw]
  refine (setAverage_standardSimplex_one_max_mul_sup'_sub_log_sub_sq_le _).trans_eq ?_
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- The squared lower tail at budget `1`, in the form `max (log 6 + log d - d * ∑ i, u i) 0`. -/
private theorem lowerTail_sq_gt_of_budget_one {d : ℕ} (hd : 500 ≤ d) :
    (27 / 10 : ℝ) < ⨍ u in weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) 1,
      max (Real.log 6 + Real.log d - d * ∑ i, u i) 0 ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hw : ∀ i : Fin d, 0 < (i : ℝ) + 1 := fun i ↦ by positivity
  have hI : ∀ f : (Fin d → ℝ) → ℝ, Continuous f →
      IntegrableOn f (weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) 1) :=
    fun f hf ↦ hf.continuousOn.integrableOn_weightedSimplex hw
  have hsplit : (fun u : Fin d → ℝ ↦ max (Real.log 6 + Real.log d - d * ∑ i, u i) 0 ^ 2) =
      fun u ↦ (Real.log 6 + Real.log d - d * ∑ i, u i) ^ 2 -
        max (d * ∑ i, u i - Real.log d - Real.log 6) 0 ^ 2 := by
    funext u
    rcases le_total (d * ∑ i, u i - Real.log d - Real.log 6) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  rw [hsplit, setAverage_fun_sub (hI _ (by fun_prop)) (hI _ (by fun_prop)),
    setAverage_weightedSimplex_succ_sub_mul_sum_sq d one_pos]
  simp only [one_mul, one_pow]
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hharm : 0 ≤ (harmonic d : ℝ) := by
    rw [harmonic_eq_sum_fin]
    positivity
  have haffine := lt_affine_moment_of_bounds (D := (d : ℝ)) (H := (harmonic d : ℝ))
    (Q := ∑ i : Fin d, 1 / ((i : ℝ) + 1) ^ 2) (L := Real.log d) (A := Real.log 6)
    (by exact_mod_cast hd) hlog hharm (Real.harmonic_sub_log_lt (by omega))
    (Real.lt_sum_fin_one_div_add_one_sq (by omega)) log_six_gt
  have hq : ∀ x : ℝ, (x + 29 / 50) ^ 2 - 2 * (121 / 100) * (500 / 501) * (x + 29 / 50) +
      3 * (41 / 25) = x ^ 2 - 15721 / 12525 * x + 4829141 / 1252500 := fun x ↦ by ring
  rw [hq] at haffine
  have htail := setAverage_weightedSimplex_succ_upperTail_sq_le d
  have herror := errorQuadratic_log_div_le hd
  have hendpoint : (27 / 10 : ℝ) < (121 / 100) ^ 2 + 41 / 25 - 1 / 3 -
      ((311 / 50 : ℝ) ^ 2 - 15721 / 12525 * (311 / 50) + 4829141 / 1252500) / 500 := by
    norm_num
  linarith

/-- The squared lower tail of the coordinate sum on the weighted simplex with weights `1, …, d`:
for `500 ≤ d` and `0 < W`,
`27 / 10 < ⨍ u in weightedSimplex (i + 1) W, max (log (6 * d) - d * (∑ i, u i) / W) 0 ^ 2`. -/
theorem setAverage_weightedSimplex_succ_lowerTail_sq_gt {d : ℕ} (hd : 500 ≤ d) {W : ℝ}
    (hW : 0 < W) :
    (27 / 10 : ℝ) < ⨍ u in weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      max (Real.log (6 * d) - d * (∑ i, u i) / W) 0 ^ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hscale := setAverage_weightedSimplex_mul (fun i : Fin d ↦ (i : ℝ) + 1) hW 1
    fun u ↦ max (Real.log (6 * d) - d * (∑ i, u i) / W) 0 ^ 2
  beta_reduce at hscale
  rw [mul_one] at hscale
  have hfun : (fun u : Fin d → ℝ ↦
      max (Real.log (6 * d) - d * (∑ i, (W • u) i) / W) 0 ^ 2) =
      fun u ↦ max (Real.log 6 + Real.log d - d * ∑ i, u i) 0 ^ 2 := by
    funext u
    have hsum : (d : ℝ) * (∑ i, (W • u) i) / W = d * ∑ i, u i := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      field_simp
    rw [hsum, Real.log_mul (by norm_num) hdpos.ne']
  rw [hscale, hfun]
  exact lowerTail_sq_gt_of_budget_one hd

end ReedSolomon.HiddenDerivative.RatePartition
