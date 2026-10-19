/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.WeightedVolume
public import ArkLib.ToMathlib.MvPolynomial.CompleteHomogeneous
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Probability.ConditionalProbability

/-!
# Moments of linear forms on simplices

For coefficients `c : ι → ℝ`, `n = Fintype.card ι`, and `0 ≤ L`, the `k`-th moment of the linear
form `∑ i, c i * x i` on the standard simplex is
`∫ x in standardSimplex ι L, (∑ i, c i * x i) ^ k = L ^ (n + k) * (k! / (n + k)!) * h_k(c)`,
where `h_k(c) = MvPolynomial.eval c (MvPolynomial.hsymm ι ℝ k)` is the complete homogeneous
symmetric polynomial of degree `k` evaluated at `c`. The proof expands the power with the
multinomial theorem `Finset.sum_pow_eq_sum_piAntidiag` and evaluates each monomial with the
Dirichlet integral `integral_standardSimplex_prod_pow_mul_pow`; the multinomial coefficient and
the factorials `∏ i, (a i)!` from the Dirichlet integral multiply to `k!`.

For positive weights `w`, the substitution `setIntegral_weightedSimplex` turns the same moment on
`weightedSimplex w W` into the standard moment with coefficients `c i / w i`, times
`(∏ i, w i)⁻¹`. Dividing by the volumes gives the normalized moments (set averages):
`⨍ x in standardSimplex ι L, (∑ i, c i * x i) ^ k = L ^ k * h_k(c) / (n + k).choose k` for
`0 < L`, and the same with `W` and `c i / w i` on the weighted simplex. In degrees `1`, `2`, `3`
the Newton identities `MvPolynomial.two_mul_eval_hsymm_two` and
`MvPolynomial.six_mul_eval_hsymm_three` give the averages in terms of power sums of `c i / w i`.
With weights `1, …, n` and `c = 1` these are the moments of the coordinate sum `∑ i, u i`, with
the harmonic power sums `∑ i, 1 / (i + 1) ^ q`.

The set average `⨍ x in s, f x` is the integral against the conditional measure `volume[|s]`
(Mathlib's `setAverage_eq'`, since `μ[|s] = (μ s)⁻¹ • μ.restrict s`). On a weighted simplex
with a positive budget this is a probability measure
(`isProbabilityMeasure_cond_weightedSimplex`).

Hypotheses. The integral formulas need `0 ≤ L` (for `L < 0` the simplex is empty) and positive
weights (otherwise the weighted simplex is unbounded). The averages need `0 < L`: for `L = 0` and
`n ≥ 1` the simplex is a null set, so the average is `0`, while the formula gives `1` for `k = 0`.

## Main statements

* `MeasureTheory.integral_standardSimplex_linearForm_pow` and
  `MeasureTheory.integral_weightedSimplex_linearForm_pow`: the `k`-th moments.
* `MeasureTheory.setAverage_standardSimplex_linearForm_pow` and
  `MeasureTheory.setAverage_weightedSimplex_linearForm_pow`: the normalized `k`-th moments.
* `MeasureTheory.setAverage_weightedSimplex_linearForm`,
  `MeasureTheory.setAverage_weightedSimplex_linearForm_sq`,
  `MeasureTheory.setAverage_weightedSimplex_linearForm_cube`: power-sum forms in degrees
  `1`, `2`, `3`.
* `MeasureTheory.setAverage_weightedSimplex_succ_sum`, `..._sum_sq`, `..._sum_cube`: the moments
  of `∑ i, u i` on the weighted simplex with weights `1, …, n`.
* `MeasureTheory.isProbabilityMeasure_cond_weightedSimplex`: the uniform probability measure.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped BigOperators ProbabilityTheory

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- `(n + 2).choose 2 = (n + 1) * (n + 2) / 2`, cast to `ℝ`. -/
private theorem cast_choose_add_two (n : ℕ) :
    (((n + 2).choose 2 : ℕ) : ℝ) = (n + 1) * (n + 2) / 2 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- `(n + 3).choose 3 = (n + 1) * (n + 2) * (n + 3) / 6`, cast to `ℝ`. -/
private theorem cast_choose_add_three (n : ℕ) :
    (((n + 3).choose 3 : ℕ) : ℝ) = (n + 1) * (n + 2) * (n + 3) / 6 := by
  rw [Nat.cast_choose ℝ (Nat.le_add_left 3 n), Nat.add_sub_cancel,
    show n + 3 = n + 2 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The `k`-th moment of a linear form on the standard simplex: for `n = Fintype.card ι` and
`0 ≤ L`,
`∫ x in standardSimplex ι L, (∑ i, c i * x i) ^ k = L ^ (n + k) * (k! / (n + k)!) * h_k(c)`,
where `h_k(c)` is the complete homogeneous symmetric polynomial of degree `k` evaluated at `c`.

The hypothesis `0 ≤ L` is needed: for `L < 0` the simplex is empty, so the left side is `0`,
while for `k = 0` the right side is `L ^ n / n!`, which is nonzero. -/
theorem integral_standardSimplex_linearForm_pow [DecidableEq ι] (c : ι → ℝ) (k : ℕ) {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ x in standardSimplex ι L, (∑ i, c i * x i) ^ k) =
      L ^ (Fintype.card ι + k) *
        ((k.factorial : ℝ) / (Fintype.card ι + k).factorial) *
          MvPolynomial.eval c (MvPolynomial.hsymm ι ℝ k) := by
  simp_rw [sum_pow_eq_sum_piAntidiag, MvPolynomial.eval_hsymm_eq_sum_piAntidiag, mul_sum]
  rw [integral_finsetSum _ fun a _ ↦
    (by fun_prop : Continuous fun x : ι → ℝ ↦
      (Nat.multinomial univ a : ℝ) * ∏ i, (c i * x i) ^ a i).continuousOn
      |>.integrableOn_standardSimplex]
  refine sum_congr rfl fun a ha ↦ ?_
  have hsum : ∑ i, a i = k := (mem_piAntidiag.1 ha).1
  have hD := integral_standardSimplex_prod_pow_mul_pow a 0 hL
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero, hsum] at hD
  have hspec : ((k.factorial : ℕ) : ℝ) =
      (∏ i, ((a i).factorial : ℝ)) * (Nat.multinomial univ a : ℝ) := by
    rw [← hsum]
    exact_mod_cast (Nat.multinomial_spec univ a).symm
  simp_rw [mul_pow, prod_mul_distrib, ← mul_assoc]
  rw [integral_const_mul, hD, hspec]
  ring

/-- The `k`-th moment of a linear form on a weighted simplex: for positive weights `w`,
`n = Fintype.card ι`, and `0 ≤ W`,
`∫ u in weightedSimplex w W, (∑ i, c i * u i) ^ k =
  (∏ i, w i)⁻¹ * (W ^ (n + k) * (k! / (n + k)!) * h_k(c / w))`,
where `h_k(c / w)` is the complete homogeneous symmetric polynomial of degree `k` evaluated at
`fun i ↦ c i / w i`. The substitution `u i = t i / w i` turns the linear form into
`∑ i, (c i / w i) * t i` on the standard simplex.

Positive weights are needed for the substitution; `0 ≤ W` is needed as in
`integral_standardSimplex_linearForm_pow`. -/
theorem integral_weightedSimplex_linearForm_pow [DecidableEq ι] {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (c : ι → ℝ) (k : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ u in weightedSimplex w W, (∑ i, c i * u i) ^ k) =
      (∏ i, w i)⁻¹ * (W ^ (Fintype.card ι + k) *
        ((k.factorial : ℝ) / (Fintype.card ι + k).factorial) *
          MvPolynomial.eval (fun i ↦ c i / w i) (MvPolynomial.hsymm ι ℝ k)) := by
  rw [setIntegral_weightedSimplex hw, ← integral_standardSimplex_linearForm_pow _ _ hW]
  congr 2
  funext t
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- The normalized `k`-th moment of a linear form on the standard simplex: for
`n = Fintype.card ι` and `0 < L`,
`⨍ x in standardSimplex ι L, (∑ i, c i * x i) ^ k = L ^ k * h_k(c) / (n + k).choose k`.

The hypothesis `0 < L` is needed: for `L = 0` and `n ≥ 1` the simplex is a null set, so the
average is `0`, while for `k = 0` the right side is `1`. -/
theorem setAverage_standardSimplex_linearForm_pow [DecidableEq ι] (c : ι → ℝ) (k : ℕ) {L : ℝ}
    (hL : 0 < L) :
    ⨍ x in standardSimplex ι L, (∑ i, c i * x i) ^ k =
      L ^ k * MvPolynomial.eval c (MvPolynomial.hsymm ι ℝ k) /
        (Fintype.card ι + k).choose k := by
  rw [setAverage_eq, volume_real_standardSimplex ι hL.le,
    integral_standardSimplex_linearForm_pow c k hL.le, smul_eq_mul,
    Nat.cast_choose ℝ (Nat.le_add_left k _), Nat.add_sub_cancel]
  have hn : ((Fintype.card ι).factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hnk : ((Fintype.card ι + k).factorial : ℝ) ≠ 0 := by positivity
  have hL' : L ≠ 0 := hL.ne'
  field_simp
  ring

/-- The normalized `k`-th moment of a linear form on a weighted simplex: for positive weights
`w`, `n = Fintype.card ι`, and `0 < W`,
`⨍ u in weightedSimplex w W, (∑ i, c i * u i) ^ k = W ^ k * h_k(c / w) / (n + k).choose k`.
The Jacobian `(∏ i, w i)⁻¹` cancels against the same factor in the volume.

Positive weights are needed for the substitution, and `0 < W` for the reason given in
`setAverage_standardSimplex_linearForm_pow`. -/
theorem setAverage_weightedSimplex_linearForm_pow [DecidableEq ι] {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (c : ι → ℝ) (k : ℕ) {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex w W, (∑ i, c i * u i) ^ k =
      W ^ k * MvPolynomial.eval (fun i ↦ c i / w i) (MvPolynomial.hsymm ι ℝ k) /
        (Fintype.card ι + k).choose k := by
  rw [setAverage_eq, volume_real_weightedSimplex hw hW.le,
    integral_weightedSimplex_linearForm_pow hw c k hW.le, smul_eq_mul,
    Nat.cast_choose ℝ (Nat.le_add_left k _), Nat.add_sub_cancel]
  have hn : ((Fintype.card ι).factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hnk : ((Fintype.card ι + k).factorial : ℝ) ≠ 0 := by positivity
  have hprod : ∏ i, w i ≠ 0 := (prod_pos fun i _ ↦ hw i).ne'
  have hW' : W ≠ 0 := hW.ne'
  field_simp
  ring

/-- The mean of a linear form on a weighted simplex: for positive weights, `n = Fintype.card ι`,
and `0 < W`, `⨍ u in weightedSimplex w W, ∑ i, c i * u i = W * (∑ i, c i / w i) / (n + 1)`.
The hypotheses are needed as in `setAverage_weightedSimplex_linearForm_pow`. -/
theorem setAverage_weightedSimplex_linearForm {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → ℝ)
    {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex w W, ∑ i, c i * u i =
      W * (∑ i, c i / w i) / (Fintype.card ι + 1) := by
  classical
  have h := setAverage_weightedSimplex_linearForm_pow hw c 1 hW
  simp only [pow_one, MvPolynomial.hsymm_one, map_sum, MvPolynomial.eval_X,
    Nat.choose_one_right] at h
  rw [h]
  push_cast
  ring

/-- The second moment of a linear form on a weighted simplex, in power-sum form: for positive
weights, `n = Fintype.card ι`, and `0 < W`,
`⨍ u in weightedSimplex w W, (∑ i, c i * u i) ^ 2 =
  W ^ 2 * ((∑ i, c i / w i) ^ 2 + ∑ i, (c i / w i) ^ 2) / ((n + 1) * (n + 2))`.
The hypotheses are needed as in `setAverage_weightedSimplex_linearForm_pow`. -/
theorem setAverage_weightedSimplex_linearForm_sq {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → ℝ)
    {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex w W, (∑ i, c i * u i) ^ 2 =
      W ^ 2 * ((∑ i, c i / w i) ^ 2 + ∑ i, (c i / w i) ^ 2) /
        ((Fintype.card ι + 1) * (Fintype.card ι + 2)) := by
  classical
  rw [setAverage_weightedSimplex_linearForm_pow hw c 2 hW, cast_choose_add_two,
    ← MvPolynomial.two_mul_eval_hsymm_two]
  field_simp

/-- The third moment of a linear form on a weighted simplex, in power-sum form: for positive
weights, `n = Fintype.card ι`, `0 < W`, and `p q = ∑ i, (c i / w i) ^ q`,
`⨍ u in weightedSimplex w W, (∑ i, c i * u i) ^ 3 =
  W ^ 3 * (p 1 ^ 3 + 3 * p 1 * p 2 + 2 * p 3) / ((n + 1) * (n + 2) * (n + 3))`.
The hypotheses are needed as in `setAverage_weightedSimplex_linearForm_pow`. -/
theorem setAverage_weightedSimplex_linearForm_cube {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → ℝ)
    {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex w W, (∑ i, c i * u i) ^ 3 =
      W ^ 3 * ((∑ i, c i / w i) ^ 3 + 3 * (∑ i, c i / w i) * (∑ i, (c i / w i) ^ 2) +
        2 * ∑ i, (c i / w i) ^ 3) /
          ((Fintype.card ι + 1) * (Fintype.card ι + 2) * (Fintype.card ι + 3)) := by
  classical
  rw [setAverage_weightedSimplex_linearForm_pow hw c 3 hW, cast_choose_add_three,
    ← MvPolynomial.six_mul_eval_hsymm_three]
  field_simp

/-- The weighted simplex with positive weights and a positive budget has finite positive volume,
so the conditional measure `volume[|weightedSimplex w W]` is the uniform probability measure on it.
The budget must be positive: for `W = 0` and a nonempty index type the simplex is a null set. -/
theorem isProbabilityMeasure_cond_weightedSimplex {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ}
    (hW : 0 < W) : IsProbabilityMeasure (volume[|weightedSimplex w W]) := by
  refine ProbabilityTheory.cond_isProbabilityMeasure_of_finite ?_
    (volume_weightedSimplex_lt_top hw W).ne
  rw [volume_weightedSimplex hw hW.le, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have hprod : 0 < ∏ i, w i := prod_pos fun i _ ↦ hw i
  positivity

/-! ### Weights `1, …, n` and the coordinate sum -/

/-- The mean of the coordinate sum `∑ i, u i` on the weighted simplex with weights `1, …, n`:
`W * H_n / (n + 1)` for `0 < W`, where `H_n` is the harmonic number. -/
theorem setAverage_weightedSimplex_succ_sum (n : ℕ) {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, ∑ i, u i =
      W * (harmonic n : ℝ) / (n + 1) := by
  have h := setAverage_weightedSimplex_linearForm
    (w := fun i : Fin n ↦ (i : ℝ) + 1) (fun i ↦ by positivity) 1 hW
  simp only [Pi.one_apply, one_mul, Fintype.card_fin] at h
  rw [h, harmonic, Rat.cast_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1)) n]
  push_cast
  simp [one_div]

/-- The second moment of the coordinate sum on the weighted simplex with weights `1, …, n`, for
`0 < W`, in terms of the harmonic power sums `∑ i, 1 / (i + 1) ^ q`. -/
theorem setAverage_weightedSimplex_succ_sum_sq (n : ℕ) {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, (∑ i, u i) ^ 2 =
      W ^ 2 * ((∑ i : Fin n, 1 / ((i : ℝ) + 1)) ^ 2 + ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) /
        ((n + 1) * (n + 2)) := by
  have h := setAverage_weightedSimplex_linearForm_sq
    (w := fun i : Fin n ↦ (i : ℝ) + 1) (fun i ↦ by positivity) 1 hW
  simp only [Pi.one_apply, one_mul, Fintype.card_fin, div_pow, one_pow] at h
  exact h

/-- The third moment of the coordinate sum on the weighted simplex with weights `1, …, n`, for
`0 < W`, in terms of the harmonic power sums `p q = ∑ i, 1 / (i + 1) ^ q`. -/
theorem setAverage_weightedSimplex_succ_sum_cube (n : ℕ) {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, (∑ i, u i) ^ 3 =
      W ^ 3 * ((∑ i : Fin n, 1 / ((i : ℝ) + 1)) ^ 3 +
        3 * (∑ i : Fin n, 1 / ((i : ℝ) + 1)) * (∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) +
          2 * ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 3) /
        ((n + 1) * (n + 2) * (n + 3)) := by
  have h := setAverage_weightedSimplex_linearForm_cube
    (w := fun i : Fin n ↦ (i : ℝ) + 1) (fun i ↦ by positivity) 1 hW
  simp only [Pi.one_apply, one_mul, Fintype.card_fin, div_pow, one_pow] at h
  exact h

end MeasureTheory
