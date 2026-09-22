/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.CenteredMoments
public import ArkLib.ToMathlib.MeasureTheory.Integral.PositivePart
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.MomentBounds

/-!
# Centered radius moments and the cubic contribution

The hidden-derivative dimension estimate draws a point `u` uniformly from the weighted simplex
`weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W` and looks at its radius `∑ i, u i`. The radius
has mean `W * H / (n + 1)`, where `H = harmonic n`. The normalized radius
`normalizedRadius W t u = (∑ i, u i - W * H / (n + 1)) / t` centers it and divides by a scale
`t`. With `s = W / ((n + 1) * t)`, `H₂ = ∑ i : Fin n, 1 / (i + 1) ^ 2` and
`H₃ = ∑ i : Fin n, 1 / (i + 1) ^ 3`, its first three moments are
`0`, `s ^ 2 * (n + 1) / (n + 2) * (H₂ - H ^ 2 / (n + 1))` and
`2 * s ^ 3 * ((n + 1) ^ 2 * H₃ - 3 * (n + 1) * H * H₂ + 2 * H ^ 3) / ((n + 2) * (n + 3))`.
These are the centered moments `setAverage_weightedSimplex_linearForm_sub_mean{,_sq,_cube}` for
the weights `1, …, n` and coefficients `1`, divided by `t`, `t ^ 2`, `t ^ 3`.

The cubic contribution bound `normalizedRadius_contribution_lower` is
`(5 / 8) ^ 3 + (4147 / 2160) * s ^ 2 ≤ ⨍ u, (max (5 / 8 - normalizedRadius W t u) 0) ^ 3`.
It combines three facts. `MeasureTheory.le_integral_max_sub_zero_pow_three` bounds the right
side below by `(5 / 8) ^ 3 + 3 * (5 / 8) * E[z ^ 2] - E[z ^ 3]` for the mean-zero `z`. The
moment factors of `MomentBounds.lean` give `E[z ^ 2] > 3 / 2 * s ^ 2` and
`E[z ^ 3] ≤ 241 / 100 * s ^ 3` from bounds on `H`, `H₂`, `H₃`. Finally
`cubic_contribution_numeric` turns these into the stated constant for `s ≤ 10 / 27`; that
threshold is sharp for the numeric step, since `3 * (5 / 8) * (3 / 2) - 4147 / 2160 = 241 / 270`
and `241 / 270 = 241 / 100 * (10 / 27)`.

## Main statements

* `ReedSolomon.HiddenDerivative.normalizedRadius` and `continuous_normalizedRadius`.
* `ReedSolomon.HiddenDerivative.setAverage_normalizedRadius`,
  `setAverage_normalizedRadius_sq`, `setAverage_normalizedRadius_cube`: the three moments.
* `ReedSolomon.HiddenDerivative.cubic_contribution_numeric` and
  `contribution_integral_lower`: the cubic bound for any mean-zero variable under a probability
  measure, given the two moment estimates.
* `ReedSolomon.HiddenDerivative.normalizedRadius_contribution_lower`: the bound for the
  normalized radius.

## References

Ports declarations of `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`WeightedSupport/` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

* `Moments.lean`. The source's probability measure `weightedSimplexProbabilityMeasure n W` is
  the conditional measure `volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W]`, whose
  integrals are set averages (Mathlib's `setAverage_eq'`); the moments are stated as set
  averages. `normalizedRadius` is the source's definition with `weightedRadius u` written as
  `∑ i, u i` and `harmonicPowerSum n 1` as `harmonic n`; `continuous_normalizedRadius` is the
  source's. `integral_normalizedRadius`, `integral_normalizedRadius_sq` and
  `integral_normalizedRadius_cube` become `setAverage_normalizedRadius`, `_sq`, `_cube`,
  specializations of the general centered moments in
  `ArkLib.ToMathlib.Analysis.Simplex.CenteredMoments`. The budget hypothesis `0 < W` is dropped
  for the mean and weakened to `0 ≤ W` for the other two, and `t` is arbitrary (for `t = 0` both
  sides are `0`). `integrable_weighted_probability` is `MeasureTheory.IntegrableOn.integrable_cond`
  composed with `ContinuousOn.integrableOn_weightedSimplex`.
* `Cubic.lean`. `cubic_numeric` and `contribution_integral_lower` (namespace
  `WeightedSupportParameters`) become `cubic_contribution_numeric` and
  `contribution_integral_lower` here, and `positive_cube_moments` with `cubic_le_positive_cube`
  is `MeasureTheory.le_integral_max_sub_zero_pow_three`. The integrability hypotheses for `z ^ 2`
  and for the positive-part cube are dropped because they follow from those of `z` and `z ^ 3`.
* `Estimate.lean`. `normalizedRadius_contribution_lower` drops the hypothesis
  `48000 ≤ n + 1`: `150 < n + 1`, which the moment factor `weightedSupport_variance_factor_gt`
  needs, already follows from the harmonic hypotheses, and the third-moment factor needs only
  `1 ≤ n + 1`. The hypothesis `0 < t` is weakened to `0 ≤ t`.

The source's `weighted_dimension_probability` is in `WeightedSupport/Estimate.lean`.
Deferred: `weighted_dimension_lower` of `Estimate.lean` (it needs the harmonic-number
estimates), `Margin.lean`, `RankIntegral.lean`, `NormalizedRank.lean`,
and `positive_cube_tangent`, `positive_cube_jensen`, `positive_cube_convex` of `Cubic.lean`,
which have no consumer yet.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped BigOperators ProbabilityTheory

namespace ReedSolomon.HiddenDerivative

/-- The radius `∑ i, u i` of a point `u` of the weighted simplex with weights `1, …, n` and budget
`W`, centered at its mean `W * harmonic n / (n + 1)` and divided by the scale `t`. -/
noncomputable def normalizedRadius {n : ℕ} (W t : ℝ) (u : Fin n → ℝ) : ℝ :=
  (∑ i, u i - W * (harmonic n : ℝ) / (n + 1)) / t

/-- The normalized radius is continuous in `u`. -/
theorem continuous_normalizedRadius (n : ℕ) (W t : ℝ) :
    Continuous (normalizedRadius (n := n) W t) := by
  unfold normalizedRadius
  fun_prop

/-- The harmonic number as a sum over `Fin n`. -/
private theorem harmonic_eq_sum_fin (n : ℕ) :
    (harmonic n : ℝ) = ∑ i : Fin n, 1 / ((i : ℝ) + 1) := by
  rw [harmonic, Rat.cast_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1)) n]
  push_cast
  simp [one_div]

/-- The weights `1, …, n` are positive. -/
private theorem succ_weight_pos (n : ℕ) (i : Fin n) : (0 : ℝ) < (i : ℝ) + 1 := by positivity

/-- The normalized radius has mean `0` on the weighted simplex with weights `1, …, n`. No
hypothesis on `W` or `t` is needed: for `W ≤ 0` the centered radius vanishes on the simplex, and
for `t = 0` the normalized radius is `0`. -/
theorem setAverage_normalizedRadius (n : ℕ) (W t : ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, normalizedRadius W t u = 0 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean (succ_weight_pos n) 1 W
  simp only [Pi.one_apply, one_mul, Fintype.card_fin, ← harmonic_eq_sum_fin] at h
  simp_rw [normalizedRadius, div_eq_mul_inv]
  rw [average_mul_const]
  simp only [← div_eq_mul_inv] at h ⊢
  rw [h, zero_div]

/-- The second moment of the normalized radius on the weighted simplex with weights `1, …, n`:
with `H = harmonic n` and `H₂ = ∑ i : Fin n, 1 / (i + 1) ^ 2`,
`⨍ u, normalizedRadius W t u ^ 2 =
  (W / ((n + 1) * t)) ^ 2 * (n + 1) / (n + 2) * (H₂ - H ^ 2 / (n + 1))`.

The hypothesis `0 ≤ W` is needed: for `W < 0` the simplex is empty and the left side is `0`,
while for `n = 1` and `t = 1` the right side is `W ^ 2 / 12`. -/
theorem setAverage_normalizedRadius_sq (n : ℕ) {W : ℝ} (hW : 0 ≤ W) (t : ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, normalizedRadius W t u ^ 2 =
      (W / ((n + 1) * t)) ^ 2 * (n + 1) / (n + 2) *
        (∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2 - (harmonic n : ℝ) ^ 2 / (n + 1)) := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_sq (succ_weight_pos n) 1 hW
  simp only [Pi.one_apply, one_mul, Fintype.card_fin, div_pow, one_pow,
    ← harmonic_eq_sum_fin] at h
  simp_rw [normalizedRadius, div_pow]
  simp_rw [div_eq_mul_inv _ (t ^ 2)]
  rw [average_mul_const]
  simp only [← div_eq_mul_inv] at h ⊢
  rw [h]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  field_simp

/-- The third moment of the normalized radius on the weighted simplex with weights `1, …, n`:
with `H = harmonic n`, `H₂ = ∑ i : Fin n, 1 / (i + 1) ^ 2` and `H₃ = ∑ i : Fin n, 1 / (i + 1) ^ 3`,
`⨍ u, normalizedRadius W t u ^ 3 =
  2 * (W / ((n + 1) * t)) ^ 3 * ((n + 1) ^ 2 * H₃ - 3 * (n + 1) * H * H₂ + 2 * H ^ 3) /
    ((n + 2) * (n + 3))`.
No fourth moment is needed. The hypothesis `0 ≤ W` plays the same role as in
`setAverage_normalizedRadius_sq`. -/
theorem setAverage_normalizedRadius_cube (n : ℕ) {W : ℝ} (hW : 0 ≤ W) (t : ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, normalizedRadius W t u ^ 3 =
      2 * (W / ((n + 1) * t)) ^ 3 *
        ((n + 1) ^ 2 * ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 3 -
          3 * (n + 1) * (harmonic n : ℝ) * ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2 +
          2 * (harmonic n : ℝ) ^ 3) / ((n + 2) * (n + 3)) := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_cube (succ_weight_pos n) 1 hW
  simp only [Pi.one_apply, one_mul, Fintype.card_fin, div_pow, one_pow,
    ← harmonic_eq_sum_fin] at h
  simp_rw [normalizedRadius, div_pow]
  simp_rw [div_eq_mul_inv _ (t ^ 3)]
  rw [average_mul_const]
  simp only [← div_eq_mul_inv] at h ⊢
  rw [h]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  field_simp

/-- The numeric step of the cubic contribution: if `s ≤ 10 / 27`, `3 / 2 * s ^ 2 ≤ v₂` and
`v₃ ≤ 241 / 100 * s ^ 3`, then
`(5 / 8) ^ 3 + (4147 / 2160) * s ^ 2 ≤ (5 / 8) ^ 3 + 3 * (5 / 8) * v₂ - v₃`.
The difference of the two sides is at least `241 / 100 * s ^ 2 * (10 / 27 - s)`, so the threshold
`10 / 27` is sharp: for `s > 10 / 27` the bound fails at `v₂ = 3 / 2 * s ^ 2` and
`v₃ = 241 / 100 * s ^ 3`. -/
theorem cubic_contribution_numeric (s v₂ v₃ : ℝ) (hs : s ≤ 10 / 27)
    (h₂ : 3 / 2 * s ^ 2 ≤ v₂) (h₃ : v₃ ≤ 241 / 100 * s ^ 3) :
    (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2 ≤ (5 / 8 : ℝ) ^ 3 + 3 * (5 / 8) * v₂ - v₃ := by
  have hp := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs)
  nlinarith

/-- The cubic contribution for a mean-zero variable: for a probability measure `P` and `z` with
`∫ z ∂P = 0` such that `z` and `z ^ 3` are integrable, if `s ≤ 10 / 27`,
`3 / 2 * s ^ 2 ≤ ∫ z ^ 2 ∂P` and `∫ z ^ 3 ∂P ≤ 241 / 100 * s ^ 3`, then
`(5 / 8) ^ 3 + (4147 / 2160) * s ^ 2 ≤ ∫ (max (5 / 8 - z) 0) ^ 3 ∂P`.
The hypotheses are those of `cubic_contribution_numeric` and
`MeasureTheory.le_integral_max_sub_zero_pow_three`. -/
theorem contribution_integral_lower {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (z : X → ℝ) (s : ℝ) (hz : Integrable z P)
    (h3 : Integrable (fun x ↦ z x ^ 3) P) (hm : ∫ x, z x ∂P = 0) (hs : s ≤ 10 / 27)
    (hv₂ : 3 / 2 * s ^ 2 ≤ ∫ x, z x ^ 2 ∂P) (hv₃ : ∫ x, z x ^ 3 ∂P ≤ 241 / 100 * s ^ 3) :
    (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2 ≤ ∫ x, (max (5 / 8 - z x) 0) ^ 3 ∂P :=
  (cubic_contribution_numeric s _ _ hs hv₂ hv₃).trans
    (le_integral_max_sub_zero_pow_three P z (5 / 8) hz h3 hm)

/-- The integral against the conditional measure `μ[|s]` is the set average over `s`. -/
private theorem integral_cond_eq_setAverage {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Set α) (f : α → ℝ) : (∫ x, f x ∂μ[|s]) = ⨍ x in s, f x ∂μ :=
  (setAverage_eq' μ f s).symm

/-- If the square of the `n`-th harmonic number is at most `(n + 1) / 100` and
`38 / 25 ≤ ∑ i : Fin n, 1 / (i + 1) ^ 2`, then `n ≥ 224`; in particular `150 < n + 1`.
For `n = 0` the second sum is `0`, for `n = 1` the first hypothesis reads `1 ≤ 2 / 100`, and for
`n ≥ 2` the harmonic number is at least `3 / 2`. -/
private theorem lt_succ_of_harmonic_bounds {n : ℕ} (hHsq : (harmonic n : ℝ) ^ 2 ≤ (n + 1) / 100)
    (hH₂ : 38 / 25 ≤ ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) : (150 : ℝ) < n + 1 := by
  rcases n with _ | _ | k
  · simp at hH₂
    norm_num at hH₂
  · norm_num [harmonic] at hHsq
  · have hk : (3 / 2 : ℚ) ≤ harmonic (k + 2) := by
      rw [harmonic]
      calc (3 / 2 : ℚ) = ∑ i ∈ Finset.range 2, ((↑(i + 1) : ℚ))⁻¹ := by norm_num [sum_range_succ]
        _ ≤ ∑ i ∈ Finset.range (k + 2), ((↑(i + 1) : ℚ))⁻¹ :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
            fun _ _ _ ↦ by positivity
    have hkR : (3 / 2 : ℝ) ≤ harmonic (k + 2) := by
      have := (Rat.cast_le (K := ℝ)).2 hk
      push_cast at this
      exact this
    push_cast at hHsq ⊢
    nlinarith

/-- The cubic contribution of the normalized radius on the weighted simplex with weights
`1, …, n`: with `s = W / ((n + 1) * t)`, `H = harmonic n`, `H₂ = ∑ i : Fin n, 1 / (i + 1) ^ 2`
and `H₃ = ∑ i : Fin n, 1 / (i + 1) ^ 3`,
`(5 / 8) ^ 3 + (4147 / 2160) * s ^ 2 ≤ ⨍ u, (max (5 / 8 - normalizedRadius W t u) 0) ^ 3`,
provided `0 < W`, `0 ≤ t`, `H ^ 2 ≤ (n + 1) / 100`, `38 / 25 ≤ H₂`, `H₃ ≤ 12021 / 10000` and
`s ≤ 10 / 27`.

Role of the hypotheses. `0 < W` makes the uniform measure on the simplex a probability measure;
for `W = 0` and `n ≥ 1` the simplex is a null set and the average is `0`. `0 ≤ t` makes
`s ^ 3 ≥ 0`, which turns the bound on the third-moment factor into a bound on the third moment.
The bounds on `H` and `H₂` give the variance bound `weightedSupport_variance_factor_gt`, whose
dimension hypothesis `150 < n + 1` follows from them; the bounds on `H` and `H₃` give
`weightedSupport_third_factor_numeric`. The threshold `s ≤ 10 / 27` is the sharp threshold of
`cubic_contribution_numeric`. -/
theorem normalizedRadius_contribution_lower (n : ℕ) {W t : ℝ} (hW : 0 < W) (ht : 0 ≤ t)
    (hHsq : (harmonic n : ℝ) ^ 2 ≤ (n + 1) / 100)
    (hH₂ : 38 / 25 ≤ ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2)
    (hH₃ : ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 3 ≤ 12021 / 10000)
    (hs : W / ((n + 1) * t) ≤ 10 / 27) :
    (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (W / ((n + 1) * t)) ^ 2 ≤
      ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W,
        (max (5 / 8 - normalizedRadius W t u) 0) ^ 3 := by
  set S := weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W
  have : IsProbabilityMeasure (volume[|S]) :=
    isProbabilityMeasure_cond_weightedSimplex (succ_weight_pos n) hW
  have hc := continuous_normalizedRadius n W t
  have hI : ∀ f : (Fin n → ℝ) → ℝ, Continuous f → Integrable f (volume[|S]) :=
    fun f hf ↦ (hf.continuousOn.integrableOn_weightedSimplex (succ_weight_pos n)).integrable_cond
  have hH : (0 : ℝ) ≤ harmonic n := by
    rw [harmonic_eq_sum_fin]
    exact sum_nonneg fun i _ ↦ by positivity
  have hH₂0 : (0 : ℝ) ≤ ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2 := sum_nonneg fun i _ ↦ by positivity
  have hH₃0 : (0 : ℝ) ≤ ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 3 := sum_nonneg fun i _ ↦ by positivity
  have hs0 : 0 ≤ W / ((n + 1) * t) := by positivity
  rw [← integral_cond_eq_setAverage]
  refine contribution_integral_lower _ _ _ (hI _ hc) (hI _ (hc.pow 3)) ?_ hs ?_ ?_
  · rw [integral_cond_eq_setAverage, setAverage_normalizedRadius]
  · rw [integral_cond_eq_setAverage, setAverage_normalizedRadius_sq n hW.le]
    have hv := weightedSupport_variance_factor_gt (d := (n : ℝ) + 1)
      (lt_succ_of_harmonic_bounds hHsq hH₂) hHsq hH₂
    have hh := mul_le_mul_of_nonneg_left hv.le (sq_nonneg (W / ((n + 1) * t)))
    convert hh using 1 <;> ring
  · rw [integral_cond_eq_setAverage, setAverage_normalizedRadius_cube n hW.le]
    have ha := weightedSupport_third_factor_le (d := (n : ℝ) + 1) (by positivity) hH hH₂0 hH₃0
    have hb := weightedSupport_third_factor_numeric (d := (n : ℝ) + 1) (by linarith) hH hHsq hH₃
    have hh := mul_le_mul_of_nonneg_left (ha.trans hb) (pow_nonneg hs0 3)
    convert hh using 1 <;> ring

end ReedSolomon.HiddenDerivative
