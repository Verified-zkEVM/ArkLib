/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.Moments

/-!
# Centered moments of linear forms on weighted simplices

Let `w : ι → ℝ` be positive weights, `c : ι → ℝ` coefficients, `n = Fintype.card ι`, and write
`p q = ∑ i, (c i / w i) ^ q` for the power sums of the ratios `c i / w i`. On the weighted simplex
`weightedSimplex w W` with `0 < W`, the linear form `X u = ∑ i, c i * u i` has mean
`m = W * p 1 / (n + 1)` (`setAverage_weightedSimplex_linearForm`). This file computes the first
three moments of `X - m` under the uniform measure on the simplex:

* `⨍ (X - m) = 0`;
* `⨍ (X - m) ^ 2 = W ^ 2 * ((n + 1) * p 2 - p 1 ^ 2) / ((n + 1) ^ 2 * (n + 2))`;
* `⨍ (X - m) ^ 3 =
    2 * W ^ 3 * ((n + 1) ^ 2 * p 3 - 3 * (n + 1) * p 1 * p 2 + 2 * p 1 ^ 3) /
      ((n + 1) ^ 3 * (n + 2) * (n + 3))`.

Each follows from the raw moments `setAverage_weightedSimplex_linearForm{,_sq,_cube}` by
expanding the power of `X - m` and using linearity of the set average.

Budget hypotheses. For `W ≤ 0` every point `u` of the simplex satisfies `W = 0` and `u = 0`
(the simplex is empty for `W < 0` and equals `{0}` for `W = 0`), so `X - m` vanishes on it and
every average above is `0`. Hence the mean statement needs no hypothesis on `W`, and the second
and third moment statements need only `0 ≤ W`, because their right sides have the factor `W ^ 2`
or `W ^ 3`. For `W < 0` the second moment formula fails: with one coordinate and
`w = c = 1` the left side is `0` and the right side is `W ^ 2 / 12`.

Set averages are integrals against the conditional measure `volume[|weightedSimplex w W]`
(Mathlib's `setAverage_eq'`), which is a probability measure for `0 < W`
(`isProbabilityMeasure_cond_weightedSimplex`). `IntegrableOn.integrable_cond` transfers
integrability on a set to integrability under the conditional measure, so a function continuous
on the weighted simplex is integrable for that measure by
`ContinuousOn.integrableOn_weightedSimplex`.

## Main statements

* `MeasureTheory.IntegrableOn.integrable_cond`: integrability on `s` gives integrability under
  `μ[|s]`.
* `MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean`: the centered form has mean `0`.
* `MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean_sq`: the variance.
* `MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean_sq_le`: the variance is at most
  `W ^ 2 * p 2 / ((n + 1) * (n + 2))`, for every real `W`.
* `MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean_cube`: the third central moment.

## References

Generalizes the centered moments of `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/`
`Interpolation/WeightedSupport/Moments.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source's `integral_normalizedRadius`,
`integral_normalizedRadius_sq` and `integral_normalizedRadius_cube` state these moments for the
weights `1, …, n` and coefficients `1`, scaled by `1 / t`; here the weights and coefficients are
arbitrary, the index type is any `Fintype`, and the budget hypothesis is weakened from `0 < W`.
The source's `integrable_weighted_probability` is `IntegrableOn.integrable_cond` composed with
`ContinuousOn.integrableOn_weightedSimplex`. The hidden-derivative specializations are in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments`.

`setAverage_weightedSimplex_linearForm_sub_mean_sq_le` generalizes
`ReedSolomon.HiddenDerivative.weightedSimplex_centeredRadius_sq_le_harmonic` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at the same revision. The source states the case of weights `i + 1` on
`Fin n` and coefficients `1`; here the weights are arbitrary positive reals, the coefficients are
arbitrary, and there is no budget hypothesis. The specialization keeps the source name in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral`.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped BigOperators ProbabilityTheory ENNReal

namespace MeasureTheory

/-- A function integrable on `s` is integrable for the conditional measure
`μ[|s] = (μ s)⁻¹ • μ.restrict s`. No hypothesis on `μ s` is needed: if `μ s = 0` then
`μ.restrict s = 0`, and otherwise `(μ s)⁻¹` is finite. -/
theorem IntegrableOn.integrable_cond {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {f : α → E} (hf : IntegrableOn f s μ) :
    Integrable f μ[|s] := by
  by_cases hs : μ s = 0
  · simp [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 hs]
  · exact hf.smul_measure (ENNReal.inv_ne_top.2 hs)

variable {ι : Type*} [Fintype ι]

/-- For positive weights and `W ≤ 0`, a point of `weightedSimplex w W` forces `W = 0` and is the
zero vector: the terms `w i * u i` are nonnegative and sum to at most `W ≤ 0`. -/
private theorem eq_zero_of_mem_weightedSimplex_of_nonpos {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {W : ℝ} (hW : W ≤ 0) {u : ι → ℝ} (hu : u ∈ weightedSimplex w W) : W = 0 ∧ u = 0 := by
  obtain ⟨hnn, hsum⟩ := hu
  have hterm : ∀ i ∈ (univ : Finset ι), 0 ≤ w i * u i :=
    fun i _ ↦ mul_nonneg (hw i).le (hnn i)
  have h0 : ∑ i, w i * u i = 0 := le_antisymm (hsum.trans hW) (sum_nonneg hterm)
  refine ⟨le_antisymm hW (by linarith), funext fun i ↦ ?_⟩
  have hi := (sum_eq_zero_iff_of_nonneg hterm).1 h0 i (mem_univ i)
  exact (mul_eq_zero.1 hi).resolve_left (hw i).ne'

/-- For `W ≤ 0`, the average over `weightedSimplex w W` of a function that vanishes at `0` when
`W = 0` is `0`. -/
private theorem setAverage_weightedSimplex_of_nonpos {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ}
    (hW : W ≤ 0) (f : (ι → ℝ) → ℝ) (hf : W = 0 → f 0 = 0) :
    ⨍ u in weightedSimplex w W, f u = 0 := by
  rw [setAverage_congr_fun (g := fun _ ↦ (0 : ℝ)) (measurableSet_weightedSimplex w W)
    (ae_of_all _ fun u hu ↦ ?_)]
  · simp
  · obtain ⟨hW0, rfl⟩ := eq_zero_of_mem_weightedSimplex_of_nonpos hw hW hu
    exact hf hW0

/-- For positive weights and a positive budget, the weighted simplex has nonzero volume. -/
private theorem volume_weightedSimplex_ne_zero {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ}
    (hW : 0 < W) : volume (weightedSimplex w W) ≠ 0 := by
  rw [volume_weightedSimplex hw hW.le, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have hprod : 0 < ∏ i, w i := prod_pos fun i _ ↦ hw i
  positivity

/-- The average of a constant over the weighted simplex with a positive budget. -/
private theorem setAverage_weightedSimplex_const {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ}
    (hW : 0 < W) (a : ℝ) : ⨍ _u in weightedSimplex w W, a = a :=
  setAverage_const (volume_weightedSimplex_ne_zero hw hW) (volume_weightedSimplex_lt_top hw W).ne a

/-- The linear form `∑ i, c i * u i` centered at its mean `W * (∑ i, c i / w i) / (n + 1)` has
average `0` on the weighted simplex, for positive weights `w` and `n = Fintype.card ι`.

No hypothesis on `W` is needed: for `W ≤ 0` the simplex is empty or `{0}`, and the centered form
vanishes on it. Positive weights are needed for the mean formula. -/
theorem setAverage_weightedSimplex_linearForm_sub_mean {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (c : ι → ℝ) (W : ℝ) :
    ⨍ u in weightedSimplex w W,
      (∑ i, c i * u i - W * (∑ i, c i / w i) / (Fintype.card ι + 1)) = 0 := by
  rcases le_or_gt W 0 with hW | hW
  · exact setAverage_weightedSimplex_of_nonpos hw hW _ fun h ↦ by simp [h]
  have hI : ∀ f : (ι → ℝ) → ℝ, Continuous f → IntegrableOn f (weightedSimplex w W) :=
    fun f hf ↦ hf.continuousOn.integrableOn_weightedSimplex hw
  rw [setAverage_fun_sub (hI _ (by fun_prop)) (hI _ continuous_const),
    setAverage_weightedSimplex_linearForm hw c hW, setAverage_weightedSimplex_const hw hW,
    sub_self]

/-- The variance of a linear form on a weighted simplex: for positive weights `w`,
`n = Fintype.card ι`, `0 ≤ W`, mean `m = W * p 1 / (n + 1)` and `p q = ∑ i, (c i / w i) ^ q`,
`⨍ u in weightedSimplex w W, (∑ i, c i * u i - m) ^ 2 =
  W ^ 2 * ((n + 1) * p 2 - p 1 ^ 2) / ((n + 1) ^ 2 * (n + 2))`.

The hypothesis `0 ≤ W` is needed: for `W < 0` the simplex is empty, so the left side is `0`,
while with one coordinate and `w = c = 1` the right side is `W ^ 2 / 12`. At `W = 0` both sides
are `0`. -/
theorem setAverage_weightedSimplex_linearForm_sub_mean_sq {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (c : ι → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    ⨍ u in weightedSimplex w W,
      (∑ i, c i * u i - W * (∑ i, c i / w i) / (Fintype.card ι + 1)) ^ 2 =
      W ^ 2 * ((Fintype.card ι + 1) * ∑ i, (c i / w i) ^ 2 - (∑ i, c i / w i) ^ 2) /
        ((Fintype.card ι + 1) ^ 2 * (Fintype.card ι + 2)) := by
  rcases hW.eq_or_lt with rfl | hW
  · rw [setAverage_weightedSimplex_of_nonpos hw le_rfl _ fun _ ↦ by simp]
    simp
  have hI : ∀ f : (ι → ℝ) → ℝ, Continuous f → IntegrableOn f (weightedSimplex w W) :=
    fun f hf ↦ hf.continuousOn.integrableOn_weightedSimplex hw
  set m := W * (∑ i, c i / w i) / (Fintype.card ι + 1) with hm
  have he : (fun u : ι → ℝ ↦ (∑ i, c i * u i - m) ^ 2) =
      fun u ↦ ((∑ i, c i * u i) ^ 2 - (2 * m) * ∑ i, c i * u i) + m ^ 2 := by
    funext u
    ring
  rw [he, setAverage_fun_add (hI _ (by fun_prop)) (hI _ continuous_const),
    setAverage_fun_sub (hI _ (by fun_prop)) (hI _ (by fun_prop)), average_const_mul,
    setAverage_weightedSimplex_const hw hW, setAverage_weightedSimplex_linearForm_sq hw c hW,
    setAverage_weightedSimplex_linearForm hw c hW, hm]
  field_simp
  ring

/-- The variance of a linear form on a weighted simplex is at most its diagonal term: for positive
weights `w`, `n = Fintype.card ι`, `0 ≤ W` and mean `m = W * (∑ i, c i / w i) / (n + 1)`,
`⨍ u in weightedSimplex w W, (∑ i, c i * u i - m) ^ 2 ≤
  W ^ 2 * (∑ i, (c i / w i) ^ 2) / ((n + 1) * (n + 2))`.
It drops the nonpositive term `-W ^ 2 * (∑ i, c i / w i) ^ 2 / ((n + 1) ^ 2 * (n + 2))` from
`setAverage_weightedSimplex_linearForm_sub_mean_sq`. With one coordinate and `W ≠ 0` the dropped
term is half of the bound, so the inequality is strict. No hypothesis on `W` is needed: for `W < 0`
the simplex is empty, so the left side is `0`. -/
theorem setAverage_weightedSimplex_linearForm_sub_mean_sq_le {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (c : ι → ℝ) (W : ℝ) :
    ⨍ u in weightedSimplex w W,
      (∑ i, c i * u i - W * (∑ i, c i / w i) / (Fintype.card ι + 1)) ^ 2 ≤
      W ^ 2 * (∑ i, (c i / w i) ^ 2) / ((Fintype.card ι + 1) * (Fintype.card ι + 2)) := by
  rcases lt_or_ge W 0 with hW | hW
  · rw [setAverage_weightedSimplex_of_nonpos hw hW.le _ fun h ↦ absurd h hW.ne]
    positivity
  rw [setAverage_weightedSimplex_linearForm_sub_mean_sq hw c hW]
  have hn : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  calc W ^ 2 * ((Fintype.card ι + 1) * ∑ i, (c i / w i) ^ 2 - (∑ i, c i / w i) ^ 2) /
        ((Fintype.card ι + 1) ^ 2 * (Fintype.card ι + 2))
      ≤ W ^ 2 * ((Fintype.card ι + 1) * ∑ i, (c i / w i) ^ 2) /
        ((Fintype.card ι + 1) ^ 2 * (Fintype.card ι + 2)) := by
        gcongr
        exact sub_le_self _ (sq_nonneg _)
    _ = _ := by
        field_simp

/-- The third central moment of a linear form on a weighted simplex: for positive weights `w`,
`n = Fintype.card ι`, `0 ≤ W`, mean `m = W * p 1 / (n + 1)` and `p q = ∑ i, (c i / w i) ^ q`,
`⨍ u in weightedSimplex w W, (∑ i, c i * u i - m) ^ 3 =
  2 * W ^ 3 * ((n + 1) ^ 2 * p 3 - 3 * (n + 1) * p 1 * p 2 + 2 * p 1 ^ 3) /
    ((n + 1) ^ 3 * (n + 2) * (n + 3))`.
Only the raw moments of degree at most `3` enter the proof.

The hypothesis `0 ≤ W` is needed for the same reason as in
`setAverage_weightedSimplex_linearForm_sub_mean_sq`: for `W < 0` the left side is `0`, while the
right side is `W ^ 3` times a factor that is nonzero for suitable coefficients. -/
theorem setAverage_weightedSimplex_linearForm_sub_mean_cube {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (c : ι → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    ⨍ u in weightedSimplex w W,
      (∑ i, c i * u i - W * (∑ i, c i / w i) / (Fintype.card ι + 1)) ^ 3 =
      2 * W ^ 3 * ((Fintype.card ι + 1) ^ 2 * ∑ i, (c i / w i) ^ 3 -
          3 * (Fintype.card ι + 1) * (∑ i, c i / w i) * ∑ i, (c i / w i) ^ 2 +
          2 * (∑ i, c i / w i) ^ 3) /
        ((Fintype.card ι + 1) ^ 3 * (Fintype.card ι + 2) * (Fintype.card ι + 3)) := by
  rcases hW.eq_or_lt with rfl | hW
  · rw [setAverage_weightedSimplex_of_nonpos hw le_rfl _ fun _ ↦ by simp]
    simp
  have hI : ∀ f : (ι → ℝ) → ℝ, Continuous f → IntegrableOn f (weightedSimplex w W) :=
    fun f hf ↦ hf.continuousOn.integrableOn_weightedSimplex hw
  set m := W * (∑ i, c i / w i) / (Fintype.card ι + 1) with hm
  have he : (fun u : ι → ℝ ↦ (∑ i, c i * u i - m) ^ 3) =
      fun u ↦ (((∑ i, c i * u i) ^ 3 - (3 * m) * (∑ i, c i * u i) ^ 2) +
        (3 * m ^ 2) * ∑ i, c i * u i) - m ^ 3 := by
    funext u
    ring
  rw [he, setAverage_fun_sub (hI _ (by fun_prop)) (hI _ continuous_const),
    setAverage_fun_add (hI _ (by fun_prop)) (hI _ (by fun_prop)),
    setAverage_fun_sub (hI _ (by fun_prop)) (hI _ (by fun_prop)), average_const_mul,
    average_const_mul, setAverage_weightedSimplex_const hw hW,
    setAverage_weightedSimplex_linearForm_cube hw c hW,
    setAverage_weightedSimplex_linearForm_sq hw c hW,
    setAverage_weightedSimplex_linearForm hw c hW, hm]
  field_simp
  ring

end MeasureTheory
