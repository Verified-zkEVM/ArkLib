/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.ConditionalProbability

/-!
# Moment bounds for the positive part below a threshold

For a threshold `c` above a centre `μ`, the positive part `max (c - y) 0` is bounded by the
quadratic `c - y + (y - μ) ^ 2 / (4 * (c - μ))`. The quadratic minus the positive part is
`(y - μ) ^ 2 / (4 * (c - μ))` for `y ≤ c` and `(y + μ - 2 * c) ^ 2 / (4 * (c - μ))` for `c ≤ y`,
so the bound is attained at `y = μ` and at `y = 2 * c - μ`.

Averaging the pointwise bound with `μ` equal to the mean gives
`E[max (c - Y) 0] ≤ c - μ + Var(Y) / (4 * (c - μ))`. It is stated for a finite uniform average
(`Finset.expect`) and for an integral against a probability measure. The first-moment term alone
gives only the lower bound `c - μ ≤ E[max (c - Y) 0]`; the variance term controls the part of the
distribution above `c`.

The hypothesis `μ < c` is needed. At `μ = c` the quadratic term has denominator zero and the
right side becomes `c - y`, which is negative for `y > c`, while the positive part is zero.

For a probability measure `P`, a threshold `b`, and `z` with mean `0` and integrable cube,
`b ^ 3 + 3 * b * ∫ z ^ 2 ∂P - ∫ z ^ 3 ∂P ≤ ∫ (max (b - z) 0) ^ 3 ∂P`. The left side is the
integral of `(b - z) ^ 3`, and `x ^ 3 ≤ (max x 0) ^ 3` for every real `x`. Only moments up to
order three enter. The mean-zero hypothesis is needed: for `z = 1` almost surely and `b = 1`
the left side is `3` and the right side is `0`.

## Main statements

* `max_sub_zero_le_sub_add_sq_div`: the pointwise bound, over any ordered field.
* `Finset.expect_max_sub_zero_le`: the bound for a uniform average over a finite set.
* `MeasureTheory.integral_max_sub_zero_le`: the bound for a probability measure.
* `MeasureTheory.setIntegral_max_sub_zero_le`: the bound for a set integral over any set,
  `∫ x in s, max (c - Y x) 0 ∂μ ≤ μ.real s * (c - m + V / (4 * (c - m)))`, with `m` and `V` the
  set averages of `Y` and `(Y - m) ^ 2`.
* `MeasureTheory.le_integral_max_sub_zero_pow_three`: a lower bound for the cube of the positive
  part by the second and third moments.

## References

Ports `ReedSolomon.HiddenDerivative.positivePart_pointwise` and
`ReedSolomon.HiddenDerivative.positivePart_mean_variance` from `WeightedSupport/PositivePart.lean`
in `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The pointwise bound is generalized from `ℝ` to any
ordered field, and the finite-average form is new; the probability-measure statement is the
source's, renamed. Neither statement uses coding theory, so both leave the Reed–Solomon namespace.

`le_integral_max_sub_zero_pow_three` ports
`ReedSolomon.HiddenDerivative.WeightedSupportParameters.positive_cube_moments` from
`WeightedSupport/Cubic.lean` at the same revision, together with the pointwise
`cubic_le_positive_cube` used in its proof. The source's integrability hypotheses for `z ^ 2` and
for `(max (b - z) 0) ^ 3` are dropped: both follow from the integrability of `z` and `z ^ 3`.
The rest of `Cubic.lean` (`positive_cube_tangent`, `positive_cube_jensen`,
`positive_cube_convex`) has no consumer in the port so far and is not ported.

`setIntegral_max_sub_zero_le` is the step of the source's
`ReedSolomon.HiddenDerivative.weighted_residual_sum_le_volume_mul_mean_variance` (in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at the same revision) that applies `positivePart_mean_variance` to the
conditional measure on the weighted simplex and multiplies back by its volume. Here it is stated
for any measure and any set, including sets of measure `0` or `∞`.
-/

@[expose] public section

open scoped BigOperators

section Pointwise

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For `μ < c`, the positive part `max (c - y) 0` is at most
`c - y + (y - μ) ^ 2 / (4 * (c - μ))`. The right side equals
`(y + μ - 2 * c) ^ 2 / (4 * (c - μ))`, so it is also nonnegative. The hypothesis `μ < c` is
needed: at `μ = c` the right side is `c - y`, which is negative for `y > c`. -/
theorem max_sub_zero_le_sub_add_sq_div {c μ : K} (y : K) (h : μ < c) :
    max (c - y) 0 ≤ c - y + (y - μ) ^ 2 / (4 * (c - μ)) := by
  have hd : 0 < 4 * (c - μ) := by linarith
  have hsq : c - y + (y - μ) ^ 2 / (4 * (c - μ)) =
      (y + μ - 2 * c) ^ 2 / (4 * (c - μ)) := by
    field_simp
    ring
  refine max_le (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hd.le)) ?_
  rw [hsq]
  exact div_nonneg (sq_nonneg _) hd.le

/-- The uniform average of `max (c - Y i) 0` over a finite set is at most
`c - μ + (average of (Y i - μ) ^ 2) / (4 * (c - μ))`, where `μ` is the average of `Y` and
`μ < c`. The empty set is allowed: every average is then zero, so `μ = 0` and the bound reads
`0 ≤ c`. -/
theorem Finset.expect_max_sub_zero_le {ι : Type*} {s : Finset ι} (Y : ι → K) {c μ : K}
    (hmean : 𝔼 i ∈ s, Y i = μ) (hc : μ < c) :
    𝔼 i ∈ s, max (c - Y i) 0 ≤ c - μ + (𝔼 i ∈ s, (Y i - μ) ^ 2) / (4 * (c - μ)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.expect_empty, zero_div, add_zero]
    linarith
  calc
    𝔼 i ∈ s, max (c - Y i) 0 ≤ 𝔼 i ∈ s, (c - Y i + (Y i - μ) ^ 2 / (4 * (c - μ))) :=
      Finset.expect_le_expect fun i _ ↦ max_sub_zero_le_sub_add_sq_div (Y i) hc
    _ = c - μ + (𝔼 i ∈ s, (Y i - μ) ^ 2) / (4 * (c - μ)) := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, Finset.expect_const hs, hmean,
        Finset.expect_div]

end Pointwise

namespace MeasureTheory

open scoped ENNReal ProbabilityTheory

/-- For a probability measure `P`, an integrable `Y` with mean `μ` and square-integrable deviation
`Y - μ`, and a threshold `c > μ`,
`∫ max (c - Y) 0 ∂P ≤ c - μ + (∫ (Y - μ) ^ 2 ∂P) / (4 * (c - μ))`.
The integrability of `(Y - μ) ^ 2` is needed: otherwise its Bochner integral is zero by convention,
and the bound would claim `∫ max (c - Y) 0 ∂P ≤ c - μ`, which fails whenever `Y > c` with positive
probability. A probability measure is needed so that the constant `c` integrates to `c`. -/
theorem integral_max_sub_zero_le {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (Y : X → ℝ) (c μ : ℝ)
    (hY : Integrable Y P) (hmean : ∫ x, Y x ∂P = μ)
    (hv : Integrable (fun x ↦ (Y x - μ) ^ 2) P) (hc : μ < c) :
    ∫ x, max (c - Y x) 0 ∂P ≤ c - μ + (∫ x, (Y x - μ) ^ 2 ∂P) / (4 * (c - μ)) := by
  have hl : Integrable (fun x ↦ c - Y x) P := (integrable_const c).sub hY
  have hq : Integrable (fun x ↦ (Y x - μ) ^ 2 / (4 * (c - μ))) P := hv.div_const _
  calc
    ∫ x, max (c - Y x) 0 ∂P ≤ ∫ x, (c - Y x + (Y x - μ) ^ 2 / (4 * (c - μ))) ∂P :=
      integral_mono (hl.sup (integrable_const 0)) (hl.add hq)
        fun x ↦ max_sub_zero_le_sub_add_sq_div (Y x) hc
    _ = c - μ + (∫ x, (Y x - μ) ^ 2 ∂P) / (4 * (c - μ)) := by
      rw [integral_add hl hq, integral_sub (integrable_const c) hY, integral_div, hmean]
      simp

/-- The set-average form of `integral_max_sub_zero_le`: for a set `s`, a function `Y`
integrable on `s` with average `m` over `s` and square-integrable deviation `Y - m` on `s`, and a
threshold `c > m`,
`∫ x in s, max (c - Y x) 0 ∂μ ≤ μ.real s * (c - m + (⨍ x in s, (Y x - m) ^ 2 ∂μ) / (4 * (c - m)))`.
This is the bound for the conditional probability measure `μ[|s]`, multiplied by `μ.real s`.

No hypothesis on `μ s` is needed. If `μ s = 0`, both sides are `0`. If `μ s = ∞`, then
`μ.real s = 0`, so the average `m` is `0` and the right side is `0`; on the left,
`max (c - Y) 0 + Y ≥ c > 0` on `s`, so `max (c - Y) 0` is not integrable on `s` and its Bochner
integral is `0`. The integrability of `(Y - m) ^ 2` on `s` is needed for the same reason as in
`integral_max_sub_zero_le`. -/
theorem setIntegral_max_sub_zero_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (Y : X → ℝ) {c m : ℝ}
    (hY : IntegrableOn Y s μ) (hmean : ⨍ x in s, Y x ∂μ = m)
    (hv : IntegrableOn (fun x ↦ (Y x - m) ^ 2) s μ) (hc : m < c) :
    ∫ x in s, max (c - Y x) 0 ∂μ ≤
      μ.real s * (c - m + (⨍ x in s, (Y x - m) ^ 2 ∂μ) / (4 * (c - m))) := by
  by_cases hμs : μ s = ∞
  · have hreal : μ.real s = 0 := by simp [measureReal_def, hμs]
    have hm : m = 0 := by rw [← hmean, setAverage_eq, hreal, inv_zero, zero_smul]
    subst hm
    rw [hreal, zero_mul]
    refine (integral_undef fun hg ↦ ?_).le
    have hconst : IntegrableOn (fun _ ↦ c) s μ := by
      refine (hg.add hY).mono aestronglyMeasurable_const (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [Real.norm_eq_abs, abs_of_pos hc]
      have := le_max_left (c - Y x) 0
      exact (le_abs_self _).trans' (by simp only [Pi.add_apply]; linarith)
    rcases (integrableOn_const_iff (C := c)).1 hconst with h | h
    · exact hc.ne' (by simpa using h)
    · exact h.ne hμs
  by_cases h0 : μ s = 0
  · simp [Measure.restrict_eq_zero.2 h0, measureReal_def, h0]
  have := ProbabilityTheory.cond_isProbabilityMeasure_of_finite h0 hμs
  have hpos : 0 < μ.real s := ENNReal.toReal_pos h0 hμs
  have h := integral_max_sub_zero_le (μ[|s]) Y c m
    (hY.smul_measure (ENNReal.inv_ne_top.2 h0))
    (by rw [← hmean]; exact (setAverage_eq' μ _ s).symm)
    (hv.smul_measure (ENNReal.inv_ne_top.2 h0)) hc
  have hcond : ∀ f : X → ℝ, ∫ x, f x ∂μ[|s] = ⨍ x in s, f x ∂μ :=
    fun f ↦ (setAverage_eq' μ _ s).symm
  rw [hcond, hcond, setAverage_eq, smul_eq_mul] at h
  exact (inv_mul_le_iff₀ hpos).1 h

/-- For a probability measure `P`, a threshold `b`, and `z` with mean `0` such that `z` and
`z ^ 3` are integrable,
`b ^ 3 + 3 * b * ∫ z ^ 2 ∂P - ∫ z ^ 3 ∂P ≤ ∫ (max (b - z) 0) ^ 3 ∂P`.
The left side is `∫ (b - z) ^ 3 ∂P` expanded with `∫ z ∂P = 0`, and `(b - z) ^ 3` is pointwise at
most `(max (b - z) 0) ^ 3`. The functions `z ^ 2` and `(max (b - z) 0) ^ 3` are integrable because
they are bounded by `|z| + |z ^ 3|` and by `(|b| + |z|) ^ 3`.

The mean-zero hypothesis is needed: for `z = 1` almost surely and `b = 1` the left side is `3`
while the right side is `0`. The integrability of `z ^ 3` is needed because otherwise its Bochner
integral is `0` by convention. -/
theorem le_integral_max_sub_zero_pow_three {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (z : X → ℝ) (b : ℝ) (hz : Integrable z P)
    (h3 : Integrable (fun x ↦ z x ^ 3) P) (hm : ∫ x, z x ∂P = 0) :
    b ^ 3 + 3 * b * (∫ x, z x ^ 2 ∂P) - ∫ x, z x ^ 3 ∂P ≤ ∫ x, (max (b - z x) 0) ^ 3 ∂P := by
  have h2 : Integrable (fun x ↦ z x ^ 2) P := by
    refine Integrable.mono' (hz.abs.add h3.abs) (hz.aestronglyMeasurable.pow 2)
      (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_pow, sq_abs]
    nlinarith [abs_nonneg (z x), sq_nonneg (|z x| - 1 / 2), sq_abs (z x)]
  have hf : Integrable (fun x ↦ (max (b - z x) 0) ^ 3) P := by
    have hg : Integrable (fun x ↦ |b| ^ 3 + 3 * |b| ^ 2 * |z x| + 3 * |b| * z x ^ 2 + |z x ^ 3|)
        P :=
      (((integrable_const _).add (hz.abs.const_mul _)).add (h2.const_mul _)).add h3.abs
    have hmeas : AEStronglyMeasurable (fun x ↦ (max (b - z x) 0) ^ 3) P :=
      (((continuous_const.sub continuous_id).max continuous_const).pow 3).comp_aestronglyMeasurable
        hz.aestronglyMeasurable
    refine Integrable.mono' hg hmeas (ae_of_all _ fun x ↦ ?_)
    have h0 : 0 ≤ max (b - z x) 0 := le_max_right _ _
    have hle : max (b - z x) 0 ≤ |b| + |z x| :=
      max_le (by linarith [le_abs_self b, neg_abs_le (z x)]) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 3)]
    calc (max (b - z x) 0) ^ 3 ≤ (|b| + |z x|) ^ 3 := pow_le_pow_left₀ h0 hle 3
      _ = _ := by rw [abs_pow, ← sq_abs (z x)]; ring
  have he : (fun x ↦ (b - z x) ^ 3) =
      fun x ↦ b ^ 3 - 3 * b ^ 2 * z x + 3 * b * z x ^ 2 - z x ^ 3 := by
    funext x
    ring
  have hi := (((integrable_const (b ^ 3)).sub (hz.const_mul (3 * b ^ 2))).add
    (h2.const_mul (3 * b))).sub h3
  have hc : Integrable (fun x ↦ (b - z x) ^ 3) P := by rw [he]; exact hi
  have hpt : ∀ x, (b - z x) ^ 3 ≤ (max (b - z x) 0) ^ 3 := fun x ↦ by
    rcases le_total 0 (b - z x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (b - z x)]
  have h := integral_mono hc hf hpt
  rw [he, integral_sub _ h3, integral_add _ (h2.const_mul (3 * b)),
    integral_sub (integrable_const _) (hz.const_mul (3 * b ^ 2))] at h
  · simpa [integral_const_mul, hm] using h
  · exact (integrable_const _).sub (hz.const_mul _)
  · exact ((integrable_const _).sub (hz.const_mul _)).add (h2.const_mul _)

end MeasureTheory
