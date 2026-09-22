/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The positive part below a threshold, bounded by the mean and variance

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

## Main statements

* `max_sub_zero_le_sub_add_sq_div`: the pointwise bound, over any ordered field.
* `Finset.expect_max_sub_zero_le`: the bound for a uniform average over a finite set.
* `MeasureTheory.integral_max_sub_zero_le`: the bound for a probability measure.

## References

Ports `ReedSolomon.HiddenDerivative.positivePart_pointwise` and
`ReedSolomon.HiddenDerivative.positivePart_mean_variance` from `WeightedSupport/PositivePart.lean`
in `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The pointwise bound is generalized from `ℝ` to any
ordered field, and the finite-average form is new; the probability-measure statement is the
source's, renamed. Neither statement uses coding theory, so both leave the Reed–Solomon namespace.
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

end MeasureTheory
