/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments

/-!
# Integral lower bounds on the dimension of the weighted support space

This file bounds the dimension of the weighted support space at the capacity cutoff
`L = m * D * (1 + g)` from below by an integral over the continuous higher-jet simplex
`∑ i, (i + 1) * u i ≤ W` in `Fin (d - 1) → ℝ`.

Dividing the cutoff by `D` leaves the budget `m * (1 + g) - ∑ i, c i` for a lattice point `c`, so
`weightedSupport_dimension_ge_cubic_sum` bounds the dimension below by
`D / 6 * ∑_c (max (m * (1 + g) - ∑ i, c i) 0) ^ 3`. The floor-cell transfer
`weighted_floor_integral` bounds this lattice sum below by the integral of the cubic positive part
`(g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3` of a normalized coordinate sum `z`. With `z` the
normalized radius and the integral written as volume times set average, this is the form in which
the moment estimates of `WeightedSupport/Moments.lean` apply.

## Main statements

* `weighted_dimension_integral`: the integral over any measurable part of the simplex bounds the
  dimension.
* `weighted_dimension_probability`: the same bound over the whole simplex, as
  `W ^ (d - 1) / ((d - 1)!) ^ 2 * D / 6 * (g * m) ^ 3` times the set average of
  `(max (5 / 8 - normalizedRadius W (g * m) u) 0) ^ 3`.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d:

* `WeightedSupportParameters.weighted_dimension_integral` (`FloorTransfer.lean`). As in the port of
  `weighted_floor_integral`, the pointwise hypotheses `hu` and `hW` become
  `T ⊆ Set.weightedSimplex _ W` and the hypothesis `0 ≤ g * m` is dropped.
* `weighted_dimension_probability` (`Estimate.lean`). The integral against the source's
  `weightedSimplexProbabilityMeasure` is the set average over the simplex, following
  `WeightedSupport/Moments.lean`, and its `harmonicPowerSum (d - 1) 1` is `harmonic (d - 1)`. The
  hypotheses `0 < W` and `0 < g * m` are dropped: for `g * m = 0` the left side is `0`, and when
  the simplex has volume zero the product of its volume with the set average is `0`.

Deferred: `weighted_dimension_lower`, which needs the harmonic-number estimates
`Real.harmonic_pred_le_log_add_three_fifths`, `Real.log_add_three_fifths_le_sqrt_div_ten`,
`Real.reciprocal_square_sum_gt` and `Real.reciprocal_cube_sum_lt`.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

/-- The integral lower bound on the dimension of the weighted support space at the cutoff
`m * D * (1 + g)`. Let `T` be a measurable part of the continuous simplex
`∑ i, (i + 1) * u i ≤ W` and let `z` satisfy `∑ i, u i - μ = z u * (g * m)` on `T`. If
`μ ≤ (1 + 3 * g / 8) * m`, then `D / 6` times the integral over `T` of
`(g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3` is at most the dimension.

The hypotheses on `μ`, `z` and integrability are those of `weighted_floor_integral`; `0 < d` and
`0 < D` are those of `weightedSupport_dimension_ge_cubic_sum`. -/
theorem weighted_dimension_integral (F : Type*) [Field F] (hd : 0 < d) (hD : 0 < D)
    (g m μ : ℝ) {T : Set (Fin (d - 1) → ℝ)} (hT : MeasurableSet T)
    (hTW : T ⊆ weightedSimplex (fun i : Fin (d - 1) ↦ ((i.val + 1 : ℕ) : ℝ)) W)
    (z : (Fin (d - 1) → ℝ) → ℝ) (hμ : μ ≤ (1 + 3 * g / 8) * m)
    (hZ : ∀ u ∈ T, ∑ i, u i - μ = z u * (g * m))
    (hint : IntegrableOn (fun u ↦ (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3) T) :
    (D : ℝ) / 6 * ∫ u in T, (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3 ≤
      Module.finrank F (weightedSupportSpace F D d W (m * D * (1 + g)) hD) := by
  have hf := weighted_floor_integral (d - 1) W g m μ hT hTW z hμ hZ hint
  have hdim := weightedSupport_dimension_ge_cubic_sum F (W := W) (L := m * D * (1 + g)) hd hD
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : m * D * (1 + g) / D = m * (1 + g) := by field_simp
  rw [he] at hdim
  refine (mul_le_mul_of_nonneg_left hf (by positivity)).trans (le_of_eq_of_le ?_ hdim)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The whole-simplex form of `weighted_dimension_integral`. With
`V = W ^ (d - 1) / ((d - 1)!) ^ 2` the volume of the simplex with weights `1, …, d - 1` and
budget `W`, the quantity `V * D / 6 * (g * m) ^ 3` times the set average over that simplex of
`(max (5 / 8 - normalizedRadius W (g * m) u) 0) ^ 3` is at most the dimension of the weighted
support space at the cutoff `m * D * (1 + g)`, provided the mean `W * harmonic (d - 1) / d` of the
coordinate sum is at most `(1 + 3 * g / 8) * m`.

The hypothesis `0 < d` provides the `Y₁` coordinate and `0 < D` the finiteness of the support.
No positivity of `W` or `g * m` is needed. -/
theorem weighted_dimension_probability (F : Type*) [Field F] (hd : 0 < d) (hD : 0 < D)
    (g m : ℝ) (hμ : (W : ℝ) * (harmonic (d - 1) : ℝ) / d ≤ (1 + 3 * g / 8) * m) :
    (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 * D / 6 * (g * m) ^ 3 *
        ⨍ u in weightedSimplex (fun i : Fin (d - 1) ↦ (i : ℝ) + 1) W,
          (max (5 / 8 - normalizedRadius W (g * m) u) 0) ^ 3 ≤
      Module.finrank F (weightedSupportSpace F D d W (m * D * (1 + g)) hD) := by
  set S := weightedSimplex (fun i : Fin (d - 1) ↦ (i : ℝ) + 1) W with hS
  set f := fun u : Fin (d - 1) → ℝ ↦ (max (5 / 8 - normalizedRadius W (g * m) u) 0) ^ 3
  rcases eq_or_ne (g * m) 0 with hgm | hgm
  · simp [hgm]
  have hn : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast Nat.sub_add_cancel hd
  have hSw : weightedSimplex (fun i : Fin (d - 1) ↦ ((i.val + 1 : ℕ) : ℝ)) W = S := by
    simp only [S, Nat.cast_add, Nat.cast_one]
  have hint : IntegrableOn (fun u ↦ (g * m) ^ 3 * f u) S :=
    (continuous_const.mul (((continuous_const.sub
      (continuous_normalizedRadius (d - 1) W (g * m))).max continuous_const).pow 3)).continuousOn
      |>.integrableOn_weightedSimplex fun i => by positivity
  have hμ' : (W : ℝ) * (harmonic (d - 1) : ℝ) / (((d - 1 : ℕ) : ℝ) + 1) ≤
      (1 + 3 * g / 8) * m := by
    rwa [hn]
  have hdim := weighted_dimension_integral F (W := W) (T := S) hd hD g m _
    (measurableSet_weightedSimplex _ _) hSw.ge (normalizedRadius W (g * m)) hμ'
    (fun u _ => by rw [normalizedRadius, div_mul_cancel₀ _ hgm]) hint
  rw [integral_const_mul] at hdim
  rw [← volume_real_weightedSimplex_succ (d - 1) (Nat.cast_nonneg W), ← hS, setAverage_eq,
    smul_eq_mul]
  rcases eq_or_ne (volume.real S) 0 with hv | hv
  · simp only [hv, zero_mul, zero_div]
    positivity
  refine le_of_eq_of_le ?_ hdim
  field_simp

end ReedSolomon.HiddenDerivative
