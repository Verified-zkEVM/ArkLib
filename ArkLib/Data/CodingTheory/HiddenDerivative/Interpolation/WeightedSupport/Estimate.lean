/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments
public import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds

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
the moment estimates of `WeightedSupport/Moments.lean` apply. For `d ≥ 10000` the harmonic-number
bounds of `ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds` discharge the hypotheses of
`normalizedRadius_contribution_lower`, which bounds that set average below by
`(5 / 8) ^ 3 + (4147 / 2160) * (W / (d * (g * m))) ^ 2`.

## Main statements

* `weighted_dimension_integral`: the integral over any measurable part of the simplex bounds the
  dimension.
* `weighted_dimension_probability`: the same bound over the whole simplex, as
  `W ^ (d - 1) / ((d - 1)!) ^ 2 * D / 6 * (g * m) ^ 3` times the set average of
  `(max (5 / 8 - normalizedRadius W (g * m) u) 0) ^ 3`.
* `weighted_dimension_lower`: the explicit lower bound
  `W ^ (d - 1) / ((d - 1)!) ^ 2 * D / 6 * (g * m) ^ 3 *
    ((5 / 8) ^ 3 + (4147 / 2160) * (W / (d * (g * m))) ^ 2)` for `d ≥ 10000`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1, the coefficient count (71).
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

/-- The explicit lower bound on the dimension of the weighted support space at the cutoff
`m * D * (1 + g)`: for `d ≥ 10000`, with `V = W ^ (d - 1) / ((d - 1)!) ^ 2` the volume of the
simplex with weights `1, …, d - 1` and budget `W`, and `s = W / (d * (g * m))`,
`V * D / 6 * (g * m) ^ 3 * ((5 / 8) ^ 3 + (4147 / 2160) * s ^ 2)` is at most the dimension,
provided the mean `W * harmonic (d - 1) / d` of the coordinate sum is at most
`(1 + 3 * g / 8) * m` and `s ≤ 10 / 27`.

This is `weighted_dimension_probability` combined with `normalizedRadius_contribution_lower` in
dimension `d - 1`. Role of the hypotheses. `10000 ≤ d` gives `harmonic (d - 1) ^ 2 ≤ d / 100`
(`Real.harmonic_sq_le_succ_div_hundred`) and `8 ≤ d - 1` for the lower bound on
`∑ i < d - 1, 1 / (i + 1) ^ 2` (`Real.reciprocal_square_sum_gt`); the upper bound on
`∑ i < d - 1, 1 / (i + 1) ^ 3` (`Real.reciprocal_cube_sum_lt`) needs no hypothesis. `0 < D` makes
the support finite. `s ≤ 10 / 27` is the sharp threshold of `cubic_contribution_numeric`. No
positivity of `W` or `g * m` is needed: for `W = 0` the volume factor `V` is `0`, and for
`g * m ≤ 0` the left side is at most `0`. -/
theorem weighted_dimension_lower (F : Type*) [Field F] (hd : 10000 ≤ d) (hD : 0 < D)
    (g m : ℝ) (hμ : (W : ℝ) * (harmonic (d - 1) : ℝ) / d ≤ (1 + 3 * g / 8) * m)
    (hs : W / ((d : ℝ) * (g * m)) ≤ 10 / 27) :
    (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 * D / 6 * (g * m) ^ 3 *
        ((5 / 8) ^ 3 + (4147 / 2160) * (W / ((d : ℝ) * (g * m))) ^ 2) ≤
      Module.finrank F (weightedSupportSpace F D d W (m * D * (1 + g)) hD) := by
  have hV : 0 ≤ (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 * D / 6 := by positivity
  have hc0 : 0 ≤ (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (W / ((d : ℝ) * (g * m))) ^ 2 := by
    positivity
  rcases le_or_gt (g * m) 0 with hgm | hgm
  · refine le_trans ?_ (Nat.cast_nonneg _)
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hV
      (Odd.pow_nonpos (by decide) hgm)) hc0
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · rw [Nat.cast_zero, zero_pow (by omega)]
    simp
  have hn : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ d)
  have hsum (k : ℕ) : ∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ k =
      ∑ i ∈ Finset.range (d - 1), 1 / ((i : ℝ) + 1) ^ k :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1) ^ k) (d - 1)
  have hc := normalizedRadius_contribution_lower (d - 1) (W := W) (t := g * m)
    (Nat.cast_pos.mpr hW) hgm.le (Real.harmonic_sq_le_succ_div_hundred (by omega))
    (by rw [hsum]; exact (Real.reciprocal_square_sum_gt (by omega)).le)
    (by rw [hsum]; exact (Real.reciprocal_cube_sum_lt _).le) (by rwa [hn])
  rw [hn] at hc
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (weighted_dimension_probability F (by omega) hD g m hμ)

end ReedSolomon.HiddenDerivative
