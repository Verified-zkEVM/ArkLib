/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Finset.WeightedSimplex.FloorTransfer

/-!
# Floor-cell transfers for the hidden-derivative weighted support

The higher-jet exponents of the hidden-derivative interpolation space are tuples
`c : Fin n → ℕ` with `∑ i, (i + 1) * c i ≤ W`, that is, the lattice simplex
`Finset.natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W`. Here `n = d - 1` for derivative order
`d`. This file specializes the generic floor-cell transfers of
`ArkLib.Data.Finset.WeightedSimplex.FloorTransfer` to these weights and to the two integrands used
by the dimension and rank estimates.

* **Dimension direction.** On a measurable part `T` of the continuous simplex of budget `W`, the
  cubic positive part `(g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3` of a normalized coordinate sum
  `z u` integrates to at most the lattice sum of `(max (m * (1 + g) - ∑ i, c i) 0) ^ 3`
  (`weighted_floor_integral`). Flooring a point lowers its coordinate sum, which raises the
  remaining degree `m * (1 + g) - ∑ i, c i` (`floor_remaining`, `floor_cubic`).
* **Rank direction.** The lattice sum of the residual `max (T - ∑ i, c i) 0 + 1` is at most its
  integral over the continuous simplex enlarged by `∑ i, (i + 1) = (n + 1).choose 2`, with the
  threshold raised by `n` (`weighted_residual_sum_le_integral`).

## Main statements

* `ReedSolomon.HiddenDerivative.floor_remaining` and `ReedSolomon.HiddenDerivative.floor_cubic`:
  the pointwise comparisons.
* `ReedSolomon.HiddenDerivative.sum_fin_succ_eq_choose_two`: the total weight
  `∑ i : Fin n, (i + 1) = (n + 1).choose 2`.
* `ReedSolomon.HiddenDerivative.weighted_floor_integral`: the dimension-direction transfer.
* `ReedSolomon.HiddenDerivative.weighted_residual_sum_le_integral`: the rank-direction transfer.

## References

Ports, from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `WeightedSupportParameters.floor_remaining` and `WeightedSupportParameters.floor_cubic`
  (`FloorTransfer.lean`). The hypothesis `0 ≤ g * m` of `floor_cubic` is dropped, since for
  `g * m < 0` the left side is nonpositive.
* `WeightedSupportParameters.weighted_floor_integral` (`FloorTransfer.lean`). The source's
  `weightedHigherJetTuples d W` is `Finset.natWeightedSimplex (fun i : Fin (d - 1) ↦ i.val + 1) W`
  and its `higherJetTupleDegree c` is `∑ i, c i`; the dimension `d - 1` is a free `n`. The
  pointwise hypotheses `hu` and `hW` become `T ⊆ Set.weightedSimplex _ W`, the hypothesis
  `hgm0 : 0 ≤ g * m` is dropped with that of `floor_cubic`, and the cell argument is
  `Finset.setIntegral_le_sum_natWeightedSimplex`.
* `weighted_residual_sum_le_integral` and `residual_le_on_floorCell` (`CubeTransfer.lean`). The
  integrability hypothesis `hint` is dropped: the integrand is continuous and the enlarged simplex
  is compact. The cell argument is `Finset.sum_natWeightedSimplex_le_setIntegral`.
* `coordinateWeight_sum` (`CubeTransfer.lean`) becomes `sum_fin_succ_eq_choose_two`, stated in `ℕ`
  with `n + 1` in place of `d`.

Deferred: `WeightedSupportParameters.weighted_dimension_integral`, which needs the support space
`weightedSupportSpace` and its dimension bound, not yet ported.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

/-- If `μ ≤ (1 + 3 * g / 8) * m`, the continuous coordinate sum `R` satisfies
`R - μ = z * (g * m)`, and the lattice sum `C` is at most `R`, then
`g * m * (5 / 8 - z) ≤ m * (1 + g) - C`. In words, flooring lowers the coordinate sum and so can
only raise the remaining degree budget `m * (1 + g) - C`. -/
theorem floor_remaining (g m μ R C z : ℝ) (hμ : μ ≤ (1 + 3 * g / 8) * m)
    (hZ : R - μ = z * (g * m)) (hfloor : C ≤ R) :
    g * m * (5 / 8 - z) ≤ m * (1 + g) - C := by
  nlinarith

/-- Under the hypotheses of `floor_remaining`, the cubic positive part
`(g * m) ^ 3 * (max (5 / 8 - z) 0) ^ 3` is at most `(max (m * (1 + g) - C) 0) ^ 3`. No sign
condition on `g * m` is needed: for `0 ≤ g * m` the factor moves inside the positive part and
`floor_remaining` applies, and for `g * m < 0` the left side is nonpositive while the right side is
a cube of a nonnegative number. -/
theorem floor_cubic (g m μ R C z : ℝ) (hμ : μ ≤ (1 + 3 * g / 8) * m)
    (hZ : R - μ = z * (g * m)) (hfloor : C ≤ R) :
    (g * m) ^ 3 * (max (5 / 8 - z) 0) ^ 3 ≤ (max (m * (1 + g) - C) 0) ^ 3 := by
  rw [← mul_pow]
  rcases le_or_gt 0 (g * m) with hgm | hgm
  · have hmax : g * m * max (5 / 8 - z) 0 ≤ max (m * (1 + g) - C) 0 := by
      rw [mul_max_of_nonneg _ _ hgm, mul_zero]
      exact max_le_max_right 0 (floor_remaining g m μ R C z hμ hZ hfloor)
    exact pow_le_pow_left₀ (by positivity) hmax _
  · have hneg : g * m * max (5 / 8 - z) 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hgm.le (le_max_right _ _)
    exact (Odd.pow_nonpos (by decide) hneg).trans (by positivity)

/-- The weights `i + 1` of `Fin n` sum to the triangular number `(n + 1).choose 2`. This is the
amount by which the rank-direction transfer enlarges the weighted budget. -/
theorem sum_fin_succ_eq_choose_two (n : ℕ) : ∑ i : Fin n, (i.val + 1) = (n + 1).choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ i + 1), Nat.choose_two_right, ← Finset.sum_range_id,
    Finset.sum_range_succ']
  simp

/-- The dimension-direction transfer. Let `T` be a measurable part of the continuous simplex
`∑ i, (i + 1) * u i ≤ W` in `Fin n → ℝ`, and let `z u` normalize the coordinate sum, so that
`∑ i, u i - μ = z u * (g * m)` on `T`. Then the integral over `T` of the cubic positive part
`(g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3` is at most the sum, over the lattice points `c` of the
same simplex, of `(max (m * (1 + g) - ∑ i, c i) 0) ^ 3`.

The hypothesis `μ ≤ (1 + 3 * g / 8) * m` is that of `floor_cubic`, applied at each point with `C`
the coordinate sum of the floored point. Integrability on `T` is assumed
because the Bochner integral of a non-integrable function is zero by convention; when `T` is
closed and `z` is continuous on it, integrability follows from compactness of the simplex. -/
theorem weighted_floor_integral (n W : ℕ) (g m μ : ℝ) {T : Set (Fin n → ℝ)}
    (hT : MeasurableSet T)
    (hTW : T ⊆ Set.weightedSimplex (fun i : Fin n ↦ ((i.val + 1 : ℕ) : ℝ)) W)
    (z : (Fin n → ℝ) → ℝ) (hμ : μ ≤ (1 + 3 * g / 8) * m)
    (hZ : ∀ u ∈ T, ∑ i, u i - μ = z u * (g * m))
    (hint : IntegrableOn (fun u ↦ (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3) T) :
    ∫ u in T, (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3 ≤
      ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W,
        (max (m * (1 + g) - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 3 := by
  have h := Finset.setIntegral_le_sum_natWeightedSimplex (w := fun i : Fin n ↦ i.val + 1)
    (fun i ↦ Nat.succ_ne_zero _) (W := (W : ℝ)) hT hTW hint
    (g := fun c ↦ (max (m * (1 + g) - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 3)
    (fun c _ ↦ by positivity) fun u hu ↦ ?_
  · simpa only [Nat.floor_natCast] using h
  have hu0 := (Set.mem_weightedSimplex.mp (hTW hu)).1
  refine floor_cubic g m μ (∑ i, u i) _ (z u) hμ (hZ u hu) ?_
  push_cast
  exact Finset.sum_le_sum fun i _ ↦ Nat.floor_le (hu0 i)

/-- The rank-direction transfer. The sum, over the lattice points `c` of the simplex
`∑ i, (i + 1) * c i ≤ W` in `Fin n → ℕ`, of the residual `max (T - ∑ i, c i) 0 + 1` is at most the
integral of `max (T + n - ∑ i, u i) 0 + 1` over the continuous simplex of budget
`W + (n + 1).choose 2`. On the unit cell of `c` the continuous coordinate sum exceeds `∑ i, c i`
by less than `n`, which is why the threshold is raised by `n`; the cells lie in the simplex whose
budget is enlarged by the total weight `(n + 1).choose 2`. No integrability hypothesis is needed:
the integrand is continuous and the weights are positive, so the enlarged simplex is compact. -/
theorem weighted_residual_sum_le_integral (n W : ℕ) (T : ℝ) :
    ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W,
        (max (T - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) ≤
      ∫ u in Set.weightedSimplex (fun i : Fin n ↦ ((i.val + 1 : ℕ) : ℝ))
          ((W : ℝ) + ((n + 1).choose 2 : ℕ)),
        (max (T + n - ∑ i, u i) 0 + 1) := by
  have hsum : ∑ i : Fin n, ((i.val + 1 : ℕ) : ℝ) = ((n + 1).choose 2 : ℕ) := by
    rw [← sum_fin_succ_eq_choose_two]
    push_cast
    rfl
  have h := Finset.sum_natWeightedSimplex_le_setIntegral (w := fun i : Fin n ↦ i.val + 1) W
    (f := fun u ↦ max (T + n - ∑ i, u i) 0 + 1)
    (g := fun c ↦ max (T - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) ?_ (fun _ _ ↦ by positivity) ?_
  · simpa only [hsum] using h
  · refine ContinuousOn.integrableOn_weightedSimplex (fun i ↦ by positivity) ?_
    fun_prop
  · intro c _ u hu
    have h1 := MeasureTheory.sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell
      (a := fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one) hu
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at h1
    push_cast
    exact add_le_add_left (max_le_max_right 0 (by linarith)) 1

end ReedSolomon.HiddenDerivative
