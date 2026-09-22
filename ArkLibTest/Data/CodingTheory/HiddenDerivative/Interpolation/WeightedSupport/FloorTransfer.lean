/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer

/-!
# Acceptance cases for the hidden-derivative floor-cell transfers

These cases evaluate the triangular total weight, restate it and
`weighted_residual_sum_le_integral` in the dimension `d - 1`, check the zero-dimensional case of
the residual transfer, and check `floor_cubic` for a negative `g * m`.
-/

open MeasureTheory
open scoped BigOperators
open ReedSolomon.HiddenDerivative

/-- The weights `1, 2, 3, 4` sum to `10 = (5).choose 2`. -/
example : ∑ i : Fin 4, (i.val + 1) = 10 := by
  rw [sum_fin_succ_eq_choose_two]
  rfl

/-- In dimension `d - 1` the total weight is `d.choose 2`, including `d = 0`, where both sides
are zero. -/
theorem sum_fin_sub_one_succ_eq_choose_two (d : ℕ) :
    ∑ i : Fin (d - 1), ((i.val + 1 : ℕ) : ℝ) = (d.choose 2 : ℝ) := by
  have h := sum_fin_succ_eq_choose_two (d - 1)
  rcases d with _ | d
  · simp
  · simp only [Nat.add_sub_cancel] at h ⊢
    exact_mod_cast h

/-- `weighted_residual_sum_le_integral` in dimension `d - 1`, with the budget enlargement written
as the weight sum `∑ i : Fin (d - 1), (i + 1)` instead of `d.choose 2`. -/
example (d W : ℕ) (T : ℝ) :
    ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin (d - 1) ↦ i.val + 1) W,
        (max (T - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) ≤
      ∫ u in Set.weightedSimplex (fun i : Fin (d - 1) ↦ ((i.val + 1 : ℕ) : ℝ))
          ((W : ℝ) + ∑ i : Fin (d - 1), ((i.val + 1 : ℕ) : ℝ)),
        (max (T + (d - 1 : ℕ) - ∑ i, u i) 0 + 1) := by
  have h := weighted_residual_sum_le_integral (d - 1) W T
  have hs : ∑ i : Fin (d - 1), ((i.val + 1 : ℕ) : ℝ) = (((d - 1 + 1).choose 2 : ℕ) : ℝ) := by
    exact_mod_cast sum_fin_succ_eq_choose_two (d - 1)
  rwa [hs]

/-- In dimension zero both sides of the residual transfer equal `max T 0 + 1`: the lattice
simplex has one point and the continuous simplex is the one-point space of volume one. -/
example (W : ℕ) (T : ℝ) :
    ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin 0 ↦ i.val + 1) W,
        (max (T - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) = max T 0 + 1 ∧
      max T 0 + 1 ≤ ∫ u in Set.weightedSimplex (fun i : Fin 0 ↦ ((i.val + 1 : ℕ) : ℝ))
          ((W : ℝ) + ((0 + 1).choose 2 : ℕ)),
        (max (T + (0 : ℕ) - ∑ i, u i) 0 + 1) := by
  have hcard : Finset.natWeightedSimplex (fun i : Fin 0 ↦ i.val + 1) W = {![]} := by
    ext c
    simp only [Finset.mem_natWeightedSimplex (fun i : Fin 0 ↦ i.elim0), Finset.mem_singleton,
      Subsingleton.elim c ![]]
    simp
  have h := weighted_residual_sum_le_integral 0 W T
  rw [hcard] at h ⊢
  simp only [Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero,
    sub_zero] at h ⊢
  exact ⟨trivial, h⟩

/-- `floor_cubic` needs no sign condition on `g * m`: at `g = -1`, `m = 1`, `μ = R = C = z = 0`
the left side is `-(5 / 8) ^ 3` and the right side is `0`. -/
example : ((-1 : ℝ) * 1) ^ 3 * (max (5 / 8 - 0) 0) ^ 3 ≤ (max (1 * (1 + -1) - 0) 0) ^ 3 :=
  floor_cubic (-1) 1 0 0 0 0 (by norm_num) (by norm_num) le_rfl
