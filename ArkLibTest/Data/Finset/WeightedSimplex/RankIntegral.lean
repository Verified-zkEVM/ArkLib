/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.WeightedSimplex.RankIntegral

/-!
# Acceptance cases for residual sums over a lattice weighted simplex

A one-point lattice simplex evaluated through the discharged bound, a three-point segment on
which the bound fails once the threshold condition `m < c` becomes an equality, and a zero weight,
for which the bound fails because the enlarged simplex has infinite volume.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace RankIntegralTest

/-- One coordinate, weight `1`, budget `0`, coefficient `1`, threshold `0`. The lattice simplex is
`{0}`, so the sum is `max 0 0 + 1 = 1`. The enlarged simplex is `[0, 1]`, of volume `1`, the mean
is `m = 1 / 2`, `c = 1`, and the variance bound is `1 / 6`; the right side is
`1 * (1 / 2 + (1 / 6) / 2 + 1) = 19 / 12`. -/
example : (1 : ℝ) ≤ 19 / 12 := by
  have h := sum_natWeightedSimplex_max_sub_add_one_le (w := fun _ : Fin 1 ↦ 1)
    (fun _ ↦ one_ne_zero) 0 (a := 1) (fun _ ↦ zero_le_one) (T := 0) (by norm_num)
  have hset : natWeightedSimplex (fun _ : Fin 1 ↦ 1) 0 = {fun _ ↦ 0} := by decide
  rw [hset, volume_real_weightedSimplex (fun _ ↦ by norm_num) (by norm_num)] at h
  norm_num at h
  linarith

/-- The threshold condition `m < c` is needed. One coordinate, weight `1`, budget `2`,
coefficient `1` and threshold `1 / 2` give `m = 3 * 1 / 2 = c`. The lattice points `0, 1, 2`
contribute `3 / 2 + 1 + 1 = 7 / 2`, while the right side is `3 * (0 + V / 0 + 1) = 3` for every
`V`. -/
example (V : ℝ) :
    ¬ (∑ c ∈ natWeightedSimplex (fun _ : Fin 1 ↦ 1) 2,
          (max (1 / 2 - ∑ i, (1 : Fin 1 → ℝ) i * (c i : ℝ)) 0 + 1) ≤
        volume.real (Set.weightedSimplex (fun _ : Fin 1 ↦ ((1 : ℕ) : ℝ)) 3) *
          (3 / 2 - 3 / 2 + V / (4 * (3 / 2 - 3 / 2)) + 1)) := by
  have hset : natWeightedSimplex (fun _ : Fin 1 ↦ 1) 2 = {![0], ![1], ![2]} := by decide
  rw [hset, volume_real_weightedSimplex (fun _ ↦ by norm_num) (by norm_num)]
  norm_num

/-- Positive weights are needed. With one coordinate of weight `0`, budget `0`, coefficient `1`
and threshold `0`, the mean is `m = 0 * (1 / 0) / 2 = 0 < 1 = c`, and the lattice sum is `1`.
The enlarged simplex is the half-line `[0, ∞)`, whose `volume.real` is `0`, so the right side of
the bound is `0`. -/
example : (∑ c ∈ natWeightedSimplex (fun _ : Fin 1 ↦ 0) 0,
      (max (0 - ∑ i, (1 : Fin 1 → ℝ) i * (c i : ℝ)) 0 + 1)) = 1 ∧
    volume.real (Set.weightedSimplex (fun _ : Fin 1 ↦ ((0 : ℕ) : ℝ))
      (((0 : ℕ) : ℝ) + ∑ _i : Fin 1, ((0 : ℕ) : ℝ))) = 0 := by
  have hset : natWeightedSimplex (fun _ : Fin 1 ↦ 0) 0 = {fun _ ↦ 0} := by decide
  refine ⟨by rw [hset]; norm_num, ?_⟩
  have hline : Set.weightedSimplex (fun _ : Fin 1 ↦ ((0 : ℕ) : ℝ))
      (((0 : ℕ) : ℝ) + ∑ _i : Fin 1, ((0 : ℕ) : ℝ)) =
      MeasurableEquiv.funUnique (Fin 1) ℝ ⁻¹' Set.Ici 0 := by
    ext u
    simp [Set.mem_weightedSimplex, Fin.forall_fin_one]
  have htop : volume (Set.weightedSimplex (fun _ : Fin 1 ↦ ((0 : ℕ) : ℝ))
      (((0 : ℕ) : ℝ) + ∑ _i : Fin 1, ((0 : ℕ) : ℝ))) = ⊤ := by
    rw [hline]
    exact ((volume_preserving_funUnique (Fin 1) ℝ).measure_preimage_equiv _).trans Real.volume_Ici
  rw [measureReal_def, htop]
  rfl

end RankIntegralTest
