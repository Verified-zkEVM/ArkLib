/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral

/-!
# Acceptance cases for the hidden-derivative residual sums

A two-coordinate instance evaluated through the discharged bound, the zero-dimensional case, where
the bound is attained, and the source's `weightedSimplex_centeredRadius_sq_le_harmonic` and
`volume_weightedSimplex_add_choose_le_exp` in the dimension `d - 1`.
-/

open MeasureTheory
open scoped BigOperators
open ReedSolomon.HiddenDerivative

/-- Weights `1, 2`, budget `0` and threshold `0`. The lattice simplex is `{0}`, so the sum is `1`.
The enlarged simplex has budget `0 + 3` and volume `3 ^ 2 / (2!) ^ 2 = 9 / 4`; the mean is
`3 * harmonic 2 / 3 = 3 / 2`, `c = 0 + 2`, and the variance bound is
`3 ^ 2 * (1 + 1 / 4) / (3 * 4) = 15 / 16`. The right side is
`9 / 4 * (1 / 2 + (15 / 16) / 2 + 1) = 567 / 128`. -/
example : (1 : ℝ) ≤ 567 / 128 := by
  have hH : (harmonic 2 : ℝ) = 3 / 2 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have h := weighted_residual_sum_le_volume_mul_harmonic_variance 2 0 (T := 0)
    (by norm_num [hH, Nat.choose])
  have hset : Finset.natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 0 = {fun _ ↦ 0} := by decide
  rw [hset, volume_real_weightedSimplex_succ 2 (by positivity)] at h
  norm_num [hH, Nat.choose, Nat.factorial, Fin.sum_univ_two] at h
  linarith

/-- In dimension zero the bound is attained for every `T > 0`: the lattice sum is `T + 1`, the
enlarged simplex is a point of volume `1`, `harmonic 0 = 0`, the variance term vanishes, and the
right side is `T + 1`. -/
example (W : ℕ) {T : ℝ} (hT : 0 < T) :
    ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin 0 ↦ i.val + 1) W,
        (max (T - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) = T + 1 ∧
      volume.real (Set.weightedSimplex (fun i : Fin 0 ↦ (i : ℝ) + 1)
          ((W : ℝ) + ((0 + 1).choose 2 : ℕ))) *
        (T + (0 : ℕ) - ((W : ℝ) + ((0 + 1).choose 2 : ℕ)) * harmonic 0 / ((0 : ℕ) + 1) +
          (((W : ℝ) + ((0 + 1).choose 2 : ℕ)) ^ 2 * (∑ i : Fin 0, 1 / ((i : ℝ) + 1) ^ 2) /
              (((0 : ℕ) + 1) * ((0 : ℕ) + 2))) /
            (4 * (T + (0 : ℕ) - ((W : ℝ) + ((0 + 1).choose 2 : ℕ)) * harmonic 0 /
              ((0 : ℕ) + 1))) + 1) = T + 1 := by
  have hset : Finset.natWeightedSimplex (fun i : Fin 0 ↦ i.val + 1) W = {![]} := by
    ext c
    simp only [Finset.mem_natWeightedSimplex (fun i : Fin 0 ↦ i.elim0), Finset.mem_singleton,
      Subsingleton.elim c ![]]
    simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    simp [hT.le]
  · rw [volume_real_weightedSimplex_succ 0 (by positivity)]
    simp

/-- The source's `weightedSimplex_centeredRadius_sq_le_harmonic`, in dimension `d - 1` with the
mean `W' * harmonic (d - 1) / d` and the denominator `d * (d + 1)`. The source's hypothesis
`0 < W'` is not needed. -/
example (d : ℕ) (hd : 1 ≤ d) (W' : ℝ) :
    ⨍ u in Set.weightedSimplex (fun i : Fin (d - 1) ↦ (i : ℝ) + 1) W',
        (∑ i, u i - W' * harmonic (d - 1) / d) ^ 2 ≤
      W' ^ 2 * (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / (d * (d + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have h := weightedSimplex_centeredRadius_sq_le_harmonic n W'
  change ⨍ u in Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W',
      (∑ i, u i - W' * harmonic n / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
    W' ^ 2 * (∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) / (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1))
  push_cast
  refine h.trans_eq ?_
  ring

/-- The source's `volume_weightedSimplex_add_choose_le_exp`, in dimension `d - 1` with the budget
`W + r + d.choose 2`. It holds for every `d`, including `d = 0`. -/
example (d W r : ℕ) (hW : 0 < W) :
    volume.real (Set.weightedSimplex (fun i : Fin (d - 1) ↦ (i : ℝ) + 1)
        ((W : ℝ) + r + (d.choose 2 : ℕ))) ≤
      (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + (d.choose 2 : ℕ))) := by
  have h := volume_weightedSimplex_add_choose_le_exp (d - 1) W r hW
  rcases d with _ | d
  · simpa using h
  · simpa using h
