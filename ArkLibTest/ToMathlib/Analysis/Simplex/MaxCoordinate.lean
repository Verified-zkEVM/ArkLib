/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.MaxCoordinate

/-!
# Acceptance cases for the largest coordinate of the standard simplex

Concrete coordinate tails and the necessity of `0 ≤ y` and `y ≤ W`, the union bound and the
exponential tail at small parameters, and the first two moments of the largest coordinate in one
and two dimensions.
-/

open MeasureTheory Set Finset

/-- On the triangle `x₀ + x₁ ≤ 1`, the part where `1 / 2 ≤ x₀` is a triangle of area `1 / 8`. -/
example : volume.real (standardSimplex (Fin 2) 1 ∩ {x | 1 / 2 ≤ x 0}) = 1 / 8 := by
  rw [volume_real_standardSimplex_inter_le_apply 0 (by norm_num) (by norm_num)]
  norm_num [Nat.factorial]

/-- `0 ≤ y` is needed: for `y = -1` the part where `-1 ≤ x₀` is the whole segment `[0, 1]`, of
length `1`, while `(1 - (-1)) ^ 1 / 1! = 2`. -/
example : volume.real (standardSimplex (Fin 1) 1 ∩ {x | -1 ≤ x 0}) ≠
    (1 - (-1)) ^ Fintype.card (Fin 1) / (Fintype.card (Fin 1)).factorial := by
  have hset : standardSimplex (Fin 1) 1 ∩ {x | -1 ≤ x 0} = standardSimplex (Fin 1) 1 :=
    Set.inter_eq_left.2 fun x hx ↦ show -1 ≤ x 0 by linarith [hx.1 0]
  rw [hset, volume_real_standardSimplex _ zero_le_one]
  norm_num

/-- `y ≤ W` is needed: for `W = 0` and `y = 1` the formula `(0 - 1) ^ 1 / 1! = -1` is negative. -/
example : volume.real (standardSimplex (Fin 1) 0 ∩ {x | 1 ≤ x 0}) ≠
    (0 - 1) ^ Fintype.card (Fin 1) / (Fintype.card (Fin 1)).factorial := by
  have h := measureReal_nonneg (μ := volume) (s := standardSimplex (Fin 1) 0 ∩ {x | 1 ≤ x 0})
  norm_num
  linarith

/-- The union bound on the triangle `x₀ + x₁ ≤ 1`: the part where the larger coordinate is at
least `1 / 2` has area at most `2 * (1 / 8)`. It is exactly `1 / 4`: the two corner triangles
meet in a point. -/
example : volume.real (standardSimplex (Fin 2) 1 ∩ {x | 1 / 2 ≤ univ.sup' univ_nonempty x}) ≤
    1 / 4 := by
  refine (volume_real_standardSimplex_inter_le_sup'_le (by norm_num) (by norm_num)).trans ?_
  norm_num [Nat.factorial]

/-- The exponential tail at `t = 0` for one coordinate: the part of `[0, 1]` where `0 < x₀` has
length at most `exp 0 / 1! = 1`. -/
example : volume.real (standardSimplex (Fin 1) 1 ∩
    {x | 0 < (1 : ℕ) * univ.sup' univ_nonempty x - Real.log (1 : ℕ)}) ≤ 1 := by
  simpa using volume_real_standardSimplex_one_inter_lt_mul_sup'_sub_log_le (n := 1) 0

/-- The upper-tail second moment at `a = 0` on `[0, 1]`: `⨍ max (x - 0) 0 ^ 2 ≤ 2`. -/
example : ⨍ x in standardSimplex (Fin 1) 1,
    max ((1 : ℕ) * univ.sup' univ_nonempty x - Real.log (1 : ℕ) - 0) 0 ^ 2 ≤ 2 := by
  simpa using setAverage_standardSimplex_one_max_mul_sup'_sub_log_sub_sq_le (n := 1) 0

/-- The larger coordinate on the triangle `x₀ + x₁ ≤ 1` has mean `harmonic 2 / 3 = 1 / 2`. -/
example : ⨍ x in standardSimplex (Fin 2) 1, univ.sup' univ_nonempty x = 1 / 2 := by
  rw [setAverage_standardSimplex_sup' 2 one_pos]
  norm_num [harmonic, Finset.sum_range_succ]

/-- On the segment `[0, W]` the only coordinate has second moment `W ^ 2 / 3`. -/
example {W : ℝ} (hW : 0 < W) :
    ⨍ x in standardSimplex (Fin 1) W, univ.sup' univ_nonempty x ^ 2 = W ^ 2 / 3 := by
  rw [setAverage_standardSimplex_sup'_sq 1 hW]
  norm_num
  ring
