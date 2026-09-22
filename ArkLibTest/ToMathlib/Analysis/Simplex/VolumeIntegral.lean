/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.VolumeIntegral

/-!
# Acceptance cases for the Dirichlet integral on the standard simplex

Concrete Dirichlet integrals and volumes, an index type other than `Fin`, the empty index type,
the necessity of `0 ≤ L`, and the `Fin n` statements derived from the general ones.
-/

open MeasureTheory Set

/-- `∫ x₀ (1 - x₀ - x₁)` over the unit triangle is `1 / 24`. -/
example : (∫ x in standardSimplex (Fin 2) 1,
    (∏ i, x i ^ (![1, 0] : Fin 2 → ℕ) i) * (1 - ∑ i, x i) ^ 1) = 1 / 24 := by
  rw [integral_standardSimplex_prod_pow_mul_pow _ _ zero_le_one]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, Nat.factorial]

/-- The tetrahedron of side `2` has volume `2³ / 3! = 4 / 3`. -/
example : volume.real (standardSimplex (Fin 3) 2) = 4 / 3 := by
  rw [volume_real_standardSimplex _ zero_le_two, Fintype.card_fin]
  norm_num [Nat.factorial]

/-- An index type other than `Fin`: the triangle in `Bool → ℝ` of budget `1` has area `1 / 2`. -/
example : volume.real (standardSimplex Bool 1) = 1 / 2 := by
  rw [volume_real_standardSimplex _ zero_le_one, Fintype.card_bool]
  norm_num [Nat.factorial]

/-- The empty index type: the simplex is a point and the integrand is the slack power `L ^ b`. -/
example : (∫ x in standardSimplex (Fin 0) 3,
    (∏ i, x i ^ (Fin.elim0 : Fin 0 → ℕ) i) * (3 - ∑ i, x i) ^ 2) = 9 := by
  rw [integral_standardSimplex_prod_pow_mul_pow _ _ (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num [Nat.factorial]

/-- The Fubini recurrence at `Fin 1`, with the zero-dimensional volume as the inner integral:
the segment `[0, 5]` has length `5`. -/
example : (∫ _ in standardSimplex (Fin 1) 5, (1 : ℝ)) = 5 := by
  rw [setIntegral_standardSimplex_succ (continuousOn_const.integrableOn_standardSimplex)]
  have h : ∀ x : ℝ, (∫ _ in standardSimplex (Fin 0) (5 - x), (1 : ℝ)) =
      volume.real (standardSimplex (Fin 0) (5 - x)) := fun x ↦ by simp
  simp only [h]
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ))]
  · simp
  intro x hx
  rw [uIcc_of_le (by norm_num)] at hx
  dsimp only
  rw [volume_real_standardSimplex _ (by linarith [hx.2])]
  simp

/-- The hypothesis `0 ≤ L` is needed: at `L = -1` the empty-index simplex is empty, so its
volume is `0`, while the formula `L ^ 0 / 0!` gives `1`. -/
example : volume.real (standardSimplex (Fin 0) (-1)) = 0 ∧
    (-1 : ℝ) ^ Fintype.card (Fin 0) / (Fintype.card (Fin 0)).factorial = 1 := by
  refine ⟨?_, by simp⟩
  rw [standardSimplex_eq_empty (by norm_num)]
  simp

/-- The Dirichlet integral on `Fin n`, with the factorial product cast from `ℕ`. -/
example (n : ℕ) (a : Fin n → ℕ) (b : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex (Fin n) L, (∏ i, x i ^ a i) * (L - ∑ i, x i) ^ b) =
      L ^ (n + ∑ i, a i + b) *
        (((∏ i, (a i).factorial : ℕ) : ℝ) * b.factorial /
          (n + ∑ i, a i + b).factorial) := by
  rw [integral_standardSimplex_prod_pow_mul_pow a b hL, Fintype.card_fin]
  push_cast
  rfl

/-- The volume of the standard simplex on `Fin n`. -/
example (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    volume.real (standardSimplex (Fin n) L) = L ^ n / n.factorial := by
  rw [volume_real_standardSimplex _ hL, Fintype.card_fin]
