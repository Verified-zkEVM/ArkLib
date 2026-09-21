/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.WeightedSimplex
import Mathlib.Basic.Real.Basic

/-!
# Acceptance cases for weighted discrete simplices

These small computations check the finite box, weighted count, ordinary stars and bars,
degenerate index set, zero weights, and a finite index other than `Fin`.
-/

open Finset

example : (natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card = 6 := by
  decide

example : (natWeightedSimplex (fun _ : Fin 3 ↦ 1) 2).card = 10 := by
  decide

/-- Unit-weight stars and bars at `n = 3`, `W = 2`, checked against the enumeration. -/
example : (natWeightedSimplex (fun _ : Fin 3 ↦ 1) 2).card = 10 := by
  rw [card_natWeightedSimplex_one]
  decide

/-- The `1, …, n` sandwich at `n = 2`, `W = 3`: its constants reduce to `16 ≤ 4 · 6 ≤ 36`. -/
example : 16 ≤ 4 * (natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card ∧
    4 * (natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card ≤ 36 := by
  have h := natWeightedSimplex_succ_sandwich 2 3
  norm_num [Nat.factorial, Nat.choose] at h
  exact h

/-- The general sandwich at weights `(2, 1)` on `Bool`, `W = 3`, where the count is `6`. -/
example : 16 ≤ 2 * 2 * (natWeightedSimplex (fun b : Bool ↦ if b then 2 else 1) 3).card ∧
    2 * 2 * (natWeightedSimplex (fun b : Bool ↦ if b then 2 else 1) 3).card ≤ 36 := by
  have hlo := succ_pow_le_factorial_mul_prod_mul_card_natWeightedSimplex
    (fun b : Bool ↦ if b then 2 else 1) (by decide) 3
  have hhi := factorial_mul_prod_mul_card_natWeightedSimplex_le
    (fun b : Bool ↦ if b then 2 else 1) 3
  simp only [Fintype.card_bool, Fintype.prod_bool, Fintype.sum_bool] at hlo hhi
  norm_num [Nat.factorial] at hlo hhi
  exact ⟨by omega, by omega⟩

/-- With a zero weight the budget no longer bounds the coordinate: `c = 3` has weighted sum
`0 ≤ 2` but lies outside the box, so `mem_natWeightedSimplex` needs positive weights. -/
example : (∑ i : Fin 1, 0 * (fun _ : Fin 1 ↦ 3) i) ≤ 2 ∧
    (fun _ : Fin 1 ↦ 3) ∉ natWeightedSimplex (fun _ : Fin 1 ↦ 0) 2 := by
  decide

example : (natWeightedSimplex (fun _ : Fin 0 ↦ 1) 0).card = 1 := by
  decide

example : (natWeightedSimplex (fun _ : Fin 1 ↦ 0) 2).card = 3 := by
  decide

example : (natWeightedSimplex (fun b : Bool ↦ if b then 2 else 1) 3).card = 6 := by
  decide

example : ((natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card : ℚ) ≤
    ((3 : ℚ) + ∑ i : Fin 2, (i.val + 1 : ℚ)) ^ 2 /
      ((2 : ℚ) * ∏ i : Fin 2, (i.val + 1 : ℚ)) := by
  simpa [Nat.cast_add] using
    (card_natWeightedSimplex_le (K := ℚ) (fun i : Fin 2 ↦ i.val + 1)
      (fun i ↦ Nat.succ_ne_zero _) 3)

example : ((natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card : ℝ) ≤
    ((3 : ℝ) + ∑ i : Fin 2, (i.val + 1 : ℝ)) ^ 2 /
      ((2 : ℝ) * ∏ i : Fin 2, (i.val + 1 : ℝ)) := by
  simpa [Nat.cast_add] using
    (card_natWeightedSimplex_le (K := ℝ) (fun i : Fin 2 ↦ i.val + 1)
      (fun i ↦ Nat.succ_ne_zero _) 3)
