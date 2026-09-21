/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.WeightedSimplex

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

example : 16 ≤ 2 * 2 * (natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card := by
  decide

example : 2 * 2 * (natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card ≤ 36 := by
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
