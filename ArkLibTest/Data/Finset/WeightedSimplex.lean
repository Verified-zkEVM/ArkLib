/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.WeightedSimplex
import ArkLib.Data.Finset.WeightedSimplex.FloorTransfer
import ArkLib.Data.Finset.WeightedSimplex.Moments
import ArkLib.Data.Finset.WeightedSimplex.RankIntegral
import ArkLib.Data.Finset.WeightedSimplex.Variance
import Mathlib.Basic.Real.Basic

/-!
# Acceptance cases for weighted discrete simplices

These small computations check the finite box, weighted count, ordinary stars and bars,
exact-simplex and `Finsupp` bridges, shell decomposition, degenerate index set, zero weights, and a
finite index other than `Fin`.
-/

open Finset
open MeasureTheory
open scoped BigOperators

example : (natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 3).card = 6 := by
  decide

/-- The slack-coordinate exact-simplex equivalence is executable through the ordinary public
import, including at an index type other than `Fin`. The unused unit of budget becomes the `none`
coordinate. -/
example :
    ((natWeightedSimplexOneEquivExact (σ := Bool) 2)
      ⟨fun b ↦ if b then 1 else 0, by decide⟩).1 none = 1 := by
  decide

/-- The inverse exact-simplex map discards the slack coordinate and recovers the original tuple. -/
example :
    ((natWeightedSimplexOneEquivExact (σ := Bool) 2).symm
      ⟨fun i ↦ i.elim 1 (fun b ↦ if b then 1 else 0), by decide⟩).1 true = 1 := by
  decide

/-- The bounded canonical `Finsupp` representation has the same count as the executable tuple
simplex. -/
example : Nat.card
    {c : Bool →₀ ℕ // c.weight (fun b ↦ if b then 2 else 1) ≤ 3} = 6 := by
  rw [card_finsupp_weight_le_eq_card_natWeightedSimplex _ (by decide)]
  decide

/-- The exact shell of weight three for weights `(2, 1)` consists of `(1, 1)` and `(0, 3)`. -/
example : (natWeightedSimplexShell (fun b : Bool ↦ if b then 2 else 1) 3).card = 2 := by
  decide

example : Nat.card
    {c : Bool →₀ ℕ // c.weight (fun b ↦ if b then 2 else 1) = 3} = 2 := by
  rw [card_finsupp_weight_eq_card_natWeightedSimplexShell _ (by decide)]
  decide

/-- The weighted simplex count is the sum of its exact shells. -/
example : (natWeightedSimplex (fun b : Bool ↦ if b then 2 else 1) 3).card =
    ∑ t ∈ range 4, (natWeightedSimplexShell (fun b : Bool ↦ if b then 2 else 1) t).card := by
  exact card_natWeightedSimplex_eq_sum_card_shell _ (by decide) 3

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

/-- The same zero-weight boundary is visible for shells: the exact weighted-sum equation holds,
but the executable shell at weight zero deliberately keeps only the coordinate-box value zero. -/
example : (∑ i : Fin 1, 0 * (fun _ : Fin 1 ↦ 1) i) = 0 ∧
    (fun _ : Fin 1 ↦ 1) ∉ natWeightedSimplexShell (fun _ : Fin 1 ↦ 0) 0 := by
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

example : (fun _ : Fin 1 ↦ 0) ∈
    natWeightedSimplex (fun _ : Fin 1 ↦ 1) 1 := by
  simpa [Nat.floor_zero] using natFloor_mem_natWeightedSimplex
    (w := fun _ : Fin 1 ↦ 1) (W := (1 : ℝ)) (x := fun _ ↦ (0 : ℝ))
    (fun _ ↦ one_ne_zero)
    (Set.mem_weightedSimplex.mpr ⟨fun _ ↦ by norm_num, by norm_num⟩)

/-- The unit floor cell of the zero lattice point fits in the enlarged one-dimensional simplex. -/
example :
    MeasureTheory.natFloorCell (fun _ : Unit ↦ 0) ⊆
      Set.weightedSimplex (fun _ : Unit ↦ (1 : ℝ)) 1 := by
  simpa using (natFloorCell_subset_weightedSimplex
    (w := fun _ : Unit ↦ 1) (W := 0) (c := fun _ ↦ 0) (by decide))

/-- The integral of one over the one-dimensional budget-one simplex is bounded by its two cells. -/
example :
    ∫ _x in MeasureTheory.natFloorCell (fun _ : Unit ↦ 0), (1 : ℝ) ∂volume ≤
      ∑ _c ∈ natWeightedSimplex (fun _ : Unit ↦ 1) 1, (1 : ℝ) := by
  have hTW : MeasureTheory.natFloorCell (fun _ : Unit ↦ 0) ⊆
      Set.weightedSimplex (fun _ : Unit ↦ (1 : ℝ)) 1 := by
    intro x hx
    refine Set.mem_weightedSimplex.mpr ⟨?_, ?_⟩
    · intro i
      simpa using (MeasureTheory.mem_natFloorCell.mp hx i).1
    · have hupper : x () ≤ 1 := by
        simpa using (MeasureTheory.mem_natFloorCell.mp hx ()).2.le
      simpa using hupper
  simpa using setIntegral_le_sum_natWeightedSimplex (w := fun _ : Unit ↦ 1) (W := (1 : ℝ))
    (T := MeasureTheory.natFloorCell (fun _ ↦ 0)) (f := fun _ ↦ (1 : ℝ)) (g := fun _ ↦ 1)
    (fun _ ↦ one_ne_zero) (MeasureTheory.measurableSet_natFloorCell _) (by simpa using hTW)
    (integrableOn_const (by rw [MeasureTheory.volume_natFloorCell]; simp))
    (by intro c hc; norm_num) (by intro x hx; norm_num)

/-- The two budget-one lattice points contribute inside the enlarged one-dimensional simplex. -/
example :
    ∑ _c ∈ natWeightedSimplex (fun _ : Unit ↦ 1) 1, (1 : ℝ) ≤
      ∫ _x in Set.weightedSimplex (fun _ : Unit ↦ (1 : ℝ))
        ((1 : ℝ) + ∑ _i : Unit, (1 : ℝ)), (1 : ℝ) ∂volume := by
  simpa using sum_natWeightedSimplex_le_setIntegral (w := fun _ : Unit ↦ 1) 1
    (f := fun _ ↦ (1 : ℝ)) (g := fun _ ↦ 1)
    (continuousOn_const.integrableOn_weightedSimplex (fun _ ↦ by norm_num))
    (by intro x hx; norm_num) (by intro _c _hc _x _hx; norm_num)

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true = 10 := by
  have h := card_add_one_mul_sum_natWeightedSimplex_one_apply (σ := Bool) true 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * c false = 5 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_of_ne
    (show true ≠ false by decide) 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * (c true - 1) = 10 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred true 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 2,
    ((c true : ℤ) - (c false : ℤ)) ^ 2 = 10 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_weighted_sq
    (fun b : Bool ↦ if b then (1 : ℤ) else -1) 2
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool, Fintype.sum_bool] at h
  norm_num [Nat.choose] at h
  simp only [← sub_eq_add_neg] at h
  omega

example : 𝔼 c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2,
    ∑ i, (![1, 1 / 2] : Fin 2 → ℚ) i * (c i : ℚ) = 1 := by
  rw [expect_natWeightedSimplex_one_weighted]
  norm_num [natSimplexWeightedMean, Fin.sum_univ_succ]

example : 𝔼 c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2,
    (∑ i, (![1, 1 / 2] : Fin 2 → ℚ) i * (c i : ℚ) - 1) ^ 2 = 5 / 12 := by
  have hMean : natSimplexWeightedMean 2 (![1, 1 / 2] : Fin 2 → ℚ) = 1 := by
    norm_num [natSimplexWeightedMean, Fin.sum_univ_succ]
  have h := expect_natWeightedSimplex_one_weighted_sub_sq (![1, 1 / 2] : Fin 2 → ℚ) 2
  rw [hMean] at h
  rw [h]
  norm_num [natSimplexWeightedVariance, Fin.sum_univ_succ]

example : (1 : ℝ) ≤ 19 / 12 := by
  have h := sum_natWeightedSimplex_max_sub_add_one_le (w := fun _ : Fin 1 ↦ 1)
    (fun _ ↦ one_ne_zero) 0 (a := 1) (fun _ ↦ zero_le_one) (T := 0) (by norm_num)
  have hset : natWeightedSimplex (fun _ : Fin 1 ↦ 1) 0 = {fun _ ↦ 0} := by decide
  rw [hset, volume_real_weightedSimplex (fun _ ↦ by norm_num) (by norm_num)] at h
  norm_num at h
  linarith
