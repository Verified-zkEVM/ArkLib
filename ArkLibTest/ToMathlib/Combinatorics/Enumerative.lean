/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting
import ArkLib.ToMathlib.Combinatorics.Enumerative.IncidenceProduct
import ArkLib.ToMathlib.Combinatorics.Enumerative.MonomialCount
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for combinatorial counting bounds
-/

open Finset Finsupp

/-- Deleting two positions from `range 6` loses at most two even incidences. -/
example : #((range 6).bipartiteAbove (fun (_ : ℕ) b ↦ b % 2 = 0) 0) - #({2, 3} : Finset ℕ) ≤
    #(((range 6) \ {2, 3}).bipartiteAbove (fun (_ : ℕ) b ↦ b % 2 = 0) 0) :=
  card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff _ _ _ _

/-- The sharp deletion estimate on a concrete relation with `s = {0, 1, 2}`. -/
example : #({0, 1, 2} : Finset ℕ) * (1 - #({5, 6} : Finset ℕ)) ≤
    ∑ b ∈ ({0, 1, 2} : Finset ℕ) \ {5, 6},
      #(({0, 1, 2} : Finset ℕ).bipartiteBelow (fun a b : ℕ ↦ a = b) b) := by
  apply card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff
  intro a ha
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> decide

/-- A concrete full relation attains the complement deletion bound. -/
example :
    #(univ : Finset (Fin 3)) * (5 - #({0, 1} : Finset (Fin 5))) ≤
      ∑ b ∈ ({0, 1} : Finset (Fin 5))ᶜ,
        #((univ : Finset (Fin 3)).bipartiteBelow (fun _ : Fin 3 => fun _ : Fin 5 => True) b) :=
  card_mul_sub_card_le_sum_compl_card_bipartiteBelow
    (r := fun _ : Fin 3 => fun _ : Fin 5 => True) (u := {0, 1}) (A := 5)
    (by intro a ha; fin_cases a <;> decide)

/-- Root dependent exceptional sets give the expected bound on the concrete full ranges. -/
example : #(range 3) * (#(range 5) - 1) ≤ #(range 5) * 3 :=
  card_mul_sub_le_card_mul_of_card_bad_le (fun a b : ℕ ↦ b ≠ a) (fun a ↦ {a})
    (fun _ _ ↦ by simp) (fun a _ b _ hb ↦ by simpa using hb)
    fun b _ ↦ (card_filter_le _ _).trans (by simp)

/-- There are six exponent vectors of degree at most two in two variables. -/
example : #(degreeLEFinset (Fin 2) 2) = 6 := by
  rw [card_degreeLEFinset]
  decide

/-- Three degree-three exponent vectors lie above `X₀ X₁` in two variables. -/
example : #{e ∈ degreeLEFinset (Fin 2) 3 | single 0 1 + single 1 1 ≤ e} = 3 := by
  rw [card_filter_le_degreeLEFinset _ (by simp)]
  simp

/-- A concrete ratio increases from `9/4` to `8/3` as the deletion count grows. -/
example : ((10 - 1 : ℕ) : ℚ) / (5 - 1 : ℕ) ≤ ((10 - 2 : ℕ) : ℚ) / (5 - 2 : ℕ) :=
  natCast_sub_div_natCast_sub_le (K := ℚ) (by omega) (by omega) (by omega)

/-- With `δ = 1 / 2`, `x = 4`, `y = 2`, and offset `3`, the shifted ratio is at most `2`. -/
example : ((4 + 3 + 1 : ℕ) : ℚ) / ((2 + 3 + 1 : ℕ) : ℚ) ≤ 1 / (1 / 2 : ℚ) :=
  natCast_shiftedRatio_le_one_div (1 / 2 : ℚ) (by norm_num) (by norm_num) 4 2 3 (by norm_num)

/-- The incidence factor is at least one for these concrete counts and degree bound. -/
example : (1 : ℚ) ≤ ((((3 - 5 + 1) * 1 : ℕ) : ℚ) / ((2 - 5 + 1 : ℕ) : ℚ)) :=
  one_le_incidenceFactor (by norm_num) one_pos

/-- A lower-threshold incidence ratio is bounded by its concrete incidence factor. -/
example : (((10 - 1) * 1 : ℕ) : ℚ) ≤
    ((((10 - 3 + 1) * 1 : ℕ) : ℚ) / ((5 - 3 + 1 : ℕ) : ℚ)) * ((5 - 1 : ℕ) : ℚ) :=
  natCast_sub_mul_le_incidenceFactor_mul (by omega) (by omega) (by omega)

/-- A constant threshold makes the incidence product a power. -/
example : incidenceProduct 10 5 1 (fun _ ↦ 2) 3 = (9 / 4 : ℚ) ^ 3 :=
  incidenceProduct_const 10 5 1 2 3

/-- The incidence product is monotone in dimension for concrete valid parameters. -/
example : incidenceProduct 10 5 1 (fun t ↦ 7 * t) 2 ≤
    incidenceProduct 10 5 1 (fun t ↦ 7 * t) 5 :=
  incidenceProduct_mono_dimension _ (by norm_num) one_pos (by norm_num)

/-- The dimension-sensitive product contributes the degree factor `2 ^ 2`. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 2 2 = 24 := by
  rw [dimensionSensitiveIncidenceProduct_eq_pow_mul]
  norm_num [dimensionSensitiveIncidenceProduct]

/-- With a half-gap between `k = 2` and `A = 7`, the degree-one product through dimension two
is at most `4`. -/
example :
    dimensionSensitiveIncidenceProduct 10 7 2 1 2 ≤ (1 / (1 / 2 : ℚ)) ^ 2 :=
  dimensionSensitiveIncidenceProduct_le_one_div_pow_of_gap (1 / 2 : ℚ) 10 2 7 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The dimension-sensitive product is monotone between dimensions one and two. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 1 1 ≤
    dimensionSensitiveIncidenceProduct 10 5 3 1 2 :=
  dimensionSensitiveIncidenceProduct_mono_dimension (by norm_num) one_pos (by norm_num)

/-- The degree-one dimension-sensitive product through dimension two is at most its first-factor
square. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 1 2 ≤
    (((10 - 3 + 1 : ℕ) : ℚ) / ((5 - 3 + 1 : ℕ) : ℚ)) ^ 2 :=
  dimensionSensitiveIncidenceProduct_le_first_pow 10 5 3 2 (by norm_num) (by norm_num)

/-- A dimension-sensitive product agrees with its threshold-function form. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 1 2 =
    incidenceProduct 10 5 1 (fun t ↦ 3 - t) 2 :=
  dimensionSensitiveIncidenceProduct_eq_incidenceProduct (by norm_num) (by norm_num) (by norm_num)

/-- The hybrid product agrees with its threshold-function form. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 2 =
    incidenceProduct 10 5 1 (fun t ↦ if t = 0 then 2 else 3 + 1 - t) 2 :=
  hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct 10 5 2 3 1 2

/-- The hybrid product is monotone between dimensions one and two. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 1 ≤
    hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 2 :=
  hybridDimensionSensitiveIncidenceProduct_mono_dimension (by norm_num) one_pos (by norm_num)

/-- Through dimension three, the hybrid product splits into its first factor and two later
dimension-sensitive factors. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 3 =
    ((((10 - 2 + 1) * 1 : ℕ) : ℚ) / ((5 - 2 + 1 : ℕ) : ℚ)) *
      dimensionSensitiveIncidenceProduct 10 5 3 1 2 :=
  hybridDimensionSensitiveIncidenceProduct_eq_factor_mul 10 5 2 3 1 2
    (by norm_num) (by norm_num) (by norm_num)

/-- Capping the hybrid dimension at `k` bounds it by its first factor and the full product. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 (min 5 3 + 1) ≤
    ((((10 - 2 + 1) * 1 : ℕ) : ℚ) / ((5 - 2 + 1 : ℕ) : ℚ)) *
      dimensionSensitiveIncidenceProduct 10 5 3 1 5 :=
  hybridDimensionSensitiveIncidenceProduct_min_le 10 5 2 3 1 5
    (by norm_num) (by norm_num) one_pos

/-- The dimension-sensitive product in dimension at most one is bounded by its first factor. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 1 0 ≤
    ((10 - 3 + 1 : ℕ) : ℚ) / (5 - 3 + 1 : ℕ) :=
  dimensionSensitiveIncidenceProduct_le_one (by norm_num) (by norm_num)

/-- The hybrid product through dimension one is bounded by its first two factors. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 1 ≤
    ((((10 - 2 + 1) * 1 : ℕ) : ℚ) / ((5 - 2 + 1 : ℕ) : ℚ)) *
      ((((10 - 3 + 1) * 1 : ℕ) : ℚ) / ((5 - 3 + 1 : ℕ) : ℚ)) :=
  hybridDimensionSensitiveIncidenceProduct_le_two (by norm_num) (by norm_num) one_pos
