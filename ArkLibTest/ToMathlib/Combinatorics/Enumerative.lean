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

/-- Deleting two of five related columns leaves a positive sharp incidence bound. -/
example : #(univ : Finset (Fin 3)) * (3 - #({0, 1} : Finset (Fin 5))) ≤
    ∑ b ∈ (univ : Finset (Fin 5)) \ {0, 1},
      #((univ : Finset (Fin 3)).bipartiteBelow
        (fun _ : Fin 3 => fun b : Fin 5 => b.val < 3) b) := by
  simpa using card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff
    (r := fun _ : Fin 3 => fun b : Fin 5 => b.val < 3)
    (s := univ) (t := univ) ({0, 1} : Finset (Fin 5)) (A := 3)
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

open Classical in
/-- Among the degree-at-most-two exponents in one variable, one lies below `X`. -/
example :
    (#{e ∈ degreeLEFinset (Fin 1) 2 |
      ∀ b ∈ ({single (0 : Fin 1) 1} : Finset (Fin 1 →₀ ℕ)), ¬b ≤ e} : ℤ) =
      ∑ T ∈ ({single (0 : Fin 1) 1} : Finset (Fin 1 →₀ ℕ)).powerset,
        (-1 : ℤ) ^ #T * #{e ∈ degreeLEFinset (Fin 1) 2 | T.sup id ≤ e} := by
  simpa using (card_filter_forall_not_le_degreeLEFinset (σ := Fin 1)
    (B := {single (0 : Fin 1) 1}) 2)

open Classical in
/-- The cone-avoidance polynomial for the cone above `X` counts the degree-two exponents outside
it. -/
example :
    (coneAvoidancePoly ℚ 1 ({single (0 : Fin 1) 1} : Finset (Fin 1 →₀ ℕ))).eval 2 =
      #{e ∈ degreeLEFinset (Fin 1) 2 |
        ∀ b ∈ ({single (0 : Fin 1) 1} : Finset (Fin 1 →₀ ℕ)), ¬b ≤ e} := by
  simpa using (eval_coneAvoidancePoly (K := ℚ) (σ := Fin 1)
    (B := ({single (0 : Fin 1) 1} : Finset (Fin 1 →₀ ℕ))) (N := 2) (by norm_num))

/-- A concrete ratio increases from `9/4` to `8/3` as the deletion count grows. -/
example : ((10 - 1 : ℕ) : ℚ) / (5 - 1 : ℕ) ≤ ((10 - 2 : ℕ) : ℚ) / (5 - 2 : ℕ) :=
  natCast_sub_div_natCast_sub_le (K := ℚ) (by omega) (by omega) (by omega)

/-- The threshold-one incidence factor is `2` for these counts and degree bound. -/
example : (1 : ℚ) ≤ ((((10 - 1 + 1) * 1 : ℕ) : ℚ) / ((5 - 1 + 1 : ℕ) : ℚ)) :=
  one_le_incidenceFactor (n := 10) (A := 5) (T := 1) (b := 1) (by norm_num) (by norm_num)

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

/-- A dimension-sensitive product agrees with its threshold-function form. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 1 2 =
    incidenceProduct 10 5 1 (fun t ↦ 3 - t) 2 :=
  dimensionSensitiveIncidenceProduct_eq_incidenceProduct (by norm_num) (by norm_num) (by norm_num)

/-- The hybrid product agrees with its threshold-function form. -/
example : hybridDimensionSensitiveIncidenceProduct 10 5 2 3 1 2 =
    incidenceProduct 10 5 1 (fun t ↦ if t = 0 then 2 else 3 + 1 - t) 2 :=
  hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct 10 5 2 3 1 2

/-- The dimension-one incidence product is bounded by its first factor. -/
example : dimensionSensitiveIncidenceProduct 10 5 3 1 1 ≤
    ((10 - 3 + 1 : ℕ) : ℚ) / (5 - 3 + 1 : ℕ) :=
  dimensionSensitiveIncidenceProduct_le_one (by norm_num) (by norm_num)
