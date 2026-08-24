/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Powers

/-!
# Gao--Kopparty--Lovett affine-line MCA bound

This file derives the affine-line 1.5-Johnson bound by specializing the univariate-powers
MCA theorem.

## Main result

- `linear_mcaError_le_one_point_five_johnson` is [GaoKL24, Theorem 3].

## References

- [GaoKL24] Theorem 3.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- Bounds affine-line MCA error below the 1.5-Johnson radius of a linear code. -/
theorem linear_mcaError_le_one_point_five_johnson
    (C : LinearCode ι F) (δ_min η δ : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_δ_min : η < δ_min)
    (_hδ_pos : 0 < δ)
    (_hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      ENNReal.ofReal
        ((((Fintype.card ι : ℝ) + 6) / η
          + 2 / ((η : ℝ) *
              ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))
         ) / (Fintype.card F : ℝ)) := by
  classical
  let x : ℝ := 1 - (δ_min : ℝ) + (η : ℝ)
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hq_pos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hη_pos : (0 : ℝ) < (η : ℝ) := by exact_mod_cast _hη
  have hη_lt : (η : ℝ) < (δ_min : ℝ) := by exact_mod_cast _hη_lt_δ_min
  have hdmin_le : Code.minDist (C : Set (ι → F)) ≤ Fintype.card ι := by
    rw [← Code.dist_eq_minDist]
    exact Code.dist_le_card _
  have hδmin_le_one : (δ_min : ℝ) ≤ 1 := by
    rw [_h_δ_min]
    apply (div_le_one hn_pos).2
    exact_mod_cast hdmin_le
  have hx_pos : 0 < x := by
    dsimp only [x]
    linarith
  have hx_lt_one : x < 1 := by
    dsimp only [x]
    linarith
  have hdiff_pos :
      0 < x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2) := by
    apply sub_pos.mpr
    exact Real.rpow_lt_rpow_of_exponent_gt hx_pos hx_lt_one (by norm_num)
  have hsqrt_nonneg : 0 ≤ x ^ ((1 : ℝ) / 2) := by positivity
  have hgen : univariatePowersGenerator F 1 = AffineLineGenerator F := by
    funext y i
    fin_cases i <;> simp [univariatePowersGenerator, AffineLineGenerator]
  have hpow := linear_mcaError_powers_le (C := C) (k := 1) δ_min η δ
    (by omega) (by exact Fintype.one_lt_card) _h_δ_min _hη _hη_lt_δ_min
    (by
      convert _hδ using 1
      all_goals norm_num)
  norm_num at hpow
  rw [hgen] at hpow
  refine hpow.trans ?_
  apply ENNReal.ofReal_le_ofReal
  change
    (Fintype.card ι : ℝ) * (1 - x ^ ((1 : ℝ) / 2)) / (η : ℝ) *
          (Fintype.card F : ℝ)⁻¹ +
        max
          (2 / ((η : ℝ) *
              (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)) *
              (Fintype.card F : ℝ)))
          (6 / ((η : ℝ) * (Fintype.card F : ℝ))) ≤
      (((Fintype.card ι : ℝ) + 6) / (η : ℝ) +
          2 / ((η : ℝ) *
            (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)))) /
        (Fintype.card F : ℝ)
  have hbase :
      (Fintype.card ι : ℝ) * (1 - x ^ ((1 : ℝ) / 2)) / (η : ℝ) ≤
        (Fintype.card ι : ℝ) / (η : ℝ) := by
    apply (div_le_div_iff_of_pos_right hη_pos).2
    have hn_nonneg : (0 : ℝ) ≤ Fintype.card ι := le_of_lt hn_pos
    nlinarith [mul_nonneg hn_nonneg hsqrt_nonneg]
  have hfirst :
      (Fintype.card ι : ℝ) * (1 - x ^ ((1 : ℝ) / 2)) / (η : ℝ) *
          (Fintype.card F : ℝ)⁻¹ ≤
        (Fintype.card ι : ℝ) / (η : ℝ) / (Fintype.card F : ℝ) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hbase (by positivity)
  have ha_nonneg :
      0 ≤ 2 / ((η : ℝ) *
        (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)) *
        (Fintype.card F : ℝ)) := by positivity
  have hb_nonneg : 0 ≤ 6 / ((η : ℝ) * (Fintype.card F : ℝ)) := by positivity
  have hmax :
      max
          (2 / ((η : ℝ) *
              (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)) *
              (Fintype.card F : ℝ)))
          (6 / ((η : ℝ) * (Fintype.card F : ℝ))) ≤
        2 / ((η : ℝ) *
              (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)) *
              (Fintype.card F : ℝ)) +
          6 / ((η : ℝ) * (Fintype.card F : ℝ)) := by
    apply max_le
    · exact le_add_of_nonneg_right hb_nonneg
    · exact le_add_of_nonneg_left ha_nonneg
  calc
    (Fintype.card ι : ℝ) * (1 - x ^ ((1 : ℝ) / 2)) / (η : ℝ) *
          (Fintype.card F : ℝ)⁻¹ +
        max
          (2 / ((η : ℝ) *
              (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)) *
              (Fintype.card F : ℝ)))
          (6 / ((η : ℝ) * (Fintype.card F : ℝ))) ≤
        (Fintype.card ι : ℝ) / (η : ℝ) / (Fintype.card F : ℝ) +
          (2 / ((η : ℝ) *
              (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)) *
              (Fintype.card F : ℝ)) +
            6 / ((η : ℝ) * (Fintype.card F : ℝ))) := add_le_add hfirst hmax
    _ = (((Fintype.card ι : ℝ) + 6) / (η : ℝ) +
          2 / ((η : ℝ) *
            (x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2)))) /
        (Fintype.card F : ℝ) := by
      field_simp
      ring

end General

end CodingTheory
