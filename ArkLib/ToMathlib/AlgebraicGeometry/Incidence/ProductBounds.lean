/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.DimensionSensitive
/-!
# Extending dimension-sensitive products

Coefficient-space dimension bounds are essential before comparing a hybrid product with
its untruncated form. Below the coefficient dimension they agree exactly; after capping
the actual dimension there, monotonicity extends the untruncated product to any requested
upper bound. In particular, no lower bound on the code dimension is needed.
-/

@[expose] public section

namespace AffineHilbert

/-- Increasing the dimension increases the untruncated incidence product. -/
theorem dimensionSensitiveIncidenceProduct_mono_dimension
    (n A k b r s : ℕ) (hAn : A ≤ n) (hb : 0 < b) (hrs : r ≤ s) :
    dimensionSensitiveIncidenceProduct n A k b r ≤
      dimensionSensitiveIncidenceProduct n A k b s := by
  apply monotone_nat_of_le_succ ?_ hrs
  intro d
  rw [dimensionSensitiveIncidenceProduct_succ]
  apply le_mul_of_one_le_right (dimensionSensitiveIncidenceProduct_nonneg n A k b d)
  rw [one_le_div₀ (by positivity)]
  exact_mod_cast (show A - k + d + 1 ≤ (n - k + d + 1) * b from
    (by omega : A - k + d + 1 ≤ n - k + d + 1).trans (Nat.le_mul_of_pos_right _ hb))

/-- Below the coefficient dimension, split off the joint factor exactly. -/
theorem hybridDimensionSensitiveIncidenceProduct_eq_factor_mul
    (n A L k b s : ℕ) (hkA : k ≤ A) (hAn : A ≤ n) (hsk : s ≤ k) :
    hybridDimensionSensitiveIncidenceProduct n A L k b (s + 1) =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k b s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [hybridDimensionSensitiveIncidenceProduct_succ, ih (by omega),
      dimensionSensitiveIncidenceProduct_succ]
    have hnEq : n - (if s + 1 = 0 then L else k + 1 - (s + 1)) + 1 = n - k + s + 1 := by
      simp only [show s + 1 ≠ 0 by omega, if_false]
      omega
    have hAEq : A - (if s + 1 = 0 then L else k + 1 - (s + 1)) + 1 = A - k + s + 1 := by
      simp only [show s + 1 ≠ 0 by omega, if_false]
      omega
    rw [hnEq, hAEq, mul_assoc]

/-- Cap the actual dimension before extending the untruncated product. -/
theorem hybridDimensionSensitiveIncidenceProduct_min_le
    (n A L k b r : ℕ) (hkA : k ≤ A) (hAn : A ≤ n) (hb : 0 < b) :
    hybridDimensionSensitiveIncidenceProduct n A L k b (min r k + 1) ≤
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k b r := by
  rw [hybridDimensionSensitiveIncidenceProduct_eq_factor_mul n A L k b _ hkA hAn
    (Nat.min_le_right _ _)]
  exact mul_le_mul_of_nonneg_left
    (dimensionSensitiveIncidenceProduct_mono_dimension n A k b _ _ hAn hb
      (Nat.min_le_left _ _)) (by positivity)
/-- A fixed-threshold power remains a valid coarser bound for the evaluation product. -/
theorem dimensionSensitiveIncidenceProduct_le_first_pow
    (n A k r : ℕ) (hkA : k ≤ A) (hAn : A ≤ n) :
    dimensionSensitiveIncidenceProduct n A k 1 r ≤
      (((n-k+1 : ℕ) : ℚ) / (A-k+1 : ℕ)) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [dimensionSensitiveIncidenceProduct_succ, pow_succ]
    apply mul_le_mul ih _ (by positivity) (by positivity)
    simp only [Nat.mul_one]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast [Nat.cast_sub hkA, Nat.cast_sub (hkA.trans hAn)]
    have hdiff : (0 : ℚ) ≤ n - A := sub_nonneg.mpr (by exact_mod_cast hAn)
    have hh := mul_nonneg hdiff (show (0 : ℚ) ≤ r by positivity)
    nlinarith
end AffineHilbert
