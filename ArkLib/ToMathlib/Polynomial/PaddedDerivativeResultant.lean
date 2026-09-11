/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.SeparableResultant

/-!
# Padded derivative resultants over a general coefficient domain

Unlike `separableResultant`, which records a polynomial-valued resultant for bivariate degree
counting, this definition allows an arbitrary coefficient domain.  Its declared Sylvester sizes
remain the original sizes `b - 1` and `b` under coefficient specialization.
-/

@[expose] public section

namespace Polynomial

noncomputable section

variable {R L : Type*}

/-- The derivative resultant with the original outer degree supplied explicitly. -/
def paddedDerivativeResultant [CommRing R] (A : R[X]) (b : ℕ) : R :=
  resultant A.derivative A (b - 1) b

/-- Fraction-field separability makes the general padded derivative resultant nonzero. -/
theorem paddedDerivativeResultant_ne_zero_of_map_separable
    [CommRing R] [IsDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (A : R[X]) {b : ℕ} (hdegree : A.natDegree = b)
    (hseparable : (A.map (algebraMap R L)).Separable) :
    paddedDerivativeResultant A b ≠ 0 := by
  let f : R →+* L := algebraMap R L
  let A' : L[X] := A.map f
  have hA'degree : A'.natDegree = b := by
    simpa only [A', f, hdegree] using
      (natDegree_map_eq_of_injective (IsFractionRing.injective R L) A)
  have hderivativeDegree : A'.derivative.natDegree ≤ b - 1 :=
    (natDegree_derivative_le A').trans (Nat.sub_le_sub_right hA'degree.le 1)
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hderivativeDegree
  have hA'ne : A' ≠ 0 := hseparable.ne_zero
  have hleading : A'.coeff b ≠ 0 := by
    rw [← hA'degree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hA'ne
  have hcanonical : resultant A'.derivative A' ≠ 0 :=
    resultant_ne_zero A'.derivative A' hseparable.symm
  have hcanonical' :
      resultant A'.derivative A' A'.derivative.natDegree b ≠ 0 := by
    simpa only [hA'degree] using hcanonical
  have hfieldResultant : resultant A'.derivative A' (b - 1) b ≠ 0 := by
    rw [hc, resultant_add_left_deg A'.derivative A'
      A'.derivative.natDegree b c le_rfl]
    exact mul_ne_zero (mul_ne_zero (by simp) (pow_ne_zero c hleading)) hcanonical'
  have hmap : f (paddedDerivativeResultant A b) =
      resultant A'.derivative A' (b - 1) b := by
    rw [paddedDerivativeResultant, ← resultant_map_map]
    congr 2
    exact (derivative_map A f).symm
  intro hzero
  apply hfieldResultant
  rw [← hmap, hzero, map_zero]

end

end Polynomial
