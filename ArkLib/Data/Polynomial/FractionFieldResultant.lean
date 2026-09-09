/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Separability resultants over a fraction field

The derivative resultant padded to degrees `d` and `d - 1` is nonzero whenever the
polynomial becomes separable over its fraction field. The derivative may have degree
strictly below `d - 1`, as happens for `Y^p - Y` in characteristic `p`.
The actual-degree resultant also provides a Bezout certificate after arbitrary coefficient
maps, including maps that lower polynomial degrees.

This generalizes the large-characteristic argument in Remco Bloemen's BCHKS formalization,
`ProximityPrize/SubmissionLower/BCHKSConcreteGoodSpecialization.lean`, lines 272–316, at
https://github.com/proximity-prize/proximity-prize/commit/19bc7d3e21b2261257e1961acd720b2c395d87e1.
The proof uses Mathlib's padding identity instead of requiring that differentiation retain
the leading term. No donor proof is copied.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {R K : Type*} [CommRing R]

/-- Padding the derivative degree preserves the nonzero resultant of a separable polynomial.
This also covers nonzero constant polynomials, where both dimensions are zero. -/
theorem resultant_derivative_ne_zero_of_separable [IsDomain R] (f : R[X]) (hsep : f.Separable) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
  have hf : f ≠ 0 := hsep.ne_zero
  have hdegree := natDegree_derivative_le f
  rw [← Nat.add_sub_of_le hdegree,
    resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf))
    (resultant_ne_zero f f.derivative hsep)

variable [Field K]

/-- The original resultant provides a coprimality certificate after any coefficient map to a
field where its value remains nonzero. No preservation of degrees under the map is required. -/
theorem isCoprime_map_of_resultant_ne_zero (φ : R →+* K) (f g : R[X])
    (hdegree : 0 < f.natDegree + g.natDegree) (hres : φ (resultant f g) ≠ 0) :
    IsCoprime (f.map φ) (g.map φ) := by
  obtain ⟨a, b, _, _, hab⟩ :=
    exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (by omega)
  have hmap := congrArg (Polynomial.map φ) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C] at hmap
  refine ⟨C ((φ (resultant f g))⁻¹) * a.map φ,
    C ((φ (resultant f g))⁻¹) * b.map φ, ?_⟩
  calc
    _ = C ((φ (resultant f g))⁻¹) * (f.map φ * a.map φ + g.map φ * b.map φ) := by ring
    _ = 1 := by rw [hmap]; simp [← C_mul, hres]

/-- Nonvanishing of the original derivative resultant after specialization is sufficient for
separability, including specializations where the outer polynomial degree drops. -/
theorem separable_map_of_resultant_derivative_ne_zero (φ : R →+* K) (f : R[X])
    (hdegree : 0 < f.natDegree) (hres : φ (resultant f f.derivative) ≠ 0) :
    (f.map φ).Separable := by
  rw [separable_def, derivative_map]
  exact isCoprime_map_of_resultant_ne_zero φ f f.derivative
    (hdegree.trans_le (Nat.le_add_right _ _)) hres

/-- Separability over the fraction field gives a nonzero actual-degree derivative resultant
in the coefficient domain. This does not assert a Bezout identity equal to one over that domain. -/
theorem resultant_derivative_ne_zero_of_fractionField_separable
    [Algebra R K] [IsFractionRing R K] (f : R[X])
    (hf : (f.map (algebraMap R K)).Separable) : resultant f f.derivative ≠ 0 := by
  have hres := resultant_ne_zero (f.map (algebraMap R K))
    (f.map (algebraMap R K)).derivative hf
  rw [derivative_map] at hres
  simp only [natDegree_map_eq_of_injective (IsFractionRing.injective R K),
    resultant_map_map] at hres
  exact fun h ↦ hres (by simp [h])

variable [Algebra R K] [IsFractionRing R K]

/-- Fraction-field separability gives a nonzero derivative resultant in the original domain.
No ring-level Bezout identity or restriction on the characteristic is assumed. -/
theorem resultant_derivative_ne_zero_of_separable_map_fractionField (f : R[X])
    (hsep : (f.map (algebraMap R K)).Separable) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
  have hdeg : (f.map (algebraMap R K)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (IsFractionRing.injective R K) f
  have hne := resultant_derivative_ne_zero_of_separable _ hsep
  rw [hdeg, derivative_map, resultant_map_map] at hne
  exact fun hz => hne (by rw [hz, map_zero])

end Polynomial
