/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.SpecializationDegree
/-!
# Canaries for exact interpolation specialization degree

The zero-vector example pins the truncated natural-degree boundary.  The order-one example
reconstructs `X² Y₁³` from a single exact interpolation coefficient: with `P = X⁵`, its
specialization has degree fourteen, exactly the predecessor of the strict budget fifteen.
-/

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

noncomputable section

open Polynomial

/-- The exact coefficient vector can represent zero, whose specialization has natural degree
zero.  Thus a strict theorem at budget zero would be false. -/
theorem exactInterpolation_zero_specialization_canary :
    let hdD : 1 < 2 := by decide
    let c : ExactInterpolationCoefficients ℚ 2 0 1 1 0 0 hdD := 0
    (differentialSpecialization
      (exactInterpolationPolynomial hdD c : DifferentialPolynomial ℚ 1) 0).natDegree = 0 := by
  simp [differentialSpecialization]

/-- Exponent of the tight order-one monomial `X² Y₁³`. -/
private def tightOrderOneExponent : JetVariable 1 →₀ ℕ :=
  Finsupp.single none 2 + Finsupp.single (some (Fin.last 1)) 3

/-- At weights `(1, 5, 4)`, the test monomial has weight fourteen and lies immediately below the
strict budget fifteen. -/
private theorem tightOrderOneEligible :
    ExactInterpolationEligibleExponent 5 15 1 1 3 0 tightOrderOneExponent := by
  classical
  norm_num [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
    exactInterpolationMonomialWeight, differentialWeight, tightOrderOneExponent,
    Finsupp.weight_single, Fin.last]

/-- Canonical exact interpolation column for `X² Y₁³`. -/
private def tightOrderOneIndex : ExactInterpolationIndex 5 15 1 1 3 0 (by decide) :=
  ⟨tightOrderOneExponent, mem_exactInterpolationExponents.mpr tightOrderOneEligible⟩

private theorem hasseDeriv_one_X_five :
    hasseDeriv 1 (X ^ 5 : ℚ[X]) = C 5 * X ^ 4 := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  norm_num
  rw [← C_mul_X_pow_eq_monomial]

/-- The equality checks singleton reconstruction, the exact order-one derivative weight, and the
inclusive input bound `natDegree P ≤ D`; the conjunction's second clause consumes the new bridge
at the sharp strict boundary `mA - 1`. -/
theorem exactInterpolation_tight_specialization_canary :
    (differentialSpecialization
      (exactInterpolationPolynomial (F := ℚ) (D := 5) (A := 15) (d := 1) (m := 1)
        (M := 3) (W := 0) (by decide) (Finsupp.single tightOrderOneIndex 1) :
          DifferentialPolynomial ℚ 1)
      (X ^ 5)).natDegree = 14 ∧
    (differentialSpecialization
      (exactInterpolationPolynomial (F := ℚ) (D := 5) (A := 15) (d := 1) (m := 1)
        (M := 3) (W := 0) (by decide) (Finsupp.single tightOrderOneIndex 1) :
          DifferentialPolynomial ℚ 1)
      (X ^ 5)).natDegree < 15 := by
  constructor
  · rw [exactInterpolationPolynomial_single]
    change (differentialSpecialization
      (MvPolynomial.monomial tightOrderOneExponent 1) (X ^ 5)).natDegree = 14
    rw [tightOrderOneExponent, MvPolynomial.monomial_add_single,
      ← MvPolynomial.X_pow_eq_monomial]
    simp only [differentialSpecialization, map_mul, map_pow, MvPolynomial.eval₂Hom_X',
      Fin.last, hasseDeriv_one_X_five]
    rw [Polynomial.natDegree_mul (by simp) (by norm_num), Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, Polynomial.natDegree_mul (by norm_num) (by simp),
      Polynomial.natDegree_pow]
    norm_num
  · apply natDegree_differentialSpecialization_exactInterpolationPolynomial_lt
    · decide
    · simp

end

end ReedSolomon.HiddenDerivative
