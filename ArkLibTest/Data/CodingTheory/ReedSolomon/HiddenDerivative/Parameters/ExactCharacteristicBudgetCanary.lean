/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.ExactCharacteristicBudget
/-!
# Canary tests for exact interpolation characteristic budgets

The asymmetric polynomial below has a `Y₀²` term of weight ten and a `Y₂⁴` term of weight
twelve for ambient degree five.  At budget thirteen, its coordinate floors are respectively two
and four.  This distinguishes the sharp denominator `D - j` from the uniform denominator `D - d`
and detects an off-by-one error at the highest jet.
-/

namespace ReedSolomon
namespace HiddenDerivative

open PolynomialDifferential

noncomputable section

/-- The exponent of `Y₀²`. -/
private def lowJetExponent : JetVariable 2 →₀ ℕ :=
  Finsupp.single (some (0 : Fin 3)) 2

/-- The exponent of `Y₂⁴`. -/
private def highJetExponent : JetVariable 2 →₀ ℕ :=
  Finsupp.single (some (2 : Fin 3)) 4

private theorem lowJetExponent_ne_highJetExponent : lowJetExponent ≠ highJetExponent := by
  intro h
  have hvalue := congrArg (fun u : JetVariable 2 →₀ ℕ ↦ u (some (0 : Fin 3))) h
  simp [lowJetExponent, highJetExponent] at hvalue

private theorem lowJetExponent_eligible :
    ExactInterpolationEligibleExponent 5 13 2 1 0 4 lowJetExponent := by
  classical
  norm_num [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
    exactInterpolationMonomialWeight, differentialWeight, lowJetExponent,
    Finsupp.weight_single]

private theorem highJetExponent_eligible :
    ExactInterpolationEligibleExponent 5 13 2 1 0 4 highJetExponent := by
  classical
  norm_num [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
    exactInterpolationMonomialWeight, differentialWeight, highJetExponent,
    Finsupp.weight_single]

private def lowJetIndex : ExactInterpolationIndex 5 13 2 1 0 4 (by decide) :=
  ⟨lowJetExponent, mem_exactInterpolationExponents.mpr lowJetExponent_eligible⟩

private def highJetIndex : ExactInterpolationIndex 5 13 2 1 0 4 (by decide) :=
  ⟨highJetExponent, mem_exactInterpolationExponents.mpr highJetExponent_eligible⟩

/-- Coefficients reconstructing `Y₀² + Y₂⁴` in the exact interpolation space. -/
private def asymmetricCoefficients (F : Type*) [Semiring F] :
    ExactInterpolationCoefficients F 5 13 2 1 0 4 (by decide) :=
  Finsupp.single lowJetIndex 1 + Finsupp.single highJetIndex 1

/-- Reconstruction really produces the two distinct test monomials. -/
private theorem asymmetricPolynomial_eq (F : Type*) [CommSemiring F] :
    (exactInterpolationPolynomial (F := F) (by decide) (asymmetricCoefficients F) :
      DifferentialPolynomial F 2) =
      MvPolynomial.monomial lowJetExponent 1 +
        MvPolynomial.monomial highJetExponent 1 := by
  simp [asymmetricCoefficients, lowJetIndex, highJetIndex]

/-- The coefficient-facing API exposes the distinct sharp coordinate floors and the direct
below-characteristic bridge for the same reconstructed polynomial. -/
theorem exactInterpolationCharacteristicBudget_asymmetric_canary :
    let Q := exactInterpolationPolynomial (F := ZMod 7) (by decide)
      (asymmetricCoefficients (ZMod 7))
    jetDegree (Q : DifferentialPolynomial (ZMod 7) 2) 0 = 2 ∧
      jetDegree (Q : DifferentialPolynomial (ZMod 7) 2) 2 = 4 ∧
      IsBelowCharacteristic 5 (Q : DifferentialPolynomial (ZMod 7) 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · simpa [exactInterpolationJetDegreeFloorAt] using
        jetDegree_exactInterpolationPolynomial_le_floorAt
          (asymmetricCoefficients (ZMod 7)) (0 : Fin 3)
    · rw [jetDegree]
      have hsupport : lowJetExponent ∈
          (exactInterpolationPolynomial (F := ZMod 7) (by decide)
            (asymmetricCoefficients (ZMod 7)) : DifferentialPolynomial (ZMod 7) 2).support := by
        rw [asymmetricPolynomial_eq]
        norm_num [lowJetExponent_ne_highJetExponent,
          Ne.symm lowJetExponent_ne_highJetExponent]
        exact (by decide : (1 : ZMod 7) ≠ 0)
      have hdegree := MvPolynomial.le_degreeOf_of_mem_support (some (0 : Fin 3)) hsupport
      simpa [lowJetExponent] using hdegree
  · apply le_antisymm
    · simpa [exactInterpolationJetDegreeFloorAt] using
        jetDegree_exactInterpolationPolynomial_le_floorAt
          (asymmetricCoefficients (ZMod 7)) (2 : Fin 3)
    · rw [jetDegree]
      have hsupport : highJetExponent ∈
          (exactInterpolationPolynomial (F := ZMod 7) (by decide)
            (asymmetricCoefficients (ZMod 7)) : DifferentialPolynomial (ZMod 7) 2).support := by
        rw [asymmetricPolynomial_eq]
        norm_num [lowJetExponent_ne_highJetExponent,
          Ne.symm lowJetExponent_ne_highJetExponent]
        exact (by decide : (1 : ZMod 7) ≠ 0)
      have hdegree := MvPolynomial.le_degreeOf_of_mem_support (some (2 : Fin 3)) hsupport
      simpa [highJetExponent] using hdegree
  · apply isBelowCharacteristic_exactInterpolationPolynomial
    · norm_num [ZMod.ringChar_zmod_n]
    · norm_num [exactInterpolationJetDegreeFloor, ZMod.ringChar_zmod_n]

end

end HiddenDerivative
end ReedSolomon
