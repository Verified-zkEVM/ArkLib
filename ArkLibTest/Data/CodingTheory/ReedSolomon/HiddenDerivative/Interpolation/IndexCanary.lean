/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Index
/-!
# Canary tests for the exact interpolation index

These kernel-executed examples reject swapped differential weights, loss of the strict `mA`
boundary, omission of the `Y₁` cap, and any attempt to infer finiteness from the high-jet weight
alone.
-/

namespace ReedSolomon
namespace HiddenDerivative

open PolynomialDifferential

noncomputable section

/-- The asymmetric monomial `X Y₀² Y₁³ Y₂⁴` at derivative order two. -/
private def smallBandExponent : JetVariable 2 →₀ ℕ :=
  Finsupp.single none 1 +
    Finsupp.single (some (0 : Fin 3)) 2 +
    Finsupp.single (some (1 : Fin 3)) 3 +
    Finsupp.single (some (2 : Fin 3)) 4

/-- The paper weights `(1,4,3,2)` give `X Y₀² Y₁³ Y₂⁴` exact weight 26.  The
asymmetric exponents make this sensitive to permuting the variable weights. -/
theorem exactInterpolationMonomialWeight_small_canary :
    exactInterpolationMonomialWeight 4 smallBandExponent = 26 := by
  classical
  norm_num [smallBandExponent, exactInterpolationMonomialWeight, differentialWeight,
    Finsupp.weight_single]

/-- At threshold 27 the test monomial is in the band. -/
theorem exactInterpolationEligible_small_canary :
    ExactInterpolationEligibleExponent 4 27 2 1 3 4 smallBandExponent := by
  classical
  norm_num [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
    exactInterpolationMonomialWeight, differentialWeight, smallBandExponent,
    Finsupp.weight_single]

/-- Replacing the strict threshold 27 by 26 excludes the boundary monomial. -/
theorem exactInterpolationStrictBoundary_small_canary :
    ¬ExactInterpolationEligibleExponent 4 26 2 1 3 4 smallBandExponent := by
  classical
  norm_num [ExactInterpolationEligibleExponent, exactInterpolationMonomialWeight,
    differentialWeight, smallBandExponent, Finsupp.weight_single]

/-- Reducing the `Y₁` cap from three to two excludes the same monomial. -/
theorem exactInterpolationFirstJetCap_small_canary :
    ¬ExactInterpolationEligibleExponent 4 27 2 1 2 4 smallBandExponent := by
  classical
  norm_num [ExactInterpolationEligibleExponent, firstJetExponent, smallBandExponent,
    Finsupp.weight_single]

/-- Reducing the higher-jet weight budget from four to three excludes the `Y₂⁴` factor. -/
theorem exactInterpolationHigherJetBudget_small_canary :
    ¬ExactInterpolationEligibleExponent 4 27 2 1 3 3 smallBandExponent := by
  classical
  norm_num [ExactInterpolationEligibleExponent, fullHigherJetWeight, smallBandExponent,
    Finsupp.weight_single]

/-- The high-jet weight deliberately ignores `X`, `Y₀`, and `Y₁`; their exponents must be bounded
by the other support clauses. -/
theorem highJetWeight_zeroVariable_canary :
    let u : JetVariable 2 →₀ ℕ :=
      Finsupp.single none 7 +
        Finsupp.single (some (0 : Fin 3)) 8 +
        Finsupp.single (some (1 : Fin 3)) 9
    fullHigherJetWeight u = 0 := by
  classical
  norm_num [fullHigherJetWeight, Finsupp.weight_single]

/-- At the rejected boundary `D=d`, every power of the top jet has exact differential weight
zero.  Thus the floor bound used to construct the finite index genuinely needs `d < D`. -/
theorem exactInterpolationBoundaryTopJet_canary (r : ℕ) :
    exactInterpolationMonomialWeight 2
      (Finsupp.single (some (Fin.last 2)) r : JetVariable 2 →₀ ℕ) = 0 := by
  simp [exactInterpolationMonomialWeight, Finsupp.weight_single]

/-- Concrete canonical column witnessing that the finite coefficient interface accepts the
small test monomial. -/
private def smallBandIndex : ExactInterpolationIndex 4 27 2 1 3 4 (by decide) :=
  ⟨smallBandExponent, mem_exactInterpolationExponents.mpr exactInterpolationEligible_small_canary⟩

/-- Reconstructing a singleton coefficient vector and reading its coordinate returns the input
coefficient. -/
theorem exactInterpolationCoefficientRoundTrip_small_canary (a : ℤ) :
    exactInterpolationRepr (F := ℤ) (D := 4) (A := 27) (d := 2) (m := 1) (M := 3)
      (W := 4) (by decide)
      (exactInterpolationPolynomial (F := ℤ) (D := 4) (A := 27) (d := 2) (m := 1)
        (M := 3) (W := 4) (by decide) (Finsupp.single smallBandIndex a)) =
      Finsupp.single smallBandIndex a := by
  exact LinearEquiv.apply_symm_apply _ _

end
end HiddenDerivative
end ReedSolomon
