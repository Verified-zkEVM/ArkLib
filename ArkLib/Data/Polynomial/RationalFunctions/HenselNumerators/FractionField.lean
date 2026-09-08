/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov, Quang Dao
-/

import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Hensel

/-!
# Fraction-field-separable Hensel lifts

This backward-compatible adapter reuses the native Hensel engine and the initial-root proof
from `Hensel.lean`. It replaces coefficient-ring separability only at the lift-existence
boundary, using an explicit embedding of any coefficient fraction field into the function field.
Existing `Hypotheses` and numerator/weight interfaces remain unchanged.
-/

open Polynomial Polynomial.Bivariate
namespace RationalFunctions.HenselNumerators
variable {F : Type} [Field F]

/-- The initial root identity needs only divisibility, not coefficient-ring separability. -/
theorem initial_root_at_x0_of_dvd (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hdvd : H ∣ Bivariate.evalX (Polynomial.C x₀) R) :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0 := by
  classical
  rcases hdvd with ⟨Q, hQ⟩
  rw [hQ, Polynomial.eval₂_mul, H_eval2_T_div_W_eq_zero H, zero_mul]

set_option maxHeartbeats 800000 in
-- Reducing the explicit fraction-field lift composite needs extra elaboration heartbeats.
/-- Separability over any fraction field of the coefficient ring makes the initial root simple.
The fraction-field embedding is constructed explicitly from the native coefficient embedding. -/
theorem zeta_ne_zero_of_fractionField_separable
    (K : Type*) [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hdvd : H ∣ Bivariate.evalX (Polynomial.C x₀) R)
    (hsep : ((Bivariate.evalX (Polynomial.C x₀) R).map
      (algebraMap F[X] K)).Separable) :
    zeta R x₀ H ≠ 0 := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  let t : 𝕃 H := functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff
  have hinj : Function.Injective (liftToFunctionField (H := H)) := by
    intro a b hab
    apply sub_eq_zero.mp
    by_contra h
    exact liftToFunctionField_ne_zero (H := H) h (by simp [map_sub, hab])
  let φ : K →+* 𝕃 H := IsFractionRing.lift hinj
  have hcomp : φ.comp (algebraMap F[X] K) = liftToFunctionField (H := H) := by
    apply RingHom.ext
    intro p
    exact IsFractionRing.lift_algebraMap (K := K) hinj p
  have hroot : Polynomial.eval₂ (liftToFunctionField (H := H)) t P = 0 :=
    initial_root_at_x0_of_dvd x₀ R H hdvd
  have hroot' : Polynomial.eval₂ φ t (P.map (algebraMap F[X] K)) = 0 := by
    simpa only [Polynomial.eval₂_map, hcomp] using hroot
  have hne := hsep.eval₂_derivative_ne_zero φ hroot'
  have hne' : Polynomial.eval₂ (liftToFunctionField (H := H)) t P.derivative ≠ 0 := by
    simpa only [Polynomial.derivative_map, Polynomial.eval₂_map, hcomp] using hne
  have hderiv_evalX : Bivariate.evalX (Polynomial.C x₀) R.derivative = P.derivative := by
    ext i
    simp [P, derivative_evalX_coeff, Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  simpa [zeta, P, t, hderiv_evalX] using hne'

/-- The existing formal Hensel engine applies under fraction-field separability.
This is a lift-existence endpoint only; it does not extend the numerator/weight interfaces. -/
theorem exists_hensel_alpha_sequence_of_fractionField_separable
    (K : Type*) [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hdvd : H ∣ Bivariate.evalX (Polynomial.C x₀) R)
    (hsep : ((Bivariate.evalX (Polynomial.C x₀) R).map
      (algebraMap F[X] K)).Separable) :
    ∃ αseq : ℕ → 𝕃 H,
      αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0 := by
  exact formalHenselAlphaSequence x₀ R H (initial_root_at_x0_of_dvd x₀ R H hdvd)
    (zeta_ne_zero_of_fractionField_separable K x₀ R H hdvd hsep)

end RationalFunctions.HenselNumerators
