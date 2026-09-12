/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ConfluentAlgebra.ParameterKernel

/-! Whole-kernel nilpotence for polynomial residuals in a deformed, nonreduced quotient. -/

namespace ConfluentParameterKernelTests

open CompPoly CPoly.BoxAlgebra ArkLib.ConfluentAlgebra

private instance : Fact (0 < 2) := ⟨by decide⟩
private abbrev A := Carrier 2 2 ℤ
private def e₀ : A := eps 0
private def e₁ : A := eps 1
private def equation : CPolynomial A := CPolynomial.X ^ 2 - CPolynomial.C e₀
private instance : Fact equation.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [equation, CPolynomial.toPoly_sub, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_sub_C e₀ (by decide)⟩
private abbrev B := Representative equation
private def z : B := reductionHom equation CPolynomial.X
private def residual : B := constantHom equation e₀ * z + constantHom equation e₁
private def fiber : A →+* ℤ := constantSpecialization (by decide)

private theorem residual_specializes_zero : coefficientMapHom equation fiber residual = 0 := by
  change coefficientMapHom equation fiber
    (constantHom equation e₀ * z + constantHom equation e₁) = 0
  rw [(coefficientMapHom equation fiber).map_add, (coefficientMapHom equation fiber).map_mul,
    coefficientMapHom_constantHom, coefficientMapHom_constantHom]
  have h₀ : fiber e₀ = 0 := constantSpecialization_eps (by decide) 0
  have h₁ : fiber e₁ = 0 := constantSpecialization_eps (by decide) 1
  rw [h₀, h₁, (constantHom (mapCoefficients fiber equation)).map_zero, zero_mul, zero_add]

example : RingHom.ker (coefficientMapHom equation fiber) ^ 3 = ⊥ :=
  parameterSpecialization_ker_pow equation

example : residual ^ 3 = 0 :=
  pow_eq_zero_of_parameterSpecialization_eq_zero equation residual residual_specializes_zero

example (p : B) (hp : coefficientMapHom equation fiber p = 0) : p ^ 3 = 0 :=
  pow_eq_zero_of_parameterSpecialization_eq_zero equation p hp

private theorem z_square : z ^ 2 = constantHom equation e₀ := by
  have he := reductionHom_modulus equation
  change reductionHom equation (CPolynomial.X ^ 2 - CPolynomial.C e₀) = 0 at he
  rw [map_sub, map_pow] at he
  exact sub_eq_zero.mp he

private theorem fiber_inverse :
    coefficientMapHom equation fiber ((1 + z) * (1 - z)) = 1 := by
  have he : (1 + z) * (1 - z) = 1 - constantHom equation e₀ := by
    rw [← z_square]
    ring
  rw [he, map_sub, map_one, coefficientMapHom_constantHom]
  have h₀ : fiber e₀ = 0 := constantSpecialization_eps (by decide) 0
  rw [h₀, (constantHom (mapCoefficients fiber equation)).map_zero, sub_zero]

example :
    (1 + z) * Polynomial.NilpotentInverse.correct 3 (1 + z) (1 - z) = 1 ∧
      Polynomial.NilpotentInverse.correct 3 (1 + z) (1 - z) * (1 + z) = 1 :=
  corrected_inverse_of_specialized_mul_eq_one equation (1 + z) (1 - z) fiber_inverse

/-- Run mixed polynomial residuals and lift a nonconstant inverse from the repeated-root fiber. -/
def run : IO Unit := do
  unless coefficientMapHom equation fiber residual == 0 do
    throw (IO.userError "polynomial parameter residual has nonzero constant fiber")
  unless residual ^ 2 != 0 do
    throw (IO.userError "polynomial residual incorrectly vanished at coordinate precision")
  unless (residual ^ 2).val.coeff 1 == 2 * e₀ * e₁ do
    throw (IO.userError "polynomial residual square lost its mixed linear coefficient")
  unless residual ^ 3 == 0 do
    throw (IO.userError "polynomial residual exceeded the whole-kernel bound")
  let inverseMixed := Polynomial.NilpotentInverse.correct 3 (1 - residual) 1
  unless (1 - residual) * inverseMixed == 1 && inverseMixed * (1 - residual) == 1 do
    throw (IO.userError "mixed polynomial residual inverse correction failed")
  unless (1 + z) * (1 - z) != 1 do
    throw (IO.userError "nonconstant fiber inverse was already an inverse before lifting")
  unless coefficientMapHom equation fiber ((1 + z) * (1 - z)) == 1 do
    throw (IO.userError "nonconstant approximate inverse failed in the constant fiber")
  let inverse := Polynomial.NilpotentInverse.correct 3 (1 + z) (1 - z)
  unless (1 + z) * inverse == 1 && inverse * (1 + z) == 1 do
    throw (IO.userError "nonconstant fiber inverse did not lift to a two-sided inverse")

#print axioms ArkLib.ConfluentAlgebra.ker_coefficientMapHom
#print axioms ArkLib.ConfluentAlgebra.parameterSpecialization_ker_pow
#print axioms ArkLib.ConfluentAlgebra.corrected_inverse_of_specialized_mul_eq_one

end ConfluentParameterKernelTests
