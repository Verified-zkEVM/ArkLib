/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ConfluentAlgebra.MonicArithmetic
import ArkLib.Data.MvPolynomial.BoxAlgebraNilpotence

/-! Monic arithmetic over a nonreduced parameter box, with repeated-root constant fiber. -/

namespace ConfluentMonicArithmeticTests

open CompPoly CPoly.BoxAlgebra ArkLib.ConfluentAlgebra

private instance : Fact (0 < 2) := ⟨by decide⟩
private abbrev A := Carrier 2 2 ℤ
private def e₀ : A := eps 0
private def e₁ : A := eps 1
private def equation : CPolynomial A :=
  CPolynomial.X ^ 2 + (CPolynomial.C (-e₀) * CPolynomial.X + CPolynomial.C (-e₁))
private theorem equation_monic : equation.monic := by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [equation, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_add Polynomial.degree_linear_lt
private def fiber : A →+* ℤ := constantSpecialization (by decide)

example (p : CPolynomial A) :
    mapCoefficients fiber (p.modByMonic equation) =
      (mapCoefficients fiber p).modByMonic (mapCoefficients fiber equation) :=
  mapCoefficients_remainder fiber equation p equation_monic

example (p : Representative equation) : p.val.toPoly.degree < equation.toPoly.degree :=
  degree_representative_lt equation equation_monic p

/-- Check nonlinear reduction, surviving mixed coefficients, and a repeated-root constant fiber. -/
def run : IO Unit := do
  let z := reduce equation equation_monic (CPolynomial.X : CPolynomial A)
  let square := mul equation equation_monic z z
  unless square.val.coeff 0 == e₁ && square.val.coeff 1 == e₀ do
    throw (IO.userError "monic square reduction lost parameter coefficients")
  unless square.val.coeff 2 == 0 do
    throw (IO.userError "monic square reduction retained leading term")
  let cube := mul equation equation_monic square z
  unless cube.val.coeff 0 == e₀ * e₁ && cube.val.coeff 1 == e₁ do
    throw (IO.userError "monic cube reduction lost mixed parameter term")
  let fourth := mul equation equation_monic cube z
  unless fourth.val.coeff 0 == 0 && fourth.val.coeff 1 == 2 * e₀ * e₁ do
    throw (IO.userError "monic fourth-power reduction lost mixed multiplicity")
  let cancellation := add equation equation_monic cube (neg equation equation_monic cube)
  unless cancellation.val == 0 do
    throw (IO.userError "canonical quotient addition/negation failed")
  let specializedEquation := mapCoefficients fiber equation
  unless specializedEquation == (CPolynomial.X : CPolynomial ℤ) ^ 2 do
    throw (IO.userError "constant fiber is not the repeated-root equation")
  unless mapCoefficients fiber square.val ==
      (mapCoefficients fiber (CPolynomial.X ^ 2 : CPolynomial A)).modByMonic
        specializedEquation do
    throw (IO.userError "specialization does not commute with monic remainder")
  let unitReduction := reduce (1 : CPolynomial A)
    (by rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_one]; exact Polynomial.monic_one)
    (CPolynomial.X + 1)
  unless unitReduction.val == 0 do
    throw (IO.userError "unit modulus did not reduce to zero")

#print axioms ArkLib.ConfluentAlgebra.quotientHom_mul
#print axioms ArkLib.ConfluentAlgebra.mapCoefficients_remainder

end ConfluentMonicArithmeticTests
