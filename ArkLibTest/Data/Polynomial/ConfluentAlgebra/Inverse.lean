/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ConfluentAlgebra.Inverse

/-! Computed Bézout initialization and Newton lifting over a repeated-root constant fiber. -/

namespace ConfluentInverseTests

open CompPoly CPoly.BoxAlgebra ArkLib.ConfluentAlgebra

private instance : Fact (0 < 2) := ⟨by decide⟩
private abbrev A := Carrier 2 2 ℚ
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
private def mixed : B := constantHom equation (e₀ + e₁)

example (a b : B) (hb : inverse? equation a = some b) : a * b = 1 ∧ b * a = 1 :=
  inverse?_sound equation a b hb

example (a b : B) (hab : a * b = 1) : ∃ c, inverse? equation a = some c :=
  inverse?_exists_of_mul_eq_one equation a b hab

example : ∃ b, inverse? equation 1 = some b :=
  inverse?_exists_of_mul_eq_one equation 1 1 (by simp)

private instance : Fact (CPolynomial.monic (1 : CPolynomial A)) := ⟨by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_one]
  exact Polynomial.monic_one⟩

/-- Execute the full producer without supplying a Bézout coefficient or approximate inverse. -/
def run : IO Unit := do
  let some nonconstantInverse := inverse? equation (1 + z)
    | throw (IO.userError "nonconstant unit rejected in repeated-root constant fiber")
  unless (1 + z) * nonconstantInverse == 1 && nonconstantInverse * (1 + z) == 1 do
    throw (IO.userError "computed nonconstant inverse is not two-sided")
  unless nonconstantInverse != 1 - z do
    throw (IO.userError "producer skipped lifting the constant-fiber inverse")
  unless nonconstantInverse == 1 - z + z ^ 2 - z ^ 3 do
    throw (IO.userError "lifted nonconstant inverse has incorrect coefficients")
  let some mixedInverse := inverse? equation (1 - mixed)
    | throw (IO.userError "mixed-parameter unit rejected")
  unless mixedInverse == 1 + mixed + mixed ^ 2 do
    throw (IO.userError "Newton inverse omitted the mixed second-order correction")
  unless (1 - mixed) * mixedInverse == 1 && mixedInverse * (1 - mixed) == 1 do
    throw (IO.userError "computed mixed inverse is not two-sided")
  let combined := (1 + z) * (1 - mixed)
  let some combinedInverse := inverse? equation combined
    | throw (IO.userError "combined nonconstant and mixed-parameter unit rejected")
  unless combined * combinedInverse == 1 && combinedInverse * combined == 1 do
    throw (IO.userError "computed combined inverse is not two-sided")
  unless (inverse? equation z).isNone do
    throw (IO.userError "nonunit with shared fiber factor was accepted")
  unless (inverse? equation (constantHom equation e₀)).isNone do
    throw (IO.userError "nilpotent parameter with zero fiber was accepted")
  unless (inverse? equation 0).isNone do
    throw (IO.userError "zero input in positive-degree quotient was accepted")
  let some unitModulusInverse := inverse? (1 : CPolynomial A) 0
    | throw (IO.userError "zero-ring unit modulus was rejected")
  unless unitModulusInverse == 0 do
    throw (IO.userError "unit modulus returned a noncanonical inverse")
  unless Polynomial.NewtonInverse.rounds 3 == 2 do
    throw (IO.userError "kernel precision did not select two Newton doubling rounds")

#print axioms ArkLib.ConfluentAlgebra.inverse?_sound
#print axioms ArkLib.ConfluentAlgebra.inverse?_exists_iff_coprime
#print axioms ArkLib.ConfluentAlgebra.inverse?_exists_iff_exists_inverse

end ConfluentInverseTests
