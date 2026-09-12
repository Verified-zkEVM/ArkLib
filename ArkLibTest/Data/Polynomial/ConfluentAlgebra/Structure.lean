/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ConfluentAlgebra.Structure
import ArkLib.Data.MvPolynomial.BoxAlgebraNilpotence
import ArkLib.Data.Polynomial.NilpotentInverse

/-! Ring structure and inverse-correction clients over nonreduced monic coefficients. -/

namespace ConfluentStructureTests

open CompPoly CPoly.BoxAlgebra ArkLib.ConfluentAlgebra

private instance : Fact (0 < 2) := ⟨by decide⟩
private abbrev A := Carrier 2 2 ℤ
private def e₀ : A := eps 0
private def e₁ : A := eps 1
private def equation : CPolynomial A :=
  CPolynomial.X ^ 2 + (CPolynomial.C (-e₀) * CPolynomial.X + CPolynomial.C (-e₁))
private instance : Fact equation.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [equation, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_add Polynomial.degree_linear_lt⟩
private instance : Fact (0 < equation.toPoly.degree) := ⟨by
  simp only [equation, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  rw [Polynomial.degree_add_eq_left_of_degree_lt (by
    simpa using (Polynomial.degree_linear_lt (a := -e₀) (b := -e₁)))]
  simp⟩
private abbrev B := Representative equation
private def z : B := reductionHom equation CPolynomial.X
private def u : B := constantHom equation (e₀ + e₁)
private def fiber : A →+* ℤ := constantSpecialization (by decide)

example : (0 : B) ≠ 1 := zero_ne_one

example (a b c : B) : a * (b + c) = a * b + a * c := mul_add a b c
example (a b c : B) : a * b * c = a * (b * c) := mul_assoc a b c
example (a : B) : a + -a = 0 := add_neg_cancel a

private theorem u_cube : u ^ 3 = 0 := by
  have hu : (e₀ + e₁) ^ 3 = 0 := by
    apply pow_eq_zero_of_constantValue_eq_zero (by decide)
    change constantSpecialization (by decide) (eps 0 + eps 1 : A) = 0
    simp
  change constantHom equation (e₀ + e₁) ^ 3 = 0
  rw [← map_pow, hu, map_zero]

example : (1 - u) * Polynomial.NilpotentInverse.correct 3 (1 - u) 1 = 1 := by
  apply Polynomial.NilpotentInverse.right_inverse
  simpa using u_cube

example (p q : B) :
    coefficientMapHom equation fiber (p * q) =
      coefficientMapHom equation fiber p * coefficientMapHom equation fiber q := map_mul _ p q

private instance : Fact (CPolynomial.monic (1 : CPolynomial A)) := ⟨by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_one]
  exact Polynomial.monic_one⟩

example : Subsingleton (Representative (1 : CPolynomial A)) :=
  subsingleton_of_isUnit 1 isUnit_one

/-- Execute ring laws, a finite inverse correction, and specialization on stored representatives. -/
def run : IO Unit := do
  unless (0 : B) != 1 do
    throw (IO.userError "positive-degree monic quotient collapsed to the zero ring")
  let a := 1 + z + u
  let b := 2 - z
  let c := z * z + u
  unless a * (b + c) == a * b + a * c do
    throw (IO.userError "stored quotient distributivity failed")
  unless a * b * c == a * (b * c) do
    throw (IO.userError "stored quotient associativity failed")
  unless a - a == 0 && a + -a == 0 do
    throw (IO.userError "stored quotient additive group laws failed")
  unless (3 : ℤ) • a == a + a + a do
    throw (IO.userError "stored quotient scalar arithmetic failed")
  unless a ^ 3 == a * a * a do
    throw (IO.userError "stored quotient power arithmetic failed")
  unless u ^ 2 != 0 && u ^ 3 == 0 do
    throw (IO.userError "quotient ring lost mixed-parameter nilpotence")
  let inverse := Polynomial.NilpotentInverse.correct 3 (1 - u) 1
  unless (1 - u) * inverse == 1 && inverse * (1 - u) == 1 do
    throw (IO.userError "inverse correction failed over the nonreduced quotient ring")
  unless coefficientMapHom equation fiber (a * b) ==
      coefficientMapHom equation fiber a * coefficientMapHom equation fiber b do
    throw (IO.userError "quotient coefficient specialization failed multiplicativity")
  unless (0 : Representative (1 : CPolynomial A)) == 1 do
    throw (IO.userError "unit modulus failed to produce the zero ring")

#print axioms ArkLib.ConfluentAlgebra.interpret_injective
#print axioms ArkLib.ConfluentAlgebra.quotientEquiv
#print axioms ArkLib.ConfluentAlgebra.nontrivial_of_degree_pos
#print axioms ArkLib.ConfluentAlgebra.coefficientMapHom

end ConfluentStructureTests
