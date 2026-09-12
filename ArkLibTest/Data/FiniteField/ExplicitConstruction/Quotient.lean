/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.Quotient
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Executed quotient-field tests, including arithmetic over a nonprime current field. -/

namespace ExplicitQuotientTests

open CompPoly CompPoly.CPolynomial ArkLib.FiniteField.ExplicitConstruction

private def modulus : CPolynomial (ZMod 3) := X ^ 2 + 1


private theorem modulus_poly : modulus.toPoly = (Polynomial.X : Polynomial (ZMod 3)) ^ 2 + 1 := by
  simp only [modulus, toPoly_add, toPoly_pow, X_toPoly, toPoly_one]

private instance : Fact modulus.monic := ⟨by
  apply (monic_toPoly_iff modulus).mpr
  rw [modulus_poly, ← Polynomial.C_1]
  exact Polynomial.monic_X_pow_add_C _ (by decide)⟩

private instance : Fact (Irreducible modulus.toPoly) := ⟨by
  rw [modulus_poly]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [← Polynomial.C_1, Polynomial.natDegree_X_pow_add_C]
    decide
  · intro x
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide⟩

private abbrev F9 := Carrier modulus
private def omega : F9 := canonical modulus X

example (a : F9) (ha : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
example : Function.Injective (embedding modulus) :=
  embedding_injective modulus (Polynomial.degree_pos_of_irreducible Fact.out)

private def nestedModulus : CPolynomial F9 := X ^ 2 - C omega
private instance : Fact nestedModulus.monic := ⟨by
  apply (monic_toPoly_iff nestedModulus).mpr
  simp only [nestedModulus, toPoly_sub, toPoly_pow, X_toPoly, toPoly_C]
  exact Polynomial.monic_X_pow_sub_C _ (by decide)⟩
private abbrev Nested := Carrier nestedModulus
private def nestedRoot : Nested := canonical nestedModulus X

example (a b : F9) : embed nestedModulus (a * b) =
    embed nestedModulus a * embed nestedModulus b := map_mul (embedding nestedModulus) a b

/-- Exercise quadratic extension arithmetic, xgcd inverse and zero convention, literal base
embedding, and quotient arithmetic whose current coefficient field is already nonprime. -/
def run : IO Unit := do
  unless omega != 0 && omega != 1 && omega != 2 do
    throw (IO.userError "quadratic generator collapsed into the prime field")
  unless omega * omega == (2 : F9) do
    throw (IO.userError "quadratic reduction failed")
  unless (omega + 1) * (omega + 1)⁻¹ == (1 : F9) do
    throw (IO.userError "extended-gcd inverse failed")
  unless (0 : F9)⁻¹ == 0 do
    throw (IO.userError "zero inverse convention failed")
  unless embed modulus (2 : ZMod 3) == (2 : F9) do
    throw (IO.userError "prime base embedding failed")
  unless nestedRoot * nestedRoot == embed nestedModulus omega do
    throw (IO.userError "nonprime current-field quotient lost its coefficient")
  unless embed nestedModulus (omega + 1) ==
      embed nestedModulus omega + (1 : Nested) do
    throw (IO.userError "nonprime base embedding failed")
  match inverse? nestedModulus nestedRoot with
  | none => throw (IO.userError "nonprime-field xgcd unexpectedly rejected a unit")
  | some b =>
    unless nestedRoot * b == (1 : Nested) do
      throw (IO.userError "nonprime-field inverse equation failed")
  let reducible : CPolynomial (ZMod 3) := X ^ 2
  letI : Fact reducible.monic := ⟨by
    apply (monic_toPoly_iff reducible).mpr
    simp only [reducible, toPoly_pow, X_toPoly]
    exact Polynomial.monic_X_pow 2⟩
  let zeroDivisor := canonical reducible X
  unless (inverse? reducible zeroDivisor).isNone do
    throw (IO.userError "reducible quotient failed to reject a nonunit")

#print axioms ArkLib.FiniteField.ExplicitConstruction.mul_inverse
#print axioms ArkLib.FiniteField.ExplicitConstruction.embedding_injective
#print axioms ArkLib.FiniteField.ExplicitConstruction.inverse?_exists_of_irreducible

end ExplicitQuotientTests
