/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.Euclidean
import Mathlib.Algebra.Field.ZMod

/-! Executed Euclidean gcd and exact division with nonconstant rational coefficients. -/

namespace FunctionFieldEuclidTests

open CompPoly CPolynomial Polynomial.FunctionFieldAlgorithms

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev E := StoredField.Carrier (ZMod 5)

/-- Quotient equality, rational inversion, nontrivial outer gcd, exact and inexact division. -/
def run : IO Unit := do
  let u : E := StoredField.ofPolynomial CPolynomial.X
  let a : E := u / (u + 1)
  unless a == (u * u) / (u * (u + 1)) do
    throw (IO.userError "cross-product equality rejected equivalent representatives")
  unless a != u / (u + 2) do
    throw (IO.userError "cross-product equality identified distinct rational functions")
  unless a * a⁻¹ == 1 && (0 : E)⁻¹ == 0 do
    throw (IO.userError "stored field inversion failed")
  let v : CPolynomial E := CPolynomial.X
  let shared := v - CPolynomial.C a
  let left := v - CPolynomial.C ((u + 1)⁻¹)
  let right := v - CPolynomial.C ((u + 2)⁻¹)
  let p := shared * left
  let q := shared * right
  let g := FunctionFieldEuclid.gcd p q
  unless g == shared && g.natDegree == 1 do
    throw (IO.userError "function-field gcd missed the nonconstant-denominator linear factor")
  unless FunctionFieldEuclid.divide p g == some left do
    throw (IO.userError "function-field exact division returned the wrong quotient")
  unless FunctionFieldEuclid.divide left g == none do
    throw (IO.userError "function-field inexact division was accepted")
  unless FunctionFieldEuclid.divide p 0 == none do
    throw (IO.userError "function-field zero divisor was accepted")
  unless FunctionFieldEuclid.gcd (0 : CPolynomial E) 0 == 0 do
    throw (IO.userError "zero gcd policy failed")
  unless FunctionFieldEuclid.gcd p 0 == p do
    throw (IO.userError "monic nonzero/zero gcd policy failed")

example (p q r : CPolynomial E) :
    FunctionFieldEuclid.divide p q = some r ↔ q ≠ 0 ∧
      FunctionFieldEuclid.value r * FunctionFieldEuclid.value q = FunctionFieldEuclid.value p :=
  FunctionFieldEuclid.divide_eq_some_iff p q r

end FunctionFieldEuclidTests
