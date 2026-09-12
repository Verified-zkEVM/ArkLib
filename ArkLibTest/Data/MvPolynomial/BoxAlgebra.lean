/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoxAlgebra
import CompPoly.Univariate.Basic

/-! Regression tests for the executable nonreduced parameter coefficient ring. -/

open CPoly

namespace BoxAlgebraTests

private instance : Fact (0 < 2) := ⟨by decide⟩
private abbrev A := BoxAlgebra.Carrier 2 2 ℤ
private def e₀ : A := BoxAlgebra.eps 0
private def e₁ : A := BoxAlgebra.eps 1

example : e₀ ^ 2 = 0 := BoxAlgebra.eps_pow 0
example (a b c : A) : a * (b + c) = a * b + a * c := mul_add a b c
example (p q : CMvPolynomial 2 ℤ) :
    BoxAlgebra.projection (N := 2) (p * q) =
      BoxAlgebra.projection p * BoxAlgebra.projection q := map_mul _ p q

/-- Check nilpotence, surviving mixed terms, equality, and monic division over this ring. -/
def run : IO Unit := do
  unless e₀ != 0 do
    throw (IO.userError "box parameter incorrectly zero")
  unless e₀ * e₀ == 0 do
    throw (IO.userError "box parameter square not zero")
  unless (e₀ * e₁).val.coeff #m[1, 1] = 1 do
    throw (IO.userError "box algebra lost mixed term")
  unless e₀ + -e₀ == 0 do
    throw (IO.userError "box additive inverse failed")
  unless (3 : A) - 2 == 1 do
    throw (IO.userError "box integer constants failed")
  unless (2 : ℤ) • e₀ == e₀ + e₀ do
    throw (IO.userError "box integer scalar multiplication failed")
  let z : CompPoly.CPolynomial A := CompPoly.CPolynomial.X
  let h := z * z
  let p := h + CompPoly.CPolynomial.C e₀
  let rem := CompPoly.CPolynomial.modByMonic p h
  unless rem.coeff 0 == e₀ do
    throw (IO.userError "monic remainder lost nilpotent constant")
  unless rem.coeff 1 == 0 do
    throw (IO.userError "monic remainder retained linear term")
  unless rem.coeff 2 == 0 do
    throw (IO.userError "monic remainder retained quadratic term")


end BoxAlgebraTests
