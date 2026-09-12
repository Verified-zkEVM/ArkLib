/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.NormProducts.MultiplicationMatrix

/-! Executed polynomial-valued norms, including ramified and intersecting fibers. -/

namespace NormProductsTests

open CompPoly CompPoly.CPolynomial CompPoly.CPolynomial.NormProducts

private abbrev R := CPolynomial ℚ
private def u : R := X
private def v : CPolynomial R := X
private def h : CPolynomial R := v ^ 2 - C u
private def g : CPolynomial R := v + C u

/-- Check every column and nonconstant determinant; a repeated fiber is intentionally retained. -/
def run : IO Unit := do
  let m := multiplicationMatrix 2 h g
  unless m 0 0 == u && m 1 0 == 1 && m 0 1 == u && m 1 1 == u do
    throw (IO.userError "norm multiplication matrix has incorrect monic remainder columns")
  let ng := polynomialNorm h g
  unless ng == u ^ 2 - u do
    throw (IO.userError "polynomial norm lost a coefficient or determinant sign")
  unless polynomialNorm h (v + 1) == 1 - u do
    throw (IO.userError "norm of V+1 is not 1-U")
  let nv := polynomialNorm h v
  unless nv == -u do
    throw (IO.userError "norm of the fiber coordinate is incorrect")
  unless nv.eval 0 == 0 && nv.eval 2 == -2 do
    throw (IO.userError "ramified fiber norm specialization is incorrect")
  unless ng.eval 2 == 2 do
    throw (IO.userError "nonvanishing specialization is incorrect")
  let meeting := v ^ 2 - C (u ^ 2)
  unless polynomialNorm meeting (v - C u) == 0 do
    throw (IO.userError "generic common factor did not give zero norm")
  unless polynomialNorm h (0 : CPolynomial R) == 0 do
    throw (IO.userError "zero element of positive-rank quotient has nonzero norm")
  unless polynomialNorm (1 : CPolynomial R) g == 1 do
    throw (IO.userError "rank-zero quotient determinant policy is incorrect")

end NormProductsTests
