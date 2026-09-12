/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.Univariate

/-! Executed stored Sylvester matrices, degree guards, and padded resultant conventions. -/

open CompPoly CompPoly.CPolynomial ArkLib.Rojas.Producer.Univariate

namespace RojasUnivariateProducerTests

#print axioms ArkLib.Rojas.Producer.Univariate.storedResultant_eq
#print axioms ArkLib.Rojas.Producer.Univariate.checkedResultant_eq_some_iff
#print axioms ArkLib.Rojas.Producer.Univariate.checkedResultant_success

/-- Nonconstant inputs, shared roots, padding signs, constants, and rejected guards. -/
def run : IO Unit := do
  let x : CPolynomial ℤ := X
  unless checkedResultant (x ^ 2 - C 2) (x - 1) 2 1 == some (-1) do
    throw (IO.userError "stored resultant: quadratic evaluation identity failed")
  unless checkedResultant ((x - 1) * (x + C 2)) (x - 1) 2 1 == some 0 do
    throw (IO.userError "stored resultant: common root was not detected")
  unless checkedResultant (C 3) (x ^ 2 - C 2) 0 2 == some 9 do
    throw (IO.userError "stored resultant: constant polynomial convention failed")
  unless checkedResultant (x - 1) (x - C 3) 1 1 == some (-2) do
    throw (IO.userError "stored resultant: unpadded linear sign failed")
  unless checkedResultant (x - 1) (x - C 3) 2 1 == some 2 do
    throw (IO.userError "stored resultant: explicit padding sign was ignored")
  unless checkedResultant (x ^ 2 - C 2) (x - 1) 1 1 == none do
    throw (IO.userError "stored resultant: first undersized bound was accepted")
  unless checkedResultant (x - 1) (x ^ 2 - C 2) 1 1 == none do
    throw (IO.userError "stored resultant: second undersized bound was accepted")
  unless checkedResultant (0 : CPolynomial ℤ) 0 0 0 == some 1 do
    throw (IO.userError "stored resultant: empty determinant convention failed")
  unless checkedResultant (x ^ 3 - C 2) (x ^ 2 - C 3) 3 2 == some (-23) do
    throw (IO.userError "stored resultant: degree-three/two determinant failed")
  IO.println "Rojas stored univariate resultants: checks passed"

end RojasUnivariateProducerTests
