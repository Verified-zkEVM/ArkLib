/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Materialize

/-!
# Executable tower-inversion regressions

These examples exercise the actual multiplication-matrix solver.  In particular the final example
uses `U^2 + 1` over `ℚ`, whose base modulus has no rational root; the algorithm therefore cannot be
secretly relying on enumeration of geometric points.
-/

namespace ArkLibTest.TowerAlgebraInverse

open CompPoly ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra

private abbrev Base := CPolynomial ℚ
private abbrev Nested := CPolynomial Base

private def U : Base := CPolynomial.X
private def V : Nested := CPolynomial.X
private def liftBase (p : Base) : Nested := CPolynomial.C p

private def splitBase : Base := U * (U - 1)
private def extensionOnlyBase : Base := U ^ 2 + 1

/-- Execute units, a zero divisor, multiple base components, and materialization. -/
def run : IO Unit := do
  unless inverseRepresentative? extensionOnlyBase V (2 : Nested) ==
      some (liftBase (CPolynomial.C (1 / 2 : ℚ))) do
    throw (IO.userError "tower inverse: scalar unit")
  unless (inverseRepresentative? splitBase V (liftBase U)).isNone do
    throw (IO.userError "tower inverse: zero divisor")
  unless inverseRepresentative? splitBase V (liftBase (U + 1)) ==
      some (liftBase (1 - CPolynomial.C (1 / 2 : ℚ) * U)) do
    throw (IO.userError "tower inverse: multiple base components")
  unless inverseRepresentative? extensionOnlyBase V (liftBase U) == some (liftBase (-U)) do
    throw (IO.userError "tower inverse: extension-only base")
  let r : TowerRepresentation (F := ℚ) :=
    { modulus := extensionOnlyBase, fiber := V, coefficients := [] }
  unless (materializeCoefficients? r (liftBase U) [1, liftBase U]).map
      TowerRepresentation.coefficients == some [liftBase (-U), 1] do
    throw (IO.userError "tower inverse: coefficient materialization")

end ArkLibTest.TowerAlgebraInverse
