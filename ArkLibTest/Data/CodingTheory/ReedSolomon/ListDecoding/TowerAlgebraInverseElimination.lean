/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.InverseElimination

/-!
# Executed elimination inversion regressions

Exercise genuine positive-dimensional rectangular slices, including a zero divisor involving both
variables, independent of the proof that elimination agrees with the Cramer reference backend.
-/

namespace ArkLibTest.TowerAlgebraInverseElimination

open CompPoly ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra

private abbrev Base := CPolynomial ℚ
private abbrev Nested := CPolynomial Base

private def U : Base := CPolynomial.X
private def V : Nested := CPolynomial.X
private def liftBase (p : Base) : Nested := CPolynomial.C p
private def scalar (a : ℚ) : Nested := liftBase (CPolynomial.C a)

/-- Execute unit, nonunit, split-component, and extension-only tower examples. -/
def run : IO Unit := do
  let extensionBase : Base := U ^ 2 + 1
  let splitBase : Base := U * (U - 1)
  unless inverseElimination? extensionBase V (2 : Nested) == some (scalar (1 / 2)) do
    throw (IO.userError "elimination inverse: scalar unit")
  unless (inverseElimination? splitBase V (liftBase U)).isNone do
    throw (IO.userError "elimination inverse: base zero divisor")
  unless inverseElimination? splitBase V (liftBase (U + 1)) ==
      some (liftBase (1 - CPolynomial.C (1 / 2 : ℚ) * U)) do
    throw (IO.userError "elimination inverse: split base components")
  unless inverseElimination? extensionBase V (liftBase U) == some (liftBase (-U)) do
    throw (IO.userError "elimination inverse: extension-only base")
  unless inverseElimination? extensionBase (V ^ 2 - 2) (liftBase U + V) ==
      some (scalar (1 / 3) * (V - liftBase U)) do
    throw (IO.userError "elimination inverse: mixed-variable extension unit")
  unless (inverseElimination? extensionBase (V ^ 2 + 1) (V - liftBase U)).isNone do
    throw (IO.userError "elimination inverse: mixed-variable zero divisor")
  let splitFiber : Nested := V * (V - 1)
  let splitDenominator : Nested := liftBase U + V + 1
  let splitInverse : Nested :=
    1 - scalar (1 / 2) * liftBase U - scalar (1 / 2) * V + scalar (1 / 3) * liftBase U * V
  unless inverseElimination? splitBase splitFiber splitDenominator == some splitInverse do
    throw (IO.userError "elimination inverse: four geometric components")
  unless inverseElimination? splitBase splitFiber splitDenominator ==
      inverseRepresentative? splitBase splitFiber splitDenominator do
    throw (IO.userError "elimination inverse: executed Cramer refinement")

end ArkLibTest.TowerAlgebraInverseElimination
