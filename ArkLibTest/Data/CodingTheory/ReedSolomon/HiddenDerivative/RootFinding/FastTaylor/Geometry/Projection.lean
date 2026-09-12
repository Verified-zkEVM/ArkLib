/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Projection

/-! A nonidentity shear preserves polynomial coefficients and regular-point evaluations. -/

open CPoly CPoly.CMvPolynomial
open ReedSolomon.HiddenDerivative.FastTaylor.Geometry

namespace FastTaylorLinearSubstitutionTests

private def shear : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
private def unshear : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]
private def equation : CMvPolynomial 2 ℤ := X 0 - X 1 ^ 2

example : shear * unshear = 1 := by decide

example (u : Fin 2 → ℤ) :
    (projectPolynomial shear equation).eval (unshear.mulVec u) = equation.eval u :=
  eval_projectPolynomial_inverse shear unshear (by decide) equation u

/-- Exercise actual stored substitution, inverse substitution, and a regular point. -/
def run : IO Unit := do
  let projected := projectPolynomial shear equation
  unless projected == X 0 + X 1 - X 1 ^ 2 do
    throw (IO.userError "linear projection produced incorrect coefficients")
  unless projectPolynomial unshear projected == equation do
    throw (IO.userError "inverse linear projection failed")
  unless projected.eval ![2, 2] == 0 do
    throw (IO.userError "linear projection lost an equation point")
  unless (projectPolynomial shear (1 : CMvPolynomial 2 ℤ)).eval ![0, 0] == 1 do
    throw (IO.userError "linear projection discarded a regular point")

end FastTaylorLinearSubstitutionTests
