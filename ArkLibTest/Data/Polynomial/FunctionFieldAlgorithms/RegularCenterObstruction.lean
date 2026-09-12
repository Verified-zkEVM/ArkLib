/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RegularCenterObstruction
import Mathlib.Algebra.Field.ZMod

/-! Executed fixed-Sylvester obstruction tests over `ZMod 5`. -/

namespace RegularCenterObstructionTests

open CompPoly CPolynomial
open Polynomial.FunctionFieldAlgorithms.RegularCenterObstruction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev E := ZMod 5

/-- `X Y² + Y + 4` has a vanishing leading coefficient at `X = 0`, a repeated-root
fiber at `X = 1`, and a regular degree-two fiber at `X = 2`. -/
private def testPolynomial : CBivariate E :=
  CPolynomial.ofArray #[CPolynomial.C 4, CPolynomial.C 1, CPolynomial.X]

/-- A concrete certified input used to execute the proof-carrying producer path. -/
private def linearInput : Input E where
  polynomial :=
    (CPolynomial.X : CBivariate E) - CPolynomial.C (CPolynomial.X : CPolynomial E)
  primitive := by
    have hmonic :
        (CBivariate.toPoly ((CPolynomial.X : CBivariate E) -
          CPolynomial.C (CPolynomial.X : CPolynomial E))).Monic := by
      simpa [CBivariate.toPoly_eq_map, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
        CPolynomial.C_toPoly] using
          (Polynomial.monic_X_sub_C (Polynomial.X : Polynomial E))
    exact hmonic.isPrimitive
  positiveDegree := by
    have hdeg := CBivariate.natDegreeY_toPoly
      ((CPolynomial.X : CBivariate E) - CPolynomial.C (CPolynomial.X : CPolynomial E))
    change (CBivariate.toPoly ((CPolynomial.X : CBivariate E) -
      CPolynomial.C (CPolynomial.X : CPolynomial E))).natDegree =
        ((CPolynomial.X : CBivariate E) -
          CPolynomial.C (CPolynomial.X : CPolynomial E)).natDegree at hdeg
    rw [← hdeg]
    simp [CBivariate.toPoly_eq_map, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
      CPolynomial.C_toPoly, CPolynomial.ringEquiv_apply]
  coprimeDerivative := by
    simp only [functionFieldPolynomial, CBivariate.toPoly_eq_map, CPolynomial.toPoly_sub,
      CPolynomial.X_toPoly, CPolynomial.C_toPoly,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
    exact isCoprime_one_right

/-- The expected derivative resultant is `X(X-1)` and the complete obstruction is
`X²(X-1)`.  All values are obtained from the executable determinant producer. -/
def run : IO Unit := do
  let x : CPolynomial E := CPolynomial.X
  unless linearInput.produce == 1 do
    throw (IO.userError "certified linear input produced the wrong obstruction")
  let T := testPolynomial
  let resultant := derivativeResultant T
  let D := obstruction T
  unless resultant == x * (x - 1) do
    throw (IO.userError "fixed Sylvester determinant returned the wrong derivative resultant")
  unless D == x * x * (x - 1) do
    throw (IO.userError "leading-coefficient/resultant obstruction is incorrect")
  unless CPolynomial.eval 2 D != 0 do
    throw (IO.userError "regular center was rejected by the obstruction")
  let goodFiber := fiber T 2
  unless goodFiber.natDegree == 2 && goodFiber != 0 do
    throw (IO.userError "regular center did not preserve the Y-degree")
  let some inverse := CPolynomial.inverseMod? goodFiber.derivative goodFiber
    | throw (IO.userError "regular fiber did not execute a derivative inverse")
  let xgcd := CPolynomial.normXgcd goodFiber.derivative goodFiber
  unless inverse == xgcd.2.1 &&
      xgcd.2.1 * goodFiber.derivative + xgcd.2.2 * goodFiber == 1 do
    throw (IO.userError "returned derivative inverse failed its Bezout certificate")
  let monicFiber := CPolynomial.monicNormalize goodFiber
  let some monicInverse := CPolynomial.inverseMod? goodFiber.derivative monicFiber
    | throw (IO.userError "regular fiber did not execute an inverse modulo its monic form")
  unless (goodFiber.derivative * monicInverse).modByMonic monicFiber ==
      (1 : CPolynomial E).modByMonic monicFiber do
    throw (IO.userError "returned monic-fiber inverse failed modular multiplication")
  unless CPolynomial.eval 0 T.leadingCoeff == 0 do
    throw (IO.userError "leading-coefficient bad center was not exercised")
  unless CPolynomial.eval 0 D == 0 do
    throw (IO.userError "obstruction accepted a center with vanishing leading coefficient")
  unless CPolynomial.eval 1 T.leadingCoeff != 0 do
    throw (IO.userError "resultant canary unexpectedly killed the leading coefficient")
  unless CPolynomial.eval 1 resultant == 0 do
    throw (IO.userError "repeated-root bad center was not detected by the resultant")
  unless CPolynomial.eval 1 D == 0 do
    throw (IO.userError "obstruction accepted a repeated-root fiber")

example (hpositive : 0 < testPolynomial.natDegree)
    (hregular : CPolynomial.eval 2 (obstruction testPolynomial) ≠ 0) :
    FiberFacts testPolynomial 2 :=
  fiberFacts_of_eval_obstruction_ne_zero testPolynomial 2 hpositive hregular

example (input : Input E) : input.produce ≠ 0 := obstruction_ne_zero input

example (T : CBivariate E) (hT : 0 < T.natDegree) :
    (obstruction T).natDegree ≤
      2 * T.natDegree * Polynomial.Bivariate.degreeX (CBivariate.toPoly T) :=
  obstruction_natDegree_le T hT

#print axioms sylvesterResultant_eq
#print axioms derivativeResultant_toPoly_assignment_order
#print axioms obstruction_ne_zero
#print axioms obstruction_natDegree_le
#print axioms fiberFacts_of_eval_obstruction_ne_zero
#print axioms map_obstruction_toPoly

end RegularCenterObstructionTests
