/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Multilinear.Fold
import Mathlib.Data.ZMod.Basic
import Lean.Compiler.IR

/-! # Formal head-folding and cached equality weights in arbitrary commutative rings -/

open CompPoly CompPoly.CMlPolynomialEval MvPolynomial

namespace MultilinearFoldTest

/-- The external runtime caller uses the existing head-fold algorithm. -/
def caller {R : Type} [CommRing R] {n : Nat}
    (table : CMlPolynomialEval R (n + 1)) (r : R) : CMlPolynomialEval R n :=
  evalMleLayer table r

theorem caller_polynomial {R : Type} [CommRing R] {n : Nat}
    (table : CMlPolynomialEval R (n + 1)) (r : R) :
    MLE (fun u => (caller table r).get (finFunctionFinEquiv u)) =
      Polynomial.eval (C r) (MvPolynomial.finSuccEquiv R n
        (MLE (fun u => table.get (finFunctionFinEquiv u)))) :=
  MLE_evalMleLayer table r

def asymmetric : CMlPolynomialEval Int 3 := #v[2,5,11,17,23,31,41,47]
def firstFold : CMlPolynomialEval Int 2 := caller asymmetric 3
def secondFold : CMlPolynomialEval Int 1 := caller firstFold (-2)
def finalFold : CMlPolynomialEval Int 0 := caller secondFold 5

-- ZMod4 has zero divisors; none of these statements request a field/domain instance.
abbrev R := ZMod 4

theorem zeroRoundFormal :
    MLE (fun u => (caller (#v[3,1] : CMlPolynomialEval R 1) 2).get
      (finFunctionFinEquiv u)) =
      Polynomial.eval (C (2 : R)) (MvPolynomial.finSuccEquiv R 0
        (MLE (fun u => (#v[3,1] : CMlPolynomialEval R 1).get (finFunctionFinEquiv u)))) :=
  MLE_evalMleLayer _ _

def oneFold : CMlPolynomialEval R 0 := caller #v[(3 : R),1] (2 : R)

def zeroCoordinateKernel : CMlPolynomialEval R 1 :=
  caller (lagrangeBasisFast #v[(0 : R),2]) 1

def scaledKernel : CMlPolynomialEval R 2 := (2 : R) • lagrangeBasisFast #v[(3 : R),2]
def zeroDivisorKernel : CMlPolynomialEval R 1 := caller scaledKernel 0

theorem scaledCacheFormal :
    MLE (fun u => scaledKernel.get (finFunctionFinEquiv u)) =
      C (2 : R) * eqPolynomial (#v[(3 : R),2].get) :=
  MLE_smul_lagrangeBasisFast _ _

theorem zeroScalarFormal :
    MLE (fun u => ((0 : R) • lagrangeBasisFast #v[(3 : R),2]).get
      (finFunctionFinEquiv u)) = 0 := by
  rw [MLE_smul_lagrangeBasisFast, map_zero, zero_mul]

theorem emptyCacheFormal :
    MLE (fun u => (lagrangeBasisFast (#v[] : Vector R 0)).get (finFunctionFinEquiv u)) =
      eqPolynomial (#v[] : Vector R 0).get :=
  MLE_lagrangeBasisFast _

open Lean Elab Command

run_cmd do
  unless firstFold == #v[11,29,47,59] do throwError "head fold lost adjacent little-endian pairs"
  unless secondFold == #v[-25,23] do throwError "second coordinate fold changed"
  unless finalFold == #v[215] do throwError "zero-variable terminal fold changed"
  unless oneFold == #v[3] do
    throwError "head fold incorrectly requires field/domain arithmetic"
  unless zeroCoordinateKernel == #v[0,0] do throwError "zero coordinate kernel factor failed"
  unless scaledKernel == #v[0,2,0,0] do throwError "scaled cache initialization changed"
  unless zeroDivisorKernel == #v[0,0] do throwError "zero divisor scalar factor failed"
  unless (0 : R) • lagrangeBasisFast #v[(3 : R),2] == #v[0,0,0,0] do
    throwError "zero scalar equality cache failed"
  unless lagrangeBasisFast (#v[] : Vector R 0) == #v[1] do
    throwError "zero-variable equality cache failed"

run_cmd do
  for name in #[``caller, ``firstFold, ``secondFold, ``finalFold,
      ``oneFold, ``zeroCoordinateKernel, ``scaledKernel, ``zeroDivisorKernel] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing formal fold external caller IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``MLE_evalMleLayer, ``MLE_lagrangeBasisFast, ``MLE_smul_lagrangeBasisFast,
      ``caller_polynomial, ``zeroRoundFormal, ``scaledCacheFormal, ``zeroScalarFormal,
      ``emptyCacheFormal] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected formal fold/cache axiom: {name}"

end MultilinearFoldTest
