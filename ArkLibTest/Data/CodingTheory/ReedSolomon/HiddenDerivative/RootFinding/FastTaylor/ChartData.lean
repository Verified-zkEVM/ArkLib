/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.ChartData
import Mathlib.Data.ZMod.Basic

/-! Representative stored chart producer and agreement consumer. -/

namespace FastTaylorChartDataTests

open CPoly ReedSolomon.HiddenDerivative.FastTaylor

private def chart : ChartData (ZMod 5) 1 3 where
  center := 1
  projection := 1
  inverseProjection := 1
  equation := CMvPolynomial.X 1 - CMvPolynomial.X 0
  separant := 1
  denominator := 1
  numerators := ![CMvPolynomial.X 0, CMvPolynomial.X 1, CMvPolynomial.X 1 ^ 2]

/-- The public payload and extension-compatible consumer compile together. -/
example {L : Type*} [CommRing L] (base : ZMod 5 →+* L) (point : Fin 2 → L)
    (alpha received : ZMod 5) :
    CMvPolynomial.eval₂ base point (chart.agreement alpha received) =
      (∑ j : Fin 3, CMvPolynomial.eval₂ base point (chart.numerators j) *
        (base alpha - base chart.center) ^ j.val) -
      base received * CMvPolynomial.eval₂ base point chart.denominator :=
  chart.eval₂_agreement base point alpha received

/-- Check that the center shift and received-symbol sign are present in the runtime residual. -/
def run : IO Unit := do
  let residual := chart.agreement 3 4
  unless residual = CMvPolynomial.X 0 + CMvPolynomial.C 2 * CMvPolynomial.X 1 +
      CMvPolynomial.C 4 * CMvPolynomial.X 1 ^ 2 - 4 do
    throw (IO.userError "Taylor chart agreement coefficient mismatch")
  unless CMvPolynomial.eval ![2, 2] residual = 3 do
    throw (IO.userError "Taylor chart agreement evaluation mismatch")

end FastTaylorChartDataTests
