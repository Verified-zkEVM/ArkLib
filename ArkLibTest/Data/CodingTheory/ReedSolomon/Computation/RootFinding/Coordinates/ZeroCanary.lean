/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ZeroRefinement
/-! # Kernel replay of coordinate residual acceptance boundaries -/

namespace ReedSolomon.HiddenDerivative.QuadraticResidualZeroMachine

private abbrev P := Pair (ZMod 5)
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def input : Input (ZMod 5) := ⟨[], [], (1, 1), 0⟩
private def output : Configuration (ZMod 5) → Option Bool
  | .done b => some b
  | _ => none
private def cursor : Configuration (ZMod 5) → Option (List (Entry (ZMod 5)))
  | .scan ps => some ps
  | _ => none

example : output (runFuel 2 input 12 (.scan [((1, 1), (0, 0))])).1 = some true := by
  decide +kernel
example : output (runFuel 2 input 11 (.scan [((1, 1), (0, 2))])).1 = some false := by
  decide +kernel
example : output (runFuel 2 input 11 (.scan [((1, 1), (2, 0))])).1 = some false := by
  decide +kernel
example : cursor (runFuel 2 input 10
    (.scan [((1, 1), (0, 0)), ((2, 3), (1, 0))])).1 = some [((2, 3), (1, 0))] := by
  decide +kernel
example : (runFuel 2 input 1 (.start ([] : List P))).2.base.data = 7 := by decide +kernel
example : (runFuel 2 input 1 (.scan [((1, 1), (0, 0))])).2.base.constants = 2 := by
  decide +kernel
example : (runFuel 2 input 1 (.scan [((1, 1), (0, 0))])).2.base.data = 10 := by
  decide +kernel
example : (runFuel 2 input 1 (.check [] ⟨2, (0, 0), (0, 0)⟩ (.start .equal))).2 =
    ⟨{ control := 2, data := 13, constants := 10 }, 0⟩ := by decide +kernel
example : (runFuel 2 input 1 (.emit true)).2.base.output = 1 := by decide +kernel
example : output (runFuel 2 input 0 (.emit true)).1 = none := by decide +kernel

example : output (runFuel 2 input 43 (.start [(1, 1)])).1 = some true := by decide +kernel
example : (runFuel 2 input 43 (.start [(1, 1)])).2 =
    ⟨{ additions := 2, equalities := 2, control := 116, data := 336,
       constants := 26, output := 7 }, 4⟩ := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticResidualZeroMachine
