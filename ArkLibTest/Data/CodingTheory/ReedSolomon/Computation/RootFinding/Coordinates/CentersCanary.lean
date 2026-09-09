/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.CentersRefinement
/-! # Kernel checks for coordinate centers and separately allocated records -/

namespace ReedSolomon.HiddenDerivative.QuadraticCenterRootsMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[(1, 1)], [], 0⟩
private def payload : QuadraticJetRootsMachine.Input (ZMod 5) := ⟨[(1, 1)], [], (1, 1), 0⟩
private def output : Configuration (ZMod 5) → Option (Option (List (Record (ZMod 5))))
  | .done out => some out
  | _ => none
private def center : Configuration (ZMod 5) → Option (Pair (ZMod 5))
  | .jets _ _ _ _ p _ => some p.center
  | _ => none
private def record : Configuration (ZMod 5) → Option (Record (ZMod 5))
  | .save r _ _ _ _ _ => some r
  | _ => none

example : output (runFuel 2 input 0 1 119 (.start [])).1 =
    some (some [((1, 1), [(1, 1)])]) := by decide +kernel
example : (runFuel 2 input 0 1 119 (.start [])).2 =
    ⟨{ additions := 4, multiplications := 5, negations := 2, control := 455,
       data := 1175, constants := 32, output := 15 }, 24⟩ := by decide +kernel
example : center (runFuel 2 input 0 1 1 (.scan [(2, 3)] [] [])).1 = some (2, 3) := by
  decide +kernel
example : (runFuel 2 input 0 1 1 (.scan [(2, 3)] [] [])).2.base.data = 10 := by decide +kernel
example : record (runFuel 2 input 0 1 1 (.collect (2, 3) [[(4, 1)]] [] [] [])).1 =
    some ((2, 3), [(4, 1)]) := by decide +kernel
example : output (runFuel 2 input 0 1 6
    (.collect (2, 3) [[(4, 1)]] [] [((2, 3), [(4, 1)])] [])).1 = none := by decide +kernel
example : output (runFuel 2 input 0 1 9
    (.collect (2, 3) [[(4, 1)]] [] [((2, 3), [(4, 1)])] [])).1 =
    some (some [((2, 3), [(4, 1)]), ((2, 3), [(4, 1)])]) := by decide +kernel
example : output (runFuel 2 input 0 1 2
    (.jets (1, 1) [] [] [] payload (.done none))).1 = some none := by decide +kernel
example : (runFuel 2 input 0 1 1
    (.jets (1, 1) [] [] [] payload (.start []))).2.base.control = 2 := by
  decide +kernel
example : (runFuel 2 input 0 1 1 (.reverse [] [])).2.base.data = 3 := by decide +kernel
example : (runFuel 2 input 0 1 1 (.emit none)).2.base.output = 1 := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticCenterRootsMachine
