/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ShiftRefinement
/-! # Kernel replay of actual center translation -/

namespace ReedSolomon.HiddenDerivative.QuadraticCenterShiftMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[(1, 0), (1, 1)], (1, 1), 1⟩
private def output : Configuration (ZMod 5) → Option (Option (List (Pair (ZMod 5))))
  | .done out => some out
  | _ => none
private def point : Configuration (ZMod 5) → Option (Pair (ZMod 5))
  | .jet x _ => some x
  | _ => none

example : output (runFuel 2 input 137 .start).1 = some (some [(1, 0), (0, 0)]) := by
  decide +kernel
example : (runFuel 2 input 137 .start).2 =
    ⟨{ additions := 16, multiplications := 20, negations := 2, control := 366,
       data := 1166, constants := 94, output := 13 }, 12⟩ := by decide +kernel
example : point (runFuel 2 input 8 .start).1 = some (4, 4) := by decide +kernel
example : (runFuel 2 input 1 .start).2.base.data = 6 := by decide +kernel
example : (runFuel 2 input 1 (.negate ⟨2, (1, 1), (1, 1)⟩ (.start .neg))).2 =
    ⟨{ control := 2, data := 13, constants := 10 }, 0⟩ := by decide +kernel
example : (runFuel 2 input 1 (.prepare (.pad 1 []))).2 =
    ⟨{ control := 2, data := 9, constants := 2 }, 2⟩ := by decide +kernel
example : output (runFuel 2 input 1 (.prepare (.done none))).1 = some none := by decide +kernel
example : (runFuel 2 input 1 (.prepare (.done none))).2.base.output = 1 := by decide +kernel
example : point (runFuel 2 input 1
    (.negate ⟨2, (1, 1), (1, 1)⟩ (.done (.pair (2, 3))))).1 = some (2, 3) := by
  decide +kernel
example : output (runFuel 2 input 0 (.prepare (.done none))).1 = none := by decide +kernel

example : (runFuel 2 input 1 (.jet (1, 1) (.ready (.initialize [] 1 [])))).2.base.control = 2 := by
  decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticCenterShiftMachine
