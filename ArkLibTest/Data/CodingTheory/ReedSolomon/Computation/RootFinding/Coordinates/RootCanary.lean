/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootRefinement
/-! # Kernel checks for retained accepted-candidate control -/

namespace ReedSolomon.HiddenDerivative.QuadraticRegularRootMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[(1, 1)], [], (1, 1), 0⟩
private def output : Configuration (ZMod 5) → Option (Option (List (Pair (ZMod 5))))
  | .done out => some out
  | _ => none
private def shifted : Configuration (ZMod 5) → Option (List (Pair (ZMod 5)) × Pair (ZMod 5) × ℕ)
  | .shift p .start => some (p.coefficients, p.center, p.degree)
  | _ => none
private def checkedInput : Configuration (ZMod 5) → Option (List (Pair (ZMod 5)))
  | .check p _ => some p.coefficients
  | _ => none

example : output (runFuel 2 input 0 1 131 (.start [(1, 1)])).1 = some (some [(1, 1)]) := by
  decide +kernel
example : (runFuel 2 input 0 1 131 (.start [(1, 1)])).2 =
    ⟨{ additions := 10, multiplications := 10, negations := 2, equalities := 2, control := 514,
       data := 1392, constants := 78, output := 17 }, 15⟩ := by decide +kernel
example : (runFuel 2 input 0 1 1 (.start [])).2.base.data = 7 := by decide +kernel
example : checkedInput (runFuel 2 input 0 1 1
    (.lift [] input (.done (some [(2, 3)])))).1 = some [(2, 3)] := by decide +kernel
example : (runFuel 2 input 0 1 1 (.lift [] input (.done (some [(2, 3)])))).2.base.data = 9 := by
  decide +kernel
example : output (runFuel 2 input 0 1 2 (.lift [] input (.done none))).1 = some none := by
  decide +kernel
example : output (runFuel 2 input 0 1 2 (.check input (.done false))).1 = some none := by
  decide +kernel
example : shifted (runFuel 2 input 4 1 1 (.check input (.done true))).1 =
    some ([(1, 1)], (1, 1), 4) := by decide +kernel
example : (runFuel 2 input 4 1 1 (.check input (.done true))).2.base.data = 8 := by decide +kernel
example : (runFuel 2 input 0 1 1 (.lift [] input (.start []))).2.base.control = 2 := by
  decide +kernel
example : (runFuel 2 input 0 1 1 (.check input (.emit true))).2.base.output = 1 := by
  decide +kernel
example : output (runFuel 2 input 0 1 2
    (.shift ⟨[], (1, 1), 0⟩ (.done (some [(2, 4)])))).1 = some (some [(2, 4)]) := by
  decide +kernel
example : (runFuel 2 input 0 1 1 (.emit none)).2.base.output = 1 := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticRegularRootMachine
