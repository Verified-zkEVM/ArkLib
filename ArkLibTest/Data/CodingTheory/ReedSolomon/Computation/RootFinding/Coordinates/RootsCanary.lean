/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootsRefinement
/-! # Kernel replay of ordered coordinate enumeration and collection -/

namespace ReedSolomon.HiddenDerivative.QuadraticJetRootsMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[(1, 1), (2, 3), (1, 1)], [], (1, 1), 0⟩
private def payload : QuadraticRegularRootMachine.Input (ZMod 5) := ⟨[(1, 1)], [], (1, 1), 0⟩
private def output : Configuration (ZMod 5) → Option (Option (List (List (Pair (ZMod 5)))))
  | .done out => some out
  | _ => none
private def scanned : Configuration (ZMod 5) → Option (List (List (Pair (ZMod 5))))
  | .scan _ out _ => some out
  | _ => none
private def preparedInput : Configuration (ZMod 5) → Option (List (Pair (ZMod 5)))
  | .root _ _ _ p _ => some p.coefficients
  | _ => none

example : output (runFuel 2 input 0 1 275 (.start [])).1 =
    some (some [[(1, 1)], [(2, 3)], [(1, 1)]]) := by decide +kernel
example : (runFuel 2 input 0 1 275 (.start [])).2 =
    ⟨{ additions := 12, multiplications := 15, negations := 6, control := 922,
       data := 2516, constants := 96, output := 36 }, 60⟩ := by decide +kernel
example : preparedInput (runFuel 2 input 0 1 1
    (.prepare [] [] [] (.done (some [(2, 4)])))).1 = some [(2, 4)] := by decide +kernel
example : (runFuel 2 input 0 1 1 (.prepare [] [] [] (.done (some [(2, 4)])))).2.base.data = 9 := by
  decide +kernel
example : output (runFuel 2 input 0 1 2 (.prepare [] [] [] (.done none))).1 = some none := by
  decide +kernel
example : output (runFuel 2 input 0 1 2 (.axes [] (.done none))).1 = some none := by decide +kernel
example : scanned (runFuel 2 input 0 1 1
    (.root [] [[(1, 1)]] [] payload (.done none))).1 = some [[(1, 1)]] := by decide +kernel
example : scanned (runFuel 2 input 0 1 2
    (.root [] [[(1, 1)]] [] payload (.done (some [(1, 1)])))).1 =
    some [[(1, 1)], [(1, 1)]] := by decide +kernel
example : (runFuel 2 input 0 1 1 (.root [] [] [] payload (.start []))).2.base.control = 2 := by
  decide +kernel
example : (runFuel 2 input 0 1 1 (.axes [] (.start []))).2.base.control = 2 := by decide +kernel
example : (runFuel 2 input 0 1 1 (.product [] (.start []))).2.base.control = 2 := by decide +kernel
example : (runFuel 2 input 0 1 1 (.prepare [] [] [] (.pad 1 []))).2.base.constants = 2 := by
  decide +kernel
example : (runFuel 2 input 0 1 1 (.reverse [] [])).2.base.data = 3 := by decide +kernel
example : (runFuel 2 input 0 1 1 (.emit none)).2.base.output = 1 := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticJetRootsMachine
