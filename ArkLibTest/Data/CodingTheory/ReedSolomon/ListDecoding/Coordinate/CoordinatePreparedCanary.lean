/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinatePreparedRefinement
/-! # Kernel replay of the complete prepared coordinate decoder -/

namespace ReedSolomon.ListDecoding.QuadraticPreparedDecoderMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[(0, 0)], [(0, 0)], [(0, 0)], 0, 0, 1, 1, 1⟩
private def ts : List (Term (ZMod 5)) := [(1, [(1, 1)])]
private def ri : HiddenDerivative.QuadraticStageRootsMachine.Input (ZMod 5) :=
  ⟨[(0, 0)], [((1, 0), [(1, 1)])], 0⟩
private abbrev run := runFuel (2 : ZMod 5) input
private def output : Configuration (ZMod 5) → Option (Option (List (List (ZMod 5))))
  | .done out => some out
  | _ => none

example : output (run 450 (.start ts)).1 = some (some [[0]]) := by decide +kernel
example : (run 450 (.start ts)).2 = 10143 := by decide +kernel
example : output (run 2 (.roots ri (.done none))).1 = some none := by decide +kernel
example : output (run 7 (.roots ri (.done (some [])))).1 = some (some []) := by decide +kernel
example : (run 7 (.roots ri (.done (some [])))).2 = 36 := by decide +kernel
example : (run 1 (.start ts)).2 = 4 := by decide +kernel
example : (run 1 (.convert (.scan ts []))).2 = 15 := by decide +kernel
example : (run 1 (.roots ri (.start [(0, 0)]))).2 = 11 := by decide +kernel
example : (run 1 (.collect (.start []))).2 = 7 := by decide +kernel
example : (run 1 (.convert (.done ri.terms))).2 = 8 := by decide +kernel
example : (run 1 (.done none)).2 = 0 := by decide +kernel

end ReedSolomon.ListDecoding.QuadraticPreparedDecoderMachine
