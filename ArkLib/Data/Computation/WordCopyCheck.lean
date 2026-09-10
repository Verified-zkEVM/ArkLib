/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.WordCopyMachine

/-! # Kernel replay of destination clearing, retained source order and exact handoffs -/

@[expose] public section

namespace Computation.WordCopyMachine

example :
    runFuel 3 (.clear [true, false] [false, true, true]) = .clear [true, false] [] ∧
    runFuel 4 (.clear [true, false] [false, true, true]) = .save [true, false] [] ∧
    runFuel 6 (.clear [true, false] [false, true, true]) = .save [] [false, true] ∧
    runFuel 7 (.clear [true, false] [false, true, true]) = .restore [false, true] [] [] ∧
    runFuel 9 (.clear [true, false] [false, true, true]) =
      .restore [] [true, false] [true, false] ∧
    runFuel 10 (.clear [true, false] [false, true, true]) =
      .done [true, false] [true, false] := by
  decide +kernel

example :
    runFuel 5 (.clear [] [true, false]) = .done [] [] ∧
    runFuel 3 (.clear [] []) = .done [] [] ∧
    runFuel 9 (.clear [true, false, false] []) =
      .done [true, false, false] [true, false, false] ∧
    runFuel 8 (.clear [false, false] [true]) = .done [false, false] [false, false] := by
  decide +kernel

/-- A suspended restore preserves rather than silently discarding existing prefixes. -/
example : runFuel 3 (.restore [true, false] [false] [true, true]) =
    .done [false, true, false] [false, true, true, true] := by
  decide +kernel

end Computation.WordCopyMachine
