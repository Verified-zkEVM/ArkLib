/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinatePreparedInput
/-! # Literal coefficient allocation and exact preparation ledger -/

namespace ReedSolomon.ListDecoding.QuadraticPreparedInputMachine

private def ts : List (Term ℕ) := [(7, [(1, 2)]), (3, []), (7, [(1, 2)])]
private def output : Configuration ℕ → Option (List (Term (ℕ × ℕ)))
  | .done out => some out
  | _ => none

example : output (runFuel 9 (.scan ts [])).1 =
    some [((7, 0), [(1, 2)]), ((3, 0), []), ((7, 0), [(1, 2)])] := by decide +kernel
example : (runFuel 9 (.scan ts [])).2 =
    { control := 9, data := 52, constants := 3, output := 1 } := by decide +kernel
example : output (runFuel 3 (.scan [] [])).1 = some [] := by decide +kernel
example : (runFuel 1 (.scan ts [])).2.constants = 1 := by decide +kernel
example : (runFuel 1 (.scan ts [])).2.data = 10 := by decide +kernel
example : (runFuel 1 (.emit [] : Configuration ℕ)).2.output = 1 := by decide +kernel

end ReedSolomon.ListDecoding.QuadraticPreparedInputMachine
