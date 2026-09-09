/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateOutputRefinement
/-! # Kernel checks of coordinate collection, retained payloads and ordered output -/

namespace ReedSolomon.ListDecoding.QuadraticCanonicalOutputMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def record (x : ZMod 5 × ZMod 5) : Record (ZMod 5 × ZMod 5) :=
  ⟨⟨⟨[], none⟩, [[]], [((1, 0), [])]⟩, (1, 1), [x]⟩
private def output : Configuration (ZMod 5) → Option (List (List (ZMod 5)))
  | .done out => some out
  | _ => none
private def payload : Configuration (ZMod 5) → Option (ℕ × (ZMod 5 × ZMod 5))
  | .accept _ _ _ input _ => some (input.order, input.center)
  | _ => none

/-- Empty input still executes scan, reversal and final emission, with the full ledger. -/
example : output (runFuel 2 0 [(1, 1)] 1 1 0 [] 4 (.start [])).1 = some [] ∧
    (runFuel (F := ZMod 5) 2 0 [(1, 1)] 1 1 0 [] 4 (.start [])).2 = 13 := by
  decide +kernel

/-- Record launch pays for and retains its five-field input without changing the center. -/
example :
    payload (runFuel 2 7 [(1, 1)] 1 1 0 [] 1 (.scan [record (2, 0)] [])).1 =
      some (7, (1, 1)) ∧
    (runFuel 2 7 [(1, 1)] 1 1 0 [] 1 (.scan [record (2, 0)] [])).2 = 17 := by
  decide +kernel

/-- Actual acceptance rejects the imaginary cell while preserving order and duplicates. -/
example : output (runFuel 2 0 [(1, 1)] 1 1 0 [] 2048
    (.start [record (2, 0), record (4, 1), record (3, 0), record (2, 0)])).1 =
      some [[2], [3], [2]] := by decide +kernel

end ReedSolomon.ListDecoding.QuadraticCanonicalOutputMachine
