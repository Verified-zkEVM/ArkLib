/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticVandermondeRefinement

/-!
# Kernel checks for coordinate Vandermonde construction

Repeated points with distinct values test row order and pairing. Empty and zero-width inputs
check allocation and output charges. The final unused power still executes, and arithmetic
calls use their retained payload rather than reconstructing it from the surrounding frame.
-/

@[expose] public section

namespace Matrix.QuadraticVandermondeMachine

private def observe : Configuration (ZMod 3) → Option (List (Row (ZMod 3)))
  | .ready (.done rows) => some rows
  | _ => none

private def repeated := runFuel (2 : ZMod 3) 2 130
  (.ready (.start [((1, 1), (0, 1)), ((1, 1), (2, 0)), ((2, 1), (1, 2))]))

example : (observe repeated.1, repeated.2) =
    (some [([(1, 0), (1, 1)], (0, 1)), ([(1, 0), (1, 1)], (2, 0)),
      ([(1, 0), (2, 1)], (1, 2))],
      ⟨⟨12, 30, 0, 0, 0, 220, 831, 66, 7⟩, 15⟩) := by decide +kernel

private def noColumns := runFuel (2 : ZMod 3) 0 10
  (.ready (.start [((1, 1), (2, 1))]))

example : (observe noColumns.1, noColumns.2) =
    (some [([], (2, 1))], ⟨⟨0, 0, 0, 0, 0, 10, 39, 2, 1⟩, 1⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) 3 4 (.ready (.start []))

example : (observe empty.1, empty.2) =
    (some [], ⟨⟨0, 0, 0, 0, 0, 4, 9, 0, 1⟩, 0⟩) := by decide +kernel

private def powerValue : Configuration (ZMod 3) → Option (ℕ × Pair (ZMod 3))
  | .ready (.power _ _ _ _ n p _) => some (n, p)
  | _ => none

-- The one emitted coefficient is 1, but the next power must still be computed.
theorem final_unused_power_is_computed :
    (match (runFuel (2 : ZMod 3) 1 19
      (.ready (.start [((1, 1), (2, 1))]))).1 with
    | .ready (.power _ _ _ _ n p _) => some (n, p)
    | _ => none) = some (0, (1, 1)) := by decide +kernel

-- The saved payload deliberately differs from the external parameter and frame's point.
example : powerValue (runFuel (0 : ZMod 3) 1 15
    (.call ⟨(0, 0), (0, 0), [], [], 0, []⟩
      ⟨2, (1, 1), (2, 1)⟩ (.start .mul))).1 = some (0, (1, 0)) := by decide +kernel

end Matrix.QuadraticVandermondeMachine
