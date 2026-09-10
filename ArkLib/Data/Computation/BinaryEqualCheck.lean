/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryEqualField

/-!
# Literal scalar equality execution checks

Arbitrary zero padding affects physical cost but not the Boolean result. The comparison's
ordering and final Boolean result occupy distinct charged control states.
-/

@[expose] public section

namespace Computation.BinaryEqualMachine

/-- Value equality accepts distinct physical encodings and rejects both strict orderings. -/
example :
    runFuel 7 (.compare [true, true] (.startCompare [false, true, false, false] [false, true])) =
      .done [true, true] true ∧
    runFuel 5 (.compare [true, true] (.startCompare [] [false, false])) =
      .done [true, true] true ∧
    runFuel 5 (.compare [true, true] (.startCompare [true] [false, true])) =
      .done [true, true] false ∧
    runFuel 5 (.compare [true, true] (.startCompare [false, true] [true])) =
      .done [true, true] false ∧
    runFuel 3 (.compare [true, true] (.startCompare [] [])) = .done [true, true] true := by
  decide +kernel

/-- The finite ordering branch is charged, and the same lifted guard preserves RAM. -/
example :
    let mem := AddressedBits.Memory.node true .empty .empty
    runFuel 4 (.compare [true, true] (.startCompare [true] [false, true])) =
      .compare [true, true] (.ordering .lt) ∧
    ramRunFuel 5 (mem, .compare [true, true] (.startCompare [true] [false, true])) =
      (mem, .done [true, true] false) := by
  decide +kernel

end Computation.BinaryEqualMachine
