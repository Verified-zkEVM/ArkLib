/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.PaddedMul

/-!
# Fixed-width multiplication execution checks

The same controller normalizes padded operands, multiplies, then pads its output. Tests cover
nonempty representations of zero, modular wraparound, retained padding and dirty RAM.
-/

@[expose] public section

namespace Computation.PaddedMul

example :
    runFuel 316 (.normalizing [true, true] [false, true]
      (.startAdd [false, true] [] false)) =
      .padding [false, true] (.padding [true, true] (.done [true, false])) ∧
    runFuel 634 (.normalizing [true, false, true] [false, false, true]
      (.startAdd [true, true, false] [] false)) =
      .padding [false, false, true] (.padding [true, false, true] (.done [false, true, false])) ∧
    runFuel 316 (.normalizing [true, true] [true, false]
      (.startAdd [false, false] [] false)) =
      .padding [true, false] (.padding [true, true] (.done [false, false])) := by
  decide +kernel

example :
    step (.normalizing [true, true] [true, false] (.word [])) =
      some (.multiplying (.start [true, true] [] [true, false])) ∧
    step (.multiplying (.done [true, true] [true, false] [])) =
      some (.padding [true, false] (.shaping [] (.shapeStart [true, true]))) := by
  decide +kernel

example :
    let mem := AddressedBits.Memory.node true .empty .empty
    ramRunFuel 760 (mem, .normalizing [true, false, true, false] [false, true, false, false]
      (.startAdd [true, true, false, false] [] false)) =
      (mem, .padding [false, true, false, false]
        (.padding [true, false, true, false] (.done [true, false, false, false]))) := by
  decide +kernel

end Computation.PaddedMul
