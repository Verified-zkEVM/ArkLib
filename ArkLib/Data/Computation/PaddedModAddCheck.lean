/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.PaddedModAdd

/-!
# Fixed-width modular-add execution checks

The actual combined controller handles wraparound, padded zero, and leading-zero operands.
The modulus is retained exactly, including its padding, and the output has its physical width.
-/

@[expose] public section

namespace Computation.PaddedModAdd

example :
    runFuel 75 (.adding (.start [true, false, true] [false, true, false]
      [false, false, true])) =
      .padding (.padding [true, false, true] (.done [true, false, false])) ∧
    runFuel 61 (.adding (.start [true, true] [false, true] [true, false])) =
      .padding (.padding [true, true] (.done [false, false])) ∧
    runFuel 89 (.adding (.start [true, false, true, false] [] [])) =
      .padding (.padding [true, false, true, false] (.done [false, false, false, false])) := by
  decide +kernel

example :
    step (.adding (.done [true, false, true] [true])) =
      some (.padding (.shaping [true] (.shapeStart [true, false, true]))) ∧
    tapes (.adding (.done [true, false, true] [true])) =
      tapes (.padding (.shaping [true] (.shapeStart [true, false, true]))) := by
  decide +kernel

example :
    let mem := AddressedBits.Memory.node true .empty .empty
    ramRunFuel 61 (mem, .adding (.start [true, true] [true, false] [true, false])) =
      (mem, .padding (.padding [true, true] (.done [false, true]))) := by
  decide +kernel

end Computation.PaddedModAdd
