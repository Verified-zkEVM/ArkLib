/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.PaddedInverse

/-! # Kernel checks for inverse search followed by actual fixed-width padding -/

@[expose] public section

namespace Computation.PaddedInverse

example :
    runFuel 1080 (.inverting (.start [true, true] [false, true])) =
      .padding [false, true] (.padding [true, true] (.done [false, true])) ∧
    runFuel 3430 (.inverting (.start [true, false, true] [false, true, false])) =
      .padding [false, true, false] (.padding [true, false, true] (.done [true, true, false])) ∧
    runFuel 536 (.inverting (.start [false, true] [true, false])) =
      .padding [true, false] (.padding [false, true] (.done [true, false])) := by
  decide +kernel

example :
    runFuel 3430 (.inverting (.start [true, false, true] [false, false, false])) =
      .padding [false, false, false] (.padding [true, false, true] (.done [false, false, false])) ∧
    step (.inverting (.done [true, false, true] [false, true, false] [true, true])) =
      some (.padding [false, true, false]
        (.shaping [true, true] (.shapeStart [true, false, true]))) :=
  by decide +kernel

example :
    let mem := AddressedBits.Memory.node true .empty .empty
    ramRunFuel 1310 (mem, .inverting (.start [true, true, false] [false, true, false])) =
      (mem, .padding [false, true, false]
        (.padding [true, true, false] (.done [false, true, false]))) :=
  by decide +kernel

end Computation.PaddedInverse
