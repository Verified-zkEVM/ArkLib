/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.PaddedNegate

/-! # Kernel checks for retained-modulus negation and fixed-width output -/

@[expose] public section

namespace Computation.PaddedNegate

example :
    runFuel 49 (.negating (.start [true, false, true] [true, true, false])) =
      .padding (.padding [true, false, true] (.done [false, true, false])) ∧
    runFuel 49 (.negating (.start [true, false, true] [false, false, false])) =
      .padding (.padding [true, false, true] (.done [false, false, false])) ∧
    runFuel 59 (.negating (.start [true, false, true, false] [true, true])) =
      .padding (.padding [true, false, true, false] (.done [false, true, false, false])) := by
  decide +kernel

example :
    let mem := AddressedBits.Memory.node true .empty .empty
    ramRunFuel 39 (mem, .negating (.start [false, true] [true, false])) =
      (mem, .padding (.padding [false, true] (.done [true, false]))) ∧
    step (.negating (.done [false, true] [true])) =
      some (.padding (.shaping [true] (.shapeStart [false, true]))) := by
  decide +kernel

end Computation.PaddedNegate
