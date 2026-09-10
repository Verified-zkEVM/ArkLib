/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.ScalarWordPadding

/-!
# Kernel checks for physically constructed fixed-width scalars

These runs cover padded zero, marker-bit irrelevance, excess-width rejection with saved input,
literal reference restoration, and the precise construction-to-padding handoff.
-/

@[expose] public section

namespace Computation.FixedWidthWordMachine

example : runFuel 9 (.start [true] [false, true, false]) = .done [true, false, false] ∧
    runFuel 9 (.start [] [true, true, true]) = .done [false, false, false] ∧
    runFuel 3 (.start [] []) = .done [] ∧
    runFuel 4 (.start [true, false, true] [true, false]) =
      .rejected [true] [false, true] := by decide +kernel

example : runFuel 9 (.shapeStart [true, false, true]) =
      .shapeDone [true, false, true] [false, false, false] ∧
    runFuel 8 (.shapeStart [true, false, true]) =
      .shapeRestore [] [true, false, true] [false, false, false] := by decide +kernel

end Computation.FixedWidthWordMachine

namespace Computation.ScalarWordPadding

example : runFuel 19 (.shaping [true] (.shapeStart [true, false, true])) =
      .padding [true, false, true] (.done [true, false, false]) ∧
    runFuel 9 (.shaping [true] (.shapeStart [true, false, true])) =
      .shaping [true] (.shapeDone [true, false, true] [false, false, false]) ∧
    runFuel 10 (.shaping [true] (.shapeStart [true, false, true])) =
      .padding [true, false, true] (.start [true] [false, false, false]) ∧
    runFuel 7 (.shaping [] (.shapeStart [])) = .padding [] (.done []) := by decide +kernel

example :
    let mem := AddressedBits.Memory.node true .empty (.node false .empty .empty)
    ramRunFuel 23 (mem, .shaping [] (.shapeStart [true, false, true, false])) =
      (mem, .padding [true, false, true, false] (.done [false, false, false, false])) := by
  decide +kernel

end Computation.ScalarWordPadding
