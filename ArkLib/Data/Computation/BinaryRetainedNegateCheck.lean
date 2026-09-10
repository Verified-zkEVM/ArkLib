/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryRetainedNegateField

/-!
# Retained-modulus negation checks

Zero, nonzero and padded operands use actual copy/restore and negation successors. A boundary
check verifies that two physical modulus copies have been constructed before arithmetic starts.
-/

@[expose] public section

namespace Computation.BinaryRetainedNegateMachine

/-- Actual scalar negation retains the exact modulus word, including its padding. -/
example :
    runFuel 29 (.start [true, false, true] [true, true]) =
      .done [true, false, true] [false, true] ∧
    runFuel 29 (.start [true, false, true] [false, false, false]) =
      .done [true, false, true] [] ∧
    runFuel 35 (.start [true, false, true, false] [true, true]) =
      .done [true, false, true, false] [false, true] ∧
    runFuel 23 (.start [false, true] [true]) = .done [false, true] [true] := by
  decide +kernel

/-- Copy preparation creates the retained and arithmetic modulus on distinct tapes. -/
example :
    let mem := AddressedBits.Memory.node true .empty .empty
    runFuel 9 (.start [true, false, true] [true, true]) =
      .negate [true, false, true] (.start [true, false, true] [true, true]) ∧
    ramRunFuel 29 (mem, .start [true, false, true] [true, true]) =
      (mem, .done [true, false, true] [false, true]) := by
  decide +kernel

end Computation.BinaryRetainedNegateMachine
