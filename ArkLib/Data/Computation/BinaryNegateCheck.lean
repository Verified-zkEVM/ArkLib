/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryNegateField

/-!
# Modular negation execution checks

The scan must restore its operand on the same physical tape before subtraction. A padded zero
must select explicit input clearing rather than return a nonreduced modulus.
-/

@[expose] public section

namespace Computation.BinaryNegateMachine

/-- Nonzero residues and padded zero execute the same fixed controller. -/
example :
    runFuel 19 (.start [true, false, true] [true, true]) =
      .subtract (.normalize (.word [false, true])) ∧
    runFuel 19 (.start [true, false, true] []) = .subtract (.normalize (.word [])) ∧
    runFuel 19 (.start [true, false, true] [false, false, false]) =
      .subtract (.normalize (.word [])) ∧
    runFuel 15 (.start [false, true] [true]) =
      .subtract (.normalize (.word [true])) := by
  decide +kernel

/-- Restoration and clearing phase boundaries are charged; RAM remains identical. -/
example :
    let mem := AddressedBits.Memory.node true .empty .empty
    runFuel 7 (.start [true, false, true] [true, true]) =
      .subtract (.start [true, false, true] [true, true] false) ∧
    runFuel 12 (.start [true, false, true] [false, false, false]) = .clear [] [] ∧
    ramRunFuel 13 (mem, .start [true, false, true] [false, false, false]) =
      (mem, .subtract (.normalize (.word []))) := by
  decide +kernel

end Computation.BinaryNegateMachine
