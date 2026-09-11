/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FieldLiteralFiniteControl

/-! # Kernel checks of finite-head literal construction and suspended child phases -/

@[expose] public section

namespace Computation.FieldLiteralFiniteControl

open FiniteHeadProgram

private def reference : List Bool := [true, false, true, true]
private def view (s : Configuration 24 6) : Fin 24 × List (List Bool) :=
  (s.control, [s.bank 0, s.bank 1, s.bank 2, s.bank 3, s.bank 4, s.bank 5])
private def run (fuel : ℕ) (one : Bool) :=
  view (runFuel program fuel (represent (.start reference one)))

/-- Literal outputs retain every reference bit, exact width and all six physical tape positions. -/
example :
    run 13 false = (22, [[false, false, false, false], [], [], [], reference, []]) ∧
    run 15 true = (22, [[true, false, false, false], [], [], [], reference, []]) ∧
    run 80 true = (22, [[true, false, false, false], [], [], [], reference, []]) := by
  decide +kernel

/-- Restoration and the two low-bit replacement instructions are distinct physical transitions. -/
example :
    run 8 false = (9, [[false], [], [true, false, true], [], [true], []]) ∧
    run 13 true = (20, [[false, false, false, false], [], [], [], reference, []]) ∧
    run 14 true = (21, [[false, false, false], [], [], [], reference, []]) := by
  decide +kernel

/-- Zero-width one rejects, while zero succeeds; neither creates an uncharged cell. -/
example :
    view (runFuel program 6 (represent (.start [] true))) = (23, [[], [], [], [], [], []]) ∧
    view (runFuel program 5 (represent (.start [] false))) = (22, [[], [], [], [], [], []]) := by
  decide +kernel

/-- Arbitrary padding entries preserve their separate spare-output tape and rejected input. -/
theorem padding_preserves_spare_output_and_rejected_input :
    let view := fun (s : Configuration 24 6) ↦
      (s.control, [s.bank 0, s.bank 1, s.bank 2, s.bank 3, s.bank 4, s.bank 5])
    view (runFuel program 20 (represent
      (.shaping false (.start [true, false] [false, true, false])))) =
        (5, [[], [], [], [], [], [true, false, false]]) ∧
    view (runFuel program 20 (represent (.shaping true (.scan [true, false] [] [false])))) =
      (15, [[], [], [false], [], [true, false], []]) := by decide +kernel

end Computation.FieldLiteralFiniteControl
