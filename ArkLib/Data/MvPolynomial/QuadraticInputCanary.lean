/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.QuadraticInputSemantics

/-!
# Literal coordinate-allocation checks

Distinct coefficients and factor vectors detect reversal or coordinate swaps. Zero and repeated
terms must remain present. A short run retains its exact suspended output rather than emitting
early. These are kernel evaluations of the program, not uses of its correctness theorem.
-/

@[expose] public section

namespace MvPolynomial.QuadraticInputMachine

private def terms : List (Term (ZMod 3)) :=
  [(2, [(0, 1), (1, 0)]), (0, [(0, 0), (1, 2)]), (2, [(0, 1), (1, 0)])]

private def expected : List (Term (QuadraticAlgebra (ZMod 3) 2 0)) :=
  [(⟨2, 0⟩, [(0, 1), (1, 0)]), (⟨0, 0⟩, [(0, 0), (1, 2)]),
    (⟨2, 0⟩, [(0, 1), (1, 0)])]

example : runFuel 9 (.scan terms [] : Configuration (ZMod 3) 2) =
    (.done expected, { control := 9, data := 52, constants := 3, output := 1 }) := by
  decide +kernel

example : runFuel 8 (.scan terms [] : Configuration (ZMod 3) 2) =
    (.emit expected, { control := 8, data := 50, constants := 3 }) := by decide +kernel

theorem empty_input_emits_empty_coordinates :
    runFuel 3 (.scan [] [] : Configuration (ZMod 3) 2) =
    (.done [], { control := 3, data := 7, output := 1 }) := by decide +kernel

end MvPolynomial.QuadraticInputMachine
