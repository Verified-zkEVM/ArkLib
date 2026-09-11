/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.CoordinateAlphabetMachine

/-! # Kernel checks of explicit coordinate materialization and its allocation ledger -/

@[expose] public section

namespace QuadraticAlgebra.CoordinateAlphabetMachine

private def xs : List (QuadraticAlgebra (ZMod 5) 2 0) := [⟨1, 2⟩, ⟨3, 4⟩, ⟨1, 2⟩]

/-- Nonzero imaginary coordinates, order, and duplicate records all survive. -/
example : runFuel 8 (.scan xs []) = (.done [(1, 2), (3, 4), (1, 2)], 53) := by
  decide +kernel

/-- This nonpalindromic case detects an omitted or duplicated output reversal. -/
theorem nonpalindromic_coordinates_preserve_order :
    runFuel 6 (.scan [⟨1, 2⟩, ⟨3, 4⟩] [] : Configuration (ZMod 5) 2 0) =
    (.done [(1, 2), (3, 4)], 38) := by
  decide +kernel

example :
    runFuel 3 (.scan xs []) = (.scan [] [(1, 2), (3, 4), (1, 2)], 27) ∧
    runFuel 4 (.scan xs []) = (.reverse [(1, 2), (3, 4), (1, 2)] [], 31) ∧
    runFuel 7 (.scan xs []) = (.reverse [] [(1, 2), (3, 4), (1, 2)], 49) := by
  decide +kernel

/-- An overestimate of the length neither repeats output nor adds fictitious work. -/
example : runFuel 20 (.scan xs []) = (.done [(1, 2), (3, 4), (1, 2)], 53) := by
  decide +kernel

example : runFuel 2 (.scan [] [] : Configuration (ZMod 5) 2 0) = (.done [], 8) := by
  decide +kernel

end QuadraticAlgebra.CoordinateAlphabetMachine
