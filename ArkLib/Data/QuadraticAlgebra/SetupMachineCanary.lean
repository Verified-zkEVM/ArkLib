/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.SetupRefinement

/-!
# Quadratic preparation kernel canaries

Literal outputs exercise zero samples, a row-crossing prefix, exhausted input and characteristic
two. Complete ledger literals include child dispatch wrappers and quadratic allocations.
-/

@[expose] public section

namespace QuadraticAlgebra.SetupMachine

/-- Coordinate order is fixed by the actual nested enumeration. -/
private def alphabetThree : List (Element 3 2) :=
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 2⟩]

example : runFuel 0 155 (.base (.start : ZMod.EnumerationMachine.Configuration 3)) =
    (.done (some ⟨2, ⟨[0, 1, 2], alphabetThree, [], 3, 9, 0⟩⟩),
      ⟨26, 9, 21, 72, 46, 277, 786, 5⟩) := by decide +kernel

example : runFuel 4 163 (.base (.start : ZMod.EnumerationMachine.Configuration 3)) =
    (.done (some ⟨2, ⟨[0, 1, 2], alphabetThree, [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩],
      3, 9, 4⟩⟩), ⟨26, 9, 21, 84, 46, 293, 846, 5⟩) := by decide +kernel

theorem exhausted_setup_input_returns_none :
    runFuel 10 163 (.base (.start : ZMod.EnumerationMachine.Configuration 3)) =
    (.done none, ⟨26, 9, 21, 99, 46, 293, 844, 5⟩) := by decide +kernel

example : runFuel 0 39 (.base (.start : ZMod.EnumerationMachine.Configuration 2)) =
    (.done none, ⟨8, 4, 10, 20, 16, 76, 181, 3⟩) := by decide +kernel

example : List.PrefixMachine.runFuel 10 (.scan 3 ([7, 8] : List ℕ) [] 0) =
    (.done none, ⟨0, 0, 0, 7, 0, 3, 14, 1⟩) := by decide +kernel

end QuadraticAlgebra.SetupMachine
