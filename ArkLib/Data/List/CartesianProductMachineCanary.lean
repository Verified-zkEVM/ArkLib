/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.List.CartesianProductMachine

/-!
# Cartesian-product machine boundary checks

Distinct axis values expose reversed coordinate order. Duplicates, empty axes, no axes and
partial execution distinguish the essential branches without raising kernel limits.
-/

@[expose] public section

namespace List.CartesianProductMachine

/-- The first coordinate varies more slowly than the second. -/
example : runFuel 38 (.start [[1, 2], [3, 4]] : Configuration ℕ) =
    (.done [[1, 3], [1, 4], [2, 3], [2, 4]], ⟨38, 144, 0, 1⟩) := by decide

/-- Complete materialization still awaits the separately charged output transition. -/
example : runFuel 37 (.start [[1, 2], [3, 4]] : Configuration ℕ) =
    (.emit [[1, 3], [1, 4], [2, 3], [2, 4]], ⟨37, 143, 0, 0⟩) := by decide

/-- Repeated axis entries remain repeated output occurrences. -/
example : runFuel 27 (.start [[1, 1], [3]] : Configuration ℕ) =
    (.done [[1, 3], [1, 3]], ⟨27, 96, 0, 1⟩) := by decide

/-- No axes produce the singleton empty tuple, rather than an empty product. -/
example : runFuel 4 (.start [] : Configuration ℕ) =
    (.done [[]], ⟨4, 8, 0, 1⟩) := by decide

/-- An empty middle axis empties the product, including subsequent nonempty-axis processing. -/
example : runFuel 25 (.start [[1, 2], [], [3]] : Configuration ℕ) =
    (.done [], ⟨25, 82, 0, 1⟩) := by decide

end List.CartesianProductMachine
