/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.BaseEmbeddingMachine

/-!
# Base-alphabet allocation boundary checks

The output preserves a deliberately nonmonotone order and a zero entry. Exact ledgers include
all coordinate constants, list cells, reversal work and final emission. One missing instruction
does not yet emit the completed list.
-/

@[expose] public section

namespace QuadraticAlgebra.BaseEmbeddingMachine

example : runFuel 8 (.scan [2, 0, 1] [] : Configuration ℕ 3) =
    (.done [⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ⟨0, 0, 0, 0, 0, 8, 44, 3, 1⟩) := by decide +kernel

example : runFuel 7 (.scan [2, 0, 1] [] : Configuration ℕ 3) =
    (.reverse [] [⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ⟨0, 0, 0, 0, 0, 7, 42, 3, 0⟩) := by decide +kernel

example : runFuel 2 (.scan [] [] : Configuration ℕ 3) =
    (.done [], ⟨0, 0, 0, 0, 0, 2, 5, 0, 1⟩) := by decide +kernel

end QuadraticAlgebra.BaseEmbeddingMachine
