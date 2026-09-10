/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.AugmentedColumnMachine

/-!
# Augmented column regression checks

Nonzero RHS values distinguish physical column `j+1` from the prepended RHS and exercise its
arithmetic update. Exact costs include both serialization passes and inner/outer dispatches.
-/

@[expose] public section

namespace Matrix.AugmentedColumnMachine

/-- A nontrivial inverse changes the first RHS; an already-zero second target remains unchanged. -/
example : runFuel 1 83 (.pack
    ([([2, 2, 4], 6), ([3, 5, 2], 10), ([6, 0, 1], 7)] : List (Row ℚ)) []) =
    (.done [([2, 2, 4], 6), ([-2, 0, -8], -5), ([6, 0, 1], 7)],
      ⟨⟨8, 10, 149, 505, 6⟩, 2, 2, 3, 16⟩) := by decide +kernel

/-- One short of exact fuel leaves the final decoded-matrix emission pending. -/
example : runFuel 1 82 (.pack
    ([([2, 2, 4], 6), ([3, 5, 2], 10), ([6, 0, 1], 7)] : List (Row ℚ)) []) =
    (.reverseRows [] [([2, 2, 4], 6), ([-2, 0, -8], -5), ([6, 0, 1], 7)],
      ⟨⟨8, 10, 148, 503, 5⟩, 2, 2, 3, 16⟩) := by decide +kernel

/-- A supplied head-only pivot still passes through full packing, validation and unpacking. -/
example : runFuel 1 17 (.pack ([([2, 2], 6)] : List (Row ℚ)) []) =
    (.done [([2, 2], 6)], ⟨⟨0, 0, 25, 83, 2⟩, 0, 0, 1, 6⟩) := by decide +kernel

/-- An empty matrix is rejected by the actual delegated column machine. -/
example : runFuel 0 4 (.pack ([] : List (Row ℚ)) []) =
    (.rejected, ⟨⟨0, 0, 5, 10, 2⟩, 0, 0, 0, 1⟩) := by decide +kernel

/-- Decoding a malformed packed row rejects instead of inventing a right-hand side. -/
example : runFuel 0 1 (.unpack ([[]] : List (List ℚ)) []) =
    (.rejected, ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩) := by decide +kernel

/-- A nonzero RHS cannot disguise a zero selected coefficient pivot. -/
example : (runFuel 0 100 (.pack ([([0, 2], 9), ([3, 4], 7)] : List (Row ℚ)) [])).1 =
    .rejected := by decide +kernel

end Matrix.AugmentedColumnMachine
