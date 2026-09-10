/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.List.PrefixAxesMachine

/-!
# Prefix-axis materialization boundary checks

Different prefix lengths expose both reversal orders. Zero lengths, an empty request list and
oversized requests distinguish success from rejection without returning partial axes.
-/

@[expose] public section

namespace List.PrefixAxesMachine

/-- Prefixes preserve both source order and the requested axis order, including zero length. -/
example : runFuel [4, 7, 9] 29 (.start [2, 0, 3] : Configuration ℕ) =
    (.done (some [[4, 7], [], [4, 7, 9]]), ⟨29, 122, 13, 1⟩) := by decide

/-- Materialized axes await their separately charged emission. -/
example : runFuel [4, 7, 9] 28 (.start [2, 0, 3] : Configuration ℕ) =
    (.emit (some [[4, 7], [], [4, 7, 9]]), ⟨28, 121, 13, 0⟩) := by decide

/-- Oversized requests reject the entire result even after an earlier successful prefix. -/
example : runFuel [4, 7] 22 (.start [1, 3] : Configuration ℕ) =
    (.done none, ⟨12, 50, 8, 1⟩) := by decide

/-- Empty universes accept zero-length axes. -/
example : runFuel [] 14 (.start [0, 0] : Configuration ℕ) =
    (.done (some [[], []]), ⟨14, 44, 2, 1⟩) := by decide

/-- An empty request list succeeds and still pays initialization and output. -/
example : runFuel [4, 7] 4 (.start [] : Configuration ℕ) =
    (.done (some []), ⟨4, 8, 0, 1⟩) := by decide

/-- Exhausted universes reject huge lengths without decrementing the whole requested length. -/
example : runFuel [] 4 (.start [100] : Configuration ℕ) =
    (.done none, ⟨4, 11, 1, 1⟩) := by decide

end List.PrefixAxesMachine
