/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CandidateFilterSemantics
/-!
# Executable candidate acceptance boundaries

These kernel computations check the actual dispatcher and aggregate primitive work, not only
the proof-level predicate. Leading nonzero rejection must precede agreement evaluation.
-/

namespace ReedSolomon.ListDecoding.CandidateFilterMachine

/-- A padded linear polynomial is accepted and returned without its checked zero prefix. -/
example : runFuel 3 2 2 [(0, 2), (1, 3)] 33 (.start [0, 1, 2] : Configuration ℚ) =
    (.done (some [1, 2]), 272) := by decide +kernel

/-- The final output itself requires an instruction. -/
example : runFuel 3 2 2 [(0, 2), (1, 3)] 32 (.start [0, 1, 2] : Configuration ℚ) =
    (.emit (some [1, 2]), 269) := by decide +kernel

/-- Too few agreements reject after the complete count with the same scheduled work. -/
example : runFuel 3 2 2 [(0, 2), (1, 4)] 33 (.start [0, 1, 2] : Configuration ℚ) =
    (.done none, 272) := by decide +kernel

/-- A nonzero high coefficient cannot be silently discarded, even with threshold zero. -/
example : runFuel 3 2 0 [] 6 (.start [1, 1, 2] : Configuration ℚ) =
    (.done none, 35) := by decide +kernel

/-- Dimension zero still accepts the zero polynomial when the agreement condition holds. -/
example : runFuel 2 0 1 [(0, 0)] 16 (.start [0, 0] : Configuration ℚ) =
    (.done (some []), 117) := by decide +kernel

end ReedSolomon.ListDecoding.CandidateFilterMachine
