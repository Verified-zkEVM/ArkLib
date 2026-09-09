/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputProofRoots
/-!
# Kernel checks for canonical base output collection

These concrete collector cases distinguish physical descent, canonical centers, target degree,
and the exact agreement threshold. Padding is retained in root records and removed at output.
-/

namespace ReedSolomon.ListDecoding.CanonicalOutputProofCheck

open CanonicalOutputMachine

private abbrev E := QuadraticAlgebra ℚ (-1) 0

private def record (center : E) (cs : List E) : Record E :=
  ⟨⟨⟨[], some (1, 1)⟩, [], [(1, [])]⟩, center, cs⟩

-- Two physical leading zeros descend and truncate to the unique width-one constant output.
example : result 0 [0, 1] 3 1 2 [(0, 1), (1, 1)] [record 0 [0, 0, 1]] = [[1]] := by
  decide +kernel

-- Exactly one agreeing coordinate meets threshold one.
example : result 0 [0, 1] 3 1 1 [(0, 1), (1, 0)] [record 0 [0, 0, 1]] = [[1]] := by
  decide +kernel

-- The same candidate fails threshold two.
example : result 0 [0, 1] 3 1 2 [(0, 1), (1, 0)] [record 0 [0, 0, 1]] = [] := by
  decide +kernel

-- A genuine extension coefficient cannot descend to a base output.
example : result 0 [0, 1] 2 1 0 ([] : List (ℚ × ℚ))
    [record 0 [0, ⟨0, 1⟩]] = [] := by decide +kernel

-- A nonzero discarded coefficient violates the strict target-degree bound.
example : result 0 [0, 1] 2 1 0 ([] : List (ℚ × ℚ))
    [record 0 [1, 0]] = [] := by decide +kernel

-- Both centers are regular for separant one, but only the first supplied sample is canonical.
example : result 0 [0, 1] 2 1 0 ([] : List (ℚ × ℚ))
    [record 1 [0, 1], record 0 [0, 1]] = [[1]] := by decide +kernel

-- Width zero accepts the padded zero polynomial at the empty-domain threshold.
example : result 0 [0] 2 0 0 ([] : List (ℚ × ℚ)) [record 0 [0, 0]] = [[]] := by
  decide +kernel

-- The empty collector executes its actual four wrapper transitions with their exact charge.
example : runFuel 0 ([] : List E) 2 1 0 ([] : List (ℚ × ℚ)) 4 (.start []) =
    (.done [], 13) := by decide +kernel

end ReedSolomon.ListDecoding.CanonicalOutputProofCheck
