/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Proofs
/-!
# Kernel canaries for actual nonzero sparse interpolation

Literal results check factor allocation, scalar-zero filtering, width rejection, the actual
nonzero solver, redundant-row success, genuine full-rank failure, and end-to-end charges.
-/

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

example : factors 3 [0, 2, 1] = ([(3, 0), (4, 2), (5, 1)], 128) := by decide +kernel

example : emit [[0, 0], [0, 1]] ([0, 1] : List ℚ) =
    (some [(1, [(0, 0), (1, 1)])], 192) := by decide +kernel

example : emit [[0, 0], [0, 1]] ([0, 0] : List ℚ) = (some [], 96) := by decide +kernel

example : emit [[0, 0]] ([] : List ℚ) = (none, 32) := by decide +kernel

example : emit [] ([1] : List ℚ) = (none, 32) := by decide +kernel

example : run 0 0 1 1 [((2 : ℚ), 3)] =
    (some ⟨1, [-3, 1], [(-3, [(0, 0), (1, 0)]), (1, [(0, 0), (1, 1)])]⟩, 8280) := by decide +kernel

example : run 0 0 1 1 ([] : List (ℚ × ℚ)) =
    (some ⟨0, [1, 0], [(1, [(0, 0), (1, 0)])]⟩, 2306) := by decide +kernel

example : run 0 0 1 1 [((2 : ℚ), 3), (4, 5)] = (none, 14717) := by decide +kernel

example : run 0 0 0 1 [((2 : ℚ), 3)] = (none, 1483) := by decide +kernel

example : run 2 0 2 2 [((2 : ℚ), 3)] =
    (some ⟨3, [6, -2, -3, 1, 0, 0], [(6, [(0, 0), (1, 0)]), (-2, [(0, 0), (1, 1)]),
      (-3, [(0, 1), (1, 0)]), (1, [(0, 1), (1, 1)])]⟩, 106466) := by decide +kernel

end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
