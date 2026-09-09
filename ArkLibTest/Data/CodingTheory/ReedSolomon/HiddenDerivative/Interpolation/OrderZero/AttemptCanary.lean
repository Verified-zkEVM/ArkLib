/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.ZeroBounds
/-!
# Order-zero observed attempt canaries

Literal outputs cover D=0, increasing multiplicity, normalized nonzero interpolation, and
full-rank failure. The machine and exact primitive charges are unchanged by the new bounds.
-/

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

example : run 0 0 1 1 [((2 : ℚ), 3)] =
    (some ⟨1, [-3, 1], [(-3, [(0, 0), (1, 0)]), (1, [(0, 0), (1, 1)])]⟩, 8280) := by decide +kernel

example : run 2 0 2 2 [((2 : ℚ), 3)] =
    (some ⟨3, [6, -2, -3, 1, 0, 0], [(6, [(0, 0), (1, 0)]), (-2, [(0, 0), (1, 1)]),
      (-3, [(0, 1), (1, 0)]), (1, [(0, 1), (1, 1)])]⟩, 106466) := by decide +kernel

example : run 1 0 3 1 [((0 : ℚ), 0)] = (none, 304861) := by decide +kernel

example : run 0 0 3 1 [((0 : ℚ), 0)] =
    (some ⟨3, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [(1, [(0, 0), (1, 3)])]⟩, 2376848) := by decide +kernel

example : run 0 0 0 1 [((2 : ℚ), 3)] = (none, 1483) := by decide +kernel

end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
