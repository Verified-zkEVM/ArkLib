/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Search.Proofs
/-!
# Literal descending-search canaries

These check first-candidate success, failure followed by success, exhausted search, empty
intervals, zero multiplicity, and the derivative-order lower bound. Costs include failed
attempts and input counting. The returned sparse coefficients are literal expected values.
-/

namespace ReedSolomon.HiddenDerivative.AmbientSearchMachine

example : run 1 0 1 2 ([((0 : ℚ), 0), (1, 1), (2, 2)]) =
    (some ⟨1, ⟨2, [0, -1, 1],
      [(-1, [(0, 0), (1, 1)]), (1, [(0, 1), (1, 0)])]⟩⟩, 58856) := by decide +kernel

example : run 1 0 1 3 ([((0 : ℚ), 0), (1, 1), (2, 2)]) =
    (some ⟨2, ⟨2, [0, -1, 1, 0],
      [(-1, [(0, 0), (1, 1)]), (1, [(0, 1), (1, 0)])]⟩⟩, 58255) := by decide +kernel

example : run 1 0 1 1 ([((0 : ℚ), 0), (1, 1), (2, 2)]) =
    (none, 22394) := by decide +kernel

example : run 1 0 1 1 ([] : List (ℚ × ℚ)) = (none, 96) := by decide +kernel

example : run 4 0 1 2 ([((0 : ℚ), 0), (1, 1), (2, 2)]) =
    (none, 192) := by decide +kernel

example : run 1 0 0 2 ([((0 : ℚ), 0), (1, 1), (2, 2)]) =
    (none, 5658) := by decide +kernel

example : run 1 1 1 2 ([((0 : ℚ), 0), (1, 1), (2, 2)]) =
    (none, 42750) := by decide +kernel

end ReedSolomon.HiddenDerivative.AmbientSearchMachine
