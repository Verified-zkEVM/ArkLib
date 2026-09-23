/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.BlockLength

/-!
# Rate-partition parameter acceptance tests

The margin height controls the natural polynomial-kernel degree bound under a strict rank margin.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- A rank margin with `N = 4`, `r = 1` and `γ = 5/2` gives kernel height `1`, below margin
height `3` for `ν = 4`. -/
example : 1 * (1 * 4) / (4 - 1) ≤ 1 * marginHeight 4 (5 / 2 : ℝ) := by
  exact kernel_height_le_marginHeight (by norm_num) (by norm_num)

end ReedSolomon.HiddenDerivative.RatePartition
