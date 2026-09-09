/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateCandidateRefinement
/-! # Kernel checks of raw-coordinate descent and candidate rejection -/

namespace ReedSolomon.ListDecoding.CoordinateCandidateMachine

/-- Imaginary rejection happens before the base filter; a zero imaginary cell is projected. -/
example :
    Descent.step (F := ZMod 3) (.scan [(1, 0), (2, 1)] []) =
      some (.scan [(2, 1)] [1], Descent.charge 6 1 0 0) ∧
    Descent.step (F := ZMod 3) (.scan [(2, 1)] [1]) =
      some (.emit none, Descent.charge 3 1 0 0) := by decide +kernel

/-- Full-driver rejection and acceptance both execute their final output instruction. -/
example :
    (runFuel (F := ZMod 3) 1 1 0 [] 128 (.start [(1, 1)])).1 = .done none ∧
    (runFuel (F := ZMod 3) 1 1 0 [] 128 (.start [(2, 0)])).1 = .done (some [2]) := by
  decide +kernel

end ReedSolomon.ListDecoding.CoordinateCandidateMachine
