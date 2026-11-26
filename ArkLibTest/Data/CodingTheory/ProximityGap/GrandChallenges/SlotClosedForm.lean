/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.SlotClosedForm

/-!
# Regression cases for the closed slot counts

* Row: at `(D, A, m, M) = (2, 2, 2, 2)` and `t ≤ 3`, each of the six intervals of
  `gradedRankBound_eq_pieces` is nonempty for some `t`, the branch condition of
  `gradedSourceCount` fails for some `s < m` (at `t = 3`), and `t > M` (at `t = 3`). The closed
  form agrees with `gradedRankBound` at every such `t`.
* Height: at `(D, A, m, M, μ, ℓ, h) = (3, 2, 2, 2, 5, 1, 3)`, the subtraction `m * A + b - D * t`
  is truncated for `t ≥ 2` (partly at `t = 2`) and `h + 1 - ℓ * t` is truncated at `t = 5`.
* Slot inequality: the certificate parameters of the `CertificateWitnesses` acceptance case
  (`D = 1`, `A = 2`, `(m, M, μ, h) = (1, 1, 1, 1)`, `n = 2`) checked through the closed forms.
  The MCA instance at `D = 127`, `A = 239`, `n = 512` checks the same route at a larger scale.
* Execution: `#eval` under `#guard_msgs` runs the closed forms from this caller, outside any
  `noncomputable section`, on the cases above with independently computed values, and at `n = 3`,
  where the slot inequality of the certificate case fails (`9 < 7` is false).
-/

open ReedSolomon.HiddenDerivative ProximityGap.GrandChallenges.SlotArithmetic

namespace SlotClosedFormTest

example : heightSlotCountClosed 3 2 2 2 5 1 3 = 25 := by decide

example :
    firstOrderCurveShiftedRowSlotBound 1 2 1 1 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 1 1 1 1 1 := by
  rw [firstOrderCurveShiftedRowSlotBound_eq_closed, firstOrderCurveShiftedHeightSlotCount_eq_closed]
  decide +kernel

example :
    firstOrderCurveShiftedRowSlotBound 127 239 609 280 1148 512 1 271081 <
      firstOrderCurveShiftedHeightSlotCount 127 239 609 280 1148 1 271081 := by
  rw [firstOrderCurveShiftedRowSlotBound_eq_closed, firstOrderCurveShiftedHeightSlotCount_eq_closed]
  decide +kernel

-- Evaluation from this caller: `gradedRankBoundClosed 2 2 2 2 t` for `t < 4`, then the
-- row and height cases above. The values were computed independently of Lean.
/-- info: ([2, 2, 2, 0], 72, 25) -/
#guard_msgs in
#eval ((List.range 4).map (gradedRankBoundClosed 2 2 2 2), rowSlotBoundClosed 2 2 2 2 3 3 1 4,
  heightSlotCountClosed 3 2 2 2 5 1 3)

-- Certificate case: row and height counts and the slot inequality at `n = 2` (accepted, `6 < 7`)
-- and at `n = 3` (rejected, `9 < 7` is false).
/-- info: [(6, 7, true), (9, 7, false)] -/
#guard_msgs in
#eval [2, 3].map fun n =>
  (rowSlotBoundClosed 1 2 1 1 1 n 1 1, heightSlotCountClosed 1 2 1 1 1 1 1,
    decide (rowSlotBoundClosed 1 2 1 1 1 n 1 1 < heightSlotCountClosed 1 2 1 1 1 1 1))

end SlotClosedFormTest
