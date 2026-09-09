/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalAcceptanceSemantics
/-!
# Canonical acceptance execution boundaries

These literal runs distinguish guard rejection, checked coordinate descent, agreement failure,
and final emission. The positive run traverses every composed child program. No root validity
is inferred from this acceptance component: the stage enumerator supplies that certificate.
-/

namespace ReedSolomon.ListDecoding.CanonicalAcceptanceMachine

private abbrev E := QuadraticAlgebra ℕ 2 0

private def input : Guard.Input E :=
  ⟨[⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], [⟨0, 0⟩], 0, ⟨0, 0⟩, [(1, [])]⟩

-- Canonical guard, descent, degree truncation and agreement all succeed.
example : runFuel input 3 2 2 [(0, 2), (1, 3)] 96 (.start []) =
    (.done (some [1, 2]), 1378) := by decide +kernel

-- Final emission consumes its own instruction and charge.
example : runFuel input 3 2 2 [(0, 2), (1, 3)] 95 (.start []) =
    (.emit (some [1, 2]), 1375) := by decide +kernel

-- A noncanonical center stops before attempting base-field acceptance.
example : runFuel { input with center := ⟨1, 0⟩ } 3 2 2 [(0, 2), (1, 3)] 48 (.start []) =
    (.done none, 760) := by decide +kernel

-- Failure of an earlier equation stops before witness search or coordinate descent.
example : runFuel input 3 2 2 [(0, 2), (1, 3)] 48 (.start [[(1, [])]]) =
    (.done none, 754) := by decide +kernel

-- Guard success does not license projection of a non-base interior coefficient.
example : runFuel { input with coefficients := [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩] }
    3 2 2 [(0, 2), (1, 3)] 56 (.start []) = (.done none, 829) := by decide +kernel

-- The integer agreement threshold is still enforced after every previous acceptance.
example : runFuel input 3 2 2 [(0, 2), (1, 4)] 96 (.start []) =
    (.done none, 1378) := by decide +kernel

end ReedSolomon.ListDecoding.CanonicalAcceptanceMachine
