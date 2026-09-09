/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticCandidateSemantics
/-!
# Composed quadratic-candidate acceptance regressions

These computations pass through both actual callees and their driver wrappers. The three
failure modes—non-base coordinates, excess degree and insufficient agreement—remain distinct.
-/

namespace ReedSolomon.ListDecoding.QuadraticCandidateMachine

/-- Base descent, checked degree truncation and complete agreement counting compose. -/
example : runFuel 3 2 2 [(0, 2), (1, 3)] 47
    (.start [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩] : Configuration ℕ 2 0) =
    (.done (some [1, 2]), 473) := by decide +kernel

/-- Final driver emission is not free. -/
example : runFuel 3 2 2 [(0, 2), (1, 3)] 46
    (.start [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩] : Configuration ℕ 2 0) =
    (.emit (some [1, 2]), 470) := by decide +kernel

/-- A non-base interior coefficient is rejected before the degree/agreement filter runs. -/
example : runFuel 3 2 0 [] 7
    (.start [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩] : Configuration ℕ 2 0) =
    (.done none, 44) := by decide +kernel

/-- Successful descent does not license dropping a nonzero high coefficient. -/
example : runFuel 3 2 0 [] 20
    (.start [⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩] : Configuration ℕ 2 0) =
    (.done none, 155) := by decide +kernel

/-- A valid low-degree base polynomial may still fail the agreement threshold. -/
example : runFuel 3 2 2 [(0, 2), (1, 4)] 47
    (.start [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩] : Configuration ℕ 2 0) =
    (.done none, 473) := by decide +kernel

/-- Zero width and zero threshold still execute both callees and all handoffs. -/
example : runFuel 0 0 0 [] 16 (.start [] : Configuration ℕ 2 0) =
    (.done (some []), 111) := by decide +kernel

end ReedSolomon.ListDecoding.QuadraticCandidateMachine
