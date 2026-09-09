/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.AgreementMachine
/-!
# Closed agreement-machine boundary checks

The polynomial `2X+1` agrees at two of three supplied positions. These kernel executions check
both sides of the exact threshold, count every point even on mismatch, retain the empty-polynomial
Horner overhead, and keep the final threshold/output instruction visible at insufficient fuel.
Natural scalars exercise the general semiring interface without native-code trust.
-/

namespace ReedSolomon.ListDecoding.AgreementMachine

/-- Equality at the threshold is accepted; the mismatching middle position is still charged. -/
example : runFuel [2, 1] 2 37 (.scan ([(0, 1), (1, 4), (2, 5)] : List (ℕ × ℕ)) 0) =
    (.done 2 true, ⟨⟨6, 6, 37, 27, 135, 5⟩, 3, 3, 1⟩) := by decide

/-- Raising only the supplied threshold changes acceptance, not the count or work performed. -/
example : runFuel [2, 1] 3 37 (.scan ([(0, 1), (1, 4), (2, 5)] : List (ℕ × ℕ)) 0) =
    (.done 2 false, ⟨⟨6, 6, 37, 27, 135, 5⟩, 3, 3, 1⟩) := by decide

/-- Zero requested agreements accepts an empty row list after the charged final instruction. -/
example : runFuel [2, 1] 0 1 (.scan ([] : List (ℕ × ℕ)) 0) =
    (.done 0 true, ⟨⟨0, 0, 1, 0, 3, 2⟩, 0, 0, 1⟩) := by decide

/-- The zero polynomial still executes a Horner call and comparison for each supplied point. -/
example : runFuel [] 2 13 (.scan ([(4, 0), (9, 1)] : List (ℕ × ℕ)) 0) =
    (.done 1 false, ⟨⟨0, 0, 13, 6, 43, 4⟩, 2, 2, 1⟩) := by decide

/-- The final threshold test and two result emissions are absent
one instruction before completion. -/
example : runFuel [2, 1] 2 36 (.scan ([(0, 1), (1, 4), (2, 5)] : List (ℕ × ℕ)) 0) =
    (.scan [] 2, ⟨⟨6, 6, 36, 27, 132, 3⟩, 3, 3, 0⟩) := by decide

end ReedSolomon.ListDecoding.AgreementMachine
