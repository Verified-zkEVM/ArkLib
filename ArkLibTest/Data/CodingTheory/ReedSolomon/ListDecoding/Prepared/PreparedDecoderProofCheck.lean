/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderProof
/-!
# Exact prepared-driver execution checks

Concrete runs execute coefficient conversion, ordered roots, canonical acceptance and output
collection. The singleton alphabet is a small runtime fixture, not the full-alphabet premise
of the general completeness theorem. Every observed output and charge is kernel checked.
-/

namespace ReedSolomon.ListDecoding.PreparedDecoderProofCheck

open PreparedDecoderMachine

private theorem nonsquare : ¬IsSquare (-1 : ℚ) := by
  rintro ⟨r, hr⟩
  nlinarith [sq_nonneg r]

private def input (A : ℕ) : Input ℚ (-1) := ⟨[0], [0], [(0, 0)], 0, 0, 1, 1, A⟩

private def observe (r : Configuration ℚ (-1) × ℕ) : Option (Option (List (List ℚ)) × ℕ) :=
  match r.1 with
  | .done out => some (out, r.2)
  | _ => none

-- Y₀ produces the constant-zero base message at its exact one-coordinate agreement threshold.
example : observe (runFuel (input 1) nonsquare 2000
    (.start [(1, [(0, 0), (1, 1)])])) = some (some [[0]], 4705) := by decide +kernel

-- The same root fails threshold two, and its output-allocation charge disappears.
example : observe (runFuel (input 2) nonsquare 2000
    (.start [(1, [(0, 0), (1, 1)])])) = some (some [], 4689) := by decide +kernel

-- The terminal nonzero constant equation has no root records to collect.
example : observe (runFuel (input 1) nonsquare 2000
    (.start [(1, [(0, 0), (1, 0)])])) = some (some [], 352) := by decide +kernel

end ReedSolomon.ListDecoding.PreparedDecoderProofCheck
