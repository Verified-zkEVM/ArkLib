/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleDecoder
/-!
# Independent recovery and guard-grid execution checks

These runs recover the zero polynomial using the sample at one, but enumerate its center at
zero. The guard grid at zero accepts; the grid at one and the empty grid reject. Thus the driver
does not silently reuse its recovery grid for canonical-center selection. The singleton alphabet
is a small operational fixture, not a full-field completeness premise.
-/

namespace ReedSolomon.ListDecoding.SeparateSampleDecoder

private theorem nonsquare : ¬IsSquare (-1 : ℚ) := by
  rintro ⟨r, hr⟩
  nlinarith [sq_nonneg r]

private def input : PreparedDecoderMachine.Input ℚ (-1) :=
  ⟨[0], [1], [(0, 0)], 0, 0, 1, 1, 1⟩

private def observe (r : PreparedDecoderMachine.Configuration ℚ (-1) × ℕ) :
    Option (Option (List (List ℚ))) :=
  match r.1 with
  | .done out => some out
  | _ => none

example : observe (runFuel input [0] nonsquare 2000
    (.start [(1, [(0, 0), (1, 1)])])) = some (some [[0]]) := by decide +kernel

example : observe (runFuel input [1] nonsquare 2000
    (.start [(1, [(0, 0), (1, 1)])])) = some (some []) := by decide +kernel

example : observe (runFuel input [] nonsquare 2000
    (.start [(1, [(0, 0), (1, 1)])])) = some (some []) := by decide +kernel

end ReedSolomon.ListDecoding.SeparateSampleDecoder
