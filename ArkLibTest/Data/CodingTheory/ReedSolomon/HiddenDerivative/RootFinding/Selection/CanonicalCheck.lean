/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.CanonicalProof
/-!
# Canonical sample order and global prefix checks

The separant X is zero at the first sample and nonzero at the next two. Only the first nonzero
sample is accepted. An unsolved earlier equation rejects even that canonical center.
-/

open ReedSolomon.HiddenDerivative.CanonicalRootSelection
open ReedSolomon.HiddenDerivative.StageRootsMachine (Record)

-- Sample order, rather than alphabet order or an arbitrary regular center, selects center two.
example : accepted 0 [0, 2, 1]
    (⟨⟨⟨[(1, [(0, 1), (1, 1)])], some (1, 1)⟩, [], [(1, [(0, 1)])]⟩, 2, [0]⟩ : Record ℚ) =
      true := by decide +kernel

-- Center one is also regular but follows the first nonzero sample and is rejected.
example : accepted 0 [0, 2, 1]
    (⟨⟨⟨[(1, [(0, 1), (1, 1)])], some (1, 1)⟩, [], [(1, [(0, 1)])]⟩, 1, [0]⟩ : Record ℚ) =
      false := by decide +kernel

-- The zero sample is not a regular center for the supplied separant.
example : accepted 0 [0, 2, 1]
    (⟨⟨⟨[(1, [(0, 1), (1, 1)])], some (1, 1)⟩, [], [(1, [(0, 1)])]⟩, 0, [0]⟩ : Record ℚ) =
      false := by decide +kernel

-- The candidate zero fails an earlier constant-one identity, even at the canonical center.
example : accepted 0 [0, 2, 1]
    (⟨⟨⟨[(1, [(0, 1), (1, 1)])], some (1, 1)⟩, [[(1, [])]], [(1, [(0, 1)])]⟩,
      2, [0]⟩ : Record ℚ) = false := by decide +kernel

-- Filtering preserves the record at the first nonzero sample and drops later regular centers.
example : selected 0 [0, 2, 1]
    ([⟨⟨⟨[], some (1, 1)⟩, [], [(1, [(0, 1)])]⟩, 1, [0]⟩,
      ⟨⟨⟨[], some (1, 1)⟩, [], [(1, [(0, 1)])]⟩, 2, [0]⟩,
      ⟨⟨⟨[], some (1, 1)⟩, [], [(1, [(0, 1)])]⟩, 0, [0]⟩] : List (Record ℚ)) =
    [⟨⟨⟨[], some (1, 1)⟩, [], [(1, [(0, 1)])]⟩, 2, [0]⟩] := by decide +kernel
