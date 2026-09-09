/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.RewriteSpec
/-!
# Kernel canaries for actual local column rewriting

These cover the alternating sign, zero-based jet T degree, strict contact boundary, duplicate
paths, fixed coordinate width, missing coordinates, and scalar-input composition.
-/

namespace ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine

example : (execute 2 5 [0, 0] [⟨(1 : ℤ), 0, 1⟩]).1 =
    [(1, [0, 1, 0, 0]), (-1, [1, 0, 0, 1]), (1, [0, 0, 1, 0])] := by decide

example : (lookup [0, 1, 1] (execute 1 2 [0] [⟨(1 : ℤ), 0, 2⟩]).1).1 = 2 := by decide

example : (lookup [0, 2, 0] (execute 1 2 [0] [⟨(1 : ℤ), 0, 2⟩]).1).1 = 0 := by decide

example : (execute 0 1 [] [⟨(3 : ℤ), 0, 2⟩]).1 = [(3, [0, 2])] := by decide

example : (execute 2 0 [4, 5] [⟨(3 : ℤ), 0, 0⟩]).1 = [] := by decide

example : (execute 2 1 [4, 5] [⟨(0 : ℤ), 0, 0⟩]).1 = [(0, [0, 0, 4, 5])] := by decide

-- Even at order zero, repeated error-branch expansion and cell copies retain their charges.
example : execute 0 1 [] [⟨(3 : ℤ), 0, 2⟩] = ([(3, [0, 2])], 768) := by decide +kernel

-- Discarding the only term still pays expansion, strict filtering and empty-list emission.
example : execute 2 0 [4, 5] [⟨(3 : ℤ), 0, 0⟩] = ([], 256) := by decide +kernel

-- All coordinates and the matching length boundary are traversed before accumulation.
example : lookup [0, 2] [((3 : ℤ), [0, 2])] = (3, 160) := by decide +kernel

example : (lookup [0, 0] [((7 : ℤ), [0, 0, 0])]).1 = 0 := by decide

example : (lookup [0, 0, 0, 0] [((7 : ℤ), [0, 0, 0])]).1 = 0 := by decide

example : (column 1 2 [0] (2 : ℤ) 3 1 1).1 =
    some [(6, [0, 0, 0]), (2, [1, 0, 1]), (3, [1, 0, 0])] := by decide

example : (column 2 3 [0, 0] (2 : ℤ) 3 0 1).1 =
    some [(3, [0, 0, 0, 0]), (-1, [2, 0, 0, 1]), (1, [1, 0, 1, 0]),
      (0, [2, 0, 2, 0]), (0, [1, 0, 0, 0]), (0, [2, 0, 1, 0]), (0, [2, 0, 0, 0])] := by decide

end ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine
