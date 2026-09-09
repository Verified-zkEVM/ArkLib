/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardSemantics
/-!
# Canonical-guard execution boundaries

Full runs distinguish the first regular center from a later regular center, prior-equation
failure from center rejection, empty samples and final Boolean emission. Literal work includes
all nested evaluator instructions and their wrappers.
-/

open ReedSolomon.HiddenDerivative.CanonicalGuardMachine

-- The first nonzero sample for Y₀(T)=T is two, so center two is retained.
example : runFuel (⟨[1, 0], [0, 2, 3], 0, 2, [(1, [(1, 1)])]⟩ : Input ℕ)
    114 (.start []) = (.done true, 1701) := by decide +kernel

-- Center three is also nonzero but not the first one: it must be rejected.
example : runFuel (⟨[1, 0], [0, 2, 3], 0, 3, [(1, [(1, 1)])]⟩ : Input ℕ)
    114 (.start []) = (.done false, 1701) := by decide +kernel

-- A failed previous identity prevents the witness search from running at all.
example : runFuel (⟨[1, 0], [0, 2, 3], 0, 2, [(1, [(1, 1)])]⟩ : Input ℕ)
    114 (.start [[(1, [(1, 1)])]]) = (.done false, 1695) := by decide +kernel

-- With no samples, the previous test succeeds vacuously but there is no regular witness.
example : runFuel (⟨[], [], 0, 0, []⟩ : Input ℕ)
    20 (.start [[]]) = (.done false, 135) := by decide +kernel

-- The final Boolean is not emitted for free.
example : runFuel (⟨[1, 0], [0, 2, 3], 0, 2, [(1, [(1, 1)])]⟩ : Input ℕ)
    113 (.start []) = (.emit true, 1697) := by decide +kernel
