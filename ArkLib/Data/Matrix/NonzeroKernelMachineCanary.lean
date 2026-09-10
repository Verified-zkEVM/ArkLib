/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.NonzeroKernelSemantics

/-!
# Nonzero kernel execution regressions

Literal results and charges exercise redundant rows, free-column positions, exact emission,
full rank, empty input, and both malformed-width directions. All computations use the kernel.
-/

@[expose] public section

namespace Matrix.NonzeroKernelMachine

/-- Two dependent rows and two columns still yield a nonzero kernel: raw row count is irrelevant.
The 99 steps split as 9 preflight, 65 forward, 1 return, 2 free probes, 3 seed, 18 back, 1 emit. -/
example : runFuel 2 99 (.check [([1, 1], 0), ([2, 2], 0)]
    [([1, 1], 0), ([2, 2], 0)] : Configuration ℚ) =
    (.done 1 [-1, 1], ⟨⟨7, 7, 281, 782, 10⟩, 2, 2, 8, 42⟩) := by decide +kernel

/-- One step before final emission retains the successful callee result. -/
example : runFuel 2 98 (.check [([1, 1], 0), ([2, 2], 0)]
    [([1, 1], 0), ([2, 2], 0)] : Configuration ℚ) =
    (.back 1 (.done [-1, 1]), ⟨⟨7, 7, 280, 779, 9⟩, 2, 2, 8, 42⟩) := by decide +kernel

/-- A gap before the first pivot selects coordinate zero, without shifting pivot metadata. -/
example : runFuel 3 77 (.check [([0, 1, 2], 0)] [([0, 1, 2], 0)] : Configuration ℚ) =
    (.done 0 [1, 0, 0], ⟨⟨5, 4, 197, 552, 9⟩, 1, 1, 5, 45⟩) := by decide +kernel

/-- Full pivot coverage returns no free column instead of claiming a nonzero kernel. -/
example : runFuel 2 95 (.check [([1, 0], 0), ([0, 1], 0)]
    [([1, 0], 0), ([0, 1], 0)] : Configuration ℚ) =
    (.noFree, ⟨⟨3, 4, 288, 796, 10⟩, 1, 1, 7, 42⟩) := by decide +kernel

/-- An empty system still constructs and returns its unit seed through both callees. -/
example : runFuel 1 16 (.check [] [] : Configuration ℚ) =
    (.done 0 [1], ⟨⟨0, 0, 29, 85, 4⟩, 0, 0, 0, 10⟩) := by decide +kernel

/-- A short row fails during the width scan. -/
example : runFuel 2 3 (.check [([1], 0)] [([1], 0)] : Configuration ℚ) =
    (.rejected, ⟨⟨0, 0, 3, 10, 1⟩, 0, 0, 1, 3⟩) := by decide +kernel

/-- A long row also fails during the width scan. -/
example : runFuel 1 3 (.check [([1, 0], 0)] [([1, 0], 0)] : Configuration ℚ) =
    (.rejected, ⟨⟨0, 0, 3, 10, 1⟩, 0, 0, 1, 3⟩) := by decide +kernel

/-- Nonhomogeneous input is rejected before coefficient scans or elimination. -/
example : runFuel 2 1 (.check [([1, 0], 1)] [([1, 0], 1)] : Configuration ℚ) =
    (.rejected, ⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 1, 0⟩) := by decide +kernel

end Matrix.NonzeroKernelMachine
