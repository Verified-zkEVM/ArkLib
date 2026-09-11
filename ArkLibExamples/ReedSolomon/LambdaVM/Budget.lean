/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.LambdaVM.Parameters
import Mathlib.Tactic.GCongr

/-!
# The CPU table's summed local error

The scalar curve exceptions, query survival, constraint cancellation, OOD residual,
and early-evaluation collisions consume one common local error allocation. Only query
survival receives grinding credit. The list dimension is `T + 3`, including the increase
when the two-anchor quotient is undone. This file checks the exact rational arithmetic;
the CPU endpoint supplies actual exceptional sets and candidate families from the
interpolation and reconstruction theorems.
-/
namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU

/-- Two distinct anchors outside the length-65536 domain distinguish a finite candidate list. -/
def anchorError (list : ℕ) : ℚ :=
  (list.choose 2 : ℚ) * ((traceRows + 2 : ℕ) / (fieldSize - length - 1 : ℕ) : ℚ) ^ 2

/-- The complete local expression, using an actual anchor collision rate. -/
def localError (exceptional list queries : ℕ) (collision : ℚ) : ℚ :=
  -- Initial degree-50 powers batching and the eight binary folds.
  (exceptional : ℚ) / fieldSize +
    -- The fixed 20-bit grinding parameter applies only to queries.
    ((agreement : ℚ) / length) ^ queries / 2 ^ 20 +
    -- CPU has 49 transition constraints and one boundary constraint.
    (49 * list : ℕ) / fieldSize +
    -- Degree-3 constraints, two composition parts, and two early points.
    (((4 * traceRows + 6) * list + 2 * length + 2 : ℕ) : ℚ) /
      (fieldSize - length - traceRows : ℕ) + collision

/-- All five terms together, including early binding, fit the CPU's 128-bit local target. -/
theorem budget_at_target :
    localError totalExceptionalCount listBound 208 (anchorError listBound) <
      (1 / 2 ^ 128 : ℚ) := by
  unfold localError anchorError
  rw [Nat.choose_two_right]
  decide +kernel

/-- With these fixed finite certificates, removing one more query would exceed the target. -/
theorem budget_207_fails :
    (1 / 2 ^ 128 : ℚ) <
      localError totalExceptionalCount listBound 207 (anchorError listBound) := by
  unfold localError anchorError
  rw [Nat.choose_two_right]
  decide +kernel

/-- Smaller actual exception sets and collision rates preserve the strict local target. -/
theorem local_error_of_bounds {exceptional list : ℕ} {collision : ℚ}
    (hE : exceptional ≤ totalExceptionalCount) (hL : list ≤ listBound)
    (hcollision : collision ≤ anchorError listBound) :
    localError exceptional list 208 collision < (1 / 2 ^ 128 : ℚ) := by
  apply lt_of_le_of_lt _ budget_at_target
  unfold localError
  gcongr

end ArkLibExamples.ReedSolomon.LambdaVM.CPU
