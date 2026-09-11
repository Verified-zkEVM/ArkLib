/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Probability.FiniteFieldBudget
import ArkLib.Data.Probability.DistinctQueries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# CPU proof data after two early evaluations

Each query carries paired main, auxiliary, and composition values, followed by
initial-tree and FRI authentication data. The early vectors contain 38 cubic-field
values each. Counting these added values is necessary before asserting a net saving.
The identities concern field elements and authentication hashes, with any enclosing
proof data left arbitrary; they do not assert a serialization benchmark.
-/
set_option maxRecDepth 4096

namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU

/-- Paired field values, three initial authentication paths, and the binary FRI paths. -/
def responseBytes : ℕ :=
  2 * 38 * 8 + 2 * (10 + 2) * 24 + 3 * 15 * 32 +
    32 * (8 + 9 + 10 + 11 + 12 + 13 + 14) + 24 * 7

/-- Two evaluations of each of the 38 main columns, at 24 bytes per extension-field value. -/
def anchorBytes : ℕ := 2 * 38 * 24

/-- Ten roots, 51 OOD values, 128 terminal coefficients, and one bus contribution.
The unchanged nonce and surrounding encoding are outside this field-and-hash count. -/
def fixedBytes : ℕ := (3 + 7) * 32 + 51 * 24 + 128 * 24 + 24

/-- Removing eleven query responses pays for the early evaluations and saves 55992 bytes. -/
theorem payload_reduction (unchanged : ℕ) :
    responseBytes = 5256 ∧ anchorBytes = 1824 ∧
    unchanged + 219 * responseBytes =
      unchanged + 208 * responseBytes + anchorBytes + 55992 := by
  norm_num [responseBytes, anchorBytes]

/-- Total CPU field-and-hash data before and after the replacement. -/
theorem proof_size :
    fixedBytes + 219 * responseBytes = 1155704 ∧
    fixedBytes + 208 * responseBytes + anchorBytes = 1099712 := by
  decide

/-- Expected net saving when each distinct paired query position is transmitted once.
The original independent query draws are retained. -/
noncomputable def expectedNetSaving : ℚ :=
  responseBytes *
    (ArkLib.UniformQueryBoundary.uniformQueryExpectation 219
        (ArkLib.UniformQueryBoundary.distinctQueryCount (α := Fin 32768)) -
      ArkLib.UniformQueryBoundary.uniformQueryExpectation 208
        (ArkLib.UniformQueryBoundary.distinctQueryCount (α := Fin 32768))) - anchorBytes

/-- The finite uniform-sampling theorem gives the exact deduplicated saving formula. -/
theorem expectedNetSaving_eq :
    expectedNetSaving = (5256 * 32768 : ℚ) *
      ((32767 / 32768 : ℚ) ^ 208 - (32767 / 32768 : ℚ) ^ 219) - 1824 := by
  unfold expectedNetSaving
  rw [ArkLib.UniformQueryBoundary.uniformQueryExpectation_distinctQueryCount 219
    (by simp : 0 < Fintype.card (Fin 32768)),
    ArkLib.UniformQueryBoundary.uniformQueryExpectation_distinctQueryCount 208
    (by simp : 0 < Fintype.card (Fin 32768))]
  norm_num [responseBytes, anchorBytes]

/-- Deduplication retains an expected net reduction of approximately 55617 bytes. -/
theorem expectedNetSaving_bounds :
    (55617 : ℚ) < expectedNetSaving ∧ expectedNetSaving < 55618 := by
  rw [expectedNetSaving_eq]
  decide +kernel

/-- The selected agreement lies strictly below the finite Johnson threshold. -/
theorem agreement_beyond_johnson :
    (45690 : ℕ) ^ 2 < 65536 * (32768 - 1) := by decide

/-- Even discarding every algebraic error, 215 queries cannot meet the target at or
above finite Johnson. The grinding parameter is the same 20 bits as for CPU. -/
theorem johnson_215_queries_fail (a : ℚ) (ha : 0 ≤ a)
    (hj : (32767 / 65536 : ℚ) ≤ a ^ 2) :
    1 / 2 ^ 128 < a ^ 215 / 2 ^ 20 := by
  have hlo : (707 / 1000 : ℚ) < a := by nlinarith
  have hp : (707 / 1000 : ℚ) ^ 215 < a ^ 215 :=
    pow_lt_pow_left₀ hlo (by norm_num) (by decide)
  exact lt_trans (by decide +kernel :
    (1 / 2 ^ 128 : ℚ) < (707 / 1000 : ℚ) ^ 215 / 2 ^ 20)
    (div_lt_div_of_pos_right hp (by norm_num))

end ArkLibExamples.ReedSolomon.LambdaVM.CPU
