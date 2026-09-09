/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Counting
/-!
# Executable boundary canaries for exact hidden-derivative counts

These small computations reject strict-versus-nonstrict, ceiling, and truncated-subtraction
mutations in the exact finite certificate.  They use kernel reduction via `decide`.
-/

namespace ReedSolomon
namespace HiddenDerivative

/-! The two-dimensional weighted simplex has weights `1` and `2`. -/

example : weightedHigherJetCount 3 0 = 1 := by decide

example : weightedHigherJetCount 3 1 = 2 := by decide

example : weightedHigherJetCount 3 2 = 4 := by decide

example : weightedHigherJetShellCount 3 0 = 1 := by decide

example : weightedHigherJetShellCount 3 1 = 1 := by decide

example : weightedHigherJetShellCount 3 2 = 2 := by decide

/-! Strict inequality in `x + 3b₀ < 8` gives fibers of sizes `8`, `5`, and `2`. -/

example : staircaseCount 3 0 = 0 := by decide

example : staircaseCount 3 1 = 1 := by decide

example : staircaseCount 3 8 = 15 := by decide

/-! Ceiling contact thresholds change exactly after a multiple of `d`. -/

example : contactThreshold 3 5 1 = 2 := by decide

example : contactThreshold 3 5 2 = 1 := by decide

example : contactThreshold 3 5 4 = 1 := by decide

example : contactThreshold 3 5 5 = 0 := by decide

/-! Positive parts must be written as `r + 1 - h`, not `r - h + 1`. -/

example : exhibitedKernelContactCount 1 0 2 = 0 := by decide

example : exhibitedKernelContactCount 2 3 1 = 6 := by decide

example : certifiedEnlargedRankBound 2 3 2 1 = 38 := by decide

/-! At the invalid boundary `D = d`, the last derivative has zero specialization cost. -/

example : higherJetTupleSpecializationCost (d := 2) 2 (fun _ : Fin 1 ↦ 3) = 0 := by decide

example : higherJetTupleSpecializationCost (d := 2) 3 (fun _ : Fin 1 ↦ 3) = 3 := by decide

/-! A complete small exact-dimension instance, sensitive to every residual subtraction. -/

example : exactInterpolationDimensionCount 2 6 1 1 2 0 = 27 := by decide

example : exactInterpolationDimensionCount 3 1 2 4 1 2 = 13 := by decide

/-! The certificate is strict: equality of the two integer sides does not pass. -/

example : ExactFiniteCertificate 8 2 6 1 1 2 0 := by
  change 8 * certifiedEnlargedRankBound 1 1 2 0 <
    exactInterpolationDimensionCount 2 6 1 1 2 0
  rw [show certifiedEnlargedRankBound 1 1 2 0 = 3 by decide,
    show exactInterpolationDimensionCount 2 6 1 1 2 0 = 27 by decide]
  decide

example : ¬ExactFiniteCertificate 9 2 6 1 1 2 0 := by
  change ¬9 * certifiedEnlargedRankBound 1 1 2 0 <
    exactInterpolationDimensionCount 2 6 1 1 2 0
  rw [show certifiedEnlargedRankBound 1 1 2 0 = 3 by decide,
    show exactInterpolationDimensionCount 2 6 1 1 2 0 = 27 by decide]
  decide

end HiddenDerivative
end ReedSolomon
