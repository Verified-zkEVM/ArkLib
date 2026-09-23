/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.FiniteRateParameters

/-!
# Acceptance tests for finite first-order rate parameters

Concrete rounded counts and their rational certificate, the source-count dimension bound, and
boundary cases for its degree and agreement hypotheses.
-/

namespace ReedSolomon.HiddenDerivative

/-! ### A concrete finite certificate -/

/-- The rate ratio is `1/4` at rate `1/2` and agreement `3/4`. -/
private theorem concrete_rate_ratio : firstOrderRateBeta (1 / 2) (3 / 4) = 1 / 4 := by
  norm_num [firstOrderRateBeta]

/-- At multiplicity `4`, the derivative and total jet caps are `1` and `6`. -/
example : firstOrderRateDerivativeCap (1 / 2) (3 / 4) 4 = 1 ∧
    firstOrderRateJetDegree (1 / 2) (3 / 4) 4 = 6 := by
  constructor <;> norm_num [firstOrderRateDerivativeCap, firstOrderRateJetDegree,
    firstOrderRateBeta]

/-- At these caps, the source count is `18` and the rank count is `17`. -/
example : firstOrderSourceCount (1 / 2) (3 / 4) 4 1 6 = 18 ∧
    firstOrderRankCount 4 1 = 17 := by
  constructor
  · norm_num [firstOrderSourceCount, Finset.sum_range_succ]
  · decide

/-- The rounded finite test holds at rate `1/2`, agreement `3/4`, and multiplicity `4`. -/
private def concreteParameters : FirstOrderFiniteRateParameters (1 / 2 : ℝ) (3 / 4 : ℝ) :=
  ⟨4, by norm_num, by norm_num [FirstOrderFiniteRateTest, firstOrderRateDerivativeCap,
    firstOrderRateJetDegree, firstOrderRateBeta, firstOrderSourceCount, firstOrderRankCount,
    Finset.sum_range_succ]⟩

example : concreteParameters.derivativeCap = 1 := by
  norm_num [FirstOrderFiniteRateParameters.derivativeCap, concreteParameters,
    firstOrderRateDerivativeCap, firstOrderRateBeta]

example : concreteParameters.jetDegree = 6 := by
  norm_num [FirstOrderFiniteRateParameters.jetDegree, concreteParameters,
    firstOrderRateJetDegree]

example : concreteParameters.rankCount = 17 := by
  norm_num [FirstOrderFiniteRateParameters.rankCount, concreteParameters,
    FirstOrderFiniteRateParameters.derivativeCap, firstOrderRankCount,
    firstOrderRateDerivativeCap, firstOrderRateBeta, Finset.sum_range_succ]

example : concreteParameters.sourceCount = 18 := by
  norm_num [FirstOrderFiniteRateParameters.sourceCount, concreteParameters,
    FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree,
    firstOrderRateDerivativeCap, firstOrderRateJetDegree, firstOrderRateBeta,
    firstOrderSourceCount, Finset.sum_range_succ]

example : concreteParameters.challengeDegree = 102 := by
  norm_num [FirstOrderFiniteRateParameters.challengeDegree, concreteParameters,
    firstOrderRateChallengeDegree, FirstOrderFiniteRateParameters.rankCount,
    FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree,
    FirstOrderFiniteRateParameters.sourceCount, firstOrderRateDerivativeCap,
    firstOrderRateJetDegree, firstOrderRateBeta, firstOrderRankCount, firstOrderSourceCount,
    Finset.sum_range_succ]

example : (concreteParameters.rankCount : ℝ) < concreteParameters.sourceCount :=
  concreteParameters.sourceCount_gt_rankCount

/-! ### The rational finite test -/

/-- The rational finite test computes the same strict surplus, `17 < 18`. -/
example : FirstOrderRationalFiniteTest (1 / 2 : ℚ) (3 / 4 : ℚ) 4 := by
  norm_num [FirstOrderRationalFiniteTest, firstOrderRationalSourceCount,
    firstOrderRankCount, Finset.sum_range_succ]

/-! ### Source count and interpolation dimension -/

/-- At rate `1/2`, agreement `3/4`, block length `4`, the scaled source count is at most `91`. -/
example :
    4 * firstOrderSourceCount (1 / 2) (3 / 4) 4 1 6 ≤
      firstOrderDimensionCount 2 3 4 1 6 := by
  apply firstOrderSourceCount_mul_le_firstOrderDimensionCount <;> norm_num

/-- Without the agreement bound, the source count can exceed the dimension: `1 ≤ 0` fails. -/
example : firstOrderSourceCount 1 1 1 0 0 = 1 ∧ firstOrderDimensionCount 0 0 1 0 0 = 0 := by
  constructor <;> norm_num [firstOrderSourceCount, firstOrderDimensionCount,
    Finset.sum_range_succ]

/-- Without the degree bound, the source count can exceed the dimension: `3 ≤ 2` fails. -/
example : firstOrderSourceCount 1 2 1 0 1 = 3 ∧ firstOrderDimensionCount 2 2 1 0 1 = 2 := by
  constructor <;> norm_num [firstOrderSourceCount, firstOrderDimensionCount,
    Finset.sum_range_succ]

/-! ### The generic challenge-height estimate specializes to the rounded degree -/

example {n N r mu : ℕ} {count : ℝ} (hsurplus : (r : ℝ) < count)
    (hN : n * count ≤ N) :
    n * r * mu / (N - n * r) ≤ max 1 ⌊(r : ℝ) * mu / (count - r)⌋₊ :=
  (scaledKernelHeight_le_floor hsurplus hN).trans (le_max_right _ _)

end ReedSolomon.HiddenDerivative
