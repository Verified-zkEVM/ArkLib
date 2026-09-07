/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.CurveCertificate
import ArkLibExamples.ReedSolomon.ProveKit
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.FirstOrderCurveBound
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.FirstOrderCurveStageSum
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Numerator

/-!
# Exact exceptional-envelope arithmetic for the concrete curve profiles

The ProveKit interpolation profiles fix the equation heights. Here we evaluate the
sharper joint-and-fiber expression at the chosen split. Rational comparisons are
checked by the Lean kernel.

These are arithmetic lemmas for the geometric theorem: their conclusions concern the
explicit envelope, not an assumed or independently defined exceptional set.
-/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ConcreteCurveBounds

open CurveProfile CurveCertificate

/-! ## Revised ProveKit cubic-Goldilocks row -/

/-- The retained-pair split selected for the revised cubic-Goldilocks row. -/
def proveKitGoldilocksCubicSplit : ℕ := 268399

/-- The shifted finite constructor's challenge height for the revised row. -/
def proveKitGoldilocksCubicHeight : ℕ := 339

/-- The exact common Taylor exponent is `2k - 3 = 524285`. -/
theorem proveKitGoldilocksCubic_taylorExponent :
    2 * ProveKit.goldilocksCubic113.k - 3 = 524285 := by
  norm_num [ProveKit.goldilocksCubic113]

/-- This exponent is sufficient at every derivative order, including the order-one stages. -/
theorem proveKitGoldilocksCubic_taylorExponent_sufficient (r : ℕ) :
    TaylorExponentSufficient r ProveKit.goldilocksCubic113.k 524285 := by
  simpa [ProveKit.goldilocksCubic113] using
    taylorExponentSufficient_two_mul_sub_three r (by norm_num : 2 ≤ 262144)

/-- The revised `λ₁η` envelope at `τ = 2k - 3` lies below the integer ceiling used by
the concrete Goldilocks exceptional-set theorem. -/
theorem proveKitGoldilocksCubic_envelope_le :
    firstOrderCurveBound 1048576 262144 262144 proveKitGoldilocksCubicSplit 508263
        30 7 1 proveKitGoldilocksCubicHeight 524285
          (firstOrderCurveDirectRatio 1048576 262144 508263) ≤
      ProveKit.goldilocksCubic113.exceptionalCount := by
  decide +kernel

end ArkLibExamples.ReedSolomon.ConcreteCurveBounds
