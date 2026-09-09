/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.ProductBounds
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductCounting
/-! # Product estimates below the derivative-order cap

These examples keep the original code dimension smaller than the incidence dimension.
The paper product is untruncated; the estimates must not silently require `r ≤ k`.
-/

namespace ReedSolomon

example : correlatedProductCutoff 5 1 10 = 8 := by
  norm_num [correlatedProductCutoff, Nat.floor_eq_iff]

example :
    (AffineHilbert.dimensionSensitiveIncidenceProduct 20
      (correlatedProductCutoff 5 1 10) 1 1 4 : ℝ) < 3 * (1 / (1 / 4 : ℝ)) ^ 4 := by
  exact correlatedProductCutoff_fiberProduct_lt_three (1 / 4) 20 1 10 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example (δ : ℝ) (v h d : ℕ) :
    polynomialCurveProductMCAConstant δ v h d =
      (h : ℝ) + 2 ^ d * (v : ℝ) ^ (d + 2) * (1 / δ) ^ d *
        ((h : ℝ) * (d + 1) * (3 * d + 5) / δ + 3) := rfl

example :
    AffineHilbert.hybridDimensionSensitiveIncidenceProduct 20 10 8 1 1 (min 4 1 + 1) ≤
      (((20 - 8 + 1 : ℕ) : ℚ) / (10 - 8 + 1 : ℕ)) *
        AffineHilbert.dimensionSensitiveIncidenceProduct 20 10 1 1 4 := by
  exact AffineHilbert.hybridDimensionSensitiveIncidenceProduct_min_le
    20 10 8 1 1 4 (by norm_num) (by norm_num) (by norm_num)

end ReedSolomon
