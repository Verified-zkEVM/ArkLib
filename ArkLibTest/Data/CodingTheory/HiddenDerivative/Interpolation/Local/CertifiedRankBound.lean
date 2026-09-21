/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.CertifiedRankBound

/-!
# Certified rank bound acceptance tests

The source-shaped uniform statement, and a concrete numerical instance.
-/

open Module PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Source shape: one bound, uniform over all centers and received values. -/
example {F : Type*} [Field F] {d D A m M W : ℕ} (hd : 0 < d) (hdD : d < D) :
    ∀ center received : F,
      finrank F (LinearMap.range
          (exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received)) ≤
        certifiedEnlargedRankBound d m M W :=
  fun center received =>
    finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound hd hdD center received

/-- For `d = 1, D = 2, m = 2, M = 1, W = 0` the local constraint rank is at most `5`: the
intermediate space has dimension `6` and the exhibited kernel dimension `1`. -/
example {A : ℕ} (center received : ℚ) :
    finrank ℚ (LinearMap.range (exactLocalConstraintAt (D := 2) (A := A) (M := 1) (W := 0)
        (d := 1) (by norm_num) 2 center received)) ≤ 5 := by
  have h := finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound (A := A) (M := 1)
    (W := 0) (m := 2) (by norm_num : 0 < 1) (by norm_num : 1 < 2) center received
  have h5 : certifiedEnlargedRankBound 1 2 1 0 = 5 := by decide
  omega
