/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.ScopedGlobalDimension

/-!
# Regression canaries for the audited donor port

These small specializations guard the two reusable endpoints of the initial donor port: a free
order can be chosen after fixing `(epsilon, theta)`, and the rectangular dimension injection works
over a generic field with exact natural-number slack hypotheses.
-/

namespace ReedSolomon
namespace HiddenDerivative

example :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      2 ≤ d ∧
      2 ≤ (1 / 2 : ℝ) * (multiplicity d : ℝ) / 16 ∧
      1 < (((1 / 2 : ℝ) ^ 3) / 262144) *
        ((1 - (1 / 2 : ℝ)) * (1 / 2 : ℝ) / 2) *
        (d : ℝ) ^ rankSavingExponent (1 / 2) := by
  exact exists_freeOrderElementaryThreshold (by norm_num) (by norm_num) (by norm_num)

example :
    (goodHigherExponents 1 0 0).card * (3 - 1) * 1 ^ 3 ≤
      Module.finrank ℚ (interpolationSpace ℚ 1 1 6 3 2 0 0) := by
  exact finrank_interpolationSpace_lowerBound
    (F := ℚ) (d := 1) (m := 1) (A := 6) (K := 3) (B := 2) (W := 0) (C := 0)
      (H := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HiddenDerivative
end ReedSolomon
