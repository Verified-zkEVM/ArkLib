/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.GlobalDimension
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FreeOrder

/-!
# Global dimension at the rounded free-order parameters

This module composes the exact rectangular support count with the rounded parameter inequalities.
It is the first direct interface from a freely chosen derivative order to the interpolation-space
dimension lower bound. The order remains an input and may therefore later be chosen uniformly by
a finite rate cover.

Adapted, with permission, from `rs-ld-mca` commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`.
-/

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

/-- The rounded free-order interpolation space has the rectangular dimension lower bound. -/
theorem finrank_scopedInterpolationSpace_lowerBound {F : Type*} [Field F]
    {epsilon theta : ℝ} {d n : ℕ}
    (hepsilon : 0 < epsilon) (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hd : 0 < d) (hn : 0 < n) (hdK : d < ambientDimension epsilon theta n) :
    (goodHigherExponents d (interpolationWeightBudget theta d)
          (higherJetDegreeBudget theta d)).card *
        (ambientDimension epsilon theta n - 1) * interpolationBoxWidth theta d ^ 3 ≤
      Module.finrank F
        (interpolationSpace F d (multiplicity d) (agreementThreshold epsilon n)
          (ambientDimension epsilon theta n) (interpolationDegreeBudget d epsilon theta n)
          (interpolationWeightBudget theta d) (higherJetDegreeBudget theta d)) := by
  obtain ⟨hH, hdegree, hweighted⟩ :=
    freeGlobalDimensionSlacks hepsilon htheta hthetaOne hd hn hdK
  exact finrank_interpolationSpace_lowerBound hd hH hdegree hweighted

end
end HiddenDerivative
end ReedSolomon
