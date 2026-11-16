/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interpolation
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterpolationParams

/-! # Acceptance cases for the affine interpolation -/

open ReedSolomon

/-- The standing hypotheses hold at `d = 16`, `n = 100`, `η = 1/2`, where `√ρ = 2/5`. -/
example : AffineParams 16 100 (1 / 2) := by
  have hsqrt : √((16 : ℕ) / ((100 : ℕ) : ℝ)) = 2 / 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [hsqrt]; norm_num
  · norm_num

/-- The parameters feed the interpolation: an interpolant exists at those budgets. -/
example {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] (domain : ι ↪ F)
    (f g : ι → F) {d : ℕ} {η : ℝ} (h : AffineParams d (Fintype.card ι) η) :
    ∃ Q, IsAffineInterpolant domain f g d (affineThreshold d (Fintype.card ι) η)
      (affineMultiplicity η) (affineYZBudget d (Fintype.card ι) η)
      (affineRootBudget d (Fintype.card ι) η) Q :=
  exists_isAffineInterpolant domain f g h.surplus
