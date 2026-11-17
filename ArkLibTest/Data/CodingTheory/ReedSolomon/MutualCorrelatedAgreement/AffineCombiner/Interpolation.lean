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

-- The paper's parameter choice has these exact finite budgets.
example : affineMultiplicity (1 / 2) = 4 ∧ affineYZBudget 16 100 (1 / 2) = 42 ∧
    affineThreshold 16 100 (1 / 2) = 90 ∧ affinePersistenceThreshold 16 100 (1 / 2) = 64 ∧
    affineRootBudget 16 100 (1 / 2) = 19 := by
  have hsqrt : √((16 : ℝ) / 100) = 2 / 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  have hceil : ⌈(675 : ℝ) / 16⌉₊ = 43 := by
    apply (Nat.ceil_eq_iff (by norm_num)).mpr
    norm_num
  unfold affineRootBudget affineYZBudget affineThreshold affinePersistenceThreshold
  norm_num only [Nat.cast_ofNat]
  have hsqrt' : √((4 : ℝ) / 25) = 2 / 5 := by
    convert hsqrt using 2; norm_num
  rw [hsqrt']
  norm_num [affineMultiplicity, hceil]

-- The general sufficient count is stricter than (4.5) when M is freely chosen.
open Polynomial.SymbolicInterpolation in
example : (monomialSupport 1 (4 * 5 - 3) (2 + 1) (3 + 1)).card = 146 ∧
    5 * (constraintSupport 4 (3 + 1)).card = 150 ∧
    5 * (∑ s ∈ Finset.range (min (4 - 1) 2 + 1), (4 - s) * (3 + 1 - s)) = 145 := by
  norm_num [card_monomialSupport, card_constraintSupport, Finset.sum_range_succ]
