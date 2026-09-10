/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.RankCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Parameters

/-! # Challenge-height rounding from the actual finite ratio -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

/-- Ceil the height after dividing by the strict margin, uniformly in the curve degree. -/
theorem kernel_height_le_ratePartitionHeight {N r ℓ ν : ℕ} {γ : ℝ}
    (hγ : 1 < γ) (hmargin : γ * r < N) :
    r * (ℓ * ν) / (N - r) ≤ ℓ * ratePartitionHeight ν γ := by
  by_cases hb : 0 < ℓ * ν
  · have hh := kernel_height_lt_div_margin hγ hb hmargin
    have hc : (ν : ℝ) / (γ - 1) ≤ ratePartitionHeight ν γ :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
    have hbnd := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg ℓ (α := ℝ))
    have heq : ((ℓ * ν : ℕ) : ℝ) / (γ - 1) = (ℓ : ℝ) * ((ν : ℝ) / (γ - 1)) := by
      push_cast
      ring
    rw [heq] at hh
    exact_mod_cast (hh.le.trans hbnd)
  · have hz : ℓ * ν = 0 := by omega
    simp only [hz, mul_zero, Nat.zero_div]
    exact Nat.zero_le _

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
