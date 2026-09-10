/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Parameters
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Basic

/-! # Total jet bounds for the rate-partition support -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

/-- The ambient rate lower bound converts weighted support to an independent total-jet cap. -/
theorem ratePartition_totalJetDegree_le {D d W m n A : ℕ} {R : ℝ}
    (hD : 0 < D) (hR : 0 < R)
    (hDlower : R * n / 2 ≤ D) (hAn : A ≤ n)
    {u : JetVariable d →₀ ℕ} (hu : RatePartitionEligible D d W (m * A : ℕ) u) :
    totalJetDegree u ≤ ratePartitionJetBound R m := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have ht := totalJetDegree_lt_of_ratePartitionEligible hD hu
  have hb : ((m * A : ℕ) : ℝ) / D ≤ 2 * (m : ℝ) / R := by
    apply (div_le_div_iff₀ hD' hR).mpr
    have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hDlower (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hm'),
      mul_le_mul_of_nonneg_left hAn' (mul_nonneg hm' hR.le)]
  have hceil : 2 * (m : ℝ) / R ≤ ratePartitionJetBound R m := Nat.le_ceil _
  exact_mod_cast (ht.le.trans (hb.trans hceil))

end ReedSolomon.HiddenDerivative
