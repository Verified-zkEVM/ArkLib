/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.BlockLength
public import Mathlib.Tactic.Linarith

/-!
# Total jet degree under the rate-partition ambient bound

If the ambient degree is at least half the rate-scaled block length, the total jet degree of every
partition-support eligible exponent is bounded by the rate-dependent jet cap.

## Main statements

* `partitionSupport_totalJetDegree_le_rateJetCap`: the total jet degree is at most `⌈2m/R⌉₊`.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

open PolynomialDifferential

/-- The ambient rate lower bound and `A ≤ n` bound the total jet degree in the partition support
by the rate-dependent cap. -/
theorem partitionSupport_totalJetDegree_le_rateJetCap {D d W m n A : ℕ} {rate : ℝ}
    (hD : 0 < D) (hrate : 0 < rate) (hDlower : rate * n / 2 ≤ D) (hAn : A ≤ n)
    {u : JetVariable d →₀ ℕ} (hu : PartitionSupportEligible D d W (m * A : ℕ) u) :
    totalJetDegree u ≤ rateJetCap rate m := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have ht := totalJetDegree_lt_of_partitionSupportEligible hD hu
  have hb : ((m * A : ℕ) : ℝ) / D ≤ 2 * (m : ℝ) / rate := by
    apply (div_le_div_iff₀ hD' hrate).mpr
    have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hDlower
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hm'),
      mul_le_mul_of_nonneg_left hAn' (mul_nonneg hm' hrate.le)]
  have hceil : 2 * (m : ℝ) / rate ≤ rateJetCap rate m := Nat.le_ceil _
  exact_mod_cast (ht.le.trans (hb.trans hceil))

end ReedSolomon.HiddenDerivative.RatePartition
