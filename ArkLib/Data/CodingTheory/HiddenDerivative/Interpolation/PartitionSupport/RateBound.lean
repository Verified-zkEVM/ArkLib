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
# Rate-dependent degree bound for partition support

Ambient lower bounds on the interpolation degree and the block length bound the total jet degree
of every eligible partition-support exponent. This gives both a gap-dependent cap and the
rate-dependent cap.

## Main statements

* `partitionSupport_totalJetDegree_le_of_ambient_lower_bound`: an ambient lower bound gives the
  cap `⌈m / δ²⌉₊ - 1` for any multiplicity.
* `partitionSupport_totalJetDegree_le_rateJetCap`: the total jet degree is at most `⌈2m/R⌉₊`.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

open PolynomialDifferential

/-- An ambient degree at least `δ² n` and `A ≤ n` bound each eligible exponent's total jet degree
by `⌈m / δ²⌉₊ - 1`, for any multiplicity `m`. -/
theorem partitionSupport_totalJetDegree_le_of_ambient_lower_bound
    {D d W m n A : ℕ} {δ : ℝ} (hD : 0 < D) (hδ : 0 < δ)
    (hDlower : δ ^ 2 * n ≤ D) (hAn : A ≤ n) {u : JetVariable d →₀ ℕ}
    (hu : PartitionSupportEligible D d W (m * A : ℕ) u) :
    totalJetDegree u ≤ ⌈(m : ℝ) / δ ^ 2⌉₊ - 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have ht := totalJetDegree_lt_of_partitionSupportEligible hD hu
  have hb : ((m * A : ℕ) : ℝ) / D ≤ (m : ℝ) / δ ^ 2 := by
    apply (div_le_div_iff₀ hD' hδ2).2
    have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hDlower hm',
      mul_le_mul_of_nonneg_left hAn' (mul_nonneg hm' hδ2.le)]
  have hc : (m : ℝ) / δ ^ 2 ≤ ⌈(m : ℝ) / δ ^ 2⌉₊ := Nat.le_ceil _
  have hlt : (totalJetDegree u : ℝ) < ⌈(m : ℝ) / δ ^ 2⌉₊ := by
    exact_mod_cast (ht.trans_le (hb.trans hc))
  change totalJetDegree u ≤ ⌈(m : ℝ) / δ ^ 2⌉₊ - 1
  exact Nat.le_sub_one_of_lt (by exact_mod_cast hlt)

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
