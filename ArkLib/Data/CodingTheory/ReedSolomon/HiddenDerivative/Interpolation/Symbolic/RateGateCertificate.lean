/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.PartitionCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.FiniteSurplus
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.BlockLength

/-!
# Variable-margin rate certificates

This internal constructor connects the actual finite partition surplus to a
primitive symbolic equation. The separate moment theorem discharges its sole
analytic input before any public rate capstone is exported.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open Polynomial PolynomialDifferential SimplexIntegration RatePartition

/-- The integer primitive-kernel height fits the variable-margin curve budget. -/
theorem kernel_height_le_rateHeight {count rank order multiplicity curveDegree : ℕ}
    {rate agreement : ℝ} (hrate : 0 < rate) (hm : 0 < multiplicity)
    (hgamma : 1 < finiteGamma rate agreement order multiplicity)
    (hmargin : finiteGamma rate agreement order multiplicity * rank < count) :
    rank * (curveDegree * rateJetCap rate multiplicity) / (count - rank) ≤
      curveDegree * rateHeight rate agreement order multiplicity := by
  by_cases hcurve : curveDegree = 0
  · simp [hcurve]
  have hheight := kernel_height_lt_of_ratio hgamma
    (Nat.mul_pos (Nat.pos_of_ne_zero hcurve) (rateJetCap_pos hrate hm)) hmargin
  have hceil := Nat.le_ceil ((rateJetCap rate multiplicity : ℝ) /
    (finiteGamma rate agreement order multiplicity - 1))
  have hmax : (⌈(rateJetCap rate multiplicity : ℝ) /
      (finiteGamma rate agreement order multiplicity - 1)⌉₊ : ℝ) ≤
      rateHeight rate agreement order multiplicity := by
    exact_mod_cast le_max_right 1 ⌈(rateJetCap rate multiplicity : ℝ) /
      (finiteGamma rate agreement order multiplicity - 1)⌉₊
  have hscaled := mul_le_mul_of_nonneg_left (hceil.trans hmax) (Nat.cast_nonneg curveDegree)
  apply (Nat.cast_le (α := ℝ)).mp
  exact hheight.le.trans (by simpa only [Nat.cast_mul, mul_div_assoc] using hscaled)

/-- Actual primitive interpolation with the rate-dependent jet and variable height caps. -/
theorem exists_rateGate_certificate_of_moment {F : Type*} [Field F]
    {rate agreement : ℝ} {d m n k A curveDegree : ℕ}
    (hrate : 0 < rate) (hrateOne : rate < 1) (hagreement : 0 < agreement)
    (hd : 0 < d) (hm : 0 < m)
    (hbudget : 0 < partitionWeightBudget rate agreement d m)
    (hgamma : 1 < finiteGamma rate agreement d m)
    (hn : rateBlockThreshold rate d m ≤ n) (hk : (k : ℝ) ≤ rate * n)
    (hA : agreement * n ≤ A) (hAn : A ≤ n)
    (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ index, (received index).natDegree ≤ curveDegree)
    (hmoment : (27 / 10 : ℝ) < weightedSimplexExpectation d
      (partitionWeightBudget rate agreement d m)
      (fun point ↦ (max (Real.log (6 * (d : ℝ)) - (d : ℝ) * weightedRadius point /
        partitionWeightBudget rate agreement d m) 0) ^ 2)) :
    Nonempty (Certificate F A k curveDegree (rateJetCap rate m) d
      (curveDegree * rateHeight rate agreement d m) centers received) := by
  obtain ⟨horder, hhalf, hkD, _, _, _, hnPos⟩ := rateBlockThreshold_ambient hrate hrateOne hn hk
  have hD : 0 < ⌊rate * n⌋₊ := by omega
  have hApos : 0 < A := Nat.cast_pos.mp
    ((mul_pos hagreement (Nat.cast_pos.mpr hnPos)).trans_le hA)
  have hmargin := partitionSupport_finiteGamma_surplus (F := F)
    hD hd hnPos hm hbudget hrate hagreement
    (Nat.floor_le (show 0 ≤ rate * n by positivity)) hA hmoment
  have hmargin' : finiteGamma rate agreement d m *
      ((n * partitionLocalRankBound d m (partitionWeightBudget rate agreement d m) : ℕ) : ℝ) <
      (Module.finrank F (partitionSupportSpace F ⌊rate * n⌋₊ d
        (partitionWeightBudget rate agreement d m) (m * A : ℕ) hD) : ℝ) := by
    simpa only [Nat.cast_mul, mul_assoc] using hmargin
  have hsurplus : n * partitionLocalRankBound d m (partitionWeightBudget rate agreement d m) <
      Module.finrank F (partitionSupportSpace F ⌊rate * n⌋₊ d
        (partitionWeightBudget rate agreement d m) (m * A : ℕ) hD) := by
    have hnonnegative := Nat.cast_nonneg
      (n * partitionLocalRankBound d m (partitionWeightBudget rate agreement d m)) (α := ℝ)
    apply (Nat.cast_lt (α := ℝ)).mp
    nlinarith
  obtain ⟨certificate⟩ := exists_partition_certificate_of_surplus hD le_rfl
    (Nat.mul_pos hm hApos) (hkD.trans (Nat.le_succ _)) centers received hreceived
    (fun _ heligible ↦ partitionSupport_totalJetDegree_le_rateJetCap
      hrate hnPos hhalf hAn heligible) hsurplus
  refine ⟨{ certificate with challengeDegree_le := fun exponent ↦
    (certificate.challengeDegree_le exponent).trans ?_ }⟩
  exact kernel_height_le_rateHeight hrate hm hgamma hmargin'

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
