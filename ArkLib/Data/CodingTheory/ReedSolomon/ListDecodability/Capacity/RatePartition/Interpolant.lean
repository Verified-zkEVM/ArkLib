/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Certificates
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition.DimensionBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.ExactCharacteristicBudget
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Interpolation
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Rank
/-!
# Uniform hidden-derivative interpolants from rate-bin bounds

The finite interpolation-dimension certificate and the actual local-rank bound give a nonzero
exact interpolant.
Its bin agreement threshold is at most the requested `k + ceil(delta * n)`: this relaxes the
weighted-degree bound while retaining the sharper bin support bound for the characteristic
check. The requested contact budget is proved separately, since increasing an agreement threshold
does not preserve an upper bound on its product with the multiplicity.

The resulting order and multiplicity are chosen before all code parameters. This establishes the
qualitative construction contract, with unoptimized order and multiplicity `d^3`; it supplies no
executable decoder or operation bound. The imported source estimates retain their permission and
provenance records in `RateBinDimensionBound.lean`.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], global
  interpolation principle and uniform all-rate construction.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

open HiddenDerivative RateBinInterpolation RateBinDimensionBound

noncomputable section

/-- A finite interpolation-dimension certificate produces an interpolant at the requested agreement
threshold. The contact budget here is for that requested threshold, rather than the smaller bin
threshold. Original messages retain their dimension `k`, inside the bin ambient space. -/
theorem RateBinDimensionBound.CoveringInterpolationDimensionBound.nonempty_interpolationCertificate
    {delta : ℝ} {d n q k : ℕ} {i : Fin (RateCover.binCount delta)} [Fact q.Prime]
    (certificate : CoveringInterpolationDimensionBound (ZMod q) delta d n q k i)
    (hContact : d ^ 3 * agreementThreshold delta n k ≤ q ^ 2)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    Nonempty (HiddenDerivativeInterpolationCertificate (k := k) (A := agreementThreshold delta n k)
      d (d ^ 3) domain received) := by
  have hd : 0 < d := by
    have := certificate.orderAtLeastTwo
    omega
  have hdD : d < ambientDimension (binAgreement delta i) (binSlack delta i) n - 1 := by
    have := certificate.order_succ_lt_ambient
    omega
  have hn : 0 < n :=
    blockLength_pos_of_order_lt_ambientDimension certificate.order_lt_ambient
  have hBudget : 0 < d ^ 3 * HiddenDerivative.agreementThreshold (binAgreement delta i) n :=
    Nat.mul_pos (by positivity) (HiddenDerivative.agreementThreshold_pos
      certificate.agreement_mem.1 hn)
  obtain ⟨Q, hQZero, hQSpace, hQLocal⟩ :=
    exists_nonzero_global_interpolant_of_uniform_local_rank_bound
      (A := HiddenDerivative.agreementThreshold (binAgreement delta i) n)
      (m := d ^ 3) (M := d ^ 3) (W := interpolationWeightBudget (binSlack delta i) d)
      hdD (fun j ↦ domain j) received
      (certifiedEnlargedRankBound d (d ^ 3) (d ^ 3)
        (interpolationWeightBudget (binSlack delta i) d))
      (fun j ↦ finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound
        hd hdD (domain j) (received j))
      (by simpa using certificate.finiteRankComparison)
  refine ⟨{
    ambientDim := ambientDimension (binAgreement delta i) (binSlack delta i) n
    messageDim_le := certificate.messageDim_le_ambient
    ambientDim_le := (ambientDimension_lt_blockLength certificate.agreement_mem.1
      certificate.agreement_mem.2 certificate.slack_mem.1 certificate.slack_mem.2 hn).le
    order_lt_degree := hdD
    interpolant := Q
    nonzero := hQZero
    weighted_degree_lt := ?_
    below_characteristic := ?_
    contact_budget_le := hContact
    local_constraints := hQLocal
  }⟩
  · exact (differentialWeightedDegree_lt_of_mem_exactInterpolationSpace
      hBudget hdD hQSpace).trans_le
        (Nat.mul_le_mul_left (d ^ 3) certificate.binAgreement_le_requested)
  · apply isBelowCharacteristic_of_mem_exactInterpolationSpace Q hQSpace
    · simpa only [ringChar.eq (ZMod q) q] using certificate.ambientDegree_lt_fieldSize
    · simpa only [ringChar.eq (ZMod q) q] using certificate.exactJetDegreeBudget_lt_fieldSize

/-- Gap-only parameters produce actual constructions for every feasible requested threshold.
The extra maximum in the block threshold proves the requested contact budget `m*A ≤ q²`, while
the characteristic budget still uses the bin exact interpolation space. -/
theorem uniform_hiddenDerivative_interpolation : UniformHiddenDerivativeInterpolation := by
  intro delta hdelta hdeltaOne
  obtain ⟨d, N, hd, hCertificates⟩ :=
    exists_uniform_finite_covered_bin_certificates hdelta hdeltaOne
  refine ⟨d, d ^ 3, max N (d ^ 3), by positivity, ?_⟩
  intro n k q hn hk hkn hq hnq hAgreement domain received
  let : Fact q.Prime := ⟨hq⟩
  have hnPos : 0 < n := hk.trans_le hkn
  have hRate : (k : ℝ) / n ≤ 1 - delta := by
    have hThreshold : (k : ℝ) + (⌈delta * (n : ℝ)⌉₊ : ℝ) ≤ n := by
      exact_mod_cast hAgreement
    have hCeil := Nat.le_ceil (delta * (n : ℝ))
    rw [div_le_iff₀ (by exact_mod_cast hnPos)]
    nlinarith
  obtain ⟨i, hCertificate⟩ := hCertificates n q k ((Nat.le_max_left _ _).trans hn) hnq hRate
  apply (hCertificate (ZMod q)).nonempty_interpolationCertificate _ domain received
  calc
    d ^ 3 * agreementThreshold delta n k ≤ n * n :=
      Nat.mul_le_mul ((Nat.le_max_right _ _).trans hn) hAgreement
    _ ≤ q * q := Nat.mul_le_mul hnq hnq
    _ = q ^ 2 := by ring

end
end ReedSolomon
