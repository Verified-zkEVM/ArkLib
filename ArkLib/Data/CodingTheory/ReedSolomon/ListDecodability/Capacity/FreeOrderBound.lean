/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CertificateRootBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.QuarterGap
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupport


/-!
# Qualitative all-rate Reed--Solomon list bounds

The generic theorem in this module turns any uniform family of actual hidden-derivative
constructions into the canonical all-rate polynomial-list contract. The concrete theorem combines
the elementary quarter-gap certificate with the prescribed no-band weighted-support certificate.
Oversized agreement thresholds yield empty lists without requiring an impossible interpolant.

The finite-set decoder is a classical witness, not a polynomial-time implementation. The
paper-facing quantitative list theorem is in `Capacity.lean`; the generic transformer here remains
available to alternative uniform families of interpolation witnesses.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 7.1, Proposition 7.1
  (all-rate transfer from the low-rate certificate).
-/

@[expose] public section

namespace ReedSolomon

open HiddenDerivative

noncomputable section

/-- Uniform actual constructions imply gap-only polynomial bounds for all rates, including the
canonical relative-radius and empty-list conventions. There is no algorithmic claim. -/
theorem capacityListBound_of_uniform_interpolation
    (hConstruction : UniformHiddenDerivativeInterpolation) :
    UniformPrimeFieldCapacityListBound := by
  intro delta hdelta hOne
  obtain ⟨d, m, N, _hm, hConstruct⟩ := hConstruction delta hdelta hOne
  refine ⟨N, 2 * (d + 1), 3 * d + 2, by positivity, ?_⟩
  intro n k q hn hk hkn hq hnq domain
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨CapacityGapCertificate.ofPointwiseBound hdelta.le (hk.trans_le hkn) domain ?_⟩
  intro received
  by_cases hA : agreementThreshold delta n k ≤ n
  · obtain ⟨construction⟩ := hConstruct n k q hn hk hkn hq hnq hA domain received
    exact construction.agreeingPolynomials_encard_le
  · rw [agreeingPolynomials_eq_empty_of_card_lt
      (by simpa using Nat.lt_of_not_ge hA) received]
    simp

/-- Unconditional qualitative all-rate list decoding over prime fields, with constants depending
only on the gap. The large-gap branch uses elementary pairwise-agreement counting, while the
small-gap branch uses the prescribed weighted-support certificate. This is not an algorithmic
running-time claim. -/
theorem uniform_primeField_capacityListBound : UniformPrimeFieldCapacityListBound := by
  intro delta hdelta hOne
  by_cases hquarter : (1 / 4 : ℝ) ≤ delta
  · obtain ⟨N, hlargeGap⟩ := quarter_gap_list_bound delta hquarter hOne
    refine ⟨N, 4, 1, by norm_num, ?_⟩
    intro n k q hn hk hkn hq hnq domain
    obtain ⟨⟨certificate⟩, _hstrict⟩ := hlargeGap n k q hn hk hkn hq hnq domain
    refine ⟨CapacityGapCertificate.ofPointwiseBound hdelta.le
      (hk.trans_le hkn) domain ?_⟩
    intro received
    have hpointwise := (certificate.pointwiseListBound received).1
    by_cases hhalf : (1 / 2 : ℝ) ≤ delta
    · simp only [hhalf, if_true] at hpointwise
      apply hpointwise.trans
      simp only [polynomialListBound, pow_one, Nat.cast_mul, Nat.cast_ofNat]
      exact_mod_cast (show 1 ≤ 4 * q by omega)
    · simpa only [hhalf, if_false, polynomialListBound, pow_one] using hpointwise
  · have hsmall : delta < (1 / 4 : ℝ) := lt_of_not_ge hquarter
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    refine ⟨8 * m, 4 * m, 2 * d, ?_, ?_⟩
    · exact Nat.mul_pos (by norm_num) (weightedSupportMultiplicity_pos hdelta hsmall)
    · intro n k q hn hk hkn hq hnq domain
      obtain ⟨certificate, _largeFieldCertificate⟩ :=
        weightedSupport_capacity_list_bound_four_mul delta hdelta hsmall
          n k q (by simpa only [m] using hn) hk hkn hq hnq domain
      simpa only [polynomialListBound, d, m] using certificate

end
end ReedSolomon
