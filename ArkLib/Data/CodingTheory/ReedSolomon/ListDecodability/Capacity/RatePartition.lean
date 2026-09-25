/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.RateCertificate

/-!
# Rate-partition bounds for Reed–Solomon lists

A strict limiting rate gate selects finite interpolation parameters for a fixed derivative
order. Once the selected block-length threshold is met, the resulting complete-list bound is
uniform over fields, codes, evaluation sets, and received words.

## Main statements

* `ratePartition_close_list_bound`: a finite rate-partition certificate bounds the complete list.
* `exists_ratePartition_list_bound`: a strict limiting gate selects parameters for that bound.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- A finite rate-partition parameter record gives a complete-list bound for every code beyond
its selected block-length threshold. -/
theorem ratePartition_close_list_bound
    {F : Type u} [Field F]
    {R a : ℝ} {d n k A : ℕ}
    (p : RatePartition.PartitionFiniteParameters R a d)
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hn : RatePartition.rateBlockThreshold R d p.multiplicity ≤ n)
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (max (k - 1) d) (RatePartition.rateJetCap R p.multiplicity) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (RatePartition.rateJetCap R p.multiplicity : ℝ) ^ 2 *
          (2 * RatePartition.rateJetCap R p.multiplicity / (a - R)) ^ d * n ^ d := by
  obtain ⟨cert⟩ := exists_partitionSupport_curve_certificate_of_rateBlockThreshold p hR
    (hRa.trans haone)
    (hR.trans hRa) hd hn hkR haA hAn domain (fun i ↦ Polynomial.C (received i))
    (fun _ ↦ by simp)
  let K := max k (d + 1)
  obtain ⟨hkK, hdK, hKn, hkA, hν, _, hchar'⟩ :=
    RatePartition.rateBlockThreshold_exactAgreementGuards p hR hRa haone hn hkR haA hchar
  apply close_list_bound_of_curve_certificate_of_jetCharacteristic domain received cert hk
    hkK hdK hKn hkA hAn hν (sub_pos.mpr hRa) ?_ hchar'
  nlinarith

open Classical in
/-- A strict rate gate selects finite parameters that give a uniform complete-list bound for
every field and code beyond the selected threshold. -/
theorem exists_ratePartition_list_bound
    {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hgate : 1 < RatePartition.rateGamma R a d) :
    ∃ p : RatePartition.PartitionFiniteParameters R a d,
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      RatePartition.rateBlockThreshold R d p.multiplicity ≤ n → 0 < k →
      (k : ℝ) ≤ R * n →
      a * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      (ringChar F = 0 ∨
        max (max (k - 1) d) (RatePartition.rateJetCap R p.multiplicity) < ringChar F) →
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (RatePartition.rateJetCap R p.multiplicity : ℝ) ^ 2 *
            (2 * RatePartition.rateJetCap R p.multiplicity / (a - R)) ^ d * n ^ d := by
  have hdpos : 0 < d := by omega
  have hlimit : 1 < (27 / 20 : ℝ) * R * (d + 1) *
      Real.exp (-(R / a * Real.log (6 * (d : ℝ)))) := by
    rw [← RatePartition.rateGamma_eq_exponential (agreement := a) hdpos]
    exact hgate
  obtain ⟨p⟩ := RatePartition.PartitionFiniteParameters.nonempty hR
    (hR.trans hRa) hdpos hlimit
  refine ⟨p, fun _ _ _ _ _ hn hk hkR haA hAn domain received hchar ↦ ?_⟩
  exact ratePartition_close_list_bound p hR hRa haone hd hn hk hkR haA hAn domain received hchar

end ReedSolomon
