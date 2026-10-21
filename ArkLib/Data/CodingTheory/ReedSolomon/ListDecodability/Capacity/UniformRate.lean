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
# Uniform Reed–Solomon list bounds near capacity

For a capacity gap `δ`, the uniform rate-partition construction gives an explicit derivative
order, jet-degree bound, and sufficient block length, all depending only on `δ`. For any distinct
evaluation points and received word, the complete list of degree-`< k` polynomials agreeing in at
least `A` positions is finite and obeys a polynomial bound in the block length. The field may be
infinite; in positive characteristic, its characteristic must be at least the block length.

## Main statements

* `uniformRatePartition_close_list_bound`: the finite complete-list bound with its parameters
  expanded.
* `uniform_capacity_list_bound`: the same bound with the derivative order, jet cap, and prefactor
  named in the conclusion.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative HiddenDerivative.RatePartition

open Classical in
/-- The uniform small-gap bound in expanded parameter form. The length threshold ensures the
chosen jet cap is below the block length, and the conclusion concerns the complete list. -/
theorem uniformRatePartition_close_list_bound {F : Type*} [Field F]
    {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    (hn : uniformBlockThreshold δ ≤ n)
    (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (uniformJetCap δ : ℝ) ^ 2 *
          (2 * uniformJetCap δ / δ) ^ uniformDerivativeOrder δ *
          n ^ uniformDerivativeOrder δ := by
  obtain ⟨e⟩ := exists_uniformRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  obtain ⟨hd, hδone, hν, _hνn, hscale, hkA, hchar'⟩ :=
    uniformEnvelope_exactAgreementGuards e hδ hδsmall hn hgap hchar
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hscale hAn
    domain (fun i ↦ Polynomial.C (received i)) (fun _ ↦ by simp)
  exact close_list_bound_of_curve_certificate_of_jetCharacteristic
    domain received cert hk e.message_le
    (by have := e.order_le; omega) e.ambient_le hkA hAn hν hδ hgap hchar'

open Classical in
/-- For every gap `δ` with `0 < δ < 6/25`, the complete list of degree-`< k` polynomials
agreeing with any received word in at least `A` positions is finite and has size at most
`C * n ^ d`, where `d = ⌈exp(3 / (2 * δ))⌉₊` and `C = ν² * (2ν/δ)^d` for the uniform
jet cap `ν`. -/
theorem uniform_capacity_list_bound
    (δ : ℝ)
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    (n k A : ℕ)
    (hn : uniformBlockThreshold δ ≤ n)
    (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let d := uniformDerivativeOrder δ
    let ν := uniformJetCap δ
    let C : ℝ := (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ C * n ^ d := by
  exact uniformRatePartition_close_list_bound hδ hδsmall hn hk hgap hAn
    domain received hchar

end ReedSolomon
