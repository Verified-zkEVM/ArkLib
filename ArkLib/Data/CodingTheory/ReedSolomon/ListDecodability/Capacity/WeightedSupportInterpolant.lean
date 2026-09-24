/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Certificates
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Interpolation
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SolutionEmbedding
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
public import ArkLib.Data.Polynomial.Differential.DerivativeDescent
public import ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin
import ArkLib.Data.Polynomial.Differential.WitnessCount


/-!
# Construction and finite-field root bounds from weighted support

The symbolic primitive-kernel construction is specialized at challenge zero. Its no-bad-challenge
property supplies nonzeroness, while coefficient specialization preserves the actual weighted
support and every local constraint. The resulting certificate gives a finite-field list bound by
embedding agreeing polynomials into the bounded solutions of its interpolant.

## Main statements

* `exists_prescribed_weightedSupport_construction`: a hidden-derivative certificate at the
  prescribed weighted-support parameters.
* `HiddenDerivativeInterpolationCertificate.agreeingPolynomials_encard_le_totalJetDegree`: the
  list size is at most `4 * m * q ^ (e * d)` under the extension-field budget.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

noncomputable section

open HiddenDerivative ListDecoding Polynomial
open HiddenDerivative.WeightedSupportParameters

set_option maxHeartbeats 800000 in
-- The prescribed margin expands the continuous simplex and symbolic kernel constructions.
/-- The explicit prescribed weighted-support parameters give a genuine hidden-derivative
construction. The original message dimension remains the input parameter. -/
private theorem exists_prescribed_weightedSupport_construction_core
    {δ : ℝ} {n k q : ℕ} [Fact q.Prime]
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hnq : n ≤ q) (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let K := max k (Nat.floor (δ * n / 2))
    ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := k) (A := agreementThreshold δ n k) d m domain received,
      construction.ambientDim = K ∧ jetTotalDegree construction.interpolant < 2 * m := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let H : ℝ := harmonic (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let K := max k (Nat.floor (δ * n / 2))
  let D := K - 1
  let A := agreementThreshold δ n k
  let g := rateGap δ ((D : ℝ) / n)
  let W := Nat.floor ((1 + theta * g) * d * m / H)
  have hblock' : 8 * m ≤ n := by simpa only [m, H, d] using hblock
  have hA' : k + ⌈δ * n⌉₊ ≤ n := by
    simpa only [agreementThreshold] using hA
  have hb := prescribedBlockBounds δ n k hδ hδmax.le
    (by simpa only [H, d, m] using hblock) hA'
  have hb' :
      0 < n ∧ 0 < D ∧ d < D ∧ δ / 3 ≤ (D : ℝ) / n ∧
        (D : ℝ) / n ≤ 1 - δ ∧ K ≤ n ∧
          (D : ℝ) * (1 + g) ≤ A := by
    simpa only [d, K, D, A, g, xi, agreementThreshold, rateGap] using hb
  obtain ⟨hn, hD, hdD, hρlo, hρhi, hKn, hslack⟩ := hb'
  have hρ : 0 < (D : ℝ) / n :=
    div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hn)
  have ho := prescribed_order_lower δ hδ hδmax.le
  have hHlo : xi / δ ≤ H := by
    simpa only [H, d] using ho.2.2
  have hdLower : 3 ≤ d := by
    have := ho.1
    dsimp only [d] at this ⊢
    omega
  obtain ⟨hmpos, _hWpos, _hmean, _hradius, _hfloor⟩ :=
    prescribed_dimension_inputs δ ((D : ℝ) / n) H d hδ hδmax.le hρ hρhi
      hdLower hHlo
  have hmargin := prescribed_weightedSupport_margin
    (F := ZMod q) δ n D hδ hδmax.le hn hD hρlo hρhi
  have hcut : (D : ℝ) * m * (1 + g) ≤ (m * A : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    push_cast
    nlinarith
  have hmargin' : (543 / 500 : ℝ) * n *
      Module.finrank (ZMod q) (LinearMap.range
        (weightedSupportLocalConstraint (R := ZMod q) (d := d) (W := W)
          (L := (D : ℝ) * m * (1 + g)) m hD 0 0)) <
      Module.finrank (ZMod q) (weightedSupportSpace (ZMod q) D d W
        ((D : ℝ) * m * (1 + g)) hD) := by
    change (543 / 500 : ℝ) * n *
        Module.finrank (ZMod q) (LinearMap.range
          (weightedSupportLocalConstraint (R := ZMod q) (d := d) (W := W)
            (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) <
        Module.finrank (ZMod q) (weightedSupportSpace (ZMod q) D d W
          ((m : ℝ) * D * (1 + g)) hD) at hmargin
    rw [show (m : ℝ) * D * (1 + g) = D * m * (1 + g) by ring] at hmargin
    exact hmargin
  obtain ⟨Q, hQ0, _hQsupport, hQlocal, hQtotal, hQweight⟩ :=
    exists_weightedSupport_interpolant_of_fixed_margin domain received hD hmpos
      (show 0 < A from hk.trans_le (Nat.le_add_right _ _)) (rateGap_le_one _ _)
      hcut hmargin'
  have hkK : k ≤ K := by
    dsimp only [K]
    exact Nat.le_max_left _ _
  have hmchar : 2 * m < ringChar (ZMod q) := by
    rw [ringChar.eq (ZMod q) q]
    have : 2 * m < 8 * m := by omega
    exact this.trans_le (hblock'.trans hnq)
  have hcast : ∀ j, JetDegreeCastsNeZero Q j :=
    jetDegreeCastsNeZero_of_jetTotalDegree_charGuard (le_of_lt hQtotal) (Or.inr hmchar)
  have hcontact : m * A ≤ q ^ 2 := by
    have hmle : m ≤ q := (by omega : m ≤ n).trans hnq
    have hAle : A ≤ q := hA.trans hnq
    calc
      m * A ≤ q * q := Nat.mul_le_mul hmle hAle
      _ = q ^ 2 := by ring
  refine ⟨{
    ambientDim := K
    messageDim_le := hkK
    ambientDim_le := by simpa using hKn
    order_lt_degree := by simpa only [D] using hdD
    interpolant := Q
    nonzero := hQ0
    weighted_degree_lt := by simpa only [D] using hQweight
    castsNeZero := hcast
    contact_budget_le := hcontact
    local_constraints := hQlocal
  }, rfl, hQtotal⟩

/-- Public named-parameter form of the prescribed weighted-support construction. -/
theorem exists_prescribed_weightedSupport_construction
    {δ : ℝ} {n k q : ℕ} [Fact q.Prime]
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * weightedSupportMultiplicity (capacityDerivativeOrder δ) ≤ n)
    (hnq : n ≤ q) (hA : agreementThreshold δ n k ≤ n) :
    let d := capacityDerivativeOrder δ
    let m := weightedSupportMultiplicity (capacityDerivativeOrder δ)
    let K := weightedSupportAmbientDimension δ n k
    ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := k) (A := agreementThreshold δ n k) d m domain received,
      construction.ambientDim = K ∧ jetTotalDegree construction.interpolant < 2 * m := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  have hdEq : capacityDerivativeOrder δ = d := by
    simpa only [d, xi] using capacityDerivativeOrder_eq_ceil hδmax
  have hmEq : weightedSupportMultiplicity (capacityDerivativeOrder δ) = m := by
    simp only [weightedSupportMultiplicity, hdEq, m, d]
  have hKEq :
      weightedSupportAmbientDimension δ n k = max k (Nat.floor (δ * n / 2)) := rfl
  rw [hmEq] at hblock
  rw [hmEq, hdEq, hKEq]
  apply exists_prescribed_weightedSupport_construction_core domain received hδ hδmax hk
  · simpa only [m, d] using hblock
  · exact hnq
  · exact hA

/-- A weighted-support construction with its total-jet bound gives the sharp extension-field
root count. The natural subtraction in the field budget is the exact separant-degree budget. -/
theorem HiddenDerivativeInterpolationCertificate.agreeingPolynomials_encard_le_totalJetDegree
    {n q k A d m K e : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received)
    (hK : construction.ambientDim = K) (he : 0 < e)
    (htotal : jetTotalDegree construction.interpolant < 2 * m)
    (hlarge : 2 * (m * A + d - K) ≤ q ^ e) :
    (agreeingPolynomials domain k A received).encard ≤
      (4 * m * q ^ (e * d) : ℕ) := by
  have hbinom : ∀ a s, 0 < a → a + s ≤ construction.ambientDim - 1 →
      ((a + s).choose s : ZMod q) ≠ 0 := by
    intro a s ha has
    have hchar : construction.ambientDim - 1 < ringChar (ZMod q) := by
      rw [ringChar.eq (ZMod q) q]
      exact construction.below_characteristic.1
    exact PolynomialDifferential.natCast_choose_ne_zero_of_ringChar
      (F := ZMod q) (D := construction.ambientDim - 1) (s := s)
      (Or.inr hchar) a ha has
  have hdegreeEq : construction.ambientDim - 1 = K - 1 := by omega
  have hweight : differentialWeightedDegree (construction.ambientDim - 1)
      construction.interpolant - (construction.ambientDim - 1 - d) ≤ m * A + d - K := by
    have hdegree := construction.weighted_degree_lt
    rw [hdegreeEq] at hdegree ⊢
    omega
  have hlarge' : 2 * (m * A + d - K) ≤ Nat.card (ZMod q) ^ e := by
    simpa only [Nat.card_zmod] using hlarge
  have hroots : Nat.card (BoundedSolution construction.interpolant
      (construction.ambientDim - 1)) ≤ 4 * m * q ^ (e * d) := by
    have hr := BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul_extension
      construction.nonzero construction.castsNeZero hbinom hweight he hlarge'
    calc
      Nat.card (BoundedSolution construction.interpolant (construction.ambientDim - 1)) ≤
          2 * jetTotalDegree construction.interpolant *
            Nat.card (ZMod q) ^ (e * d) := hr
      _ ≤ 2 * (2 * m) * Nat.card (ZMod q) ^ (e * d) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 htotal.le)
      _ = 4 * m * Nat.card (ZMod q) ^ (e * d) := by ring
      _ = 4 * m * q ^ (e * d) := by simp only [Nat.card_zmod]
  calc
    (agreeingPolynomials domain k A received).encard
        ≤ ENat.card (BoundedSolution construction.interpolant
          (construction.ambientDim - 1)) :=
      ENat.card_le_card_of_injective construction.solutionEmbedding.injective
    _ = (Nat.card (BoundedSolution construction.interpolant
        (construction.ambientDim - 1)) : ℕ∞) := ENat.card_eq_coe_natCard _
    _ ≤ (4 * m * q ^ (e * d) : ℕ) := by
      exact_mod_cast hroots

end
end ReedSolomon
