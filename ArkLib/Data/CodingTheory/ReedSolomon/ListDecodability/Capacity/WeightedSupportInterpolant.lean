/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Certificates
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Soundness
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Margin
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Harmonic
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Block
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.SolutionEmbedding
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.HiddenDerivativeBound
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.TotalDegreeExtension


/-!
# Construction and finite-field root bounds from weighted support

The symbolic primitive-kernel construction is specialized at challenge zero. Its no-bad-challenge
property supplies nonzeroness, while coefficient specialization preserves the actual weighted
support and every local constraint. Thus one canonical kernel supplies both the geometric and
finite-field list arguments.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

noncomputable section

open HiddenDerivative ListDecoding Polynomial
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.WeightedSupportParameters
open SimplexIntegration

set_option maxHeartbeats 800000 in
-- Elaborating the symbolic matrix witness crosses the full weighted-support rank construction.
/-- Specializing the canonical symbolic kernel gives an actual weighted-support interpolant.
The returned strict degree bounds are exactly those used by the decoder root count. -/
theorem exists_weightedSupport_interpolant_of_fixed_margin
    {F : Type*} [Field F] {n D d m W A : ℕ} {g : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hD : 0 < D) (hm : 0 < m) (hA : 0 < A) (hg : g ≤ 1)
    (hcut : (D : ℝ) * m * (1 + g) ≤ (m * A : ℕ))
    (hmargin : (543 / 500 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := (D : ℝ) * m * (1 + g)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W
        ((D : ℝ) * m * (1 + g)) hD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
      Q ∈ weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g)) hD ∧
      (∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q) ∧
      jetTotalDegree Q < 2 * m ∧
      differentialWeightedDegree D Q < m * A := by
  let ν := 2 * m - 1
  have hν : 0 < ν := by dsimp only [ν]; omega
  have hy₀ : ∀ u, WeightedSupportEligible D d W
      ((D : ℝ) * m * (1 + g)) u → u (some 0) ≤ ν := by
    intro u hu
    exact SymbolicWeightedSupportInterpolation.y₀_le_two_mul_sub_one_of_eligible
      hD hg hm hu
  obtain ⟨v, _hv, _hkernel, _hvdegree, _hvheight, _hprimitive, hnozero,
      hconstraints, hsupport⟩ :=
    SymbolicWeightedSupportInterpolation.exists_symbolic_weightedSupport_interpolant_of_fixed_margin
      hD hν (fun i ↦ domain i) received (fun _ ↦ 0) hy₀ hmargin
  let columns := SymbolicWeightedSupportInterpolation.weightedSupportColumns
    (d := d) (W := W) (L := (D : ℝ) * m * (1 + g)) hD
  let φ : F[X] →+* F := Polynomial.eval₂RingHom (RingHom.id F) 0
  let Q : DifferentialPolynomial F d := MvPolynomial.map φ (interpolant columns v)
  have hQ0 : Q ≠ 0 := by
    simpa only [Q, φ] using hnozero (RingHom.id F) 0
  have hQsupport :
      Q ∈ weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g)) hD := by
    simpa only [Q, φ, columns] using
      map_interpolant_mem_weightedSupportSpace hD columns hsupport v (RingHom.id F) 0
  have hQlocal : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q := by
    intro i
    have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (domain i))
      (receivedLine (received i) 0) (interpolant columns v) (hconstraints i)
    change SatisfiesLocalConstraints m
      (φ (Polynomial.C (domain i))) (φ (receivedLine (received i) 0)) Q at hi
    convert hi using 1 <;> simp [φ, receivedLine]
  have hdecoder := decoder_bounds_of_mem_weightedSupportSpace hm hA
    (by
      have hnonneg : (0 : ℝ) ≤ (D : ℝ) * m := by positivity
      calc
        (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * m * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hnonneg
        _ = (D : ℝ) * (2 * m) := by ring)
    hcut hQsupport
  exact ⟨Q, hQ0, hQsupport, hQlocal, hdecoder.1, hdecoder.2⟩

set_option maxHeartbeats 800000 in
-- The prescribed margin expands the continuous simplex and symbolic kernel constructions.
/-- The explicit prescribed weighted-support parameters give a genuine hidden-derivative
construction. The original message dimension remains the input parameter. -/
theorem exists_prescribed_weightedSupport_construction_core
    {δ : ℝ} {n k q : ℕ} [Fact q.Prime]
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H := harmonicPowerSum (d - 1) 1
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hnq : n ≤ q) (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H := harmonicPowerSum (d - 1) 1
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let K := max k (Nat.floor (δ * n / 2))
    ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := k) (A := agreementThreshold δ n k) d m domain received,
      construction.ambientDim = K ∧ jetTotalDegree construction.interpolant < 2 * m := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let H := harmonicPowerSum (d - 1) 1
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let K := max k (Nat.floor (δ * n / 2))
  let D := K - 1
  let A := agreementThreshold δ n k
  let g := rateGap δ ((D : ℝ) / n)
  let W := Nat.floor ((1 + theta * g) * d * m / H)
  have hblock' : 8 * m ≤ n := by simpa only [m, H, d] using hblock
  have hb := prescribedBlockBounds δ n k hδ hδmax hk
    (by simpa only [H, harmonicPowerSum_one, harmonicNumber_eq_harmonic] using hblock) hA
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
    simpa only [H, d, harmonicPowerSum_one] using ho.2.2
  obtain ⟨hmpos, _hWpos, _hmean, _hradius, _hfloor⟩ :=
    prescribed_dimension_inputs δ ((D : ℝ) / n) H d hδ hδmax.le hρ hρhi
      (by simpa only [d] using ho.1) hHlo
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
      (show 0 < A from hk.trans_le (Nat.le_add_right _ _)) (clippedGap_mem_unit δ _ hδ hρ).2
      hcut hmargin'
  have hkK : k ≤ K := by
    dsimp only [K]
    exact Nat.le_max_left _ _
  have hDchar : D < ringChar (ZMod q) := by
    rw [ringChar.eq (ZMod q) q]
    have hDK : D < K := by dsimp only [D]; omega
    exact hDK.trans_le (hKn.trans hnq)
  have hmchar : 2 * m < ringChar (ZMod q) := by
    rw [ringChar.eq (ZMod q) q]
    have : 2 * m < 8 * m := by omega
    exact this.trans_le (hblock'.trans hnq)
  have hchar : IsBelowCharacteristic D Q :=
    ⟨hDchar, fun j ↦ ((jetDegree_le_total Q j).trans_lt hQtotal).trans hmchar⟩
  have hcontact : m * A ≤ q ^ 2 := by
    have hmle : m ≤ q := (by omega : m ≤ n).trans hnq
    have hAle : A ≤ q := hA.trans hnq
    calc
      m * A ≤ q * q := Nat.mul_le_mul hmle hAle
      _ = q ^ 2 := by ring
  refine ⟨{
    ambientDim := K
    messageDim_le := hkK
    ambientDim_le := hKn
    order_lt_degree := by simpa only [D] using hdD
    interpolant := Q
    nonzero := hQ0
    weighted_degree_lt := by simpa only [D] using hQweight
    below_characteristic := by simpa only [D] using hchar
    contact_budget_le := hcontact
    local_constraints := hQlocal
  }, rfl, hQtotal⟩

/-- Public named-parameter form of the prescribed weighted-support construction. -/
theorem exists_prescribed_weightedSupport_construction
    {δ : ℝ} {n k q : ℕ} [Fact q.Prime]
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * weightedSupportMultiplicity δ ≤ n)
    (hnq : n ≤ q) (hA : agreementThreshold δ n k ≤ n) :
    let d := capacityDerivativeOrder δ
    let m := weightedSupportMultiplicity δ
    let K := weightedSupportAmbientDimension δ n k
    ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := k) (A := agreementThreshold δ n k) d m domain received,
      construction.ambientDim = K ∧ jetTotalDegree construction.interpolant < 2 * m := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicPowerSum (d - 1) 1)
  have hdEq : capacityDerivativeOrder δ = d := by
    simpa only [d, xi] using capacityDerivativeOrder_eq_ceil hδmax
  have hmEq : weightedSupportMultiplicity δ = m := by
    simp only [weightedSupportMultiplicity, hdEq, m, harmonicPowerSum_one,
      harmonicNumber_eq_harmonic, d]
  have hKEq :
      weightedSupportAmbientDimension δ n k = max k (Nat.floor (δ * n / 2)) := rfl
  rw [hmEq] at hblock
  rw [hdEq, hmEq, hKEq]
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
  have hamb : 1 ≤ construction.ambientDim := by
    have : 0 < construction.ambientDim - 1 :=
      (Nat.zero_le d).trans_lt construction.order_lt_degree
    omega
  have hDadd : construction.ambientDim - 1 + 1 = K := by
    rw [Nat.sub_add_cancel hamb, hK]
  have hroots : Nat.card (BoundedSolution construction.interpolant
      (construction.ambientDim - 1)) ≤ 2 * (2 * m) * q ^ (e * d) := by
    have hr := natCard_boundedSolution_le_extension_totalJetDegree_of_interpolation_degree
      construction.interpolant e (m * A) (2 * m) he construction.order_lt_degree.le
      construction.nonzero construction.below_characteristic construction.weighted_degree_lt
      htotal.le
      (by simpa only [hDadd, Nat.card_zmod] using hlarge)
    simpa only [Nat.card_zmod] using hr
  calc
    (agreeingPolynomials domain k A received).encard
        ≤ ENat.card (BoundedSolution construction.interpolant
          (construction.ambientDim - 1)) :=
      ENat.card_le_card_of_injective construction.solutionEmbedding.injective
    _ = (Nat.card (BoundedSolution construction.interpolant
        (construction.ambientDim - 1)) : ℕ∞) := ENat.card_eq_coe_natCard _
    _ ≤ (4 * m * q ^ (e * d) : ℕ) := by
      have heq : 2 * (2 * m) * q ^ (e * d) = 4 * m * q ^ (e * d) := by ring
      rw [← heq]
      exact_mod_cast hroots

end
end ReedSolomon
