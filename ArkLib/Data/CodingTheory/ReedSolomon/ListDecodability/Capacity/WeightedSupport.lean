/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupportInterpolant
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Radius


/-!
# Prescribed weighted-support capacity bounds

The no-band weighted support supplies the actual hidden-derivative construction and the two
finite-field root bounds. Both bounds apply to the same canonical exact list.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open HiddenDerivative
open HiddenDerivative.WeightedSupportParameters
open ListDecoding Polynomial
open SimplexIntegration

/-- The prescribed weighted-support multiplicity is positive throughout the small-gap range. -/
theorem weightedSupportMultiplicity_pos {δ : ℝ} (hδ : 0 < δ)
    (hδmax : δ < (1 / 4 : ℝ)) : 0 < weightedSupportMultiplicity δ := by
  rw [weightedSupportMultiplicity, capacityDerivativeOrder_eq_ceil hδmax]
  rw [harmonicNumber_eq_harmonic]
  apply Nat.ceil_pos.mpr
  have ho := prescribed_order_lower δ hδ hδmax.le
  have hH : 0 < (harmonic (Nat.ceil (Real.exp (xi / δ)) - 1) : ℝ) :=
    (div_pos xi_pos hδ).trans_le ho.2.2
  have hd : 0 < Nat.ceil (Real.exp (xi / δ)) := by omega
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (Nat.cast_pos.mpr hd)))
    (by simpa only [xi] using hH)

/-- The prescribed weighted support realizes the public construction contract. -/
theorem exists_weightedSupport_hiddenDerivativeConstruction :
    WeightedSupportConstruction := by
  intro δ hδ hδmax n k q hblock hk _hkn hq hnq hA domain received
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨construction, hK, _htotal⟩ :=
    exists_prescribed_weightedSupport_construction domain received hδ hδmax hk hblock hnq hA
  exact ⟨construction, hK⟩

/-- Every prescribed small-gap instance has both finite-field bounds. The exponent-two bound
requires no extra field hypothesis; the exponent-one refinement uses the exact separant budget. -/
theorem weightedSupport_capacity_list_bound_four_mul
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ < (1 / 4 : ℝ)) :
    ∀ n k q : ℕ, 8 * weightedSupportMultiplicity δ ≤ n →
      0 < k → k ≤ n → q.Prime → n ≤ q →
      ∀ domain : Fin n ↪ ZMod q,
        Nonempty (CapacityGapCertificate δ domain k
          (4 * weightedSupportMultiplicity δ * q ^ (2 * capacityDerivativeOrder δ))) ∧
        (LargeFieldCondition δ n k q (capacityDerivativeOrder δ)
          (weightedSupportMultiplicity δ) →
          Nonempty (CapacityGapCertificate δ domain k
            (4 * weightedSupportMultiplicity δ * q ^ capacityDerivativeOrder δ))) := by
  intro n k q hblock hk hkn hq hnq domain
  let : Fact q.Prime := ⟨hq⟩
  let d := capacityDerivativeOrder δ
  let m := weightedSupportMultiplicity δ
  let K := weightedSupportAmbientDimension δ n k
  let A := agreementThreshold δ n k
  have hn : 0 < n := hk.trans_le hkn
  have pointwise (e : ℕ) (he : 0 < e)
      (hfield : 2 * (m * A + d - K) ≤ q ^ e) :
      ∀ received : Fin n → ZMod q,
        (agreeingPolynomials domain k A received).encard ≤
          (4 * m * q ^ (e * d) : ℕ) := by
    intro received
    by_cases hA : A ≤ n
    · obtain ⟨construction, hK, htotal⟩ :=
        exists_prescribed_weightedSupport_construction domain received hδ hδmax hk
          (by simpa only [m] using hblock) hnq (by simpa only [A] using hA)
      exact construction.agreeingPolynomials_encard_le_totalJetDegree hK he htotal hfield
    · rw [agreeingPolynomials_eq_empty_of_card_lt
        (by simpa only [A, Fintype.card_fin] using Nat.lt_of_not_ge hA) received]
      simp
  have pointwiseTwo : ∀ received : Fin n → ZMod q,
      (agreeingPolynomials domain k A received).encard ≤
        (4 * m * q ^ (2 * d) : ℕ) := by
    intro received
    by_cases hAfeasible : A ≤ n
    · obtain ⟨construction, hK, htotal⟩ :=
        exists_prescribed_weightedSupport_construction domain received hδ hδmax hk
          (by simpa only [m] using hblock) hnq (by simpa only [A] using hAfeasible)
      have hdK : d < K := by
        have := construction.order_lt_degree
        rw [hK] at this
        omega
      have hfieldTwo : 2 * (m * A + d - K) ≤ q ^ 2 := by
        have hsub : m * A + d - K ≤ m * A := by omega
        calc
          2 * (m * A + d - K) ≤ 2 * (m * A) := Nat.mul_le_mul_left 2 hsub
          _ ≤ 8 * (m * A) := Nat.mul_le_mul_right (m * A) (by omega)
          _ = (8 * m) * A := by ring
          _ ≤ n * n := Nat.mul_le_mul hblock hAfeasible
          _ ≤ q * q := Nat.mul_le_mul hnq hnq
          _ = q ^ 2 := by ring
      simpa only [Nat.mul_assoc] using
        construction.agreeingPolynomials_encard_le_totalJetDegree hK
          (e := 2) (by decide) htotal hfieldTwo
    · rw [agreeingPolynomials_eq_empty_of_card_lt
        (by simpa only [A, Fintype.card_fin] using Nat.lt_of_not_ge hAfeasible) received]
      simp
  constructor
  · exact ⟨CapacityGapCertificate.ofPointwiseBound hδ.le hn domain
      (by simpa only [d, m] using pointwiseTwo)⟩
  · intro hlarge
    have hlarge' : 2 * (m * A + d - K) ≤ q ^ 1 := by
      simpa only [LargeFieldCondition, d, m, K, A, pow_one] using hlarge
    exact ⟨CapacityGapCertificate.ofPointwiseBound hδ.le hn domain
      (by
        simpa only [d, m, pow_one, one_mul] using
          pointwise 1 (by decide) hlarge')⟩

/-- The finite-field conclusions packaged in the public weighted-support contract. -/
theorem weightedSupport_capacity_list_bound : WeightedSupportListBound := by
  intro δ hδ hδmax
  have hm := weightedSupportMultiplicity_pos hδ hδmax
  exact ⟨hm, 4 * weightedSupportMultiplicity δ, by positivity,
    weightedSupport_capacity_list_bound_four_mul δ hδ hδmax⟩

end
end ReedSolomon
