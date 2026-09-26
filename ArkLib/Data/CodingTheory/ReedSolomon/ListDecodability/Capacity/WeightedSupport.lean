/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupportInterpolant

/-!
# Weighted-support capacity list bounds

For a positive gap below one quarter, the prescribed derivative order and multiplicity yield a
hidden-derivative interpolation certificate at every received word. The certificate gives the
finite-field list bound with exponent `2d`, and under a larger-field condition with exponent `d`.

## Main statements

* `exists_weightedSupport_hiddenDerivativeConstruction`: the prescribed parameters satisfy the
  weighted-support construction contract.
* `weightedSupport_capacity_list_bound_four_mul`: the pointwise list bounds with prefactor `4m`.
* `weightedSupport_capacity_list_bound`: the packaged weighted-support capacity bound.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open ListDecoding PolynomialDifferential

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
    ∀ n k q : ℕ, 8 * weightedSupportMultiplicity (capacityDerivativeOrder δ) ≤ n →
      0 < k → k ≤ n → q.Prime → n ≤ q →
      ∀ domain : Fin n ↪ ZMod q,
        Nonempty (CapacityGapCertificate δ domain k
          (4 * weightedSupportMultiplicity (capacityDerivativeOrder δ) *
            q ^ (2 * capacityDerivativeOrder δ))) ∧
        (LargeFieldCondition δ n k q (capacityDerivativeOrder δ)
          (weightedSupportMultiplicity (capacityDerivativeOrder δ)) →
          Nonempty (CapacityGapCertificate δ domain k
            (4 * weightedSupportMultiplicity (capacityDerivativeOrder δ) *
              q ^ capacityDerivativeOrder δ))) := by
  intro n k q hblock hk hkn hq hnq domain
  let : Fact q.Prime := ⟨hq⟩
  let d := capacityDerivativeOrder δ
  let m := weightedSupportMultiplicity d
  let K := weightedSupportAmbientDimension δ n k
  let A := capacityAgreementThreshold δ n k
  have hn : 0 < n := hk.trans_le hkn
  have emptyList (received : Fin n → ZMod q) (hAn : n < A) :
      agreeingPolynomials domain k A received = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    change A ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received at hp
    have hAgree : Code.agree (ReedSolomon.evalOnPoints domain p) received ≤ n := by
      simpa only [Fintype.card_fin] using
        Code.agree_le_card (u := ReedSolomon.evalOnPoints domain p) (v := received)
    exact (Nat.not_le_of_lt hAn) (hp.trans hAgree)
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
    · rw [emptyList received (Nat.lt_of_not_ge hA)]
      simp
  have pointwiseTwo : ∀ received : Fin n → ZMod q,
      (agreeingPolynomials domain k A received).encard ≤
        (4 * m * q ^ (2 * d) : ℕ) := by
    intro received
    by_cases hA : A ≤ n
    · obtain ⟨construction, hK, htotal⟩ :=
        exists_prescribed_weightedSupport_construction domain received hδ hδmax hk
          (by simpa only [m] using hblock) hnq (by simpa only [A] using hA)
      have hdK : d < K := by
        have hdegree := construction.order_lt_degree
        rw [hK] at hdegree
        omega
      have hfieldTwo : 2 * (m * A + d - K) ≤ q ^ 2 := by
        have hsub : m * A + d - K ≤ m * A := by omega
        calc
          2 * (m * A + d - K) ≤ 2 * (m * A) := Nat.mul_le_mul_left 2 hsub
          _ ≤ 8 * (m * A) := Nat.mul_le_mul_right (m * A) (by omega)
          _ = (8 * m) * A := by ring
          _ ≤ n * n := Nat.mul_le_mul hblock hA
          _ ≤ q * q := Nat.mul_le_mul hnq hnq
          _ = q ^ 2 := by ring
      simpa only [Nat.mul_assoc] using
        construction.agreeingPolynomials_encard_le_totalJetDegree hK
          (e := 2) (by decide) htotal hfieldTwo
    · rw [emptyList received (Nat.lt_of_not_ge hA)]
      simp
  constructor
  · exact ⟨CapacityGapCertificate.ofPointwiseBound hδ.le
      (by simpa only [Fintype.card_fin] using hn) (domain := domain)
      (by simpa only [d, m, A, Fintype.card_fin] using pointwiseTwo)⟩
  · intro hlarge
    have hlarge' : 2 * (m * A + d - K) ≤ q ^ 1 := by
      simpa only [LargeFieldCondition, capacityAgreementThreshold, d, m, K, A, pow_one] using hlarge
    exact ⟨CapacityGapCertificate.ofPointwiseBound hδ.le
      (by simpa only [Fintype.card_fin] using hn) (domain := domain)
      (by
        simpa only [d, m, A, Fintype.card_fin, pow_one, one_mul] using
          pointwise 1 (by decide) hlarge')⟩

/-- The finite-field conclusions packaged in the public weighted-support contract. -/
theorem weightedSupport_capacity_list_bound : WeightedSupportListBound := by
  intro δ hδ hδmax
  let d := capacityDerivativeOrder δ
  let m := weightedSupportMultiplicity d
  have hm : 0 < m :=
    (weightedSupportMultiplicity_pos_iff).2 (by
      have := (capacityDerivativeOrder_lower hδ hδmax).1
      dsimp only [d]
      omega)
  exact ⟨hm, 4 * m, by positivity,
    weightedSupport_capacity_list_bound_four_mul δ hδ hδmax⟩

end
end ReedSolomon
