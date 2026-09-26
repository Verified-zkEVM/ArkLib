/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupport
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.QuarterGap

/-!
# Explicit finite-field capacity list bounds

This module combines the large-gap agreement estimates and the weighted-support estimates into
an explicit finite-field bound for prime-field Reed–Solomon agreement lists.

## Main statements

* `exists_field_bounded_capacity_list`: an exact agreement list with the large-gap and
  weighted-support size bounds at every fixed positive gap.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open ListDecoding Polynomial

noncomputable section

/-- A finite set of agreeing messages gives an exact finset of their polynomial values. -/
private theorem exists_finset_polynomial_list {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] (domain : index ↪ F) (k A : ℕ)
    (received : index → F) (hfinite : (agreeingPolynomials domain k A received).Finite) :
    ∃ list : Finset (Polynomial F),
      (∀ P, P ∈ list ↔ P.degree < k ∧
        A ≤ Code.agree (ReedSolomon.evalOnPoints domain P) received) ∧
      (list.card : ℕ∞) = (agreeingPolynomials domain k A received).encard := by
  classical
  refine ⟨hfinite.toFinset.map (messagePolynomialValue k), ?_, ?_⟩
  · intro P
    simp only [Finset.mem_map, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Polynomial.mem_degreeLT.mp p.property, hp⟩
    · rintro ⟨hdegree, hagree⟩
      exact ⟨⟨P, Polynomial.mem_degreeLT.mpr hdegree⟩, hagree, rfl⟩
  · rw [Finset.card_map, hfinite.encard_eq_coe_toFinset_card]

/-- At every fixed positive capacity gap, prime-field Reed–Solomon codes have uniformly bounded
exact agreement lists with the large-gap and weighted-support estimates. The constants depend only
on `delta`. -/
theorem exists_field_bounded_capacity_list
    (delta : ℝ) (hdelta : 0 < delta) :
    let d : ℕ := capacityDerivativeOrder delta
    let m : ℕ := weightedSupportMultiplicity d
    let N : ℕ := if (1 / 4 : ℝ) ≤ delta then 1 else 8 * m
    ∀ n k q A : ℕ, N ≤ n → 0 < k → k ≤ n → q.Prime → n ≤ q →
        (k : ℝ) + delta * n ≤ A →
        ∀ (alpha : Fin n ↪ ZMod q) (y : Fin n → ZMod q),
          ∃ list : Finset (Polynomial (ZMod q)),
            (∀ P : Polynomial (ZMod q), P ∈ list ↔
              P.degree < k ∧ A ≤ Code.agree (fun i => P.eval (alpha i)) y) ∧
            (n < A → list = ∅) ∧
            ((1 / 2 : ℝ) ≤ delta → list.card ≤ 1) ∧
            ((1 / 4 : ℝ) ≤ delta → list.card < n) ∧
            (delta < (1 / 4 : ℝ) →
              list.card ≤ 4 * m * q ^ (2 * d) ∧
              (2 * (m * A + d - max k ⌊delta * (n : ℝ) / 2⌋₊) ≤ q →
                list.card ≤ 4 * m * q ^ d)) := by
  classical
  let d := capacityDerivativeOrder delta
  let m := weightedSupportMultiplicity d
  change ∀ n k q A : ℕ,
    (if (1 / 4 : ℝ) ≤ delta then 1 else 8 * m) ≤ n → _
  intro n k q A hn hk hkn hq hnq hA alpha y
  let : Fact q.Prime := ⟨hq⟩
  have hthreshold := (capacityAgreementThreshold_le_iff_real hdelta.le n k A).mpr hA
  have hsubset : agreeingPolynomials alpha k A y ⊆
      agreeingPolynomials alpha k (capacityAgreementThreshold delta n k) y := by
    intro P hP
    change A ≤ Code.agree (ReedSolomon.evalOnPoints alpha P) y at hP
    change capacityAgreementThreshold delta n k ≤ Code.agree (ReedSolomon.evalOnPoints alpha P) y
    exact hthreshold.trans hP
  have hmono := Set.encard_mono hsubset
  have listEmptyOfOversizedThreshold (list : Finset (Polynomial (ZMod q)))
      (hexact : ∀ P : Polynomial (ZMod q), P ∈ list ↔
        P.degree < k ∧ A ≤ Code.agree (fun i => P.eval (alpha i)) y)
      (hoversized : n < A) : list = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    have h := (hexact P).mp hP
    have hAgree := Code.agree_le_card (u := ReedSolomon.evalOnPoints alpha P) (v := y)
    simp only [Fintype.card_fin] at hAgree
    exact (Nat.not_le_of_lt hoversized) (h.2.trans hAgree)
  by_cases hquarter : (1 / 4 : ℝ) ≤ delta
  · have hquarterBound := agreeingPolynomials_encard_lt_blockLength_of_quarter
      hquarter alpha hk (by simpa only [Fintype.card_fin] using hkn) y
    have hquarterBound' :
        (agreeingPolynomials alpha k (capacityAgreementThreshold delta n k) y).encard < n := by
      simpa only [Fintype.card_fin] using hquarterBound
    have hbound := hmono.trans_lt hquarterBound'
    obtain ⟨list, hexact, hcard⟩ := exists_finset_polynomial_list alpha k A y
      (Set.finite_of_encard_le_coe hbound.le)
    refine ⟨list, hexact, ?_, ?_, ?_, ?_⟩
    · exact listEmptyOfOversizedThreshold list hexact
    · intro hhalf
      have hhalfBound := agreeingPolynomials_encard_le_one_of_half
        hhalf alpha hk (by simpa only [Fintype.card_fin] using hkn) y
      have hhalfBound' :
          (agreeingPolynomials alpha k (capacityAgreementThreshold delta n k) y).encard ≤ 1 := by
        simpa only [Fintype.card_fin] using hhalfBound
      have h := hmono.trans hhalfBound'
      rw [← hcard] at h
      exact_mod_cast h
    · intro _hquarter
      exact_mod_cast hcard.le.trans_lt hbound
    · intro hsmall
      exact (not_lt_of_ge hquarter hsmall).elim
  · have hsmall : delta < (1 / 4 : ℝ) := lt_of_not_ge hquarter
    have hbound := weightedSupport_capacity_list_bound_four_mul delta hdelta hsmall
    have hblock : 8 * weightedSupportMultiplicity (capacityDerivativeOrder delta) ≤ n := by
      simpa only [ite_eq_right hquarter] using hn
    obtain ⟨⟨certificate⟩, hlarge⟩ := hbound n k q hblock hk hkn hq hnq alpha
    have hcertificateBound := (certificate.pointwiseListBound y).1
    have hcertificateBound' :
        (agreeingPolynomials alpha k (capacityAgreementThreshold delta n k) y).encard ≤
          ((4 * m * q ^ (2 * d) : ℕ) : ℕ∞) := by
      simpa only [Fintype.card_fin, d, m] using hcertificateBound
    have hbound' := hmono.trans hcertificateBound'
    obtain ⟨list, hexact, hcard⟩ := exists_finset_polynomial_list alpha k A y
      (Set.finite_of_encard_le_coe hbound')
    refine ⟨list, hexact, ?_, ?_, ?_, ?_⟩
    · exact listEmptyOfOversizedThreshold list hexact
    · intro hhalf
      linarith
    · intro hquarter'
      exact (hquarter hquarter').elim
    · intro _hsmall
      refine ⟨?_, ?_⟩
      · change list.card ≤ 4 * m * q ^ (2 * d)
        exact_mod_cast hcard.le.trans hbound'
      · intro hfield
        have hbudget : LargeFieldCondition delta n k q d m := by
          apply le_trans _ hfield
          exact Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right
            (Nat.add_le_add_right (Nat.mul_le_mul_left m hthreshold) d) _)
        obtain ⟨largeCertificate⟩ := hlarge hbudget
        change list.card ≤ 4 * m * q ^ d
        have hlargeCertificateBound := (largeCertificate.pointwiseListBound y).1
        have hlargeCertificateBound' :
            (agreeingPolynomials alpha k (capacityAgreementThreshold delta n k) y).encard ≤
              ((4 * m * q ^ d : ℕ) : ℕ∞) := by
          simpa only [Fintype.card_fin, d, m] using hlargeCertificateBound
        exact_mod_cast hcard.le.trans (hmono.trans hlargeCertificateBound')

end
end ReedSolomon
