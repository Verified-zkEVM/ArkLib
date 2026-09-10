/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupport
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.QuarterGap


/-!
# Finite-field capacity list estimates

This module assembles the field-dependent list bounds and the large-gap cases.
The central property and the combined field-independent theorem are in
`ReedSolomon/ListDecodability/Capacity`.
-/

@[expose] public section

namespace ReedSolomon
open Polynomial
noncomputable section

/-- At every fixed positive capacity gap, all prime-field Reed-Solomon codes have uniformly
bounded exact agreement lists, with the prescribed small-gap parameters and both field regimes.

The constants depend only on `delta`. The degree inequality uses `Polynomial.degree`, so the
zero polynomial is included whenever it meets the agreement threshold. A threshold greater than
the block length gives the empty list. This theorem certifies no algorithmic running time. -/
theorem exists_field_bounded_capacity_list
    (delta : ℝ) (hdelta : 0 < delta) (_hOne : delta < 1) :
    let d : ℕ := if (1 / 4 : ℝ) ≤ delta then 0
      else Nat.ceil (Real.exp (((27 : ℝ) / 10) / delta))
    let m : ℕ := Nat.ceil (100 * (d : ℝ) ^ 2 *
      ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1))
    let N : ℕ := if (1 / 4 : ℝ) ≤ delta then 1 else 8 * m
    ∀ n k q A : ℕ, N ≤ n → 0 < k → k ≤ n → q.Prime → n ≤ q →
        (k : ℝ) + delta * n ≤ A → A ≤ 2 * n →
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
  let m := weightedSupportMultiplicity delta
  change ∀ n k q A : ℕ,
    (if (1 / 4 : ℝ) ≤ delta then 1 else 8 * m) ≤ n → _
  by_cases hquarter : (1 / 4 : ℝ) ≤ delta
  · intro n k q A _hn hk hkn hq hnq hA _hAupper alpha y
    let : Fact q.Prime := ⟨hq⟩
    have hthreshold := (agreementThreshold_le_iff_real hdelta.le n k A).mpr hA
    have hmono := Set.encard_mono
      (agreeingPolynomials_antitone alpha k y hthreshold)
    have hbound := hmono.trans_lt (agreeingPolynomials_encard_lt_blockLength_of_quarter
      hquarter alpha (hk.trans_le hkn) hk hkn y)
    obtain ⟨list, hexact, hcard⟩ := exists_finset_polynomial_list alpha k A y
      (Set.finite_of_encard_le_coe hbound.le)
    refine ⟨list, hexact, ?_, ?_, ?_, ?_⟩
    · intro hoversized
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro P hP
      have h := (hexact P).mp hP
      have := Code.agree_le_card (u := ReedSolomon.evalOnPoints alpha P) (v := y)
      simp only [Fintype.card_fin] at this
      omega
    · intro hhalf
      have h := hmono.trans (agreeingPolynomials_encard_le_one_of_half
        hhalf alpha hk hkn y)
      rw [← hcard] at h
      exact_mod_cast h
    · intro _hquarter
      exact_mod_cast hcard.le.trans_lt hbound
    · intro hsmall
      exact (not_lt_of_ge hquarter hsmall).elim
  · have hsmall : delta < (1 / 4 : ℝ) := lt_of_not_ge hquarter
    have hbound := weightedSupport_capacity_list_bound_four_mul delta hdelta hsmall
    intro n k q A hn hk hkn hq hnq hA _hAupper alpha y
    have hblock : 8 * weightedSupportMultiplicity delta ≤ n := by
      simpa only [if_neg hquarter] using hn
    obtain ⟨⟨certificate⟩, hlarge⟩ := hbound n k q hblock hk hkn hq hnq alpha
    have hthreshold := (agreementThreshold_le_iff_real hdelta.le n k A).mpr hA
    have hmono := Set.encard_mono
      (agreeingPolynomials_antitone alpha k y hthreshold)
    have hbound' := hmono.trans (certificate.pointwiseListBound y).1
    obtain ⟨list, hexact, hcard⟩ := exists_finset_polynomial_list alpha k A y
      (Set.finite_of_encard_le_coe hbound')
    refine ⟨list, hexact, ?_, ?_, ?_, ?_⟩
    · intro hoversized
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro P hP
      have h := (hexact P).mp hP
      have := Code.agree_le_card (u := ReedSolomon.evalOnPoints alpha P) (v := y)
      simp only [Fintype.card_fin] at this
      omega
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
        exact_mod_cast hcard.le.trans (hmono.trans (largeCertificate.pointwiseListBound y).1)


end
end ReedSolomon
