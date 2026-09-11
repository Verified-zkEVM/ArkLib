/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter

/-! # Rate-dependent list decoding above the partition gate -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- The finite rate choice bounds the complete close list, including the zero polynomial. The
interpolation dimension is separate from the reconstruction dimension `max k (d + 1)`. -/
theorem ratePartition_close_list_bound {F : Type u} [Field F]
    {R a : ℝ} {d n k A : ℕ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hn : ratePartitionMathematicalLength R d p.multiplicity ≤ n)
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
          (2 * ratePartitionJetBound R p.multiplicity / (a - R)) ^ d * n ^ d := by
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_mathematical_length_guards hR (hRa.trans haone) (by omega) hn hkR haA
  obtain ⟨cert⟩ := exists_ratePartitionMathematical_certificate p hR (hRa.trans haone)
    (hR.trans hRa) hd hn hkR haA hAn domain (fun i ↦ Polynomial.C (received i))
    (fun _ ↦ by simp)
  let K := max k (d + 1)
  have hkK : k ≤ K := Nat.le_max_left _ _
  have hdK : d < K := lt_of_lt_of_le (Nat.lt_succ_self d) (Nat.le_max_right _ _)
  have hKn : K ≤ n := by
    apply max_le
    · exact hkD.trans (by omega)
    · omega
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := hkR.trans
      ((mul_le_mul_of_nonneg_right hRa.le (Nat.cast_nonneg n)).trans haA)
    exact_mod_cast h
  have hν : 0 < ratePartitionJetBound R p.multiplicity := by
    apply Nat.lt_ceil.mpr
    have hm : (0 : ℝ) < p.multiplicity := by exact_mod_cast p.multiplicity_pos
    simpa only [Nat.cast_zero] using (show (0 : ℝ) < 2 * p.multiplicity / R by positivity)
  have hKsub : K - 1 ≤ max (k - 1) d := by
    rcases le_total k (d + 1) with hkd | hdk
    · rw [show K = d + 1 by simp [K, max_eq_right hkd]]
      exact Nat.le_max_right _ _
    · rw [show K = k by simp [K, max_eq_left hdk]]
      exact Nat.le_max_left _ _
  have hchar' : ringChar F = 0 ∨
      max (K - 1) (ratePartitionJetBound R p.multiplicity) < ringChar F := by
    apply hchar.imp_right
    intro hc
    exact (max_le_max hKsub le_rfl).trans_lt hc
  apply close_list_bound_of_curve_certificate_of_jetCharacteristic domain received cert hk
    hkK hdK hKn hkA hAn hν (sub_pos.mpr hRa) ?_ hchar'
  nlinarith

open Classical in
/-- Any bare strict partition gate chooses all list constants before the field and code. -/
theorem exists_ratePartition_list_bound {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hgate : 1 < ratePartitionGamma R a d) :
    ∃ p : RatePartitionFiniteParameters R a d,
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      ratePartitionMathematicalLength R d p.multiplicity ≤ n → 0 < k →
      (k : ℝ) ≤ R * n → a * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      (ringChar F = 0 ∨
        max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
            (2 * ratePartitionJetBound R p.multiplicity / (a - R)) ^ d * n ^ d := by
  obtain ⟨p⟩ := exists_ratePartitionFiniteParameters hR (hR.trans hRa) (by omega) hgate
  exact ⟨p, fun _ _ _ _ _ hn hk hkR haA hAn domain received hchar ↦
    ratePartition_close_list_bound p hR hRa haone hd hn hk hkR haA hAn domain received hchar⟩

end ReedSolomon
