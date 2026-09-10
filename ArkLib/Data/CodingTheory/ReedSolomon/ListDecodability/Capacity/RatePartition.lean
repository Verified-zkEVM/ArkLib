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
/-- The finite rate choice bounds the complete close list, including the zero polynomial. -/
theorem ratePartition_close_list_bound {F : Type u} [Field F]
    {R a : ℝ} {d n k A : ℕ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hn : ratePartitionLength R d p.multiplicity ≤ n)
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
          (2 * ratePartitionJetBound R p.multiplicity / (a - R)) ^ d * n ^ d := by
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_length_guards hR (hRa.trans haone) hn hkR haA
  obtain ⟨cert⟩ := exists_ratePartitionRate_certificate p hR (hRa.trans haone)
    (hR.trans hRa) hd hn hkR haA hAn domain (fun i ↦ Polynomial.C (received i))
    (fun _ ↦ by simp)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := hkR.trans
      ((mul_le_mul_of_nonneg_right hRa.le (Nat.cast_nonneg n)).trans haA)
    exact_mod_cast h
  have hν : 0 < ratePartitionJetBound R p.multiplicity := by
    apply Nat.lt_ceil.mpr
    have hm : (0 : ℝ) < p.multiplicity := by exact_mod_cast p.multiplicity_pos
    simpa only [Nat.cast_zero] using (show (0 : ℝ) < 2 * p.multiplicity / R by positivity)
  have hchar' : ringChar F = 0 ∨
      max (⌊R * n⌋₊ + 1 - 1) (ratePartitionJetBound R p.multiplicity) < ringChar F := by
    apply hchar.imp_right
    intro hc
    apply (max_lt (by omega) hνn).trans_le hc
  apply close_list_bound_of_curve_certificate_of_jetCharacteristic domain received cert hk
    (hkD.trans (Nat.le_succ _)) (by omega) hDn hkA hAn hν (sub_pos.mpr hRa) ?_ hchar'
  nlinarith

open Classical in
/-- Any bare strict partition gate chooses all list constants before the field and code. -/
theorem exists_ratePartition_list_bound {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hgate : 1 < ratePartitionGamma R a d) :
    ∃ p : RatePartitionFiniteParameters R a d,
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      ratePartitionLength R d p.multiplicity ≤ n → 0 < k →
      (k : ℝ) ≤ R * n → a * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      (ringChar F = 0 ∨ n ≤ ringChar F) →
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
            (2 * ratePartitionJetBound R p.multiplicity / (a - R)) ^ d * n ^ d := by
  obtain ⟨p⟩ := exists_ratePartitionFiniteParameters hR (hR.trans hRa) (by omega) hgate
  exact ⟨p, fun _ _ _ _ _ hn hk hkR haA hAn domain received hchar ↦
    ratePartition_close_list_bound p hR hRa haone hd hn hk hkR haA hAn domain received hchar⟩

end ReedSolomon
