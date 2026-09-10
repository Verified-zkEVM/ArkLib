/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.RegularCounting
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
/-! # Characteristic contracts and final numerical geometric-list constants -/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

/-- Characteristic zero or characteristic at least the Taylor cutoff makes every
required binomial pivot nonzero, simultaneously for all differential orders. -/
theorem binomial_pivots_of_characteristic {F : Type*} [Field F] {K : ℕ}
    (hchar : ringChar F = 0 ∨ K ≤ ringChar F) :
    ∀ r i, r < i → i < K → (i.choose r : F) ≠ 0 := by
  intro r i hri hi
  rcases hchar with hzero | hpos
  · have : CharP F 0 := hzero ▸ inferInstanceAs (CharP F (ringChar F))
    have : CharZero F := CharP.charP_to_charZero F
    exact_mod_cast Nat.choose_ne_zero hri.le
  · exact Polynomial.natCast_choose_ne_zero_of_lt_ringChar (hi.trans_le hpos) hri.le

/-- The exact rational geometric ratio is bounded by the manuscript's simpler
real ratio whenever agreement exceeds the message dimension by delta*n. -/
theorem geometric_ratio_le {n k A K ν : ℕ} {δ : ℝ}
    (hn : 0 < n) (hν : 0 < ν) (hδ : 0 < δ) (hK : K ≤ n) (hkA : k ≤ A)
    (hgap : (k : ℝ) + δ * n ≤ A) :
    ((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) / ((A - k + 1 : ℕ) : ℝ) ≤
      (2 * ν / δ) * n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hνR : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hKR : (K : ℝ) ≤ n := by exact_mod_cast hK
  have hb : ((1 + 2 * K * (ν - 1) : ℕ) : ℝ) ≤ 2 * ν * n := by
    push_cast
    rw [Nat.cast_sub hν]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_right hKR (show 0 ≤ (ν : ℝ) - 1 by linarith)
    norm_num only [Nat.cast_one, Nat.cast_ofNat]
    nlinarith
  have ha : δ * n ≤ ((A - k + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hkA]
    push_cast
    linarith
  have ha0 : (0 : ℝ) < ((A - k + 1 : ℕ) : ℝ) := by positivity
  have hd : 0 < δ * n := mul_pos hδ hnR
  calc
    ((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) / ((A - k + 1 : ℕ) : ℝ) ≤
        ((n : ℝ) * (2 * ν * n)) / (δ * n) := by
      apply div_le_div₀ (by positivity)
      · simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hb hnR.le
      · exact hd
      · exact ha
    _ = (2 * ν / δ) * n := by field_simp

/-- The squared-degree geometric count implies exactly the stated manuscript
constant after bounding the Taylor cutoff by the block length. -/
theorem geometric_count_le_manuscript_bound {n k A K ν m d L : ℕ} {δ : ℝ}
    (hn : 0 < n) (hν : 0 < ν) (hνm : ν ≤ 2 * m) (hδ : 0 < δ)
    (hK : K ≤ n) (hkA : k ≤ A) (hgap : (k : ℝ) + δ * n ≤ A)
    (hcount : (L : ℚ) ≤ (ν : ℚ) ^ 2 *
      (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) :
    (L : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d := by
  have hcountR : (L : ℝ) ≤ (ν : ℝ) ^ 2 *
      (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) /
        ((A - k + 1 : ℕ) : ℝ)) ^ d := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hcount
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_div] using hc
  have hratio := geometric_ratio_le hn hν hδ hK hkA hgap
  have hνmR : (ν : ℝ) ≤ 2 * m := by exact_mod_cast hνm
  have hratio' : ((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) /
      ((A - k + 1 : ℕ) : ℝ) ≤ (4 * m / δ) * n := by
    apply hratio.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
    apply (div_le_div_iff_of_pos_right hδ).mpr
    linarith
  calc
    (L : ℝ) ≤ (ν : ℝ) ^ 2 *
        (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) /
          ((A - k + 1 : ℕ) : ℝ)) ^ d := hcountR
    _ ≤ (2 * (m : ℝ)) ^ 2 * ((4 * m / δ) * n) ^ d := by
      gcongr
    _ = 4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d := by
      rw [mul_pow]
      ring

end ReedSolomon.HiddenDerivative
