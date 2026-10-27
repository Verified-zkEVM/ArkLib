/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Finite Johnson bounds for explicit legacy multiplicities

The exception budget of the ordinary Johnson certificate, including the factor two needed for
rounded curve heights and affine sampling, fits the seventh-power budget of BCIKS20 and BCGM25.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- A prescribed multiplicity bounds the rounded Johnson multiplicity as soon as it supplies
the required half-gap. -/
theorem johnsonT_le_of_half_gap {n D m : ℕ} {eta : ℝ}
    (hm : 3 ≤ m) (heta : 0 < eta)
    (hgap : Real.sqrt (johnsonRhoMinus n D) / (2 * (m : ℝ)) ≤ eta) :
    johnsonT n D eta ≤ (m : ℝ) + 1 / 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).mp hgap
  have hfrac : Real.sqrt (johnsonRhoMinus n D) / (2 * eta) ≤ (m : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hmul]
  have hceil : ⌈Real.sqrt (johnsonRhoMinus n D) / (2 * eta)⌉₊ ≤ m :=
    Nat.ceil_le.mpr hfrac
  unfold johnsonT johnsonM
  have hcast : ((max ⌈Real.sqrt (johnsonRhoMinus n D) / (2 * eta)⌉₊ 3 : ℕ) : ℝ) ≤ m := by
    exact_mod_cast max_le hceil hm
  linarith

/-- The source's full-rate agreement threshold implies the half-gap for the smaller degree
ratio used by the ordinary interpolation certificate. -/
theorem johnson_half_gap_of_legacy_threshold {n D m : ℕ} {eta : ℝ}
    (hm : 3 ≤ m)
    (ha : (1 + 1 / (2 * (m : ℝ))) * Real.sqrt (((D : ℝ) + 1) / n) ≤
      johnsonAgreement n D eta) :
    Real.sqrt (johnsonRhoMinus n D) / (2 * (m : ℝ)) ≤ eta := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hroot : Real.sqrt (johnsonRhoMinus n D) ≤
      Real.sqrt (((D : ℝ) + 1) / n) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  have hmul := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 1 + 1 / (2 * (m : ℝ)) by positivity)
  unfold johnsonAgreement at ha
  have heq : (1 + 1 / (2 * (m : ℝ))) * Real.sqrt (johnsonRhoMinus n D) =
      Real.sqrt (johnsonRhoMinus n D) + Real.sqrt (johnsonRhoMinus n D) /
        (2 * (m : ℝ)) := by ring
  rw [heq] at hmul
  linarith

/-- Twice the finite exception count lies below the explicit seventh-power budget. The factor
two covers either rounded curve height or the affine sampling loss. -/
theorem two_mul_johnsonExceptionCount_le_explicit_budget {n D A m : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (hm : 3 ≤ m) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A)
    (ha : (1 + 1 / (2 * (m : ℝ))) * Real.sqrt (((D : ℝ) + 1) / n) ≤
      johnsonAgreement n D eta) :
    2 * johnsonExceptionCount n D A eta ≤
      ((m : ℝ) + 1 / 2) ^ 7 * (n : ℝ) ^ 2 /
        (3 * Real.rpow (((D : ℝ) + 1) / n) (3 / 2 : ℝ)) := by
  let t : ℝ := m + 1 / 2
  let s : ℝ := Real.sqrt (((D : ℝ) + 1) / n)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have ht : 7 / 2 ≤ t := by dsimp [t]; linarith
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs1 : s ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one hn).mpr (by exact_mod_cast (show D + 1 ≤ n by omega))
  have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hspos.le hs1
  have ht4 : 16 ≤ t ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) ht 4
    norm_num at hh
    linarith
  have hkey : 16 * s ^ 3 ≤ (D : ℝ) * t ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hD1 (pow_nonneg htpos.le 4)
    nlinarith only [hs3, ht4, hh]
  have hT := johnsonT_le_of_half_gap hm heta (johnson_half_gap_of_legacy_threshold hm ha)
  have hTpos : 0 ≤ johnsonT n D eta := by
    have := johnsonT_ge_seven_halves n D eta
    linarith
  have hclosed := (johnsonExceptionCount_lt_closed hD hDn heta hthreshold).le
  have hrpow : Real.rpow (((D : ℝ) + 1) / n) (3 / 2 : ℝ) = s ^ 3 := by
    calc
      _ = Real.rpow s (3 : ℝ) := Real.rpow_div_two_eq_sqrt 3 (by positivity)
      _ = s ^ 3 := Real.rpow_natCast _ 3
  rw [hrpow]
  change 2 * johnsonExceptionCount n D A eta ≤ t ^ 7 * (n : ℝ) ^ 2 / (3 * s ^ 3)
  calc
    2 * johnsonExceptionCount n D A eta ≤
        2 * ((8 / 3 : ℝ) * n * johnsonT n D eta ^ 3 / johnsonRhoMinus n D) :=
      mul_le_mul_of_nonneg_left hclosed (by norm_num)
    _ ≤ 2 * ((8 / 3 : ℝ) * n * t ^ 3 / johnsonRhoMinus n D) := by
      gcongr
      exact (johnsonRhoMinus_pos hD (by omega)).le
    _ = (16 / 3 : ℝ) * (n : ℝ) ^ 2 * t ^ 3 / D := by
      unfold johnsonRhoMinus
      field_simp
      norm_num
    _ ≤ t ^ 7 * (n : ℝ) ^ 2 / (3 * s ^ 3) := by
      apply (div_le_div_iff₀ hDpos (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hkey (show 0 ≤ (n : ℝ) ^ 2 * t ^ 3 by positivity)
      nlinarith only [hh]

/-- The pair-collision count for constant codes also fits the explicit budget, with a factor two
available for affine sampling. -/
theorem two_mul_choose_two_le_explicit_budget {n m : ℕ} (hn : 0 < n) (hm : 3 ≤ m) :
    2 * (n.choose 2 : ℝ) ≤ ((m : ℝ) + 1 / 2) ^ 7 * (n : ℝ) ^ 2 /
      (3 * Real.rpow (1 / (n : ℝ)) (3 / 2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hrpos : 0 < Real.rpow (1 / (n : ℝ)) (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hr1 : Real.rpow (1 / (n : ℝ)) (3 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one (by positivity) ((div_le_one hnpos).mpr hn1) (by norm_num)
  have ht7 : 6 ≤ ((m : ℝ) + 1 / 2) ^ 7 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2)
      (show (7 / 2 : ℝ) ≤ m + 1 / 2 by linarith) 7
    norm_num at hh
    linarith
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow n 2
  apply (le_div_iff₀ (by positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_right hchoose
    (show 0 ≤ 6 * Real.rpow (1 / (n : ℝ)) (3 / 2 : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ 6 * (n : ℝ) ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_right ht7 (sq_nonneg (n : ℝ))
  nlinarith only [h1, h2, h3]

/-- The half-shifted parameter is the numerator convention used by the legacy statements. -/
theorem legacy_shift_pow_seven (m : ℕ) (hm : 0 < m) :
    ((m : ℝ) + 1 / 2) ^ 7 = (1 + 1 / (2 * (m : ℝ))) ^ 7 * (m : ℝ) ^ 7 := by
  rw [← mul_pow]
  congr 1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

/-- A doubled exception budget absorbs the change from uniform field sampling to the affine
nonzero-direction denominator. -/
theorem exception_density_le_of_two_mul_le {E B q : ℝ}
    (hE : 0 ≤ E) (hq : 2 ≤ q) (hB : 2 * E ≤ B) : E / (q - 1) ≤ B / q := by
  have hqpos : 0 < q := by linarith
  have hqmpos : 0 < q - 1 := by linarith
  apply (div_le_div_iff₀ hqmpos hqpos).mpr
  have h1 := mul_nonneg hE (show 0 ≤ q - 2 by linarith)
  have h2 := mul_le_mul_of_nonneg_right hB hqmpos.le
  nlinarith only [h1, h2]

end ReedSolomon.HiddenDerivative
