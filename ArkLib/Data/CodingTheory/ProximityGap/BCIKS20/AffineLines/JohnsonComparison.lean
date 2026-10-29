/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Comparison with the BCIKS20 line error

The finite Johnson exception count is bounded by the seventh-power numerator used in the
BCIKS20 line theorem. The comparison uses positive slack and the rate `(D + 1) / n` of the
legacy statement, while the interpolation parameters use the degree ratio `D / n`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- The rounded Johnson parameter is bounded by the full-rate square root divided by slack. -/
theorem johnsonT_le_bciks {n D : ℕ} {eta b : ℝ}
    (hb : 0 < b) (hbeta : b ≤ eta)
    (hbRate : b ≤ Real.sqrt (((D : ℝ) + 1) / n) / 20) :
    johnsonT n D eta ≤ Real.sqrt (((D : ℝ) + 1) / n) / b := by
  let s := Real.sqrt (((D : ℝ) + 1) / n)
  have heta : 0 < eta := hb.trans_le hbeta
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hroot : Real.sqrt (johnsonRhoMinus n D) ≤ s := by
    apply Real.sqrt_le_sqrt
    unfold johnsonRhoMinus
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  have hfrac : Real.sqrt (johnsonRhoMinus n D) / (2 * eta) ≤ s / (2 * b) := by
    apply div_le_div₀ (Real.sqrt_nonneg _) hroot (by positivity)
    linarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt (johnsonRhoMinus n D) /
      (2 * eta) by positivity)
  have hlarge : 20 * b ≤ s := by dsimp only [s] at *; linarith
  have hratio : 20 ≤ s / b := (le_div_iff₀ hb).2 (by linarith)
  have hceil' : (⌈Real.sqrt (johnsonRhoMinus n D) / (2 * eta)⌉₊ : ℝ) + 1 / 2 ≤
      s / b := by
    have heq : s / (2 * b) = (s / b) / 2 := by ring
    rw [heq] at hfrac
    linarith
  unfold johnsonT johnsonM
  rw [Nat.cast_max]
  change max _ (3 : ℝ) + 1 / 2 ≤ s / b
  apply (le_sub_iff_add_le).mp
  exact max_le (by linarith) (by linarith)

/-- Twice the finite Johnson exception count is below the legacy seventh-power numerator.
The extra factor covers rounded curve heights or the affine sampling loss. The hypotheses
express positive slack below both the Johnson gap and one twentieth of the full-rate square root. -/
theorem two_mul_johnsonExceptionCount_le_bciks {n D A : ℕ} {eta b : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A)
    (hb : 0 < b) (hbeta : b ≤ eta)
    (hbRate : b ≤ Real.sqrt (((D : ℝ) + 1) / n) / 20) :
    2 * johnsonExceptionCount n D A eta ≤ ((D : ℝ) + 1) ^ 2 / (2 * b) ^ 7 := by
  let s := Real.sqrt (((D : ℝ) + 1) / n)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ((D : ℝ) + 1) / n := Real.sq_sqrt (by positivity)
  have hs1 : s ≤ 1 := by
    apply (Real.sqrt_le_one).2
    exact (div_le_one hn).2 (by exact_mod_cast (show D + 1 ≤ n by omega))
  have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hs hs1
  have hb4 : 160000 * b ^ 4 ≤ s ^ 4 := by
    have hp := pow_le_pow_left₀ (show 0 ≤ 20 * b by positivity)
      (show 20 * b ≤ s by dsimp only [s]; linarith) 4
    norm_num [mul_pow] at hp
    exact hp
  have hkey : 2048 * s ^ 3 * b ^ 4 ≤ 3 * (D : ℝ) * s ^ 4 := by
    have hm := mul_le_mul_of_nonneg_right hs3 (show 0 ≤ b ^ 4 by positivity)
    have hd := mul_le_mul_of_nonneg_right hD' (show 0 ≤ s ^ 4 by positivity)
    nlinarith [pow_nonneg hb.le 4]
  have hrate : (D : ℝ) + 1 = n * s ^ 2 := by
    rw [hs2]
    field_simp
  have ht := johnsonT_le_bciks hb hbeta hbRate
  have ht0 : 0 ≤ johnsonT n D eta := by
    have := johnsonT_ge_seven_halves n D eta
    linarith
  have hclosed := (johnsonExceptionCount_lt_closed hD hDn heta hthreshold).le
  refine (mul_le_mul_of_nonneg_left hclosed (by norm_num : (0 : ℝ) ≤ 2)).trans ?_
  calc
    2 * ((8 / 3 : ℝ) * n * johnsonT n D eta ^ 3 / johnsonRhoMinus n D) ≤
        2 * ((8 / 3 : ℝ) * n * (s / b) ^ 3 / johnsonRhoMinus n D) := by
      gcongr
      exact (johnsonRhoMinus_pos hD (by omega)).le
    _ = (16 / 3 : ℝ) * (n : ℝ) ^ 2 * s ^ 3 / ((D : ℝ) * b ^ 3) := by
      unfold johnsonRhoMinus
      field_simp
      ring
    _ ≤ ((D : ℝ) + 1) ^ 2 / (2 * b) ^ 7 := by
      rw [hrate]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hm := mul_le_mul_of_nonneg_left hkey
        (show 0 ≤ (n : ℝ) ^ 2 * b ^ 3 / 3 by positivity)
      nlinarith only [hm]

/-- The proved finite Johnson exception count is below the legacy seventh-power numerator.
The hypotheses express positive slack below both the Johnson gap and one twentieth of the
full-rate square root. -/
theorem johnsonExceptionCount_le_bciks {n D A : ℕ} {eta b : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A)
    (hb : 0 < b) (hbeta : b ≤ eta)
    (hbRate : b ≤ Real.sqrt (((D : ℝ) + 1) / n) / 20) :
    johnsonExceptionCount n D A eta ≤ ((D : ℝ) + 1) ^ 2 / (2 * b) ^ 7 := by
  have h := two_mul_johnsonExceptionCount_le_bciks hD hDn heta hthreshold hb hbeta hbRate
  have hnonneg : 0 ≤ johnsonExceptionCount n D A eta := by
    unfold johnsonExceptionCount johnsonTheta
    positivity
  linarith

/-- Twice the constant-code pair-collision bound fits the same seventh-power numerator. -/
theorem two_mul_choose_two_le_bciks {n : ℕ} {b : ℝ} (hn : 0 < n)
    (hb : 0 < b) (hbRate : b ≤ Real.sqrt (1 / (n : ℝ)) / 20) :
    2 * (n.choose 2 : ℝ) ≤ 1 / (2 * b) ^ 7 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let s := Real.sqrt (1 / (n : ℝ))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one hn').2 hn1
  have hs2 : s ^ 2 = 1 / (n : ℝ) := Real.sq_sqrt (by positivity)
  have hbs : 2 * b ≤ s / 2 := by dsimp only [s] at *; linarith
  have hb1 : 2 * b ≤ 1 := by linarith
  have hpow3 : (2 * b) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hb1
  have hpow4 : (2 * b) ^ 4 ≤ (s / 2) ^ 4 := pow_le_pow_left₀ (by positivity) hbs 4
  have hs4 : s ^ 4 * (n : ℝ) ^ 2 = 1 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]
    field_simp
  have hprod : 2 * (n : ℝ) ^ 2 * (2 * b) ^ 7 ≤ 1 := by
    calc
      2 * (n : ℝ) ^ 2 * (2 * b) ^ 7 =
          2 * ((2 * b) ^ 4 * (n : ℝ) ^ 2) * (2 * b) ^ 3 := by ring
      _ ≤ 2 * ((s / 2) ^ 4 * (n : ℝ) ^ 2) * 1 := by gcongr
      _ = (s ^ 4 * (n : ℝ) ^ 2) / 8 := by ring
      _ ≤ 1 := by rw [hs4]; norm_num
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow n 2
  exact (mul_le_mul_of_nonneg_left hchoose (by norm_num : (0 : ℝ) ≤ 2)).trans
    ((le_div_iff₀ (by positivity)).2 hprod)

/-- The pair-collision bound for constant codes is below the same seventh-power numerator. -/
theorem choose_two_le_bciks {n : ℕ} {b : ℝ} (hn : 0 < n)
    (hb : 0 < b) (hbRate : b ≤ Real.sqrt (1 / (n : ℝ)) / 20) :
    (n.choose 2 : ℝ) ≤ 1 / (2 * b) ^ 7 := by
  have h := two_mul_choose_two_le_bciks hn hb hbRate
  have hnonneg : (0 : ℝ) ≤ n.choose 2 := Nat.cast_nonneg _
  linarith

end ReedSolomon.HiddenDerivative
