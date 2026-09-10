/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Radius
/-!
# Characteristic-compatible order-zero parameter margins

For n≥3, multiplicity floor(n/2) leaves strict jet degree below n while retaining the numerical
surplus needed by ordinary bivariate multiplicity interpolation. These are parameter lemmas,
not an interpolation witness or a decoder. The separate n=1,2 cases remain open here.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open ReedSolomon

/-- Half-length multiplicity is positive and keeps the strict 2m jet cap below any q≥n. -/
theorem zero_multiplicity_bounds (n : ℕ) (hn : 3 ≤ n) :
    0 < n / 2 ∧ 2 * (n / 2) ≤ n ∧ n - 1 ≤ 2 * (n / 2) := by omega

/-- The quarter-gap agreement threshold has the exact quadratic Johnson margin. -/
theorem zero_quarter_margin (n k A : ℕ) (hk : 0 < k)
    (hA : (k : ℝ) + (n : ℝ) / 4 ≤ A) :
    ((k : ℝ) - (n : ℝ) / 4) ^ 2 + n ≤ (A : ℝ) ^ 2 - n * (k - 1 : ℕ) := by
  have hD : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hs : ((k : ℝ) + (n : ℝ) / 4) ^ 2 ≤ (A : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hA 2
  rw [hD]
  nlinarith only [hs]

/-- Half-length multiplicity provides strict triangle-area surplus above all local constraints. -/
theorem zero_triangle_surplus (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : (k : ℝ) + (n : ℝ) / 4 ≤ A) :
    (n : ℝ) * (k - 1 : ℕ) < (n / 2 : ℕ) *
      ((A : ℝ) ^ 2 - n * (k - 1 : ℕ)) := by
  let x : ℝ := k - (n : ℝ) / 4
  let G : ℝ := (A : ℝ) ^ 2 - n * (k - 1 : ℕ)
  have hg : x ^ 2 + n ≤ G := zero_quarter_margin n k A hk hA
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (n : ℝ) - 1 ≤ 2 * (n / 2 : ℕ) := by
    have h : n ≤ 2 * (n / 2) + 1 := by omega
    have hR : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast h
    linarith
  have hD : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hG : 0 ≤ G := (by positivity : (0 : ℝ) ≤ x ^ 2 + n).trans hg
  have h₁ := mul_le_mul_of_nonneg_right hm hG
  have h₂ := mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℝ) ≤ n - 1)
  have h₃ := mul_nonneg (show (0 : ℝ) ≤ n - 3 by linarith) (sq_nonneg x)
  have h₄ := sq_nonneg (x - (n : ℝ) / 2)
  change (n : ℝ) * (k - 1 : ℕ) < (n / 2 : ℕ) * G
  rw [hD]
  dsimp only [x] at h₁ h₂ h₃ h₄
  nlinarith only [h₁, h₂, h₃, h₄, hnR]

/-- In the truncated regime, the exact rectangular-staircase count also has strict surplus. -/
theorem zero_truncated_surplus (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : (k : ℝ) + (n : ℝ) / 4 ≤ A) :
    n * (n / 2) * (n / 2 + 1) <
      4 * (n / 2) * (n / 2) * (A - (k - 1)) + 2 * (k - 1) * (n / 2) := by
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by linarith [show (0 : ℝ) ≤ n by positivity]
    exact_mod_cast h
  have hsub : ((A - (k - 1) : ℕ) : ℝ) = (A : ℝ) - k + 1 := by
    rw [Nat.cast_sub (by omega : k - 1 ≤ A), Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  have hfour : n + 4 ≤ 4 * (A - (k - 1)) := by
    have h : (n : ℝ) + 4 ≤ 4 * (A - (k - 1) : ℕ) := by rw [hsub]; linarith
    exact_mod_cast h
  have hm : 0 < n / 2 := by omega
  have ht : n < 4 * (n / 2) + 2 * (k - 1) := by omega
  have h₁ := Nat.mul_le_mul_left (n / 2 * (n / 2)) hfour
  have h₂ := Nat.mul_lt_mul_of_pos_left ht hm
  nlinarith only [h₁, h₂]

/-- Real gap parameters supply the integer agreement premise used by the two count regimes. -/
theorem zero_threshold_quarter (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (n k A : ℕ) (hA : agreementThreshold delta n k ≤ A) :
    (k : ℝ) + (n : ℝ) / 4 ≤ A := by
  have hd : 0 ≤ delta := by linarith
  have h := (agreementThreshold_le_iff_real hd n k A).mp hA
  nlinarith [mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg n : (0 : ℝ) ≤ _)]

end ReedSolomon.HiddenDerivative
