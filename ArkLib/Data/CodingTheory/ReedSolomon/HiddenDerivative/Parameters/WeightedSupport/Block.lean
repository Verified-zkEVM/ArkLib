/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters

/-!
# Finite block bounds for the no-band weighted support

The proof-facing ambient dimension is `K = max k floor(delta*n/2)` and its polynomial degree is
`D = K - 1`.  This module derives the rate interval, the derivative-order room, and the final
agreement cutoff directly from the explicit formulas.  It has no dependency on the retired band
support or on the capacity capstone.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

noncomputable section

/-- The prescribed block threshold supplies all ambient-degree facts needed by interpolation. -/
theorem prescribedBlockBounds (δ : ℝ) (n k : ℕ)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hA : k + Nat.ceil (δ * n) ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let K := max k (Nat.floor (δ * n / 2))
    let D := K - 1
    let A := k + Nat.ceil (δ * n)
    let g := min 1 (δ / ((D : ℝ) / n))
    0 < n ∧ 0 < D ∧ d < D ∧
      δ / 3 ≤ (D : ℝ) / n ∧ (D : ℝ) / n ≤ 1 - δ ∧
      K ≤ n ∧ (D : ℝ) * (1 + g) ≤ A := by
  dsimp only at hblock ⊢
  let d := Nat.ceil (Real.exp (xi / δ))
  let H : ℝ := harmonic (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let K := max k (Nat.floor (δ * n / 2))
  let D := K - 1
  let A := k + Nat.ceil (δ * n)
  let g := min 1 (δ / ((D : ℝ) / n))
  obtain ⟨hd, _, hHlower⟩ := prescribed_order_lower δ hδ hδmax.le
  have hδH : xi ≤ δ * H := by
    have := (div_le_iff₀ hδ).mp hHlower
    simpa [H, d, mul_comm] using this
  have hH : 0 < H := by
    have : 0 < xi / δ := div_pos xi_pos hδ
    exact this.trans_le (by simpa [H, d] using hHlower)
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hsize
  have hm : 0 < m := by exact_mod_cast hmR
  have hblock' : 8 * m ≤ n := by simpa [m, H, d] using hblock
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδn : 2160 * (d : ℝ) ^ 2 ≤ δ * n := by
    have hscaled := mul_le_mul_of_nonneg_left hsize hδ.le
    have hδHscaled := mul_le_mul_of_nonneg_left hδH
      (by positivity : (0 : ℝ) ≤ 800 * (d : ℝ) ^ 2)
    have hblockR : 8 * (m : ℝ) ≤ n := by exact_mod_cast hblock'
    have hblockScaled := mul_le_mul_of_nonneg_left hblockR hδ.le
    norm_num [xi] at hδHscaled
    nlinarith
  have hδn12 : 12 ≤ δ * n := by
    have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hK : 0 < K := by
    exact hk.trans_le (Nat.le_max_left _ _)
  have hDcast : ((D : ℕ) : ℝ) = K - 1 := by
    dsimp [D]
    rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
  have hfloorLt := Nat.lt_floor_add_one (δ * (n : ℝ) / 2)
  have hfloorLe : Nat.floor (δ * (n : ℝ) / 2) ≤ K := by
    exact Nat.le_max_right _ _
  have hfloorLeR : (Nat.floor (δ * (n : ℝ) / 2) : ℝ) ≤ K := by
    exact_mod_cast hfloorLe
  have hDlow : δ * (n : ℝ) / 3 ≤ D := by
    rw [hDcast]
    linarith [hfloorLt, hfloorLeR]
  have hD : 0 < D := by
    have : (0 : ℝ) < D := (by positivity : 0 < δ * (n : ℝ) / 3).trans_le hDlow
    exact_mod_cast this
  have hceil := Nat.le_ceil (δ * (n : ℝ))
  have hAreal : (k : ℝ) + Nat.ceil (δ * (n : ℝ)) ≤ n := by exact_mod_cast hA
  have hkUpper : (k : ℝ) ≤ (1 - δ) * n := by nlinarith
  have hfloorUpper : (Nat.floor (δ * (n : ℝ) / 2) : ℝ) ≤ (1 - δ) * n := by
    have hf := Nat.floor_le (by positivity : 0 ≤ δ * (n : ℝ) / 2)
    have hcoeff : δ / 2 ≤ 1 - δ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff hnR.le
    nlinarith
  have hKUpper : (K : ℝ) ≤ (1 - δ) * n := by
    dsimp [K]
    rw [Nat.cast_max]
    exact max_le hkUpper hfloorUpper
  have hrateLower : δ / 3 ≤ (D : ℝ) / n := by
    apply (le_div_iff₀ hnR).mpr
    nlinarith [hDlow]
  have hrateUpper : (D : ℝ) / n ≤ 1 - δ := by
    apply (div_le_iff₀ hnR).mpr
    rw [hDcast]
    linarith
  have hdD : d < D := by
    have hDlarge : 720 * (d : ℝ) ^ 2 ≤ D := by nlinarith [hδn, hDlow]
    have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
    exact_mod_cast (show (d : ℝ) < D by nlinarith)
  have hKn : K ≤ n := by
    have hkA : k ≤ A := by dsimp [A]; omega
    have hkN : k ≤ n := hkA.trans hA
    have hf : (Nat.floor (δ * (n : ℝ) / 2) : ℝ) ≤ n := by
      have hfloor := Nat.floor_le (by positivity : 0 ≤ δ * (n : ℝ) / 2)
      have hδone : δ ≤ 1 := hδmax.le.trans (by norm_num)
      have := mul_le_mul_of_nonneg_right hδone hnR.le
      nlinarith
    dsimp [K]
    exact max_le hkN (by exact_mod_cast hf)
  have hcutoff : (D : ℝ) * (1 + g) ≤ A := by
    have hslack := min_le_right (1 : ℝ) (δ * n / D)
    have hone := min_le_left (1 : ℝ) (δ * n / D)
    have hAδ : (k : ℝ) + δ * n ≤ A := by
      dsimp [A]
      push_cast
      linarith
    have hDp : (0 : ℝ) < D := by exact_mod_cast hD
    have hrateEq : δ / ((D : ℝ) / n) = δ * n / D := by
      field_simp
    dsimp [g]
    rw [hrateEq]
    by_cases hcase : Nat.floor (δ * (n : ℝ) / 2) ≤ k
    · have hKeq : K = k := by dsimp [K]; exact max_eq_left hcase
      have hmul := (le_div_iff₀ hDp).mp hslack
      have hmul' : (D : ℝ) * min 1 (δ * n / D) ≤ δ * n := by
        simpa only [mul_comm] using hmul
      have hDk : (D : ℝ) ≤ k := by rw [hDcast, hKeq]; linarith
      calc
        (D : ℝ) * (1 + min 1 (δ * n / D)) = D + D * min 1 (δ * n / D) := by ring
        _ ≤ D + δ * n := add_le_add le_rfl hmul'
        _ ≤ k + δ * n := add_le_add hDk le_rfl
        _ ≤ A := hAδ
    · have hKeq : K = Nat.floor (δ * (n : ℝ) / 2) := by
        dsimp [K]
        exact max_eq_right (by omega)
      have hf := Nat.floor_le (by positivity : 0 ≤ δ * (n : ℝ) / 2)
      have hmul := mul_le_mul_of_nonneg_left hone hDp.le
      have hmul' : (D : ℝ) * min 1 (δ * n / D) ≤ D := by
        simpa only [mul_one] using hmul
      have htwice : 2 * (D : ℝ) ≤ δ * n := by
        rw [hDcast, hKeq]
        have hfR : (Nat.floor (δ * (n : ℝ) / 2) : ℝ) ≤ δ * n / 2 := hf
        linarith only [hfR]
      calc
        (D : ℝ) * (1 + min 1 (δ * n / D)) = D + D * min 1 (δ * n / D) := by ring
        _ ≤ D + D := add_le_add le_rfl hmul'
        _ = 2 * D := by ring
        _ ≤ δ * n := htwice
        _ ≤ k + δ * n := le_add_of_nonneg_left (Nat.cast_nonneg k)
        _ ≤ A := hAδ
  exact ⟨hn, hD, hdD, hrateLower, hrateUpper, hKn, hcutoff⟩

end

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
