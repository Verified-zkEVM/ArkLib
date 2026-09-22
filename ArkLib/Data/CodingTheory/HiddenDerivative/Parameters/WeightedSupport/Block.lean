/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters

/-!
# The ambient dimension of the weighted-support block

For a radius `δ`, a block length `n` and a message dimension `k`, the weighted-support
interpolation works in ambient dimension `K = max k ⌊δ n / 2⌋₊` with polynomial degree
`D = K - 1`, rate `D / n`, clipped gap `g = rateGap δ (D / n)` and agreement cutoff
`A = k + ⌈δ n⌉₊`. This file proves the facts about `K` and `D` used by the interpolation:

* `blockDegree_mul_one_add_rateGap_le`: `D (1 + g) ≤ A`, with no hypotheses. If `K = k` then
  `D < k` and `D g ≤ δ n`; if `K = ⌊δ n / 2⌋₊` then `D (1 + g) ≤ 2 D ≤ δ n`.
* `blockDegree_bounds`: for `δ ≤ 2 / 3`, `12 ≤ δ n` and `A ≤ n`, the rate lies in
  `[δ / 3, 1 - δ]` and `K ≤ (1 - δ) n`.
* `prescribedBlockBounds`: the prescribed block `8 ⌈100 d ^ 2 harmonic (d - 1)⌉₊ ≤ n` with
  `d = ⌈exp (ξ / δ)⌉₊` and `0 < δ ≤ 1 / 4` gives `δ n ≥ 2160 d ^ 2`, hence all of the above and
  `d < D`.

## Main statements

* `blockDegree_mul_one_add_rateGap_le`, `blockDegree_bounds`, `prescribedBlockBounds`
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- `D (1 + g) ≤ k + ⌈δ n⌉₊` for `D = max k ⌊δ n / 2⌋₊ - 1` and `g = rateGap δ (D / n)`, for
every real `δ` and naturals `n`, `k`. The gap satisfies `D g ≤ δ n` (it is at most
`δ / (D / n)`), and `D g ≤ D` (it is at most `1`). If `K = k` then `D ≤ k` and the first bound
applies; otherwise `2 D ≤ 2 ⌊δ n / 2⌋₊ ≤ δ n` and the second applies. When `D = 0` or `n = 0` the
product `D g` is `0`. -/
theorem blockDegree_mul_one_add_rateGap_le (δ : ℝ) (n k : ℕ) :
    let D := max k ⌊δ * n / 2⌋₊ - 1
    (D : ℝ) * (1 + rateGap δ ((D : ℝ) / n)) ≤ k + ⌈δ * n⌉₊ := by
  intro D
  have hceil : δ * n ≤ ⌈δ * n⌉₊ := Nat.le_ceil _
  have hceil0 : (0 : ℝ) ≤ ⌈δ * n⌉₊ := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hgD : (D : ℝ) * rateGap δ ((D : ℝ) / n) ≤ D :=
    mul_le_of_le_one_right hD0 (rateGap_le_one _ _)
  have hgn : (D : ℝ) * rateGap δ ((D : ℝ) / n) ≤ ⌈δ * n⌉₊ := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · simp [hD]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn, rateGap]
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc (D : ℝ) * rateGap δ ((D : ℝ) / n) ≤ D * (δ / ((D : ℝ) / n)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hD0
      _ = δ * n := by field_simp
      _ ≤ _ := hceil
  rcases le_total ⌊δ * n / 2⌋₊ k with h | h
  · have hDk : (D : ℝ) ≤ k := by exact_mod_cast (show D ≤ k by omega)
    linarith
  · have hDf : D ≤ ⌊δ * n / 2⌋₊ := by omega
    have h2 : 2 * (D : ℝ) ≤ ⌈δ * n⌉₊ := by
      rcases le_or_gt (δ * n / 2) 0 with hneg | hpos
      · rw [Nat.floor_eq_zero.mpr (hneg.trans_lt one_pos), Nat.le_zero] at hDf
        simp [hDf]
      have hf : (⌊δ * n / 2⌋₊ : ℝ) ≤ δ * n / 2 := Nat.floor_le hpos.le
      have hDfR : (D : ℝ) ≤ ⌊δ * n / 2⌋₊ := by exact_mod_cast hDf
      linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith

/-- The rate and size of the block. Let `K = max k ⌊δ n / 2⌋₊` and `D = K - 1`. If `δ ≤ 2 / 3`,
`12 ≤ δ n` and `k + ⌈δ n⌉₊ ≤ n`, then `0 < n`, `δ n / 3 ≤ D`, `δ / 3 ≤ D / n`, `D / n ≤ 1 - δ` and
`K ≤ (1 - δ) n`. The lower bound uses `⌊δ n / 2⌋₊ > δ n / 2 - 1` and `δ n / 2 - 2 ≥ δ n / 3`,
which is `δ n ≥ 12`. The upper bound uses `k ≤ n - ⌈δ n⌉₊ ≤ (1 - δ) n` and
`⌊δ n / 2⌋₊ ≤ δ n / 2 ≤ (1 - δ) n`, which is `δ ≤ 2 / 3`. -/
theorem blockDegree_bounds {δ : ℝ} {n k : ℕ} (hδmax : δ ≤ 2 / 3) (hδn : 12 ≤ δ * n)
    (hA : k + ⌈δ * n⌉₊ ≤ n) :
    let K := max k ⌊δ * n / 2⌋₊
    let D := K - 1
    0 < n ∧ δ * n / 3 ≤ D ∧ δ / 3 ≤ (D : ℝ) / n ∧ (D : ℝ) / n ≤ 1 - δ ∧
      (K : ℝ) ≤ (1 - δ) * n := by
  intro K D
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at hδn; linarith
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloorLt := Nat.lt_floor_add_one (δ * (n : ℝ) / 2)
  have hfloorLe : (⌊δ * (n : ℝ) / 2⌋₊ : ℝ) ≤ K := by exact_mod_cast Nat.le_max_right _ _
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  have hDcast : (D : ℝ) = K - 1 := by
    rw [Nat.cast_sub hK1, Nat.cast_one]
  have hDlow : δ * n / 3 ≤ D := by rw [hDcast]; linarith
  have hceil := Nat.le_ceil (δ * (n : ℝ))
  have hAR : (k : ℝ) + ⌈δ * (n : ℝ)⌉₊ ≤ n := by exact_mod_cast hA
  have hf := Nat.floor_le (by linarith : 0 ≤ δ * (n : ℝ) / 2)
  have hKup : (K : ℝ) ≤ (1 - δ) * n := by
    rw [Nat.cast_max]
    refine max_le (by linarith) ?_
    nlinarith
  refine ⟨hn, hDlow, ?_, ?_, hKup⟩
  · rw [le_div_iff₀ hnR]; linarith
  · rw [div_le_iff₀ hnR, hDcast]; linarith

/-- The prescribed block bounds. Let `0 < δ ≤ 1 / 4`, `d = ⌈exp (ξ / δ)⌉₊`,
`m = ⌈100 d ^ 2 harmonic (d - 1)⌉₊`, and suppose `8 m ≤ n` and `k + ⌈δ n⌉₊ ≤ n`. With
`K = max k ⌊δ n / 2⌋₊`, `D = K - 1`, `A = k + ⌈δ n⌉₊` and `g = rateGap δ (D / n)`:
`0 < n`, `0 < D`, `d < D`, `δ / 3 ≤ D / n ≤ 1 - δ`, `K ≤ n` and `D (1 + g) ≤ A`.
Since `harmonic (d - 1) ≥ ξ / δ` (`prescribed_order_lower`), `δ n ≥ 8 δ m ≥ 800 ξ d ^ 2 =
2160 d ^ 2`; this gives `12 ≤ δ n` for `blockDegree_bounds` and `D ≥ δ n / 3 ≥ 720 d ^ 2 > d`. -/
theorem prescribedBlockBounds (δ : ℝ) (n k : ℕ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hblock :
      let d := ⌈Real.exp (xi / δ)⌉₊
      let H : ℝ := harmonic (d - 1)
      let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
      8 * m ≤ n)
    (hA : k + ⌈δ * n⌉₊ ≤ n) :
    let d := ⌈Real.exp (xi / δ)⌉₊
    let K := max k ⌊δ * n / 2⌋₊
    let D := K - 1
    let A := k + ⌈δ * n⌉₊
    let g := rateGap δ ((D : ℝ) / n)
    0 < n ∧ 0 < D ∧ d < D ∧
      δ / 3 ≤ (D : ℝ) / n ∧ (D : ℝ) / n ≤ 1 - δ ∧
      K ≤ n ∧ (D : ℝ) * (1 + g) ≤ A := by
  intro d K D A g
  obtain ⟨hd, _, hHlower⟩ := prescribed_order_lower δ hδ hδmax
  set H : ℝ := (harmonic (d - 1) : ℝ)
  have hδH : xi ≤ δ * H := by rwa [div_le_iff₀ hδ, mul_comm] at hHlower
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ ⌈100 * (d : ℝ) ^ 2 * H⌉₊ := Nat.le_ceil _
  have hblockR : 8 * (⌈100 * (d : ℝ) ^ 2 * H⌉₊ : ℝ) ≤ n := by exact_mod_cast hblock
  have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
  have hδn : 2160 * (d : ℝ) ^ 2 ≤ δ * n := by
    have h1 := mul_le_mul_of_nonneg_left hsize hδ.le
    have h2 := mul_le_mul_of_nonneg_left hblockR hδ.le
    have h3 := mul_le_mul_of_nonneg_left hδH (by positivity : (0 : ℝ) ≤ 800 * (d : ℝ) ^ 2)
    norm_num [xi] at h3
    nlinarith
  obtain ⟨hn, hDlow, hlo, hhi, hK⟩ :=
    blockDegree_bounds (δ := δ) (n := n) (k := k) (by linarith) (by nlinarith) hA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdD : (d : ℝ) < D := by
    have : (d : ℝ) < δ * n / 3 := by nlinarith
    exact this.trans_le hDlow
  have hcut := blockDegree_mul_one_add_rateGap_le δ n k
  dsimp only at hcut
  refine ⟨hn, ?_, by exact_mod_cast hdD, hlo, hhi, ?_, by simpa only [A, Nat.cast_add] using hcut⟩
  · have : (0 : ℝ) < D := (by positivity : (0 : ℝ) ≤ d).trans_lt hdD
    exact_mod_cast this
  · have : (K : ℝ) ≤ n := hK.trans (by nlinarith)
    exact_mod_cast this

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
