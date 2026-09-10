/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Rounding
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RankRounding
/-!
# Prescribed inputs to the dimension estimate

The rounded multiplicity and radius are positive. Their floor inequalities supply the mean,
normalized radius, and squared-radius retention used by the actual support-dimension theorem.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- All rounding premises of the dimension estimate follow from the prescribed parameters. -/
theorem prescribed_dimension_inputs (δ ρ H : ℝ) (d : ℕ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ)
    (hd : 48000 ≤ d) (hHlo : xi / δ ≤ H) :
    let g := min 1 (δ / ρ)
    let a := 1 + theta * g
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    0 < m ∧ 0 < W ∧
      (W : ℝ) * H / d ≤ (1 + 3 * g / 8) * m ∧
      (W : ℝ) / ((d : ℝ) * (g * m)) ≤ 10 / 27 ∧
      (999 / 1000) * (a / (g * H)) ^ 2 ≤
        ((W : ℝ) / ((d : ℝ) * (g * m))) ^ 2 := by
  let g := min 1 (δ / ρ)
  let a := 1 + theta * g
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  have hg : 0 < g := (clippedGap_mem_unit δ ρ hδ hρ).1
  have hH : 0 < H := (div_pos xi_pos hδ).trans_le hHlo
  have ha : 1 ≤ a := by dsimp [a]; exact le_add_of_nonneg_right (mul_nonneg theta_pos.le hg.le)
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hd0 : 0 < d := by omega
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hsize
  have hm : 0 < m := Nat.cast_pos.mp hmp
  have hraw := InterpolationRounding.radius_lower a H d m ha hH hsize
  have hR : 2000 ≤ a * d * m / H := by
    calc
      2000 ≤ 100 * (48000 : ℝ) ^ 3 := by norm_num
      _ ≤ 100 * (d : ℝ) ^ 3 := by gcongr; exact_mod_cast hd
      _ ≤ _ := hraw
  have hW : 0 < W := floorRadius_pos a H d m (by linarith)
  have hmean := floorRadius_mul_div_le a H d m hap.le hH hd0 W rfl
  have hs := floorRadius_normalized_le a g H d m W hap.le hg hH hd0 hm rfl
  have hs' := normalizedRadius_le_ten_twentySeven δ ρ H
    ((W : ℝ) / ((d : ℝ) * g * m)) hδ hδmax hρ hρmax hHlo hs
  have hf := floorRadius_sq_ge a g H d m hap hg hH hd0 hm hR
  refine ⟨hm, hW, ?_, ?_, ?_⟩
  · convert hmean using 1
    dsimp [a, theta]
    ring
  · simpa only [W, m, a, g, mul_assoc] using hs'
  · simpa only [W, m, a, g, mul_assoc] using hf
end ReedSolomon.HiddenDerivative.WeightedSupportParameters
