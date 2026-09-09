/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.DimensionSensitive
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Dimension-sensitive product estimates

The correlated-agreement cutoff keeps the dimension of each incidence problem visible.
At the original agreement threshold, each factor costs at most `1 / δ`. At the
intermediate cutoff, the entire fiber product costs less than `3 / δ ^ r`.
The one remaining joint factor costs at most `(d + 1) / δ`.
-/

open AffineHilbert
namespace ReedSolomon

/-- The intermediate threshold for a maximum derivative order `d`. -/
noncomputable def correlatedProductCutoff (d k A : ℕ) : ℕ :=
  k + Nat.floor ((d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1))

/-- One evaluation incidence factor at the original agreement threshold. -/
theorem evaluation_incidence_factor_le (δ : ℝ) (n k A j : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hkA : k ≤ A) (hAn : A ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) :
    ((n - k + j + 1 : ℕ) : ℝ) / (A - k + j + 1 : ℕ) ≤ 1 / δ := by
  have hden : (0 : ℝ) < (A - k + j + 1 : ℕ) := by positivity
  rw [div_le_div_iff₀ hden hδ]
  push_cast [Nat.cast_sub hkA, Nat.cast_sub (hkA.trans hAn)]
  have hj := mul_le_mul_of_nonneg_right hδone (show (0 : ℝ) ≤ j + 1 by positivity)
  have hk : 0 ≤ δ * (k : ℝ) := by positivity
  nlinarith

/-- The dimension-sensitive product retains its actual dimension `r`. -/
theorem evaluation_incidence_product_le (δ : ℝ) (n k A r : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hkA : k ≤ A) (hAn : A ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) :
    (dimensionSensitiveIncidenceProduct n A k 1 r : ℝ) ≤ (1 / δ) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [dimensionSensitiveIncidenceProduct_succ, Rat.cast_mul, pow_succ]
    apply mul_le_mul ih
    · simpa using evaluation_incidence_factor_le δ n k A r hδ hδone hkA hAn hgap
    · positivity
    · positivity

/-- The intermediate cutoff lies between the code dimension and agreement threshold. -/
theorem correlatedProductCutoff_bounds (d k A : ℕ) (hkA : k ≤ A) :
    k ≤ correlatedProductCutoff d k A ∧ correlatedProductCutoff d k A ≤ A := by
  have hraw : 0 ≤ (d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1) := by positivity
  have hf := Nat.floor_le hraw
  have hle : (d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1) ≤ (A - k : ℕ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < d + 1)]
    push_cast [Nat.cast_sub hkA]
    have hh : (0 : ℝ) ≤ A - k := by exact_mod_cast Nat.zero_le (A - k)
    nlinarith
  have hfloor : Nat.floor ((d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1)) ≤ A - k := by
    exact_mod_cast hf.trans hle
  unfold correlatedProductCutoff
  omega

/-- The joint incidence factor costs at most `(d + 1) / δ`. -/
theorem correlatedProductCutoff_jointRatio_le (δ : ℝ) (n k A d : ℕ)
    (hδ : 0 < δ) (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) :
    let L := correlatedProductCutoff d k A
    ((n - L + 1 : ℕ) : ℝ) / (A - L + 1 : ℕ) ≤ (d + 1) / δ := by
  let L := correlatedProductCutoff d k A
  have hb := correlatedProductCutoff_bounds d k A hkA
  have hLA : L ≤ A := hb.2
  have hLn : L ≤ n := hLA.trans hAn
  have hL : 0 < L := hk.trans_le hb.1
  have hnum : (n - L + 1 : ℕ) ≤ n := by omega
  have hraw : 0 ≤ (d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1) := by positivity
  have hf := Nat.floor_le hraw
  have hfloor : (L : ℝ) - k ≤ (d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1) := by
    simpa [L, correlatedProductCutoff] using hf
  have hscaled := (le_div_iff₀ (show (0 : ℝ) < d + 1 by positivity)).mp hfloor
  have hden : (0 : ℝ) < (A - L + 1 : ℕ) := by positivity
  apply (div_le_div_iff₀ hden hδ).mpr
  have hnumR : ((n - L + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnum
  have hh := mul_le_mul_of_nonneg_left hnumR hδ.le
  push_cast [Nat.cast_sub hkA] at hscaled
  have hbound : (A : ℝ) - k ≤ (d + 1) * ((A - L + 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hLA]
    nlinarith
  calc
    _ ≤ δ * n := by simpa only [mul_comm] using hh
    _ ≤ (A : ℝ) - k := by linarith
    _ ≤ _ := hbound

/-- A fiber incidence factor at the intermediate threshold. -/
theorem correlatedProductCutoff_fiberFactor_le (δ : ℝ) (n k A d j : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hd : 0 < d) (hk : 0 < k)
    (hkA : k ≤ A) (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) :
    let L := correlatedProductCutoff d k A
    ((n - k + j + 1 : ℕ) : ℝ) / (L - k + j + 1 : ℕ) ≤ (1 + 1 / d) / δ := by
  let L := correlatedProductCutoff d k A
  have hb := correlatedProductCutoff_bounds d k A hkA
  have hkl : k ≤ L := hb.1
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hden : (0 : ℝ) < (L - k + j + 1 : ℕ) := by positivity
  have hf := Nat.lt_floor_add_one ((d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1))
  have hfloor : (d : ℝ) * ((A - k : ℕ) : ℝ) / (d + 1) < (L : ℝ) - k + 1 := by
    simpa [L, correlatedProductCutoff] using hf
  have hscaled := (div_lt_iff₀ (show (0 : ℝ) < d + 1 by positivity)).mp hfloor
  have hgap' := mul_le_mul_of_nonneg_left hgap hdR.le
  have hnum : n - k + j + 1 ≤ n + j := by omega
  have hnumR : ((n - k + j + 1 : ℕ) : ℝ) ≤ n + j := by exact_mod_cast hnum
  have hscale := mul_le_mul_of_nonneg_left hnumR (show 0 ≤ (d : ℝ) * δ by positivity)
  have hj := mul_le_mul_of_nonneg_right hδone (show 0 ≤ (d : ℝ) * j by positivity)
  have hcoeff : (1 + 1 / (d : ℝ)) / δ = (d + 1) / (d * δ) := by field_simp
  rw [hcoeff]
  apply (div_le_div_iff₀ hden (mul_pos hdR hδ)).mpr
  push_cast [Nat.cast_sub hkA] at hscaled
  push_cast [Nat.cast_sub hkl, Nat.cast_sub (hkA.trans hAn)] at hscale ⊢
  nlinarith

/-- Multiplying the fiber estimates preserves the actual dimension. -/
theorem correlatedProductCutoff_fiberProduct_le (δ : ℝ) (n k A d r : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hd : 0 < d) (hk : 0 < k)
    (hkA : k ≤ A) (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) :
    (dimensionSensitiveIncidenceProduct n (correlatedProductCutoff d k A) k 1 r : ℝ) ≤
      ((1 + 1 / d) / δ) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [dimensionSensitiveIncidenceProduct_succ, Rat.cast_mul, pow_succ]
    apply mul_le_mul ih
    · simpa using correlatedProductCutoff_fiberFactor_le δ n k A d r
        hδ hδone hd hk hkA hAn hgap
    · positivity
    · positivity

/-- The complete fiber product loses less than a factor of three for `r ≤ d`. -/
theorem correlatedProductCutoff_fiberProduct_lt_three (δ : ℝ) (n k A d r : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hd : 0 < d) (hk : 0 < k)
    (hkA : k ≤ A) (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) (hr : r ≤ d) :
    (dimensionSensitiveIncidenceProduct n (correlatedProductCutoff d k A) k 1 r : ℝ) <
      3 * (1 / δ) ^ r := by
  have hbase : (1 : ℝ) ≤ 1 + 1 / d := le_add_of_nonneg_right (by positivity)
  have hpow := pow_le_pow_right₀ hbase hr
  have he : (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp 1 := by
    simpa only [one_div] using Real.one_add_inv_pow_le_exp (n := d)
  have hthree : (1 + 1 / (d : ℝ)) ^ r < 3 :=
    (hpow.trans he).trans_lt Real.exp_one_lt_three
  calc
    _ ≤ ((1 + 1 / d) / δ) ^ r :=
      correlatedProductCutoff_fiberProduct_le δ n k A d r hδ hδone hd hk hkA hAn hgap
    _ = (1 + 1 / (d : ℝ)) ^ r * (1 / δ) ^ r := by rw [div_pow, one_div_pow]; ring
    _ < _ := mul_lt_mul_of_pos_right hthree (pow_pos (div_pos zero_lt_one hδ) _)
end ReedSolomon
