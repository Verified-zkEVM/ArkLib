/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.RankBudget
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rounding estimates for interpolation rank parameters

The weighted radius is rounded down and the multiplicity is rounded up. These estimates keep
both errors explicit and control the normalized rank parameter `κ`. They depend on the scalar
radius parameter `a`, independently of how a particular interpolation support chooses it.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationRounding

/-- A floor of a radius at least two is positive. -/
theorem floor_pos (R : ℝ) (hR : 2 ≤ R) : 0 < Nat.floor R := by
  have : 1 ≤ Nat.floor R := Nat.le_floor (by norm_num; linarith)
  omega

/-- Reciprocal floor loss, with the full error `2/R` retained. -/
theorem floor_reciprocal_le (R : ℝ) (hR : 2 ≤ R) :
    1 / (Nat.floor R : ℝ) ≤ (1 + 2 / R) / R := by
  have hRp : 0 < R := by linarith
  have hFp : (0 : ℝ) < Nat.floor R := by exact_mod_cast floor_pos R hR
  have hfloor := Nat.lt_floor_add_one R
  apply (div_le_div_iff₀ hFp hRp).mpr
  have haux : 0 ≤ (R - 2) / R := div_nonneg (by linarith) hRp.le
  have hid : (1 + 2 / R) * (R - 1) = R + (R - 2) / R := by
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_left (by linarith : R - 1 ≤
    (Nat.floor R : ℝ)) (by positivity : 0 ≤ 1 + 2 / R)
  nlinarith

/-- The multiplicity ceiling provides the exact lower bound before later estimates. -/
theorem multiplicity_lower (d : ℕ) (H : ℝ) :
    100 * (d : ℝ) ^ 2 * H ≤ (Nat.ceil (100 * (d : ℝ) ^ 2 * H) : ℝ) :=
  Nat.le_ceil _

/-- Floor rounding bounds a nonnegative numerator divided by the width on both sides. -/
theorem floor_ratio_bounds (R N : ℝ) (hR : 2 ≤ R) (hN : 0 ≤ N) :
    N / R ≤ N / (Nat.floor R : ℝ) ∧
      N / (Nat.floor R : ℝ) ≤ N / R * (1 + 2 / R) := by
  have hRp : 0 < R := by linarith
  have hFp : (0 : ℝ) < Nat.floor R := by exact_mod_cast floor_pos R hR
  constructor
  · exact div_le_div_of_nonneg_left hN hFp (Nat.floor_le hRp.le)
  · have h := mul_le_mul_of_nonneg_left (floor_reciprocal_le R hR) hN
    simpa only [div_eq_mul_inv, mul_one, mul_assoc, mul_left_comm, mul_comm] using h

/-- The prescribed radius is large before taking its floor. -/
theorem radius_lower (a H : ℝ) (d m : ℕ) (ha : 1 ≤ a) (hH : 0 < H)
    (hm : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    100 * (d : ℝ) ^ 3 ≤ a * d * m / H := by
  apply (le_div_iff₀ hH).mpr
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h := mul_le_mul_of_nonneg_left hm hd
  have h' := mul_le_mul_of_nonneg_right ha (mul_nonneg hd hm')
  nlinarith

/-- The reciprocal radius error has the paper's explicit cubic bound. -/
theorem radius_error_le (a H : ℝ) (d m : ℕ) (ha : 1 ≤ a) (hH : 0 < H)
    (hd : 0 < d) (hm : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    1 / (a * d * m / H) ≤ 1 / (100 * (d : ℝ) ^ 3) := by
  have hpos : (0 : ℝ) < 100 * (d : ℝ) ^ 3 := by positivity
  exact one_div_le_one_div_of_le hpos (radius_lower a H d m ha hH hm)

/-- Exact lower and upper bounds for κ, including the full width-floor error. -/
theorem kappa_floor_bounds (a H : ℝ) (d m : ℕ)
    (ha : 0 < a) (hH : 0 < H) (hd : 1 ≤ d) (hm : 0 < m)
    (hR : 2 ≤ a * d * m / H) :
    let R := a * d * m / H
    let κ := ((d - 1 : ℕ) : ℝ) * m / Nat.floor R
    H / a * (1 - 1 / d) ≤ κ ∧
      κ ≤ H / a * (1 - 1 / d) * (1 + 2 / R) := by
  dsimp only
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have heq : ((d - 1 : ℕ) : ℝ) * m / (a * d * m / H) =
      H / a * (1 - 1 / d) := by
    rw [Nat.cast_sub hd]
    push_cast
    field_simp
  have h := floor_ratio_bounds (a * d * m / H)
    (((d - 1 : ℕ) : ℝ) * m) hR (by positivity)
  rw [heq] at h
  exact h

/-- The loss from `d-1` absorbs the entire floor error once the radius is at least `2d`. -/
theorem kappa_interval (a H : ℝ) (d m : ℕ)
    (ha : 0 < a) (hH : 0 < H) (hd : 1000 ≤ d) (hm : 0 < m)
    (hR : 2 * (d : ℝ) ≤ a * d * m / H) :
    let κ := ((d - 1 : ℕ) : ℝ) * m / Nat.floor (a * d * m / H)
    999 / 1000 * (H / a) ≤ κ ∧ κ ≤ H / a := by
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hRp : 0 < a * d * m / H := by positivity
  have hb := kappa_floor_bounds a H d m ha hH (by omega) hm (by linarith)
  dsimp only at hb ⊢
  have ht : 0 ≤ H / a := (div_pos hH ha).le
  have hrec : 1 / (d : ℝ) ≤ 1 / 1000 :=
    one_div_le_one_div_of_le (by norm_num) hd'
  constructor
  · have := mul_le_mul_of_nonneg_left
      (by linarith : (999 / 1000 : ℝ) ≤ 1 - 1 / d) ht
    nlinarith [hb.1]
  · have herr : 2 / (a * d * m / H) ≤ 1 / (d : ℝ) := by
      apply (div_le_div_iff₀ hRp hdp).mpr
      simpa using hR
    have hbase : 0 ≤ 1 - 1 / (d : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left herr hbase
    have hs := sq_nonneg (1 / (d : ℝ))
    have hfactor : (1 - 1 / (d : ℝ)) * (1 + 2 / (a * d * m / H)) ≤ 1 := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hfactor ht
    nlinarith [hb.2]

/-- The quadratic multiplicity choice implies the radius condition for the κ interval. -/
theorem radius_ge_twice_order (a H : ℝ) (d m : ℕ)
    (ha : 1 ≤ a) (hH : 0 < H) (hd : 1 ≤ d)
    (hm : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    2 * (d : ℝ) ≤ a * d * m / H := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ d)
  have := radius_lower a H d m ha hH hm
  nlinarith

/-- The binomial shift over the prescribed multiplicity retains its finite bound. -/
theorem binomial_error_le (H : ℝ) (d m : ℕ) (hH : 0 < H) (hm : 0 < m)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    (d.choose 2 : ℝ) / m ≤ 1 / (200 * H) := by
  rw [Nat.cast_choose_two]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < m) (by positivity)).mpr
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- The κ interval implies the required exponent estimate with room in the constant. -/
theorem kappa_exponent_le (κ a H : ℝ) (d m : ℕ)
    (ha : 1 ≤ a) (hH : 0 < H) (hm : 0 < m) (hκ : 0 ≤ κ)
    (hκa : κ ≤ H / a) (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    κ * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + 1 / 100 := by
  have hB := binomial_error_le H d m hH hm hsize
  have ha' : 0 < a := by linarith
  have hκH : κ ≤ H := hκa.trans ((div_le_iff₀ ha').mpr (by nlinarith))
  have hmul := mul_le_mul_of_nonneg_left hB hκ
  have hsmall : κ * (1 / (200 * H)) ≤ 1 / 200 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  nlinarith

/-- The multiplicity lower bound makes the second reciprocal term negligible. -/
theorem kappa_multiplicity_error_le (κ H : ℝ) (d m : ℕ)
    (hH : 0 < H) (hd : 1000 ≤ d) (hm : 0 < m) (hκH : κ ≤ H)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    (d : ℝ) * κ / m ≤ 1 / 1000 := by
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_left hκH (by positivity : (0 : ℝ) ≤ d)
  have hprod : (10 : ℝ) * d ≤ (d : ℝ) ^ 2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hprod hH.le
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < m)).mpr
  nlinarith

/-- A useful scalar form of the last rounding step in the reciprocal κ factor. -/
theorem kappa_reciprocal_factor_le (κ t d m : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) (hm : 0 < m)
    (hlo : 999 / 1000 * t ≤ κ) (herr : d * κ / m ≤ 1 / 1000) :
    1 / κ ^ 2 + d / (m * κ) ≤ 101 / 100 * (1 / t ^ 2) := by
  have hsq : (999 / 1000 * t) ^ 2 ≤ κ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlo 2
  have hfactor : 1 + d * κ / m ≤ 1001 / 1000 := by linarith
  have hid : 1 / κ ^ 2 + d / (m * κ) = (1 + d * κ / m) / κ ^ 2 := by
    field_simp
  rw [hid]
  apply (div_le_iff₀ (sq_pos_of_pos hκ)).mpr
  have hnum : (1001 / 1000 : ℝ) ≤
      101 / 100 * (1 / t ^ 2) * κ ^ 2 := by
    have heq : 101 / 100 * (1 / t ^ 2) * κ ^ 2 =
        (101 / 100 * κ ^ 2) / t ^ 2 := by ring
    rw [heq]
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    have hscale := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 101 / 100)
    have ht2 := sq_nonneg t
    nlinarith
  exact hfactor.trans hnum


/-- The rounded radius and multiplicity satisfy every scalar rank prerequisite. -/
theorem prescribed_kappa_bounds (a H : ℝ) (d : ℕ)
    (ha : 1 ≤ a) (hH : 0 < H) (hd : 1000 ≤ d) :
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let κ := ((d - 1 : ℕ) : ℝ) * m / W
    0 < m ∧ 0 < W ∧ 0 < κ ∧
      999 / 1000 * (H / a) ≤ κ ∧ κ ≤ H / a ∧
      κ * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + 1 / 100 ∧
      (d : ℝ) * κ / m ≤ 1 / 1000 ∧
      1 / κ ^ 2 + (d : ℝ) / (m * κ) ≤ 101 / 100 * (1 / (H / a) ^ 2) := by
  dsimp only
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  let κ := ((d - 1 : ℕ) : ℝ) * m / W
  have hap : 0 < a := by linarith
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hsize
  have hm : 0 < m := by exact_mod_cast hmp
  have hR := InterpolationRounding.radius_ge_twice_order a H d m ha hH (by omega) hsize
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hW : 0 < W := InterpolationRounding.floor_pos _ (by linarith)
  have hpred : 0 < d - 1 := by omega
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hint := InterpolationRounding.kappa_interval a H d m hap hH hd hm hR
  have he := InterpolationRounding.kappa_exponent_le κ a H d m ha hH hm hκ.le hint.2 hsize
  have hκH : κ ≤ H := hint.2.trans ((div_le_iff₀ hap).mpr (by nlinarith))
  have herr := InterpolationRounding.kappa_multiplicity_error_le κ H d m hH hd hm hκH hsize
  have hrec := InterpolationRounding.kappa_reciprocal_factor_le κ (H / a) d m hκ
    (div_pos hH hap) hmp hint.1 herr
  exact ⟨hm, hW, hκ, hint.1, hint.2, he, herr, hrec⟩


/-- Convert the harmonic upper bound and rounding error to a real-power bound. -/
theorem exp_le_rpow (a H E C : ℝ) (d : ℕ) (ha : 1 ≤ a) (hd : 0 < d)
    (hH : H ≤ Real.log d + 3 / 5) (hE : E ≤ H / a + 1 / 100)
    (hC : Real.exp (61 / 100) ≤ C) :
    Real.exp E ≤ C * (d : ℝ) ^ (1 / a) := by
  have hap : 0 < a := by linarith
  have he : E ≤ Real.log d / a + 61 / 100 := by
    have hdiv := (div_le_div_iff_of_pos_right hap).mpr hH
    have hsmall : (3 / 5 : ℝ) / a ≤ 3 / 5 := by
      apply (div_le_iff₀ hap).mpr
      nlinarith
    rw [add_div] at hdiv
    linarith
  have hexp := Real.exp_le_exp.mpr he
  rw [Real.exp_add] at hexp
  have hrpow : Real.exp (Real.log d / a) = (d : ℝ) ^ (1 / a) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [hrpow] at hexp
  have h := mul_le_mul_of_nonneg_left hC
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < d) (1 / a)).le
  exact hexp.trans (by simpa [mul_comm] using h)


/-- Rounding the weighted radius changes its associated simplex mean by at most one. -/
theorem rounded_mean_bounds (a H : ℝ) (d m : ℕ)
    (ha : 0 ≤ a) (hH : 0 < H) (hd : 0 < d) (hHd : H ≤ d) :
    let W := Nat.floor (a * d * m / H)
    a * m - 1 ≤ (W : ℝ) * H / d ∧ (W : ℝ) * H / d ≤ a * m := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hr : 0 ≤ a * d * m / H := by positivity
  have hlo := Nat.floor_le hr
  have hhi := Nat.lt_floor_add_one (a * d * m / H)
  have hup := (le_div_iff₀ hH).mp hlo
  have hdown := (div_lt_iff₀ hH).mp hhi
  constructor
  · apply (le_div_iff₀ hd0).mpr
    nlinarith
  · apply (div_le_iff₀ hd0).mpr
    nlinarith

/-- The scaled radius is at most one quarter under the gap-harmonic inequality. -/
theorem normalized_radius_le_quarter (a H g : ℝ) (d m : ℕ)
    (ha : 0 ≤ a) (hH : 0 < H) (hg : 0 < g) (hd : 0 < d) (hm : 0 < m)
    (hgap : 4 * a ≤ g * H) :
    (Nat.floor (a * d * m / H) : ℝ) / (d * g * m) ≤ 1 / 4 := by
  have hr : 0 ≤ a * d * m / H := by positivity
  have hf := (le_div_iff₀ hH).mp (Nat.floor_le hr)
  have hscale := mul_le_mul_of_nonneg_right hgap
    (show (0 : ℝ) ≤ d * m by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < d * g * m)).mpr
  nlinarith


end ReedSolomon.HiddenDerivative.InterpolationRounding
