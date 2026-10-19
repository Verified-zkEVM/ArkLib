/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Algebra.Order.Floor.Ratio
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.GCongr

/-!
# Rounding estimates for the interpolation rank parameter

The weighted-support interpolation of the hidden-derivative list decoder fixes a real scale
`H > 0`, a real radius factor `a ≥ 1` and a derivative order `d`, and rounds the multiplicity up
and the weighted radius down:
`m = ⌈100 d ^ 2 H⌉₊` and `W = ⌊a d m / H⌋₊`. The local rank estimate is governed by
`κ = (d - 1) m / W`. Before rounding the radius, `(d - 1) m / (a d m / H) = (H / a) (1 - 1 / d)`.
This file bounds the error of both roundings explicitly.

The individual estimates are stated for an arbitrary multiplicity `m` with `C d ^ 2 H ≤ m`, for a
constant `C`, and an arbitrary order `d`:

* `radius_lower`, `radius_ge_twice_order`: the unrounded radius `R = a d m / H` is at least
  `C d ^ 3`, hence at least `2 d` once `2 ≤ C` and `1 ≤ d`.
* `kappa_floor_bounds`: `(H / a) (1 - 1 / d) ≤ κ ≤ (H / a) (1 - 1 / d) (1 + 2 / R)` for `R ≥ 1`.
* `kappa_interval`: `(1 - 1 / d) (H / a) ≤ κ ≤ H / a` once `R ≥ 2 d`; the loss `1 - 1 / d`
  absorbs the floor error `1 + 2 / R ≤ 1 + 1 / d`.
* `binomial_error_le`, `kappa_exponent_le`: `C(d, 2) / m ≤ 1 / (2 C H)`, hence
  `κ (1 + C(d, 2) / m) ≤ H / a + 1 / (2 C)`.
* `kappa_multiplicity_error_le`: `d κ / m ≤ 1 / (C d)`.
* `kappa_reciprocal_factor_le`: from `λ t ≤ κ` and `d κ / m ≤ ε`,
  `1 / κ ^ 2 + d / (m κ) ≤ (1 + ε) / λ ^ 2 · (1 / t ^ 2)`.

`prescribed_kappa_bounds` combines them for the prescribed `m` and `W` with `C = 100` and
`d ≥ 1000`, giving the constants `999 / 1000`, `1 / 100`, `1 / 1000` and `101 / 100`.

## Main statements

* `InterpolationRounding.kappa_floor_bounds`, `InterpolationRounding.kappa_interval`
* `InterpolationRounding.kappa_exponent_le`, `InterpolationRounding.kappa_multiplicity_error_le`,
  `InterpolationRounding.kappa_reciprocal_factor_le`
* `InterpolationRounding.prescribed_kappa_bounds`
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationRounding

/-- A multiplicity `m ≥ C d ^ 2 H` makes the unrounded radius at least `C d ^ 3`:
`C d ^ 3 ≤ a d m / H`. The hypothesis `1 ≤ a` gives `a d m ≥ d m`; `0 < H` is needed to clear the
denominator. -/
theorem radius_lower (C a H : ℝ) (d m : ℕ) (ha : 1 ≤ a) (hH : 0 < H)
    (hm : C * (d : ℝ) ^ 2 * H ≤ m) :
    C * (d : ℝ) ^ 3 ≤ a * d * m / H := by
  rw [le_div_iff₀ hH]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := mul_le_mul_of_nonneg_left hm hd
  have h' := mul_le_mul_of_nonneg_right ha (mul_nonneg hd (Nat.cast_nonneg m))
  nlinarith

/-- For `2 ≤ C` and `1 ≤ d`, a multiplicity `m ≥ C d ^ 2 H` makes the unrounded radius at least
`2 d`, the condition of `kappa_interval`. -/
theorem radius_ge_twice_order (C a H : ℝ) (d m : ℕ) (hC : 2 ≤ C) (ha : 1 ≤ a) (hH : 0 < H)
    (hd : 1 ≤ d) (hm : C * (d : ℝ) ^ 2 * H ≤ m) :
    2 * (d : ℝ) ≤ a * d * m / H := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcube : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith
  have h := radius_lower C a H d m ha hH hm
  nlinarith

/-- The floor error of `κ = (d - 1) m / ⌊R⌋₊` for `R = a d m / H ≥ 1`:
`(H / a) (1 - 1 / d) ≤ κ ≤ (H / a) (1 - 1 / d) (1 + 2 / R)`. The value at the unrounded radius is
`(d - 1) m / R = (H / a) (1 - 1 / d)`, which needs `a, H, d, m` nonzero. -/
theorem kappa_floor_bounds (a H : ℝ) (d m : ℕ)
    (ha : 0 < a) (hH : 0 < H) (hd : 1 ≤ d) (hm : 0 < m)
    (hR : 1 ≤ a * d * m / H) :
    let R := a * d * m / H
    let κ := ((d - 1 : ℕ) : ℝ) * m / Nat.floor R
    H / a * (1 - 1 / d) ≤ κ ∧
      κ ≤ H / a * (1 - 1 / d) * (1 + 2 / R) := by
  dsimp only
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have heq : ((d - 1 : ℕ) : ℝ) * m / (a * d * m / H) = H / a * (1 - 1 / d) := by
    rw [Nat.cast_sub hd]
    push_cast
    field_simp
  have h := Nat.div_floor_bounds hR (N := ((d - 1 : ℕ) : ℝ) * m) (by positivity)
  rw [heq] at h
  exact h

/-- Once the unrounded radius `R = a d m / H` is at least `2 d`,
`(1 - 1 / d) (H / a) ≤ κ ≤ H / a` for `κ = (d - 1) m / ⌊R⌋₊`. The upper bound holds because the
floor error `1 + 2 / R ≤ 1 + 1 / d` is absorbed by the loss `1 - 1 / d`:
`(1 - 1 / d) (1 + 1 / d) = 1 - 1 / d ^ 2 ≤ 1`. -/
theorem kappa_interval (a H : ℝ) (d m : ℕ)
    (ha : 0 < a) (hH : 0 < H) (hd : 1 ≤ d) (hm : 0 < m)
    (hR : 2 * (d : ℝ) ≤ a * d * m / H) :
    let κ := ((d - 1 : ℕ) : ℝ) * m / Nat.floor (a * d * m / H)
    (1 - 1 / (d : ℝ)) * (H / a) ≤ κ ∧ κ ≤ H / a := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hRp : 0 < a * d * m / H := by positivity
  have hb := kappa_floor_bounds a H d m ha hH hd hm (by linarith)
  dsimp only at hb ⊢
  have ht : 0 ≤ H / a := (div_pos hH ha).le
  refine ⟨by simpa [mul_comm] using hb.1, ?_⟩
  have herr : 2 / (a * d * m / H) ≤ 1 / (d : ℝ) := by
    rw [div_le_div_iff₀ hRp hdp]
    simpa only [one_mul] using hR
  have hrec : 1 / (d : ℝ) ≤ 1 := by
    rw [div_le_one hdp]
    exact hd'
  have hbase : 0 ≤ 1 - 1 / (d : ℝ) := sub_nonneg.mpr hrec
  have hfactor : (1 - 1 / (d : ℝ)) * (1 + 2 / (a * d * m / H)) ≤ 1 := by
    calc
      (1 - 1 / (d : ℝ)) * (1 + 2 / (a * d * m / H)) ≤
          (1 - 1 / (d : ℝ)) * (1 + 1 / (d : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [add_comm] using add_le_add_left herr (1 : ℝ)) hbase
      _ = 1 - (1 / (d : ℝ)) ^ 2 := by ring
      _ ≤ 1 := sub_le_self _ (sq_nonneg _)
  have hupper : H / a * ((1 - 1 / (d : ℝ)) *
      (1 + 2 / (a * d * m / H))) ≤ H / a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor ht
  have hbound : ((d - 1 : ℕ) : ℝ) * m / Nat.floor (a * d * m / H) ≤
      H / a * ((1 - 1 / (d : ℝ)) * (1 + 2 / (a * d * m / H))) := by
    simpa only [mul_assoc] using hb.2
  exact hbound.trans hupper

/-- A multiplicity `m ≥ C d ^ 2 H` makes the binomial shift small: `C(d, 2) / m ≤ 1 / (2 C H)`,
because `C(d, 2) ≤ d ^ 2 / 2`. The hypotheses `0 < C`, `0 < H` and `0 < m` keep every denominator
positive. -/
theorem binomial_error_le (C H : ℝ) (d m : ℕ) (hC : 0 < C) (hH : 0 < H) (hm : 0 < m)
    (hsize : C * (d : ℝ) ^ 2 * H ≤ m) :
    (d.choose 2 : ℝ) / m ≤ 1 / (2 * C * H) := by
  rw [Nat.cast_choose_two, div_le_div_iff₀ (by positivity : (0 : ℝ) < m) (by positivity)]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdCH : 0 ≤ (d : ℝ) * C * H := by positivity
  nlinarith

/-- If `0 ≤ κ ≤ H / a` with `a ≥ 1` and `m ≥ C d ^ 2 H`, then
`κ (1 + C(d, 2) / m) ≤ H / a + 1 / (2 C)`. The extra term is `κ C(d, 2) / m ≤ H / (2 C H)`. -/
theorem kappa_exponent_le (C κ a H : ℝ) (d m : ℕ) (hC : 0 < C)
    (ha : 1 ≤ a) (hH : 0 < H) (hm : 0 < m) (hκ : 0 ≤ κ)
    (hκa : κ ≤ H / a) (hsize : C * (d : ℝ) ^ 2 * H ≤ m) :
    κ * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + 1 / (2 * C) := by
  have hB := binomial_error_le C H d m hC hH hm hsize
  have hκH : κ ≤ H := hκa.trans (div_le_self hH.le ha)
  have hmul := mul_le_mul_of_nonneg_left hB hκ
  have hsmall : κ * (1 / (2 * C * H)) ≤ 1 / (2 * C) :=
    calc κ * (1 / (2 * C * H)) ≤ H * (1 / (2 * C * H)) :=
          mul_le_mul_of_nonneg_right hκH (by positivity)
      _ = 1 / (2 * C) := by field_simp
  have hexp : κ * (1 + (d.choose 2 : ℝ) / m) = κ + κ * ((d.choose 2 : ℝ) / m) := by ring
  linarith

/-- If `κ ≤ H` and `m ≥ C d ^ 2 H` with `C, d, m > 0`, then `d κ / m ≤ 1 / (C d)`, because
`d κ C d ≤ C d ^ 2 H ≤ m`. No sign condition on `H` or `κ` is needed. -/
theorem kappa_multiplicity_error_le (C κ H : ℝ) (d m : ℕ) (hC : 0 < C) (hd : 0 < d) (hm : 0 < m)
    (hκH : κ ≤ H)
    (hsize : C * (d : ℝ) ^ 2 * H ≤ m) :
    (d : ℝ) * κ / m ≤ 1 / (C * d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < m) (by positivity)]
  have hmul := mul_le_mul_of_nonneg_left hκH (by positivity : (0 : ℝ) ≤ C * (d : ℝ) ^ 2)
  nlinarith

/-- If `λ t ≤ κ` with `λ, t, κ > 0`, and `d κ / m ≤ ε` with `d ≥ 0`, `m > 0`, then
`1 / κ ^ 2 + d / (m κ) ≤ (1 + ε) / λ ^ 2 · (1 / t ^ 2)`. The left side equals
`(1 + d κ / m) / κ ^ 2`. The hypothesis `0 ≤ d` makes `1 + ε` nonnegative, which is needed to
replace `κ ^ 2` by the smaller `(λ t) ^ 2` in the denominator. -/
theorem kappa_reciprocal_factor_le (κ t d m lam ε : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) (hm : 0 < m) (hlam : 0 < lam) (hd : 0 ≤ d)
    (hlo : lam * t ≤ κ) (herr : d * κ / m ≤ ε) :
    1 / κ ^ 2 + d / (m * κ) ≤ (1 + ε) / lam ^ 2 * (1 / t ^ 2) := by
  have hid : 1 / κ ^ 2 + d / (m * κ) = (1 + d * κ / m) / κ ^ 2 := by
    field_simp
  have hε : 0 ≤ 1 + ε := by
    have : 0 ≤ d * κ / m := by positivity
    linarith
  rw [hid]
  calc (1 + d * κ / m) / κ ^ 2 ≤ (1 + ε) / κ ^ 2 := by gcongr
    _ ≤ (1 + ε) / (lam * t) ^ 2 := by gcongr
    _ = (1 + ε) / lam ^ 2 * (1 / t ^ 2) := by rw [mul_pow]; field_simp

/-- For the prescribed multiplicity `m = ⌈100 d ^ 2 H⌉₊` and radius `W = ⌊a d m / H⌋₊`, with
`a ≥ 1`, `H > 0` and `d ≥ 1000`, the parameter `κ = (d - 1) m / W` satisfies every scalar
prerequisite of the normalized rank estimate: `m, W, κ > 0`,
`(999 / 1000) (H / a) ≤ κ ≤ H / a`, `κ (1 + C(d, 2) / m) ≤ H / a + 1 / 100`,
`d κ / m ≤ 1 / 1000` and `1 / κ ^ 2 + d / (m κ) ≤ (101 / 100) / (H / a) ^ 2`. -/
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
  intro m W κ
  have hap : 0 < a := by linarith
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hsize
  have hm : 0 < m := by exact_mod_cast hmp
  have hR := radius_ge_twice_order 100 a H d m (by norm_num) ha hH (by omega) hsize
  have hW : 0 < W := Nat.floor_pos.mpr (by linarith)
  have hκ : 0 < κ := by
    have : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (by omega : 0 < d - 1)
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hint := kappa_interval a H d m hap hH (by omega) hm hR
  have hHa : 0 < H / a := div_pos hH hap
  have hlo : 999 / 1000 * (H / a) ≤ κ := by
    have hrec : 1 / (d : ℝ) ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hd'
    have := mul_le_mul_of_nonneg_right (by linarith : (999 / 1000 : ℝ) ≤ 1 - 1 / d) hHa.le
    exact this.trans hint.1
  have he := kappa_exponent_le 100 κ a H d m (by norm_num) ha hH hm hκ.le hint.2 hsize
  have hκH : κ ≤ H := hint.2.trans (div_le_self hH.le ha)
  have herr := kappa_multiplicity_error_le 100 κ H d m (by norm_num) (by omega) hm hκH hsize
  have herr' : (d : ℝ) * κ / m ≤ 1 / 1000 :=
    herr.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hrec := kappa_reciprocal_factor_le κ (H / a) d m (999 / 1000) (1 / 1000) hκ hHa hmp
    (by norm_num) (Nat.cast_nonneg d) hlo herr'
  refine ⟨hm, hW, hκ, hlo, hint.2, by linarith, herr',
    hrec.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))⟩

end ReedSolomon.HiddenDerivative.InterpolationRounding
