/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RankRounding

/-!
# Acceptance cases for the rank rounding estimates

A small instance of `kappa_floor_bounds` where the lower bound is attained, the case showing that
its hypothesis `1 ≤ R` is needed, and `kappa_interval`, `binomial_error_le`,
`kappa_exponent_le`, `kappa_multiplicity_error_le` and `kappa_reciprocal_factor_le` specialized to
`C = 100`, `d ≥ 1000` and the constants `999 / 1000`, `1 / 1000` and `101 / 100`.
-/

open ReedSolomon.HiddenDerivative.InterpolationRounding

/-- `a = H = 1`, `d = 2` and any `m > 0`: `R = 2 m` and `κ = m / ⌊2 m⌋₊`, and the theorem gives
`1 / 2 ≤ κ ≤ 1 / 2 + 1 / (2 m)`. Since `R` is an integer, `κ = 1 / 2` and the lower bound is
attained. -/
example (m : ℕ) (hm : 0 < m) :
    (1 / 2 : ℝ) ≤ ((2 - 1 : ℕ) : ℝ) * m / ⌊(1 : ℝ) * (2 : ℕ) * m / 1⌋₊ ∧
      ((2 - 1 : ℕ) : ℝ) * m / ⌊(1 : ℝ) * (2 : ℕ) * m / 1⌋₊ ≤ 1 / 2 + 1 / (2 * m) ∧
      ((2 - 1 : ℕ) : ℝ) * m / ⌊(1 : ℝ) * (2 : ℕ) * m / 1⌋₊ = 1 / 2 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hlo, hhi⟩ := kappa_floor_bounds 1 1 2 m (by norm_num) (by norm_num) (by norm_num) hm
    (by norm_num; linarith)
  have hf : ⌊(1 : ℝ) * (2 : ℕ) * m / 1⌋₊ = 2 * m := by
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast
    constructor <;> linarith
  refine ⟨by norm_num at hlo ⊢; exact hlo, ?_, ?_⟩
  · refine hhi.trans_eq ?_
    field_simp
    norm_num
    ring
  · rw [hf]
    push_cast
    field_simp

/-- The hypothesis `1 ≤ R` of `kappa_floor_bounds` is needed: for `a = 1`, `H = 4`, `d = 2`,
`m = 1` the ratio `R = 1 / 2` has floor `0`, so `κ = 0` while the lower bound is `2`. -/
example : ¬ ((4 : ℝ) / 1 * (1 - 1 / (2 : ℕ)) ≤
    ((2 - 1 : ℕ) : ℝ) * (1 : ℕ) / ⌊(1 : ℝ) * (2 : ℕ) * (1 : ℕ) / 4⌋₊) := by
  rw [Nat.floor_eq_zero.mpr (by norm_num)]
  norm_num

/-- `kappa_interval` for `d ≥ 1000`: the lower bound is at least
`999 / 1000 (H / a)`. -/
example (a H : ℝ) (d m : ℕ) (ha : 0 < a) (hH : 0 < H) (hd : 1000 ≤ d) (hm : 0 < m)
    (hR : 2 * (d : ℝ) ≤ a * d * m / H) :
    let κ := ((d - 1 : ℕ) : ℝ) * m / Nat.floor (a * d * m / H)
    999 / 1000 * (H / a) ≤ κ ∧ κ ≤ H / a := by
  obtain ⟨hlo, hhi⟩ := kappa_interval a H d m ha hH (by omega) hm hR
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : 1 / (d : ℝ) ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hd'
  refine ⟨le_trans ?_ hlo, hhi⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- `binomial_error_le` and `kappa_exponent_le` with `C = 100`. -/
example (κ a H : ℝ) (d m : ℕ) (ha : 1 ≤ a) (hH : 0 < H) (hm : 0 < m) (hκ : 0 ≤ κ)
    (hκa : κ ≤ H / a) (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    (d.choose 2 : ℝ) / m ≤ 1 / (200 * H) ∧
      κ * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + 1 / 100 := by
  have hb := binomial_error_le 100 H d m (by norm_num) hH hm hsize
  have he := kappa_exponent_le 100 κ a H d m (by norm_num) ha hH hm hκ hκa hsize
  refine ⟨by norm_num at hb ⊢; exact hb, by norm_num at he ⊢; linarith⟩

/-- `kappa_multiplicity_error_le`: `C = 100` and `d ≥ 1000` give `1 / 1000`. -/
example (κ H : ℝ) (d m : ℕ) (hd : 1000 ≤ d) (hm : 0 < m) (hκH : κ ≤ H)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    (d : ℝ) * κ / m ≤ 1 / 1000 := by
  refine (kappa_multiplicity_error_le 100 κ H d m (by norm_num) (by omega) hm hκH hsize).trans ?_
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

/-- `kappa_reciprocal_factor_le`: `λ = 999 / 1000` and `ε = 1 / 1000` give the
factor `(1 + 1 / 1000) / (999 / 1000) ^ 2 ≤ 101 / 100`. -/
example (κ t d m : ℝ) (hκ : 0 < κ) (ht : 0 < t) (hm : 0 < m) (hd : 0 ≤ d)
    (hlo : 999 / 1000 * t ≤ κ) (herr : d * κ / m ≤ 1 / 1000) :
    1 / κ ^ 2 + d / (m * κ) ≤ 101 / 100 * (1 / t ^ 2) := by
  refine (kappa_reciprocal_factor_le κ t d m (999 / 1000) (1 / 1000) hκ ht hm (by norm_num) hd
    hlo herr).trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))

/-- `prescribed_kappa_bounds` at `a = H = 1`, `d = 1000`: the multiplicity is
`⌈100 · 1000 ^ 2⌉₊ = 10 ^ 8`, and `κ ≤ 1`. -/
example : ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ = 10 ^ 8 ∧
    ((1000 - 1 : ℕ) : ℝ) * ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ /
      ⌊(1 : ℝ) * (1000 : ℕ) * ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ / 1⌋₊ ≤ 1 / 1 := by
  obtain ⟨-, -, -, -, hhi, -⟩ := prescribed_kappa_bounds 1 1 1000 le_rfl one_pos le_rfl
  refine ⟨?_, hhi⟩
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num
