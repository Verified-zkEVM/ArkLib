/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.MonomialIntegral

/-!
# Acceptance cases for the monomial beta integral

Concrete values of `integral_pow_mul_sub_pow`, including a negative endpoint, checked against
Mathlib's independent `integral_pow` where the slack exponent is zero.
-/

/-- `∫₀¹ x (1 - x) dx = 1 / 6`. -/
example : (∫ x : ℝ in (0 : ℝ)..1, x ^ 1 * (1 - x) ^ 1) = 1 / 6 := by
  rw [integral_pow_mul_one_sub_pow]
  norm_num [Nat.factorial]

/-- `∫₀³ x² dx = 9` from the beta formula, agreeing with `integral_pow`. -/
example : (∫ x : ℝ in (0 : ℝ)..3, x ^ 2 * (3 - x) ^ 0) = 9 := by
  rw [integral_pow_mul_sub_pow]
  norm_num [Nat.factorial]

example : (∫ x : ℝ in (0 : ℝ)..3, x ^ 2) = 9 := by
  rw [integral_pow]
  norm_num

/-- A negative endpoint needs no hypothesis: `∫₀⁻² x dx = 2`, which `integral_pow` confirms. -/
example : (∫ x : ℝ in (0 : ℝ)..(-2), x ^ 1 * (-2 - x) ^ 0) = 2 := by
  rw [integral_pow_mul_sub_pow]
  norm_num [Nat.factorial]

example : (∫ x : ℝ in (0 : ℝ)..(-2), x ^ 1) = 2 := by
  rw [integral_pow]
  norm_num

/-- A zero-length interval gives zero on both sides. -/
example (a b : ℕ) : (∫ x : ℝ in (0 : ℝ)..0, x ^ a * (0 - x) ^ b) = 0 := by
  rw [integral_pow_mul_sub_pow]
  simp
