/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The monomial beta integral

For natural exponents `a` and `b`, the beta integral gives
`∫ x in 0..L, x ^ a * (L - x) ^ b = L ^ (a + b + 1) * (a! * b! / (a + b + 1)!)`.
This is the one-dimensional step of the Dirichlet integral over a simplex, proved in
`ArkLib.ToMathlib.Analysis.Simplex.VolumeIntegral`.

The formula holds for every real `L`, including `L = 0` and `L < 0`. Interval integrals are
oriented, so the substitution `x = L * t` reduces every case to the unit interval.

## Main statements

* `integral_pow_mul_one_sub_pow`: the unit-interval case, derived from Mathlib's
  `Complex.betaIntegral_eq_Gamma_mul_div` at the natural arguments `a + 1` and `b + 1`.
* `integral_pow_mul_sub_pow`: the case of an arbitrary real endpoint `L`.

## References

Ports `SimplexIntegration.integral_pow_mul_sub_pow` from
`ArkLib/ToMathlib/Analysis/Simplex/MonomialIntegral.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source assumed `0 ≤ L` and applied
`Complex.betaIntegral_scaled` directly; here the unit-interval case is a separate public theorem
and the scaling step `intervalIntegral.mul_integral_comp_mul_left` removes the sign hypothesis.
The source's repeated integral `monomialIntegral` and its formula `monomialIntegral_eq` are not
ported: the Fubini recurrence `MeasureTheory.setIntegral_standardSimplex_succ` evaluates the
Lebesgue integral directly, so the list-indexed intermediate has no remaining use.
-/

@[expose] public section

/-- The beta integral with natural exponents on `[0, 1]`:
`∫ x in 0..1, x ^ a * (1 - x) ^ b = a! * b! / (a + b + 1)!`. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ a * (1 - x) ^ b) =
      (a.factorial : ℝ) * b.factorial / (a + b + 1).factorial := by
  have hb := Complex.betaIntegral_eq_Gamma_mul_div (a + 1) (b + 1)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
  have he : (a : ℂ) + 1 + (b + 1) = ((a + b + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [he, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, Complex.betaIntegral] at hb
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at hb
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  exact hb

/-- The beta integral with natural exponents on the interval from `0` to `L`:
`∫ x in 0..L, x ^ a * (L - x) ^ b = L ^ (a + b + 1) * (a! * b! / (a + b + 1)!)`.

No sign condition on `L` is needed: the interval integral is oriented, so for `L < 0` the
substitution `x = L * t` still applies. For `L = 0` both sides vanish. -/
theorem integral_pow_mul_sub_pow (a b : ℕ) (L : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..L, x ^ a * (L - x) ^ b) =
      L ^ (a + b + 1) * ((a.factorial : ℝ) * b.factorial / (a + b + 1).factorial) := by
  rw [← integral_pow_mul_one_sub_pow]
  have h := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := 1)
    (f := fun x ↦ x ^ a * (L - x) ^ b) L
  rw [mul_zero, mul_one] at h
  rw [← h]
  have : ∀ t : ℝ, (L * t) ^ a * (L - L * t) ^ b = L ^ (a + b) * (t ^ a * (1 - t) ^ b) := by
    intro t; rw [show L - L * t = L * (1 - t) by ring, mul_pow, mul_pow, pow_add]; ring
  simp_rw [this, intervalIntegral.integral_const_mul]
  ring
