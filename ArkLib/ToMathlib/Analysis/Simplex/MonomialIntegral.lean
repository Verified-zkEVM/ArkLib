/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Monomial integrals over a simplex

The beta integral evaluates one coordinate of a simplex monomial. Iterating it gives the
factorial formula, with an arbitrary exponent on the slack coordinate as well. These are
ordinary real interval integrals; identifying the repeated integral with a multivariate set
integral is a separate Fubini step for applications that use a volume measure.
-/

@[expose] public section

open MeasureTheory

namespace SimplexIntegration

/-- The monomial beta integral on a nonnegative interval, including the zero-length case. -/
theorem integral_pow_mul_sub_pow (a b : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x : ℝ in (0 : ℝ)..L, x ^ a * (L-x) ^ b) =
      L ^ (a+b+1) * ((a.factorial : ℝ) * b.factorial / (a+b+1).factorial) := by
  rcases hL.eq_or_lt with hzero | hpos
  · subst L
    simp
  have h := Complex.betaIntegral_scaled (a+1) (b+1) hpos
  have he : (a : ℂ) + 1 + (b+1) - 1 = (a+b+1 : ℕ) := by push_cast; ring
  rw [he] at h
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at h
  have hb := Complex.betaIntegral_eq_Gamma_mul_div (a+1) (b+1)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
  have he' : (a : ℂ) + 1 + (b+1) = (a+b+1 : ℕ)+1 := by push_cast; ring
  rw [he', Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at hb
  rw [hb] at h
  have hc : (∫ x : ℝ in (0 : ℝ)..L, (x : ℂ)^a * ((L:ℂ)-x)^b) =
      Complex.ofReal (∫ x : ℝ in (0 : ℝ)..L, x^a * (L-x)^b) := by
    simp only [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      intervalIntegral.integral_ofReal]
  have hh := hc.symm.trans h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow] using hh

/-- Repeated integration over the simplex with coordinate exponents in `as` and slack
exponent `b`. Each step removes one coordinate from the remaining nonnegative budget. -/
noncomputable def monomialIntegral : List ℕ → ℕ → ℝ → ℝ
  | [], b, L => L ^ b
  | a :: as, b, L => ∫ x in (0 : ℝ)..L, x ^ a * monomialIntegral as b (L-x)

/-- Repeated simplex integration gives the factorial monomial formula.

The total exponent includes one integration dimension per coordinate. The slack exponent is
retained in the base case, so this formula treats the slack coordinate on the same footing as
the integrated coordinates. -/
theorem monomialIntegral_eq (as : List ℕ) (b : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    monomialIntegral as b L =
      L ^ (as.length + as.sum + b) *
        (((as.map Nat.factorial).prod : ℝ) * b.factorial /
          (as.length + as.sum + b).factorial) := by
  induction as generalizing L with
  | nil => simp [monomialIntegral, Nat.factorial_ne_zero]
  | cons a as ih =>
    let N := as.length + as.sum + b
    have he : (a :: as).length + (a :: as).sum + b = a + N + 1 := by
      simp [N]; omega
    have hreplace : monomialIntegral (a :: as) b L =
        ∫ x in (0 : ℝ)..L, x ^ a * ((L-x)^N *
          (((as.map Nat.factorial).prod : ℝ) * b.factorial / N.factorial)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hL] at hx
      dsimp only
      rw [ih (sub_nonneg.mpr hx.2)]
    rw [hreplace]
    simp_rw [← mul_assoc]
    rw [intervalIntegral.integral_mul_const, integral_pow_mul_sub_pow a N hL, he]
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    field_simp

end SimplexIntegration
