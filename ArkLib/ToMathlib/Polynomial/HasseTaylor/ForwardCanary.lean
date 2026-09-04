/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.Forward
import Mathlib.Data.ZMod.Basic

/-!
# Canaries for finite forward Hasse--Taylor truncation

The characteristic-two example is decisive: shifting `X²` forward by one gives `X² + 1`, so
the order-two truncation is `1`; the generic remainder theorem then makes the discarded part
divisible by `X²`.
-/

namespace Polynomial

example : forwardTaylorTruncation 2 (1 : ZMod 2) (X ^ 2) = 1 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have htwoPoly : (2 : (ZMod 2)[X]) = 0 := by
    change C (2 : ZMod 2) = 0
    rw [htwo, C_0]
  rw [X_pow_eq_monomial]
  simp [forwardTaylorTruncation, hasseCoeffAt_apply, hasseDeriv_monomial,
    Finset.sum_range_succ, htwoPoly]

example : forwardTaylorTruncation 3 (0 : ZMod 2) (X ^ 4) = 0 := by
  rw [forwardTaylorTruncation_X_pow]
  simp

/-- A center-composition canary: two unit shifts cancel in characteristic two before
order-two truncation. -/
example :
    forwardTaylorTruncation 2 (1 : ZMod 2) (taylor 1 (X ^ 2)) = 0 := by
  rw [forwardTaylorTruncation_taylor]
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  rw [htwo]
  rw [forwardTaylorTruncation_X_pow]
  simp

/-- An asymmetric center-composition canary: shifting first by `2` and then taking the order-two
truncation at `1` uses center `1 + 2 = 3`, not the inverse shift. -/
example :
    forwardTaylorTruncation 2 (1 : ZMod 5) (taylor 2 X) = C 3 + X := by
  rw [forwardTaylorTruncation_taylor]
  norm_num [forwardTaylorTruncation, Finset.sum_range_succ, hasseCoeffAt_apply]

/-- A high-truncation canary: all three Hasse coefficients retain the shifted quadratic, leaving
both the remainder and its canonical quotient zero. -/
example :
    forwardTaylorRemainder 3 (1 : ZMod 2) (X ^ 2) = 0 ∧
      forwardTaylorQuotient 3 (1 : ZMod 2) (X ^ 2) = 0 := by
  have hp : (X ^ 2 : (ZMod 2)[X]) ∈ degreeLT (ZMod 2) 3 := by
    rw [mem_degreeLT, degree_X_pow]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self 2)
  exact ⟨forwardTaylorRemainder_eq_zero_of_mem_degreeLT 3 1 (X ^ 2) hp,
    forwardTaylorQuotient_eq_zero_of_mem_degreeLT 3 1 (X ^ 2) hp⟩

/-- An affine quotient-factor canary: the `c ^ m = 2²` factor is essential here. -/
example :
    forwardTaylorQuotient 2 (1 : ZMod 5)
      ((taylor 1 (X ^ 3)).comp (C 2 * X)) = 1 + C 3 * X := by
  rw [forwardTaylorQuotient_taylor_comp_C_mul_X]
  ext i
  rw [coeff_C_mul, comp_C_mul_X_coeff, coeff_forwardTaylorQuotient]
  rw [X_pow_eq_monomial]
  by_cases hi : i < 2
  · interval_cases i
    · norm_num [hasseCoeffAt_apply, hasseDeriv_monomial, coeff_add, coeff_one, coeff_X]
      decide
    · norm_num [hasseCoeffAt_apply, hasseDeriv_monomial, coeff_add, coeff_one, coeff_X]
      decide
  · have hchoose : Nat.choose 3 (i + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hi0 : i ≠ 0 := by omega
    have hi1 : 1 ≠ i := by omega
    simp [hasseCoeffAt_apply, hasseDeriv_monomial, hchoose, coeff_add, coeff_one, coeff_X,
      hi0, hi1]

/-- A degree-drop canary: removing orders zero and one from a shifted quartic leaves a quadratic,
and the general `degreeLT` bound records the same strict bound. -/
example :
    (forwardTaylorQuotient 2 (1 : ℤ) (X ^ 4)).natDegree = 2 ∧
      forwardTaylorQuotient 2 (1 : ℤ) (X ^ 4) ∈ degreeLT ℤ 3 := by
  have hle : (forwardTaylorQuotient 2 (1 : ℤ) (X ^ 4)).natDegree ≤ 2 := by
    have h := natDegree_forwardTaylorQuotient_le 2 (1 : ℤ) (X ^ 4)
    rw [natDegree_X_pow] at h
    norm_num at h ⊢
    exact h
  have hcoeff : (forwardTaylorQuotient 2 (1 : ℤ) (X ^ 4)).coeff 2 ≠ 0 := by
    rw [coeff_forwardTaylorQuotient, X_pow_eq_monomial]
    norm_num [hasseCoeffAt_apply, hasseDeriv_monomial]
  have hdegree : (forwardTaylorQuotient 2 (1 : ℤ) (X ^ 4)).natDegree = 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff
  refine ⟨hdegree, forwardTaylorQuotient_mem_degreeLT 2 5 (1 : ℤ) (X ^ 4) ?_⟩
  rw [mem_degreeLT, degree_X_pow]
  exact WithBot.coe_lt_coe.mpr (by omega)

/-- At order zero the quotient is the full shift, so its degree is unchanged. -/
example : (forwardTaylorQuotient 0 (2 : ℤ) (X ^ 4)).natDegree = 4 := by
  rw [forwardTaylorQuotient_zero, natDegree_taylor, natDegree_X_pow]

/-- The zero polynomial has zero quotient at every order. -/
example (m : ℕ) : forwardTaylorQuotient m (2 : ℤ) 0 = 0 := by
  simp [forwardTaylorQuotient, forwardTaylorRemainder, forwardTaylorTruncation,
    hasseCoeffAt_apply]

/-- An asymmetric tail-tower canary: dropping one coefficient and then two more gives the
order-three tail, whose independently computed value is `4 + X` here. -/
example :
    forwardTaylorQuotient 2 0
      (forwardTaylorQuotient 1 (1 : ZMod 5) (X ^ 4)) = C 4 + X := by
  rw [forwardTaylorQuotient_zero_comp]
  ext i
  rw [coeff_forwardTaylorQuotient, X_pow_eq_monomial]
  by_cases hi : i < 2
  · interval_cases i
    · norm_num [hasseCoeffAt_apply, hasseDeriv_monomial, coeff_add, coeff_X]
    · norm_num [hasseCoeffAt_apply, hasseDeriv_monomial, coeff_add, coeff_X]
  · have hchoose : Nat.choose 4 (i + 3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hi0 : i ≠ 0 := by omega
    have hi1 : 1 ≠ i := by omega
    simp [hasseCoeffAt_apply, hasseDeriv_monomial, hchoose, coeff_add, coeff_C, coeff_X,
      hi0, hi1]

/-- The extra tail operation is inert when either added order is zero. -/
example :
    forwardTaylorQuotient 0 0
        (forwardTaylorQuotient 2 (1 : ℤ) (X ^ 4)) =
      forwardTaylorQuotient (2 + 0) (1 : ℤ) (X ^ 4) := by
  exact forwardTaylorQuotient_zero_comp 2 0 1 (X ^ 4)

example :
    forwardTaylorQuotient 2 0
        (forwardTaylorQuotient 0 (1 : ℤ) (X ^ 4)) =
      forwardTaylorQuotient (0 + 2) (1 : ℤ) (X ^ 4) := by
  exact forwardTaylorQuotient_zero_comp 0 2 1 (X ^ 4)

end Polynomial
