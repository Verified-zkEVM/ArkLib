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

end Polynomial
