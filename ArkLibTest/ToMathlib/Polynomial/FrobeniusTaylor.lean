/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.FrobeniusTaylor
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance client for `ArkLib.ToMathlib.Polynomial.FrobeniusTaylor`

Over `ZMod 2` the theorems compute `(X + 1) ^ 2 = X ^ 2 + 1` and the vanishing of its linear
coefficient. Over `ℤ` the conclusion of `taylor_expand_expChar_pow` fails for `P = X`, `t = 1`
and exponent `2`, so the exponential-characteristic hypothesis is needed. The special cases over a
commutative ring are derived at the end.
-/

open Polynomial

namespace FrobeniusTaylorTest

/-- Over `ZMod 2`, translating `X ^ 2` by `1` gives `X ^ 2 + 1`. -/
example : taylor (1 : ZMod 2) (expand (ZMod 2) 2 X) = X ^ 2 + 1 := by
  have h := taylor_expand_expChar_pow (R := ZMod 2) 2 1 X 1
  simp only [pow_one, one_pow] at h
  rw [h, taylor_X, map_add, expand_X, expand_C, C_1]

/-- Over `ZMod 2`, the linear Taylor coefficient of `X ^ 2` at `1` vanishes. -/
example : (taylor (1 : ZMod 2) (expand (ZMod 2) 2 X)).coeff 1 = 0 := by
  have h := coeff_taylor_expand_expChar_pow_eq_zero (R := ZMod 2) 2 1 X 1 (r := 1)
  simpa using h

/-- Over `ZMod 2`, the coefficient at index `2 * 1` is the first Hasse derivative of `X` at
`1 ^ 2`, which is `1`. -/
example : (taylor (1 : ZMod 2) (expand (ZMod 2) 2 X)).coeff 2 = 1 := by
  have h := coeff_taylor_expand_expChar_pow_mul (R := ZMod 2) 2 1 X 1 1
  simpa [hasseDeriv_X] using h

/-- Exponential characteristic `1`: over `ℚ` the statement specializes with `p = 1`, where the
pullback is the identity. -/
example (P : ℚ[X]) (t : ℚ) (e : ℕ) :
    taylor t (expand ℚ (1 ^ e) P) = expand ℚ (1 ^ e) (taylor (t ^ (1 ^ e)) P) :=
  taylor_expand_expChar_pow 1 e P t

/-- Boundary: over `ℤ`, whose exponential characteristic is `1`, the identity fails for the
exponent `2`. Evaluating both sides at `1` gives `4` and `2`. -/
example : taylor (1 : ℤ) (expand ℤ 2 X) ≠ expand ℤ 2 (taylor (1 ^ 2) X) := by
  intro h
  have h1 := congrArg (eval 1) h
  simp only [taylor_eval, expand_eval, eval_X, one_pow] at h1
  norm_num at h1

section CommRing

variable {R : Type*} [CommRing R] (p e : ℕ) [ExpChar R p]

/-- `taylor_expand_expChar_pow` over a commutative ring. -/
example (P : R[X]) (t : R) :
    taylor t (expand R (p ^ e) P) = expand R (p ^ e) (taylor (t ^ (p ^ e)) P) :=
  taylor_expand_expChar_pow p e P t

/-- `coeff_taylor_expand_expChar_pow_mul` over a commutative ring. -/
example (P : R[X]) (t : R) (r : ℕ) :
    (taylor t (expand R (p ^ e) P)).coeff ((p ^ e) * r) = (hasseDeriv r P).eval (t ^ (p ^ e)) :=
  coeff_taylor_expand_expChar_pow_mul p e P t r

/-- `coeff_taylor_expand_expChar_pow_eq_zero` over a commutative ring. -/
example (P : R[X]) (t : R) (r : ℕ) (hr : ¬p ^ e ∣ r) :
    (taylor t (expand R (p ^ e) P)).coeff r = 0 :=
  coeff_taylor_expand_expChar_pow_eq_zero p e P t hr

end CommRing

end FrobeniusTaylorTest
