/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Canaries for finite Hasse jets

These examples are intentionally concrete.  In characteristic two the ordinary derivative of
`X²` vanishes, while its second Hasse derivative is one; this catches accidental replacement of
Hasse derivatives by iterated ordinary derivatives.
-/

namespace Polynomial

/-- Iterating the ordinary derivative also loses the order-two coefficient in characteristic two. -/
example : derivative^[2] (X ^ 2 : (ZMod 2)[X]) = 0 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp [Function.iterate_succ_apply', derivative_pow, htwo]

example : hasseJet 3 (0 : ZMod 2) (X ^ 2) = ![0, 0, 1] := by
  funext i
  fin_cases i
  · simp
  · simp
  · rw [X_pow_eq_monomial]
    simp

/-- A point/index canary: the first Hasse coefficient of `X²` at `1` in characteristic three is
`2`, while the zeroth coefficient is `1`. -/
example : hasseJet 2 (1 : ZMod 3) (X ^ 2) 1 = 2 := by
  norm_num [hasseJet_apply, hasseDeriv_monomial]

/-- A shift-sign canary: shifting `X` forward by `2` and taking its jet at `1` gives constant
coefficient `3`, not `-1`. -/
example : hasseJet 2 (1 : ZMod 5) (taylor 2 X) = ![3, 1] := by
  funext i
  fin_cases i <;> norm_num [hasseJet_apply, taylor_X]

/-- A map/shift commutation canary: the integral jet `[1, 2, 1]` of `(X + 1)²` maps to
`[1, 0, 1]` in characteristic two. -/
example :
    (fun i ↦ (Int.castRingHom (ZMod 2))
      (hasseJet 3 (0 : ℤ) (taylor 1 (X ^ 2)) i)) = ![1, 0, 1] := by
  calc
    _ = hasseJet 3 ((Int.castRingHom (ZMod 2)) 0 + (Int.castRingHom (ZMod 2)) 1)
        ((X ^ 2 : ℤ[X]).map (Int.castRingHom (ZMod 2))) :=
      map_hasseJet_taylor (Int.castRingHom (ZMod 2)) 3 1 0 (X ^ 2)
    _ = ![1, 0, 1] := by
      funext i
      fin_cases i
      · norm_num [hasseJet_apply, hasseDeriv_monomial]
      · have hone : (1 + 1 : ZMod 2) = 0 := by decide
        simpa [hasseJet_apply, hasseDeriv_monomial] using hone
      · rw [hasseJet_apply, X_pow_eq_monomial]
        simp [hasseDeriv_monomial]

/-- An affine-scaling canary: for `p = X²`, offset `1`, scale `2`, and observation point `1`,
the translated point is `3` and Hasse orders scale by `1, 2, 4`. -/
example :
    hasseJet 3 (1 : ZMod 5) ((taylor 1 (X ^ 2)).comp (C 2 * X)) = ![4, 2, 4] := by
  rw [hasseJet_taylor_comp_C_mul_X]
  funext i
  fin_cases i
  · norm_num [hasseJet_apply, hasseDeriv_monomial]
    decide
  · norm_num [hasseJet_apply, hasseDeriv_monomial]
    decide
  · rw [hasseJet_apply, X_pow_eq_monomial]
    simp only [mul_one, hasseDeriv_monomial, tsub_self, Nat.choose_self, Nat.cast_one,
      monomial_zero_left, map_one, eval_one, one_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.reduceFinMk, Matrix.cons_val]
    decide

end Polynomial
