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

end Polynomial
