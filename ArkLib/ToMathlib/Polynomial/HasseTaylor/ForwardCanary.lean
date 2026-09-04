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

end Polynomial
