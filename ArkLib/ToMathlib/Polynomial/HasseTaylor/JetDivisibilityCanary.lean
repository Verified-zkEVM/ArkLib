/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.JetDivisibility
import Mathlib.Data.ZMod.Basic

/-!
# Canaries for finite Hasse jets and local divisibility

These examples exercise the boundary order and a small-characteristic double-contact case.
-/

namespace Polynomial

/-- Order zero imposes no coordinates and corresponds to divisibility by one. -/
example (p q : (ZMod 2)[X]) (a : ZMod 2) :
    (X - C a) ^ 0 ∣ p - q ↔ hasseJet 0 a p = hasseJet 0 a q :=
  X_sub_C_pow_dvd_sub_iff_hasseJet_eq p q a 0

/-- In characteristic two, `X²` and zero have equal orders-zero-and-one jets at the origin,
exactly as witnessed by the double root factor. -/
example :
    (X - C (0 : ZMod 2)) ^ 2 ∣ (X ^ 2 - 0) ↔
      hasseJet 2 (0 : ZMod 2) (X ^ 2) = hasseJet 2 (0 : ZMod 2) 0 :=
  X_sub_C_pow_dvd_sub_iff_hasseJet_eq (X ^ 2) 0 0 2

end Polynomial
