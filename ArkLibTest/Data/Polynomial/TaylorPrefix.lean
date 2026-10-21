/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.TaylorPrefix
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for finite centered Hasse--Taylor prefixes

These ordinary-import examples cover the empty and successor boundaries, a nonzero center, and
the characteristic-two distinction between Hasse coefficients and iterated ordinary derivatives.
-/

namespace Polynomial

noncomputable section

/-- A nonzero center checks the sign of the inverse translation and the successor term. -/
example :
    centeredCoefficientPrefix (2 : ℤ) (fun i ↦ (i + 1 : ℤ)) 2 =
      C (-3) + C 2 * X := by
  rw [show (2 : ℕ) = 1 + 1 by omega, centeredCoefficientPrefix_succ,
    centeredCoefficientPrefix_succ, centeredCoefficientPrefix_zero]
  norm_num
  ring

/-- Empty prefixes remain valid at arbitrary centers and have the empty Hasse jet. -/
example (a : ZMod 2) (c : ℕ → ZMod 2) :
    centeredCoefficientPrefix a c 0 = 0 ∧
      hasseJet 0 a (centeredCoefficientPrefix a c 0) = 0 := by
  simp

/-- In characteristic two the prescribed quadratic coefficient survives in the Hasse jet, even
though the ordinary derivative of `X²` vanishes. -/
example :
    hasseJet 3 (1 : ZMod 2)
        (centeredCoefficientPrefix 1 (fun i ↦ if i = 2 then 1 else 0) 3) =
      ![0, 0, 1] := by
  rw [hasseJet_centeredCoefficientPrefix]
  funext i
  fin_cases i <;> simp

example :
    derivative
        (centeredCoefficientPrefix (1 : ZMod 2) (fun i ↦ if i = 2 then 1 else 0) 3) =
      0 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [show (3 : ℕ) = 2 + 1 by omega, centeredCoefficientPrefix_succ,
    show (2 : ℕ) = 1 + 1 by omega, centeredCoefficientPrefix_succ,
    centeredCoefficientPrefix_succ, centeredCoefficientPrefix_zero]
  simp [derivative_pow, htwo]

/-- A prefix longer than the requested jet exposes exactly the requested initial coordinates. -/
example :
    hasseJet 2 (3 : ZMod 5)
        (centeredCoefficientPrefix 3 (fun i ↦ (i : ZMod 5)) 4) = ![0, 1] := by
  calc
    _ = fun i : Fin 2 ↦ (i : ZMod 5) :=
      hasseJet_centeredCoefficientPrefix_of_le 3 (fun i ↦ (i : ZMod 5)) (by omega)
    _ = ![0, 1] := by
      funext i
      fin_cases i <;> norm_num

end

end Polynomial
