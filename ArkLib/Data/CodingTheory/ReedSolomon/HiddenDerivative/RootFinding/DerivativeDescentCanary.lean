/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DerivativeDescent
import Mathlib.Data.ZMod.Basic

/-!
# Boundary canaries for characteristic-safe derivative descent

These examples distinguish the strict below-characteristic hypothesis from its false weak
variant. They also record the sharp positivity boundary for the root-specialization weights.
-/

namespace ReedSolomon
namespace HiddenDerivative
namespace DerivativeDescentCanary

noncomputable section

private def safePolynomial : DifferentialPolynomial (ZMod 3) 0 :=
  MvPolynomial.X (some (0 : Fin 1)) ^ 2

/-- A quadratic jet variable survives one formal derivative in characteristic three. -/
example : jetDerivative safePolynomial 0 1 ≠ 0 := by
  rw [show jetDerivative safePolynomial 0 1 =
      (2 : MvPolynomial (JetVariable 0) (ZMod 3)) * MvPolynomial.X (some 0) by
    simp [safePolynomial, jetDerivative, MvPolynomial.iteratePDeriv]]
  intro hzero
  have heval := congrArg (MvPolynomial.eval fun _ ↦ (1 : ZMod 3)) hzero
  norm_num at heval
  exact (by decide : (2 : ZMod 3) ≠ 0) heval

private def boundaryPolynomial : DifferentialPolynomial (ZMod 2) 0 :=
  MvPolynomial.X (some (0 : Fin 1)) ^ 2

/-- The individual degree reaches, but does not lie below, the characteristic. -/
example : jetDegree boundaryPolynomial 0 = ringChar (ZMod 2) := by
  simp [boundaryPolynomial, jetDegree, ZMod.ringChar_zmod_n]

/-- Replacing the strict characteristic bound by a weak one would make descent false. -/
example : jetDerivative boundaryPolynomial 0 1 = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [show jetDerivative boundaryPolynomial 0 1 =
      (2 : MvPolynomial (JetVariable 0) (ZMod 2)) * MvPolynomial.X (some 0) by
    simp [boundaryPolynomial, jetDerivative, MvPolynomial.iteratePDeriv]]
  have htwoPolynomial : (2 : MvPolynomial (JetVariable 0) (ZMod 2)) = 0 := by
    change MvPolynomial.C (2 : ZMod 2) = 0
    rw [htwo]
    simp
  rw [htwoPolynomial, zero_mul]

/-- The top jet weight vanishes at the rejected boundary `D = d`. -/
example : differentialWeight (d := 2) 2 (some (Fin.last 2)) = 0 := by
  simp

/-- Moving to the required boundary `d < D` makes the top jet weight positive. -/
example : differentialWeight (d := 2) 3 (some (Fin.last 2)) = 1 := by
  simp [differentialWeight]

end

end DerivativeDescentCanary
end HiddenDerivative
end ReedSolomon
