/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.TaylorReconstruction.AffineShift
import Mathlib.Data.ZMod.Basic

/-! Executed translations with mixed terms and degree at least the characteristic. -/

open CPoly CPoly.TaylorReconstruction

namespace TaylorReconstructionTests

private def x : CMvPolynomial 2 (ZMod 3) := CMvPolynomial.X 0
private def y : CMvPolynomial 2 (ZMod 3) := CMvPolynomial.X 1
private def center : Fin 2 → ZMod 3 := ![1, 2]

/-- Kernel-checked inverse over positive characteristic, with no degree guard. -/
example (p : CMvPolynomial 2 (ZMod 3)) : shift (fun i => -center i) (shift center p) = p :=
  shift_neg_shift center p

/-- Execute coefficient checks and inverse recovery across the characteristic boundary. -/
def run : IO Unit := do
  let p := x ^ 3 + x * y + y ^ 2
  let s := shift center p
  -- (x+1)^3 + (x+1)(y+2) + (y+2)^2 = x^3+xy+y^2+2x+2y+1.
  unless s.coeff #m[3, 0] = 1 ∧ s.coeff #m[2, 0] = 0 ∧
      s.coeff #m[1, 1] = 1 ∧ s.coeff #m[0, 2] = 1 ∧
      s.coeff #m[1, 0] = 2 ∧ s.coeff #m[0, 1] = 2 ∧ s.coeff #m[0, 0] = 1 do
    throw (IO.userError "affine shift failed in characteristic three")
  let recovered := shift (fun i => -center i) (shiftToBox 4 center p)
  unless recovered = p do
    throw (IO.userError "inverse box shift failed above characteristic")
  -- Mixed degree reaches precision but each coordinate remains strictly below it.
  unless (shiftToBox 2 center (x * y)).coeff #m[1, 1] = 1 do
    throw (IO.userError "box shift lost mixed degree-two term")
  unless (shift (fun i => -center i) (shiftToBox 2 center (x * y))) = x * y do
    throw (IO.userError "mixed-term inverse shift failed")

end TaylorReconstructionTests
