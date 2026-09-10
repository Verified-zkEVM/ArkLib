/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.AffinePowerTruncationMachine
public import Mathlib.Data.ZMod.Basic

/-!
# Affine-power execution canaries

The examples distinguish coefficient order, strict truncation, zero-padding, zero exponent and
small-characteristic cancellation. No division or factorial inversion is used by the program.
-/

@[expose] public section

namespace Polynomial.AffinePowerTruncationMachine

/-- Increasing coefficient order and retained trailing zeros over a prime field. -/
example : (power (2 : ZMod 5) 3 5).1 = .done [3, 2, 1, 1, 0] := by decide

/-- Truncation drops high coefficients rather than folding them into the last retained cell. -/
example : (power (2 : ZMod 5) 3 2).1 = .done [3, 2] := by decide

/-- Zero exponent materializes the constant one at the requested physical width. -/
example : (power (7 : ℤ) 0 4).1 = .done [1, 0, 0, 0] := by decide

/-- A pure power first appears exactly when the width exceeds its exponent. -/
example : (power (0 : ℤ) 3 3).1 = .done [0, 0, 0] ∧
    (power (0 : ℤ) 3 4).1 = .done [0, 0, 0, 1] := by decide

/-- Characteristic two cancels the middle coefficient without an inverse of two. -/
example : (power (1 : ZMod 2) 2 4).1 = .done [1, 0, 1, 0] := by decide

/-- Negative scalars are propagated through the recurrence with the correct signs. -/
example : (power (-1 : ℤ) 3 4).1 = .done [-1, 3, -3, 1] := by decide

/-- Width zero still charges loop dispatch and final output. -/
example : power (2 : ℤ) 4 0 = (.done [], 512) := by decide

/-- Insufficient fuel exposes the initialized cell and charges both executed instructions. -/
example : runFuel (2 : ℤ) 2 (.start 3 4) = (.seed 3 3 1 [1], 64) := by decide

end Polynomial.AffinePowerTruncationMachine
