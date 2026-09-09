/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Capacity
import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds
/-! # The capacity contract's harmonic parameter -/

namespace ReedSolomon

/-- The contract harmonic number is the real cast of Mathlib's harmonic number. -/
theorem harmonicNumber_eq_harmonic (r : ℕ) : harmonicNumber r = (harmonic r : ℝ) := by
  simp [harmonicNumber, harmonic]

end ReedSolomon
