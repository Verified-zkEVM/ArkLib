/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterRootsSemantics
/-!
# One exponential factor for all centers and jets

The outer alphabet scan multiplies the existing jet count by exactly one alphabet factor.
The remaining terms are the polynomial per-jet budgets of the underlying machines.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CenterRootsMachine

variable {F : Type*} [Field F]

/-- Outer scanning adds one alphabet factor to the jet exponent, with absolute additive overhead. -/
theorem fuel_single_exponent (input : Input F) (D L n : ℕ)
    (hq : 0 < input.alphabet.length) :
    fuel input D L n ≤ input.alphabet.length ^ (input.order + 2) *
      (JetRootsMachine.itemFuel (centerInput input 0) D L n + 32 * (input.order + 2) + 9) + 4 := by
  have hpower : input.alphabet.length ≤ input.alphabet.length ^ (input.order + 2) :=
    le_self_pow (by omega) (by omega)
  simp only [fuel, centerFuel, JetRootsMachine.fuel, centerInput]
  rw [show input.alphabet.length ^ (input.order + 2) =
    input.alphabet.length ^ (input.order + 1) * input.alphabet.length from
      pow_succ _ _] at hpower ⊢
  nlinarith

/-- Pair/cell allocation and reversal retain a single alphabet-to-order exponential factor. -/
theorem work_single_exponent (input : Input F) (D L n : ℕ)
    (hq : 0 < input.alphabet.length) :
    workBound input D L n ≤ input.alphabet.length ^ (input.order + 2) *
      (JetRootsMachine.itemWork (centerInput input 0) D L n +
        3 * JetRootsMachine.itemFuel (centerInput input 0) D L n +
        608 * (input.order + 2) + 59) + 16 := by
  have hpower : input.alphabet.length ≤ input.alphabet.length ^ (input.order + 2) :=
    le_self_pow (by omega) (by omega)
  simp only [workBound, centerWork, JetRootsMachine.workBound, JetRootsMachine.fuel, centerInput]
  rw [show input.alphabet.length ^ (input.order + 2) =
    input.alphabet.length ^ (input.order + 1) * input.alphabet.length from
      pow_succ _ _] at hpower ⊢
  nlinarith

end ReedSolomon.HiddenDerivative.CenterRootsMachine
