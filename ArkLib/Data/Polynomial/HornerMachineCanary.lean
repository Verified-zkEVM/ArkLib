/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.HornerMachine

/-!
# Closed Horner-machine boundary and mutation checks

These kernel-checked executions use natural scalars, an instance of the machine's semiring
interface. They exercise the actual interpreter rather than replaying its correctness theorem.
The asymmetric coefficients distinguish reversed order and a copied final coefficient. Empty
input and zero coefficients check termination overhead and work independent of coefficient value.
The final mutant interchanges addition and multiplication while retaining the same instruction
count; its different result detects the wrong arithmetic order.
-/

@[expose] public section

namespace Polynomial.HornerMachine

/-- Evaluation of `2X² + 3X + 5` at four, including every operation category. -/
example : runFuel hornerCode (4 : ℕ) 12 (.running 0 [2, 3, 5] 0 0) =
    (.halted 49, ⟨3, 3, 12, 12, 42, 1⟩) := by decide

/-- Empty input still resets, tests emptiness, and emits zero. -/
example : runFuel hornerCode (4 : ℕ) 3 (.running 0 [] 99 17) =
    (.halted 0, ⟨0, 0, 3, 3, 6, 1⟩) := by decide

/-- A zero coefficient is neither skipped nor given a free arithmetic iteration. -/
example : runFuel hornerCode (3 : ℕ) 12 (.running 0 [2, 0, 5] 0 0) =
    (.halted 23, ⟨3, 3, 12, 12, 42, 1⟩) := by decide

/-- One less instruction leaves emission pending, with no output charged yet. -/
example : runFuel hornerCode (4 : ℕ) 11 (.running 0 [2, 3, 5] 0 0) =
    (.running 4 [] 49 5, ⟨3, 3, 11, 11, 40, 0⟩) := by decide

/-- Swapping the multiply and add instructions multiplies the intended answer by the input. -/
example : runFuel #[.reset 1, .take 4 2, .add 3, .multiply 1, .emit]
    (4 : ℕ) 12 (.running 0 [2, 3, 5] 0 0) =
    (.halted 196, ⟨3, 3, 12, 12, 42, 1⟩) := by decide

end Polynomial.HornerMachine
