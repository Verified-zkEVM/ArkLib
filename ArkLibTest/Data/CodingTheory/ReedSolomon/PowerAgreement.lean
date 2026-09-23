/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode

/-!
# Constant-code power-agreement acceptance tests

A concrete two-point example checks the exceptional-challenge bound for constant messages.
-/

open Polynomial ReedSolomon

namespace ConstantCodeTest

/-- The evaluation points `0, 1` in `ℚ`. -/
def domain2 : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

/-- Two received words with swapped columns `(0, 1)` and `(1, 0)`; their batched values `z` and
`1` collide at `z = 1`. -/
def swapWords : Fin 2 → Fin 2 → ℚ := ![![0, 1], ![1, 0]]

-- The theorem gives the bound `1 * (2.choose 2) / max (2 - 1) 1 = 1` for this fixture.
example : UniformExactPowerAgreement domain2 swapWords 1 2 1 := by
  simpa using uniformExactPowerAgreement_constantCode domain2 swapWords 2

end ConstantCodeTest
