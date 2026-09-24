/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Finset.LineAgreement

/-!
# Acceptance test for exceptional parameters of line agreement
-/

/-- One concrete pair of lines has an exceptional set of size at most one. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧
    ∀ z ∉ exceptional, ∀ i ∈ ({0} : Finset (Fin 1)),
      (0 : ℚ) + z * 1 = 1 + z * 0 ↔ (0 : ℚ) = 1 ∧ (1 : ℚ) = 0 := by
  simpa using Finset.exists_card_le_forall_add_mul_eq_add_mul_iff
    ({0} : Finset (Fin 1)) (fun _ ↦ (0 : ℚ)) (fun _ ↦ (1 : ℚ))
    (fun _ ↦ (1 : ℚ)) (fun _ ↦ (0 : ℚ))
