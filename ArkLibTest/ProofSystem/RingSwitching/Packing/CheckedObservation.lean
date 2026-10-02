/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.CheckedObservation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! # Checked observation distinguishes inverse witness transport from a forward three-cycle -/

namespace RingSwitching.Packing.CheckedObservationTest

/-- The forward map is `0 ↦ 1 ↦ 2 ↦ 0`; its inverse is a different permutation. -/
def cycle : Fin 3 ≃ Fin 3 where
  toFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  invFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

/-- Honest messages encode the output witness; original evaluations use source coordinates. -/
def observation : CheckedObservation Unit (Fin 3) (Fin 3) Nat Nat where
  witnessEquiv := cycle
  honestMsg _ w := 7 + w.val
  scalarEval _ w := if w = 0 then 8 else if w = 1 then 9 else 7
  observe _ msg := msg
  eval_eq_observe _ w := by fin_cases w <;> decide

/-- Honest checking uses the image of the original source witness zero. -/
theorem honest_source :
    (8 : Nat) = observation.observe ()
      (observation.honestMsg () (observation.witnessEquiv 0)) :=
  observation.honest_check (q := ()) (w := 0) rfl

/-- A message honest for output witness one is pulled back through the inverse equivalence. -/
theorem readback_source :
    (8 : Nat) = observation.scalarEval () (observation.witnessEquiv.symm 1) :=
  observation.readback (q := ()) (msg := 8) rfl rfl

/-- The extracted source is zero, while the output witness was one. -/
theorem extracted_source : observation.witnessEquiv.symm 1 = 0 := rfl

/-- Reusing the output witness without any transport gives a false scalar claim. -/
theorem wrong_witness_rejected : (8 : Nat) ≠ observation.scalarEval () 1 := by decide

/-- Applying the forward equivalence instead of its inverse also gives a false source claim. -/
theorem wrong_forward_transport_rejected :
    (8 : Nat) ≠ observation.scalarEval () (observation.witnessEquiv 1) := by decide

/-- The check alone accepts a message that is honest for no witness; read-back needs the
honest-message premise, since no source witness evaluates to the accepted claim. -/
theorem accepted_dishonest_message_has_no_source :
    (100 : Nat) = observation.observe () 100 ∧
      (∀ w, observation.honestMsg () w ≠ 100) ∧ ∀ w, observation.scalarEval () w ≠ 100 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

end RingSwitching.Packing.CheckedObservationTest
