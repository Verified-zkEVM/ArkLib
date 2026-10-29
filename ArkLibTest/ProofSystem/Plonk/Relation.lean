/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Plonk.Relation.Basic
import ArkLib.ProofSystem.Plonk.Relation.Prepared

/-! # Finite Plonk acceptance examples -/

namespace ArkLibTest.PlonkFinite

open Plonk

/-- The first variable is three, the second is twice the first, and the third is unused. -/
private def circuit : ConstraintSystem Int 3 2 :=
  ![Gate.add 0 0 1, Gate.eq 0 3]

private def assignment : Fin 3 → Int := ![3, 6, 11]

example : List.ofFn (fun p => (circuit.wireAt p).val) = [0, 0, 0, 0, 1, 0] := by
  decide

-- The occurrences of variable zero form a five-cycle; variable one's occurrence is fixed.
example : List.ofFn (fun p => (circuit.perm p).val) = [1, 2, 3, 5, 4, 0] := by
  decide

example : circuit.perm (4 : Fin 6) = 4 := by decide

example : List.ofFn (circuit.occurrences assignment) = [3, 3, 3, 3, 6, 3] := by
  decide

example : circuit.CopyConstraintsSatisfied (circuit.occurrences assignment) := by
  unfold ConstraintSystem.CopyConstraintsSatisfied
  decide

-- Reconstruction retains the used values and gives the unused variable zero.
example : List.ofFn (circuit.assignmentOfOccurrences (circuit.occurrences assignment)) =
    [3, 6, 0] := by
  decide

example : ∃ w, relation circuit 1 (by decide) (fun _ => 3) w := by
  refine ⟨![6, 11], ?_⟩
  unfold relation ConstraintSystem.accepts Gate.accepts
  decide

example : ¬ ∃ w, relation circuit 1 (by decide) (fun _ => 4) w := by
  rintro ⟨w, hw⟩
  have heq : (Gate.eq (0 : Fin 3) (3 : Int)).accepts
      (fullAssignment (by decide) (fun _ : Fin 1 => (4 : Int)) w) := hw 1
  have hbad : (4 : Int) = 3 := (Gate.eq_accepts _ _ _).mp heq
  contradiction

example : (circuit.prepare (by decide : 1 ≤ 3) (fun _ => 3)).accepts assignment := by
  unfold ConstraintSystem.accepts Gate.accepts
  decide

example : List.ofFn (privateWitness (by decide : 1 ≤ 3) assignment) = [6, 11] := by
  decide

private def preparedOccurrences : Fin 9 → Int :=
  (circuit.prepare (by decide : 1 ≤ 3) (fun _ => 3)).occurrences assignment

example : List.ofFn (circuit.decodePrepared (by decide : 1 ≤ 3) (fun _ => 3)
    preparedOccurrences) = [6, 0] := by
  decide

example : relation circuit 1 (by decide) (fun _ => 3)
    (circuit.decodePrepared (by decide) (fun _ => 3) preparedOccurrences) := by
  unfold relation ConstraintSystem.accepts Gate.accepts
  decide

-- Clearing the reserved constant and restoring the public term counts the input once.
example :
    let prepared := circuit.prepare (by decide : 1 ≤ 3) (fun _ => 3)
    let cleared := prepared.clearPublicConstants 1
    (cleared 0).qC = 0 ∧
      ConstraintSystem.publicInputTerm (by decide : 1 ≤ 3)
        (fun _ : Fin 1 => (3 : Int)) 0 = -3 ∧
      (cleared 0).eval assignment +
        ConstraintSystem.publicInputTerm (by decide : 1 ≤ 3)
          (fun _ : Fin 1 => (3 : Int)) 0 = 0 := by
  decide

private def emptyCircuit : ConstraintSystem Int 3 0 := Fin.elim0

example : List.ofFn (fun p => (emptyCircuit.perm p).val) = [] := rfl

example : List.ofFn (emptyCircuit.assignmentOfOccurrences Fin.elim0) = [0, 0, 0] := by
  decide

-- Preparation supplies an occurrence for a previously unused, nonzero public variable.
example :
    List.ofFn ((emptyCircuit.prepare (by decide : 1 ≤ 3) (fun _ => 7)).assignmentOfOccurrences
      (fun _ => 7)) = [7, 0, 0] := by
  decide

example : List.ofFn (emptyCircuit.decodePrepared (by decide : 1 ≤ 3) (fun _ => 7)
    (fun _ => 7)) = [0, 0] := by
  decide

#eval List.ofFn (fun p => (circuit.perm p).val)
#eval List.ofFn (circuit.assignmentOfOccurrences (circuit.occurrences assignment))
#eval List.ofFn (circuit.decodePrepared (by decide : 1 ≤ 3) (fun _ => 3) preparedOccurrences)

end ArkLibTest.PlonkFinite
