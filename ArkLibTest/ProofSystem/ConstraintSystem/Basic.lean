/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.ConstraintSystem.Basic

/-! Acceptance checks for claim-dependent witnesses and executable morphism composition. -/

open Interaction.Oracle ConstraintSystem

private abbrev bounded : ConstraintSystem where
  Index := Unit
  Stmt := fun _ => Nat
  OStmt := fun _ => Nat
  toRelation := Relation.ofPredicate (fun _ c => Fin (c.2 + 1)) (fun _ c w => w.val = c.1)

private def shift : Hom bounded bounded where
  index := id
  stmt := fun _ s => s + 1
  oStmt := fun _ _ o => o + 1
  wit := fun _ _ _ w => w.succ
  preserves := fun _ _ _ _ h => congrArg Nat.succ h

-- Oracle data is fixed by language membership, rather than existentially hidden.
example : bounded.toProblem.language () (2, 3) := ⟨⟨2, by decide⟩, rfl⟩
example : ¬ bounded.toProblem.language () (2, 0) := by
  rintro ⟨w, hw⟩
  have h := w.isLt
  change w.val = 2 at hw
  rw [hw] at h
  exact Nat.not_lt_zero 1 (Nat.lt_of_succ_lt_succ h)

private def contract : BehavioralContract bounded () where
  Assumptions := fun _ => True
  Spec := fun s _ w => w.val = s
  soundness := fun _ _ _ _ h => h
  completeness := fun s _ => ⟨s, ⟨s, Nat.lt_succ_self s⟩, rfl, rfl⟩

example (s : Nat) : ∃ o, bounded.toProblem.language () (s, o) :=
  contract.isSatisfiable_of_assumptions trivial

-- Dependent witnesses remain executable through nontrivial composition.
run_cmd do
  unless ((shift.comp shift).wit () 0 0 ⟨0, by decide⟩).val == 2 do
    throwError "composed witness map returned the wrong value"

example : bounded.toProblem.language () (3, 4) :=
  shift.isSatisfiable_map (s := 2) (o := 3) ⟨⟨2, by decide⟩, rfl⟩

example : (ConstraintSystem.ofRelation (fun (_ : Unit) (s w : Nat) => s = w)).toProblem.language
    () ((4 : Nat), PUnit.unit) := ⟨(4 : Nat), rfl⟩

example : (ConstraintSystem.ofWitnessFree (fun (_ : Unit) (s o : Nat) => s = o)).toProblem.language
    () ((4 : Nat), (4 : Nat)) := ⟨PUnit.unit, rfl⟩
