/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Prefix

/-! Acceptance clients for execution prefixes: hidden realizations, empty sends, and available
contexts. -/

namespace Interaction.Oracle.PrefixTest

open PFunctor.FreeM Interaction.Oracle.TypeTree

/-- One hidden message followed by a public choice. -/
def mixed : Oracle.TypeTree :=
  .oracle Bool (fun _ => .public (Fin 3) (fun _ => .done))

/-- Stop immediately after the oracle send. -/
def sent (message : Bool) : ExecutionPrefix mixed :=
  ⟨Cursor.down (P := TypeTree.basePFunctor) (a := Position.oracle Bool)
    (next := fun _ => TypeTree.public (Fin 3) (fun _ => .done)) PUnit.unit
    (Cursor.root (TypeTree.public (Fin 3) (fun _ => .done))), ⟨message, PUnit.unit⟩⟩

-- Realizations share a structural cursor but remain different execution prefixes.
example : (sent true).cursor = (sent false).cursor := rfl

example : sent true ≠ sent false := by
  intro h
  have hm : HEq (sent true).messages (sent false).messages := by cases h
  have values : (true, PUnit.unit) = (false, PUnit.unit) := eq_of_heq hm
  exact Bool.noConfusion (congrArg Prod.fst values)

-- This oracle occurrence is available only after crossing its edge.
example : (sent true).Available (sent true).cursor := by
  constructor
  · exact ⟨Cursor.root mixed, Bool, _, rfl, rfl⟩
  · exact ⟨Cursor.Extends.refl _⟩

example : ¬ (ExecutionPrefix.root mixed).Available (sent true).cursor := by
  intro h
  have bound := ExecutionPrefix.available_length_le _ _ h
  change 1 ≤ 0 at bound
  omega

-- An empty realization type permits a root prefix but supplies no crossed-send realization.
example : ExecutionPrefix (TypeTree.oracle Empty (fun _ => .done)) := ExecutionPrefix.root _

example (messages : PrefixMessages.Along
    (Cursor.down (P := TypeTree.basePFunctor) (a := Position.oracle Empty)
      (next := fun _ => TypeTree.done) PUnit.unit (Cursor.root TypeTree.done)).spine) : False :=
  messages.1.elim

-- A concrete execution path projects through the public choice and retains the hidden realization.
example : (ExecutionPrefix.ofExecutionPath (tree := mixed)
    ⟨true, ⟨(2 : Fin 3), PUnit.unit⟩⟩).cursor.length = 2 := rfl

example : (ExecutionPrefix.ofExecutionPath (tree := mixed)
    ⟨true, ⟨(2 : Fin 3), PUnit.unit⟩⟩).messages.1 = true := rfl

end Interaction.Oracle.PrefixTest
