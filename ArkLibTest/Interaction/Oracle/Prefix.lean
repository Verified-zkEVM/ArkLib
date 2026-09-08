/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Prefix

/-! Acceptance clients for full prefixes: hidden payloads, empty sends, and available resources. -/

namespace Interaction.Oracle.PrefixTest

open PFunctor.FreeM Interaction.Oracle.TypeTree

/-- One hidden message followed by a public choice. -/
def mixed : Oracle.TypeTree :=
  .oracle Bool (fun _ => .public (Fin 3) (fun _ => .done))

/-- Stop immediately after the oracle send. -/
def sent (message : Bool) : FullPrefix mixed :=
  ⟨Cursor.down (P := TypeTree.basePFunctor) (a := Position.oracle Bool)
    (next := fun _ => TypeTree.public (Fin 3) (fun _ => .done)) PUnit.unit
    (Cursor.root (TypeTree.public (Fin 3) (fun _ => .done))), ⟨message, PUnit.unit⟩⟩

-- Payloads share a structural cursor but remain different full prefixes.
example : (sent true).cursor = (sent false).cursor := rfl

example : sent true ≠ sent false := by
  intro h
  have hm : HEq (sent true).messages (sent false).messages := by cases h
  have values : (true, PUnit.unit) = (false, PUnit.unit) := eq_of_heq hm
  exact Bool.noConfusion (congrArg Prod.fst values)

-- This resource is available only after crossing the oracle edge.
example : (sent true).Available (sent true).cursor := by
  constructor
  · exact ⟨Cursor.root mixed, Bool, _, rfl, rfl⟩
  · exact ⟨Cursor.Extends.refl _⟩

example : ¬ (FullPrefix.root mixed).Available (sent true).cursor := by
  intro h
  have bound := FullPrefix.no_future _ _ h
  change 1 ≤ 0 at bound
  omega

-- An empty message type permits a root prefix, but supplies no crossed-send payload.
example : FullPrefix (TypeTree.oracle Empty (fun _ => .done)) := FullPrefix.root _

example (messages : PrefixMessages.Along
    (Cursor.down (P := TypeTree.basePFunctor) (a := Position.oracle Empty)
      (next := fun _ => TypeTree.done) PUnit.unit (Cursor.root TypeTree.done)).spine) : False :=
  messages.1.elim

-- A concrete full path projects through the public choice and retains the hidden message.
example : (FullPrefix.ofExecutionPath (tree := mixed)
    ⟨true, ⟨(2 : Fin 3), PUnit.unit⟩⟩).cursor.length = 2 := rfl

end Interaction.Oracle.PrefixTest
