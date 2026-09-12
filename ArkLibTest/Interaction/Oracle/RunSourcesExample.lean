/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.RunSources

/-! # Realized-source acceptance: retained terminal slots and hidden representations -/

namespace Interaction.Oracle.RunSourcesExample

open Interaction.Oracle.TypeTree

/-- Only the first coordinate can be queried. -/
@[reducible]
def interface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

/-- A public choice followed by two oracle sends, the second immediately before termination. -/
abbrev tree : Oracle.TypeTree :=
  .public Bool fun _ => .oracle (Nat × Nat) fun _ => .oracle (Nat × Nat) fun _ => .done

/-- Both oracle slots use the same query and answer types. -/
def oracles : tree.OracleDecoration :=
  ⟨PUnit.unit, fun _ => ⟨interface, fun _ => ⟨interface, fun _ => PUnit.unit⟩⟩⟩

/-- An arbitrary initial behavior, independently of the two sent objects. -/
abbrev initial : PFunctor := (Unit →ₒ Nat).toPFunctor

/-- An execution with a private coordinate in each message. -/
def path (hidden : Nat) : tree.ExecutionPath :=
  ⟨true, (11, hidden), (19, hidden + 1), PUnit.unit⟩

/-- The final query signature. -/
abbrev finalSpec :=
  OracleSpec.ofPFunctor (accessAfter tree oracles initial (path 0).toBranchPath)

/-- Final access distinguishes the input, first sent, and last sent slots. -/
def readAll : OracleComp
    finalSpec
    (Nat × Nat × Nat) := do
  let old : Nat ← liftM (finalSpec.query (.inl (.inl ())))
  let first : Nat ← liftM (finalSpec.query (.inl (.inr ())))
  let last : Nat ← liftM (finalSpec.query (.inr ()))
  return (old, first, last)

example (hidden : Nat) :
    simulateQ ((path hidden).closingImpl oracles initial (fun _ => 7)) readAll =
      (7, 11, 19) := rfl

example (hidden₁ hidden₂ : Nat) :
    (path hidden₁).closingImpl oracles initial (fun _ => 7) =
      (path hidden₂).closingImpl oracles initial (fun _ => 7) := by
  funext query
  rcases query with (_ | _) | _ <;> rfl

/-- Structural paths through an impossible send do not manufacture a concrete message. -/
example : IsEmpty (OracleMessagesAt (.oracle Empty fun _ => .done)
    ⟨PUnit.unit, PUnit.unit⟩) := by
  change IsEmpty (Empty × PUnit)
  infer_instance

end Interaction.Oracle.RunSourcesExample
