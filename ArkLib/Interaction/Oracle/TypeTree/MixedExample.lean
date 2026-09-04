/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.TypeTree

/-!
# Mixed public/oracle path acceptance client

This file exercises the AR-2A distinction between structural branch paths and concrete execution
paths. A public Boolean selects one of two oracle-message types. Concrete oracle payloads remain in
the execution path but project to the same `PUnit` structural branch.
-/

namespace Interaction.Oracle.TypeTree.MixedExample

section UniverseCanary

universe uPosition uTree uBranch uExecution

/-- Compile-time canary that oracle positions are not pinned to the default universe. -/
abbrev UniversePosition := Oracle.Position.{uPosition}

/-- Compile-time canary that oracle type trees are not pinned to the default universe. -/
abbrev UniverseTypeTree := Oracle.TypeTree.{uTree}

/-- Compile-time canary that structural paths elaborate independently of the other canaries. -/
abbrev UniverseBranchPath (tree : Oracle.TypeTree.{uBranch}) := tree.BranchPath

/-- Compile-time canary that execution paths elaborate independently of the other canaries. -/
abbrev UniverseExecutionPath (tree : Oracle.TypeTree.{uExecution}) := tree.ExecutionPath

end UniverseCanary

/-- A public Boolean selects either a Boolean oracle message or a `Fin 3` oracle message. -/
def mixedTree : Oracle.TypeTree :=
  .public Bool fun
    | false => .oracle Bool fun _ => .done
    | true => .oracle (Fin 3) fun _ => .done

/-- Execution taking the false public branch and carrying a false oracle payload. -/
def falsePayload : mixedTree.ExecutionPath :=
  ⟨false, false, PUnit.unit⟩

/-- A second execution on the same public branch with a distinct oracle payload. -/
def truePayload : mixedTree.ExecutionPath :=
  ⟨false, true, PUnit.unit⟩

/-- Execution taking the true public branch and carrying a `Fin 3` oracle payload. -/
def finPayload : mixedTree.ExecutionPath :=
  ⟨true, (2 : Fin 3), PUnit.unit⟩

/-- Distinct oracle payloads remain distinct in the concrete execution path. -/
example : falsePayload ≠ truePayload := by
  intro h
  cases h

/-- Opaque payloads on the same public branch have the same structural projection. -/
example : falsePayload.toBranchPath = truePayload.toBranchPath :=
  rfl

/-- The false public branch records its choice and a unit oracle marker. -/
example : falsePayload.toBranchPath = ⟨false, PUnit.unit, PUnit.unit⟩ :=
  rfl

/-- The true public branch records its choice but not the `Fin 3` payload. -/
example : finPayload.toBranchPath = ⟨true, PUnit.unit, PUnit.unit⟩ :=
  rfl

/-- Erasing the oracle distinction preserves the concrete `Fin 3` runtime message. -/
example : finPayload.toTypeTreePath = ⟨true, (2 : Fin 3), PUnit.unit⟩ :=
  rfl

end Interaction.Oracle.TypeTree.MixedExample
