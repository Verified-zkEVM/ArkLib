/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier

/-! Shape paths and full transcripts on a mixed message and oracle protocol. A public bit selects
a `Bool` oracle payload or a `Fin 3` oracle payload. Payloads stay in the full transcript and
project to the same shape path; the verifier view erases them. -/

open PFunctor PFunctor.FreeM Interaction.Core

namespace Interaction.Core.MixedExampleTests

section UniverseCanary

universe uPosition uTree uBranch uExecution

-- MixedExample 1, restated: oracle positions are `OraclePos`.
/-- Oracle positions are not pinned to the default universe. -/
abbrev UniversePosition := OraclePos.{uPosition}

-- MixedExample 2, restated: oracle trees are `OracleProtocol`.
/-- Oracle protocols are not pinned to the default universe. -/
abbrev UniverseTypeTree := OracleProtocol.{uTree}

-- MixedExample 3, restated: structural branch paths are shape paths `Path s`.
/-- Shape paths elaborate at any universe. -/
abbrev UniverseBranchPath (s : OracleProtocol.{uBranch}) := Path s

-- MixedExample 4, restated: execution paths are full transcripts `PathAlong oracleSig s`.
/-- Full transcripts elaborate at any universe. -/
abbrev UniverseExecutionPath (s : OracleProtocol.{uExecution}) := PathAlong oracleSig s

end UniverseCanary

-- MixedExample fixture: the frozen tree's public node is re-authored as a prover message.
/-- A public bit selects a `Bool` oracle payload or a `Fin 3` oracle payload. -/
@[instance_reducible] def mixedTree : OracleProtocol :=
  .liftBind (.message Bool) fun
    | false => .liftBind (.oracle Bool OracleInterface.instDefault) (fun _ => .pure ⟨⟩)
    | true => .liftBind (.oracle (Fin 3) OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

/-- The `false` branch with payload `false`. -/
def falsePayload : PathAlong oracleSig mixedTree := ⟨false, false, ⟨⟩⟩

/-- The `false` branch with payload `true`. -/
def truePayload : PathAlong oracleSig mixedTree := ⟨false, true, ⟨⟩⟩

/-- The `true` branch with payload `2 : Fin 3`. -/
def finPayload : PathAlong oracleSig mixedTree := ⟨true, (2 : Fin 3), ⟨⟩⟩

-- MixedExample 5, restated: the execution path is the full transcript.
/-- Distinct payloads stay distinct in the full transcript. -/
example : falsePayload ≠ truePayload := by
  intro h
  cases h

-- MixedExample 6, restated: `toBranchPath` is `projectPathAlong oracleSig`.
/-- Payloads on the same public branch have the same shape path. -/
example : projectPathAlong oracleSig mixedTree falsePayload =
    projectPathAlong oracleSig mixedTree truePayload := rfl

-- MixedExample 7, restated as the concrete shape path.
/-- The `false` shape path records the bit and a unit marker for the payload. -/
example : projectPathAlong oracleSig mixedTree falsePayload = ⟨false, ⟨⟩, ⟨⟩⟩ := rfl

-- MixedExample 8, restated as row 7.
/-- The `true` shape path records the bit but not the `Fin 3` payload. -/
example : projectPathAlong oracleSig mixedTree finPayload = ⟨true, ⟨⟩, ⟨⟩⟩ := rfl

-- MixedExample 9, restated: tree conversion is retired. The full transcript keeps the payload
-- `2 : Fin 3`, which the payload family returns, while the verifier view erases it.
/-- The full transcript keeps the `Fin 3` payload. -/
example : payloads mixedTree finPayload (.inl ⟨⟩) = (2 : Fin 3) := rfl

/-- The verifier view of the `true` branch erases the payload, so any two payloads have the same
view. -/
example (x y : Fin 3) :
    (toView mixedTree ⟨true, x, ⟨⟩⟩).val = (toView mixedTree ⟨true, y, ⟨⟩⟩).val := rfl

example : (toView mixedTree finPayload).val = ⟨true, ⟨⟩, ⟨⟩⟩ := rfl

end Interaction.Core.MixedExampleTests
