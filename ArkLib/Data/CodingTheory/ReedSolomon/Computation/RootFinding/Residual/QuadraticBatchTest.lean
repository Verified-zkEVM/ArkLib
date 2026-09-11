/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticBatchSpec
/-!
# Kernel checks for coordinate residual batches

Distinct and repeated points check both output order and duplicate retention. Entry checks the
retained sample payload and its charged construction. Empty input emits only the empty list.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualBatch

private def observe : Configuration (ZMod 3) → Option (List (Entry (ZMod 3)))
  | .done out => some out
  | _ => none

private def input : Input (ZMod 3) := ⟨[], [((1, 0), [(0, 1)])], (1, 1), 0⟩

private def batch := runFuel (2 : ZMod 3) input 171 (.start [(0, 1), (0, 1), (1, 0)])

example : (observe batch.1, batch.2) =
    (some [((0, 1), (1, 2)), ((0, 1), (1, 2)), ((1, 0), (2, 1))],
      ⟨⟨18, 15, 0, 0, 0, 528, 1531, 102, 19⟩, 24⟩) := by decide +kernel

private def entered : Configuration (ZMod 3) → Option (Pair (ZMod 3) × Pair (ZMod 3) × ℕ)
  | .call _ _ _ payload .start => some (payload.center, payload.sample, payload.order)
  | _ => none

private def entry := runFuel (2 : ZMod 3) input 3 (.start [(0, 1)])

theorem entry_handoff_retains_payload :
    let input : Input (ZMod 3) := ⟨[], [((1, 0), [(0, 1)])], (1, 1), 0⟩
    let entry := runFuel (2 : ZMod 3) input 3 (.start [(0, 1)])
    ((match entry.1 with
      | .call _ _ _ payload .start => some (payload.center, payload.sample, payload.order)
      | _ => none), entry.2) =
    (some ((1, 1), (0, 1), 0), ⟨⟨0, 0, 0, 0, 0, 3, 18, 0, 0⟩, 0⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) input 3 (.start [])

example : (observe empty.1, empty.2) =
    (some [], ⟨⟨0, 0, 0, 0, 0, 3, 7, 0, 1⟩, 0⟩) := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticResidualBatch
