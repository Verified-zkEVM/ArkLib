/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Closing
import ArkLibTest.ProofSystem.Sumcheck.Interaction.SingleRound

/-! # Concrete acceptance through the claim and run boundary -/

namespace Sumcheck.Interaction.SingleRound.Test

open OracleComp
open _root_.Interaction.Oracle

/-- The selected ideal guarantee certifies the actual nonconstant sent object. -/
example : polynomial.val.degree ≤ (1 : ℕ) := message_degree (ZMod 17) 1 polynomial

/-- Closing the actual finite-field execution exports the original polynomial's behavior. -/
example :
    CoreRun.closed <$> executeCore (claimReduction (ZMod 17) 1 ambient [0, 1] 5)
        (inputImpl (ZMod 17) 1 polynomial) 1 polynomial =
      pure (some (honestData (ZMod 17) 1 polynomial 5).toClosed) := by
  apply executeCore_closed
  simp [polynomial]

/-- Completeness is observed on the run's closed behavior, not on a supplied replacement oracle. -/
example :
    (fun run => run.closed.map (closedOutputRelation (ZMod 17) 1)) <$>
      executeCore (claimReduction (ZMod 17) 1 ambient [0, 1] 5)
        (inputImpl (ZMod 17) 1 polynomial) 1 polynomial = pure (some True) := by
  apply executeCore_complete
  simp [polynomial]

/-- A real uniform challenge remains perfectly complete at the measure boundary. -/
example :
    discreteEvalDist (executeSampled (ZMod 17) 1 ($ᵗ (ZMod 17)) polynomial [0, 1] 1)
      {run | run.closed.map (closedOutputRelation (ZMod 17) 1) = some True} = 1 := by
  apply executeSampled_measure_complete
  · let : MeasurableSpace (ZMod 17) := ⊤
    have h : Pr[fun _ => True | ($ᵗ (ZMod 17))] = 1 := by simp
    rw [probEvent_eq_evalSPMF_toMeasure] at h
    exact h
  · simp [polynomial]

#print axioms executeCore_closed
#print axioms executeCore_degree_complete
#print axioms executeSampled_eq
#print axioms executeSampled_measure_complete

end Sumcheck.Interaction.SingleRound.Test
