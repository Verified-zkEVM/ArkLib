/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Interaction.Legacy
import Mathlib.Data.ZMod.Basic

/-! # The legacy prover generates the transcript used by the correspondence theorem -/

namespace Sumcheck.Interaction.SingleRound.LegacyTest

open OracleComp OracleSpec Polynomial

noncomputable section

/-- A nonconstant honest message distinguishes the challenge from the input sum. -/
def polynomial : Message (ZMod 17) 1 :=
  ⟨X, Polynomial.mem_degreeLE.mpr Polynomial.degree_X_le⟩

/-- An oracle-capable ambient context remains available to both executions. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

local instance : ∀ i, OracleInterface ((Spec.SingleRound.pSpec (ZMod 17) 1).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- The real legacy prover sends its input polynomial and receives challenge five. -/
theorem prover_generates_transcript :
    simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec (ZMod 17) 1).Challenge)
      (legacyTranscript (ZMod 17) 1 polynomial 5).challenges)
      ((Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient).run
        (1, fun _ => polynomial) ()) =
      pure (legacyTranscript (ZMod 17) 1 polynomial 5,
        (((5 : ZMod 17), 5), fun _ : Unit => polynomial), ()) := by
  rw [legacy_prover_run]
  simp [polynomial]

/-- Generation is an operational fact even when the input target is wrong. -/
example :
    simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec (ZMod 17) 1).Challenge)
      (legacyTranscript (ZMod 17) 1 polynomial 3).challenges)
      ((Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient).run
        (2, fun _ => polynomial) ()) =
      pure (legacyTranscript (ZMod 17) 1 polynomial 3,
        (((3 : ZMod 17), 3), fun _ : Unit => polynomial), ()) := by
  rw [legacy_prover_run]
  simp [polynomial]

end
end Sumcheck.Interaction.SingleRound.LegacyTest
