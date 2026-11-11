/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Projection

/-! # Transport of multivariate sum-check round relations -/

@[expose] public section

namespace Sumcheck.Interaction.SingleRound

open OracleComp OracleSpec Polynomial Finset
open _root_.Interaction.Oracle
open Spec.SingleRound

noncomputable section

variable (R : Type) [CommSemiring R]

variable (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- Actual virtual-input execution is complete from the multivariate round relation. -/
theorem executeCore_projected_of_relationRound [DecidableEq R] {ι : Type}
    (ambient : OracleSpec ι) (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (p : Spec.OracleStatement R n deg ()) (r : R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc) :
    (fun run => run.closed.map (closedOutputRelation R deg)) <$>
      executeCore (claimReduction R deg ambient (univ.map D).toList r)
        (projectedInput R n deg D i stmt p) stmt.target
        (projectedRoundPolynomial R n deg D i stmt.challenges p) = pure (some True) := by
  exact executeCore_projected R n deg D ambient i stmt p r
    (Spec.SingleRound.projected_sum_of_relationRound R n deg D i stmt p h)

end
end Sumcheck.Interaction.SingleRound
