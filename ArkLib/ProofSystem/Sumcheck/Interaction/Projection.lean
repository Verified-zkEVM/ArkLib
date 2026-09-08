/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Closing

/-! # Virtual multivariate projection feeds the actual single-round executor -/

namespace Sumcheck.Interaction.SingleRound

open OracleComp OracleSpec Polynomial
open _root_.Interaction.Oracle
open Spec.SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- The existing executable round projection, packaged as a derived oracle plan. -/
def projectionView (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc) :
    VirtualOracle [Spec.OracleStatement R n deg]ₒ (outputFamily R deg) where
  query := simulateProjectedRoundPolynomial R n deg D i stmt

/-- Interpreting the virtual projection agrees with the honest projected polynomial. -/
theorem projectionView_eval (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (p : Spec.OracleStatement R n deg ()) (x : R) :
    (projectionView R n deg D i stmt).eval
      (OracleInterface.simOracle0 (Spec.OracleStatement R n deg) (fun _ => p)) ⟨(), x⟩ =
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x := by
  exact simulateProjectedRoundPolynomial_eq R n deg D i stmt (fun _ => p) ⟨(), x⟩

/-- Adapt the derived family to the single input evaluation signature without materializing it. -/
def projectedInput (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (p : Spec.OracleStatement R n deg ()) : QueryImpl (inputSpec R) Id :=
  fun x => (projectionView R n deg D i stmt).eval
    (OracleInterface.simOracle0 (Spec.OracleStatement R n deg) (fun _ => p)) ⟨(), x⟩

/-- Equality of behavior is a theorem, not a replacement of the operational projection plan. -/
theorem projectedInput_eq (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (p : Spec.OracleStatement R n deg ()) :
    projectedInput R n deg D i stmt p =
      inputImpl R deg (projectedRoundPolynomial R n deg D i stmt.challenges p) := by
  funext x
  exact projectionView_eval R n deg D i stmt p x

/-- The executor closes its own output to the honest projected polynomial's behavior. -/
theorem executeCore_projected_closed [DecidableEq R] {ι : Type} (ambient : OracleSpec ι)
    (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (p : Spec.OracleStatement R n deg ()) (r : R)
    (h : ((Finset.univ.map D).toList.map (fun x =>
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x)).sum = stmt.target) :
    CoreRun.closed <$>
      executeCore (claimReduction R deg ambient (Finset.univ.map D).toList r)
        (projectedInput R n deg D i stmt p) stmt.target
        (projectedRoundPolynomial R n deg D i stmt.challenges p) =
      pure (some (honestData R deg
        (projectedRoundPolynomial R n deg D i stmt.challenges p) r).toClosed) := by
  rw [projectedInput_eq]
  exact executeCore_closed R deg ambient _ _ _ _ h

/-- Run-derived completeness with its input behavior supplied by a virtual multivariate sum. -/
theorem executeCore_projected [DecidableEq R] {ι : Type} (ambient : OracleSpec ι)
    (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (p : Spec.OracleStatement R n deg ()) (r : R)
    (h : ((Finset.univ.map D).toList.map (fun x =>
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x)).sum = stmt.target) :
    (fun run => run.closed.map (closedOutputRelation R deg)) <$>
      executeCore (claimReduction R deg ambient (Finset.univ.map D).toList r)
        (projectedInput R n deg D i stmt p) stmt.target
        (projectedRoundPolynomial R n deg D i stmt.challenges p) = pure (some True) := by
  rw [projectedInput_eq]
  exact executeCore_complete R deg ambient _ _ _ _ h

end
end Sumcheck.Interaction.SingleRound
