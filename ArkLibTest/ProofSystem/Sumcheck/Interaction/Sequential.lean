/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Sequential
import ArkLibTest.ProofSystem.Sumcheck.Interaction.Projection

/-! # Two full rounds on a nonconstant bivariate polynomial -/

namespace Sumcheck.Interaction.MultivariateRound.Test

open OracleComp OracleSpec MvPolynomial Finset
open _root_.Interaction.Oracle
open SingleRound.ProjectionTest

noncomputable section

/-- The second honest message is selected using the first run's challenge prefix. -/
def second (middle : Spec.StatementRound (ZMod 17) 2 1) : SingleRound.Message (ZMod 17) 1 :=
  Spec.SingleRound.projectedRoundPolynomial (ZMod 17) 2 1 domain 1 middle.challenges polynomial

/-- With one variable left, the projected message is the bivariate evaluation at that prefix. -/
theorem second_eval (middle : Spec.StatementRound (ZMod 17) 2 1) (x : ZMod 17) :
    (second middle).val.eval x =
      1 + 2 * middle.challenges ⟨0, by decide⟩ + 3 * x +
        4 * middle.challenges ⟨0, by decide⟩ * x := by
  rw [second, SingleRound.projectedRoundPolynomial_eval]
  simp [polynomial, Fin.append, Fin.addCases, Fin.snoc]

/-- Challenges three then five produce final target fourteen and preserve the original oracle. -/
example :
    executeTwo (ZMod 17) 0 1 ambient 0 (univ.map domain).toList statement
      ((polynomialFamily (ZMod 17) 2 1).behaviorOfRealizations (fun _ => polynomial))
      projected second 3 5 =
      pure (some (⟨⟨14, ![3, 5]⟩,
        (polynomialFamily (ZMod 17) 2 1).behaviorOfRealizations (fun _ => polynomial)⟩ :
          ClosedClaim (Spec.StatementRound (ZMod 17) 2 2) (polynomialFamily (ZMod 17) 2 1))) := by
  have h₂ : (((univ.map domain).toList).map (fun x =>
      (second ⟨projected.val.eval 3, Fin.snoc statement.challenges 3⟩).val.eval x)).sum =
      projected.val.eval 3 := by
    change (List.map _ (Multiset.toList (univ.map domain).val)).sum = _
    rw [Multiset.sum_map_toList]
    change (∑ x ∈ univ.map domain, _) = _
    rw [domain_points]
    norm_num [second_eval, projected_eval, statement]
    decide
  rw [executeTwo_accepted (ZMod 17) 0 1 ambient 0 _ statement _ projected second 3 5
    projected_sum h₂]
  congr 2
  norm_num [second_eval, statement]
  decide

/-- The second projected message satisfies its sum claim at every first challenge. -/
theorem second_sum (r : ZMod 17) :
    (((univ.map domain).toList).map (fun x =>
      (second ⟨projected.val.eval r, Fin.snoc statement.challenges r⟩).val.eval x)).sum =
      projected.val.eval r := by
  exact SingleRound.projected_sum_of_relationRound (ZMod 17) 2 1 domain 1 _ polynomial
    (SingleRound.relationRound_projected_output (ZMod 17) 2 1 domain 0 statement polynomial r)

/-- Distinct observable events identify the two verifier challenge phases. -/
abbrev events : OracleSpec Bool := Bool →ₒ Unit

/-- Record a challenge event before returning its prescribed field element. -/
def challengeEvent (event : Bool) (r : ZMod 17) : OracleComp events (ZMod 17) := do
  let _ ← liftM (events.query event)
  return r

/-- A test interpreter remembers the exact query order. -/
def record : QueryImpl events (StateM (List Bool)) :=
  fun event => modify (fun seen => seen ++ [event])

/-- Actual sampled verifier executions emit first then second challenge events. -/
example :
    (simulateQ record (Option.isSome <$>
      executeTwoSampled (ZMod 17) 0 1 events 0 (univ.map domain).toList statement
        ((polynomialFamily (ZMod 17) 2 1).behaviorOfRealizations (fun _ => polynomial))
        projected second
        (challengeEvent false 3) (fun _ => challengeEvent true 5))).run [] =
      (true, [false, true]) := by
  rw [executeTwoSampled_accepted (ZMod 17) 0 1 events 0 _ statement _ projected second
    _ _ projected_sum second_sum]
  simp [challengeEvent, record, simulateQ_bind, simulateQ_map]
  rfl

/-- An incorrect first target skips the second verifier's challenge event. -/
example :
    (simulateQ record (Option.isSome <$>
      executeTwoSampled (ZMod 17) 0 1 events 0 (univ.map domain).toList
        { statement with target := 2 }
        ((polynomialFamily (ZMod 17) 2 1).behaviorOfRealizations (fun _ => polynomial))
        projected second
        (challengeEvent false 3) (fun _ => challengeEvent true 5))).run [] =
      (false, [false]) := by
  have h : (((univ.map domain).toList).map (fun x => projected.val.eval x)).sum ≠
      (2 : ZMod 17) := by
    rw [projected_sum]
    decide
  rw [executeTwoSampled_rejected (ZMod 17) 0 1 events 0 _ _ _ projected second _ _ h]
  simp [challengeEvent, record, simulateQ_map]
  rfl

#print axioms executeTwo_complete

end
end Sumcheck.Interaction.MultivariateRound.Test
