/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.ProjectionTransport
import ArkLibTest.ProofSystem.Sumcheck.Interaction.Projection

/-! # Multivariate input and next-round relation transport at a concrete nonconstant polynomial -/

namespace Sumcheck.Interaction.SingleRound.ProjectionTest

open OracleComp OracleSpec MvPolynomial Finset
open _root_.Interaction.Oracle

noncomputable section

/-- The numeric Boolean sum establishes the actual multivariate relation. -/
theorem input_relation :
    ((statement, fun _ => polynomial), ()) ∈ Spec.relationRound (ZMod 17) 2 1 domain 0 := by
  simp only [Spec.relationRound, statement, Set.mem_ofPred_eq]
  change (∑ z ∈ (univ.map domain) ^ᶠ 2,
    polynomial.val.eval (Fin.append Fin.elim0 z ∘ Fin.cast rfl)) = 1
  rw [sum_cube_cons, suffix_points, domain_points]
  have hne : (fun _ : Fin 1 => (0 : ZMod 17)) ≠ (fun _ => 1) := by
    intro h
    have := congrFun h 0
    norm_num at this
  norm_num [hne, polynomial]
  decide

/-- The relation-based theorem is usable through a normal import with virtual oracle input. -/
example :
    (fun run => run.closed.map (closedOutputRelation (ZMod 17) 1)) <$>
      executeCore (claimReduction (ZMod 17) 1 ambient (univ.map domain).toList 3)
        derived 1 projected = pure (some True) := by
  exact executeCore_projected_of_relationRound (ZMod 17) 2 1 domain ambient 0
    statement polynomial 3 input_relation

/-- The original bivariate polynomial is retained at the next target twelve. -/
example :
    (((⟨12, fun _ => 3⟩ : Spec.StatementRound (ZMod 17) 2 1), fun _ => polynomial), ()) ∈
      Spec.relationRound (ZMod 17) 2 1 domain 1 := by
  have h := relationRound_projected_output (ZMod 17) 2 1 domain 0 statement polynomial 3
  change (((⟨projected.val.eval 3, _⟩ : Spec.StatementRound (ZMod 17) 2 1), _), ()) ∈ _ at h
  rw [projected_eval] at h
  have hn : (5 + 8 * 3 : ZMod 17) = 12 := by decide
  have hc : Fin.snoc statement.challenges (3 : ZMod 17) = (fun _ => (3 : ZMod 17)) := by
    funext i
    fin_cases i
    rfl
  simpa [hn, hc, Spec.relationRound] using h

end
end Sumcheck.Interaction.SingleRound.ProjectionTest
