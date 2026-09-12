/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Closing
public import Mathlib.Algebra.Polynomial.Roots

/-! # One-round soundness for the actual closed Sumcheck execution

The prover commits to an arbitrary degree-bounded polynomial before the verifier samples
its fresh challenge. The original input polynomial remains the closed output oracle.
Rejection and ambient failure contribute no mass to the successful true-output event.

Here “committed” means that the prover's message is chosen before the challenge; this module
does not model a cryptographic commitment scheme. `committedRun` is a normal-form result value,
and `executeCommitted_eq` establishes that the executor produces its challenge-indexed instances.
-/

@[expose] public section

namespace Sumcheck.Interaction.SingleRound

open OracleComp OracleSpec Polynomial
open _root_.Interaction.Oracle

noncomputable section

variable (F : Type) [Field F] (deg : ℕ)

/-- Normal-form result for a committed message, including explicit sum-check rejection.
This value alone does not establish execution provenance. -/
def committedRun [DecidableEq F] (p q : Message F deg) (domain : List F) (target r : F) :
    CoreRun (protocol F deg) (inputSpec F).toPFunctor (fun _ => F × F)
      (fun _ => outputFamily F deg) (fun _ => F × F) where
  path := ⟨q, r, PUnit.unit⟩
  inputImpl := inputImpl F deg p
  proverOut := (q.val.eval r, r)
  outcome := if (domain.map (fun x => q.val.eval x)).sum = target then
    some (outputClaim F deg (q.val.eval r, r)) else none

/-- Execution with arbitrary committed message and an independent challenge program. -/
def executeCommitted [DecidableEq F] (challenge : ProbComp F) (p q : Message F deg)
    (domain : List F) (target : F) :=
  executeCore (sampledClaimReduction F deg unifSpec domain challenge)
    (inputImpl F deg p) target q

set_option backward.isDefEq.respectTransparency false in
/-- The executor retains the original input oracle while its terminal target comes from `q`. -/
theorem executeCommitted_eq [DecidableEq F] (challenge : ProbComp F)
    (p q : Message F deg) (domain : List F) (target : F) :
    executeCommitted F deg challenge p q domain target =
      committedRun F deg p q domain target <$> challenge := by
  simp only [executeCommitted, executeCore, _root_.Interaction.Oracle.Reduction.execute,
    sampledClaimReduction, pure_bind]
  simp only [executeStrategies, prover, sampledClaimVerifier, protocol,
    Protocol.oracleWith_tree, Protocol.oracleWith_roles, Protocol.oracleWith_oracles,
    Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles,
    Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles,
    Verifier.toCounterpart,
    TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public, TypeTree.toTypeTree_done,
    TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
    TypeTree.RoleDecoration.toTypeTreeRoles_public,
    TypeTree.RoleDecoration.toTypeTreeRoles_done,
    bind_assoc, pure_bind]
  dsimp only [_root_.Interaction.TwoParty.run,
    _root_.Interaction.InteractionOver.runTypeTree,
    _root_.Interaction.InteractionOver.TwoParty.pairedTypeTree,
    _root_.Interaction.InteractionOver.TwoParty.paired,
    _root_.Interaction.TwoParty.participantProfile,
    _root_.Interaction.TwoParty.collectParticipantOutputs]
  have hc : simulateQ (Verifier.liftAccessImpl unifSpec (access F deg)
      (Access.extendImpl (inputSpec F).toPFunctor (polynomialInterface F deg)
        (inputImpl F deg p) q))
      (OracleComp.liftComp challenge (unifSpec + OracleSpec.ofPFunctor (access F deg))) =
        challenge := by
    rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' unifSpec)
      (fun _ => rfl), simulateQ_id']
  simp only [id_eq, simulateQ_bind, simulateQ_pure, hc, bind_assoc, pure_bind,
    simulateQ_map, simulate_terminal, map_pure]
  simp only [bind_pure_comp]
  congr 1
  funext r
  unfold committedRun
  split <;> rfl

/-- A true closed output requires acceptance and equality with the input evaluation. -/
theorem committedRun_true_iff [DecidableEq F] (p q : Message F deg)
    (domain : List F) (target r : F) :
    (committedRun F deg p q domain target r).closed.map (closedOutputRelation F deg) =
        some True ↔
      (domain.map (fun x => q.val.eval x)).sum = target ∧ p.val.eval r = q.val.eval r := by
  by_cases h : (domain.map (fun x => q.val.eval x)).sum = target
  · simp only [committedRun, h, if_pos]
    change some (p.val.eval r = q.val.eval r) = some True ↔ _
    simp
  · simp [committedRun, h, CoreRun.closed]

/-- Ambient failure is preserved; rejection is instead an explicit completed run. -/
theorem executeCommitted_failure [DecidableEq F] (challenge : ProbComp F)
    (p q : Message F deg) (domain : List F) (target : F) :
    Pr[⊥ | executeCommitted F deg challenge p q domain target] = Pr[⊥ | challenge] := by
  rw [executeCommitted_eq, probFailure_map]

/-- A failed sum check cannot produce any closed output claim. -/
theorem committedRun_rejects [DecidableEq F] (p q : Message F deg)
    (domain : List F) (target r : F)
    (h : (domain.map (fun x => q.val.eval x)).sum ≠ target) :
    (committedRun F deg p q domain target r).closed = none := by
  simp [committedRun, h, CoreRun.closed]

variable [Fintype F] [DecidableEq F] [SampleableType F]

/-- Soundness against every polynomial fixed before the fresh uniform challenge. -/
theorem executeCommitted_soundness (p q : Message F deg) (domain : List F) (target : F)
    (hfalse : (domain.map (fun x => p.val.eval x)).sum ≠ target) :
    Pr[fun run => run.closed.map (closedOutputRelation F deg) = some True |
      executeCommitted F deg ($ᵗ F) p q domain target] ≤
        (deg : ENNReal) / Fintype.card F := by
  rw [executeCommitted_eq, probEvent_map]
  simp only [Function.comp_def]
  by_cases hsum : (domain.map (fun x => q.val.eval x)).sum = target
  · have hne : p.val - q.val ≠ 0 := by
      intro h
      have hpq := sub_eq_zero.mp h
      exact hfalse (hpq ▸ hsum)
    have hcard : (Finset.univ.filter (fun r => p.val.eval r = q.val.eval r)).card ≤ deg := by
      apply (Polynomial.card_le_degree_of_subset_roots (p := p.val - q.val) ?_).trans
      · exact natDegree_le_of_degree_le
          ((degree_sub_le _ _).trans (max_le (message_degree F deg p) (message_degree F deg q)))
      · intro r hr
        apply (mem_roots hne).mpr
        simpa only [IsRoot, eval_sub, sub_eq_zero] using (Finset.mem_filter.mp hr).2
    have hevent : (fun r => (committedRun F deg p q domain target r).closed.map
        (closedOutputRelation F deg) = some True) = (fun r => p.val.eval r = q.val.eval r) := by
      funext r
      exact propext ((committedRun_true_iff F deg p q domain target r).trans (and_iff_right hsum))
    rw [hevent, probEvent_uniformSample]
    gcongr
  · have hevent : (fun r => (committedRun F deg p q domain target r).closed.map
        (closedOutputRelation F deg) = some True) = (fun _ => False) := by
      funext r
      apply propext
      rw [committedRun_true_iff]
      simp [hsum]
    rw [hevent]
    simp

/-- Arbitrary randomized commitment, possibly failing, followed by a fresh verifier sample.
The commitment distribution may depend on `p`, the domain and target, but is sampled first. -/
theorem executeRandomCommitment_soundness (messages : ProbComp (Message F deg))
    (p : Message F deg) (domain : List F) (target : F)
    (hfalse : (domain.map (fun x => p.val.eval x)).sum ≠ target) :
    Pr[fun run => run.closed.map (closedOutputRelation F deg) = some True |
      messages >>= fun q => executeCommitted F deg ($ᵗ F) p q domain target] ≤
        (deg : ENNReal) / Fintype.card F := by
  exact probEvent_bind_le_of_forall_le
    (fun q _ => executeCommitted_soundness F deg p q domain target hfalse)

/-- Primary measure-valued soundness on the actual executor's closed output.
No countability assumption on the dependent run type is required. -/
theorem executeCommitted_measureSoundness (p q : Message F deg)
    (domain : List F) (target : F)
    (hfalse : (domain.map (fun x => p.val.eval x)).sum ≠ target) :
    discreteEvalDist (executeCommitted F deg ($ᵗ F) p q domain target)
      {run | run.closed.map (closedOutputRelation F deg) = some True} ≤
        (deg : ENNReal) / Fintype.card F := by
  let : MeasurableSpace
      (CoreRun (protocol F deg) (inputSpec F).toPFunctor (fun _ => F × F)
        (fun _ => outputFamily F deg) (fun _ => F × F)) := ⊤
  have h := executeCommitted_soundness F deg p q domain target hfalse
  rw [probEvent_eq_evalSPMF_toMeasure] at h
  exact h

/-- Primary measure bound for any possibly failing randomized commitment made first. -/
theorem executeRandomCommitment_measureSoundness (messages : ProbComp (Message F deg))
    (p : Message F deg) (domain : List F) (target : F)
    (hfalse : (domain.map (fun x => p.val.eval x)).sum ≠ target) :
    discreteEvalDist
      (messages >>= fun q => executeCommitted F deg ($ᵗ F) p q domain target)
      {run | run.closed.map (closedOutputRelation F deg) = some True} ≤
        (deg : ENNReal) / Fintype.card F := by
  let : MeasurableSpace
      (CoreRun (protocol F deg) (inputSpec F).toPFunctor (fun _ => F × F)
        (fun _ => outputFamily F deg) (fun _ => F × F)) := ⊤
  have h := executeRandomCommitment_soundness F deg messages p domain target hfalse
  rw [probEvent_eq_evalSPMF_toMeasure] at h
  exact h

end
end Sumcheck.Interaction.SingleRound
