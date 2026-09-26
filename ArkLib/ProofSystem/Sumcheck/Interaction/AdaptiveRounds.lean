/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.ArbitraryRounds
public import VCVio.OracleComp.EvalDist

/-!
# Adaptive randomized Sumcheck rounds

Every boundary carries the actual closed multivariate oracle and a private prover state `σ`.
The prover samples its next degree-bounded message and updated private state using the current
statement and carried private state. The existing sampled verifier then draws a fresh uniform
challenge, after the message has been sent. Accepted execution passes the run-derived closed
claim and updated private state to the next actual stage; rejection skips the suffix.

This module provides execution adapters and exact execution equations. Probability bounds are
separate from these definitions.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ) (σ : Type)

/-- Consecutive round interfaces retaining the same private state type at every boundary. -/
abbrev adaptiveInterfaces (start count : ℕ) (bound : start + count ≤ n)
    (j : Fin (count + 1)) : ExecutionInterface where
  Stmt := Spec.StatementRound R n ⟨start + j, by omega⟩
  Index := Unit
  Realization := Spec.OracleStatement R n deg
  oracles := polynomialFamily R n deg
  Private := σ

variable [DecidableEq R] [SampleableType R]

/-- A prover samples its message before the receiver challenge and retains its updated state. -/
def adaptiveProver (chosen : Message R deg × σ) :
    Prover.Strategy unifSpec (protocol R deg).tree (protocol R deg).roles (fun _ => σ) :=
  pure ⟨chosen.1, fun _ => pure chosen.2⟩

/-- Actual randomized message selection followed by the existing uniformly sampled verifier. -/
def adaptiveReduction (i : Fin n) (domain : List R)
    (messages : Spec.StatementRound R n i.castSucc → σ → ProbComp (Message R deg × σ)) :
    _root_.Interaction.Oracle.Reduction unifSpec (protocol R deg)
      (polynomialFamily R n deg).spec.toPFunctor (Spec.StatementRound R n i.castSucc)
      σ (fun _ => σ)
      (TerminalClaim (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
        (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)) where
  prover := fun stmt state => adaptiveProver R deg σ <$> messages stmt state
  verifier := fun stmt => sampledVerifier R n deg unifSpec i stmt domain ($ᵗ R)

/-- Ordered stages whose message distributions adapt to the current statement and private state. -/
def adaptiveStages (start count : ℕ) (bound : start + count ≤ n) (domain : List R)
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc →
      σ → ProbComp (Message R deg × σ))
    (j : Fin count) :
    ClosedStage unifSpec (adaptiveInterfaces R n deg σ start count bound j.castSucc)
      (adaptiveInterfaces R n deg σ start count bound j.succ) where
  protocol := fun _ => protocol R deg
  Witness := fun _ => σ
  OutP := fun _ _ => σ
  witness := fun _ state => state
  nextPrivate := fun _ _ _ updated => updated
  reduction := fun _ => adaptiveReduction R n deg σ ⟨start + j, by omega⟩ domain
    (messages ⟨start + j, by omega⟩)

set_option backward.isDefEq.respectTransparency false in
/-- An adaptive stage first samples the prover's message and updated state, then executes the
existing sampled reduction with that message. Closing uses the actual input oracle behavior,
and acceptance carries the sampled updated state. -/
theorem adaptiveStages_run (start count : ℕ) (bound : start + count ≤ n) (domain : List R)
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc →
      σ → ProbComp (Message R deg × σ))
    (j : Fin count)
    (input : (adaptiveInterfaces R n deg σ start count bound j.castSucc).State) :
    (adaptiveStages R n deg σ start count bound domain messages j).run input = (do
      let chosen ← messages ⟨start + j, by omega⟩ input.1.stmt input.2
      let closed ← CoreRun.closed <$> executeCore
        (sampledReduction R n deg unifSpec ⟨start + j, by omega⟩ domain ($ᵗ R))
        input.1.oracles input.1.stmt chosen.1
      return closed.map (fun claim => (claim, chosen.2))) := by
  rw [ClosedStage.run_eq_executeCore]
  simp only [adaptiveStages, adaptiveReduction, executeCore,
    _root_.Interaction.Oracle.Reduction.execute, sampledReduction,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp only [executeStrategies, prover, sampledVerifier, protocol,
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
  simp only [simulateQ_bind, simulateQ_pure, simulate_challenge, bind_assoc, pure_bind]
  rfl

/-- Execute consecutive adaptive rounds through the actual ordered closed-stage executor. -/
def executeAdaptiveRounds (start count : ℕ) (bound : start + count ≤ n) (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R n ⟨start, by omega⟩)
      (polynomialFamily R n deg)) (privateState : σ)
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc →
      σ → ProbComp (Message R deg × σ)) :
    ProbComp (Option (ClosedClaim (Spec.StatementRound R n ⟨start + count, by omega⟩)
      (polynomialFamily R n deg) × σ)) :=
  OrderedExecution.run count (adaptiveInterfaces R n deg σ start count bound)
    (adaptiveStages R n deg σ start count bound domain messages) (input, privateState)

/-- An empty adaptive interval retains both the original closed oracle and private state. -/
@[simp]
theorem executeAdaptiveRounds_zero (start : ℕ) (bound : start + 0 ≤ n) (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R n ⟨start, by omega⟩)
      (polynomialFamily R n deg)) (privateState : σ)
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc →
      σ → ProbComp (Message R deg × σ)) :
    executeAdaptiveRounds R n deg σ start 0 bound domain input privateState messages =
      pure (some (input, privateState)) := rfl

end
end Sumcheck.Interaction.MultivariateRound
