/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.ProjectionTransport

/-!
# A Sumcheck round retaining the multivariate oracle

The verifier evaluates the sent univariate message and exports the original multivariate
oracle with the extended challenge vector. This middle interface can feed a later round.
Execution is through `executeCore`; no global protocol append or soundness claim is made.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec Polynomial
open _root_.Interaction.Oracle
open SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- The original multivariate polynomial remains available at every round boundary. -/
def polynomialFamily : OracleFamily Unit (Spec.OracleStatement R n deg) :=
  ⟨fun _ => inferInstance⟩

/-- Input access extended by the actual univariate message. -/
abbrev access :=
  Access.extend (polynomialFamily R n deg).spec.toPFunctor (polynomialInterface R deg)

/-- The output oracle retains the original input behavior. -/
def outputOracle :
    VirtualOracle (OracleSpec.ofPFunctor (access R n deg)) (polynomialFamily R n deg) :=
  ⟨Access.queryPrior (polynomialFamily R n deg).spec.toPFunctor
    (polynomialInterface R deg)⟩

variable {ι : Type} (ambient : OracleSpec ι)

/-- Query and sum the sent message over the domain in list order. -/
def sumQueries : List R → OracleComp (ambient + OracleSpec.ofPFunctor (access R n deg)) R
  | [] => pure 0
  | x :: xs => do
      let y : R ← liftM
        ((ambient + OracleSpec.ofPFunctor (access R n deg)).query (.inr (.inr x)))
      let ys ← sumQueries xs
      return y + ys

/-- The terminal statement uses the sent polynomial's evaluation and extends the prefix. -/
def terminal [DecidableEq R] (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (domain : List R) (r : R) :
    OracleComp (ambient + OracleSpec.ofPFunctor (access R n deg))
      (Option (OpenClaim (OracleSpec.ofPFunctor (access R n deg))
        (Spec.StatementRound R n i.succ) (polynomialFamily R n deg))) := do
  let total ← sumQueries R n deg ambient domain
  if total = stmt.target then
    let value : R ← liftM
      ((ambient + OracleSpec.ofPFunctor (access R n deg)).query (.inr (.inr r)))
    return some ⟨⟨value, Fin.snoc stmt.challenges r⟩, outputOracle R n deg⟩
  else return none

/-- A fixed-challenge verifier with a multivariate input and output interface. -/
def verifier [DecidableEq R] (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (domain : List R) (r : R) :
    Verifier.Strategy ambient (protocol R deg).tree (protocol R deg).roles
      (protocol R deg).oracles (polynomialFamily R n deg).spec.toPFunctor
      (TerminalClaim (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
        (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)) := by
  exact pure (pure ⟨r, terminal R n deg ambient i stmt domain r⟩)

/-- The message is private prover input; the verifier sees only its evaluation interface. -/
def reduction [DecidableEq R] (i : Fin n) (domain : List R) (r : R) :
    _root_.Interaction.Oracle.Reduction ambient (protocol R deg)
      (polynomialFamily R n deg).spec.toPFunctor (Spec.StatementRound R n i.castSucc)
      (Message R deg) (fun _ => R × R)
      (TerminalClaim (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
        (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)) where
  prover := fun _ q => pure (prover R deg ambient q)
  verifier := fun stmt => verifier R n deg ambient i stmt domain r

/-- Successful execution retains arbitrary input behavior, not a reconstructed polynomial. -/
def acceptedRun (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (impl : (polynomialFamily R n deg).Behavior) (q : Message R deg) (r : R) :
    CoreRun (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
      (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)
      (fun _ => R × R) where
  path := ⟨q, r, PUnit.unit⟩
  inputImpl := impl
  proverOut := (q.val.eval r, r)
  outcome := some ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩, outputOracle R n deg⟩

/-- Sum queries evaluate exactly the sent message, independently of the input behavior. -/
theorem simulate_sumQueries (impl : (polynomialFamily R n deg).Behavior) (q : Message R deg)
    (domain : List R) :
    simulateQ (Verifier.liftAccessImpl ambient (access R n deg)
      (Access.extendImpl (polynomialFamily R n deg).spec.toPFunctor
        (polynomialInterface R deg) impl q))
      (sumQueries R n deg ambient domain) =
      pure (domain.map (fun x => q.val.eval x)).sum := by
  induction domain with
  | nil => rfl
  | cons x xs ih =>
      simp only [sumQueries, simulateQ_bind, simulateQ_pure]
      change (pure (q.val.eval x) >>= fun y =>
        simulateQ (Verifier.liftAccessImpl ambient (access R n deg)
          (Access.extendImpl (polynomialFamily R n deg).spec.toPFunctor
            (polynomialInterface R deg) impl q)) (sumQueries R n deg ambient xs) >>= fun ys =>
          pure (y + ys)) = _
      rw [ih]
      simp

/-- The actual terminal computation reads its next target from the sent message. -/
theorem simulate_terminal [DecidableEq R] (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (impl : (polynomialFamily R n deg).Behavior)
    (q : Message R deg) (domain : List R) (r : R) :
    simulateQ (Verifier.liftAccessImpl ambient (access R n deg)
      (Access.extendImpl (polynomialFamily R n deg).spec.toPFunctor
        (polynomialInterface R deg) impl q))
      (terminal R n deg ambient i stmt domain r) =
      pure (if (domain.map (fun x => q.val.eval x)).sum = stmt.target then
        some ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩, outputOracle R n deg⟩
      else none) := by
  simp only [terminal, simulateQ_bind, simulate_sumQueries, pure_bind]
  split
  · rfl
  · rfl

/-- The executor pairs its actual resources in both accepting and rejecting cases. -/
theorem executeCore_eq [DecidableEq R] (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (impl : (polynomialFamily R n deg).Behavior)
    (q : Message R deg) (domain : List R) (r : R) :
    executeCore (reduction R n deg ambient i domain r) impl stmt q =
      pure (if (domain.map (fun x => q.val.eval x)).sum = stmt.target then
        acceptedRun R n deg i stmt impl q r
      else { acceptedRun R n deg i stmt impl q r with outcome := none }) := by
  simp only [executeCore, _root_.Interaction.Oracle.Reduction.execute, reduction, pure_bind]
  change ((simulateQ (Verifier.liftAccessImpl ambient (access R n deg)
      (Access.extendImpl (polynomialFamily R n deg).spec.toPFunctor
        (polynomialInterface R deg) impl q))
      (terminal R n deg ambient i stmt domain r) >>= fun out =>
        pure (⟨⟨q, r, PUnit.unit⟩, (q.val.eval r, r), out⟩ :
          (path : (protocol R deg).tree.ExecutionPath) × (R × R) ×
            TerminalClaim (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
              (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)
              path.toBranchPath)) >>= fun result => pure
        (⟨result.1, impl, result.2.1, result.2.2⟩ :
          CoreRun (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
            (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)
            (fun _ => R × R))) = _
  rw [simulate_terminal]
  split <;> rfl

/-- The executor's own resources give the accepting run whenever the sent sum matches. -/
theorem executeCore_accepted [DecidableEq R] (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (impl : (polynomialFamily R n deg).Behavior)
    (q : Message R deg) (domain : List R) (r : R)
    (h : (domain.map (fun x => q.val.eval x)).sum = stmt.target) :
    executeCore (reduction R n deg ambient i domain r) impl stmt q =
      pure (acceptedRun R n deg i stmt impl q r) := by
  rw [executeCore_eq, if_pos h]

/-- Closing exports exactly the supplied input behavior and the new verifier statement. -/
theorem acceptedRun_closed (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (impl : (polynomialFamily R n deg).Behavior) (q : Message R deg) (r : R) :
    (acceptedRun R n deg i stmt impl q r).closed =
      some (⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩, impl⟩ :
        ClosedClaim (Spec.StatementRound R n i.succ) (polynomialFamily R n deg)) := rfl

/-- The run-derived closed result of an accepting stage preserves its entire input interface. -/
theorem executeCore_closed [DecidableEq R] (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (impl : (polynomialFamily R n deg).Behavior)
    (q : Message R deg) (domain : List R) (r : R)
    (h : (domain.map (fun x => q.val.eval x)).sum = stmt.target) :
    CoreRun.closed <$> executeCore (reduction R n deg ambient i domain r) impl stmt q =
      pure (some (⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩, impl⟩ :
        ClosedClaim (Spec.StatementRound R n i.succ) (polynomialFamily R n deg))) := by
  rw [executeCore_accepted R n deg ambient i stmt impl q domain r h]
  rfl

/-- The receiver executes an ambient challenge program after the oracle send. -/
def sampledVerifier [DecidableEq R] (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (domain : List R)
    (challenge : OracleComp ambient R) :
    Verifier.Strategy ambient (protocol R deg).tree (protocol R deg).roles
      (protocol R deg).oracles (polynomialFamily R n deg).spec.toPFunctor
      (TerminalClaim (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
        (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)) :=
  pure (do
    let r ← OracleComp.liftComp challenge (ambient + OracleSpec.ofPFunctor (access R n deg))
    return ⟨r, terminal R n deg ambient i stmt domain r⟩)

/-- A stage whose challenge effects belong to the actual verifier strategy. -/
def sampledReduction [DecidableEq R] (i : Fin n) (domain : List R)
    (challenge : OracleComp ambient R) :
    _root_.Interaction.Oracle.Reduction ambient (protocol R deg)
      (polynomialFamily R n deg).spec.toPFunctor (Spec.StatementRound R n i.castSucc)
      (Message R deg) (fun _ => R × R)
      (TerminalClaim (protocol R deg) (polynomialFamily R n deg).spec.toPFunctor
        (fun _ => Spec.StatementRound R n i.succ) (fun _ => polynomialFamily R n deg)) where
  prover := fun _ q => pure (prover R deg ambient q)
  verifier := fun stmt => sampledVerifier R n deg ambient i stmt domain challenge

/-- Interpreting resource reads leaves the ambient challenge effect unchanged. -/
theorem simulate_challenge (impl : (polynomialFamily R n deg).Behavior) (q : Message R deg)
    (challenge : OracleComp ambient R) :
    simulateQ (Verifier.liftAccessImpl ambient (access R n deg)
      (Access.extendImpl (polynomialFamily R n deg).spec.toPFunctor
        (polynomialInterface R deg) impl q))
      (OracleComp.liftComp challenge (ambient + OracleSpec.ofPFunctor (access R n deg))) =
        challenge := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
    (fun _ => rfl), simulateQ_id']

set_option backward.isDefEq.respectTransparency false in
/-- Actual sampled execution preserves challenge effects before the corresponding fixed run. -/
theorem executeCore_sampled_eq [DecidableEq R] (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (impl : (polynomialFamily R n deg).Behavior)
    (q : Message R deg) (domain : List R) (challenge : OracleComp ambient R) :
    executeCore (sampledReduction R n deg ambient i domain challenge) impl stmt q =
      (do
        let r ← challenge
        executeCore (reduction R n deg ambient i domain r) impl stmt q) := by
  simp only [executeCore, _root_.Interaction.Oracle.Reduction.execute, sampledReduction,
    reduction, pure_bind]
  simp only [executeStrategies, prover, sampledVerifier, verifier, protocol,
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
  simp only [id_eq, simulateQ_bind, simulateQ_pure, simulate_challenge, bind_assoc, pure_bind]

/-- A closed round relation observes the retained multivariate behavior only. -/
def closedRelation {m : ℕ} (D : Fin m ↪ R) (i : Fin (n + 1))
    (claim : ClosedClaim (Spec.StatementRound R n i) (polynomialFamily R n deg)) : Prop :=
  (∑ x ∈ (Finset.univ.map D) ^ᶠ (n - i),
    claim.oracles ⟨(), Fin.append claim.stmt.challenges x ∘ Fin.cast (by omega)⟩) =
      claim.stmt.target

/-- The honest next statement appends the challenge and uses the projected evaluation. -/
def honestNext {m : ℕ} (D : Fin m ↪ R) (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ()) (r : R) :
    Spec.StatementRound R n i.succ :=
  ⟨(Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval r,
    Fin.snoc stmt.challenges r⟩

/-- Honest execution exports the original polynomial at the actual next statement. -/
theorem executeCore_honest [DecidableEq R] {m : ℕ} (D : Fin m ↪ R) (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ()) (r : R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc) :
    CoreRun.closed <$>
      executeCore (reduction R n deg ambient i (Finset.univ.map D).toList r)
        ((polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)) stmt
        (Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges p) =
      pure (some (⟨honestNext R n deg D i stmt p r,
        (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩ :
          ClosedClaim (Spec.StatementRound R n i.succ) (polynomialFamily R n deg))) := by
  exact executeCore_closed R n deg ambient i stmt _ _ _ r
    (projected_sum_of_relationRound R n deg D i stmt p h)

/-- The honest successor satisfies the next relation, including at the last round. -/
theorem honestNext_related {m : ℕ} (D : Fin m ↪ R) (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ()) (r : R) :
    closedRelation R n deg D i.succ
      ⟨honestNext R n deg D i stmt p r,
        (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩ := by
  exact relationRound_projected_output R n deg D i stmt p r

end
end Sumcheck.Interaction.MultivariateRound
