/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.CoreRun
import ArkLib.Interaction.Oracle.Resource

/-! # Single-round Sumcheck through run-derived closing -/

namespace Sumcheck.Interaction.SingleRound

open OracleComp OracleSpec Polynomial
open _root_.Interaction.Oracle

noncomputable section

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- The single polynomial output family keeps its explicit evaluation interface. -/
def outputFamily : OracleFamily Unit (fun _ => Message R deg) :=
  ⟨fun _ => polynomialInterface R deg⟩

/-- The output oracle routes queries to the original input polynomial. -/
def outputView : VirtualOracle (OracleSpec.ofPFunctor (access R deg)) (outputFamily R deg) where
  query := fun q => liftM ((OracleSpec.ofPFunctor (access R deg)).query (.inl q.2))

/-- Package a terminal scalar result with the input-oracle passthrough plan. -/
def outputClaim (stmt : R × R) :
    OracleClaim (OracleSpec.ofPFunctor (access R deg)) (R × R) (outputFamily R deg) :=
  ⟨stmt, outputView R deg⟩

/-- Degree metadata is interpreted on the exact object type sent by the protocol. -/
def degreeCatalog : ResourceCatalog Unit (fun _ => R) (fun _ => Message R deg)
    Unit Unit (fun _ => ℕ) where
  source := fun _ => ⟨inputSpec R, fun x p => p.val.eval x⟩
  owner := fun _ => ()
  origin := fun _ => ()
  meaning := fun _ bound p => p.val.degree ≤ bound
  required := fun _ bound => bound = deg
  valid := by
    intro _ bound h p
    subst bound
    exact Polynomial.mem_degreeLE.mp p.property

/-- The selected degree guarantee is the protocol's actual bound. -/
def degreeGuarantee : (degreeCatalog R deg).Guarantee () := ⟨deg, rfl⟩

/-- Clients recover the bound through the resource guarantee interpretation. -/
theorem message_degree (p : Message R deg) : p.val.degree ≤ deg :=
  (degreeCatalog R deg).realizes () (degreeGuarantee R deg) p

variable {ι : Type} (ambient : OracleSpec ι)

/-- The restricted verifier emits an open claim only after the sum check succeeds. -/
def claimVerifier [DecidableEq R] (domain : List R) (target r : R) :
    Verifier.Strategy ambient (protocol R deg).tree (protocol R deg).roles
      (protocol R deg).oracles (inputSpec R).toPFunctor
      (TerminalClaim (protocol R deg) (inputSpec R).toPFunctor
        (fun _ => R × R) (fun _ => outputFamily R deg)) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
    (OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
      (Σ _ : R, OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
        (Option (OracleClaim (OracleSpec.ofPFunctor (access R deg))
          (R × R) (outputFamily R deg)))))
  exact pure (pure ⟨r, Option.map (outputClaim R deg) <$>
    terminal R deg ambient domain target r⟩)

/-- The actual reduction package used by the trace-free executor. -/
def claimReduction [DecidableEq R] (domain : List R) (r : R) :
    _root_.Interaction.Oracle.Reduction ambient (protocol R deg) (inputSpec R).toPFunctor
      R (Message R deg) (fun _ => R × R)
      (TerminalClaim (protocol R deg) (inputSpec R).toPFunctor
        (fun _ => R × R) (fun _ => outputFamily R deg)) where
  prover := fun _ p => pure (prover R deg ambient p)
  verifier := fun target => claimVerifier R deg ambient domain target r

/-- The accepting paired run for an honest polynomial at a prescribed challenge. -/
def honestRun (p : Message R deg) (r : R) :
    CoreRun (protocol R deg) (inputSpec R).toPFunctor (fun _ => R × R)
      (fun _ => outputFamily R deg) (fun _ => R × R) where
  path := ⟨p, r, PUnit.unit⟩
  inputImpl := inputImpl R deg p
  proverOut := (p.val.eval r, r)
  outcome := some (outputClaim R deg (p.val.eval r, r))

/-- The actual executor produces the paired honest run, pointwise in the challenge. -/
theorem executeCore_honest [DecidableEq R] (p : Message R deg)
    (domain : List R) (target r : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    executeCore (claimReduction R deg ambient domain r) (inputImpl R deg p) target p =
      pure (honestRun R deg p r) := by
  simp only [executeCore, _root_.Interaction.Oracle.Reduction.execute, claimReduction,
    pure_bind]
  change ((simulateQ (Verifier.readImpl ambient (access R deg)
      (Access.extendImpl (inputSpec R).toPFunctor (polynomialInterface R deg)
        (inputImpl R deg p) p))
      (Option.map (outputClaim R deg) <$> terminal R deg ambient domain target r) >>= fun out =>
        pure (⟨⟨p, r, PUnit.unit⟩, (p.val.eval r, r), out⟩ :
          (path : (protocol R deg).tree.ExecutionPath) × (R × R) ×
            TerminalClaim (protocol R deg) (inputSpec R).toPFunctor
              (fun _ => R × R) (fun _ => outputFamily R deg) path.toBranchPath)) >>=
      fun result => pure (⟨result.1, inputImpl R deg p, result.2.1, result.2.2⟩ :
        CoreRun (protocol R deg) (inputSpec R).toPFunctor (fun _ => R × R)
          (fun _ => outputFamily R deg) (fun _ => R × R))) = _
  rw [simulateQ_map, simulate_terminal, if_pos h]
  rfl

/-- The honest data claim used solely to express output realization. -/
def honestData (p : Message R deg) (r : R) : DataClaim (R × R) (outputFamily R deg) :=
  ⟨(p.val.eval r, r), fun _ => p⟩

/-- Closing derives the output behavior from the run's input and actual message. -/
theorem honestRun_closed (p : Message R deg) (r : R) :
    (honestRun R deg p r).closed = some (honestData R deg p r).toClosed := by
  rfl

/-- Programmatic perfect completeness through the new run-derived relation boundary. -/
theorem executeCore_closed [DecidableEq R] (p : Message R deg)
    (domain : List R) (target r : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    CoreRun.closed <$> executeCore (claimReduction R deg ambient domain r)
        (inputImpl R deg p) target p =
      pure (some (honestData R deg p r).toClosed) := by
  rw [executeCore_honest R deg ambient p domain target r h]
  rfl

/-- The output relation observes only the statement and evaluation behavior. -/
def closedOutputRelation (claim : ClosedClaim (R × R) (outputFamily R deg)) : Prop :=
  claim.oracles ⟨(), claim.stmt.2⟩ = claim.stmt.1

/-- The input relation is likewise stated entirely at the behavior boundary. -/
def closedInputRelation (domain : List R)
    (claim : ClosedClaim R (outputFamily R deg)) : Prop :=
  (domain.map (fun x => claim.oracles ⟨(), x⟩)).sum = claim.stmt

/-- Every accepting honest run satisfies the output relation after run-derived closing. -/
theorem honestRun_closed_related (p : Message R deg) (r : R) :
    (honestRun R deg p r).closed.map (closedOutputRelation R deg) = some True := by
  change some (p.val.eval r = p.val.eval r) = some True
  simp

/-- Programmatic completeness observes the relation on the executor's own closed output. -/
theorem executeCore_complete [DecidableEq R] (p : Message R deg)
    (domain : List R) (target r : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    (fun run => run.closed.map (closedOutputRelation R deg)) <$>
      executeCore (claimReduction R deg ambient domain r) (inputImpl R deg p) target p =
        pure (some True) := by
  rw [executeCore_honest R deg ambient p domain target r h]
  simp only [map_pure, honestRun_closed_related]

/-- The real message guarantee and actual closed execution are simultaneously certified. -/
theorem executeCore_degree_complete [DecidableEq R] (p : Message R deg)
    (domain : List R) (target r : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    p.val.degree ≤ deg ∧
      ((fun run => run.closed.map (closedOutputRelation R deg)) <$>
        executeCore (claimReduction R deg ambient domain r) (inputImpl R deg p) target p =
          pure (some True)) :=
  ⟨message_degree R deg p, executeCore_complete R deg ambient p domain target r h⟩

/-- The verifier samples its ambient challenge at the public receiver node after the send. -/
def sampledClaimVerifier [DecidableEq R] (domain : List R) (target : R)
    (challenge : OracleComp ambient R) :
    Verifier.Strategy ambient (protocol R deg).tree (protocol R deg).roles
      (protocol R deg).oracles (inputSpec R).toPFunctor
      (TerminalClaim (protocol R deg) (inputSpec R).toPFunctor
        (fun _ => R × R) (fun _ => outputFamily R deg)) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
    (OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
      (Σ _ : R, OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
        (Option (OracleClaim (OracleSpec.ofPFunctor (access R deg))
          (R × R) (outputFamily R deg)))))
  exact pure (do
    let r ← OracleComp.liftComp challenge (ambient + OracleSpec.ofPFunctor (access R deg))
    return ⟨r, Option.map (outputClaim R deg) <$> terminal R deg ambient domain target r⟩)

/-- A randomized package; its verifier owns the challenge effect at the receiver phase. -/
def sampledClaimReduction [DecidableEq R] (domain : List R)
    (challenge : OracleComp ambient R) :
    _root_.Interaction.Oracle.Reduction ambient (protocol R deg) (inputSpec R).toPFunctor
      R (Message R deg) (fun _ => R × R)
      (TerminalClaim (protocol R deg) (inputSpec R).toPFunctor
        (fun _ => R × R) (fun _ => outputFamily R deg)) where
  prover := fun _ p => pure (prover R deg ambient p)
  verifier := fun target => sampledClaimVerifier R deg ambient domain target challenge

/-- The source interpreter forwards challenge effects without reordering or interpreting them. -/
theorem simulate_challenge (p : Message R deg) (challenge : OracleComp ambient R) :
    simulateQ (Verifier.readImpl ambient (access R deg)
      (Access.extendImpl (inputSpec R).toPFunctor (polynomialInterface R deg)
        (inputImpl R deg p) p))
      (OracleComp.liftComp challenge (ambient + OracleSpec.ofPFunctor (access R deg))) =
        challenge := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
    (fun _ => rfl), simulateQ_id']

/-- The actual randomized verifier executes inside the paired runner. -/
def executeSampled [DecidableEq R] (challenge : ProbComp R) (p : Message R deg)
    (domain : List R) (target : R) :=
  executeCore (sampledClaimReduction R deg unifSpec domain challenge)
    (inputImpl R deg p) target p

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise honest execution transports any challenge kernel to the actual paired runs. -/
theorem executeSampled_eq [DecidableEq R] (challenge : ProbComp R) (p : Message R deg)
    (domain : List R) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    executeSampled R deg challenge p domain target = honestRun R deg p <$> challenge := by
  simp only [executeSampled, executeCore, _root_.Interaction.Oracle.Reduction.execute,
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
  simp only [id_eq, simulateQ_bind, simulateQ_pure, simulate_challenge, bind_assoc, pure_bind,
    simulateQ_map, simulate_terminal, if_pos h, map_pure]
  simp only [bind_pure_comp]
  rfl

/-- Every supported sampled run accepts a claim satisfying the closed output relation. -/
theorem executeSampled_support [DecidableEq R] (challenge : ProbComp R) (p : Message R deg)
    (domain : List R) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target)
    (run : CoreRun (protocol R deg) (inputSpec R).toPFunctor (fun _ => R × R)
      (fun _ => outputFamily R deg) (fun _ => R × R))
    (hrun : run ∈ support (executeSampled R deg challenge p domain target)) :
    run.closed.map (closedOutputRelation R deg) = some True := by
  rw [executeSampled_eq R deg challenge p domain target h] at hrun
  rw [support_map] at hrun
  obtain ⟨r, _, rfl⟩ := hrun
  exact honestRun_closed_related R deg p r

/-- A lossless challenge kernel gives perfect completeness in VCVio's probability semantics. -/
theorem executeSampled_perfectCompleteness [DecidableEq R] (challenge : ProbComp R)
    (hchallenge : Pr[⊥ | challenge] = 0) (p : Message R deg)
    (domain : List R) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    Pr[fun run => run.closed.map (closedOutputRelation R deg) = some True |
      executeSampled R deg challenge p domain target] = 1 := by
  apply probEvent_eq_one_iff.mpr
  constructor
  · rw [executeSampled_eq R deg challenge p domain target h, probFailure_map]
    exact hchallenge
  · intro run hrun
    exact executeSampled_support R deg challenge p domain target h run hrun

/-- Primary measure-valued completeness for the actual randomized verifier.
The challenge's total successful mass is one; no countability assumption on runs is needed. -/
theorem executeSampled_measure_complete [DecidableEq R] (challenge : ProbComp R)
    (hchallenge : discreteEvalDist challenge Set.univ = 1) (p : Message R deg)
    (domain : List R) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    discreteEvalDist (executeSampled R deg challenge p domain target)
      {run | run.closed.map (closedOutputRelation R deg) = some True} = 1 := by
  let : MeasurableSpace R := ⊤
  have hmass : Pr[fun _ => True | challenge] = 1 := by
    rw [probEvent_eq_evalSPMF_toMeasure]
    exact hchallenge
  have hfailure : Pr[⊥ | challenge] = 0 := (probEvent_eq_one_iff.mp hmass).1
  let : MeasurableSpace
      (CoreRun (protocol R deg) (inputSpec R).toPFunctor (fun _ => R × R)
        (fun _ => outputFamily R deg) (fun _ => R × R)) := ⊤
  have hprob := executeSampled_perfectCompleteness R deg challenge hfailure p domain target h
  rw [probEvent_eq_evalSPMF_toMeasure] at hprob
  exact hprob

end
end Sumcheck.Interaction.SingleRound
