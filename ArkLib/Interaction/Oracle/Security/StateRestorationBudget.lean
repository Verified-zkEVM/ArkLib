/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationOracle
public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Nonuniform round errors in state restoration

Each fixed protocol round has its own knowledge error. Completion pays the sum of those errors;
an adaptive adversary with at most `Q` queries pays `Q` times their maximum. The same actual closed
oracle-output game and named backward extraction therefore have error at most
`Q * max_j error_j + sum_j error_j`. Challenge samplers remain uniform within each round.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

/-- A vector of local knowledge errors, indexed in protocol order. -/
abbrev RoundErrors (rounds : List Round) := Fin rounds.length → ENNReal

/-- Every receiver samples its round's uniform challenge with that round's local error. -/
def roundErrorSchedule : (rounds : List Round) → RoundErrors rounds →
    RoundExtractor.ChallengeSchedule (protocol rounds).tree (protocol rounds).roles
  | [], _ => PUnit.unit
  | round :: rounds, errors => fun _ => ⟨⟨$ᵗ round.Challenge, errors 0⟩,
      fun _ => roundErrorSchedule rounds (fun j => errors j.succ)⟩

/-- The charge of a restoration key is the local error at its round. -/
def keyError {Input Salt : Type} : {rounds : List Round} → RoundErrors rounds →
    Key Input Salt rounds → ENNReal
  | [], _, key => nomatch key
  | _ :: _, errors, .inl _ => errors 0
  | _ :: _, errors, .inr (_, _, key) => keyError (fun j => errors j.succ) key

/-- Every key charge is bounded by the maximum round error, including zero or infinite errors. -/
theorem keyError_le_max {Input Salt : Type} {rounds : List Round}
    (errors : RoundErrors rounds) (key : Key Input Salt rounds) :
    keyError errors key ≤ Finset.univ.sup errors := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl _ => exact Finset.le_sup (Finset.mem_univ (0 : Fin (rounds.length + 1)))
      | inr data =>
          apply (ih (fun j => errors j.succ) data.2.2).trans
          apply Finset.sup_le
          intro j _
          exact Finset.le_sup (Finset.mem_univ j.succ)

/-- All authored-prefix local bounds apply to each key's reconstructed pre-challenge state. -/
theorem keyExtractor_round_bound {Input Salt : Type} {rounds : List Round}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (protocol rounds).tree state)
    (errors : RoundErrors rounds)
    (bounded : RoundExtractor.IsLocallyBounded extractor (protocol rounds).roles
      (roundErrorSchedule rounds errors))
    (key : Key Input Salt rounds) (table : Table Input Salt rounds) :
    Pr{let response ← $ᵗ key.Challenge}[
      RoundExtractor.badChallenge (keyExtractor extractor key table).2 response] ≤
      keyError errors key := by
  induction rounds generalizing state with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl data =>
          rcases data with ⟨z, message, salt⟩
          exact (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp
            (bounded message).1 PUnit.unit PUnit.unit
      | inr data =>
          rcases data with ⟨message, salt, key⟩
          exact ih ((extractor message).2.2 (table (Key.here key.input message salt))).2.2
            (fun j => errors j.succ) ((bounded message).2 (table (Key.here key.input message salt)))
            key (fun q => table (Key.later message salt q))

/-- Resampling a key in any background table has bad-event probability at most its round error. -/
theorem badKey_round_resample_bound {Input Salt : Type} {rounds : List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (errors : RoundErrors rounds)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (roundErrorSchedule rounds errors))
    (key : Key Input Salt rounds) (table : Table Input Salt rounds) :
    Pr{let response ← $ᵗ key.Challenge}[
      badKey state extractor Z key (Function.update table key response)] ≤ keyError errors key := by
  have hevent : ∀ response, badKey state extractor Z key (Function.update table key response) ↔
      key.input ∈ Z ∧
        RoundExtractor.badChallenge (keyExtractor (extractor key.input) key table).2 response := by
    intro response
    unfold badKey
    rw [keyExtractor_update]
    simp
  simp_rw [hevent]
  by_cases hz : key.input ∈ Z
  · simp only [hz, true_and]
    exact keyExtractor_round_bound (extractor key.input) errors (bounded key.input hz) key table
  · simp only [hz, false_and]
    simp

/-- Routing a suffix key retains its round charge exactly, on every complete execution path. -/
theorem costDist_prependQuery {Input Salt A : Type} {round : Round} {rounds : List Round}
    (errors : RoundErrors (round :: rounds)) (message : round.Message) (salt : Salt)
    (program : OracleComp (oracleSpec Input Salt rounds) A) :
    costDist (simulateQ (prependQuery message salt) program)
        (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) =
      simulateQ (prependQuery message salt)
        (costDist program (⟨keyError (fun j => errors j.succ)⟩ :
          CostModel (oracleSpec Input Salt rounds) ENNReal)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [costDist, instrumentedRun]
  | query_bind key next ih =>
      simp only [costDist, instrumentedRun, QueryImpl.withAddCost, QueryImpl.ofLift_eq_id'] at ih
      simp [costDist, instrumentedRun, QueryImpl.withAddCost, prependQuery, OracleSpec.query,
        WriterT.run_bind, simulateQ_bind, simulateQ_query, bind_assoc, keyError, ih]

/-- A `Q`-query adversary pays at most `Q` times the largest round error on every branch. -/
theorem queryBound_round_cost {Input Salt A : Type} {rounds : List Round}
    (errors : RoundErrors rounds) (program : OracleComp (oracleSpec Input Salt rounds) A)
    (Q : Nat) (bounded : IsTotalQueryBound program Q) :
    WorstCaseCostBound program (⟨keyError errors⟩ :
      CostModel (oracleSpec Input Salt rounds) ENNReal) (Q * Finset.univ.sup errors) := by
  induction program using OracleComp.inductionOn generalizing Q with
  | pure value => simp
  | query_bind key next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro response result supported
      have tail := ih response (Q - 1) (bounded.2 response) result supported
      calc
        keyError errors key + Multiplicative.toAdd result.2 ≤
            Finset.univ.sup errors + (Q - 1 : Nat) * Finset.univ.sup errors :=
          add_le_add (keyError_le_max errors key) tail
        _ = Q * Finset.univ.sup errors := by
          have hQ : Q = (Q - 1) + 1 := by omega
          conv_rhs => rw [hQ]
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- The native suffix-key injection preserves a complete-path error budget. -/
theorem roundCost_prependQuery {Input Salt A : Type} {round : Round} {rounds : List Round}
    (errors : RoundErrors (round :: rounds)) (message : round.Message) (salt : Salt)
    (program : OracleComp (oracleSpec Input Salt rounds) A) (budget : ENNReal)
    (bounded : WorstCaseCostBound program (⟨keyError (fun j => errors j.succ)⟩ :
      CostModel (oracleSpec Input Salt rounds) ENNReal) budget) :
    WorstCaseCostBound (simulateQ (prependQuery message salt) program)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) budget := by
  intro result supported
  change result ∈ support (costDist _ _) at supported
  rw [costDist_prependQuery] at supported
  exact bounded result (simulateQ_support_subset _ _ supported)

/-- Completion pays one round error per actual access, hence the sum of the round-error vector. -/
theorem complete_round_cost {Input Salt : Type} (rounds : List Round) (errors : RoundErrors rounds)
    (z : Input) (messages : Messages Salt rounds) :
    WorstCaseCostBound (complete rounds z messages)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal) (∑ j, errors j) := by
  induction rounds with
  | nil => simp [complete, protocol, Protocol.done]
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, List.length_cons]
      rw [Fin.sum_univ_succ]
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro challenge result supported
      have tail := roundCost_prependQuery errors message salt (complete rounds z messages) _
        (ih (fun j => errors j.succ) messages)
      have combined := tail.bind (fun path => show WorstCaseCostBound
        (pure (⟨message, challenge, path⟩ : (protocol (round :: rounds)).tree.ExecutionPath))
          (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) 0 from
            by simp)
      have hcost := combined result supported
      simpa only [keyError, add_zero, zero_add, add_comm] using add_le_add_left hcost (errors 0)

/-- Adversary and completion budgets add in the same actual restoration oracle program. -/
theorem restoredExecution_round_cost {Input Salt W : Type} (rounds : List Round)
    (errors : RoundErrors rounds)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : Nat) (bounded : IsTotalQueryBound adversary Q) :
    WorstCaseCostBound (restoredExecution rounds adversary)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal)
      (Q * Finset.univ.sup errors + ∑ j, errors j) := by
  apply (queryBound_round_cost errors adversary Q bounded).bind
  rintro ⟨z, messages, witness⟩
  have completed := (complete_round_cost rounds errors z messages).bind
    (fun path => show WorstCaseCostBound (pure (z, path, witness))
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal) 0 from by simp)
  simpa only [add_zero] using completed

/-- Per-round knowledge errors imply the `Q * max + sum` extraction bound in the actual cached
restoration experiment. Inputs may be adaptive and keys may be queried out of order or repeatedly.
The terminal witness is supplied by the adversary; extraction remains the named native backward map.
The sum budget is proved for completion, rather than assumed independent of earlier accesses. -/
theorem restored_extraction_round_bound {Input Salt W : Type} {rounds : List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (errors : RoundErrors rounds)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (roundErrorSchedule rounds errors))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (restoredExecution rounds adversary)).run' ∅}[
      result.1 ∈ Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  apply prEvent_randomOracle_le_of_bad_queries_weighted _ (keyError errors) _
    (restoredExecution_round_cost rounds errors adversary Q queryBound) _
    (badKey state extractor Z)
  · exact badKey_round_resample_bound state extractor Z errors bounded
  · exact restored_bad_trace state extractor Z preserving terminalWitness adversary

/-- The actual closed-oracle verification game has knowledge error at most `Q * max + sum` for
an arbitrary adaptive `Q`-query adversary and distinct all-prefix local round errors. The output
relation observes this same run's closed virtual behavior; rejection `none` is unsuccessful.
The named terminal-witness equivalence and exact input/output relation laws link the certificate
to the actual source-only terminal program. No finite input or salt domain is required. -/
theorem stateRestoration_oracle_knowledge_soundness_nonuniform
    {Input Salt : Type} {rounds : List Round} {W : Type}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (errors : RoundErrors rounds)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (roundErrorSchedule rounds errors))
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      ClosedClaim (Stmt z p) (family z p) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        ∃ claim, closedTerminalObservation initial impl Stmt family terminal z path = some claim ∧
          Rout z path.toBranchPath claim witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
        (closedVerificationGame initial impl Stmt family terminal adversary)).run' ∅}[
      result.1 ∈ Z ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness state extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ Q * Finset.univ.sup errors + ∑ j, errors j := by
  rw [closedVerificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  simp only [extractInputWitness, ← inputLaw, ← outputLaw]
  exact restored_extraction_round_bound state extractor Z errors preserving bounded
    (fun z path => terminalWitness z path) adversary Q queryBound

end Interaction.Oracle.Security.StateRestoration
