/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.InducedAdversary
public import ArkLib.Interaction.Oracle.FiatShamir.StoppedCompletionTransport
public import ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget

/-!
# Knowledge security of native single-salt Fiat–Shamir

The adversary selects a statement, one global salt, a full message proof and a terminal seed.
Verification runs the public-message native strategy executor. Both phases share the same lazy
challenge oracle; verification stops before querying a challenge whose prefix guard fails.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec MeasureTheory

namespace Interaction.Oracle.FiatShamir

open Security Security.StateRestoration

universe w

variable {Statement GlobalSalt Witness : Type} {rounds : List Round}

/-- A malicious single-salt prover may interleave private coins and typed challenge queries. -/
abbrev SingleSaltAdversary (Statement GlobalSalt Witness : Type) (rounds : List Round) :=
  OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
    (Option (Statement × SaltedProof GlobalSalt rounds × Witness))

/-- Execute native verification after the selected proof, retaining the adversary phase log.
Failure retains all spent queries. No verifier round is executed after a failed guard. -/
def singleSaltExecution (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) :
    OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
      (Option ((Statement × GlobalSalt) × (protocol rounds).tree.ExecutionPath × Witness) ×
        QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)) := do
  let (selected, log) ← adversary.withQueryLog
  match selected with
  | none => pure (none, log)
  | some (statement, (salt, messages), witness) =>
      let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit rounds)
        (publicStoppedVerify rounds guards (statement, salt) messages)
      pure (path.map (fun p => ((statement, salt), p, witness)), log)

private theorem withQueryLog_map_output {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (f : α → β) (computation : OracleComp spec α) :
    (f <$> computation).withQueryLog =
      (fun result => (f result.1, result.2)) <$> computation.withQueryLog := by
  simp only [map_eq_pure_bind, withQueryLog_bind, withQueryLog_pure,
    pure_bind, Prod.map_apply, id_eq, List.append_nil]

/-- The native joint experiment is exactly the induced stopped-restoration program. -/
theorem singleSaltExecution_eq_stopped
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) :
    singleSaltExecution rounds guards adversary =
      randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards
        (inducedAdversary adversary) := by
  unfold singleSaltExecution randomizedStoppedRestoredExecutionWithAdversaryLog inducedAdversary
  rw [withQueryLog_map_output]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  congr 1
  funext selectedAndLog
  rcases selectedAndLog with ⟨selected, log⟩
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨statement, ⟨salt, messages⟩, witness⟩
      simp only [toRestorationSelection, randomizedStoppedCompletionAfterAdversaryLog,
        publicStoppedVerify_eq_stoppedComplete]

/-- The adversary phase includes its selected proof, ordered logs and final challenge cache. -/
abbrev SingleSaltAdversaryResult (Statement GlobalSalt Witness : Type) (rounds : List Round) :=
  (((Option (Statement × SaltedProof GlobalSalt rounds × Witness) ×
      QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)) ×
        QueryLog (oracleSpec (Statement × GlobalSalt) PUnit rounds)) ×
          (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache)

/-- Expected distinct challenge keys queried by the malicious prover, including failed outputs. -/
noncomputable def expectedSingleSaltAdversaryKeys
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) : ENNReal :=
  letI : MeasurableSpace (SingleSaltAdversaryResult Statement GlobalSalt Witness rounds) := ⊤
  ∫⁻ phase, ((freshKeysOfLog phase.1.2).card : ENNReal)
    ∂𝒟[randomOracleLoggedRun adversary.withQueryLog ∅]

/-- Repackaging a single-salt proof preserves the actual expected distinct adversary cost. -/
theorem expectedSingleSaltAdversaryKeys_eq_induced
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) :
    expectedSingleSaltAdversaryKeys adversary =
      expectedAdversaryFreshKeys rounds (inducedAdversary adversary) := by
  let : MeasurableSpace (SingleSaltAdversaryResult Statement GlobalSalt Witness rounds) := ⊤
  let : MeasurableSpace
      (((Option ((Statement × GlobalSalt) × Messages PUnit rounds × Witness) ×
          QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)) ×
            QueryLog (oracleSpec (Statement × GlobalSalt) PUnit rounds)) ×
              (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache) := ⊤
  unfold expectedSingleSaltAdversaryKeys expectedAdversaryFreshKeys inducedAdversary
  rw [withQueryLog_map_output, randomOracleLoggedRun_map,
    lintegral_evalDist_map_of_discrete]

/-- Native verification performs the prefix checks, then the explicit terminal acceptance check.
The terminal check is pure; source observations use a matched stateless handler. -/
def singleSaltVerify (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (z : Statement × GlobalSalt) (messages : PublicMessages rounds) :
    OracleComp (oracleSpec (Statement × GlobalSalt) PUnit rounds)
      (Option (protocol rounds).tree.ExecutionPath) :=
  (fun path => path.filter (accepts z)) <$> publicStoppedVerify rounds guards z messages

/-- Filter the returned transcript using the terminal check, leaving all phase logs intact. -/
def acceptSingleSaltResult
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (result : Option ((Statement × GlobalSalt) × (protocol rounds).tree.ExecutionPath × Witness) ×
        QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)) :=
  (result.1.filter (fun selected => accepts selected.1 selected.2.1), result.2)

/-- The joint experiment whose returned value records actual prefix and terminal acceptance. -/
def singleSaltAcceptedExecution (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) :=
  acceptSingleSaltResult accepts <$> singleSaltExecution rounds guards adversary

/-- Terminal filtering preserves the exact ordered challenge log and final lazy cache. -/
theorem singleSaltAcceptedExecution_loggedRun
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds)
    (cache : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache) :
    randomOracleLoggedRun (singleSaltAcceptedExecution rounds guards accepts adversary) cache =
      (fun result => ((acceptSingleSaltResult accepts result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun (singleSaltExecution rounds guards adversary) cache := by
  exact randomOracleLoggedRun_map _ _ _

/-- The accepted experiment executes the concrete native verifier after the adversary phase. -/
theorem singleSaltAcceptedExecution_eq_verify
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) :
    singleSaltAcceptedExecution rounds guards accepts adversary = (do
      let (selected, log) ← adversary.withQueryLog
      match selected with
      | none => pure (none, log)
      | some (statement, (salt, messages), witness) =>
          let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit rounds)
            (singleSaltVerify rounds guards accepts (statement, salt) messages)
          pure (path.map (fun p => ((statement, salt), p, witness)), log)) := by
  unfold singleSaltAcceptedExecution singleSaltExecution
  simp only [map_eq_pure_bind, bind_assoc]
  congr 1
  funext selectedAndLog
  rcases selectedAndLog with ⟨selected, log⟩
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨statement, ⟨salt, messages⟩, witness⟩
      simp only [singleSaltVerify, map_eq_pure_bind, simulateQ_bind, simulateQ_pure,
        bind_assoc, pure_bind]
      congr 1
      funext path
      cases path with
      | none => rfl
      | some path =>
          cases h : accepts (statement, salt) path <;>
            simp [acceptSingleSaltResult, Option.filter, h]

/-- Pure terminal rejection changes acceptance, but not the joint run's distinct-query charge. -/
theorem singleSaltAcceptedExecution_expectedCharge
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds)
    (errors : RoundErrors rounds) :
    expectedFreshQueryCharge (singleSaltAcceptedExecution rounds guards accepts adversary)
        (keyError errors) =
      expectedFreshQueryCharge (singleSaltExecution rounds guards adversary) (keyError errors) := by
  let : MeasurableSpace (StoppedJointResult (Statement × GlobalSalt) PUnit Witness rounds) := ⊤
  unfold expectedFreshQueryCharge
  rw [singleSaltAcceptedExecution_loggedRun, lintegral_evalDist_map_of_discrete]

/-- The filtered failure event requires both the actual terminal check and the output relation. -/
theorem badRelation_acceptSingleSaltResult
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) → RoundExtractor (protocol rounds).tree (state z))
    (Rin : (z : Statement × GlobalSalt) → (state z).Witness → Prop)
    (Rout : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Witness → Prop)
    (seed : (z : Statement × GlobalSalt) → (path : (protocol rounds).tree.ExecutionPath) →
      Witness → ((extractor z).terminalState path).Witness)
    (Z : Set (Statement × GlobalSalt))
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (result : Option ((Statement × GlobalSalt) × (protocol rounds).tree.ExecutionPath × Witness) ×
        QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)) :
    badStoppedRelation state extractor Rin Rout seed Z (acceptSingleSaltResult accepts result).1 ↔
      badStoppedRelation state extractor Rin
        (fun z path witness => accepts z path = true ∧ Rout z path witness) seed Z result.1 := by
  rcases result with ⟨selected, log⟩
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨z, path, witness⟩
      cases h : accepts z path <;>
        simp [acceptSingleSaltResult, Option.filter, badStoppedRelation, h]

/-- Native single-salt knowledge security from all-prefix local certificates. Acceptance runs
both the prefix guards and terminal check; extraction uses the supplied terminal seed verbatim. -/
theorem singleSalt_knowledge_soundness
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (errors : RoundErrors rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set (Statement × GlobalSalt))
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (Rin : (z : Statement × GlobalSalt) → (state z).Witness → Prop)
    (Rout : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Witness → Prop)
    (seed : (z : Statement × GlobalSalt) → (path : (protocol rounds).tree.ExecutionPath) →
      Witness → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness, accepts z path = true → Rout z path witness →
      ((extractor z).terminalState path).holds (seed z path witness)) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution rounds guards accepts adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout seed Z joint.1.1.1] ≤
    expectedFreshQueryCharge (singleSaltAcceptedExecution rounds guards accepts adversary)
      (keyError errors) := by
  have bound := randomizedStopped_badRelation_le_expectedFreshCharge rounds guards errors
    (inducedAdversary adversary) state extractor Z preserving bounded Rin
    (fun z path witness => accepts z path = true ∧ Rout z path witness) seed inputLaw
    (fun z path witness accepted => outputLaw z path witness accepted.1 accepted.2)
  rw [← singleSaltExecution_eq_stopped guards adversary] at bound
  rw [singleSaltAcceptedExecution_expectedCharge]
  refine le_trans ?_ bound
  rw [singleSaltAcceptedExecution_loggedRun, prEvent_map]
  exact (prEvent_congr _ _ _
    (fun result : StoppedJointResult (Statement × GlobalSalt) PUnit Witness rounds =>
      badRelation_acceptSingleSaltResult state extractor Rin Rout seed Z accepts result.1.1)).le

/-- Expected cost of verifier challenge calls actually executed in the accepted-output experiment.
Terminal rejection does not erase the calls that preceded it. Cached hits are counted as calls. -/
noncomputable def expectedSingleSaltVerifierCost
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (errors : RoundErrors rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) : ENNReal :=
  letI : MeasurableSpace (StoppedJointResult (Statement × GlobalSalt) PUnit Witness rounds) := ⊤
  ∫⁻ result, stoppedVerifierRoundCost errors result.1.1.2 result.1.2
    ∂𝒟[randomOracleLoggedRun (singleSaltAcceptedExecution rounds guards accepts adversary) ∅]

/-- Native execution preserves the exact expected cost of reached verifier rounds. -/
theorem expectedSingleSaltVerifierCost_eq_stopped
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (errors : RoundErrors rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) :
    expectedSingleSaltVerifierCost guards accepts errors adversary =
      expectedStoppedVerifierRoundCost rounds guards errors (inducedAdversary adversary) := by
  let : MeasurableSpace (StoppedJointResult (Statement × GlobalSalt) PUnit Witness rounds) := ⊤
  unfold expectedSingleSaltVerifierCost expectedStoppedVerifierRoundCost
  rw [singleSaltAcceptedExecution_loggedRun, lintegral_evalDist_map_of_discrete,
    singleSaltExecution_eq_stopped guards adversary]
  rfl

/-- Actual native query costs separate adversary distinct keys from reached verifier calls. -/
theorem singleSalt_query_cost
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (errors : RoundErrors rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) :
    expectedFreshQueryCharge (singleSaltAcceptedExecution rounds guards accepts adversary)
        (keyError errors) ≤
      Finset.univ.sup errors * expectedSingleSaltAdversaryKeys adversary +
        expectedSingleSaltVerifierCost guards accepts errors adversary ∧
    expectedSingleSaltVerifierCost guards accepts errors adversary ≤ ∑ j, errors j := by
  rw [singleSaltAcceptedExecution_expectedCharge,
    singleSaltExecution_eq_stopped guards adversary,
    expectedSingleSaltVerifierCost_eq_stopped guards accepts errors adversary,
    expectedSingleSaltAdversaryKeys_eq_induced]
  constructor
  · simpa only [expectedStoppedJointAdversaryKeys_eq_expectedAdversaryFreshKeys] using
      expectedStoppedFreshCharge_le_actualRounds rounds guards errors (inducedAdversary adversary)
  · exact expectedStoppedVerifierRoundCost_le_sum rounds guards errors (inducedAdversary adversary)

/-- An actual supported-run cap on the malicious prover bounds its expected distinct-key cost. -/
theorem expectedSingleSaltAdversaryKeys_le_queryBound
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    expectedSingleSaltAdversaryKeys adversary ≤ Q := by
  rw [expectedSingleSaltAdversaryKeys_eq_induced]
  apply expectedAdversaryFreshKeys_le_queryBound rounds (inducedAdversary adversary) Q
  intro phase supported
  unfold inducedAdversary at supported
  rw [withQueryLog_map_output, randomOracleLoggedRun_map, support_map] at supported
  obtain ⟨original, originalSupported, rfl⟩ := supported
  exact queryBound original originalSupported

/-- The actual malicious prover query cap yields the standard `Q * max error + sum errors`
bound. The named extractor and seed are fixed independently of the query budget. -/
theorem singleSalt_knowledge_soundness_queryBound
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (errors : RoundErrors rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set (Statement × GlobalSalt))
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (Rin : (z : Statement × GlobalSalt) → (state z).Witness → Prop)
    (Rout : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Witness → Prop)
    (seed : (z : Statement × GlobalSalt) → (path : (protocol rounds).tree.ExecutionPath) →
      Witness → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness, accepts z path = true → Rout z path witness →
      ((extractor z).terminalState path).holds (seed z path witness))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution rounds guards accepts adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout seed Z joint.1.1.1] ≤
    Q * Finset.univ.sup errors + ∑ j, errors j := by
  have security := singleSalt_knowledge_soundness guards accepts errors adversary
    state extractor Z preserving bounded Rin Rout seed inputLaw outputLaw
  have cost := singleSalt_query_cost guards accepts errors adversary
  calc
    _ ≤ expectedFreshQueryCharge (singleSaltAcceptedExecution rounds guards accepts adversary)
          (keyError errors) := security
    _ ≤ Finset.univ.sup errors * expectedSingleSaltAdversaryKeys adversary +
          expectedSingleSaltVerifierCost guards accepts errors adversary := cost.1
    _ ≤ Finset.univ.sup errors * Q + ∑ j, errors j :=
      add_le_add (mul_le_mul' le_rfl (expectedSingleSaltAdversaryKeys_le_queryBound
        adversary Q queryBound)) cost.2
    _ = _ := by rw [mul_comm]

/-- Uniform local errors and an actual adversary cap give the standard `(Q + rounds) * error`
query charge. Early rejection can make the sharper expected-cost bound strictly smaller. -/
theorem singleSalt_uniform_query_cost
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (error : ENNReal)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    expectedFreshQueryCharge (singleSaltAcceptedExecution rounds guards accepts adversary)
      (keyError (fun _ => error)) ≤ (Q + rounds.length : ℕ) * error := by
  have cost := singleSalt_query_cost guards accepts (fun _ => error) adversary
  have maximum : Finset.univ.sup (fun _ : Fin rounds.length => error) ≤ error :=
    Finset.sup_le fun _ _ => le_rfl
  have verifier : expectedSingleSaltVerifierCost guards accepts (fun _ => error) adversary ≤
      (rounds.length : ENNReal) * error := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using cost.2
  calc
    _ ≤ Finset.univ.sup (fun _ : Fin rounds.length => error) *
          expectedSingleSaltAdversaryKeys adversary +
          expectedSingleSaltVerifierCost guards accepts (fun _ => error) adversary := cost.1
    _ ≤ error * Q + (rounds.length : ENNReal) * error :=
      add_le_add (mul_le_mul' maximum
        (expectedSingleSaltAdversaryKeys_le_queryBound adversary Q queryBound)) verifier
    _ = _ := by rw [Nat.cast_add, add_mul, mul_comm error (Q : ENNReal)]

end Interaction.Oracle.FiatShamir
