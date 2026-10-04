/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationStopped

/-!
# Expected cost of actual stopped verification

The joint cached run charges each distinct restoration key once. Its adversary phase keeps all
queries, even if the adversary returns failure. Its verifier phase pays only the round-error sum
for challenge calls that actually execute before the first rejecting guard. The expectation-level
bound uses this same stopped run, without completing a padded suffix.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : List Round}

/-- The full result of a stopped logged random-oracle run, including the source phase log and
the final hash log and cache. -/
abbrev StoppedJointResult (Input Salt W : Type) (rounds : List Round) :=
  (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache)

/-- The actual expected number of distinct adversary hash keys, read from the retained source
phase of the stopped joint run. Failure branches remain in this expectation. -/
noncomputable def expectedStoppedJointAdversaryKeys
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) : ENNReal :=
  letI : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  ∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
    ∂𝒟[randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅]

/-- Expected sum of local errors over verifier rounds actually queried before stopping. This
counts executed calls even when they hit an adversarially populated cache. -/
noncomputable def expectedStoppedVerifierRoundCost
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) : ENNReal :=
  letI : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  ∫⁻ result, stoppedVerifierRoundCost errors result.1.1.2 result.1.2
    ∂𝒟[randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅]

/-- The actual random-oracle support inherits the fixed-table bound on distinct charge. -/
theorem randomOracle_stopped_freshCharge_le_actualRounds
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (result : StoppedJointResult Input Salt W rounds)
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      (adversaryHashKeys result.1.1.2).card * Finset.univ.sup errors +
        stoppedVerifierRoundCost errors result.1.1.2 result.1.2 := by
  obtain ⟨table, htable⟩ := mem_support_fixedTableLoggedRun_of_randomOracle
    (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
    ∅ result supported
  exact fixedTable_stopped_freshCharge_le_actualRounds rounds guards errors
    adversary table result htable

/-- The actual random-oracle support pays no more than the full schedule's round-error sum
in the verifier phase, including rejected runs. -/
theorem randomOracle_stopped_verifierCost_le_sum
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (result : StoppedJointResult Input Salt W rounds)
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅)) :
    stoppedVerifierRoundCost errors result.1.1.2 result.1.2 ≤ ∑ j, errors j := by
  obtain ⟨table, htable⟩ := mem_support_fixedTableLoggedRun_of_randomOracle
    (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
    ∅ result supported
  exact fixedTable_stopped_verifierCost_le_sum rounds guards errors
    adversary table result htable

/-- The first resource inequality for the actual stopped run: expected distinct-key charge
is bounded by adversary distinct keys plus exactly the cost of executed verifier rounds. -/
theorem expectedStoppedFreshCharge_le_actualRounds
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedFreshQueryCharge
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
      (keyError errors) ≤
      Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards adversary +
      expectedStoppedVerifierRoundCost rounds guards errors adversary := by
  let program := randomizedStoppedRestoredExecutionWithAdversaryLog
    rounds guards adversary
  let : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  have hae := evalDist.ae_of_forall_mem_support
    (randomOracleLoggedRun program ∅)
    (fun result => freshQueryCharge (keyError errors) result.1.2 ≤
      Finset.univ.sup errors * (adversaryHashKeys result.1.1.2).card +
        stoppedVerifierRoundCost errors result.1.1.2 result.1.2)
    MeasurableSet.of_discrete
    (fun result hresult => by
      have h := randomOracle_stopped_freshCharge_le_actualRounds
        rounds guards errors adversary result hresult
      simpa only [mul_comm] using h)
  change (∫⁻ result, freshQueryCharge (keyError errors) result.1.2
    ∂𝒟[randomOracleLoggedRun program ∅]) ≤ _
  calc
    (∫⁻ result, freshQueryCharge (keyError errors) result.1.2
      ∂𝒟[randomOracleLoggedRun program ∅]) ≤
        ∫⁻ result, Finset.univ.sup errors *
          (adversaryHashKeys result.1.1.2).card +
          stoppedVerifierRoundCost errors result.1.1.2 result.1.2
          ∂𝒟[randomOracleLoggedRun program ∅] := lintegral_mono_ae hae
    _ = Finset.univ.sup errors *
          expectedStoppedJointAdversaryKeys rounds guards adversary +
          expectedStoppedVerifierRoundCost rounds guards errors adversary := by
      rw [lintegral_add_left Measurable.of_discrete,
        lintegral_const_mul _ Measurable.of_discrete]
      rfl

/-- The second resource inequality: stopping queries no more than one challenge per round,
so expected executed-round cost is at most the total local-error sum. -/
theorem expectedStoppedVerifierRoundCost_le_sum
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedStoppedVerifierRoundCost rounds guards errors adversary ≤
      ∑ j, errors j := by
  let program := randomizedStoppedRestoredExecutionWithAdversaryLog
    rounds guards adversary
  let : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  have hae := evalDist.ae_of_forall_mem_support
    (randomOracleLoggedRun program ∅)
    (fun result => stoppedVerifierRoundCost errors result.1.1.2 result.1.2 ≤
      ∑ j, errors j)
    MeasurableSet.of_discrete
    (fun result hresult => randomOracle_stopped_verifierCost_le_sum
      rounds guards errors adversary result hresult)
  change (∫⁻ result, stoppedVerifierRoundCost errors result.1.1.2 result.1.2
    ∂𝒟[randomOracleLoggedRun program ∅]) ≤ _
  calc
    _ ≤ ∫⁻ _, (∑ j, errors j)
          ∂𝒟[randomOracleLoggedRun program ∅] := lintegral_mono_ae hae
    _ = ∑ j, errors j := by
      rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- The actual stopped distinct-query budget, with both the refined verifier term and the
coarser full-schedule consequence. The adversary count belongs to this same joint run. -/
theorem expectedStoppedFreshCharge_le_actualAdversary_and_sum
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedFreshQueryCharge
        (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
        (keyError errors) ≤
      Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards adversary +
      expectedStoppedVerifierRoundCost rounds guards errors adversary ∧
    Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards adversary +
      expectedStoppedVerifierRoundCost rounds guards errors adversary ≤
      Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards adversary +
      ∑ j, errors j := by
  exact ⟨expectedStoppedFreshCharge_le_actualRounds rounds guards errors adversary,
    add_le_add_right
      (expectedStoppedVerifierRoundCost_le_sum rounds guards errors adversary) _⟩

/-- The generic stopped-restoration knowledge theorem. Acceptance validates the explicit
terminal seed through `outputLaw`; the named backward extractor then produces the input witness.
The first bound uses the actual stopped verifier's executed rounds, and the second bounds those
rounds by the full finite schedule. No finite input or salt domain is required. -/
theorem randomizedStopped_knowledge_soundness_actualRounds
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path witness) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
      Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards adversary +
      expectedStoppedVerifierRoundCost rounds guards errors adversary ∧
    Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards adversary +
      expectedStoppedVerifierRoundCost rounds guards errors adversary ≤
      Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards adversary +
      ∑ j, errors j := by
  have hsecurity := randomizedStopped_badRelation_le_expectedFreshCharge
    rounds guards errors adversary state extractor Z preserving bounded
    Rin Rout terminalWitness inputLaw outputLaw
  have hbudget := expectedStoppedFreshCharge_le_actualAdversary_and_sum
    rounds guards errors adversary
  exact ⟨hsecurity.trans hbudget.1, hbudget.2⟩

/-- Stopped completion preserves the adversary's returned source log, including on failure
and rejection. This identifies the joint count with the actual cached source phase. -/
theorem randomOracle_stoppedCompletion_sourceLog
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (selectedAndLog : Option (Input × Messages Salt rounds × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (result : StoppedJointResult Input Salt W rounds)
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedStoppedCompletionAfterAdversaryLog rounds guards selectedAndLog)
      cache)) :
    result.1.1.2 = selectedAndLog.2 := by
  rcases selectedAndLog with ⟨selected, adversaryLog⟩
  cases selected with
  | none =>
      simp [randomizedStoppedCompletionAfterAdversaryLog,
        randomOracleLoggedRun] at supported
      subst result
      rfl
  | some data =>
      rcases data with ⟨z, messages, witness⟩
      have hprogram : randomizedStoppedCompletionAfterAdversaryLog rounds guards
          (some (z, messages, witness), adversaryLog) =
          (fun path => (path.map (fun p => (z, p, witness)), adversaryLog)) <$>
            simulateQ (restorationQueries Input Salt rounds)
              (stoppedComplete rounds guards z messages) := by
        simp only [randomizedStoppedCompletionAfterAdversaryLog, map_eq_pure_bind]
      rw [hprogram, randomOracleLoggedRun_map, support_map] at supported
      obtain ⟨completion, _, rfl⟩ := supported
      rfl

private theorem stoppedCompletion_expected_adversaryKeys
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (selectedAndLog : Option (Input × Messages Salt rounds × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    letI : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
    (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
      ∂𝒟[randomOracleLoggedRun
        (randomizedStoppedCompletionAfterAdversaryLog rounds guards selectedAndLog)
        cache]) =
      (adversaryHashKeys selectedAndLog.2).card := by
  let : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  have hae := evalDist.ae_of_forall_mem_support
    (randomOracleLoggedRun
      (randomizedStoppedCompletionAfterAdversaryLog rounds guards selectedAndLog)
      cache)
    (fun result => ((adversaryHashKeys result.1.1.2).card : ENNReal) =
      (adversaryHashKeys selectedAndLog.2).card)
    MeasurableSet.of_discrete
    (fun result hresult => by
      rw [randomOracle_stoppedCompletion_sourceLog rounds guards
        selectedAndLog cache result hresult])
  calc
    (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
      ∂𝒟[randomOracleLoggedRun
        (randomizedStoppedCompletionAfterAdversaryLog rounds guards selectedAndLog)
        cache]) =
        ∫⁻ _, ((adversaryHashKeys selectedAndLog.2).card : ENNReal)
          ∂𝒟[randomOracleLoggedRun
            (randomizedStoppedCompletionAfterAdversaryLog rounds guards selectedAndLog)
            cache] := lintegral_congr_ae hae
    _ = (adversaryHashKeys selectedAndLog.2).card := by
      rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- The adversary count carried by the stopped joint run equals the count measured at the
actual cached adversary phase. The stopping decision cannot change its earlier key set. -/
theorem expectedStoppedJointAdversaryKeys_eq_expectedAdversaryFreshKeys
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedStoppedJointAdversaryKeys rounds guards adversary =
      expectedAdversaryFreshKeys rounds adversary := by
  let Phase :=
    (((Option (Input × Messages Salt rounds × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache)
  let : MeasurableSpace Phase := ⊤
  let : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  let phaseRun := randomOracleLoggedRun adversary.withQueryLog ∅
  let jointRun := randomOracleLoggedRun
    (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅
  change (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
    ∂𝒟[jointRun]) =
    ∫⁻ phase, ((freshKeysOfLog phase.1.2).card : ENNReal) ∂𝒟[phaseRun]
  have hbind : jointRun = phaseRun >>= fun phase =>
      (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
        randomOracleLoggedRun
          (randomizedStoppedCompletionAfterAdversaryLog rounds guards phase.1.1)
          phase.2 := by
    simpa only [jointRun, phaseRun] using
      randomizedStoppedRestoredExecutionWithAdversaryLog_handoff
        rounds guards adversary ∅
  rw [hbind, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
  have hinner (phase : Phase) :
      (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
        ∂𝒟[(fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          randomOracleLoggedRun
            (randomizedStoppedCompletionAfterAdversaryLog rounds guards phase.1.1)
            phase.2]) =
      (adversaryHashKeys phase.1.1.2).card := by
    rw [lintegral_evalDist_map_of_discrete]
    exact stoppedCompletion_expected_adversaryKeys rounds guards phase.1.1 phase.2
  simp_rw [hinner]
  apply lintegral_congr_ae
  have hae := evalDist.ae_of_forall_mem_support phaseRun
    (fun phase => phase.1.1.2.snd = phase.1.2)
    MeasurableSet.of_discrete
    (fun phase hphase => randomOracle_withQueryLog_hashLog_eq adversary ∅ phase hphase)
  filter_upwards [hae] with phase hphase
  simp only [adversaryHashKeys, freshKeysOfLog, hphase]

/-- The stopped theorem in the standard adversary-phase budget form. The first inequality
retains the expected cost of rounds actually queried, and the second replaces it by the full
schedule sum. -/
theorem randomizedStopped_knowledge_soundness_actualAdversary
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path witness) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
      Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
        expectedStoppedVerifierRoundCost rounds guards errors adversary ∧
    Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
        expectedStoppedVerifierRoundCost rounds guards errors adversary ≤
      Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
        ∑ j, errors j := by
  simpa only [expectedStoppedJointAdversaryKeys_eq_expectedAdversaryFreshKeys]
    using randomizedStopped_knowledge_soundness_actualRounds rounds guards errors
      adversary state extractor Z preserving bounded Rin Rout terminalWitness
      inputLaw outputLaw

end Interaction.Oracle.Security.StateRestoration
