/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedCompletion
public import ArkLib.Interaction.Oracle.Security.EncodedChallengeCost

/-!
# Encoded-domain adversaries in native restoration security

An arbitrary encoded-domain oracle adversary is routed through the strict codec with a private
memoized off-image cache, then through the common-challenge interpreter into the actual native
restoration oracle. The returned selection is unchanged and the final native oracle cache is
carried into stopped completion.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt C D W : Type} {rounds : List Round}

/-- The adversary-phase budget is exactly the expected distinct native hash-log count of the
adversary program itself. Surface query logging does not add hash queries. -/
theorem expectedAdversaryFreshKeys_eq_expectedFreshQueryCharge
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedAdversaryFreshKeys rounds adversary =
      expectedFreshQueryCharge adversary (fun _ => 1) := by
  let : MeasurableSpace
      (((Option (Input × Messages Salt rounds × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  let : MeasurableSpace
      ((Option (Input × Messages Salt rounds × W) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache) := ⊤
  simp only [expectedAdversaryFreshKeys, expectedFreshQueryCharge,
    freshQueryCharge, Finset.sum_const, nsmul_eq_mul, mul_one]
  have herase : (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
      randomOracleLoggedRun adversary.withQueryLog ∅ =
      randomOracleLoggedRun adversary ∅ := by
    rw [← randomOracleLoggedRun_map (fun pair => pair.1) adversary.withQueryLog ∅]
    congr 1
    exact loggingOracle.fst_map_run_simulateQ adversary
  rw [← herase, lintegral_evalDist_map_of_discrete]

/-- Roundwise challenge equivalences give the common-carrier data for every native key.
This is a structural restriction on the schedule, with no game-equality premise. -/
def CommonChallenge.ofRoundEquivs
    (rounds : List Round)
    (equivs : ∀ round, round ∈ rounds → round.Challenge ≃ C) :
    CommonChallenge Input Salt C rounds := by
  let rec build : (rs : List Round) →
      (∀ round, round ∈ rs → round.Challenge ≃ C) →
      (key : Key Input Salt rs) → key.Challenge ≃ C
    | [], _, key => nomatch key
    | round :: rest, es, .inl _ => es round (by simp)
    | round :: rest, es, .inr data =>
        build rest (fun r hr => es r (by simp [hr])) data.2.2
  exact ⟨build rounds equivs⟩

/-- Forgetting the external writer/off-image cache from the selected value does not erase any
actual native hash query or alter its distinct-key expectation. -/
theorem encodedNativeAdversary_expectedKeys_eq_route
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W))) :
    expectedAdversaryFreshKeys rounds
      (encodedNativeAdversary common codec external) =
    expectedFreshQueryCharge
      (common.simulateNative (codec.routeProgram external ∅)) (fun _ => 1) := by
  rw [expectedAdversaryFreshKeys_eq_expectedFreshQueryCharge]
  let : MeasurableSpace
      ((Option (Input × Messages Salt rounds × W) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache) := ⊤
  let : MeasurableSpace
      ((((Option (Input × Messages Salt rounds × W) × QueryLog (D →ₒ C)) ×
        (D →ₒ C).QueryCache) × QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache) := ⊤
  simp only [expectedFreshQueryCharge, freshQueryCharge, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  unfold encodedNativeAdversary
  rw [randomOracleLoggedRun_map, lintegral_evalDist_map_of_discrete]

/-- The native certificate applies to the actual stopped joint run of the encoded adversary.
The resource term is the native image-query count. Its external transport is separate. -/
theorem encodedNativeReduction_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W)))
    (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      Rout z path witness →
        ((extractor z).terminalState path).holds (terminalWitness z path witness)) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards
        (encodedNativeAdversary common codec external)) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
      Finset.univ.sup errors *
        expectedAdversaryFreshKeys rounds (encodedNativeAdversary common codec external) +
      ∑ j, errors j := by
  have h := randomizedStopped_knowledge_soundness_actualAdversary rounds guards errors
    (encodedNativeAdversary common codec external) state extractor Z preserving bounded
    Rin Rout terminalWitness inputLaw outputLaw
  exact h.1.trans h.2

end Interaction.Oracle.Security.StateRestoration
