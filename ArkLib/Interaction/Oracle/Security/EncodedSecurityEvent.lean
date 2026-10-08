/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedSecurity
public import ArkLib.Interaction.Oracle.Security.EncodedChallengeCoupling
public import ArkLib.Data.OracleComp.RandomOracleCost
public import ArkLib.Interaction.Oracle.Security.EncodedCharge

/-!
# Actual encoded-domain stopped event

The external adversary and encoded stopped verifier share one lazy random oracle. Their
selected-result distribution agrees with the native stopped experiment through the strict
codec and the uniform common challenge representations.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

variable {Input Salt C D W : Type}

/-- The actual external stopped game and the native stopped joint game have the same selected
result distribution, including failure and guard rejection. -/
theorem encodedExternalStopped_evalDist_result_eq_native
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (guards : GuardSchedule Input Salt rounds)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W))) :
    letI : MeasurableSpace
      (Option (Input × (protocol rounds).tree.ExecutionPath × W)) := ⊤
    𝒟[(fun joint => joint.1.1) <$> randomOracleLoggedRun
      (encodedExternalStoppedExecution rounds common codec guards external) ∅] =
    𝒟[(fun joint => joint.1.1.1) <$> randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards
        (encodedNativeAdversary common codec external)) ∅] := by
  let : MeasurableSpace
      (Option (Input × (protocol rounds).tree.ExecutionPath × W)) := ⊤
  let Result := Option (Input × (protocol rounds).tree.ExecutionPath × W)
  let Routed := ((Result × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache)
  let : MeasurableSpace
      ((Routed × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  let : MeasurableSpace
      ((Routed × QueryLog (oracleSpec Input Salt rounds)) ×
        (oracleSpec Input Salt rounds).QueryCache) := ⊤
  let externalProgram :=
    encodedExternalStoppedExecution rounds common codec guards external
  let routedProgram := codec.routeProgram externalProgram ∅
  let nativeProgram := common.simulateNative routedProgram
  let nativeStopped := nativeStoppedExecution rounds guards
    (encodedNativeAdversary common codec external)
  have hroute := codec.routeProgram_externalProjection externalProgram
    (∅ : (Key Input Salt rounds →ₒ C).QueryCache)
    (∅ : (D →ₒ C).QueryCache)
  rw [codec.mergeCache_empty] at hroute
  have hchallenge := common.evalDist_randomOracleLoggedRun_simulateNative
    routedProgram (∅ : (oracleSpec Input Salt rounds).QueryCache)
  have hcache : common.toCommonCache
      (∅ : (oracleSpec Input Salt rounds).QueryCache) = ∅ := by
    apply QueryCache.ext
    intro key
    simp [CommonChallenge.toCommonCache]
  have hsource := encodedExternalStopped_route_nativeValue rounds common codec
    guards external
  have herase := randomizedStoppedExecution_eraseSourceLog rounds guards
    (encodedNativeAdversary common codec external)
  calc
    _ = 𝒟[(fun joint => joint.1.1.1.1) <$>
        randomOracleLoggedRun routedProgram ∅] := by
          rw [← hroute]
          simp only [Functor.map_map]
          rfl
    _ = 𝒟[(fun joint => joint.1.1.1.1) <$>
        randomOracleLoggedRun nativeProgram ∅] := by
          have hchallenge' := congrArg
            (fun measure => Measure.map (fun joint => joint.1.1.1.1) measure)
            hchallenge.symm
          rw [evalDist_map_of_discrete, evalDist_map_of_discrete]
          rw [evalDist_map_of_discrete,
            Measure.map_map Measurable.of_discrete Measurable.of_discrete] at hchallenge'
          rw [hcache] at hchallenge'
          simpa only [CommonChallenge.encodeJoint, Function.comp_def] using hchallenge'
    _ = 𝒟[(fun joint => joint.1.1) <$>
        randomOracleLoggedRun nativeStopped ∅] := by
          dsimp only [nativeStopped, nativeProgram, routedProgram]
          rw [← hsource]
          simp only [randomOracleLoggedRun_map, Functor.map_map]
          rfl
    _ = _ := by
          dsimp only [nativeStopped]
          rw [← herase]
          simp only [randomOracleLoggedRun_map, Functor.map_map]

/-- Every event on the selected stopped result has the same probability in the actual
external encoded oracle experiment and the native certificate experiment. -/
theorem encodedExternalStopped_prEvent_eq_native
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (guards : GuardSchedule Input Salt rounds)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W)))
    (event : Option (Input × (protocol rounds).tree.ExecutionPath × W) → Prop) :
    Pr{let joint ← (randomOracleLoggedRun
      (encodedExternalStoppedExecution rounds common codec guards external) ∅)}[
        event joint.1.1] =
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards
        (encodedNativeAdversary common codec external)) ∅)}[
        event joint.1.1.1] := by
  let : MeasurableSpace
      (Option (Input × (protocol rounds).tree.ExecutionPath × W)) := ⊤
  have hresult := encodedExternalStopped_evalDist_result_eq_native
    rounds common codec guards external
  have hevent := prEvent_congr_of_evalDist_eq _ _ hresult event
  simpa only [prEvent_map] using hevent

/-- The actual external image-weighted query charge equals the native certificate experiment's
charge. The equality includes adversary failure, early rejection, and repeated cache hits. -/
theorem encodedExternalStopped_expectedCharge_eq_native
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (guards : GuardSchedule Input Salt rounds)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W)))
    (weight : Key Input Salt rounds → ENNReal) :
    expectedFreshQueryCharge
      (encodedExternalStoppedExecution rounds common codec guards external)
      (codec.encodedWeight weight) =
    expectedFreshQueryCharge
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards
        (encodedNativeAdversary common codec external)) weight := by
  let externalProgram :=
    encodedExternalStoppedExecution rounds common codec guards external
  let routedProgram := codec.routeProgram externalProgram ∅
  let nativeProgram := common.simulateNative routedProgram
  let nativeAdversary := encodedNativeAdversary common codec external
  let nativeJoint := randomizedStoppedRestoredExecutionWithAdversaryLog
    rounds guards nativeAdversary
  have hsource := encodedExternalStopped_route_nativeValue rounds common codec
    guards external
  have herase := randomizedStoppedExecution_eraseSourceLog rounds guards nativeAdversary
  symm
  calc
    _ = expectedFreshQueryCharge
        (nativeStoppedExecution rounds guards nativeAdversary) weight := by
          rw [← herase]
          exact (OracleComp.expectedFreshQueryCharge_map nativeJoint Prod.fst weight).symm
    _ = expectedFreshQueryCharge nativeProgram weight := by
          rw [← hsource]
          exact OracleComp.expectedFreshQueryCharge_map nativeProgram
            (fun result => result.1.1) weight
    _ = expectedFreshQueryCharge routedProgram weight :=
          common.expectedFreshQueryCharge_simulateNative routedProgram weight
    _ = expectedFreshQueryCharge externalProgram (codec.encodedWeight weight) :=
          codec.expectedNativeCharge_eq_external externalProgram weight

/-- The external stopped run's own weighted cost is bounded by its original adversary's
expected distinct queries and the round-error sum. This resource bound needs no security
certificate or acceptance hypothesis. -/
theorem encodedExternalStopped_expectedCharge_le_adversaryCount
    [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W))) :
    expectedFreshQueryCharge
      (encodedExternalStoppedExecution rounds common codec guards external)
      (codec.encodedWeight (keyError errors)) ≤
    Finset.univ.sup errors * expectedFreshQueryCharge external (fun _ => 1) +
      ∑ j, errors j := by
  classical
  rw [encodedExternalStopped_expectedCharge_eq_native]
  let nativeAdversary := encodedNativeAdversary common codec external
  have hcost := expectedStoppedFreshCharge_le_actualAdversary_and_sum
    rounds guards errors nativeAdversary
  have hcount : expectedAdversaryFreshKeys rounds nativeAdversary ≤
      expectedFreshQueryCharge external (fun _ => 1) := by
    rw [encodedNativeAdversary_expectedKeys_eq_route]
    rw [common.expectedFreshQueryCharge_simulateNative]
    exact codec.expectedNativeFreshKeys_le_external external
  calc
    _ ≤ Finset.univ.sup errors *
        expectedStoppedJointAdversaryKeys rounds guards nativeAdversary +
          ∑ j, errors j := hcost.1.trans hcost.2
    _ = Finset.univ.sup errors * expectedAdversaryFreshKeys rounds nativeAdversary +
          ∑ j, errors j := by
            rw [expectedStoppedJointAdversaryKeys_eq_expectedAdversaryFreshKeys]
    _ ≤ _ := by
      gcongr

/-- The actual external stopped verifier's bad accepted event is bounded by the image-weighted
distinct-key charge of its own complete, cached encoded-domain run. Off-image keys have weight
zero, and every executed verifier or adversary query remains in the observed log. -/
theorem encodedExternalStopped_knowledge_soundness_sharp
    [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W)))
    (state : Input → KnowledgeState)
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
      (encodedExternalStoppedExecution rounds common codec guards external) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1] ≤
    expectedFreshQueryCharge
      (encodedExternalStoppedExecution rounds common codec guards external)
      (codec.encodedWeight (keyError errors)) := by
  classical
  rw [encodedExternalStopped_expectedCharge_eq_native]
  rw [encodedExternalStopped_prEvent_eq_native rounds common codec guards
    external (badStoppedRelation state extractor Rin Rout terminalWitness Z)]
  exact randomizedStopped_badRelation_le_expectedFreshCharge
    rounds guards errors (encodedNativeAdversary common codec external)
    state extractor Z preserving bounded Rin Rout terminalWitness inputLaw outputLaw

/-- The external bad accepted event also obeys the familiar query budget form. The budget is
the expected number of distinct keys queried by the original external adversary, including
off-image keys and failed selections; stopped verifier rounds cost at most the error sum. -/
theorem encodedExternalStopped_knowledge_soundness_adversaryCount
    [DecidableEq D] [SampleableType C]
    (rounds : List Round)
    (common : CommonChallenge Input Salt C rounds)
    (codec : StrictCodec (Key Input Salt rounds) D)
    (guards : GuardSchedule Input Salt rounds)
    (errors : RoundErrors rounds)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Input × Messages Salt rounds × W)))
    (state : Input → KnowledgeState)
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
      (encodedExternalStoppedExecution rounds common codec guards external) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1] ≤
    Finset.univ.sup errors * expectedFreshQueryCharge external (fun _ => 1) +
      ∑ j, errors j := by
  exact (encodedExternalStopped_knowledge_soundness_sharp rounds common codec guards
    errors external state extractor Z preserving bounded Rin Rout terminalWitness
    inputLaw outputLaw).trans
      (encodedExternalStopped_expectedCharge_le_adversaryCount
        rounds common codec guards errors external)

end Interaction.Oracle.Security.StateRestoration
