/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget

/-!
# Finite-table presentation of stopped restoration

On the finite compatible fragment, VCVio's lazy/eager random-oracle equivalence identifies the
entire stopped joint run with an eagerly sampled full answer table. The equality retains the
selected result, ordered challenge log, and final cache, including source failure and guard
rejection. This is the finite semantic bridge needed before comparing native restoration to the
legacy Fiat–Shamir game's table presentation. Infinite input and salt types remain supported by
the owner security theorem, but have no finite full-table sampler.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : List Round}

/-- Canonical uniform full-table sampler on the finite compatible fragment. This is explicit:
the native owner theorems for arbitrary input and salt types do not sample an infinite table. -/
@[reducible] noncomputable def finiteTableSampler (rounds : List Round)
    [Finite Input] [Finite Salt] : SampleableType (Table Input Salt rounds) := by
  classical
  letI : Fintype (Key Input Salt rounds) := Fintype.ofFinite _
  letI : ∀ key : Key Input Salt rounds, Fintype key.Challenge :=
    fun _ => Fintype.ofFinite _
  exact SampleableType.piOfFintype (fun key : Key Input Salt rounds => key.Challenge)

/-- The full lazy stopped run equals an eager full-table experiment on the finite fragment.
Private uniform samples may be interleaved with adaptive hash queries in either execution. -/
theorem evalDist_randomizedStopped_joint_eq_eager
    (rounds : List Round)
    [DecidableEq Input] [DecidableEq Salt] [Finite Input] [Finite Salt]
    [SampleableType (Table Input Salt rounds)]
    (guards : GuardSchedule Input Salt rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    letI : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
    𝒟[randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅] =
    𝒟[($ᵗ (Table Input Salt rounds)) >>= fun table =>
      fixedTableLoggedRun
        (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
        table ∅] := by
  let : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  have h := evalDist_randomOracleLoggedRun_eq_fixedTable_finite
    (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅
  simpa only [completeTable_empty] using h

/-- The complete native restoration program has the same entire joint lazy/eager distribution.
This is the finite-table law needed by the legacy SR experiment, which reconstructs every
challenge before running its verifier and extractor. -/
theorem evalDist_randomizedRestored_joint_eq_eager
    (rounds : List Round)
    [DecidableEq Input] [DecidableEq Salt] [Finite Input] [Finite Salt]
    [SampleableType (Table Input Salt rounds)]
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    letI : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
    𝒟[randomOracleLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅] =
    𝒟[($ᵗ (Table Input Salt rounds)) >>= fun table =>
      fixedTableLoggedRun
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅] := by
  let : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  have h := evalDist_randomOracleLoggedRun_eq_fixedTable_finite
    (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅
  simpa only [completeTable_empty] using h

/-- Native all-prefix knowledge certificates supply the relation-level extraction bound in
the eager full-table experiment. The table is sampled once, private coins remain interleaved,
and the named backward extractor acts on the exact terminal seed supplied by the adversary.
This is the finite native security premise to transport into the legacy SR game. -/
theorem eagerRestored_knowledge_soundness
    (rounds : List Round)
    [DecidableEq Input] [DecidableEq Salt] [Finite Input] [Finite Salt]
    [SampleableType (Table Input Salt rounds)]
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
      W → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      Rout z path witness →
        ((extractor z).terminalState path).holds (terminalWitness z path witness)) :
    Pr{let joint ← (($ᵗ (Table Input Salt rounds)) >>= fun table =>
      fixedTableLoggedRun
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
    Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
      ∑ j, errors j := by
  let : MeasurableSpace (StoppedJointResult Input Salt W rounds) := ⊤
  have hlazy :
      Pr{let joint ← (randomOracleLoggedRun
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅)}[
        badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
      expectedFreshQueryCharge
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary)
        (keyError errors) := by
    apply prEvent_randomOracle_le_expectedFreshQueryCharge
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary)
      (fun result => badStoppedRelation state extractor Rin Rout terminalWitness Z result.1)
      (badKey state extractor Z) (keyError errors)
    · intro table result supported bad
      obtain ⟨query, hquery, hbad⟩ := fixedTable_badExtract_has_bad_query
        rounds adversary state extractor Z preserving
          (fun z path => terminalWitness z path) table result supported
          (badStoppedRelation_implies_badExtractOnPath state extractor Rin Rout
            terminalWitness Z inputLaw outputLaw result.1.1.1 bad)
      exact ⟨query.1, (mem_freshKeysOfLog _ _).mpr ⟨query, hquery, rfl⟩, hbad⟩
    · intro key table
      exact badKey_round_resample_bound state extractor Z errors bounded key table
  have heager :
      Pr{let joint ← (randomOracleLoggedRun
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅)}[
        badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] =
      Pr{let joint ← (($ᵗ (Table Input Salt rounds)) >>= fun table =>
        fixedTableLoggedRun
          (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅)}[
        badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] :=
    prEvent_congr_of_evalDist_eq _ _
      (evalDist_randomizedRestored_joint_eq_eager rounds adversary)
      (fun joint =>
        badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1)
  rw [← heager]
  exact hlazy.trans (expectedJointFreshCharge_le_actualAdversary rounds errors adversary)

end Interaction.Oracle.Security.StateRestoration
