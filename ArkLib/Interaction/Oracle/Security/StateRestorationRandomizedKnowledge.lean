/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomized

/-!
# Expected knowledge security for randomized native state restoration

The scalar and closed-output native games observe the same completed challenge path. Their
relation-level extraction events inherit one joint expected distinct-query bound, with a
worst-case corollary from the actual cached adversary-phase query count.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : List Round}

/-- Observe the selected native path while retaining the adversary's exact source query log.
Both scalar observations and closed oracle outputs use this one owner-level wrapper. -/
def randomizedObservedGameWithAdversaryLog
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
        Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) :=
  (fun result =>
    (result.1.map fun outcome =>
      (⟨outcome.1, outcome.2.1, observe outcome.1 outcome.2.1, outcome.2.2⟩ :
        (z : Input) × (path : (protocol rounds).tree.ExecutionPath) × Out z path × W),
      result.2)) <$> randomizedRestoredExecutionWithAdversaryLog rounds adversary

/-- The extraction event viewed through any native observation. The observed output stays in
the result type, so scalar and closed claims retain their actual same-path behavior. -/
def badExtractObserved
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (result : Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W)) : Prop :=
  match result with
  | none => False
  | some ⟨z, path, _, witness⟩ =>
      badExtractOnPath state extractor Z terminalWitness (some (z, path, witness))

/-- Any observed scalar or closed bad extraction is witnessed by a bad key in the very same
fixed-table joint run; observation does not introduce or erase hash queries. -/
theorem fixedTable_observed_badExtract_has_bad_query [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (table : Table Input Salt rounds)
    (result : (((Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) table ∅))
    (bad : badExtractObserved Out state extractor Z terminalWitness result.1.1.1) :
    ∃ query ∈ result.1.2, badKey state extractor Z query.1 table := by
  rw [randomizedObservedGameWithAdversaryLog, fixedTableLoggedRun_map, support_map]
    at supported
  obtain ⟨base, hbase, rfl⟩ := supported
  apply fixedTable_badExtract_has_bad_query rounds adversary state extractor Z preserving
    terminalWitness table base hbase
  cases hselected : base.1.1.1 with
  | none => simp [badExtractObserved, hselected] at bad
  | some selected =>
      rcases selected with ⟨z, path, witness⟩
      simpa [badExtractObserved, hselected] using bad

/-- The pointwise charge bound is unchanged by the actual scalar or closed native observation. -/
theorem fixedTable_observed_freshCharge_le [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (table : Table Input Salt rounds)
    (result : (((Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) table ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      (adversaryHashKeys result.1.1.2).card * Finset.univ.sup errors +
        ∑ j, errors j := by
  rw [randomizedObservedGameWithAdversaryLog, fixedTableLoggedRun_map, support_map]
    at supported
  obtain ⟨base, hbase, rfl⟩ := supported
  exact fixedTable_joint_freshCharge_le rounds errors adversary table base hbase

/-- The scalar and closed observed games inherit the same pointwise bound on the actual cached
run. Optional failure remains in the returned value and its preceding queries stay charged. -/
theorem randomOracle_observed_freshCharge_le [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (result : (((Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      (adversaryHashKeys result.1.1.2).card * Finset.univ.sup errors +
        ∑ j, errors j := by
  obtain ⟨table, htable⟩ := mem_support_fixedTableLoggedRun_of_randomOracle
    (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅ result supported
  exact fixedTable_observed_freshCharge_le rounds errors adversary Out observe table result htable

/-- The actual adversary-phase support cap also bounds the adversary count carried by every
scalar or closed observed execution. -/
theorem randomOracle_observed_adversaryKeys_le [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (result : (((Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅)) :
    (adversaryHashKeys result.1.1.2).card ≤ Q := by
  rw [randomizedObservedGameWithAdversaryLog, randomOracleLoggedRun_map, support_map]
    at supported
  obtain ⟨base, hbase, rfl⟩ := supported
  exact randomOracle_joint_adversaryKeys_le rounds adversary Q actualQueryBound base hbase

/-- Native observation changes only the returned value. Its expected distinct hash-key charge
is exactly that of the underlying joint restoration run. -/
theorem expectedObservedFreshQueryCharge_eq [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (error : Key Input Salt rounds → ENNReal) :
    expectedFreshQueryCharge
      (randomizedObservedGameWithAdversaryLog Out observe adversary) error =
      expectedFreshQueryCharge
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary) error := by
  let : MeasurableSpace
      (((Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
        Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  let : MeasurableSpace
      (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  unfold expectedFreshQueryCharge
  rw [randomizedObservedGameWithAdversaryLog, randomOracleLoggedRun_map,
    lintegral_evalDist_map_of_discrete]

/-- Shared second inequality for both scalar and closed native observations. -/
theorem expectedObservedFreshCharge_le_actualAdversary
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path) :
    expectedFreshQueryCharge
      (randomizedObservedGameWithAdversaryLog Out observe adversary) (keyError errors) ≤
      Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
        ∑ j, errors j := by
  rw [expectedObservedFreshQueryCharge_eq rounds adversary Out observe]
  exact expectedJointFreshCharge_le_actualAdversary rounds errors adversary

/-- A cap on the *actual* distinct adversary queries recovers the familiar worst-case bound
for either native observation, with repetitions and failed branches counted correctly. -/
theorem expectedObservedFreshCharge_le_queryBound
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    expectedFreshQueryCharge
      (randomizedObservedGameWithAdversaryLog Out observe adversary) (keyError errors) ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  calc
    _ ≤ Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
          ∑ j, errors j :=
      expectedObservedFreshCharge_le_actualAdversary rounds errors adversary Out observe
    _ ≤ Q * Finset.univ.sup errors + ∑ j, errors j := by
      calc
        Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
            ∑ j, errors j ≤
          Finset.univ.sup errors * Q + ∑ j, errors j := by
            gcongr
            exact expectedAdversaryFreshKeys_le_queryBound rounds adversary Q actualQueryBound
        _ = _ := by rw [mul_comm]

/-- The relation-level event on an actual native observation, including the output carried in
that run. For a closed oracle output, `Rout` requires an accepted closed claim. -/
def badObservedRelation
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      Out z path → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (Z : Set Input)
    (result : Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W)) : Prop :=
  match result with
  | none => False
  | some ⟨z, path, output, witness⟩ =>
      z ∈ Z ∧ Rout z path output witness ∧
        ¬ Rin z (extractInputWitness state extractor terminalWitness z path witness)

/-- Relation laws identify the actual observed failure with the named extractor failure on
every fixed-table supported execution; no independent output reconstruction is used. -/
theorem fixedTable_observed_badRelation_has_bad_query [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      Out z path → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path (observe z path) witness)
    (table : Table Input Salt rounds)
    (result : (((Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) table ∅))
    (bad : badObservedRelation Out state extractor Rin Rout terminalWitness Z result.1.1.1) :
    ∃ query ∈ result.1.2, badKey state extractor Z query.1 table := by
  apply fixedTable_observed_badExtract_has_bad_query rounds adversary Out observe state
    extractor Z preserving (fun z path => terminalWitness z path) table result supported
  rw [randomizedObservedGameWithAdversaryLog, fixedTableLoggedRun_map, support_map]
    at supported
  obtain ⟨base, _, hresult⟩ := supported
  rw [← hresult] at bad ⊢
  cases hselected : base.1.1.1 with
  | none => simp [badObservedRelation, hselected] at bad
  | some selected =>
      rcases selected with ⟨z, path, witness⟩
      simp only [badObservedRelation, hselected, Option.map_some] at bad
      simp only [badExtractObserved, badExtractOnPath, hselected, Option.map_some]
      exact ⟨bad.1, (outputLaw z path witness).mpr bad.2.1,
        fun h => bad.2.2 ((inputLaw z _).mp h)⟩

/-- The owner-level trace implication in the exact shape required by the expected fresh-query
theorem: the failure event on the returned value yields a bad distinct key in the joint log. -/
theorem fixedTable_observed_badRelation_fresh_htrace
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      Out z path → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path (observe z path) witness)
    (table : Table Input Salt rounds)
    (result : (((Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) table ∅))
    (bad : badObservedRelation Out state extractor Rin Rout terminalWitness Z
      result.1.1.1) :
    ∃ key ∈ freshKeysOfLog result.1.2,
      badKey state extractor Z key table := by
  obtain ⟨query, hquery, hbad⟩ := fixedTable_observed_badRelation_has_bad_query
    rounds adversary Out observe state extractor Z preserving Rin Rout terminalWitness
    inputLaw outputLaw table result supported bad
  exact ⟨query.1, (mem_freshKeysOfLog _ _).mpr ⟨query, hquery, rfl⟩, hbad⟩

/-- Shared first inequality: an invalid named extraction from an actual scalar or closed
native observation is charged by the expected distinct keys of that same cached joint run. -/
theorem randomizedObserved_badRelation_le_expectedFreshCharge
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      Out z path → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path (observe z path) witness) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅)}[
        badObservedRelation Out state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
      expectedFreshQueryCharge
        (randomizedObservedGameWithAdversaryLog Out observe adversary)
        (keyError errors) := by
  apply prEvent_randomOracle_le_expectedFreshQueryCharge
    (randomizedObservedGameWithAdversaryLog Out observe adversary)
    (fun result => badObservedRelation Out state extractor Rin Rout terminalWitness Z result.1)
    (badKey state extractor Z) (keyError errors)
  · intro table result supported bad
    exact fixedTable_observed_badRelation_fresh_htrace rounds adversary Out observe
      state extractor Z preserving Rin Rout terminalWitness inputLaw outputLaw
      table result supported bad
  · intro key table
    exact badKey_round_resample_bound state extractor Z errors bounded key table

/-- An almost-sure cap on the actual cached adversary's distinct key count yields the
traditional `Q * max + sum` bound for the shared scalar/closed failure event. -/
theorem randomizedObserved_badRelation_le_queryBound
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      Out z path → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path (observe z path) witness)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅)}[
        badObservedRelation Out state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  exact (randomizedObserved_badRelation_le_expectedFreshCharge rounds errors adversary
    Out observe state extractor Z preserving bounded Rin Rout terminalWitness
    inputLaw outputLaw).trans
      (expectedObservedFreshCharge_le_queryBound rounds errors adversary Out observe
        Q actualQueryBound)

/-- Erasing the adversary-phase log gives the ordinary observed joint game as an exact
`OracleComp` equation; every stateful logged interpreter therefore preserves its cache and log. -/
theorem randomizedObservedGameWithAdversaryLog_erase
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Prod.fst <$> randomizedObservedGameWithAdversaryLog Out observe adversary =
      (fun result => result.map fun outcome =>
        (⟨outcome.1, outcome.2.1, observe outcome.1 outcome.2.1, outcome.2.2⟩ :
          (z : Input) × (path : (protocol rounds).tree.ExecutionPath) × Out z path × W)) <$>
        randomizedRestoredExecution rounds adversary := by
  rw [randomizedObservedGameWithAdversaryLog, Functor.map_map]
  conv_rhs => rw [← randomizedRestoredExecutionWithAdversaryLog_erase rounds adversary]
  rw [Functor.map_map]

/-- The scalar observed game erases to the existing native verifier exactly. -/
theorem randomizedObservedGame_scalar_erase (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Prod.fst <$> randomizedObservedGameWithAdversaryLog
      (fun z path => Out z path.toBranchPath)
      (terminalObservation initial impl Out terminal) adversary =
        randomizedVerificationGame initial impl Out terminal adversary := by
  rw [randomizedObservedGameWithAdversaryLog_erase, randomizedVerificationGame_eq]

/-- The closed observed game erases to the existing native verifier and actual closing handler. -/
theorem randomizedObservedGame_closed_erase (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Prod.fst <$> randomizedObservedGameWithAdversaryLog
      (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
        (family z path.toBranchPath)))
      (closedTerminalObservation initial impl Stmt family terminal) adversary =
        randomizedClosedVerificationGame initial impl Stmt family terminal adversary := by
  rw [randomizedObservedGameWithAdversaryLog_erase, randomizedClosedVerificationGame_eq]

/-- Forgetting the observed hash log and cache recovers the ordinary cached random-oracle
execution of an arbitrary randomized restoration program. -/
private theorem randomOracleLoggedRun_output [DecidableEq Input] [DecidableEq Salt]
    {A : Type} (program : OracleComp (unifSpec + oracleSpec Input Salt rounds) A) :
    (fun result => result.1.1) <$> randomOracleLoggedRun program ∅ =
      (simulateQ (oracleSpec Input Salt rounds).romImpl program).run' ∅ := by
  rw [StateT.run'_eq, ← randomOracleLoggedRun_project program ∅]
  simp only [Functor.map_map]

private theorem randomOracleLoggedRun_output_map [DecidableEq Input] [DecidableEq Salt]
    {A B : Type} (f : A → B)
    (program : OracleComp (unifSpec + oracleSpec Input Salt rounds) A) :
    (fun result => f result.1.1) <$> randomOracleLoggedRun program ∅ =
      (simulateQ (oracleSpec Input Salt rounds).romImpl (f <$> program)).run' ∅ := by
  rw [simulateQ_map, StateT.run'_map', ← randomOracleLoggedRun_output program]
  simp only [Functor.map_map]

/-- Erasing only the instrumentation from the joint observed run produces exactly the native
cached output marginal; the first inequality can therefore be stated on the native game. -/
theorem randomizedObservedGame_actual_marginal [DecidableEq Input] [DecidableEq Salt]
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅ =
      (simulateQ (oracleSpec Input Salt rounds).romImpl
        (Prod.fst <$> randomizedObservedGameWithAdversaryLog Out observe adversary)).run' ∅ := by
  exact randomOracleLoggedRun_output_map Prod.fst
    (randomizedObservedGameWithAdversaryLog Out observe adversary)

/-- Every event on the native observed output has the same probability in the instrumented
joint run; the latter additionally retains the ordered hash log and final cache. -/
theorem randomizedObservedGame_actual_event [DecidableEq Input] [DecidableEq Salt]
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (event : Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path × W) → Prop) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt rounds).romImpl
      (Prod.fst <$> randomizedObservedGameWithAdversaryLog Out observe adversary)).run' ∅}[
        event result] =
      Pr{let joint ← (randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅)}[
          event joint.1.1.1] := by
  rw [← randomizedObservedGame_actual_marginal Out observe adversary]
  exact prEvent_map _ _ _

/-- The scalar native verifier is the exact output marginal of the instrumented joint run. -/
theorem randomizedVerificationGame_actual_marginal [DecidableEq Input] [DecidableEq Salt]
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Out z path.toBranchPath)
          (terminalObservation initial impl Out terminal) adversary) ∅ =
      (simulateQ (oracleSpec Input Salt rounds).romImpl
        (randomizedVerificationGame initial impl Out terminal adversary)).run' ∅ := by
  rw [← randomizedObservedGame_scalar_erase initial impl Out terminal adversary]
  exact randomizedObservedGame_actual_marginal
    (fun z path => Out z path.toBranchPath)
    (terminalObservation initial impl Out terminal) adversary

/-- The closed native verifier is the exact output marginal of the same instrumented run. -/
theorem randomizedClosedVerificationGame_actual_marginal
    [DecidableEq Input] [DecidableEq Salt]
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
            (family z path.toBranchPath)))
          (closedTerminalObservation initial impl Stmt family terminal) adversary) ∅ =
      (simulateQ (oracleSpec Input Salt rounds).romImpl
        (randomizedClosedVerificationGame initial impl Stmt family terminal adversary)).run' ∅ := by
  rw [← randomizedObservedGame_closed_erase initial impl Stmt family terminal adversary]
  exact randomizedObservedGame_actual_marginal
    (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
      (family z path.toBranchPath)))
    (closedTerminalObservation initial impl Stmt family terminal) adversary

/-- Scalar output events have exactly the same probability in the native verifier and in the
instrumented joint game used for the expected-key analysis. -/
theorem randomizedVerificationGame_actual_event
    [DecidableEq Input] [DecidableEq Salt]
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (event : Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Out z path.toBranchPath × W) → Prop) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt rounds).romImpl
      (randomizedVerificationGame initial impl Out terminal adversary)).run' ∅}[
        event result] =
      Pr{let joint ← (randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Out z path.toBranchPath)
          (terminalObservation initial impl Out terminal) adversary) ∅)}[
          event joint.1.1.1] := by
  rw [← randomizedObservedGame_scalar_erase initial impl Out terminal adversary]
  exact randomizedObservedGame_actual_event _ _ adversary event

/-- Closed output events likewise refer to the native verifier's actual closed claim on the
completed path, while retaining the joint hash log for the bound. -/
theorem randomizedClosedVerificationGame_actual_event
    [DecidableEq Input] [DecidableEq Salt]
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (event : Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
      Option (ClosedClaim (Stmt z path.toBranchPath)
        (family z path.toBranchPath)) × W) → Prop) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt rounds).romImpl
      (randomizedClosedVerificationGame initial impl Stmt family terminal adversary)).run' ∅}[
        event result] =
      Pr{let joint ← (randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
            (family z path.toBranchPath)))
          (closedTerminalObservation initial impl Stmt family terminal) adversary) ∅)}[
          event joint.1.1.1] := by
  rw [← randomizedObservedGame_closed_erase initial impl Stmt family terminal adversary]
  exact randomizedObservedGame_actual_event _ _ adversary event

/-- The native scalar verifier's relation failure has the actual expected fresh-query bound.
The second inequality uses the adversary's actual cached phase, including failed selections. -/
theorem randomizedVerificationGame_expected_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      Out z p → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path.toBranchPath (terminalObservation initial impl Out terminal z path) witness)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt rounds).romImpl
      (randomizedVerificationGame initial impl Out terminal adversary)).run' ∅}[
        badObservedRelation (fun z path => Out z path.toBranchPath)
          state extractor Rin (fun z path out witness => Rout z path.toBranchPath out witness)
          terminalWitness Z result] ≤
      expectedFreshQueryCharge
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Out z path.toBranchPath)
          (terminalObservation initial impl Out terminal) adversary) (keyError errors) ∧
    expectedFreshQueryCharge
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Out z path.toBranchPath)
          (terminalObservation initial impl Out terminal) adversary) (keyError errors) ≤
      Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
        ∑ j, errors j := by
  constructor
  · rw [randomizedVerificationGame_actual_event initial impl Out terminal adversary]
    exact randomizedObserved_badRelation_le_expectedFreshCharge rounds errors adversary
      (fun z path => Out z path.toBranchPath)
      (terminalObservation initial impl Out terminal) state extractor Z preserving bounded
      Rin (fun z path out witness => Rout z path.toBranchPath out witness)
      terminalWitness inputLaw outputLaw
  · exact expectedObservedFreshCharge_le_actualAdversary rounds errors adversary
      (fun z path => Out z path.toBranchPath)
      (terminalObservation initial impl Out terminal)

/-- The scalar native verifier recovers the `Q * max + sum` bound from a cap on the actual
cached adversary phase's distinct restoration keys. -/
theorem randomizedVerificationGame_queryBound_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      Out z p → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path.toBranchPath (terminalObservation initial impl Out terminal z path) witness)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt rounds).romImpl
      (randomizedVerificationGame initial impl Out terminal adversary)).run' ∅}[
        badObservedRelation (fun z path => Out z path.toBranchPath)
          state extractor Rin (fun z path out witness => Rout z path.toBranchPath out witness)
          terminalWitness Z result] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  have h := randomizedVerificationGame_expected_knowledge_soundness
    rounds errors state extractor Z preserving bounded initial impl Out terminal
    Rin Rout terminalWitness inputLaw outputLaw adversary
  exact h.1.trans (expectedObservedFreshCharge_le_queryBound rounds errors adversary
    (fun z path => Out z path.toBranchPath)
    (terminalObservation initial impl Out terminal)
    Q actualQueryBound)

/-- The closed oracle-output verifier uses its actual same-path closing handler. A rejected or
failed output is unsuccessful, and a valid closed claim with invalid named extraction is charged
by the actual expected distinct hash queries. -/
theorem randomizedClosedVerificationGame_expected_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
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
        ∃ claim,
          closedTerminalObservation initial impl Stmt family terminal z path = some claim ∧
          Rout z path.toBranchPath claim witness)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt rounds).romImpl
      (randomizedClosedVerificationGame initial impl Stmt family terminal adversary)).run' ∅}[
        badObservedRelation
          (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
            (family z path.toBranchPath)))
          state extractor Rin
          (fun z path output witness =>
            ∃ claim, output = some claim ∧ Rout z path.toBranchPath claim witness)
          terminalWitness Z result] ≤
      expectedFreshQueryCharge
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
            (family z path.toBranchPath)))
          (closedTerminalObservation initial impl Stmt family terminal) adversary)
        (keyError errors) ∧
    expectedFreshQueryCharge
        (randomizedObservedGameWithAdversaryLog
          (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
            (family z path.toBranchPath)))
          (closedTerminalObservation initial impl Stmt family terminal) adversary)
        (keyError errors) ≤
      Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
        ∑ j, errors j := by
  constructor
  · rw [randomizedClosedVerificationGame_actual_event initial impl Stmt family
      terminal adversary]
    exact randomizedObserved_badRelation_le_expectedFreshCharge rounds errors adversary
      (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
        (family z path.toBranchPath)))
      (closedTerminalObservation initial impl Stmt family terminal) state extractor Z
      preserving bounded Rin
      (fun z path output witness =>
        ∃ claim, output = some claim ∧ Rout z path.toBranchPath claim witness)
      terminalWitness inputLaw outputLaw
  · exact expectedObservedFreshCharge_le_actualAdversary rounds errors adversary
      (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
        (family z path.toBranchPath)))
      (closedTerminalObservation initial impl Stmt family terminal)

/-- The closed native verifier's expected bound specializes to `Q * max + sum` when the
actual cached adversary phase makes at most `Q` distinct restoration queries almost surely. -/
theorem randomizedClosedVerificationGame_queryBound_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
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
        ∃ claim,
          closedTerminalObservation initial impl Stmt family terminal z path = some claim ∧
          Rout z path.toBranchPath claim witness)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt rounds).romImpl
      (randomizedClosedVerificationGame initial impl Stmt family terminal adversary)).run' ∅}[
        badObservedRelation
          (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
            (family z path.toBranchPath)))
          state extractor Rin
          (fun z path output witness =>
            ∃ claim, output = some claim ∧ Rout z path.toBranchPath claim witness)
          terminalWitness Z result] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  have h := randomizedClosedVerificationGame_expected_knowledge_soundness
    rounds errors state extractor Z preserving bounded initial impl Stmt family terminal
    Rin Rout terminalWitness inputLaw outputLaw adversary
  exact h.1.trans ((expectedObservedFreshCharge_le_queryBound rounds errors adversary
    (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
      (family z path.toBranchPath)))
    (closedTerminalObservation initial impl Stmt family terminal)
    Q actualQueryBound))

end Interaction.Oracle.Security.StateRestoration
