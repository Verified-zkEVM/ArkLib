/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationLegacyGameUnroll
public import ArkLib.Interaction.Oracle.Security.StateRestorationFixedTableProjection

/-!
# Native certificate bound for the canonical legacy knowledge game

The actual coin-bearing legacy prover is translated through the typed query equivalence.
Its canonical transcript is the completed native path at the same uniformly sampled table.
The pure verifier and backward extractor therefore test the native certificate's relation event.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec Interaction.Oracle.TypeTree Interaction.Oracle
open Interaction.TwoParty

namespace Interaction.Oracle.FiatShamir

open Security Security.StateRestoration

universe w

private noncomputable instance nativeTableSampleable {Input : Type}
    [Finite Input] (rounds : List Round) :
    SampleableType (Table Input PUnit rounds) :=
  finiteTableSampler rounds

private theorem nativeLegacyResult_selectedPath
    {Input W WitIn StmtOut : Type} (rounds : List Round)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relIn : Set (Input × WitIn)) (relOut : Set (StmtOut × W))
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) (witness : W) :
    relationKSFailEvent relIn relOut
      (nativeLegacyResult rounds state extractor seed witnessMap observe
        (z, toLegacyTranscript rounds (toPublicPath rounds path), witness)) ↔
    badStoppedRelation state extractor
      (legacyInputRelation state witnessMap relIn)
      (legacyOutputRelation observe relOut) seed Set.univ
      (some (z, path, witness)) := by
  have hpath : legacyToRestorationPath rounds
      (toLegacyTranscript rounds (toPublicPath rounds path)) = path := by
    simp [legacyToRestorationPath, toRestorationPath_toPublicPath]
  dsimp only [nativeLegacyResult]
  rw [hpath]
  exact legacyFailure_eq_badStoppedRelation state extractor seed witnessMap observe
    relIn relOut z path witness

/-- At one fixed full table, the canonical transcript event is the native completed-path
failure event. This is an equality of probabilities for the actual arbitrary coin-bearing prover. -/
theorem legacyFailure_fixedTable_eq_native
    {Input W WitIn StmtOut : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relIn : Set (Input × WitIn)) (relOut : Set (StmtOut × W))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    Pr{let selected ← legacyFixedTableTranscript rounds
        (nativeTableToLegacy rounds table) prover}[
      relationKSFailEvent relIn relOut
        (nativeLegacyResult rounds state extractor seed witnessMap observe selected)] =
    Pr{let selected ← simulateQ (nativeFixedTableCoinImpl rounds table)
        (randomizedRestoredExecution rounds (simulateLegacyProver rounds prover))}[
      badStoppedRelation state extractor
        (legacyInputRelation state witnessMap relIn)
        (legacyOutputRelation observe relOut) seed Set.univ selected] := by
  rw [simulateLegacyProver_complete_at_fixedTable]
  rw [prEvent_map]
  unfold legacyFixedTableTranscript
  simp only [bind_pure_comp, Functor.map_map]
  have hfun :
      (fun result => relationKSFailEvent relIn relOut
        (nativeLegacyResult rounds state extractor seed witnessMap observe
          (result.1,
            evalWithAnswerFn (legacyTableAnswer rounds (nativeTableToLegacy rounds table))
              (result.2.1.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) result.1),
            result.2.2))) =
      (fun result => badStoppedRelation state extractor
        (legacyInputRelation state witnessMap relIn)
        (legacyOutputRelation observe relOut) seed Set.univ
        (legacySelectedNativePath rounds table result)) := by
    funext result
    rcases result with ⟨z, messages, witness⟩
    simp only [legacySelectedNativePath]
    rw [legacyDeriveTranscript_completedPath]
    exact propext (nativeLegacyResult_selectedPath rounds state extractor seed witnessMap
      observe relIn relOut z
        (completedPath rounds z
          (withUnitSalts rounds ((fullLegacyMessagesEquiv rounds).symm messages)) table)
        witness)
  rw [hfun]

/-- Sampling one native table makes the exact canonical transcript failure event equal the
native certificate's eager full-table event. Logs and cache are only projected after the
same fixed-table execution has been run. -/
theorem legacyFailure_eager_eq_native
    {Input W WitIn StmtOut : Type} (rounds : List Round)
    [DecidableEq Input] [SampleableType (Table Input PUnit rounds)]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relIn : Set (Input × WitIn)) (relOut : Set (StmtOut × W))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    Pr{let selected ← (($ᵗ (Table Input PUnit rounds)) >>= fun table =>
        legacyFixedTableTranscript rounds (nativeTableToLegacy rounds table) prover)}[
      relationKSFailEvent relIn relOut
        (nativeLegacyResult rounds state extractor seed witnessMap observe selected)] =
    Pr{let joint ← (($ᵗ (Table Input PUnit rounds)) >>= fun table =>
        fixedTableLoggedRun
          (randomizedRestoredExecutionWithAdversaryLog rounds
            (simulateLegacyProver rounds prover)) table ∅)}[
      badStoppedRelation state extractor
        (legacyInputRelation state witnessMap relIn)
        (legacyOutputRelation observe relOut) seed Set.univ joint.1.1.1] := by
  apply prEvent_bind_congr
  intro table
  rw [legacyFailure_fixedTable_eq_native]
  rw [← fixedTableLoggedRun_restored_value rounds table
    (simulateLegacyProver rounds prover)]
  rw [prEvent_map]

/-- The actual canonical coin-bearing SR game is bounded by the native all-prefix certificate.
The prover may adaptively query the FS oracle and draw arbitrary private uniform coins. The
right-hand charge counts its translated native adversary's actual distinct hash keys. -/
theorem coinKSExperimentProb_nativeCertificate_bound
    {Input W WitIn StmtOut : Type} (rounds : List Round)
    [DecidableEq Input] [Finite Input]
    [∀ i, SampleableType ((legacySpec rounds).Challenge i)]
    (errors : RoundErrors rounds)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (preserving : ∀ z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relIn : Set (Input × WitIn)) (relOut : Set (StmtOut × W))
    (inputLaw : ∀ z witness, (state z).holds witness ↔
      legacyInputRelation state witnessMap relIn z witness)
    (outputLaw : ∀ z path witness,
      legacyOutputRelation observe relOut z path witness →
        ((extractor z).terminalState path).holds (seed z path witness)) :
    Verifier.StateRestoration.coinKSExperimentProb
      (nativeFiniteLegacyInit (Input := Input) (Salt := PUnit) rounds
        (legacySpec rounds)
        (fun table => QueryImpl.ofFn (nativeTableToLegacy rounds table)))
      (emptyLegacyImpl rounds)
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
      (nativeBackwardLegacyExtractor (OracleSpec.ofPFunctor 0) (legacySpec rounds)
        (legacyToRestorationPath rounds) state extractor seed witnessMap)
      relIn relOut
      (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
        (legacyToRestorationPath rounds) observe) prover ≤
      Finset.univ.sup errors *
        expectedAdversaryFreshKeys rounds (simulateLegacyProver rounds prover) +
        ∑ j, errors j := by
  rw [coinKSExperimentProb_eq_fixedTable]
  have heager := legacyFailure_eager_eq_native rounds state extractor seed witnessMap
    observe relIn relOut prover
  have hbound := eagerNative_legacyFailure_bound rounds errors
    (simulateLegacyProver rounds prover) state extractor preserving bounded seed witnessMap
    observe relIn relOut inputLaw outputLaw
  simpa only [nativeFiniteLegacyInit, QueryImpl.ofFn,
    bind_map_left] using heager.trans_le hbound

end Interaction.Oracle.FiatShamir
