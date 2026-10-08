/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationReplay

/-!
# State-restoration knowledge soundness

The actual restoration game lets an adversary choose the input, all messages and salts, and an
output witness after adaptive cached-oracle queries. Completion uses the same oracle. The native
verifier then runs on those completed challenges and queries its actual accumulated source access.
Its execution equation is proved from the native runner, without a table available to the game.

The principal theorem converts all-authored-prefix round-by-round knowledge certificates into the
relation-level `(Q + k) * error` bound. A named terminal witness equivalence and endpoint iff laws
identify the supplied output witness and the extracted input witness. Extraction cost and private
random coins are separate statements; the adversary here is a total oracle program.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : List Round}

/-- The verifier's actual terminal observation of the closed input and oracle messages. -/
def terminalObservation (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) : Out z path.toBranchPath :=
  evalWithAnswerFn (path.closingImpl (protocol rounds).oracles initial (impl z))
    (terminal z path.toBranchPath)

/-- The actual native restoration game: complete with the same oracle, then execute the native
prover/verifier on the completed challenges. Replay sees only the completed path, not a table. -/
def verificationGame (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W)) :
    OracleComp (oracleSpec Input Salt rounds)
      ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
        Out z path.toBranchPath × W) := do
  let (z, messages, witness) ← adversary
  let path ← complete rounds z messages
  let result ← executeStrategies (oracleSpec Input Salt rounds) (protocol rounds).tree
    (protocol rounds).roles (protocol rounds).oracles initial (impl z)
    (scriptedProver (oracleSpec Input Salt rounds) rounds messages)
    (challengeVerifier (oracleSpec Input Salt rounds) rounds initial
      (pathPrograms (oracleSpec Input Salt rounds) rounds path) (Out z) (terminal z))
  pure ⟨z, result.1, result.2.2, witness⟩

/-- Actual native verification is exactly the observation of the completed native path. -/
theorem verificationGame_eq (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W)) :
    verificationGame initial impl Out terminal adversary =
      (fun result => (⟨result.1, result.2.1,
        terminalObservation initial impl Out terminal result.1 result.2.1, result.2.2⟩ :
        (z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
          Out z path.toBranchPath × W)) <$>
      restoredExecution rounds adversary := by
  simp only [verificationGame, restoredExecution, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  rintro ⟨z, messages, witness⟩
  apply OracleComp.bind_congr_of_forall_mem_support
  intro path supported
  rw [execute_pathReplay _ _ _ _ messages path
    (complete_support_matches rounds z messages path supported)]
  rfl

/-- The supplied output witness is transported by a named equivalence and extracted backwards
through the actual completed native path. No valid intermediate witness is selected. -/
def extractInputWitness (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) (witness : W) : (state z).Witness :=
  (extractor z).extractWitness path (terminalWitness z path witness)

/-- Round-by-round knowledge bounds imply state-restoration knowledge soundness for the actual
native verifier. The adversary chooses the input adaptively and supplies the terminal witness;
the named backwards extractor fails on a valid output with probability at most `(Q+k)*error`. -/
theorem stateRestoration_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (uniformSchedule error rounds))
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Out z p → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path.toBranchPath (terminalObservation initial impl Out terminal z path) witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
        (verificationGame initial impl Out terminal adversary)).run' ∅}[
      result.1 ∈ Z ∧ Rout result.1 result.2.1.toBranchPath result.2.2.1 result.2.2.2 ∧
      ¬ Rin result.1 (extractInputWitness state extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ (Q + rounds.length) * error := by
  rw [verificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  simp only [extractInputWitness, ← inputLaw, ← outputLaw]
  exact restored_extraction_bound state extractor Z error preserving bounded
    (fun z path => terminalWitness z path) adversary Q queryBound

end Interaction.Oracle.Security.StateRestoration
