/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationGame

/-!
# State-restoration knowledge soundness for oracle outputs

The native verifier returns an optional open oracle claim. After actual execution, the relation
observes its closed behavior under that same path's accumulated input/message handler. The native
verifier never receives concrete oracle realizations or that closing handler as authoring data.
Rejection remains unsuccessful. The resulting extraction bound applies to arbitrary output
relations on closed behavior, including virtual outputs with arbitrarily many possible queries.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : List Round}

/-- The native terminal program may reject or return an open claim over declared source access. -/
abbrev OracleOutput (initial : PFunctor)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (z : Input) (p : (protocol rounds).tree.BranchPath) :=
  Option (OpenClaim
    (ofPFunctor (accessAfter (protocol rounds).tree (protocol rounds).oracles initial p))
    (Stmt z p) (family z p))

/-- Close the actual native verifier's returned virtual output under that same run's handler.
Closing interprets the relation and grants no concrete payload access to verifier authoring. -/
def closedVerificationGame (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W)) :
    OracleComp (oracleSpec Input Salt rounds)
      ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
        Option (ClosedClaim (Stmt z path.toBranchPath) (family z path.toBranchPath)) × W) :=
  (fun result => ⟨result.1, result.2.1,
    result.2.2.1.map (fun claim => claim.closeWith
      (result.2.1.closingImpl (protocol rounds).oracles initial (impl result.1))),
    result.2.2.2⟩) <$>
    verificationGame initial impl (OracleOutput initial Stmt family) terminal adversary

/-- Observe the output oracle behavior using the accumulated handler of the completed path. -/
def closedTerminalObservation (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) :
    Option (ClosedClaim (Stmt z path.toBranchPath) (family z path.toBranchPath)) :=
  (terminalObservation initial impl (OracleOutput initial Stmt family) terminal z path).map
    (fun claim => claim.closeWith
      (path.closingImpl (protocol rounds).oracles initial (impl z)))

/-- Exact actual-execution equation, including the verifier's virtual output interpretation. -/
theorem closedVerificationGame_eq (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W)) :
    closedVerificationGame initial impl Stmt family terminal adversary =
      (fun result => (⟨result.1, result.2.1,
        closedTerminalObservation initial impl Stmt family terminal result.1 result.2.1,
        result.2.2⟩ : (z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
          Option (ClosedClaim (Stmt z path.toBranchPath) (family z path.toBranchPath)) × W)) <$>
        restoredExecution rounds adversary := by
  rw [closedVerificationGame, verificationGame_eq, Functor.map_map]
  rfl

/-- Round-by-round knowledge bounds imply state-restoration knowledge soundness for oracle
output relations. The relation sees the actual closed output behavior, never open query code or
unobserved concrete realizations. Rejection is never a valid output. -/
theorem stateRestoration_oracle_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (uniformSchedule error rounds))
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
        result.1 result.2.1 result.2.2.2)] ≤ (Q + rounds.length) * error := by
  rw [closedVerificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  simp only [extractInputWitness, ← inputLaw, ← outputLaw]
  exact restored_extraction_bound state extractor Z error preserving bounded
    (fun z path => terminalWitness z path) adversary Q queryBound

end Interaction.Oracle.Security.StateRestoration
