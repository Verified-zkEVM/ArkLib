/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.KnowledgeResources.Composition
public import ArkLib.Interaction.Oracle.Security.StateRestorationBudget

/-!
# State restoration with measured knowledge certificates

`MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform` derives the
closed-oracle knowledge bound `Q * max_j error_j + sum_j error_j` and a bound for the actual
composed extraction program on every completed path. The local stage bound may depend on the
input statement. Each fixed round contributes one message and one challenge stage, giving bound
`rounds.length • (messageBound z + challengeBound z)` from the supplied separate stage bounds.
The same conclusion identifies the measured program's return with the game's input witness.

The suffix `nonuniform` refers to the round-error schedule. Statement-indexed budgets do not impose
one uniform executable implementation on the certificate family, or charge statement/prefix-based
program construction. This is a declared nonnegative instruction count, not a complete execution
or expected-time bound. Pure work, outer views on intermediate witnesses, handlers, terminal
witness identifications, witness sizes, and adversary/replay/restoration work remain outside it.
Every map still has a zero-budget `OracleComp.BudgetedProgram.ofFun`; fixed natural-number
count arithmetic does not remove that limitation.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security

/-- Fixed-round protocols have two authored nodes per round, so local weighted stage bounds
bound every completed instruction path of the actual composed program. -/
theorem RoundExtractor.MeasuredStages.programAlong_costAtMost_protocol
    {ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    {rounds : List Round} {state : KnowledgeState.{0}}
    {extractor : RoundExtractor (protocol rounds).tree state}
    (stages : extractor.MeasuredStages ω) {bound : ω} (h : stages.BudgetAtMost bound)
    (path : (protocol rounds).tree.ExecutionPath) :
    (stages.programAlong path).program.CostAtMost ((2 * rounds.length) • bound) := by
  simpa only [length_executionPath_protocol] using stages.programAlong_costAtMost h path

/-- Local message and challenge budgets for the fixed protocol's paired stages. -/
def RoundExtractor.MeasuredStages.ProtocolBudgetAtMost
    {ω : Type} [AddCommMonoid ω] [Preorder ω] (messageBound challengeBound : ω) :
    {rounds : List Round} → {state : KnowledgeState.{0}} →
    {extractor : RoundExtractor (protocol rounds).tree state} →
    extractor.MeasuredStages ω → Prop
  | [], _, _, _ => True
  | _ :: _, _, _, stages =>
      stages.1.budget ≤ messageBound ∧ ∀ message,
        (stages.2 message).1.budget ≤ challengeBound ∧ ∀ challenge,
          ProtocolBudgetAtMost messageBound challengeBound ((stages.2 message).2 challenge)

/-- Each fixed round contributes one message budget and one challenge budget. -/
theorem RoundExtractor.MeasuredStages.programAlong_budget_le_protocol
    {ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (messageBound challengeBound : ω) :
    {rounds : List Round} → {state : KnowledgeState.{0}} →
    {extractor : RoundExtractor (protocol rounds).tree state} →
    (stages : extractor.MeasuredStages ω) →
    stages.ProtocolBudgetAtMost messageBound challengeBound →
    (path : (protocol rounds).tree.ExecutionPath) →
    (stages.programAlong path).budget ≤ rounds.length • (messageBound + challengeBound)
  | [], _, _, _, _, _ => by
      change (0 : ω) ≤ (0 : Nat) • (messageBound + challengeBound)
      simp
  | _ :: rounds, _, _, stages, hbudget, path => by
      change (((stages.2 path.1).2 path.2.1).programAlong path.2.2).budget +
        (stages.2 path.1).1.budget + stages.1.budget ≤
          (rounds.length + 1) • (messageBound + challengeBound)
      rw [succ_nsmul]
      calc
        _ ≤ rounds.length • (messageBound + challengeBound) + challengeBound + messageBound :=
          add_le_add (add_le_add
            (programAlong_budget_le_protocol messageBound challengeBound
              ((stages.2 path.1).2 path.2.1) ((hbudget.2 path.1).2 path.2.1) path.2.2)
            (hbudget.2 path.1).1) hbudget.1
        _ = _ := by ac_rfl

/-- Separate message and challenge bounds control every actual composed instruction path. -/
theorem RoundExtractor.MeasuredStages.programAlong_costAtMost_protocol_paired
    {ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    {rounds : List Round} {state : KnowledgeState.{0}}
    {extractor : RoundExtractor (protocol rounds).tree state}
    (stages : extractor.MeasuredStages ω) {messageBound challengeBound : ω}
    (hbudget : stages.ProtocolBudgetAtMost messageBound challengeBound)
    (path : (protocol rounds).tree.ExecutionPath) :
    (stages.programAlong path).program.CostAtMost
      (rounds.length • (messageBound + challengeBound)) :=
  (stages.programAlong path).costAtMost.mono
    (stages.programAlong_budget_le_protocol messageBound challengeBound hbudget path)

/-- After the uncharged terminal-carrier conversion, the named composed run returns exactly the
input witness used by the original state-restoration game. -/
theorem MeasuredKnowledgeCertificate.run_programAlong_terminalWitness
    {Kind Input W : Type} [Finite Kind] {rounds : List Round}
    (state : Input → KnowledgeState.{0})
    (certificate : (z : Input) →
      MeasuredKnowledgeCertificate Kind (protocol rounds).tree (protocol rounds).roles (state z))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((certificate z).extractor.terminalState path).Witness)
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) (witness : W) :
    ((certificate z).stages.programAlong path).program.run (terminalWitness z path witness) =
      extractInputWitness state (fun z => (certificate z).extractor) terminalWitness
        z path witness :=
  (certificate z).stages.run_programAlong path (terminalWitness z path witness)

/-- The original closed-oracle game has knowledge error at most `Q * max + sum`. Every actual
composed extraction program has the derived statement-indexed instruction bound. The suffix
`nonuniform` concerns round errors, not a uniform implementation or an extraction-time guarantee. -/
theorem MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform
    {Kind Input Salt : Type} [Finite Kind] {rounds : List Round} {W : Type}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{0})
    (certificate : (z : Input) →
      MeasuredKnowledgeCertificate Kind (protocol rounds).tree (protocol rounds).roles (state z))
    (Z : Set Input) (errors : RoundErrors rounds)
    (schedule : ∀ z ∈ Z, (certificate z).challenges = roundErrorSchedule rounds errors)
    (messageBound challengeBound : Input → Kind → Nat)
    (hbudget : ∀ z ∈ Z, (certificate z).stages.ProtocolBudgetAtMost
      (messageBound z) (challengeBound z))
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
      W ≃ (((certificate z).extractor).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      (((certificate z).extractor).terminalState path).holds (terminalWitness z path witness) ↔
        ∃ claim, closedTerminalObservation initial impl Stmt family terminal z path = some claim ∧
          Rout z path.toBranchPath claim witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
        (closedVerificationGame initial impl Stmt family terminal adversary)).run' ∅}[
      result.1 ∈ Z ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness state (fun z => (certificate z).extractor) terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ Q * Finset.univ.sup errors + ∑ j, errors j ∧
      ∀ z ∈ Z, ∀ path,
        (∀ witness, ((certificate z).stages.programAlong path).program.run
            (terminalWitness z path witness) =
          extractInputWitness state (fun z => (certificate z).extractor) terminalWitness
            z path witness) ∧
        ((certificate z).stages.programAlong path).program.CostAtMost
          (rounds.length • (messageBound z + challengeBound z)) := by
  constructor
  · exact StateRestoration.stateRestoration_oracle_knowledge_soundness_nonuniform state
      (fun z => (certificate z).extractor) Z errors
      (fun z _ => (certificate z).prover_preserving)
      (fun z hz => by rw [← schedule z hz]; exact (certificate z).local_bound)
      initial impl Stmt family terminal Rin Rout terminalWitness inputLaw outputLaw
      adversary Q queryBound
  · intro z hz path
    exact ⟨fun witness => run_programAlong_terminalWitness state certificate terminalWitness
      z path witness,
      (certificate z).stages.programAlong_costAtMost_protocol_paired (hbudget z hz) path⟩

end Interaction.Oracle.Security
