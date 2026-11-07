/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Interaction.Oracle.Security.Knowledge
public import VCVio.OracleComp.QueryTracking.MeasuredProgram

/-!
# Knowledge certificates with measured stages

At each authored node of a tree, a `RoundExtractor` names one backward witness map for each
actual move or oracle message. `RoundExtractor.stageMap` combines them into the stage at that node:
a map from a move or message and a witness of the knowledge state after it to a witness of the
knowledge state before it. Complete extraction, `RoundExtractor.extractWitness`, applies the stage
maps along a path (`RoundExtractor.extractWitness_public`, `RoundExtractor.extractWitness_oracle`).

`RoundExtractor.MeasuredStages` names, for the stage at every authored node, a measured program
that realizes the stage map and a budget for its declared instruction charges
(`OracleComp.BudgetedProgram`). `MeasuredStages.BudgetAtMost` bounds all of these budgets by one
value. `MeasuredKnowledgeCertificate` adds the stages to a `KnowledgeCertificate` for the same
extractor; forgetting them recovers the certificate, whose fields the round-by-round and
state-restoration theorems take. The theorem
`MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform` in
`StateRestorationResources` derives a composed-path instruction bound from the supplied local
stage bounds and the fixed protocol depth, for that same named extractor. The local bound may
depend on the input statement; it does not impose a uniform executable certificate family.

`MeasuredStages.programAlong` in `KnowledgeResources.Composition` composes the stage instruction
programs along an actual path and adds their declared budgets.

## Scope

Each budget bounds the declared instructions of one stage, under the accounting of
`OracleComp.MeasuredProgram`, which lists what is uncharged. Every map has a budgeted program with
budget zero, so only a named program with a stated instruction set is evidence. Beyond that
accounting, the following are uncharged.

* Stages are indexed by the actual earlier moves and oracle messages, so each stage's program, view
  and handlers may compute anything from that earlier prefix without charge, and stages at
  different prefixes may carry different budgets. A common bound across prefixes is an assumed
  hypothesis, such as `BudgetAtMost` or `ProtocolBudgetAtMost`.
* The intermediate witness carriers are chosen with the extractor, and the identifications of
  carriers with a game's witnesses (`TerminalRelation.witnessEquiv`, a state-restoration
  `terminalWitness`, `RoundExtractor.changeInputState`) are not programs. An equivalence onto the
  graph of a function computes that function, so stage budgets bound extraction only together with
  a separately stated cost of these identifications.
* Complete execution of the stage composition, the size of intermediate witnesses, and computation
  of the knowledge predicates are not bounded. The composed program counts only the declared
  instructions of the stage programs.

`MeasuredKnowledgeCertificate` uses a finite resource-kind type and fixes standard addition and
order on natural-number count profiles. The underlying `MeasuredStages` and `BudgetAtMost` remain
generic weighted accounting, including idempotent or signed valuations that do not count
instructions. Fixed count arithmetic does not eliminate zero-charge instructions or the uncharged
work above.

An empty `Kind` records no resources: its count profile is uniquely zero, so every count budget
is vacuous. A scalar count uses `Unit → Nat`.

Moves and witness carriers live in `Type`, the universe of a measured program's input and result.
-/

@[expose] public section

namespace Interaction.Oracle.Security

open OracleComp

namespace RoundExtractor

/-- The input of the stage at the root of a tree: an actual move or oracle message and a
witness of the knowledge state after it. A completed tree has no stage and no stage input. -/
def StageInput : {tree : Oracle.TypeTree.{0}} → {state : KnowledgeState.{0}} →
    RoundExtractor tree state → Type
  | .done, _, _ => PEmpty
  | .public Moves _, _, extractor => (move : Moves) × (extractor move).1.Witness
  | .oracle Messages _, _, extractor => (message : Messages) × (extractor message).1.Witness

/-- The backward witness map at the root of a tree. -/
def stageMap : {tree : Oracle.TypeTree.{0}} → {state : KnowledgeState.{0}} →
    (extractor : RoundExtractor tree state) → extractor.StageInput → state.Witness
  | .done, _, _, input => input.elim
  | .public _ _, _, extractor, input => (extractor input.1).2.1 input.2
  | .oracle _ _, _, extractor, input => (extractor input.1).2.1 input.2

/-- Complete extraction at a move node applies the root stage map to the witness extracted from
the remaining path. -/
theorem extractWitness_public {Moves : Type} {next : Moves → Oracle.TypeTree.{0}}
    {state : KnowledgeState.{0}} (extractor : RoundExtractor (.public Moves next) state)
    (path : (Oracle.TypeTree.public Moves next).ExecutionPath)
    (witness : (extractor.terminalState path).Witness) :
    extractor.extractWitness path witness =
      extractor.stageMap ⟨path.1, (extractor path.1).2.2.extractWitness path.2 witness⟩ :=
  rfl

/-- Complete extraction at an oracle node applies the root stage map to the witness extracted from
the remaining path. -/
theorem extractWitness_oracle {Messages : Type} {next : PUnit → Oracle.TypeTree.{0}}
    {state : KnowledgeState.{0}} (extractor : RoundExtractor (.oracle Messages next) state)
    (path : (Oracle.TypeTree.oracle Messages next).ExecutionPath)
    (witness : (extractor.terminalState path).Witness) :
    extractor.extractWitness path witness =
      extractor.stageMap ⟨path.1, (extractor path.1).2.2.extractWitness path.2 witness⟩ :=
  rfl

/-- A budgeted program for the stage map at every authored node, indexed by the actual earlier
moves and oracle messages. -/
def MeasuredStages (ω : Type) [AddCommMonoid ω] [Preorder ω] :
    {tree : Oracle.TypeTree.{0}} → {state : KnowledgeState.{0}} → RoundExtractor tree state →
    Type 1
  | .done, _, _ => PUnit
  | .public Moves _, _, extractor =>
      BudgetedProgram extractor.stageMap ω ×
        ((move : Moves) → MeasuredStages ω (extractor move).2.2)
  | .oracle Messages _, _, extractor =>
      BudgetedProgram extractor.stageMap ω ×
        ((message : Messages) → MeasuredStages ω (extractor message).2.2)

/-- Every stage's budget is at most `bound`, at every authored node. -/
def MeasuredStages.BudgetAtMost {ω : Type} [AddCommMonoid ω] [Preorder ω] (bound : ω) :
    {tree : Oracle.TypeTree.{0}} → {state : KnowledgeState.{0}} →
    {extractor : RoundExtractor tree state} → extractor.MeasuredStages ω → Prop
  | .done, _, _, _ => True
  | .public _ _, _, _, stages =>
      stages.1.budget ≤ bound ∧ ∀ move, BudgetAtMost bound (stages.2 move)
  | .oracle _ _, _, _, stages =>
      stages.1.budget ≤ bound ∧ ∀ message, BudgetAtMost bound (stages.2 message)

end RoundExtractor

/-- A knowledge certificate whose named extractor has, at every authored node, a budgeted stage
program charging natural-number counts indexed by the finite type `Kind`. -/
structure MeasuredKnowledgeCertificate (Kind : Type) [Finite Kind]
    (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration) (state : KnowledgeState.{0})
    extends KnowledgeCertificate tree roles state where
  /-- A measured program and budget for each stage of the named extractor. -/
  stages : extractor.MeasuredStages (Kind → Nat)

end Interaction.Oracle.Security
