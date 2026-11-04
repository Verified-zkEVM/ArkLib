/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.Interaction.Oracle.Security.KnowledgeResources
public import VCVio.OracleComp.QueryTracking.MeasuredProgram.Composition

/-!
# Measured extraction along an actual execution path

`RoundExtractor.MeasuredStages.programAlong` composes the named instruction programs of all stages
on a supplied path. Its result is the original extractor's witness on that path. The instruction
program of the suffix executes before the instruction program of the root stage, and their
declared budgets add.

The actual path selects the stage programs, under the same scope as `MeasuredStages`. Selecting
and constructing the composed program, packing moves with witnesses, evaluating handlers, and
computing an outer view on the suffix's resulting witness remain uncharged. Terminal witness
conversions are also outside the program. Bounds concern declared weights, not complete extraction
time or intermediate witness sizes. Uniform stage bounds give a path-length bound; when branches
have unbounded depth they do not supply one global composed budget.
-/

@[expose] public section

namespace Interaction.Oracle.Security.RoundExtractor

open OracleComp

variable {ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]

/-- Compose the stage programs along the actual path to compute exactly the named extractor. -/
def MeasuredStages.programAlong : {tree : Oracle.TypeTree.{0}} → {state : KnowledgeState.{0}} →
    {extractor : RoundExtractor tree state} → (stages : extractor.MeasuredStages ω) →
    (path : tree.ExecutionPath) → BudgetedProgram (extractor.extractWitness path) ω
  | .done, _, _, _, _ => BudgetedProgram.ofFun id
  | .public _ _, _, extractor, stages, path =>
      (stages.1.contramap
        (fun witness : (extractor path.1).1.Witness => ⟨path.1, witness⟩)).comp
        ((stages.2 path.1).programAlong path.2)
  | .oracle _ _, _, extractor, stages, path =>
      (stages.1.contramap
        (fun witness : (extractor path.1).1.Witness => ⟨path.1, witness⟩)).comp
        ((stages.2 path.1).programAlong path.2)

/-- The composed instruction program returns the witness of the original extractor. -/
theorem MeasuredStages.run_programAlong {tree : Oracle.TypeTree.{0}} {state : KnowledgeState.{0}}
    {extractor : RoundExtractor tree state} (stages : extractor.MeasuredStages ω)
    (path : tree.ExecutionPath) (witness : (extractor.terminalState path).Witness) :
    (stages.programAlong path).program.run witness = extractor.extractWitness path witness :=
  ((stages.programAlong path).realizes witness).symm

/-- A completed path has no extraction stage and no declared instruction charge. -/
@[simp] theorem MeasuredStages.programAlong_budget_done {state : KnowledgeState.{0}}
    {extractor : RoundExtractor .done state} (stages : extractor.MeasuredStages ω)
    (path : Oracle.TypeTree.done.ExecutionPath) :
    (stages.programAlong path).budget = 0 := rfl

/-- The budget at a public move is the suffix budget plus the root stage's budget. -/
theorem MeasuredStages.programAlong_budget_public {Moves : Type}
    {next : Moves → Oracle.TypeTree.{0}} {state : KnowledgeState.{0}}
    {extractor : RoundExtractor (.public Moves next) state} (stages : extractor.MeasuredStages ω)
    (path : (Oracle.TypeTree.public Moves next).ExecutionPath) :
    (stages.programAlong path).budget =
      ((stages.2 path.1).programAlong path.2).budget + stages.1.budget := rfl

/-- The budget at an oracle message is the suffix budget plus the root stage's budget. -/
theorem MeasuredStages.programAlong_budget_oracle {Messages : Type}
    {next : PUnit → Oracle.TypeTree.{0}} {state : KnowledgeState.{0}}
    {extractor : RoundExtractor (.oracle Messages next) state} (stages : extractor.MeasuredStages ω)
    (path : (Oracle.TypeTree.oracle Messages next).ExecutionPath) :
    (stages.programAlong path).budget =
      ((stages.2 path.1).programAlong path.2).budget + stages.1.budget := rfl

/-- A local stage bound gives a composed bound proportional to the actual path length.
This remains valid for generic weights; no nonnegativity assumption on `bound` is used. -/
theorem MeasuredStages.programAlong_budget_le (bound : ω) :
    {tree : Oracle.TypeTree.{0}} → {state : KnowledgeState.{0}} →
    {extractor : RoundExtractor tree state} → (stages : extractor.MeasuredStages ω) →
    stages.BudgetAtMost bound → (path : tree.ExecutionPath) →
    (stages.programAlong path).budget ≤ path.length • bound
  | .done, _, _, _, _, _ => by
      change (0 : ω) ≤ (0 : Nat) • bound
      simp
  | .public _ _, _, _, stages, h, path => by
      change ((stages.2 path.1).programAlong path.2).budget + stages.1.budget ≤
        (Oracle.TypeTree.ExecutionPath.length path.2 + 1) • bound
      rw [succ_nsmul]
      exact add_le_add (programAlong_budget_le bound (stages.2 path.1) (h.2 path.1) path.2) h.1
  | .oracle _ _, _, _, stages, h, path => by
      change ((stages.2 path.1).programAlong path.2).budget + stages.1.budget ≤
        (Oracle.TypeTree.ExecutionPath.length path.2 + 1) • bound
      rw [succ_nsmul]
      exact add_le_add (programAlong_budget_le bound (stages.2 path.1) (h.2 path.1) path.2) h.1

/-- Every completed instruction path of the actual composed program satisfies the length bound. -/
theorem MeasuredStages.programAlong_costAtMost {tree : Oracle.TypeTree.{0}}
    {state : KnowledgeState.{0}} {extractor : RoundExtractor tree state}
    (stages : extractor.MeasuredStages ω) {bound : ω} (h : stages.BudgetAtMost bound)
    (path : tree.ExecutionPath) :
    (stages.programAlong path).program.CostAtMost (path.length • bound) :=
  (stages.programAlong path).costAtMost.mono (stages.programAlong_budget_le bound h path)

/-- A larger depth cap bounds the composed budget when the local bound is nonnegative. -/
theorem MeasuredStages.programAlong_budget_le_of_length_le {tree : Oracle.TypeTree.{0}}
    {state : KnowledgeState.{0}} {extractor : RoundExtractor tree state}
    (stages : extractor.MeasuredStages ω) {bound : ω} (h : stages.BudgetAtMost bound)
    (nonneg : 0 ≤ bound) (path : tree.ExecutionPath) {depth : Nat}
    (length_le : path.length ≤ depth) : (stages.programAlong path).budget ≤ depth • bound :=
  (stages.programAlong_budget_le bound h path).trans (nsmul_le_nsmul_left nonneg length_le)

end Interaction.Oracle.Security.RoundExtractor
