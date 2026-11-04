/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Interaction.Oracle.Security.KnowledgeResources.Composition
import ArkLibTest.Data.OracleComp.AddProgram

/-!
# Path-dependent budgets and ordered extraction

A natural-number branch selects an arbitrarily long chain of real one-addition stage programs.
Local budget one therefore gives no global composed budget without a path-depth cap.

A separate three-stage program doubles, applies an explicitly uncharged pure map, then increments.
Its result is checked against arithmetic alternatives that swap or omit the maps. The profile
counts two declared additions; it does not count all host-language arithmetic.
-/

open Interaction.Oracle Interaction.Oracle.Security OracleComp AddProgramTest

namespace MeasuredPathBudgetsTest

/-- Every natural number is an admissible witness. -/
def state : KnowledgeState := ⟨Nat, fun _ => True⟩

private def recorded {A B : Type} (program : MeasuredProgram A B Nat) (input : A) : B × Nat :=
  (simulateQ ((program.answer (program.view input)).withAddCost program.cost)
    (program.program (program.view input))).runAdd.run

private theorem recorded_comp {A B C : Type} (outer : MeasuredProgram B C Nat)
    (inner : MeasuredProgram A B Nat) (input : A) :
    recorded (outer.comp inner) input =
      let inside := recorded inner input
      let outside := recorded outer inside.1
      (outside.1, inside.2 + outside.2) := by
  have h := MeasuredProgram.simulateQ_withAddCost_comp outer inner (inner.view input)
  exact (congrArg (fun computation => computation.runAdd.run) h).trans (by rfl)

/-- A chain with one public node per requested step. -/
def chain : Nat → TypeTree
  | 0 => .done
  | n + 1 => .public Unit (fun _ => chain n)

/-- The first move chooses the remaining depth. -/
def deep : TypeTree := .public Nat chain

def chainExtractor : (n : Nat) → RoundExtractor (chain n) state
  | 0 => PUnit.unit
  | n + 1 => fun _ => ⟨state, (fun w : Nat => w + 1), chainExtractor n⟩

def deepExtractor : RoundExtractor deep state := fun n => ⟨state, id, chainExtractor n⟩

def chainStages : (n : Nat) → (chainExtractor n).MeasuredStages Nat
  | 0 => PUnit.unit
  | n + 1 =>
      ⟨⟨addProgram (fun x => (x.2, 1)), 1, addProgram_realizes _,
        addProgram_costAtMost_one _⟩, fun _ => chainStages n⟩

def deepStages : deepExtractor.MeasuredStages Nat :=
  ⟨BudgetedProgram.ofFun _, fun n => chainStages n⟩

theorem chainStages_budgetAtMost : (n : Nat) → (chainStages n).BudgetAtMost 1
  | 0 => trivial
  | n + 1 => ⟨le_rfl, fun _ => chainStages_budgetAtMost n⟩

def chainPath : (n : Nat) → (chain n).ExecutionPath
  | 0 => PUnit.unit
  | n + 1 => ⟨(), chainPath n⟩

theorem chain_budget : (n : Nat) →
    ((chainStages n).programAlong (chainPath n)).budget = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (chain_budget n)

theorem deep_budget (n : Nat) :
    (deepStages.programAlong (⟨n, chainPath n⟩ : deep.ExecutionPath)).budget = n :=
  (congrArg (· + 0) (chain_budget n)).trans (Nat.add_zero n)

/-- Even real, locally unit-cost instruction programs can have no global composed budget. -/
theorem no_global_budget_of_stage_bound :
    deepStages.BudgetAtMost 1 ∧ ∀ bound : Nat, ∃ path : deep.ExecutionPath,
      ¬ (deepStages.programAlong path).budget ≤ bound := by
  refine ⟨⟨Nat.zero_le 1, chainStages_budgetAtMost⟩, fun bound => ?_⟩
  refine ⟨⟨bound + 1, chainPath (bound + 1)⟩, ?_⟩
  intro le_bound
  have too_large : bound + 1 ≤ bound := deep_budget (bound + 1) ▸ le_bound
  exact Nat.not_succ_le_self bound too_large

private theorem chain_recorded_cost : (n : Nat) →
    (witness : ((chainExtractor n).terminalState (chainPath n)).Witness) →
    (recorded ((chainStages n).programAlong (chainPath n)).program witness).2 = n
  | 0, _ => rfl
  | n + 1, witness => by
      let outer := (chainStages (n + 1)).1.program.contramap
        (fun witness : (chainExtractor (n + 1) ()).1.Witness => ⟨(), witness⟩)
      let inner := ((chainStages n).programAlong (chainPath n)).program
      change (recorded (outer.comp inner) witness).2 = n + 1
      apply (congrArg Prod.snd (recorded_comp outer inner witness)).trans
      change (recorded inner witness).2 + 1 = n + 1
      exact congrArg (· + 1) (chain_recorded_cost n witness)

private def chainWitness : (n : Nat) → ((chainExtractor n).terminalState (chainPath n)).Witness
  | 0 => (0 : Nat)
  | n + 1 => chainWitness n

private theorem deep_recorded_cost (n : Nat) :
    (recorded (deepStages.programAlong (⟨n, chainPath n⟩ : deep.ExecutionPath)).program
      (chainWitness n)).2 = n := by
  let outer := deepStages.1.program.contramap
    (fun witness : (deepExtractor n).1.Witness => ⟨n, witness⟩)
  let inner := ((chainStages n).programAlong (chainPath n)).program
  change (recorded (outer.comp inner) (chainWitness n)).2 = n
  apply (congrArg Prod.snd (recorded_comp outer inner (chainWitness n))).trans
  change (recorded inner (chainWitness n)).2 + 0 = n
  exact (Nat.add_zero _).trans (chain_recorded_cost n (chainWitness n))

/-- No global bound controls actual instruction cost, despite local budget one. -/
theorem no_global_cost_bound_of_stage_bound :
    deepStages.BudgetAtMost 1 ∧ ∀ bound : Nat, ∃ path : deep.ExecutionPath,
      ¬ (deepStages.programAlong path).program.CostAtMost bound := by
  refine ⟨no_global_budget_of_stage_bound.1, fun bound => ?_⟩
  refine ⟨⟨bound + 1, chainPath (bound + 1)⟩, ?_⟩
  intro h
  have cost_le := h.runAdd_le
    ((deepStages.programAlong
      (⟨bound + 1, chainPath (bound + 1)⟩ : deep.ExecutionPath)).program.view
      (chainWitness (bound + 1)))
  change (recorded
    (deepStages.programAlong (⟨bound + 1, chainPath (bound + 1)⟩ : deep.ExecutionPath)).program
    (chainWitness (bound + 1))).2 ≤ bound at cost_le
  have too_large : bound + 1 ≤ bound :=
    (congrArg (fun value : Nat => value ≤ bound) (deep_recorded_cost (bound + 1))).mp cost_le
  exact Nat.not_succ_le_self bound too_large

/-- The actual path-length theorem applies without unfolding the chosen branch's tree. -/
example (path : deep.ExecutionPath) :
    (deepStages.programAlong path).program.CostAtMost (path.length • (1 : Nat)) :=
  deepStages.programAlong_costAtMost ⟨Nat.zero_le 1, chainStages_budgetAtMost⟩ path

/-- The zero-round boundary has no charged stage, for every terminal witness. -/
example :
    let extractor : RoundExtractor .done state := PUnit.unit
    let stages : extractor.MeasuredStages Nat := PUnit.unit
    (stages.programAlong PUnit.unit).program.CostAtMost 0 := by
  exact MeasuredProgram.costAtMost_ofFun _

/-- No authored nodes means path length zero. -/
example (path : TypeTree.done.ExecutionPath) : path.length = 0 := rfl

/-- A larger depth cap is invalid for negative weights without the nonnegativity premise. -/
example :
    let extractor : RoundExtractor .done state := PUnit.unit
    let stages : extractor.MeasuredStages Int := PUnit.unit
    stages.BudgetAtMost (-1) ∧
      TypeTree.ExecutionPath.length (tree := TypeTree.done) PUnit.unit ≤ 1 ∧
      ¬ (stages.programAlong PUnit.unit).budget ≤ (1 : Nat) • (-1 : Int) := by
  change True ∧ (0 : Nat) ≤ 1 ∧ ¬ (0 : Int) ≤ (1 : Nat) • (-1 : Int)
  exact ⟨trivial, Nat.zero_le 1, by decide⟩

/-- Three public stages, with only the first and last requesting an addition instruction. -/
def orderedTree : TypeTree :=
  .public Unit (fun _ => .public Unit (fun _ => .public Unit (fun _ => .done)))

def orderedExtractor : RoundExtractor orderedTree state := fun _ =>
  ⟨state, (fun w : Nat => w + 1), fun _ =>
    ⟨state, (fun w : Nat => w + 5), fun _ =>
      ⟨state, (fun w : Nat => w + w), PUnit.unit⟩⟩⟩

def orderedStages : orderedExtractor.MeasuredStages Nat :=
  ⟨⟨addProgram (fun x => (x.2, 1)), 1, addProgram_realizes _,
      addProgram_costAtMost_one _⟩, fun _ =>
    ⟨BudgetedProgram.ofFun _, fun _ =>
      ⟨⟨addProgram (fun x => (x.2, x.2)), 1, addProgram_realizes _,
          addProgram_costAtMost_one _⟩, fun _ => PUnit.unit⟩⟩⟩

def orderedPath : orderedTree.ExecutionPath := ⟨(), (), (), PUnit.unit⟩

def orderedObservation (witness : Nat) : Nat × Nat :=
  recorded (orderedStages.programAlong orderedPath).program witness

/-- Both charged programs execute, with the intervening uncharged map, on every input. -/
example (witness : Nat) : orderedObservation witness = (witness + witness + 6, 2) := rfl

/-- Swapping the charged stages would give eighteen, rather than twelve. -/
example : (orderedObservation 3).1 ≠ (3 + 1 + 5) + (3 + 1 + 5) := by decide

/-- Omitting the zero-charge middle map would give seven, rather than twelve. -/
example : (orderedObservation 3).1 ≠ 3 + 3 + 1 := by decide

private def checkOrderedObservation : IO Unit := do
  for witness in [0, 3, 19] do
    unless orderedObservation witness == (witness + witness + 6, 2) do
      throw (IO.userError "Composed extraction changed stage order or omitted a stage")
  IO.println "Ordered extraction preserves both charged stages and the uncharged middle map."

/-- info: Ordered extraction preserves both charged stages and the uncharged middle map. -/
#guard_msgs in
#eval checkOrderedObservation

/-- info: (4, 4) -/
#guard_msgs in
#eval recorded (deepStages.programAlong (⟨(4 : Nat), chainPath 4⟩ : deep.ExecutionPath)).program
  (chainWitness 4)

end MeasuredPathBudgetsTest
