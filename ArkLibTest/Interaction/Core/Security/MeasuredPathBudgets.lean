/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Quang Dao
-/
import ArkLib.Interaction.Core.Security.MeasuredResources
import ArkLibTest.Data.OracleComp.AddProgram

/-!
# Path-dependent budgets and ordered extraction

A first natural-number message selects an arbitrarily long chain of unit messages, and the state
function adds one at each chain message with a real one-addition stage program. A local step
budget of one therefore gives no global budget without a bound on the number of moves.

A separate three-move program doubles, applies an explicitly uncharged pure map, then increments.
Its result is checked against arithmetic alternatives that swap or omit the maps. The profile
counts two declared additions; it does not count all host-language arithmetic.
-/

open PFunctor PFunctor.FreeM Interaction.Core OracleComp AddProgramTest

namespace Interaction.Core.MeasuredPathBudgetsTests

/-- Runs a measured program with its handlers and records its additive cost. -/
def recorded {A B : Type} (program : MeasuredProgram A B Nat) (input : A) : B × Nat :=
  (simulateQ ((program.answer (program.view input)).withAddCost program.cost)
    (program.program (program.view input))).runAdd.run

-- MeasuredPathBudgets row 1 (`recorded_comp`): ported unchanged.
/-- Recording the additive cost commutes with composition. -/
theorem recorded_comp {A B C : Type} (outer : MeasuredProgram B C Nat)
    (inner : MeasuredProgram A B Nat) (input : A) :
    recorded (outer.comp inner) input =
      let inside := recorded inner input
      let outside := recorded outer inside.1
      (outside.1, inside.2 + outside.2) := by
  have h := MeasuredProgram.simulateQ_withAddCost_comp outer inner (inner.view input)
  exact (congrArg (fun computation => computation.runAdd.run) h).trans (by rfl)

/-- Recording the cost of a precomposed program records it on the mapped input. -/
theorem recorded_contramap {A B I : Type} (M : MeasuredProgram A B Nat) (g : I → A) (input : I) :
    recorded (M.contramap g) input = recorded M (g input) := rfl

/-- A program that requests no instruction records no cost. -/
theorem recorded_ofFun {A B : Type} (f : A → B) (input : A) :
    recorded (MeasuredProgram.ofFun f) input = (f input, 0) := rfl

/-- The one-addition program records one addition. -/
theorem recorded_addProgram {A : Type} (view : A → Nat × Nat) (input : A) :
    recorded (addProgram view) input = ((view input).1 + (view input).2, 1) := rfl

/-- Whether a cursor is the root. -/
def isRoot {s t : Protocol.{0}} : Cursor.Spine s t → Bool
  | .root _ => true
  | .down _ _ => false

/-- A cursor extended by one move is not the root. -/
@[simp] theorem isRoot_comp {s t u : Protocol.{0}} (sp : Cursor.Spine s t)
    (tail : Cursor.Spine t u) (h : isRoot tail = false) : isRoot (sp.comp tail) = false := by
  cases sp with
  | root => exact h
  | down => rfl

/-- A state function with natural-number witnesses at every prefix, given step maps and identity
root and leaf maps. Every state holds. -/
def natState (s : Protocol.{0}) (step : ∀ {a next}, Cursor.Spine s (.liftBind a next) → Nat → Nat) :
    KnowledgeStateFunction plainSig s Unit Nat Nat (fun _ => True) (fun _ _ => True)
      (fun _ _ _ => True) where
  Witness _ _ := Nat
  toFun _ _ _ _ := True
  extractRoot _ w := w
  extractStep sp _ _ _ w := step sp w
  extractLeaf _ _ _ w := w
  root _ _ _ _ := trivial
  send _ _ _ _ _ _ _ := trivial
  leaf _ _ _ _ _ := trivial

/-- Adds one unless skipped. -/
def countMap : Bool → Nat → Nat
  | true, w => w
  | false, w => w + 1

/-- The uncharged identity when skipped, and otherwise one charged addition. -/
def countProgram {A : Type} (g : A → Nat) :
    (skip : Bool) → BudgetedProgram (fun x => countMap skip (g x)) Nat
  | true => BudgetedProgram.ofFun _
  | false => ⟨addProgram (fun x => (g x, 1)), 1, addProgram_realizes _,
      addProgram_costAtMost_one _⟩

/-- Every count program has budget at most one. -/
theorem countProgram_budget_le {A : Type} (g : A → Nat) :
    (skip : Bool) → (countProgram g skip).budget ≤ 1
  | true => Nat.zero_le 1
  | false => le_rfl

/-- A chain with one unit message per requested step. -/
def chain : Nat → Protocol.{0}
  | 0 => .pure ⟨⟩
  | n + 1 => .liftBind (.message Unit) (fun _ => chain n)

/-- The first message chooses the remaining depth. -/
def deep : Protocol.{0} := .liftBind (.message Nat) chain

/-- Every chain message adds one. -/
def chainState (n : Nat) := natState (chain n) (fun _ w => w + 1)

/-- The first message of `deep` is uncharged; every chain message adds one. -/
def deepState := natState deep (fun sp w => countMap (isRoot sp) w)

/-- One charged addition at every chain message. -/
def chainStages (n : Nat) : (chainState n).MeasuredStages Nat where
  root _ := BudgetedProgram.ofFun _
  step _ _ _ sp history := countProgram (fun x : (chainState n).StageInput sp history => x.2) false
  leaf _ _ _ := BudgetedProgram.ofFun _

/-- The first stage requests no instruction; every chain stage requests one addition. -/
def deepStages : deepState.MeasuredStages Nat where
  root _ := BudgetedProgram.ofFun _
  step _ _ _ sp history := countProgram (fun x : deepState.StageInput sp history => x.2) (isRoot sp)
  leaf _ _ _ := BudgetedProgram.ofFun _

/-- The chain transcript. -/
def chainPath : (n : Nat) → PathAlong plainSig (chain n)
  | 0 => ⟨⟩
  | n + 1 => ⟨(), chainPath n⟩

/-- The transcript of `deep` whose first message is `n`. -/
def deepPath (n : Nat) : PathAlong plainSig deep := ⟨n, chainPath n⟩

-- MeasuredPathBudgets row 2 (`chainStages_budgetAtMost`), restated with root and leaf bounds zero.
/-- Every chain stage has budget at most one. -/
theorem chainStages_budgetAtMost (n : Nat) : (chainStages n).BudgetAtMost 0 1 0 where
  root _ := le_rfl
  step _ _ _ _ _ := le_rfl
  leaf _ _ _ := le_rfl

/-- Every stage of `deep` has budget at most one. -/
theorem deepStages_budgetAtMost : deepStages.BudgetAtMost 0 1 0 where
  root _ := le_rfl
  step _ _ _ sp _ := countProgram_budget_le _ (isRoot sp)
  leaf _ _ _ := le_rfl

/-- From any chain cursor, the remaining chain costs one per message. -/
theorem chain_budgetFrom (n : Nat) : (k : Nat) → (sp : Cursor.Spine (chain n) (chain k)) →
    (history : PrefixMoves plainSig sp) →
    ((chainStages n).programFrom () sp history (chainPath k)).budget = k
  | 0, _, _ => rfl
  | k + 1, _, _ => congrArg (· + 1) (chain_budgetFrom n k _ _)

-- MeasuredPathBudgets row 3 (`chain_budget`): the length is the number of chain messages.
/-- The budget along the chain transcript is its length. -/
theorem chain_budget (n : Nat) : ((chainStages n).programAlong () (chainPath n)).budget = n :=
  chain_budgetFrom n n (.root _) ⟨⟩

/-- Below the first message of `deep`, the remaining chain costs one per message. -/
theorem deep_budgetFrom : (k : Nat) → (sp : Cursor.Spine deep (chain k)) → isRoot sp = false →
    (history : PrefixMoves plainSig sp) →
    (deepStages.programFrom () sp history (chainPath k)).budget = k
  | 0, _, _, _ => rfl
  | k + 1, sp, hsp, history => by
    change (deepStages.programFrom () _ _ (chainPath k)).budget +
      (countProgram (fun x : deepState.StageInput sp history => x.2) (isRoot sp)).budget = k + 1
    rw [hsp]
    exact congrArg (· + 1) (deep_budgetFrom k _ (isRoot_comp sp _ rfl) _)

-- MeasuredPathBudgets row 4 (`deep_budget`).
/-- The budget along the transcript of `deep` with first message `n` is `n`. -/
theorem deep_budget (n : Nat) : (deepStages.programAlong () (deepPath n)).budget = n :=
  deep_budgetFrom n _ rfl _

-- MeasuredPathBudgets row 5 (`no_global_budget_of_stage_bound`).
/-- Locally unit-cost instruction programs can have no global composed budget. -/
theorem no_global_budget_of_stage_bound :
    deepStages.BudgetAtMost 0 1 0 ∧ ∀ bound : Nat, ∃ tr : PathAlong plainSig deep,
      ¬ (deepStages.programAlong () tr).budget ≤ bound := by
  refine ⟨deepStages_budgetAtMost, fun bound => ⟨deepPath (bound + 1), ?_⟩⟩
  rw [deep_budget]
  exact Nat.not_succ_le_self bound

/-- From any chain cursor, the recorded cost of the remaining chain is one per message. -/
theorem chain_recordedFrom (n : Nat) : (k : Nat) → (sp : Cursor.Spine (chain n) (chain k)) →
    (history : PrefixMoves plainSig sp) → (w : Nat) →
    (recorded ((chainStages n).programFrom () sp history (chainPath k)).program w).2 = k
  | 0, _, _, _ => rfl
  | k + 1, sp, history, w => by
    refine (congrArg Prod.snd (recorded_comp _ _ w)).trans ?_
    exact congrArg (· + 1) (chain_recordedFrom n k _ _ w)

-- MeasuredPathBudgets row 6 (`chain_recorded_cost`), at every output witness.
/-- The recorded cost along the chain transcript is its length. -/
theorem chain_recorded_cost (n w : Nat) :
    (recorded ((chainStages n).programAlong () (chainPath n)).program w).2 = n :=
  (congrArg Prod.snd (recorded_comp _ _ w)).trans
    ((congrArg (· + 0) (chain_recordedFrom n n (.root _) ⟨⟩ w)).trans (Nat.add_zero n))

/-- Below the first message of `deep`, the recorded cost of the remaining chain is one per
message. -/
theorem deep_recordedFrom : (k : Nat) → (sp : Cursor.Spine deep (chain k)) → isRoot sp = false →
    (history : PrefixMoves plainSig sp) → (w : Nat) →
    (recorded (deepStages.programFrom () sp history (chainPath k)).program w).2 = k
  | 0, _, _, _, _ => rfl
  | k + 1, sp, hsp, history, w => by
    refine (congrArg Prod.snd (recorded_comp _ _ w)).trans ?_
    refine congrArg₂ (· + ·) (deep_recordedFrom k _ (isRoot_comp sp _ rfl) _ w) ?_
    change (recorded (countProgram (fun x : deepState.StageInput sp history => x.2)
      (isRoot sp)).program _).2 = 1
    rw [hsp]
    rfl

-- MeasuredPathBudgets row 7 (`deep_recorded_cost`), at every output witness.
/-- The recorded cost along the transcript of `deep` with first message `n` is `n`. -/
theorem deep_recorded_cost (n w : Nat) :
    (recorded (deepStages.programAlong () (deepPath n)).program w).2 = n := by
  refine (congrArg Prod.snd (recorded_comp _ _ w)).trans ?_
  refine (congrArg (· + 0) ((congrArg Prod.snd (recorded_comp _ _ w)).trans ?_)).trans
    (Nat.add_zero n)
  exact (congrArg (· + 0) (deep_recordedFrom n _ rfl _ w)).trans (Nat.add_zero n)

-- MeasuredPathBudgets row 8 (`no_global_cost_bound_of_stage_bound`).
/-- No global bound controls actual instruction cost, despite local budget one. -/
theorem no_global_cost_bound_of_stage_bound :
    deepStages.BudgetAtMost 0 1 0 ∧ ∀ bound : Nat, ∃ tr : PathAlong plainSig deep,
      ¬ (deepStages.programAlong () tr).program.CostAtMost bound := by
  refine ⟨deepStages_budgetAtMost, fun bound => ⟨deepPath (bound + 1), fun h => ?_⟩⟩
  have cost_le := h.runAdd_le
    ((deepStages.programAlong () (deepPath (bound + 1))).program.view 0)
  change (recorded (deepStages.programAlong () (deepPath (bound + 1))).program 0).2 ≤ bound
    at cost_le
  rw [deep_recorded_cost] at cost_le
  exact Nat.not_succ_le_self bound cost_le

-- MeasuredPathBudgets row 9: the length is the number of moves of the transcript.
/-- The path-length bound applies without unfolding the chosen branch. -/
example (tr : PathAlong plainSig deep) :
    (deepStages.programAlong () tr).program.CostAtMost
      ((completeSpine plainSig tr).length • (1 : Nat)) :=
  deepStages.programAlong_costAtMost_nsmul deepStages_budgetAtMost () tr

-- MeasuredPathBudgets row 10, restated for every state function on the empty protocol and every
-- stages with zero root and leaf bounds.
/-- On the empty protocol, stages with zero root and leaf bounds cost nothing. -/
example {S W Win : Type} {admissible : S → Prop} {relIn : S → Win → Prop}
    {validOutput : S → PathAlong plainSig (.pure ⟨⟩ : Protocol.{0}) → W → Prop}
    (F : KnowledgeStateFunction plainSig (.pure ⟨⟩ : Protocol.{0}) S W Win admissible relIn
      validOutput)
    (stages : F.MeasuredStages Nat) {stepBound : Nat} (h : stages.BudgetAtMost 0 stepBound 0)
    (stmt : S) (tr : PathAlong plainSig (.pure ⟨⟩ : Protocol.{0})) :
    (stages.programAlong stmt tr).program.CostAtMost 0 := by
  simpa [completeSpine, Cursor.Spine.length] using stages.programAlong_costAtMost_nsmul h stmt tr

-- MeasuredPathBudgets row 11: the transcript of the empty protocol has no move.
/-- The empty transcript has length zero. -/
example (tr : PathAlong plainSig (.pure ⟨⟩ : Protocol.{0})) :
    (completeSpine plainSig tr).length = 0 := rfl

-- MeasuredPathBudgets row 12: the ω-generic monoid is kept, with step bound `-1` over `Int`.
/-- With a negative weight, `length • stepBound` cannot be relaxed to a larger depth cap. -/
example :
    let F := natState (.pure ⟨⟩) (fun _ w => w)
    let stages : F.MeasuredStages Int := KnowledgeStateFunction.MeasuredStages.zero F
    stages.BudgetAtMost 0 (-1) 0 ∧ (completeSpine plainSig (s := .pure ⟨⟩) ⟨⟩).length ≤ 1 ∧
      ¬ (stages.programAlong () ⟨⟩).budget ≤ (1 : Nat) • (-1 : Int) := by
  intro F stages
  refine ⟨⟨fun _ => le_rfl, fun _ _ _ sp _ => (nomatch sp), fun _ _ _ => le_rfl⟩,
    Nat.zero_le 1, ?_⟩
  change ¬ (0 : Int) + 0 ≤ (1 : Nat) • (-1 : Int)
  decide

/-- Three unit messages. -/
def orderedProtocol : Protocol.{0} :=
  .liftBind (.message Unit) fun _ => .liftBind (.message Unit) fun _ =>
    .liftBind (.message Unit) fun _ => .pure ⟨⟩

/-- The backward map at each depth: increment, add five, double. -/
def orderedMap : Nat → Nat → Nat
  | 0, w => w + 1
  | 1, w => w + 5
  | _, w => w + w

/-- The first and last stages request one addition; the middle stage is uncharged. -/
def orderedProgram {A : Type} (g : A → Nat) :
    (k : Nat) → BudgetedProgram (fun x => orderedMap k (g x)) Nat
  | 0 => ⟨addProgram (fun x => (g x, 1)), 1, addProgram_realizes _,
      addProgram_costAtMost_one _⟩
  | 1 => BudgetedProgram.ofFun _
  | _ + 2 => ⟨addProgram (fun x => (g x, g x)), 1, addProgram_realizes _,
      addProgram_costAtMost_one _⟩

/-- The state function whose step at depth `k` is `orderedMap k`. -/
def orderedState := natState orderedProtocol (fun sp w => orderedMap sp.length w)

/-- The stage programs of `orderedState`. -/
def orderedStages : orderedState.MeasuredStages Nat where
  root _ := BudgetedProgram.ofFun _
  step _ _ _ sp history := orderedProgram (fun x : orderedState.StageInput sp history => x.2)
    sp.length
  leaf _ _ _ := BudgetedProgram.ofFun _

/-- The transcript of `orderedProtocol`. -/
def orderedPath : PathAlong plainSig orderedProtocol := ⟨(), (), (), ⟨⟩⟩

/-- The extracted witness and recorded cost of the ordered extraction. -/
def orderedObservation (w : Nat) : Nat × Nat :=
  recorded (orderedStages.programAlong () orderedPath).program w

-- MeasuredPathBudgets row 13.
/-- Both charged programs execute, with the intervening uncharged map, on every input. -/
example (w : Nat) : orderedObservation w = (w + w + 6, 2) := rfl

-- MeasuredPathBudgets row 14.
/-- Swapping the charged stages would give eighteen, rather than twelve. -/
example : (orderedObservation 3).1 ≠ (3 + 1 + 5) + (3 + 1 + 5) := by decide

-- MeasuredPathBudgets row 15.
/-- Omitting the zero-charge middle map would give seven, rather than twelve. -/
example : (orderedObservation 3).1 ≠ 3 + 3 + 1 := by decide

/-- Checks the ordered extraction at sample witnesses. -/
def checkOrderedObservation : IO Unit := do
  for w in [0, 3, 19] do
    unless orderedObservation w == (w + w + 6, 2) do
      throw (IO.userError "Composed extraction changed stage order or omitted a stage")
  IO.println "Ordered extraction preserves both charged stages and the uncharged middle map."

-- MeasuredPathBudgets row 16.
/-- info: Ordered extraction preserves both charged stages and the uncharged middle map. -/
#guard_msgs in
#eval checkOrderedObservation

-- MeasuredPathBudgets row 17, at output witness 0.
/-- info: (4, 4) -/
#guard_msgs in
#eval recorded (deepStages.programAlong () (deepPath 4)).program 0

end Interaction.Core.MeasuredPathBudgetsTests

run_cmd do
  for decl in [``Interaction.Core.KnowledgeStateFunction.MeasuredStages.programAlong_budget_le,
      ``Interaction.Core.KnowledgeStateFunction.MeasuredStages.programAlong_costAtMost_nsmul,
      ``Interaction.Core.KnowledgeStateFunction.MeasuredStages.run_programAlong,
      ``Interaction.Core.MeasuredPathBudgetsTests.no_global_budget_of_stage_bound,
      ``Interaction.Core.MeasuredPathBudgetsTests.no_global_cost_bound_of_stage_bound] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
