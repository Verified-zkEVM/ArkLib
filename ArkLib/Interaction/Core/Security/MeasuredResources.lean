/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.KnowledgeComposition
public import VCVio.OracleComp.QueryTracking.MeasuredProgram.Composition

/-!
# Knowledge state functions with measured extraction

A knowledge state function extracts backwards in three kinds of stage: the leaf map turns an
output witness into a terminal witness, the step map at an interaction node turns a move and the
witness after it into the witness before it (`KnowledgeStateFunction.stageMap`), and the root map
returns an input witness. `KnowledgeStateFunction.MeasuredStages` names a budgeted instruction
program (`OracleComp.BudgetedProgram`) for every stage, indexed by the statement and the full
transcript prefix. `MeasuredStages.programAlong` composes these programs along a completed
transcript; it realizes `KnowledgeStateFunction.extractAlong` on output witnesses at that
transcript, whose type depends on it, and its budget is the sum of the stage budgets along that
transcript.

`MeasuredStages.BudgetAtMost` bounds the root, step and leaf budgets separately. The composed
budget is then at most the leaf bound, plus the step bound once for each move of the transcript,
plus the root bound (`MeasuredStages.programAlong_budget_le`). With zero root and leaf bounds this
is the transcript length times the step bound (`MeasuredStages.programAlong_budget_le_nsmul`).

## Scope

Each budget bounds the declared instructions of one stage under the accounting of
`OracleComp.MeasuredProgram`, which lists what is uncharged. Every map has a budgeted program with
budget zero (`MeasuredStages.zero`), so only a named program with a stated instruction set is
evidence. In addition:

* Stages are indexed by the statement and the actual earlier moves, including oracle payloads, so
  a stage program, view and handlers may compute anything from them without charge, and stages at
  different prefixes may carry different budgets. A common bound is the hypothesis
  `MeasuredStages.BudgetAtMost`.
* Witness carriers are chosen with the state function, so stage budgets bound extraction only
  together with a separately stated cost of identifying carriers with a game's witnesses.
* Complete execution of the stage composition, the size of intermediate witnesses, and the
  computation of the knowledge states are not bounded.

The budget along a transcript depends on the transcript, not only on the protocol shape: the
number of moves of a transcript through an unbounded protocol is unbounded, so a stage bound alone
gives no global bound.

`MeasuredKnowledgeStateFunction` fixes natural-number count profiles over a finite resource-kind
type, with pointwise addition and order. An empty `Kind` records no resources, and a scalar count
uses `Unit → Nat`.
-/

@[expose] public section

universe uS

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp

variable {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly}

namespace KnowledgeStateFunction

variable {s : FreeM P PUnit.{1}} {S : Type uS} {Win : S → Type} {W : S → PathAlong l s → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
  (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput)

/-- The input of the step at an interaction node: a move and a witness of the state after it. -/
def StageInput (stmt : S) {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp) : Type :=
  (x : Move l a) × F.Witness stmt (sp.comp (.down (l.toFunB a x) (.root _)))
    (PrefixMoves.snoc l sp history x)

/-- The backward witness map at an interaction node. -/
def stageMap (stmt : S) {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp)
    (input : F.StageInput stmt sp history) : F.Witness stmt sp history :=
  F.extractStep stmt sp history input.1 input.2

/-- Backward extraction at an interaction node applies the stage map to the witness extracted
from the rest of the transcript. -/
theorem extractFrom_eq_stageMap (stmt : S) {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp)
    (x : Move l a) (tr : PathAlong l (next (l.toFunB a x)))
    (w : W stmt (PrefixMoves.completeWith l sp history (t := .liftBind a next) ⟨x, tr⟩)) :
    F.extractFrom stmt sp history ⟨x, tr⟩ w =
      F.stageMap stmt sp history
        ⟨x, F.extractFrom stmt _ (PrefixMoves.snoc l sp history x) tr w⟩ := rfl

/-- A budgeted program for every extraction stage: the root map, the step map at every
interaction node and the leaf map, each indexed by the statement and the full prefix. -/
structure MeasuredStages (ω : Type) [AddCommMonoid ω] [Preorder ω] where
  /-- The input-witness map. -/
  root : ∀ stmt, BudgetedProgram (F.extractRoot stmt) ω
  /-- The step map at every interaction node. -/
  step : ∀ stmt {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp),
    BudgetedProgram (F.stageMap stmt sp history) ω
  /-- The terminal-witness map at every completed prefix, from output witnesses at its
  transcript. -/
  leaf : ∀ stmt (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PrefixMoves l sp),
    BudgetedProgram (F.extractLeaf stmt sp history) ω

namespace MeasuredStages

variable {F} {ω : Type}

section bounds

variable [AddCommMonoid ω] [Preorder ω]

/-- The root, step and leaf budgets are at most the given bounds, at every statement and prefix. -/
structure BudgetAtMost (stages : MeasuredStages F ω) (rootBound stepBound leafBound : ω) :
    Prop where
  /-- The root budget is bounded. -/
  root : ∀ stmt, (stages.root stmt).budget ≤ rootBound
  /-- Every step budget is bounded. -/
  step : ∀ stmt {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp),
    (stages.step stmt sp history).budget ≤ stepBound
  /-- Every leaf budget is bounded. -/
  leaf : ∀ stmt (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PrefixMoves l sp),
    (stages.leaf stmt sp history).budget ≤ leafBound

variable (F) in
/-- The stages that request no instruction, for every state function. -/
def zero : MeasuredStages F ω where
  root _ := BudgetedProgram.ofFun _
  step _ _ _ _ _ := BudgetedProgram.ofFun _
  leaf _ _ _ := BudgetedProgram.ofFun _

variable (F) in
/-- The stages that request no instruction have zero budgets. -/
theorem zero_budgetAtMost : (zero F (ω := ω)).BudgetAtMost 0 0 0 where
  root _ := le_rfl
  step _ _ _ _ _ := le_rfl
  leaf _ _ _ := le_rfl

end bounds

section compose

variable [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]

/-- The stage programs composed along the rest of a transcript from a prefix: the leaf program,
then the step program at every move, from the last move to the first. -/
def programFrom (stages : MeasuredStages F ω) (stmt : S) :
    {t : FreeM P PUnit.{1}} → (sp : Cursor.Spine s t) → (history : PrefixMoves l sp) →
    (tr : PathAlong l t) → BudgetedProgram (F.extractFrom stmt sp history tr) ω
  | .pure _, sp, history, _ => stages.leaf stmt sp history
  | .liftBind _ _, sp, history, ⟨x, tr⟩ =>
    ((stages.step stmt sp history).contramap
      (fun w : F.Witness stmt _ (PrefixMoves.snoc l sp history x) => (⟨x, w⟩ : F.StageInput stmt _
        _))).comp
      (programFrom stages stmt _ (PrefixMoves.snoc l sp history x) tr)

/-- The stage programs composed along a completed transcript, ending with the root program. Its
input is an output witness at that transcript. -/
def programAlong (stages : MeasuredStages F ω) (stmt : S) (tr : PathAlong l s) :
    BudgetedProgram (F.extractAlong stmt tr) ω :=
  ((stages.root stmt).comp (stages.programFrom stmt (.root s) ⟨⟩ tr)).contramap
    (cast (congrArg (W stmt) (PrefixMoves.completeWith_root l tr).symm))

/-- The composed program returns the extracted input witness. -/
theorem run_programAlong (stages : MeasuredStages F ω) (stmt : S) (tr : PathAlong l s)
    (w : W stmt tr) :
    (stages.programAlong stmt tr).program.run w = F.extractAlong stmt tr w :=
  ((stages.programAlong stmt tr).realizes w).symm

/-- At a completed prefix, the composed budget is the leaf budget. -/
@[simp] theorem programFrom_budget_pure (stages : MeasuredStages F ω) (stmt : S)
    (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PrefixMoves l sp)
    (tr : PathAlong l (FreeM.pure (P := P) PUnit.unit)) :
    (stages.programFrom stmt sp history tr).budget = (stages.leaf stmt sp history).budget := rfl

/-- At an interaction node, the composed budget is the budget of the rest plus the step budget. -/
theorem programFrom_budget_liftBind (stages : MeasuredStages F ω) (stmt : S) {a : P.A}
    {next : P.B a → FreeM P PUnit.{1}} (sp : Cursor.Spine s (.liftBind a next))
    (history : PrefixMoves l sp) (x : Move l a) (tr : PathAlong l (next (l.toFunB a x))) :
    (stages.programFrom stmt sp history ⟨x, tr⟩).budget =
      (stages.programFrom stmt _ (PrefixMoves.snoc l sp history x) tr).budget +
        (stages.step stmt sp history).budget := rfl

/-- The budget along a transcript is the budget from the root plus the root budget. -/
theorem programAlong_budget (stages : MeasuredStages F ω) (stmt : S) (tr : PathAlong l s) :
    (stages.programAlong stmt tr).budget =
      (stages.programFrom stmt (.root s) ⟨⟩ tr).budget + (stages.root stmt).budget := rfl

/-- Under stage bounds, the budget from a prefix is at most the leaf bound plus the step bound for
each remaining move. -/
theorem programFrom_budget_le (stages : MeasuredStages F ω) {rootBound stepBound leafBound : ω}
    (h : stages.BudgetAtMost rootBound stepBound leafBound) (stmt : S) :
    {t : FreeM P PUnit.{1}} → (sp : Cursor.Spine s t) → (history : PrefixMoves l sp) →
    (tr : PathAlong l t) →
    (stages.programFrom stmt sp history tr).budget ≤
      leafBound + (completeSpine l tr).length • stepBound
  | .pure _, sp, history, _ => by
    simpa [completeSpine] using h.leaf stmt sp history
  | .liftBind _ _, sp, history, ⟨x, tr⟩ => by
    rw [programFrom_budget_liftBind, length_completeSpine_liftBind, succ_nsmul, ← add_assoc]
    exact add_le_add (programFrom_budget_le stages h stmt _ _ tr) (h.step stmt sp history)

/-- Under stage bounds, the budget along a transcript is at most the leaf bound, plus the step
bound for each move, plus the root bound. -/
theorem programAlong_budget_le (stages : MeasuredStages F ω) {rootBound stepBound leafBound : ω}
    (h : stages.BudgetAtMost rootBound stepBound leafBound) (stmt : S) (tr : PathAlong l s) :
    (stages.programAlong stmt tr).budget ≤
      leafBound + (completeSpine l tr).length • stepBound + rootBound :=
  add_le_add (programFrom_budget_le stages h stmt (.root s) ⟨⟩ tr) (h.root stmt)

/-- With zero root and leaf bounds, the budget along a transcript is at most its number of moves
times the step bound. -/
theorem programAlong_budget_le_nsmul (stages : MeasuredStages F ω) {stepBound : ω}
    (h : stages.BudgetAtMost 0 stepBound 0) (stmt : S) (tr : PathAlong l s) :
    (stages.programAlong stmt tr).budget ≤ (completeSpine l tr).length • stepBound := by
  simpa using programAlong_budget_le stages h stmt tr

/-- Every execution path of the composed program satisfies the stage-bound budget. -/
theorem programAlong_costAtMost (stages : MeasuredStages F ω) {rootBound stepBound leafBound : ω}
    (h : stages.BudgetAtMost rootBound stepBound leafBound) (stmt : S) (tr : PathAlong l s) :
    (stages.programAlong stmt tr).program.CostAtMost
      (leafBound + (completeSpine l tr).length • stepBound + rootBound) :=
  (stages.programAlong stmt tr).costAtMost.mono (programAlong_budget_le stages h stmt tr)

/-- With zero root and leaf bounds, every execution path of the composed program costs at most the
number of moves times the step bound. -/
theorem programAlong_costAtMost_nsmul (stages : MeasuredStages F ω) {stepBound : ω}
    (h : stages.BudgetAtMost 0 stepBound 0) (stmt : S) (tr : PathAlong l s) :
    (stages.programAlong stmt tr).program.CostAtMost ((completeSpine l tr).length • stepBound) :=
  (stages.programAlong stmt tr).costAtMost.mono (programAlong_budget_le_nsmul stages h stmt tr)

end compose

end MeasuredStages

end KnowledgeStateFunction

/-- A knowledge state function with a budgeted program for every extraction stage, charging
natural-number counts indexed by the finite type `Kind`. -/
structure MeasuredKnowledgeStateFunction (Kind : Type) [Finite Kind] (l : PFunctor.Lens P rolePoly)
    (s : FreeM P PUnit.{1}) (S : Type uS) (W : S → PathAlong l s → Type) (Win : S → Type)
    (admissible : S → Prop) (relIn : (stmt : S) → Win stmt → Prop)
    (validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop)
    extends KnowledgeStateFunction l s S W Win admissible relIn validOutput where
  /-- A measured program and budget for each extraction stage. -/
  stages : toKnowledgeStateFunction.MeasuredStages (Kind → Nat)

end Interaction.Core
