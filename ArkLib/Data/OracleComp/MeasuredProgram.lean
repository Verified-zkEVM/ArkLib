/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.OracleComp.DeterminedCost

/-!
# Measured programs

A measured program computes a function by running an instruction program on a view of its input.
Deterministic handlers answer the instructions, and each instruction carries a charge in an
additive cost type, such as a vector of operation counts. `MeasuredProgram.Realizes` states that a
function is the handlers' execution of the program, and `MeasuredProgram.CostAtMost` bounds the
cost of every execution path, on every view, by a budget. The budget holds for every view, not
only for views arising from the inputs of interest. `BudgetedProgram f` bundles a program that
realizes `f` with a budget that bounds its cost.

The program does not depend on any security game. A game whose extractor or witness map has a
given input and result type states its resource contract by naming that map and a measured
program for it.

Only the declared instructions are charged. Computing the view, the size or encoding of the view,
evaluating any handler, pure Lean code between instructions, and the bit complexity of values are
not. The instance also chooses the instructions, their charges, and the cost order. A program that
computes its result without instructions, for example by exhaustive search, costs zero. In
particular, every function has a budgeted program with budget zero (`BudgetedProgram.ofFun`), so
an existential statement over measured programs adds nothing; only a named program with a stated
instruction set is evidence. The bound is an operation count relative to that instruction set,
not a running-time bound, and each instance must state what its view and handlers leave uncharged.

## Scope

Handlers are deterministic: each returns its response in `Id`. The budget is one value for every
view; a budget that may be any function of the view could restate the program's own cost on that
view. The cost bound is VCVio's `WorstCaseCostBound` for every view; `CostAtMost.runAdd_le`
transfers it to the handlers' execution, which `Realizes` identifies with the function.
-/

@[expose] public section

open OracleSpec

namespace OracleComp

/-- A charged instruction program computing a function from `Input` to `Result`.

The input is reduced to a `View`, which the instruction program reads through handlers whose
response types may depend on the view. Computing the view and evaluating the handlers are outside
the charged program. -/
structure MeasuredProgram (Input Result ω : Type) where
  /-- The data read by the instruction program. -/
  View : Type
  /-- The uncharged reduction of the input to the program's view. -/
  view : Input → View
  /-- The instruction names. -/
  Op : Type
  /-- The instruction set for one view, whose responses may certify the view's data. -/
  spec : View → OracleSpec.{0, 0} Op
  /-- The charged program. -/
  program : (v : View) → OracleComp (spec v) Result
  /-- The uncharged deterministic instruction handlers. -/
  answer : (v : View) → QueryImpl (spec v) Id
  /-- The charge for one instruction. -/
  cost : Op → ω

namespace MeasuredProgram

variable {Input Result ω : Type} (M : MeasuredProgram Input Result ω)

/-- The handlers' execution of the program on the view of `input`. -/
def run (input : Input) : Result :=
  (simulateQ (M.answer (M.view input)) (M.program (M.view input))).run

/-- The function `f` is the handlers' execution of the program on the view of each input. -/
def Realizes (f : Input → Result) : Prop :=
  ∀ input, f input = M.run input

/-- On every view, every execution path of the program costs at most `budget`. Paths are taken
over all responses permitted by the instruction set. -/
def CostAtMost [AddCommMonoid ω] [Preorder ω] (budget : ω) : Prop :=
  ∀ v, WorstCaseCostBound (M.program v) ⟨M.cost⟩ budget

variable {M} in
/-- A cost bound remains valid for any larger budget. -/
theorem CostAtMost.mono [AddCommMonoid ω] [Preorder ω] {budget budget' : ω}
    (h : M.CostAtMost budget) (hle : budget ≤ budget') : M.CostAtMost budget' :=
  fun v z hz ↦ (h v z hz).trans hle

variable {M} in
/-- The handlers' execution, which `Realizes` identifies with the realized function, records a
cost within the budget. -/
theorem CostAtMost.runAdd_le [AddCommMonoid ω] [Preorder ω] {budget : ω}
    (h : M.CostAtMost budget) (v : M.View) :
    (simulateQ ((M.answer v).withAddCost M.cost) (M.program v)).runAdd.2 ≤ budget :=
  ArkLib.DeterminedCost.worstCaseCostBound_runAdd_withAddCost_le (h v) (M.answer v)

/-- If the handlers' answers are the only responses, the cost recorded by running the handlers
bounds every execution path. -/
theorem costAtMost_of_forall_eq_answer [AddCommMonoid ω] [Preorder ω] (budget : ω)
    (hanswer : ∀ v t (u : (M.spec v).Range t), u = M.answer v t)
    (hcost : ∀ v, (simulateQ ((M.answer v).withAddCost M.cost) (M.program v)).runAdd.2 ≤
      budget) :
    M.CostAtMost budget :=
  fun v ↦ (ArkLib.DeterminedCost.worstCaseCostBound_iff_of_forall_eq_answer
    (M.answer v) (hanswer v) (M.program v) ⟨M.cost⟩ budget).mpr (hcost v)

/-- The program with no instructions that computes `f` on its whole input. -/
def ofFun (f : Input → Result) : MeasuredProgram Input Result ω where
  View := Input
  view := id
  Op := PEmpty
  spec _ := []ₒ
  program v := pure (f v)
  answer _ := fun t ↦ t.elim
  cost := fun t ↦ t.elim

/-- The program with no instructions realizes the function it computes. -/
theorem realizes_ofFun (f : Input → Result) : (ofFun f (ω := ω)).Realizes f :=
  fun _ ↦ rfl

/-- A program with no instructions costs zero. -/
theorem costAtMost_ofFun [AddCommMonoid ω] [Preorder ω] (f : Input → Result) :
    (ofFun f (ω := ω)).CostAtMost 0 :=
  fun _ ↦ (worstCaseCostBound_pure _ _ _).mpr le_rfl

end MeasuredProgram

/-- A named measured program for `f` and a budget: the program realizes `f`, and every execution
path of the program, on every view, costs at most the budget.
Native stages form a tree-indexed family of data, so each node keeps its program, budget and proofs
in one value; `Verifier.knowledgeSoundnessWithResources` instead keeps the program and budget as
parameters for budget monotonicity and realizes the extractor's monadic run. -/
structure BudgetedProgram {Input Result : Type} (f : Input → Result) (ω : Type) [AddCommMonoid ω]
    [Preorder ω] where
  /-- The measured program executed by `f`. -/
  program : MeasuredProgram Input Result ω
  /-- The bound on the program's declared instruction charges. -/
  budget : ω
  /-- The function is the handlers' execution of the program. -/
  realizes : program.Realizes f
  /-- Every execution path of the program costs at most the budget. -/
  costAtMost : program.CostAtMost budget

/-- Every function has a budgeted program with budget zero, which requests no instruction. -/
def BudgetedProgram.ofFun {Input Result ω : Type} [AddCommMonoid ω] [Preorder ω]
    (f : Input → Result) : BudgetedProgram f ω :=
  ⟨MeasuredProgram.ofFun f, 0, MeasuredProgram.realizes_ofFun f,
    MeasuredProgram.costAtMost_ofFun f⟩

end OracleComp
