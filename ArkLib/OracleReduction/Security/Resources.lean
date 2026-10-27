/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.Data.OracleComp.DeterminedCost

/-!
# Knowledge soundness with measured extraction

`knowledgeSoundnessWith` bounds the error of one named extractor but says nothing about its cost.
A measured program supplies that cost for a deterministic extractor. It splits extraction into a
view of the extractor's inputs and an instruction program run on that view by deterministic
handlers. Each instruction carries a charge in an additive cost type, such as a vector of operation
counts. The resource contract adds two claims to the game: the extractor is the handlers' execution
of the program on its view, and every execution path of the program costs at most a budget. The
budget holds for every view, not only for views arising from accepting runs.

The contract certifies the declared instructions only. Computing the view, the size or encoding
of the view, evaluating any handler, pure Lean code between instructions, and the bit complexity
of values are not charged. The instance also chooses the instructions, their charges, and the
cost order. A program that computes its result without instructions, for example by exhaustive
search, costs zero. In particular, every deterministic extractor that makes no `oSpec` query has
a measured program with budget zero, so an existential statement over measured programs adds
nothing to `knowledgeSoundnessWith`. Only a named program with a stated instruction set is
evidence. The contract is an operation count relative to that instruction set, not a running-time
bound; each instance must state what its view and handlers leave uncharged.

## Scope

Handlers are deterministic and the extractor's run is `pure`, which covers extractors that do
not query `oSpec`, such as FRI's. The budget is one value for every view at the given parameters;
a budget that varied with the view could restate the program's own cost. The cost bound is
VCVio's `WorstCaseCostBound` for every view; `CostAtMost.runAdd_le` transfers it to the handlers'
execution, which `Realizes` identifies with the extractor.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

namespace Extractor.Straightline

/-- A charged instruction program for a deterministic straightline extractor.

The extractor's inputs are reduced to a `View`, which the instruction program reads through
handlers whose response types may depend on the view. Computing the view and evaluating the
handlers are outside the charged program. -/
structure MeasuredProgram (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type)
    (pSpec : ProtocolSpec n) (ω : Type) where
  /-- The data read by the instruction program. -/
  View : Type
  /-- The uncharged reduction of the extractor's inputs to the program's view. -/
  view : StmtIn → WitOut → FullTranscript pSpec → QueryLog oSpec → QueryLog oSpec → View
  /-- The instruction names. -/
  Op : Type
  /-- The instruction set for one view, whose responses may certify the view's data. -/
  spec : View → OracleSpec.{0, 0} Op
  /-- The charged extraction program. -/
  program : (v : View) → OracleComp (spec v) (Option WitIn)
  /-- The uncharged deterministic instruction handlers. -/
  answer : (v : View) → QueryImpl (spec v) Id
  /-- The charge for one instruction. -/
  cost : Op → ω

namespace MeasuredProgram

variable {ω : Type} (M : MeasuredProgram oSpec StmtIn WitIn WitOut pSpec ω)

/-- The extractor returns the handlers' execution of the program on its view, without querying
`oSpec`. -/
def Realizes (extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) : Prop :=
  ∀ stmtIn witOut transcript proveQueryLog verifyQueryLog,
    let v := M.view stmtIn witOut transcript proveQueryLog verifyQueryLog
    (extractor stmtIn witOut transcript proveQueryLog verifyQueryLog).run =
      pure (simulateQ (M.answer v) (M.program v))

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
/-- The handlers' execution, which `Realizes` identifies with the extractor, records a cost
within the budget. -/
theorem CostAtMost.runAdd_le [AddCommMonoid ω] [Preorder ω] {budget : ω}
    (h : M.CostAtMost budget) (v : M.View) :
    (simulateQ ((M.answer v).withAddCost M.cost) (M.program v)).runAdd.2 ≤ budget :=
  WorstCaseCostBound.runAdd_withAddCost_le (h v) (M.answer v)

/-- If the handlers' answers are the only responses, the cost recorded by running the handlers
bounds every execution path. -/
theorem costAtMost_of_forall_eq_answer [AddCommMonoid ω] [Preorder ω] (budget : ω)
    (hanswer : ∀ v t (u : (M.spec v).Range t), u = M.answer v t)
    (hcost : ∀ v, (simulateQ ((M.answer v).withAddCost M.cost) (M.program v)).runAdd.2 ≤
      budget) :
    M.CostAtMost budget :=
  fun v ↦ (worstCaseCostBound_iff_of_forall_eq_answer (M.answer v) (hanswer v) (M.program v)
    ⟨M.cost⟩ budget).mpr (hcost v)

end MeasuredProgram

end Extractor.Straightline

variable [∀ i, SampleableType (pSpec.Challenge i)]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

/-- Knowledge soundness of a named extractor together with a cost bound for a measured program
that it executes. The budget bounds the program's declared instruction charges only; see the
module documentation for what is uncharged. -/
def knowledgeSoundnessWithResources {ω : Type} [AddCommMonoid ω] [Preorder ω]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    (knowledgeError : ℝ≥0)
    (program : Extractor.Straightline.MeasuredProgram oSpec StmtIn WitIn WitOut pSpec ω)
    (budget : ω) : Prop :=
  verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError ∧
    program.Realizes extractor ∧ program.CostAtMost budget

namespace knowledgeSoundnessWithResources

variable {ω : Type} [AddCommMonoid ω] [Preorder ω]
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} {knowledgeError : ℝ≥0}
  {program : Extractor.Straightline.MeasuredProgram oSpec StmtIn WitIn WitOut pSpec ω}
  {budget : ω}

/-- Forget the measured program, keeping the game for the same named extractor. -/
theorem knowledgeSoundnessWith
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError :=
  h.1

/-- Forget the measured program and the extractor's identity. -/
theorem knowledgeSoundness
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError :=
  knowledgeSoundness_of_with init impl h.1

/-- A resource certificate remains valid for any larger budget. -/
theorem mono
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) {budget' : ω} (hle : budget ≤ budget') :
    verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget' :=
  ⟨h.1, h.2.1, h.2.2.mono hle⟩

end knowledgeSoundnessWithResources

end Verifier

namespace OracleVerifier

variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)]

/-- Measured knowledge soundness of an oracle verifier is that of its non-oracle verifier. -/
def knowledgeSoundnessWithResources {ω : Type} [AddCommMonoid ω] [Preorder ω]
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (extractor : Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec)
    (knowledgeError : ℝ≥0)
    (program : Extractor.Straightline.MeasuredProgram oSpec (StmtIn × ∀ i, OStmtIn i)
      WitIn WitOut pSpec ω)
    (budget : ω) : Prop :=
  verifier.toVerifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
    knowledgeError program budget

namespace knowledgeSoundnessWithResources

variable {ω : Type} [AddCommMonoid ω] [Preorder ω]
  {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
  {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
  {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
  {extractor : Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec}
  {knowledgeError : ℝ≥0}
  {program : Extractor.Straightline.MeasuredProgram oSpec (StmtIn × ∀ i, OStmtIn i)
    WitIn WitOut pSpec ω}
  {budget : ω}

/-- Forget the measured program, keeping the game for the same named extractor. -/
theorem knowledgeSoundnessWith
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError :=
  h.1

/-- Forget the measured program and the extractor's identity. -/
theorem knowledgeSoundness
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError :=
  OracleVerifier.knowledgeSoundness_of_with init impl h.1

/-- A resource certificate remains valid for any larger budget. -/
theorem mono
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) {budget' : ω} (hle : budget ≤ budget') :
    verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget' :=
  Verifier.knowledgeSoundnessWithResources.mono init impl h hle

end knowledgeSoundnessWithResources

end OracleVerifier
