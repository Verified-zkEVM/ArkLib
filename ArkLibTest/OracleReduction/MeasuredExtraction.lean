/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.OracleReduction.Security.Resources
import ArkLib.Interaction.Oracle.Security.KnowledgeResources.Composition
import ArkLibTest.Data.OracleComp.AddProgram

/-!
# Measured extraction charges only declared instructions

An extractor that searches all `2 ^ m` candidate witnesses in pure Lean code requests no
instruction. Its measured program therefore meets the zero budget, so the resource contract alone
gives no running-time bound.

An interaction-layer round-by-round extractor is measured stage by stage with the same program
type: one program with a charged addition realizes the stage map of a one-round extractor for every
message, although the later witness type depends on the message.
-/

open OracleComp OracleSpec ProtocolSpec AddProgramTest

section Search

variable {WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Return the first of the `2 ^ m` candidate witnesses accepted by `rel`. -/
def searchExtractor (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    Extractor.Straightline []ₒ ℕ (Fin (2 ^ m)) WitOut pSpec :=
  fun stmtIn _ _ _ _ ↦ OptionT.mk (pure ((List.finRange (2 ^ m)).find? (rel stmtIn)))

/-- The search as a program with no instructions. -/
def searchProgram (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    Extractor.Straightline.MeasuredProgram []ₒ ℕ (Fin (2 ^ m)) WitOut pSpec (Unit → Nat) :=
  MeasuredProgram.ofFun fun input ↦ (List.finRange (2 ^ m)).find? (rel input.1)

/-- The search extractor is the execution of its program. -/
theorem searchProgram_realizesExtractor (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    (searchProgram m rel (WitOut := WitOut) (pSpec := pSpec)).RealizesExtractor
      (searchExtractor m rel) :=
  fun _ _ _ _ _ ↦ rfl

/-- The search requests no instruction, so it costs zero. -/
theorem searchProgram_costAtMost_zero (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    (searchProgram m rel (WitOut := WitOut) (pSpec := pSpec)).CostAtMost 0 :=
  MeasuredProgram.costAtMost_ofFun _

-- Any game bound for exhaustive search is a resource-certified bound at budget zero.
example (m : ℕ) [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) {StmtOut : Type}
    (relIn : Set (ℕ × Fin (2 ^ m))) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier []ₒ ℕ StmtOut pSpec) (rel : ℕ → Fin (2 ^ m) → Bool)
    (knowledgeError : NNReal)
    (h : verifier.knowledgeSoundnessWith init impl relIn relOut (searchExtractor m rel)
      knowledgeError) :
    verifier.knowledgeSoundnessWithResources init impl relIn relOut (searchExtractor m rel)
      knowledgeError (searchProgram m rel) 0 :=
  ⟨h, searchProgram_realizesExtractor m rel, searchProgram_costAtMost_zero m rel⟩

end Search

namespace MeasuredExtractionTest

open Interaction.Oracle Interaction.Oracle.Security

/-- A one-round interaction-layer tree: the prover sends a public message in `Fin 8`. -/
abbrev oneRound : TypeTree := .public (Fin 8) fun _ ↦ .done

/-- Input witnesses are natural numbers. -/
def inputState : KnowledgeState := ⟨ℕ, fun _ ↦ True⟩

/-- After message `m`, a witness is a number below `m + 1`, so the carrier depends on `m`. -/
def afterState (message : Fin 8) : KnowledgeState := ⟨Fin (message.val + 1), fun _ ↦ True⟩

/-- Backward extraction adds the actual message to the later witness. -/
def addExtractor : RoundExtractor oneRound inputState :=
  fun message ↦ ⟨afterState message, fun w ↦ w.val + message.val, PUnit.unit⟩

/-- The single stage of the interaction-layer extractor, with budget one. -/
def addStages : addExtractor.MeasuredStages ℕ :=
  ⟨⟨addProgram (fun x => (x.2.val, x.1.val)), 1, addProgram_realizes _,
    addProgram_costAtMost_one _⟩, fun _ ↦ PUnit.unit⟩

/-- Path composition retains the witness carrier selected by the actual message. -/
example (message : Fin 8) (witness : Fin (message.val + 1)) :
    (addStages.programAlong ⟨message, PUnit.unit⟩).program.run witness =
      witness.val + message.val :=
  addStages.run_programAlong ⟨message, PUnit.unit⟩ witness

example (message : Fin 8) : (addStages.programAlong ⟨message, PUnit.unit⟩).budget = 1 := rfl

/-- A completed tree with no witnesses still has its empty, zero-budget extraction program. -/
example :
    let state : KnowledgeState := ⟨Empty, fun _ => False⟩
    let extractor : RoundExtractor .done state := PUnit.unit
    let stages : extractor.MeasuredStages Nat := PUnit.unit
    (stages.programAlong PUnit.unit).budget = 0 := rfl

end MeasuredExtractionTest

/-- The done-tree certificate fixes standard natural-number profiles without model instances. -/
example (Kind : Type) [Finite Kind] : Type 1 :=
  Interaction.Oracle.Security.MeasuredKnowledgeCertificate Kind .done PUnit.unit
    MeasuredExtractionTest.inputState

namespace FixedCountArithmeticTest

open Interaction.Oracle Interaction.Oracle.Security

/-- Standard count stages fill the public certificate without supplying a cost model. -/
example {tree : TypeTree} {roles : tree.RoleDecoration} {state : KnowledgeState}
    (certificate : KnowledgeCertificate tree roles state)
    (stages : certificate.extractor.MeasuredStages (Unit → Nat)) :
    MeasuredKnowledgeCertificate Unit tree roles state :=
  { certificate with stages := stages }

/-- A max-additive monoid on Nat combines positive charges without counting them. -/
@[instance_reducible] private def maxNatAddCommMonoid : AddCommMonoid Nat where
  add := max
  zero := 0
  add_assoc := Nat.max_assoc
  zero_add := Nat.zero_max
  add_zero := Nat.max_zero
  add_comm := Nat.max_comm
  nsmul n a := if n = 0 then 0 else a
  nsmul_zero _ := rfl
  nsmul_succ n a := by
    change (if n + 1 = 0 then 0 else a) = max (if n = 0 then 0 else a) a
    by_cases h : n = 0 <;> simp only [h, Nat.add_one_ne_zero] <;>
      first | exact (Nat.zero_max _).symm | exact (Nat.max_self _).symm

section MaxWeights

local instance : AddCommMonoid Nat := maxNatAddCommMonoid

/-- A caller's max-additive profile is weighted accounting, not the fixed count certificate. -/
example {tree : TypeTree} {roles : tree.RoleDecoration} {state : KnowledgeState}
    (certificate : KnowledgeCertificate tree roles state)
    (_stages : certificate.extractor.MeasuredStages (Unit → Nat)) : True := by
  fail_if_success
    have accepted : MeasuredKnowledgeCertificate Unit tree roles state :=
      { certificate with stages := _stages }
  trivial

end MaxWeights

section ReversedWeights

local instance : Preorder (Unit → Nat) := inferInstanceAs (Preorder (OrderDual (Unit → Nat)))

/-- A caller's reversed order also cannot replace the public certificate's standard order. -/
example {tree : TypeTree} {roles : tree.RoleDecoration} {state : KnowledgeState}
    (certificate : KnowledgeCertificate tree roles state)
    (_stages : certificate.extractor.MeasuredStages (Unit → Nat)) : True := by
  fail_if_success
    have accepted : MeasuredKnowledgeCertificate Unit tree roles state :=
      { certificate with stages := _stages }
  trivial

end ReversedWeights

end FixedCountArithmeticTest

/-- Infinite coordinate families cannot instantiate a public operation-count certificate. -/
example : True := by
  fail_if_success
    have certificateType :=
      Interaction.Oracle.Security.MeasuredKnowledgeCertificate Nat .done PUnit.unit
        MeasuredExtractionTest.inputState
  trivial

namespace ZeroStageAccountingTest

open Interaction.Oracle Interaction.Oracle.Security

/-- Putting a map in the uncharged pure fragment gives it a zero-instruction stage program. -/
private def zeroStages : {tree : TypeTree} → {state : KnowledgeState} →
    (extractor : RoundExtractor tree state) → extractor.MeasuredStages (Unit → Nat)
  | .done, _, _ => PUnit.unit
  | .public _ _, _, extractor =>
      ⟨BudgetedProgram.ofFun _, fun move => zeroStages (extractor move).2.2⟩
  | .oracle _ _, _, extractor =>
      ⟨BudgetedProgram.ofFun _, fun message => zeroStages (extractor message).2.2⟩

private theorem zeroStages_budgetAtMost : {tree : TypeTree} → {state : KnowledgeState} →
    (extractor : RoundExtractor tree state) → (zeroStages extractor).BudgetAtMost 0
  | .done, _, _ => trivial
  | .public _ _, _, extractor => ⟨le_rfl, fun move => zeroStages_budgetAtMost (extractor move).2.2⟩
  | .oracle _ _, _, extractor =>
      ⟨le_rfl, fun message => zeroStages_budgetAtMost (extractor message).2.2⟩

/-- Every native certificate admits a zero-count certificate without bounding its pure work. -/
example {tree : TypeTree} {roles : tree.RoleDecoration} {state : KnowledgeState}
    (certificate : KnowledgeCertificate tree roles state) :
    ∃ measured : MeasuredKnowledgeCertificate Unit tree roles state,
      measured.extractor = certificate.extractor ∧
      ∀ path, (measured.stages.programAlong path).program.CostAtMost 0 :=
  ⟨{ certificate with stages := zeroStages certificate.extractor }, rfl, fun path => by
    simpa using (zeroStages certificate.extractor).programAlong_costAtMost
      (zeroStages_budgetAtMost certificate.extractor) path⟩

end ZeroStageAccountingTest
