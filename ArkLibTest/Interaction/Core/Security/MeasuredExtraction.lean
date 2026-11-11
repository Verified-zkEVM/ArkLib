/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Quang Dao
-/
import ArkLib.Interaction.Core.Security.MeasuredResources
import ArkLibTest.Data.OracleComp.AddProgram

/-!
# Measured extraction stages of an interaction-layer state function

A state function on a one-message protocol is measured stage by stage: one program with a charged
addition realizes its step map for every message, although the witness after the message has a
carrier that depends on the message, and the composed program runs on output witnesses in that
carrier. Measured state functions fix natural-number count profiles over a finite kind type, and
every state function has zero-instruction stages.
-/

open PFunctor PFunctor.FreeM Interaction.Core OracleComp AddProgramTest

-- Disposition IDs refer to docs/design/interaction-layer/knowledge-composition-disposition.md.

namespace Interaction.Core.MeasuredExtractionTests

/-- One public message in `Fin 8`. -/
abbrev oneRound : Protocol.{0} := .liftBind (.message (Fin 8)) fun _ => .pure ⟨⟩

/-- Output witnesses after message `m` are numbers below `m + 1`. -/
abbrev OutWitness (tr : PathAlong plainSig oneRound) : Type := Fin (tr.1.val + 1)

/-- Input witnesses are natural numbers; after message `m`, a witness is a number below `m + 1`,
the output witness carrier. The leaf map is the identity, and the step map adds the message. -/
def addState : KnowledgeStateFunction plainSig oneRound Unit (fun _ => OutWitness) (fun _ => Nat)
    (fun _ => True)
    (fun _ _ => True) (fun _ _ _ => True) where
  Witness _ {_} sp history := match sp, history with
    | .root _, _ => Nat
    | .down _ _, history => Fin (history.1.1.val + 1)
  toFun _ {_} _ _ _ := True
  extractRoot _ w := w
  extractStep _ {_ _} sp _ x w := by
    cases sp with
    | root => exact w.val + x.val
    | down _ tail => cases tail
  extractLeaf _ sp history w := by
    cases sp with
    | down _ tail =>
      cases tail
      exact w
  root _ _ _ _ := trivial
  send _ _ _ _ _ _ _ := trivial
  leaf _ _ _ _ _ := trivial

/-- The single step program requests one addition; the root and leaf maps are uncharged. -/
def addStages : addState.MeasuredStages Nat where
  root _ := BudgetedProgram.ofFun _
  step _ _ _ sp history := by
    cases sp with
    | root =>
      exact ⟨addProgram (fun x : addState.StageInput () (.root _) history => (x.2.val, x.1.val)), 1,
        addProgram_realizes _, addProgram_costAtMost_one _⟩
    | down _ tail => cases tail
  leaf _ _ _ := BudgetedProgram.ofFun _

-- Disposition ME-086.
/-- The step program returns the witness plus the message, in the carrier selected by the
message. -/
example (m : Fin 8) (w : Fin (m.val + 1)) :
    (addStages.step () (.root _) ⟨⟩).program.run ⟨m, w⟩ = w.val + m.val :=
  ((addStages.step () (.root _) ⟨⟩).realizes _).symm

-- Disposition ME-086.
/-- The composed program retains the witness carrier selected by the actual message. -/
example (message : Fin 8) (witness : Fin (message.val + 1)) :
    (addStages.programAlong () ⟨message, ⟨⟩⟩).program.run witness =
      witness.val + message.val :=
  addStages.run_programAlong () ⟨message, ⟨⟩⟩ witness

-- Disposition ME-091.
/-- The budget along every transcript is one. -/
example (m : Fin 8) : (addStages.programAlong () ⟨m, ⟨⟩⟩).budget = 1 := rfl

/-- On the empty protocol, an empty witness carrier needs no fabricated witness. -/
def emptyState : KnowledgeStateFunction plainSig (.pure ⟨⟩ : Protocol.{0}) Unit (fun _ _ => Empty)
    (fun _ => Empty)
    (fun _ => True) (fun _ _ => False) (fun _ _ _ => True) where
  Witness _ {_} _ _ := Empty
  toFun _ {_} _ _ _ := False
  extractRoot _ w := w
  extractStep _ {_ _} sp _ _ _ := nomatch sp
  extractLeaf _ _ _ w := w
  root _ _ _ h := h
  send sp _ _ _ _ _ _ := nomatch sp
  leaf _ _ _ w _ := w.elim

-- Disposition ME-094.
/-- The empty protocol with no witnesses has a zero-budget extraction program. -/
example (tr : PathAlong plainSig (.pure ⟨⟩ : Protocol.{0})) :
    ((KnowledgeStateFunction.MeasuredStages.zero emptyState (ω := Nat)).programAlong () tr).budget
      = 0 := rfl

-- Disposition ME-103.
/-- Measured state functions fix natural-number profiles, needing only `[Finite Kind]`. -/
example (Kind : Type) [Finite Kind] : Type 1 :=
  MeasuredKnowledgeStateFunction Kind plainSig (.pure ⟨⟩ : Protocol.{0}) Unit (fun _ _ => Empty)
    (fun _ => Empty)
    (fun _ => True) (fun _ _ => False) (fun _ _ _ => True)

/-- At statement `n`, all witness carriers are `Fin (n + 1)`, independently of the transcript. -/
def indexedState : KnowledgeStateFunction plainSig oneRound Nat (fun n _ => Fin (n + 1))
    (fun n => Fin (n + 1)) (fun _ => True) (fun _ _ => True) (fun _ _ _ => True) where
  Witness n {_} _ _ := Fin (n + 1)
  toFun _ {_} _ _ _ := True
  extractRoot _ w := w
  extractStep _ {_ _} _ _ _ w := w
  extractLeaf _ _ _ w := w
  root _ _ _ _ := trivial
  send _ _ _ _ _ _ _ := trivial
  leaf _ _ _ _ _ := trivial

/-- Measured extraction retains the statement-indexed input and output carrier without encoding. -/
example (n : Nat) (tr : PathAlong plainSig oneRound) (w : Fin (n + 1)) :
    ((KnowledgeStateFunction.MeasuredStages.zero indexedState
      (ω := Nat)).programAlong n tr).program.run w = w := by
  rw [KnowledgeStateFunction.MeasuredStages.run_programAlong]
  rcases tr with ⟨x, ⟨⟩⟩
  rfl

/-- info: 2 -/
#guard_msgs in
#eval (((KnowledgeStateFunction.MeasuredStages.zero indexedState (ω := Nat)).programAlong
  3 ⟨(2 : Fin 8), ⟨⟩⟩).program.run (2 : Fin 4)).val

section FixedCountArithmetic

variable {s : Protocol.{0}} {S : Type} {Win : S → Type} {W : S → PathAlong plainSig s → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong plainSig s) → W stmt tr → Prop}

-- Disposition ME-112.
/-- Standard count stages extend a state function without supplying a cost model. -/
example (F : KnowledgeStateFunction plainSig s S W Win admissible relIn validOutput)
    (stages : F.MeasuredStages (Unit → Nat)) :
    MeasuredKnowledgeStateFunction Unit plainSig s S W Win admissible relIn validOutput :=
  { F with stages := stages }

/-- A max-additive monoid on `Nat` combines positive charges without counting them. -/
@[instance_reducible] def maxNatAddCommMonoid : AddCommMonoid Nat where
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

-- Disposition ME-138.
/-- A max-additive profile is weighted accounting, not the fixed count arithmetic. -/
example (F : KnowledgeStateFunction plainSig s S W Win admissible relIn validOutput)
    (_stages : F.MeasuredStages (Unit → Nat)) : True := by
  fail_if_success
    have accepted :
        MeasuredKnowledgeStateFunction Unit plainSig s S W Win admissible relIn validOutput :=
      { F with stages := _stages }
  trivial

end MaxWeights

section ReversedWeights

local instance : Preorder (Unit → Nat) := inferInstanceAs (Preorder (OrderDual (Unit → Nat)))

-- Disposition ME-153.
/-- A reversed order cannot replace the standard order. -/
example (F : KnowledgeStateFunction plainSig s S W Win admissible relIn validOutput)
    (_stages : F.MeasuredStages (Unit → Nat)) : True := by
  fail_if_success
    have accepted :
        MeasuredKnowledgeStateFunction Unit plainSig s S W Win admissible relIn validOutput :=
      { F with stages := _stages }
  trivial

end ReversedWeights

-- Disposition ME-166.
/-- An infinite kind type cannot instantiate a measured state function. -/
example : True := by
  fail_if_success
    have measuredType :=
      MeasuredKnowledgeStateFunction Nat plainSig (.pure ⟨⟩ : Protocol.{0}) Unit
        (fun _ _ => Empty) (fun _ => Empty)
        (fun _ => True) (fun _ _ => False) (fun _ _ _ => True)
  trivial

end FixedCountArithmetic

section ZeroStageAccounting

variable {s : Protocol.{0}} {S : Type} {Win : S → Type} {W : S → PathAlong plainSig s → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong plainSig s) → W stmt tr → Prop}

-- Disposition ME-186.
/-- The zero-instruction stages of every state function have zero budgets. -/
example (F : KnowledgeStateFunction plainSig s S W Win admissible relIn validOutput) :
    (KnowledgeStateFunction.MeasuredStages.zero F (ω := Unit → Nat)).BudgetAtMost 0 0 0 :=
  KnowledgeStateFunction.MeasuredStages.zero_budgetAtMost F

-- Disposition ME-194.
/-- Every state function admits a zero-count measured state function, without bounding its pure
work. -/
example (F : KnowledgeStateFunction plainSig s S W Win admissible relIn validOutput) :
    ∃ measured : MeasuredKnowledgeStateFunction Unit plainSig s S W Win admissible relIn
        validOutput,
      measured.toKnowledgeStateFunction = F ∧
      ∀ stmt tr, (measured.stages.programAlong stmt tr).program.CostAtMost 0 :=
  ⟨{ F with stages := KnowledgeStateFunction.MeasuredStages.zero F }, rfl, fun stmt tr => by
    simpa using (KnowledgeStateFunction.MeasuredStages.zero F).programAlong_costAtMost
      (KnowledgeStateFunction.MeasuredStages.zero_budgetAtMost F) stmt tr⟩

end ZeroStageAccounting

end Interaction.Core.MeasuredExtractionTests
