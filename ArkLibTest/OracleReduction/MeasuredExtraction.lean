/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.OracleReduction.Security.Resources
import ArkLib.Interaction.Oracle.Security.KnowledgeResources
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
    Extractor.Straightline.MeasuredProgram []ₒ ℕ (Fin (2 ^ m)) WitOut pSpec ℕ :=
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

end MeasuredExtractionTest
