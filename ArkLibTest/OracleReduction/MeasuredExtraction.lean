/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.OracleReduction.Security.Resources

/-!
# Measured extraction charges only declared instructions

An extractor that searches all `2 ^ m` candidate witnesses in pure Lean code requests no
instruction. Its measured program therefore meets the zero budget, so the resource contract alone
gives no running-time bound.
-/

open OracleComp OracleSpec ProtocolSpec

variable {WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Return the first of the `2 ^ m` candidate witnesses accepted by `rel`. -/
def searchExtractor (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    Extractor.Straightline []ₒ ℕ (Fin (2 ^ m)) WitOut pSpec :=
  fun stmtIn _ _ _ _ ↦ OptionT.mk (pure ((List.finRange (2 ^ m)).find? (rel stmtIn)))

/-- The search as a program with no instructions. -/
def searchProgram (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    Extractor.Straightline.MeasuredProgram []ₒ ℕ (Fin (2 ^ m)) WitOut pSpec ℕ where
  View := ℕ
  view stmtIn _ _ _ _ := stmtIn
  Op := PEmpty
  spec _ := []ₒ
  program stmtIn := pure ((List.finRange (2 ^ m)).find? (rel stmtIn))
  answer _ := fun t ↦ t.elim
  cost := fun t ↦ t.elim

/-- The search extractor is the execution of its program. -/
theorem searchProgram_realizes (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    (searchProgram m rel (WitOut := WitOut) (pSpec := pSpec)).Realizes
      (searchExtractor m rel) :=
  fun _ _ _ _ _ ↦ rfl

/-- The search requests no instruction, so it costs zero. -/
theorem searchProgram_costAtMost_zero (m : ℕ) (rel : ℕ → Fin (2 ^ m) → Bool) :
    (searchProgram m rel (WitOut := WitOut) (pSpec := pSpec)).CostAtMost 0 :=
  fun _ ↦ (worstCaseCostBound_pure _ _ _).mpr le_rfl

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
  ⟨h, searchProgram_realizes m rel, searchProgram_costAtMost_zero m rel⟩
