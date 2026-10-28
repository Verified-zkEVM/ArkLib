/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.GrandProduct

/-! # Revealing the Plonk wire polynomials

A single table message exposes three separately addressable evaluation oracles. Backward
extraction returns that exact message, with no challenge error.
-/

@[expose] public section

namespace Plonk.SendWitness

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal

variable (F : Type) [Field F] [DecidableEq F] (n : ℕ)

/-- There are no polynomial oracles before the witness table is sent. -/
abbrev OStmtIn : Fin 0 → Type := Fin.elim0

instance : ∀ i, OracleInterface (OStmtIn i) := fun i => Fin.elim0 i

/-- One table of three degree-bounded wire polynomials. -/
@[reducible] def pSpec : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Fin 3 → PowerBatch.Poly F n]⟩

instance : ∀ i, OracleInterface ((pSpec F n).Message i)
  | ⟨0, _⟩ => OracleInterface.instProdForall (fun _ : Fin 3 => PowerBatch.Poly F n)

instance : ∀ i, SampleableType ((pSpec F n).Challenge i)
  | ⟨0, h⟩ => nomatch h

variable {F n} {m : ℕ} (ω : F) (hω : IsPrimitiveRoot ω n)
  (cs : ConstraintSystem F m n) (pi : PowerBatch.Poly F n)

/-- The unrevealed table satisfies the gate and copy equations. -/
def relIn : Set ((Unit × ∀ i, OStmtIn i) × (Fin 3 → PowerBatch.Poly F n)) :=
  {x | GrandProduct.InputRelation ω hω cs pi x.2}

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Each output column query is one evaluation query to the table message. -/
def outputSimulation : OracleOutputSimulation oSpec OStmtIn
    (GrandProduct.OStmtIn F n) (pSpec F n) where
  materializeOutput _ _ msg := msg ⟨0, rfl⟩
  simulateOutputQuery _ q := liftM <| OracleSpec.query
    (show (oSpec + ([OStmtIn]ₒ + [(pSpec F n).Message]ₒ)).Domain from
      .inr (.inr ⟨⟨0, rfl⟩, q⟩))
  simulateOutputQuery_eq _ _ _ _ := rfl

/-- Reveal the table through its evaluation-only interface. -/
def oracleVerifier : OracleVerifier oSpec Unit OStmtIn Unit
    (GrandProduct.OStmtIn F n) (pSpec F n) where
  verify _ _ := pure ()
  outputOracle := .inr (outputSimulation oSpec)

omit [DecidableEq F] in
/-- Materialization exposes exactly the received table. -/
theorem oracleVerifier_toVerifier (stmt : Unit × ∀ i, OStmtIn i)
    (tr : (pSpec F n).FullTranscript) :
    (oracleVerifier oSpec).toVerifier.verify stmt tr = pure ((), tr 0) := by
  simp only [OracleVerifier.toVerifier, oracleVerifier, outputSimulation]
  erw [simulateQ_optionT_pure]
  rfl

/-- Revealing a table never rejects. -/
def guardedForm : (oracleVerifier (F := F) (n := n) oSpec).toVerifier.GuardedForm where
  check _ _ := true
  out _ tr := ((), tr 0)
  verify_eq := oracleVerifier_toVerifier oSpec

/-- The honest prover sends its input table unchanged. -/
def oracleProver : OracleProver oSpec Unit OStmtIn (Fin 3 → PowerBatch.Poly F n)
    Unit (GrandProduct.OStmtIn F n) Unit (pSpec F n) where
  PrvState _ := Fin 3 → PowerBatch.Poly F n
  input x := x.2
  sendMessage | ⟨0, _⟩ => fun a => pure (a, a)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output a := pure (((), a), ())

instance : (oracleProver (F := F) (n := n) oSpec).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- The initial polynomial-table reveal reduction. -/
def oracleReduction : OracleReduction oSpec Unit OStmtIn (Fin 3 → PowerBatch.Poly F n)
    Unit (GrandProduct.OStmtIn F n) Unit (pSpec F n) :=
  ⟨oracleProver oSpec, oracleVerifier oSpec⟩

/-- Intermediate witnesses retain the table throughout the reveal. -/
abbrev WitMid (_ : Fin 2) := Fin 3 → PowerBatch.Poly F n

/-- Backward extraction reads the actual table message. -/
def rbrExtractor : Extractor.RoundByRound oSpec (Unit × ∀ i, OStmtIn i)
    (Fin 3 → PowerBatch.Poly F n) Unit (pSpec F n) (WitMid (F := F) (n := n)) where
  extractIn _ a := a
  extractMid _ _ tr _ := tr ⟨0, Nat.zero_lt_succ _⟩
  extractOut _ tr _ := tr 0

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The table relation is transferred from the witness to its revealed message. -/
def knowledgeStateFunction : (oracleVerifier oSpec).toVerifier.KnowledgeStateFunction
    init impl (relIn ω hω cs pi) (GrandProduct.relIn ω hω cs pi) (rbrExtractor oSpec) where
  toFun
    | 0 => fun _ _ a => GrandProduct.InputRelation ω hω cs pi a
    | 1 => fun _ tr _ => GrandProduct.InputRelation ω hω cs pi (tr ⟨0, by decide⟩)
  toFun_empty _ _ h := h
  toFun_next | ⟨0, _⟩ => fun _ _ _ _ _ h => h
  toFun_full stmt tr _ h := ((guardedForm oSpec).check_and_of_prEvent_pos h).2

/-- The reveal has zero fixed-prefix knowledge error. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith :
    (oracleVerifier oSpec).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn ω hω cs pi) (GrandProduct.relIn ω hω cs pi) _ (rbrExtractor oSpec)
      (knowledgeStateFunction ω hω cs pi oSpec init impl) (fun _ => 0) := by
  intro _ ⟨i, hi⟩
  fin_cases i
  nomatch hi

/-- The actual honest reveal run preserves the input relation with probability one. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction oSpec).perfectCompleteness init impl
      (relIn ω hω cs pi) (GrandProduct.relIn ω hω cs pi) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit h x hx
  rw [Reduction.run_run_eq_bind] at hx
  have hrun : (oracleProver oSpec).run stmt wit =
      pure ((default : (pSpec F n).Transcript 0).concat (m := (0 : Fin 1)) wit,
        (((), wit), ())) := by
    simp [Prover.run, Prover.runToRound, Fin.induction, Fin.induction.go,
      Prover.processRound, oracleProver, Fin.vcons, Fin.dcons]
    rfl
  simp only [oracleReduction, OracleReduction.toReduction, hrun, pure_bind,
    Verifier.run, oracleVerifier_toVerifier, OptionT.run_pure, liftComp_pure,
    Option.map_some] at hx
  subst x
  exact ⟨_, rfl, h, rfl⟩

end Plonk.SendWitness
