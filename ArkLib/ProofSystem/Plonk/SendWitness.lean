/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.GrandProduct.Reduction
public import ArkLib.ProofSystem.Component.SendWitness

/-! # Revealing the Plonk wire polynomials

A `SendSingleWitness.Adapter` sends the three-column table unchanged and exposes three separately
addressable evaluation oracles. Its shared guarded verifier and transcript extractor give perfect
completeness and zero-error round-by-round knowledge soundness from the Plonk relation transfers.
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
  SendSingleWitness.oraclePSpec (Fin 3 → GeneratorBatch.Poly F n)

instance : ∀ i, OracleInterface ((pSpec F n).Message i) :=
  inferInstanceAs (∀ i, OracleInterface
    ((SendSingleWitness.oraclePSpec (Fin 3 → GeneratorBatch.Poly F n)).Message i))

instance : ∀ i, SampleableType ((pSpec F n).Challenge i) :=
  inferInstanceAs (∀ i, SampleableType
    ((SendSingleWitness.oraclePSpec (Fin 3 → GeneratorBatch.Poly F n)).Challenge i))

variable {F n} {m : ℕ} (ω : F) (hω : IsPrimitiveRoot ω n)
  (cs : ConstraintSystem F m n) (pi : GeneratorBatch.Poly F n)

/-- The unrevealed table satisfies the gate and copy equations. -/
def relIn : Set ((Unit × ∀ i, OStmtIn i) × (Fin 3 → GeneratorBatch.Poly F n)) :=
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

/-- The shared witness sender exposes the table through three evaluation-only oracles. -/
def adapter : SendSingleWitness.Adapter oSpec Unit OStmtIn
    (Fin 3 → GeneratorBatch.Poly F n) Unit (GrandProduct.OStmtIn F n)
    (Fin 3 → GeneratorBatch.Poly F n) where
  stmtOut _ := ()
  encode := id
  decode := id
  outputOracle := .inr (outputSimulation oSpec)

/-- Reveal the table through its evaluation-only interface. -/
def oracleVerifier : OracleVerifier oSpec Unit OStmtIn Unit
    (GrandProduct.OStmtIn F n) (pSpec F n) :=
  (adapter oSpec).oracleVerifier

omit [DecidableEq F] in
/-- Materialization exposes exactly the received table. -/
theorem oracleVerifier_toVerifier (stmt : Unit × ∀ i, OStmtIn i)
    (tr : (pSpec F n).FullTranscript) :
    (oracleVerifier oSpec).toVerifier.verify stmt tr = pure ((), tr 0) :=
  (adapter oSpec).verifier_run stmt tr

/-- Revealing a table never rejects. -/
def guardedForm : (oracleVerifier (F := F) (n := n) oSpec).toVerifier.GuardedForm :=
  (adapter oSpec).guardedForm

/-- The honest prover sends its input table unchanged. -/
def oracleProver : OracleProver oSpec Unit OStmtIn (Fin 3 → GeneratorBatch.Poly F n)
    Unit (GrandProduct.OStmtIn F n) Unit (pSpec F n) :=
  (adapter oSpec).oracleProver

instance : (oracleProver (F := F) (n := n) oSpec).OutputIsPure :=
  SendSingleWitness.Adapter.instOutputIsPure _

/-- The initial polynomial-table reveal reduction. -/
def oracleReduction : OracleReduction oSpec Unit OStmtIn (Fin 3 → GeneratorBatch.Poly F n)
    Unit (GrandProduct.OStmtIn F n) Unit (pSpec F n) :=
  (adapter oSpec).oracleReduction

/-- Intermediate witnesses retain the table throughout the reveal. -/
abbrev WitMid (_ : Fin 2) := Fin 3 → GeneratorBatch.Poly F n

/-- Backward extraction reads the actual table message. -/
def rbrExtractor : Extractor.RoundByRound oSpec (Unit × ∀ i, OStmtIn i)
    (Fin 3 → GeneratorBatch.Poly F n) Unit (pSpec F n) (WitMid (F := F) (n := n)) :=
  (adapter oSpec).rbrExtractor

/-- An accepted revealed table is the same witness for the input relation. -/
theorem decode_relation (stmt : Unit × ∀ i, OStmtIn i)
    (a : Fin 3 → GeneratorBatch.Poly F n)
    (h : ((adapter oSpec).output stmt a, ()) ∈ GrandProduct.relIn ω hω cs pi) :
    (stmt, (adapter oSpec).decode a) ∈ relIn ω hω cs pi := h

/-- Revealing an honest table preserves its gate and copy equations. -/
theorem encode_relation (stmt : Unit × ∀ i, OStmtIn i)
    (a : Fin 3 → GeneratorBatch.Poly F n) (h : (stmt, a) ∈ relIn ω hω cs pi) :
    ((adapter oSpec).output stmt ((adapter oSpec).encode a), ()) ∈
      GrandProduct.relIn ω hω cs pi := h

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The table relation is transferred from the witness to its revealed message. -/
def knowledgeStateFunction : (oracleVerifier oSpec).toVerifier.KnowledgeStateFunction
    init impl (relIn ω hω cs pi) (GrandProduct.relIn ω hω cs pi) (rbrExtractor oSpec) :=
  (adapter oSpec).knowledgeStateFunction init impl (relIn ω hω cs pi)
    (GrandProduct.relIn ω hω cs pi) (decode_relation ω hω cs pi oSpec)

/-- The reveal has zero fixed-prefix knowledge error. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith :
    (oracleVerifier oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn ω hω cs pi) (GrandProduct.relIn ω hω cs pi) _ (rbrExtractor oSpec)
      (knowledgeStateFunction ω hω cs pi oSpec init impl) (fun _ => 0) :=
  (adapter oSpec).rbrKnowledgeSoundnessWith init impl (relIn ω hω cs pi)
    (GrandProduct.relIn ω hω cs pi) (decode_relation ω hω cs pi oSpec)

/-- The actual honest reveal run preserves the input relation with probability one. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction oSpec).perfectCompleteness init impl
      (relIn ω hω cs pi) (GrandProduct.relIn ω hω cs pi) :=
  (adapter oSpec).perfectCompleteness init impl (relIn ω hω cs pi)
    (GrandProduct.relIn ω hω cs pi) (encode_relation ω hω cs pi oSpec)

end Plonk.SendWitness
