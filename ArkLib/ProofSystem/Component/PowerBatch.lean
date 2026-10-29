/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PowerBatch
public import ArkLib.ProofSystem.Component.GeneratorBatch

/-!
# Power batching

The powers generator specializes linear batching to the coefficients `1, α, …, α^(k-1)`.
Its fixed-prefix knowledge error is `(k - 1) / |F|`.
-/

@[expose] public section

open OracleSpec OracleComp OracleQuery ProtocolSpec CoreDefinitions
open scoped NNReal ENNReal ProbabilityTheory

namespace PowerBatch

variable (F : Type) [Field F] [DecidableEq F]

/-- One uniformly sampled field challenge. -/
@[reducible] def pSpec := GeneratorBatch.pSpec F

abbrev instOracleInterfaceMessagePSpec := GeneratorBatch.instOracleInterfaceMessagePSpec F
abbrev instSampleableTypeChallengePSpec [SampleableType F] :=
  GeneratorBatch.instSampleableTypeChallengePSpec F

variable (D : QuotientZeroTest.Domain F) (d k : ℕ)

/-- The family of strictly degree-bounded input oracles. -/
abbrev OStmtIn := GeneratorBatch.OStmtIn F d k

/-- All inputs vanish on the domain. -/
abbrev relIn := GeneratorBatch.relIn F D d k

/-- The batch vanishes on the domain. -/
abbrev relOut := GeneratorBatch.relOut F D d

omit [DecidableEq F] in
/-- The output relation is the quotient zero test's input relation. -/
theorem relOut_eq_quotient_relIn : relOut F D d = QuotientZeroTest.relIn F D d := rfl

variable (hd : 0 < d) {ι : Type} (oSpec : OracleSpec ι)

/-- The materialized power batch. -/
abbrev output := GeneratorBatch.output F F d k (powerBatchGenerator F k) hd

/-- Query an input oracle at a point. -/
abbrev queryInput := GeneratorBatch.queryInput F F d k oSpec

/-- Input simulation evaluates the corresponding polynomial. -/
abbrev simulateQ_queryInput := GeneratorBatch.simulateQ_queryInput F F d k oSpec

/-- Evaluate the virtual power batch. -/
abbrev queryBatch := GeneratorBatch.queryBatch F F d k (powerBatchGenerator F k) oSpec

/-- Virtual evaluation is the power-weighted sum of input evaluations. -/
abbrev simulateQ_queryBatch :=
  GeneratorBatch.simulateQ_queryBatch F F d k (powerBatchGenerator F k) oSpec

/-- The virtual oracle simulation for power weights. -/
abbrev outputSimulation :=
  GeneratorBatch.outputSimulation F F d k (powerBatchGenerator F k) hd oSpec

/-- Forward the challenge and expose the virtual batch. -/
abbrev oracleVerifier :=
  GeneratorBatch.oracleVerifier F F d k (powerBatchGenerator F k) hd oSpec

/-- Materialization agrees with the power batch. -/
abbrev oracleVerifier_toVerifier :=
  GeneratorBatch.oracleVerifier_toVerifier F F d k (powerBatchGenerator F k) hd oSpec

/-- The forwarding verifier has an always-true guard. -/
abbrev guardedForm := GeneratorBatch.guardedForm F F d k (powerBatchGenerator F k) hd oSpec

/-- The honest prover computes the power batch. -/
abbrev oracleProver := GeneratorBatch.oracleProver F F d k (powerBatchGenerator F k) hd oSpec

/-- Power batching as an instance of generator batching. -/
abbrev oracleReduction :=
  GeneratorBatch.oracleReduction F F d k (powerBatchGenerator F k) hd oSpec

/-- The extractor retains the unique witness. -/
abbrev rbrExtractor := GeneratorBatch.rbrExtractor F F d k oSpec

variable [SampleableType F]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Knowledge is vanishing of every input before the challenge and of the batch afterwards. -/
abbrev knowledgeStateFunction :=
  GeneratorBatch.knowledgeStateFunction F F D d k (powerBatchGenerator F k) hd oSpec init impl

/-- Perfect completeness for every ambient oracle implementation. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction F d k hd oSpec).perfectCompleteness init impl
      (relIn F D d k) (relOut F D d) :=
  GeneratorBatch.oracleReduction_perfectCompleteness F F D d k
    (powerBatchGenerator F k) hd oSpec init impl

variable [Fintype F]

/-- Each fixed false family is hidden with probability at most `(k - 1) / |F|`. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith :
    (oracleVerifier F d k hd oSpec).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn F D d k) (relOut F D d) (fun _ => Unit) (rbrExtractor F d k oSpec)
      (knowledgeStateFunction F D d k hd oSpec init impl)
      (fun _ => ((k - 1 : ℕ) : ℝ≥0) / Fintype.card F) := by
  apply GeneratorBatch.oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_of_prob_le
  intro v hv
  simpa only [ENNReal.coe_div (by simp : (Fintype.card F : ℝ≥0) ≠ 0),
    ENNReal.coe_natCast] using prob_dotProduct_powerBatchGenerator_eq_zero_le v hv

/-- Existential form of the named fixed-prefix knowledge certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCase :
    (oracleVerifier F d k hd oSpec).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (relIn F D d k) (relOut F D d)
      (fun _ => ((k - 1 : ℕ) : ℝ≥0) / Fintype.card F) :=
  ⟨_, rbrExtractor F d k oSpec, knowledgeStateFunction F D d k hd oSpec init impl,
    oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith F D d k hd oSpec init impl⟩

end PowerBatch
