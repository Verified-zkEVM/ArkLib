/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Batch.Data
public import ArkLib.ProofSystem.Plonk.GrandProduct.Reduction
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-! # Plonk residual batching

One uniform challenge combines the three retained residual oracles, preserving their exact
inclusive degree budget and every earlier oracle. The verifier implements batch evaluation by
the reindexed GeneratorBatch queries with `powerBatchGenerator F 3`. The named fixed-prefix
knowledge error is `2 / |F|`.

The component's output type permits degree `D + 1`, while its generated batch has degree at most
`D`. A value-preserving lens cannot tighten arbitrary outputs of that type; the retained-context
adapter transports the generated output, honest run, and named certificate directly.
-/

@[expose] public section

namespace Plonk.Batch

open OracleSpec OracleComp OracleQuery ProtocolSpec CompPoly CoreDefinitions
open scoped NNReal ENNReal ProbabilityTheory

variable (F : Type) [Field F] [DecidableEq F] (n : ℕ)

/-- Batching retains the grand-product stage's oracle family. -/
abbrev OStmtIn := GrandProduct.OStmtOut F n

/-- Retained earlier oracles and the new degree-bounded batch. -/
abbrev OStmtOut := Sum.elim (OStmtIn F n)
  (fun _ : Unit => FiniteDomainQuotient.Poly F (GrandProduct.residualDegree n))

instance : ∀ i, OracleInterface (OStmtOut F n i)
  | .inl i => inferInstanceAs (OracleInterface (OStmtIn F n i))
  | .inr _ => inferInstanceAs
      (OracleInterface (FiniteDomainQuotient.Poly F (GrandProduct.residualDegree n)))

/-- One verifier challenge, with no prover messages. -/
@[reducible] def pSpec : ProtocolSpec 1 := GeneratorBatch.pSpec F

instance : ∀ i, OracleInterface ((pSpec F).Message i) :=
  inferInstanceAs (∀ i, OracleInterface ((GeneratorBatch.pSpec F).Message i))

instance [SampleableType F] : ∀ i, SampleableType ((pSpec F).Challenge i) :=
  inferInstanceAs (∀ i, SampleableType ((GeneratorBatch.pSpec F).Challenge i))

variable {F n} (ω : F) (hω : IsPrimitiveRoot ω n)

/-- The input relation is exactly the grand-product output relation. -/
def relIn := GrandProduct.relOut ω hω

/-- The output batch vanishes on the row domain. -/
def relOut : Set (((F × F) × ∀ i, OStmtOut F n i) × Unit) :=
  {x | (EvaluationDomain.primitiveRoot ω hω).Vanishes (x.1.2 (.inr ())).val.toPoly}

/-- Select the three residual polynomials from the retained context. -/
def residualFamily (f : ∀ i, OStmtIn F n i) :
    Fin 3 → GeneratorBatch.Poly F (GrandProduct.residualDegree n + 1) :=
  fun j => f (.inr (.inr j))

/-- Materialize all earlier oracles and the new power-weighted residual. -/
def outputOracles (f : ∀ i, OStmtIn F n i) (α : F) : ∀ i, OStmtOut F n i
  | .inl i => f i
  | .inr _ => batch (residualFamily f) α

/-- Preserve the joint grand-product challenge alongside the retained output oracles. -/
def output (stmt : (F × F) × ∀ i, OStmtIn F n i) (α : F) :=
  (stmt.1, outputOracles stmt.2 α)

/-- The projected residual family satisfies exactly the component's input relation. -/
theorem relIn_iff_component (stmt : (F × F) × ∀ i, OStmtIn F n i) (wit : Unit) :
    (stmt, wit) ∈ relIn ω hω ↔
      (((), residualFamily stmt.2), wit) ∈ GeneratorBatch.relIn F
        (QuotientZeroTest.finiteDomain F (points ω hω))
        (GrandProduct.residualDegree n + 1) 3 := by
  exact forall_congr' fun _ => vanishes_iff_zeroOn ω hω _

/-- Retaining context and tightening the generated batch preserve the output relation. -/
theorem relOut_output_iff_component (stmt : (F × F) × ∀ i, OStmtIn F n i)
    (α : F) (wit : Unit) :
    (output stmt α, wit) ∈ relOut ω hω ↔
      (GeneratorBatch.output F F (GrandProduct.residualDegree n + 1) 3
        (powerBatchGenerator F 3) (Nat.succ_pos _) ((), residualFamily stmt.2) α, wit) ∈
        GeneratorBatch.relOut F
        (QuotientZeroTest.finiteDomain F (points ω hω))
        (GrandProduct.residualDegree n + 1) :=
  vanishes_iff_zeroOn ω hω _

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Forward an evaluation query to any retained oracle. -/
def queryRetained (q : [OStmtIn F n]ₒ.Domain) :
    OracleComp (oSpec + ([OStmtIn F n]ₒ + [(pSpec F).Message]ₒ))
      ([OStmtIn F n]ₒ.Range q) :=
  liftM <| OracleSpec.query
    (show (oSpec + ([OStmtIn F n]ₒ + [(pSpec F).Message]ₒ)).Domain from
      .inr (.inl q))

omit [DecidableEq F] in
/-- Simulation of a retained query agrees with its original oracle interface. -/
theorem simulateQ_queryRetained (f : ∀ i, OStmtIn F n i)
    (messages : (pSpec F).Messages) (q : [OStmtIn F n]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec f messages) (queryRetained oSpec q) =
      pure (OracleInterface.answer (f q.1) q.2) := rfl

/-- Reindex the component's input queries into the retained residual family. -/
def componentQueryImpl : QueryImpl
    (oSpec + ([GeneratorBatch.OStmtIn F (GrandProduct.residualDegree n + 1) 3]ₒ +
      [(pSpec F).Message]ₒ))
    (OracleComp (oSpec + ([OStmtIn F n]ₒ + [(pSpec F).Message]ₒ)))
  | .inl q => liftM (OracleSpec.query
      (spec := oSpec + ([OStmtIn F n]ₒ + [(pSpec F).Message]ₒ)) (.inl q))
  | .inr (.inl ⟨j, z⟩) => queryRetained oSpec ⟨.inr (.inr j), z⟩
  | .inr (.inr q) => liftM (OracleSpec.query
      (spec := oSpec + ([OStmtIn F n]ₒ + [(pSpec F).Message]ₒ)) (.inr (.inr q)))

omit [DecidableEq F] in
/-- Reindexing preserves every query's materialized answer. -/
theorem simulateQ_componentQueryImpl (f : ∀ i, OStmtIn F n i)
    (messages : (pSpec F).Messages) {A : Type}
    (oa : OracleComp (oSpec +
      ([GeneratorBatch.OStmtIn F (GrandProduct.residualDegree n + 1) 3]ₒ +
        [(pSpec F).Message]ₒ)) A) :
    simulateQ (OracleInterface.simOracle2 oSpec f messages)
      (simulateQ (componentQueryImpl (n := n) oSpec) oa) =
        simulateQ (OracleInterface.simOracle2 oSpec (residualFamily f) messages) oa := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  apply QueryImpl.ext
  intro q
  rcases q with q | (⟨j, z⟩ | q) <;> rfl

/-- The virtual batch is the component's query implementation in the retained context. -/
def queryBatch (α z : F) :
    OracleComp (oSpec + ([OStmtIn F n]ₒ + [(pSpec F).Message]ₒ)) F :=
  simulateQ (componentQueryImpl (n := n) oSpec)
    (GeneratorBatch.queryBatch F F (GrandProduct.residualDegree n + 1) 3
      (powerBatchGenerator F 3) oSpec α z)

/-- Materializing the reindexed component query gives the degree-tightened batch. -/
theorem simulateQ_queryBatch (f : ∀ i, OStmtIn F n i)
    (messages : (pSpec F).Messages) (α z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec f messages) (queryBatch (n := n) oSpec α z) =
      pure (FiniteDomainQuotient.eval (batch (residualFamily f) α) z) := by
  unfold queryBatch
  rw [simulateQ_componentQueryImpl]
  exact (GeneratorBatch.outputSimulation F F (GrandProduct.residualDegree n + 1) 3
    (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec).simulateOutputQuery_eq
      (fun | ⟨⟨0, _⟩, _⟩ => α) (residualFamily f) messages ⟨(), z⟩

/-- Evaluation-only implementation of the retained and batched output oracles. -/
def outputSimulation : OracleOutputSimulation oSpec (OStmtIn F n) (OStmtOut F n) (pSpec F) where
  materializeOutput chals f _ := outputOracles f (chals ⟨0, rfl⟩)
  simulateOutputQuery chals
    | ⟨.inl i, q⟩ => queryRetained oSpec ⟨i, q⟩
    | ⟨.inr _, z⟩ => queryBatch (n := n) oSpec (chals ⟨0, rfl⟩) z
  simulateOutputQuery_eq chals f messages
    | ⟨.inl i, q⟩ => simulateQ_queryRetained oSpec f messages ⟨i, q⟩
    | ⟨.inr _, z⟩ => simulateQ_queryBatch oSpec f messages (chals ⟨0, rfl⟩) z

/-- Forward the public context and expose the virtual batch. -/
def oracleVerifier : OracleVerifier oSpec (F × F) (OStmtIn F n)
    (F × F) (OStmtOut F n) (pSpec F) where
  verify stmt chals := do
    let _ ← OptionT.mk <| simulateQ (componentQueryImpl (n := n) oSpec)
      ((GeneratorBatch.oracleVerifier F F (GrandProduct.residualDegree n + 1) 3
        (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec).verify () chals).run
    pure stmt
  outputOracle := .inr (outputSimulation (n := n) oSpec)

/-- Materialization gives the retained context with the challenge-weighted batch. -/
theorem oracleVerifier_toVerifier (stmt : (F × F) × ∀ i, OStmtIn F n i)
    (tr : (pSpec F).FullTranscript) :
    (oracleVerifier (n := n) oSpec).toVerifier.verify stmt tr = pure (output stmt (tr 0)) := by
  simp only [OracleVerifier.toVerifier, oracleVerifier, outputSimulation,
    GeneratorBatch.oracleVerifier, OptionT.run_pure, simulateQ_pure, OptionT.run_bind,
    OptionT.run_mk]
  erw [simulateQ_optionT_pure]
  rfl

/-- Batching forwards every transcript without a guard. -/
def guardedForm : (oracleVerifier (F := F) (n := n) oSpec).toVerifier.GuardedForm where
  check _ _ := true
  out stmt tr := output stmt (tr 0)
  verify_eq stmt tr := oracleVerifier_toVerifier oSpec stmt tr

/-- The component prover carries the retained context and tightens its generated batch.
The field seed is retained separately because the component state stores only its weights. -/
def oracleProver : OracleProver oSpec (F × F) (OStmtIn F n) Unit
    (F × F) (OStmtOut F n) Unit (pSpec F) where
  PrvState i := (((F × F) × ∀ j, OStmtIn F n j) × F) ×
    (GeneratorBatch.oracleProver F F (GrandProduct.residualDegree n + 1) 3
      (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec).PrvState i
  input x := ((x.1, 0), (GeneratorBatch.oracleProver F F (GrandProduct.residualDegree n + 1) 3
    (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec).input (((), residualFamily x.1.2), x.2))
  sendMessage i s := do
    let (msg, next) ← (GeneratorBatch.oracleProver F F (GrandProduct.residualDegree n + 1) 3
      (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec).sendMessage i s.2
    pure (msg, s.1, next)
  receiveChallenge
    | ⟨0, hi⟩ => fun s => do
      let next ← (GeneratorBatch.oracleProver F F (GrandProduct.residualDegree n + 1) 3
        (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec).receiveChallenge ⟨0, hi⟩ s.2
      pure (fun α => ((s.1.1, α), next α))
  output s := pure (output s.1.1 s.1.2, ())

instance : (oracleProver (F := F) (n := n) oSpec).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- Residual batching over the full retained Plonk context. -/
def oracleReduction : OracleReduction oSpec (F × F) (OStmtIn F n) Unit
    (F × F) (OStmtOut F n) Unit (pSpec F) :=
  ⟨oracleProver oSpec, oracleVerifier oSpec⟩

/-- The component extractor acts on the projected residual family. -/
def rbrExtractor : Extractor.RoundByRound oSpec ((F × F) × ∀ i, OStmtIn F n i)
    Unit Unit (pSpec F) (fun _ => Unit) where
  extractIn stmt := (GeneratorBatch.rbrExtractor F F (GrandProduct.residualDegree n + 1) 3
    oSpec).extractIn ((), residualFamily stmt.2)
  extractMid i stmt := (GeneratorBatch.rbrExtractor F F (GrandProduct.residualDegree n + 1) 3
    oSpec).extractMid i ((), residualFamily stmt.2)
  extractOut stmt := (GeneratorBatch.rbrExtractor F F (GrandProduct.residualDegree n + 1) 3
    oSpec).extractOut ((), residualFamily stmt.2)

variable [SampleableType F] {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Knowledge is vanishing of all three inputs before the challenge and the batch afterwards. -/
def knowledgeStateFunction : (oracleVerifier (n := n) oSpec).toVerifier.KnowledgeStateFunction
    init impl (relIn ω hω) (relOut ω hω) (rbrExtractor oSpec) where
  toFun i stmt tr w :=
    (GeneratorBatch.knowledgeStateFunction F F (QuotientZeroTest.finiteDomain F (points ω hω))
      (GrandProduct.residualDegree n + 1) 3 (powerBatchGenerator F 3)
    (Nat.succ_pos _) oSpec init impl)
      i ((), residualFamily stmt.2) tr w
  toFun_empty stmt w h := (relIn_iff_component ω hω stmt w).mpr h
  toFun_next | ⟨0, _⟩ => fun h => nomatch h
  toFun_full stmt tr w h :=
    (relOut_output_iff_component ω hω stmt (tr ⟨0, by decide⟩) w).mp
      ((guardedForm oSpec).check_and_of_prEvent_pos h).2

omit [SampleableType F] in
/-- The honest runs have the same challenge and corresponding retained outputs. -/
theorem oracleProver_run (stmt : (F × F) × ∀ i, OStmtIn F n i) (wit : Unit) :
    (oracleProver (n := n) oSpec).run stmt wit = (do
      let r ← (GeneratorBatch.oracleProver F F (GrandProduct.residualDegree n + 1) 3
        (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec).run ((), residualFamily stmt.2) wit
      pure (r.1, (output stmt (r.1 0), r.2.2))) := by
  simp [Prover.run, Prover.runToRound, Fin.induction, Fin.induction.go,
    Prover.processRound, oracleProver, GeneratorBatch.oracleProver,
    ProtocolSpec.getChallenge, Fin.vcons, Fin.dcons, output]

/-- Batching inherits perfect completeness from the component's honest run. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction (n := n) oSpec).perfectCompleteness init impl
      (relIn ω hω) (relOut ω hω) := by
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness
  rw [Reduction.completeness_iff_of_guarded_verifier _ (guardedForm oSpec)]
  intro stmt wit hstmt
  have hc := GeneratorBatch.oracleReduction_perfectCompleteness F F
    (QuotientZeroTest.finiteDomain F (points ω hω))
    (GrandProduct.residualDegree n + 1) 3 (powerBatchGenerator F 3)
    (Nat.succ_pos _) oSpec init impl
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at hc
  rw [Reduction.completeness_iff_of_guarded_verifier _
    (GeneratorBatch.guardedForm F F (GrandProduct.residualDegree n + 1) 3
      (powerBatchGenerator F 3) (Nat.succ_pos _) oSpec)] at hc
  have h := hc ((), residualFamily stmt.2) wit
    ((relIn_iff_component ω hω stmt wit).mp hstmt)
  simp only [OracleReduction.toReduction, oracleReduction, oracleProver_run]
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map]
  rw [← map_bind, prEvent_map]
  refine h.trans (prEvent_mono _ _ _ ?_)
  intro q hq
  exact ⟨rfl, (relOut_output_iff_component ω hω stmt (q.1.1 0) q.1.2.2).mpr hq.2.1, rfl⟩

variable [Fintype F]

/-- Every fixed false residual family survives the uniform batch challenge with probability
at most `2 / |F|`. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith :
    (oracleVerifier (n := n) oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn ω hω) (relOut ω hω) (fun _ => Unit) (rbrExtractor oSpec)
      (knowledgeStateFunction ω hω oSpec init impl)
      (fun _ => (2 : ℝ≥0) / Fintype.card F) := by
  intro stmt i tr
  apply GeneratorBatch.oracleVerifier_rbrKnowledgeSoundnessWith_of_prob_le F F
    (QuotientZeroTest.finiteDomain F (points ω hω))
    (GrandProduct.residualDegree n + 1) 3 (powerBatchGenerator F 3)
    (Nat.succ_pos _) oSpec init impl ((2 : ℝ≥0) / Fintype.card F) ?_
    ((), residualFamily stmt.2) i tr
  intro v hv
  have hG := isZeroEvadingGenerator_powerBatchGenerator (F := F) 3
  refine (hG.prob_le v hv).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  exact min_le_right _ _

/-- Existential packaging of the named fixed-prefix certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundness :
    (oracleVerifier (n := n) oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn ω hω) (relOut ω hω) (fun _ => (2 : ℝ≥0) / Fintype.card F) :=
  ⟨_, rbrExtractor oSpec, knowledgeStateFunction ω hω oSpec init impl,
    oracleVerifier_rbrKnowledgeSoundnessWith ω hω oSpec init impl⟩

end Plonk.Batch
