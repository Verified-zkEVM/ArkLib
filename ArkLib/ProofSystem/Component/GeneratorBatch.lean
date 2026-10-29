/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.GeneratorBatch
public import ArkLib.ProofSystem.Component.QuotientZeroTest

/-!
# Batching with zero-evading generators

One uniform seed selects a linear combination of a fixed family of polynomial oracles.
Queries to the virtual batch evaluate each input at the same point. Zero evasion bounds
how often a false family becomes a vanishing batch; linearity gives perfect completeness.
-/

@[expose] public section

open OracleSpec OracleComp OracleQuery ProtocolSpec CoreDefinitions
open scoped NNReal ENNReal ProbabilityTheory

namespace GeneratorBatch

variable (F : Type) [Field F] [DecidableEq F]
variable (S : Type)

/-- Strictly degree-bounded input polynomials expose evaluation queries. -/
instance (d : ℕ) : OracleInterface (Poly F d) where
  Query := F
  toOC.spec := fun _ => F
  toOC.impl z := do return CompPoly.CPolynomial.evalHorner z (← read).val

/-- One verifier challenge, with no prover messages. -/
@[reducible] def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[S]⟩

instance : ∀ i, OracleInterface ((pSpec S).Message i)
  | ⟨0, h⟩ => nomatch h

instance [SampleableType S] : ∀ i, SampleableType ((pSpec S).Challenge i)
  | ⟨0, _⟩ => inferInstanceAs (SampleableType S)

variable (D : QuotientZeroTest.Domain F) (d k : ℕ)
variable (G : Generator S (Fin k) F)

/-- The fixed family of input polynomial oracles. -/
abbrev OStmtIn := fun _ : Fin k => Poly F d

/-- The input relation requires each polynomial to vanish on the domain. -/
def relIn : Set ((Unit × ∀ i, OStmtIn F d k i) × Unit) :=
  {x | ∀ i, Polynomial.ZeroOn D.points (x.1.2 i).val.toPoly}

/-- The output relation is the quotient zero test's relation on the batched oracle. -/
def relOut : Set ((Unit × ∀ i, QuotientZeroTest.OStmtIn F d i) × Unit) :=
  QuotientZeroTest.relIn F D d

omit [DecidableEq F] in
/-- The batching output and quotient input relations coincide on their shared oracle type. -/
theorem relOut_eq_quotient_relIn : relOut F D d = QuotientZeroTest.relIn F D d := rfl

variable (hd : 0 < d) {ι : Type} (oSpec : OracleSpec ι)

/-- The materialized batched output, with no extra public data. -/
def output (stmt : Unit × ∀ i, OStmtIn F d k i) (s : S) :
    Unit × ∀ i, QuotientZeroTest.OStmtIn F d i :=
  ((), fun _ => batch hd stmt.2 (G s))

/-- Query one member of the fixed input family. -/
def queryInput (i : Fin k) (z : F) :
    OracleComp (oSpec + ([OStmtIn F d k]ₒ + [(pSpec S).Message]ₒ)) F :=
  liftM <| OracleSpec.query
    (show (oSpec + ([OStmtIn F d k]ₒ + [(pSpec S).Message]ₒ)).Domain from
      Sum.inr (Sum.inl ⟨i, z⟩))

omit [DecidableEq F] in
/-- Input simulation evaluates the corresponding computable polynomial. -/
theorem simulateQ_queryInput (f : ∀ i, OStmtIn F d k i)
    (messages : (pSpec S).Messages) (i : Fin k) (z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec f messages)
      (queryInput F S d k oSpec i z) =
        pure (CompPoly.CPolynomial.evalHorner z (f i).val) := rfl

/-- Answer a virtual batch query by combining the input evaluations. -/
def queryBatch (s : S) (z : F) :
    OracleComp (oSpec + ([OStmtIn F d k]ₒ + [(pSpec S).Message]ₒ)) F := do
  let values ← (List.finRange k).mapM fun i => do
    let v ← queryInput F S d k oSpec i z
    pure (G s i * v)
  pure values.sum

omit [DecidableEq F] in
/-- Materializing a virtual query gives the weighted sum of evaluations. -/
theorem simulateQ_queryBatch (f : ∀ i, OStmtIn F d k i)
    (messages : (pSpec S).Messages) (s : S) (z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec f messages)
      (queryBatch F S d k G oSpec s z) =
        pure (∑ i, G s i * CompPoly.CPolynomial.evalHorner z (f i).val) := by
  simp only [queryBatch, simulateQ_bind, simulateQ_queryInput, simulateQ_list_mapM,
    List.mapM_pure, pure_bind, simulateQ_pure]
  congr 1

/-- Evaluation-only simulation of the batched polynomial oracle. -/
def outputSimulation : OracleOutputSimulation oSpec (OStmtIn F d k)
    (QuotientZeroTest.OStmtIn F d) (pSpec S) where
  materializeOutput chals f _ _ := batch hd f (G (chals ⟨0, rfl⟩))
  simulateOutputQuery chals q := queryBatch F S d k G oSpec (chals ⟨0, rfl⟩) q.2
  simulateOutputQuery_eq chals f messages q := by
    rcases q with ⟨u, z⟩
    change simulateQ (OracleInterface.simOracle2 oSpec f messages)
      (queryBatch F S d k G oSpec (chals ⟨0, rfl⟩) z) =
        pure (FiniteDomainQuotient.eval (batch hd f (G (chals ⟨0, rfl⟩))) z)
    rw [simulateQ_queryBatch, FiniteDomainQuotient.eval_eq, batch_toPoly,
      Polynomial.generatorBatch_eval]
    simp only [CompPoly.CPolynomial.eval_horner_eq_eval, CompPoly.CPolynomial.eval_toPoly]

/-- Forward the uniform challenge and expose the virtual batch without additional checks. -/
def oracleVerifier : OracleVerifier oSpec Unit (OStmtIn F d k)
    Unit (QuotientZeroTest.OStmtIn F d) (pSpec S) where
  verify _ _ := pure ()
  outputOracle := .inr (outputSimulation F S d k G hd oSpec)

/-- Materialization returns exactly the computable batch at the transcript challenge. -/
theorem oracleVerifier_toVerifier (stmt : Unit × ∀ i, OStmtIn F d k i)
    (tr : (pSpec S).FullTranscript) :
    (oracleVerifier F S d k G hd oSpec).toVerifier.verify stmt tr =
      pure (output F S d k G hd stmt (tr 0)) := by
  simp only [OracleVerifier.toVerifier, oracleVerifier, outputSimulation]
  erw [simulateQ_optionT_pure]
  rfl

/-- The forwarding stage has an always-true guard. -/
def guardedForm : (oracleVerifier F S d k G hd oSpec).toVerifier.GuardedForm where
  check _ _ := true
  out stmt tr := output F S d k G hd stmt (tr 0)
  verify_eq stmt tr := oracleVerifier_toVerifier F S d k G hd oSpec stmt tr

/-- The honest prover records the received challenge and computes the output polynomial. -/
def oracleProver : OracleProver oSpec Unit (OStmtIn F d k) Unit
    Unit (QuotientZeroTest.OStmtIn F d) Unit (pSpec S) where
  PrvState _ := (Fin k → Poly F d) × (Fin k → F)
  input x := (x.1.2, 0)
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun s => pure (fun seed => (s.1, G seed))
  output s := pure (((), fun _ => batch hd s.1 s.2), ())

instance : (oracleProver F S d k G hd oSpec).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- Generator batching as a one-challenge oracle reduction. -/
def oracleReduction : OracleReduction oSpec Unit (OStmtIn F d k) Unit
    Unit (QuotientZeroTest.OStmtIn F d) Unit (pSpec S) :=
  ⟨oracleProver F S d k G hd oSpec, oracleVerifier F S d k G hd oSpec⟩

/-- Extraction retains the unique witness; the oracle family is fixed in the statement. -/
def rbrExtractor : Extractor.RoundByRound oSpec (Unit × ∀ i, OStmtIn F d k i)
    Unit Unit (pSpec S) (fun _ => Unit) where
  extractIn _ w := w
  extractMid _ _ _ _ := ()
  extractOut _ _ _ := ()

variable [SampleableType S]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Knowledge means all inputs vanish before the challenge, and the batch vanishes afterwards. -/
def knowledgeStateFunction : (oracleVerifier F S d k G hd oSpec).toVerifier.KnowledgeStateFunction
    init impl (relIn F D d k) (relOut F D d) (rbrExtractor F S d k oSpec) where
  toFun
    | 0 => fun stmt _ _ => ∀ i, Polynomial.ZeroOn D.points (stmt.2 i).val.toPoly
    | 1 => fun stmt tr _ =>
      Polynomial.ZeroOn D.points (batch hd stmt.2 (G (tr ⟨0, by decide⟩))).val.toPoly
  toFun_empty _ _ h := h
  toFun_next | ⟨0, _⟩ => fun h => nomatch h
  toFun_full stmt tr _ h := by
    exact ((guardedForm F S d k G hd oSpec).check_and_of_prEvent_pos h).2

/-- Perfect completeness for every ambient oracle implementation and initial state. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction F S d k G hd oSpec).perfectCompleteness init impl
      (relIn F D d k) (relOut F D d) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit hf x hx
  rw [Reduction.run_run_eq_bind] at hx
  simp only [oracleReduction, OracleReduction.toReduction] at hx
  have hpr : (oracleProver F S d k G hd oSpec).run stmt wit = (do
      let s ← (pSpec S).getChallenge ⟨0, rfl⟩
      pure ((default : (pSpec S).Transcript 0).concat (m := (0 : Fin 1)) s,
        (output F S d k G hd stmt s, ()))) := by
    simp [Prover.run, Prover.runToRound, Fin.induction, Fin.induction.go,
      Prover.processRound, oracleProver, ProtocolSpec.getChallenge, Fin.vcons, Fin.dcons, output]
  rw [hpr] at hx
  simp only [bind_assoc, pure_bind, Verifier.run, oracleVerifier_toVerifier,
    OptionT.run_pure, liftComp_pure, Option.map_some, support_bind, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨s, _, rfl⟩ := hx
  refine ⟨_, rfl, ?_, rfl⟩
  change Polynomial.ZeroOn D.points (batch hd stmt.2 (G s)).val.toPoly
  rw [batch_toPoly]
  exact Polynomial.zeroOn_generatorBatch hf (G s)

variable [Fintype S] [Nonempty S]

omit [Fintype S] in
/-- A pointwise zero-evasion bound gives a fixed-prefix knowledge certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith_of_prob_le (ε : ℝ≥0)
    (hG : ∀ v : Fin k → F, v ≠ 0 →
      Pr{let s ← $ᵗ S}[dotProduct (G s) v = 0] ≤ (ε : ℝ≥0∞)) :
    (oracleVerifier F S d k G hd oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn F D d k) (relOut F D d) (fun _ => Unit) (rbrExtractor F S d k oSpec)
      (knowledgeStateFunction F S D d k G hd oSpec init impl) (fun _ => ε) := by
  intro stmt i tr
  obtain ⟨i, hi⟩ := i
  fin_cases i
  change Pr{let s ← $ᵗ S}[∃ _ : Unit,
    ¬ (∀ j, Polynomial.ZeroOn D.points (stmt.2 j).val.toPoly) ∧
      Polynomial.ZeroOn D.points (batch hd stmt.2 (G s)).val.toPoly] ≤ _
  simp only [exists_const]
  by_cases hf : ∀ j, Polynomial.ZeroOn D.points (stmt.2 j).val.toPoly
  · simp [hf]
  · simp only [hf, not_false_eq_true, true_and]
    simpa only [Polynomial.generatorBatch, CompPoly.CPolynomial.toPoly_sum,
      CompPoly.CPolynomial.toPoly_smul] using
      Polynomial.prob_zeroOn_generatorBatch_le_of_pointwise G hG hf

/-- A zero-evading generator hides each fixed false family with probability at most `ε`. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith (ε : unitInterval)
    (hG : IsZeroEvadingGenerator G ε) :
    (oracleVerifier F S d k G hd oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn F D d k) (relOut F D d) (fun _ => Unit) (rbrExtractor F S d k oSpec)
      (knowledgeStateFunction F S D d k G hd oSpec init impl)
      (fun _ => unitInterval.toNNReal ε) := by
  apply oracleVerifier_rbrKnowledgeSoundnessWith_of_prob_le
  intro v hv
  rw [← ENNReal.ofReal_coe_nnreal]
  apply le_trans (le_sSup ?_) hG
  exact ⟨v, hv, rfl⟩

/-- Existential form of the named fixed-prefix knowledge certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundness (ε : unitInterval)
    (hG : IsZeroEvadingGenerator G ε) :
    (oracleVerifier F S d k G hd oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn F D d k) (relOut F D d) (fun _ => unitInterval.toNNReal ε) :=
  ⟨_, rbrExtractor F S d k oSpec, knowledgeStateFunction F S D d k G hd oSpec init impl,
    oracleVerifier_rbrKnowledgeSoundnessWith F S D d k G hd oSpec init impl ε hG⟩

end GeneratorBatch
