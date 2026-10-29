/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PowerBatch
public import ArkLib.ProofSystem.Component.QuotientZeroTest

/-!
# Power batching of finite-domain zero tests

A single uniform challenge combines a fixed family of degree-`< d` polynomials with
coefficients `1, α, …, α^(k-1)`. The virtual output oracle answers an evaluation query by
querying each input at the same point and combining the answers. Its materialized value is
a computable polynomial in the existing quotient zero test's inclusive degree-`≤ d` type.
Thus the output relation is exactly that test's input relation, without retaining extra
statement data. The stronger strict degree bound is preserved when `0 < d`, including an
empty family. All witnesses are `Unit`; the fixed-prefix knowledge error is `(k - 1) / |F|`.
-/

@[expose] public section

open OracleSpec OracleComp OracleQuery ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory

namespace PowerBatch

variable (F : Type) [Field F] [DecidableEq F]

/-- Strictly degree-bounded input polynomials expose evaluation queries. -/
instance (d : ℕ) : OracleInterface (Poly F d) where
  Query := F
  toOC.spec := fun _ => F
  toOC.impl z := do return CompPoly.CPolynomial.evalHorner z (← read).val

/-- One verifier challenge, with no prover messages. -/
@[reducible] def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[F]⟩

instance : ∀ i, OracleInterface ((pSpec F).Message i)
  | ⟨0, h⟩ => nomatch h

instance [SampleableType F] : ∀ i, SampleableType ((pSpec F).Challenge i)
  | ⟨0, _⟩ => inferInstanceAs (SampleableType F)

variable (D : QuotientZeroTest.Domain F) (d k : ℕ)

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
def output (stmt : Unit × ∀ i, OStmtIn F d k i) (α : F) :
    Unit × ∀ i, QuotientZeroTest.OStmtIn F d i :=
  ((), fun _ => batch hd stmt.2 α)

/-- Query one member of the fixed input family. -/
def queryInput (i : Fin k) (z : F) :
    OracleComp (oSpec + ([OStmtIn F d k]ₒ + [(pSpec F).Message]ₒ)) F :=
  liftM <| OracleSpec.query
    (show (oSpec + ([OStmtIn F d k]ₒ + [(pSpec F).Message]ₒ)).Domain from
      Sum.inr (Sum.inl ⟨i, z⟩))

omit [DecidableEq F] in
/-- Input simulation evaluates the corresponding computable polynomial. -/
theorem simulateQ_queryInput (f : ∀ i, OStmtIn F d k i)
    (messages : (pSpec F).Messages) (i : Fin k) (z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec f messages)
      (queryInput F d k oSpec i z) =
        pure (CompPoly.CPolynomial.evalHorner z (f i).val) := rfl

/-- Answer a virtual batch query by combining the input evaluations. -/
def queryBatch (α z : F) :
    OracleComp (oSpec + ([OStmtIn F d k]ₒ + [(pSpec F).Message]ₒ)) F := do
  let values ← (List.finRange k).mapM fun i => do
    let v ← queryInput F d k oSpec i z
    pure (α ^ i.val * v)
  pure values.sum

omit [DecidableEq F] in
/-- Materializing a virtual query gives the power-weighted sum of evaluations. -/
theorem simulateQ_queryBatch (f : ∀ i, OStmtIn F d k i)
    (messages : (pSpec F).Messages) (α z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec f messages)
      (queryBatch F d k oSpec α z) =
        pure (∑ i, α ^ i.val * CompPoly.CPolynomial.evalHorner z (f i).val) := by
  simp only [queryBatch, simulateQ_bind, simulateQ_queryInput, simulateQ_list_mapM,
    List.mapM_pure, pure_bind, simulateQ_pure]
  congr 1

/-- Evaluation-only simulation of the batched polynomial oracle. -/
def outputSimulation : OracleOutputSimulation oSpec (OStmtIn F d k)
    (QuotientZeroTest.OStmtIn F d) (pSpec F) where
  materializeOutput chals f _ _ := batch hd f (chals ⟨0, rfl⟩)
  simulateOutputQuery chals q := queryBatch F d k oSpec (chals ⟨0, rfl⟩) q.2
  simulateOutputQuery_eq chals f messages q := by
    rcases q with ⟨u, z⟩
    change simulateQ (OracleInterface.simOracle2 oSpec f messages)
      (queryBatch F d k oSpec (chals ⟨0, rfl⟩) z) =
        pure (FiniteDomainQuotient.eval (batch hd f (chals ⟨0, rfl⟩)) z)
    rw [simulateQ_queryBatch, FiniteDomainQuotient.eval_eq, batch_toPoly,
      Polynomial.powerBatch_eval]
    simp only [CompPoly.CPolynomial.eval_horner_eq_eval, CompPoly.CPolynomial.eval_toPoly]

/-- Forward the uniform challenge and expose the virtual batch without additional checks. -/
def oracleVerifier : OracleVerifier oSpec Unit (OStmtIn F d k)
    Unit (QuotientZeroTest.OStmtIn F d) (pSpec F) where
  verify _ _ := pure ()
  outputOracle := .inr (outputSimulation F d k hd oSpec)

/-- Materialization returns exactly the computable batch at the transcript challenge. -/
theorem oracleVerifier_toVerifier (stmt : Unit × ∀ i, OStmtIn F d k i)
    (tr : (pSpec F).FullTranscript) :
    (oracleVerifier F d k hd oSpec).toVerifier.verify stmt tr =
      pure (output F d k hd stmt (tr 0)) := by
  simp only [OracleVerifier.toVerifier, oracleVerifier, outputSimulation]
  erw [simulateQ_optionT_pure]
  rfl

/-- The forwarding stage has an always-true guard. -/
def guardedForm : (oracleVerifier F d k hd oSpec).toVerifier.GuardedForm where
  check _ _ := true
  out stmt tr := output F d k hd stmt (tr 0)
  verify_eq stmt tr := oracleVerifier_toVerifier F d k hd oSpec stmt tr

/-- The honest prover records the received challenge and computes the output polynomial. -/
def oracleProver : OracleProver oSpec Unit (OStmtIn F d k) Unit
    Unit (QuotientZeroTest.OStmtIn F d) Unit (pSpec F) where
  PrvState _ := (Fin k → Poly F d) × F
  input x := (x.1.2, 0)
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun s => pure (fun α => (s.1, α))
  output s := pure (output F d k hd ((), s.1) s.2, ())

instance : (oracleProver F d k hd oSpec).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- Power batching as a one-challenge oracle reduction. -/
def oracleReduction : OracleReduction oSpec Unit (OStmtIn F d k) Unit
    Unit (QuotientZeroTest.OStmtIn F d) Unit (pSpec F) :=
  ⟨oracleProver F d k hd oSpec, oracleVerifier F d k hd oSpec⟩

/-- Extraction retains the unique witness; the oracle family is fixed in the statement. -/
def rbrExtractor : Extractor.RoundByRound oSpec (Unit × ∀ i, OStmtIn F d k i)
    Unit Unit (pSpec F) (fun _ => Unit) where
  extractIn _ w := w
  extractMid _ _ _ _ := ()
  extractOut _ _ _ := ()

variable [SampleableType F]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Knowledge means all inputs vanish before the challenge, and the batch vanishes afterwards. -/
def knowledgeStateFunction : (oracleVerifier F d k hd oSpec).toVerifier.KnowledgeStateFunction
    init impl (relIn F D d k) (relOut F D d) (rbrExtractor F d k oSpec) where
  toFun
    | 0 => fun stmt _ _ => ∀ i, Polynomial.ZeroOn D.points (stmt.2 i).val.toPoly
    | 1 => fun stmt tr _ =>
      Polynomial.ZeroOn D.points (batch hd stmt.2 (tr ⟨0, by decide⟩)).val.toPoly
  toFun_empty _ _ h := h
  toFun_next | ⟨0, _⟩ => fun h => nomatch h
  toFun_full stmt tr _ h := by
    exact ((guardedForm F d k hd oSpec).check_and_of_prEvent_pos h).2

/-- Perfect completeness for every ambient oracle implementation and initial state. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction F d k hd oSpec).perfectCompleteness init impl
      (relIn F D d k) (relOut F D d) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit hf x hx
  rw [Reduction.run_run_eq_bind] at hx
  simp only [oracleReduction, OracleReduction.toReduction] at hx
  have hpr : (oracleProver F d k hd oSpec).run stmt wit = (do
      let α ← (pSpec F).getChallenge ⟨0, rfl⟩
      pure ((default : (pSpec F).Transcript 0).concat (m := (0 : Fin 1)) α,
        (output F d k hd stmt α, ()))) := by
    simp [Prover.run, Prover.runToRound, Fin.induction, Fin.induction.go,
      Prover.processRound, oracleProver, ProtocolSpec.getChallenge, Fin.vcons, Fin.dcons, output]
  rw [hpr] at hx
  simp only [bind_assoc, pure_bind, Verifier.run, oracleVerifier_toVerifier,
    OptionT.run_pure, liftComp_pure, Option.map_some, support_bind, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨α, _, rfl⟩ := hx
  refine ⟨_, rfl, ?_, rfl⟩
  change Polynomial.ZeroOn D.points (batch hd stmt.2 α).val.toPoly
  rw [batch_toPoly]
  exact Polynomial.zeroOn_powerBatch hf α

variable [Fintype F]

/-- Every fixed false family is hidden by a fresh power-batching challenge with probability
at most `(k - 1) / |F|`. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith :
    (oracleVerifier F d k hd oSpec).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn F D d k) (relOut F D d) (fun _ => Unit) (rbrExtractor F d k oSpec)
      (knowledgeStateFunction F D d k hd oSpec init impl)
      (fun _ => ((k - 1 : ℕ) : ℝ≥0) / Fintype.card F) := by
  intro stmt i tr
  obtain ⟨i, hi⟩ := i
  fin_cases i
  change Pr{let α ← $ᵗ F}[∃ _ : Unit,
    ¬ (∀ j, Polynomial.ZeroOn D.points (stmt.2 j).val.toPoly) ∧
      Polynomial.ZeroOn D.points (batch hd stmt.2 α).val.toPoly] ≤ _
  simp only [exists_const]
  by_cases hf : ∀ j, Polynomial.ZeroOn D.points (stmt.2 j).val.toPoly
  · simp [hf]
  · simp only [hf, not_false_eq_true, true_and, batch_toPoly]
    have hbound := Polynomial.prob_zeroOn_powerBatch_le hf
    have hdenom : (Fintype.card F : ℝ≥0) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simpa only [ENNReal.coe_div hdenom, ENNReal.coe_natCast] using hbound

/-- Existential form of the named fixed-prefix knowledge certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCase :
    (oracleVerifier F d k hd oSpec).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (relIn F D d k) (relOut F D d)
      (fun _ => ((k - 1 : ℕ) : ℝ≥0) / Fintype.card F) :=
  ⟨_, rbrExtractor F d k oSpec, knowledgeStateFunction F D d k hd oSpec init impl,
    oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith F D d k hd oSpec init impl⟩

end PowerBatch
