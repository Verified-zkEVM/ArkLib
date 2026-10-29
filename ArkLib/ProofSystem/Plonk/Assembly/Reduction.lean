/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Assembly.Data
public import ArkLib.ProofSystem.Plonk.SendWitness
public import ArkLib.ProofSystem.Plonk.GrandProduct.Completeness
public import ArkLib.ProofSystem.Plonk.GrandProduct.Security
public import ArkLib.ProofSystem.Plonk.Quotient.Reduction
public import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
public import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound
public import ArkLib.OracleReduction.Security.GuardedBridges

/-! # The Plonk polynomial oracle reduction

The wire reveal, joint-challenge grand product, power batch and guarded quotient zero test
form a single oracle reduction. The quotient stage includes evaluation and the terminal guard.
-/

@[expose] public section

namespace Plonk.Assembly

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

variable (F : Type) [Field F] [DecidableEq F] (n : ℕ)

/-- Public statement types at the four stage boundaries. -/
def Stmt : Fin 5 → Type
  | 0 => Unit
  | 1 => Unit
  | 2 => F × F
  | 3 => F × F
  | 4 => F × F

/-- Oracle indices at the four stage boundaries. -/
def OracleIdx : Fin 5 → Type
  | 0 => Fin 0
  | 1 => Fin 3
  | 2 => Fin 3 ⊕ (Unit ⊕ Fin 3)
  | 3 => (Fin 3 ⊕ (Unit ⊕ Fin 3)) ⊕ Unit
  | 4 => (Fin 3 ⊕ (Unit ⊕ Fin 3)) ⊕ Unit

/-- Retained and virtual polynomial oracles at each boundary. -/
def OStmt : (i : Fin 5) → OracleIdx i → Type
  | 0 => SendWitness.OStmtIn
  | 1 => GrandProduct.OStmtIn F n
  | 2 => GrandProduct.OStmtOut F n
  | 3 => Batch.OStmtOut F n
  | 4 => Batch.OStmtOut F n

instance : ∀ i j, OracleInterface (OStmt F n i j)
  | 0 => inferInstanceAs (∀ j, OracleInterface (SendWitness.OStmtIn j))
  | 1 => inferInstanceAs (∀ j, OracleInterface (GrandProduct.OStmtIn F n j))
  | 2 => inferInstanceAs (∀ j, OracleInterface (GrandProduct.OStmtOut F n j))
  | 3 => inferInstanceAs (∀ j, OracleInterface (Batch.OStmtOut F n j))
  | 4 => inferInstanceAs (∀ j, OracleInterface (Batch.OStmtOut F n j))

/-- Only the input has a private polynomial table. -/
def Wit : Fin 5 → Type
  | 0 => Fin 3 → GeneratorBatch.Poly F n
  | 1 => Unit
  | 2 => Unit
  | 3 => Unit
  | 4 => Unit

/-- The stages send respectively one, two, one and two messages or challenges. -/
def rounds : Fin 4 → ℕ := ![1, 2, 1, 2]

variable {F n} {m : ℕ} (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 2 ≤ n)
  (cs : ConstraintSystem F m n)
  (L : CosetLabels (EvaluationDomain.primitiveRoot ω hω)) (pi : GeneratorBatch.Poly F n)

/-- Stage protocol specifications in execution order. -/
def stageSpec : (i : Fin 4) → ProtocolSpec (rounds i)
  | 0 => SendWitness.pSpec F n
  | 1 => GrandProduct.pSpec F n
  | 2 => Batch.pSpec F
  | 3 => Quotient.pSpec ω hω hn

instance : ∀ i j, OracleInterface ((stageSpec ω hω hn i).Message j)
  | 0 => inferInstanceAs (∀ j, OracleInterface ((SendWitness.pSpec F n).Message j))
  | 1 => inferInstanceAs (∀ j, OracleInterface ((GrandProduct.pSpec F n).Message j))
  | 2 => inferInstanceAs (∀ j, OracleInterface ((Batch.pSpec F).Message j))
  | 3 => inferInstanceAs (∀ j, OracleInterface ((Quotient.pSpec ω hω hn).Message j))

instance [SampleableType F] : ∀ i j, SampleableType ((stageSpec ω hω hn i).Challenge j)
  | 0 => inferInstanceAs (∀ j, SampleableType ((SendWitness.pSpec F n).Challenge j))
  | 1 => inferInstanceAs (∀ j, SampleableType ((GrandProduct.pSpec F n).Challenge j))
  | 2 => inferInstanceAs (∀ j, SampleableType ((Batch.pSpec F).Challenge j))
  | 3 => inferInstanceAs (∀ j, SampleableType ((Quotient.pSpec ω hω hn).Challenge j))

/-- The exact gate/copy, residual, batch and accepting relations. -/
def rel : (i : Fin 5) → Set ((Stmt F i × ∀ j, OStmt F n i j) × Wit F n i)
  | 0 => SendWitness.relIn ω hω cs pi
  | 1 => GrandProduct.relIn ω hω cs pi
  | 2 => GrandProduct.relOut ω hω
  | 3 => Batch.relOut ω hω
  | 4 => Quotient.relOut

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The actual oracle reductions, including their honest provers. -/
def stages : (i : Fin 4) → OracleReduction oSpec
    (Stmt F i.castSucc) (OStmt F n i.castSucc) (Wit F n i.castSucc)
    (Stmt F i.succ) (OStmt F n i.succ) (Wit F n i.succ) (stageSpec ω hω hn i)
  | 0 => SendWitness.oracleReduction oSpec
  | 1 => GrandProduct.oracleReduction ω hω hn cs L pi oSpec
  | 2 => Batch.oracleReduction oSpec
  | 3 => Quotient.oracleReduction ω hω hn oSpec

/-- The six-round polynomial oracle protocol. -/
abbrev pSpec := ProtocolSpec.seqCompose (stageSpec ω hω hn)

/-- The full Plonk reduction, retaining every earlier oracle through its terminal guard. -/
def oracleReduction := OracleReduction.seqCompose (Stmt F) (OStmt F n) (Wit F n)
  (stages ω hω hn cs L pi oSpec)

/-- The named deterministic guards of all four stages. -/
def stageGuards : ∀ i, ((stages ω hω hn cs L pi oSpec i).verifier.toVerifier).GuardedForm
  | 0 => SendWitness.guardedForm oSpec
  | 1 => GrandProduct.guardedForm ω hω hn cs L pi oSpec
  | 2 => Batch.guardedForm oSpec
  | 3 => Quotient.guardedForm ω hω hn oSpec

/-- The composed verifier retains the terminal quotient guard. -/
def guardedForm : (oracleReduction ω hω hn cs L pi oSpec).verifier.toVerifier.GuardedForm :=
  OracleVerifier.seqComposeGuardedForm (Stmt F) (OStmt F n)
    (stageGuards ω hω hn cs L pi oSpec)

/-- Materialization of the composed verifier is exactly the scalar quotient identity. -/
theorem oracleVerifier_toVerifier (stmt : Unit × ∀ i, SendWitness.OStmtIn i)
    (tr : (pSpec ω hω hn).FullTranscript) :
    (oracleReduction ω hω hn cs L pi oSpec).verifier.toVerifier.verify stmt tr =
      let gp := GrandProduct.output ω hω hn cs L pi (tr ⟨0, by decide⟩)
        (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩)
      let out := Batch.output gp (tr ⟨3, by decide⟩)
      let z : F := tr ⟨5, by decide⟩
      if FiniteDomainQuotient.eval (out.2 (.inr ())) z =
          FiniteDomainQuotient.eval (tr ⟨4, by decide⟩) z * (z ^ n - 1)
      then pure out else failure := by
  refine ((guardedForm ω hω hn cs L pi oSpec).verify_eq stmt tr).trans ?_
  let out := Batch.output
    (GrandProduct.output ω hω hn cs L pi (tr ⟨0, by decide⟩)
      (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩)) (tr ⟨3, by decide⟩)
  let z : F := tr ⟨5, by decide⟩
  change (if (true && (true && (true &&
    (decide (FiniteDomainQuotient.eval (out.2 (.inr ())) z =
      FiniteDomainQuotient.eval (tr ⟨4, by decide⟩) z * (z ^ n - 1)) && true)))) = true
    then pure out else failure) = _
  simp only [Bool.true_and, Bool.and_true, decide_eq_true_eq]
  rfl

/-- Intermediate extraction witnesses for the named stage certificates. -/
def StageWitMid : (i : Fin 4) → Fin (rounds i + 1) → Type
  | 0 => SendWitness.WitMid (F := F) (n := n)
  | 1 => fun _ => Unit
  | 2 => fun _ => Unit
  | 3 => fun _ => Unit × Unit

/-- Stage extractors preserve the first revealed table through backward composition. -/
def stageExtractors : (i : Fin 4) → Extractor.RoundByRound oSpec
    (Stmt F i.castSucc × ∀ j, OStmt F n i.castSucc j)
    (Wit F n i.castSucc) (Wit F n i.succ) (stageSpec ω hω hn i)
    (StageWitMid (F := F) (n := n) i)
  | 0 => SendWitness.rbrExtractor oSpec
  | 1 => GrandProduct.rbrExtractor oSpec
  | 2 => Batch.rbrExtractor oSpec
  | 3 => Quotient.rbrExtractor ω hω hn oSpec

/-- The designated backward composition of the four stage extractors. -/
def rbrExtractor := Extractor.RoundByRound.seqCompose
  (fun i => Stmt F i × ∀ j, OStmt F n i j) (Wit F n)
  (fun i => (stages ω hω hn cs L pi oSpec i).verifier.toVerifier)
  (stageGuards ω hω hn cs L pi oSpec) (stageExtractors ω hω hn oSpec)

variable [SampleableType F] {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Named fixed-prefix knowledge functions at each stage. -/
def stageKnowledge : ∀ i,
    (stages ω hω hn cs L pi oSpec i).verifier.toVerifier.KnowledgeStateFunction
      init impl (rel ω hω cs pi i.castSucc) (rel ω hω cs pi i.succ)
      (stageExtractors ω hω hn oSpec i)
  | 0 => SendWitness.knowledgeStateFunction ω hω cs pi oSpec init impl
  | 1 => GrandProduct.knowledgeStateFunction ω hω hn cs L pi oSpec init impl
  | 2 => Batch.knowledgeStateFunction ω hω oSpec init impl
  | 3 => Quotient.knowledgeStateFunction ω hω hn oSpec init impl

/-- The named knowledge state of the full oracle verifier. -/
def knowledgeStateFunction := OracleVerifier.seqComposeKnowledgeStateFunction
  (Stmt F) (OStmt F n) (Wit F n) (rel ω hω cs pi)
  (fun i => (stages ω hω hn cs L pi oSpec i).verifier)
  (stageGuards ω hω hn cs L pi oSpec) (stageExtractors ω hω hn oSpec)
  (stageKnowledge ω hω hn cs L pi oSpec init impl)

variable [Fintype F]

/-- The exact error charged at each component challenge. Real division is noncomputable. -/
noncomputable def stageError : (i : Fin 4) → (stageSpec ω hω hn i).ChallengeIdx → ℝ≥0
  | 0 => fun _ => 0
  | 1 => fun _ => ((3 * n - 1 : ℕ) : ℝ≥0) / Fintype.card F
  | 2 => fun _ => 2 / Fintype.card F
  | 3 => fun _ => (GrandProduct.residualDegree n : ℝ≥0) / Fintype.card F

/-- Each global challenge inherits its component's fixed-prefix error, using real division. -/
noncomputable def error (i : (pSpec ω hω hn).ChallengeIdx) : ℝ≥0 :=
  let j := seqComposeChallengeIdxToSigma i
  stageError ω hω hn j.1 j.2

/-- Named fixed-prefix knowledge security of the entire oracle reduction. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith :
    (oracleReduction ω hω hn cs L pi oSpec).verifier.toVerifier.rbrKnowledgeSoundnessWith
      init impl (rel ω hω cs pi 0)
        (rel ω hω cs pi 4) _ (rbrExtractor ω hω hn cs L pi oSpec)
        (knowledgeStateFunction ω hω hn cs L pi oSpec init impl) (error ω hω hn) := by
  change Verifier.rbrKnowledgeSoundnessWith init impl _ _
    (OracleVerifier.seqCompose (Stmt F) (OStmt F n)
      (fun i => (stages ω hω hn cs L pi oSpec i).verifier)).toVerifier _ _ _ _
  refine OracleVerifier.seqCompose_rbrKnowledgeSoundnessWith_of_guarded
    (Stmt F) (OStmt F n) (Wit F n) (rel ω hω cs pi)
    (fun i => (stages ω hω hn cs L pi oSpec i).verifier)
    (stageGuards ω hω hn cs L pi oSpec) (stageExtractors ω hω hn oSpec)
    (stageKnowledge ω hω hn cs L pi oSpec init impl) (stageError ω hω hn) ?_
  intro i
  fin_cases i
  · exact SendWitness.oracleVerifier_rbrKnowledgeSoundnessWith ω hω cs pi oSpec init impl
  · exact GrandProduct.oracleVerifier_rbrKnowledgeSoundnessWith ω hω hn cs L pi
      oSpec init impl
  · exact Batch.oracleVerifier_rbrKnowledgeSoundnessWith ω hω oSpec init impl
  · exact Quotient.oracleVerifier_rbrKnowledgeSoundnessWith ω hω hn oSpec init impl

/-- Completeness loss occurs only at the joint grand-product challenge. Real division is
noncomputable. -/
noncomputable def completenessError : Fin 4 → ℝ≥0 :=
  ![0, ((3 * n : ℕ) : ℝ≥0) / Fintype.card F, 0, 0]

/-- The composed honest prover is complete with failure at most `3n / |F|`. -/
theorem oracleReduction_completeness :
    (oracleReduction ω hω hn cs L pi oSpec).completeness init impl
      (rel ω hω cs pi 0) (rel ω hω cs pi 4)
      (((3 * n : ℕ) : ℝ≥0) / Fintype.card F) := by
  have h := Reduction.seqCompose_completeness_of_guarded_verifiers
    (fun i => Stmt F i × ∀ j, OStmt F n i j) (Wit F n) init impl
    (rel ω hω cs pi) (fun i => (stages ω hω hn cs L pi oSpec i).toReduction)
    (completenessError (F := F) (n := n))
    (by
      intro i
      fin_cases i
      · change (SendWitness.oracleProver (F := F) (n := n) oSpec).OutputIsPure
        infer_instance
      · change (GrandProduct.oracleProver ω hω hn cs L pi oSpec).OutputIsPure
        infer_instance
      · change (Batch.oracleProver (F := F) (n := n) oSpec).OutputIsPure
        infer_instance
      · change (Quotient.oracleReduction ω hω hn oSpec).prover.OutputIsPure
        infer_instance)
    (stageGuards ω hω hn cs L pi oSpec) (by
      intro i s
      fin_cases i
      · exact SendWitness.oracleReduction_perfectCompleteness ω hω cs pi oSpec (pure s) impl
      · exact GrandProduct.oracleReduction_completeness ω hω hn cs L pi oSpec (pure s) impl
      · exact Batch.oracleReduction_perfectCompleteness ω hω oSpec (pure s) impl
      · exact Quotient.oracleReduction_perfectCompleteness ω hω hn oSpec (pure s) impl)
  simpa only [oracleReduction, OracleReduction.completeness,
    OracleReduction.seqCompose_toReduction, completenessError, Fin.sum_univ_succ,
    Fin.reduceLast, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, zero_add] using h

omit [SampleableType F] in
/-- Summing the three challenge errors gives exactly `(7n - 3) / |F|`. -/
theorem sum_error : ∑ i, error ω hω hn i =
    ((7 * n - 3 : ℕ) : ℝ≥0) / Fintype.card F := by
  unfold error pSpec
  rw [sum_seqComposeChallengeIdxToSigma]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : Fintype.card ((stageSpec ω hω hn 1).ChallengeIdx) = 1 := by
    change Fintype.card {i : Fin 2 // !v[Direction.V_to_P, Direction.P_to_V] i =
      Direction.V_to_P} = 1
    decide
  have h2 : Fintype.card ((stageSpec ω hω hn 2).ChallengeIdx) = 1 := by
    change Fintype.card {i : Fin 1 // !v[Direction.V_to_P] i = Direction.V_to_P} = 1
    decide
  have h3 : Fintype.card ((stageSpec ω hω hn 3).ChallengeIdx) = 1 := by
    change Fintype.card {i : Fin 2 // !v[Direction.P_to_V, Direction.V_to_P] i =
      Direction.V_to_P} = 1
    decide
  simp only [Fin.reduceSucc, stageError]
  simpa only [stageError, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
    h1, h2, h3, one_smul, zero_add, ← add_assoc, GrandProduct.residualDegree] using
    error_sum n hn (Fintype.card F)

/-- The ordinary extractor returns the exact initially revealed table. -/
def transcriptExtractor : Extractor.Straightline oSpec
    (Unit × ∀ i, SendWitness.OStmtIn i) (Fin 3 → GeneratorBatch.Poly F n) Unit
    (pSpec ω hω hn) :=
  fun _ _ tr _ _ => pure (tr ⟨0, by decide⟩)

omit [SampleableType F] [Fintype F] in
/-- Folding the composed round-by-round extractor reads the initial table message. -/
theorem foldExtractor_eq : (rbrExtractor ω hω hn cs L pi oSpec).foldExtractor =
    transcriptExtractor ω hω hn oSpec := by
  rfl

/-- Ordinary knowledge security with the designated table extractor and exact total error. -/
theorem oracleVerifier_knowledgeSoundnessWith :
    (oracleReduction ω hω hn cs L pi oSpec).verifier.knowledgeSoundnessWith init impl
      (rel ω hω cs pi 0) (rel ω hω cs pi 4) (transcriptExtractor ω hω hn oSpec)
      (((7 * n - 3 : ℕ) : ℝ≥0) / Fintype.card F) := by
  have h := OracleVerifier.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith_of_guarded
    (guardedForm ω hω hn cs L pi oSpec) (knowledgeStateFunction ω hω hn cs L pi oSpec init impl)
    (oracleVerifier_rbrKnowledgeSoundnessWith ω hω hn cs L pi oSpec init impl)
  change (oracleReduction ω hω hn cs L pi oSpec).verifier.knowledgeSoundnessWith init impl
    (rel ω hω cs pi 0) (rel ω hω cs pi 4)
    (rbrExtractor ω hω hn cs L pi oSpec).foldExtractor (∑ i, error ω hω hn i) at h
  rw [sum_error ω hω hn] at h
  simpa only [foldExtractor_eq ω hω hn cs L pi oSpec] using h

end Plonk.Assembly
