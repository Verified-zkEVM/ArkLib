/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Protocol
public import ArkLib.ProofSystem.Spartan.Error

/-!
# Knowledge soundness of Spartan

The fixed-prefix certificate composes the named stage extractors. Its input relation is the
original R1CS relation. The guarded bridge folds this extractor along the actual transcript;
the only nontrivial input witness is recovered from the attached witness table.
-/

@[expose] public section

namespace Spartan

open OracleComp OracleSpec ProtocolSpec Realization
open scoped NNReal

variable {R : Type} [Field R] [DecidableEq R] [Fintype R] [SampleableType R]
    (sz : R1CS.Size) {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local notation "params" => PublicParams.forSize sz

local instance : ∀ i, OracleInterface (R1CS.OracleStatement R sz i) :=
  WitnessAttachment.sourceOracleInterface sz

namespace Assembly

/-- The intermediate witness families of the seven certificates. The sumcheck families are
selected from their proved existential certificates. -/
noncomputable def intermediateWitness : (i : Fin 7) → Fin (length sz i + 1) → Type
  | 0 => fun _ => R1CS.Witness R (params).toSizeR1CS
  | 1 => fun _ => Unit
  | 2 => FirstSumcheck.intermediateWitness (R := R) params oSpec init impl
  | 3 => fun _ => Unit
  | 4 => fun _ => Unit
  | 5 => SecondSumcheck.intermediateWitness (R := R) params oSpec init impl
  | 6 => fun _ => Unit

/-- Each named stage extractor, including the attachment's restriction of the sent table.
The sumcheck extractors use a nonconstructively selected proved certificate. -/
noncomputable def extractor : (i : Fin 7) → Extractor.RoundByRound oSpec
    (Statement (R := R) sz i.castSucc × (∀ j, Oracles (R := R) sz i.castSucc j))
    (Witness (R := R) sz i.castSucc) (Witness (R := R) sz i.succ)
    (stageSpec (R := R) sz i) (intermediateWitness (R := R) sz oSpec init impl i)
  | 0 => WitnessAttachment.rbrExtractor (R := R) sz oSpec
  | 1 => ZeroCheck.rbrExtractor params oSpec
  | 2 => FirstSumcheck.rbrExtractor params oSpec init impl
  | 3 => Extractor.RoundByRound.unit
  | 4 => Batching.rbrExtractor params oSpec
  | 5 => SecondSumcheck.rbrExtractor params oSpec init impl
  | 6 => Extractor.RoundByRound.unit

/-- Stage knowledge predicates for the retained relations. Their semantic sumcheck views and
chosen inner certificates are noncomputable. -/
noncomputable def knowledgeState : (i : Fin 7) →
    (stage (R := R) sz oSpec i).verifier.toVerifier.KnowledgeStateFunction init impl
      (relation (R := R) sz i.castSucc) (relation (R := R) sz i.succ)
      (extractor (R := R) sz oSpec init impl i)
  | 0 => WitnessAttachment.knowledgeStateFunction (R := R) sz oSpec init impl
  | 1 => ZeroCheck.knowledgeStateFunction params oSpec
  | 2 => FirstSumcheck.knowledgeStateFunction params oSpec init impl
  | 3 => SendEvaluations.knowledgeStateFunction params oSpec init impl
  | 4 => Batching.knowledgeStateFunction params oSpec init impl
  | 5 => SecondSumcheck.knowledgeStateFunction params oSpec init impl
  | 6 => Terminal.knowledgeStateFunction params oSpec init impl

/-- Per-challenge errors, with real division used only in the security statement. -/
noncomputable def error : (i : Fin 7) → (stageSpec (R := R) sz i).ChallengeIdx → ℝ≥0
  | 0 => fun _ => 0
  | 1 => fun _ => ((params).ℓ_m : ℝ≥0) / Fintype.card R
  | 2 => fun _ => 3 / (Fintype.card R : ℝ≥0)
  | 3 => fun _ => 0
  | 4 => fun _ => 1 / (Fintype.card R : ℝ≥0)
  | 5 => fun _ => 2 / (Fintype.card R : ℝ≥0)
  | 6 => fun _ => 0

/-- Each stage satisfies its named fixed-prefix certificate at the displayed error. -/
theorem stageCertificate (i : Fin 7) :
    (stage (R := R) sz oSpec i).verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (relation (R := R) sz i.castSucc) (relation (R := R) sz i.succ)
      (intermediateWitness (R := R) sz oSpec init impl i)
      (extractor (R := R) sz oSpec init impl i) (knowledgeState (R := R) sz oSpec init impl i)
      (error sz i) := by
  fin_cases i
  · exact WitnessAttachment.rbrKnowledgeSoundnessWorstCaseWith sz oSpec init impl
  · exact ZeroCheck.challenge_rbrKnowledgeSoundnessWorstCaseWith params oSpec
  · exact FirstSumcheck.rbrKnowledgeSoundnessWorstCaseWith params oSpec init impl
  · exact SendEvaluations.verifier_rbrKnowledgeSoundnessWorstCaseWith params oSpec init impl
  · exact Batching.batch_rbrKnowledgeSoundnessWorstCaseWith (F := R) params oSpec init impl
  · exact SecondSumcheck.rbrKnowledgeSoundnessWorstCaseWith params oSpec init impl
  · exact Terminal.finalVerifier_rbrKnowledgeSoundnessWorstCaseWith params oSpec init impl

end Assembly

/-- The composed backward extractor. Noncomputability is confined to the semantic guards and
chosen sumcheck certificates; witness attachment reads the actual sent table. -/
noncomputable def rbrExtractor :=
  Extractor.RoundByRound.seqCompose
    (fun i => Assembly.Statement (R := R) sz i × (∀ j, Assembly.Oracles (R := R) sz i j))
    (Assembly.Witness (R := R) sz)
    (fun i => (Assembly.stage (R := R) sz oSpec i).verifier.toVerifier)
    (Assembly.stageGuardedForm (R := R) sz oSpec) (Assembly.extractor (R := R) sz oSpec init impl)

/-- The composed knowledge invariant, retaining every earlier rejecting guard.
The constituent guards and sumcheck certificate choices are noncomputable. -/
noncomputable def knowledgeStateFunction :=
  OracleVerifier.seqComposeKnowledgeStateFunction (Assembly.Statement (R := R) sz)
    (Assembly.Oracles (R := R) sz) (Assembly.Witness (R := R) sz) (Assembly.relation (R := R) sz)
    (fun i => (Assembly.stage (R := R) sz oSpec i).verifier)
    (Assembly.stageGuardedForm (R := R) sz oSpec)
    (Assembly.extractor (R := R) sz oSpec init impl)
    (Assembly.knowledgeState (R := R) sz oSpec init impl)

/-- The challenge schedule routes each challenge to its stage's error. Real-valued bounds
are noncomputable and do not occur in the executable protocol. -/
noncomputable def challengeError (i : (pSpec (R := R) sz).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma i
  Assembly.error (R := R) sz ij.1 ij.2

/-- The seven-stage verifier has a named fixed-prefix knowledge certificate for the original
R1CS relation, with each combined challenge charged exactly its component error. -/
theorem rbrKnowledgeSoundnessWorstCaseWith :
    (oracleReduction (R := R) sz oSpec).verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (WitnessAttachment.relIn sz) (Terminal.relOut params) _
      (rbrExtractor (R := R) sz oSpec init impl)
      (knowledgeStateFunction (R := R) sz oSpec init impl)
      (challengeError (R := R) sz) := by
  exact OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded
    (Assembly.Statement (R := R) sz) (Assembly.Oracles (R := R) sz)
    (Assembly.Witness (R := R) sz) (Assembly.relation (R := R) sz)
    (fun i => (Assembly.stage (R := R) sz oSpec i).verifier)
    (Assembly.stageGuardedForm (R := R) sz oSpec)
    (Assembly.extractor (R := R) sz oSpec init impl)
    (Assembly.knowledgeState (R := R) sz oSpec init impl)
    (Assembly.error (R := R) sz) (Assembly.stageCertificate (R := R) sz oSpec init impl)

omit [DecidableEq R] [SampleableType R] in
/-- The routed challenge schedule sums to the exact Spartan error ledger. -/
theorem sum_challengeError :
    ∑ i, challengeError (R := R) sz i =
      totalError (params).ℓ_m (params).ℓ_n (Fintype.card R) := by
  have sumcheck (d n : ℕ) (e : ℝ≥0) :
      (∑ _ : (Sumcheck.Spec.pSpec R d n).ChallengeIdx, e) = n * e := by
    have h := sum_seqComposeChallengeIdxToSigma
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R d) (fun _ _ => e)
    have hc : Fintype.card (Sumcheck.Spec.SingleRound.pSpec R d).ChallengeIdx = 1 := by
      change Fintype.card (Sumcheck.Spec.SingleRound.pSpec ℤ 0).ChallengeIdx = 1
      decide
    simpa only [Finset.sum_const, Finset.card_univ, hc, one_smul, Fintype.card_fin,
      nsmul_eq_mul] using h
  unfold challengeError
  rw [sum_seqComposeChallengeIdxToSigma]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (∑ _ : (WitnessAttachment.pSpec (R := R) sz).ChallengeIdx, (0 : ℝ≥0)) +
    ((∑ _ : (_root_.ZeroCheck.pSpec R (params).ℓ_m).ChallengeIdx,
      ((params).ℓ_m : ℝ≥0) / Fintype.card R) +
    ((∑ _ : (Sumcheck.Spec.pSpec R 3 (params).ℓ_m).ChallengeIdx,
      3 / (Fintype.card R : ℝ≥0)) +
    ((∑ _ : (SendEvaluations.pSpec R).ChallengeIdx, (0 : ℝ≥0)) +
    ((∑ _ : (Batching.pSpec R).ChallengeIdx, 1 / (Fintype.card R : ℝ≥0)) +
    ((∑ _ : (Sumcheck.Spec.pSpec R 2 (params).ℓ_n).ChallengeIdx,
      2 / (Fintype.card R : ℝ≥0)) +
    ((∑ _ : (!p[] : ProtocolSpec 0).ChallengeIdx, (0 : ℝ≥0)) + 0)))))) = _
  simp only [Finset.sum_const_zero, add_zero, zero_add, sumcheck]
  have hz : Fintype.card (_root_.ZeroCheck.pSpec R (params).ℓ_m).ChallengeIdx = 1 :=
    Fintype.card_unique
  have hb : Fintype.card (Batching.pSpec R).ChallengeIdx = 1 := Fintype.card_unique
  simpa only [Finset.sum_const, Finset.card_univ, hz, hb, one_smul, add_assoc] using
    error_ledger (params).ℓ_m (params).ℓ_n (Fintype.card R)

/-- Folding the specified composed extractor gives ordinary knowledge soundness with error
`(4s + 2t + 1) / |R|` for satisfiability of the original R1CS instance. -/
theorem knowledgeSoundnessWith :
    (oracleReduction (R := R) sz oSpec).verifier.knowledgeSoundnessWith init impl
      (WitnessAttachment.relIn sz) (Terminal.relOut params)
      (rbrExtractor (R := R) sz oSpec init impl).foldExtractor
      (totalError (params).ℓ_m (params).ℓ_n (Fintype.card R)) := by
  rw [← sum_challengeError (R := R) sz]
  exact OracleVerifier.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWorstCaseWith_of_guarded
    (guardedForm (R := R) sz oSpec) (knowledgeStateFunction (R := R) sz oSpec init impl)
    (rbrKnowledgeSoundnessWorstCaseWith (R := R) sz oSpec init impl)

/-- Spartan is knowledge sound for the original R1CS relation with additive error
`(4s + 2t + 1) / |R|`. -/
theorem knowledgeSoundness :
    (oracleReduction (R := R) sz oSpec).verifier.knowledgeSoundness init impl
      (WitnessAttachment.relIn sz) (Terminal.relOut params)
      (totalError (params).ℓ_m (params).ℓ_n (Fintype.card R)) :=
  OracleVerifier.knowledgeSoundness_of_with init impl
    (knowledgeSoundnessWith (R := R) sz oSpec init impl)

/-- The same folded extractor also satisfies the error bound clipped at one. -/
theorem knowledgeSoundness_clipped :
    (oracleReduction (R := R) sz oSpec).verifier.knowledgeSoundness init impl
      (WitnessAttachment.relIn sz) (Terminal.relOut params)
      (min 1 (totalError (params).ℓ_m (params).ℓ_n (Fintype.card R))) := by
  apply OracleVerifier.knowledgeSoundness_of_with init impl
    (verifier := (oracleReduction (R := R) sz oSpec).verifier)
    (extractor := (rbrExtractor (R := R) sz oSpec init impl).foldExtractor)
  intro Aux stmt aux prover
  have h := knowledgeSoundnessWith (R := R) sz oSpec init impl Aux stmt aux prover
  rw [ENNReal.coe_min, ENNReal.coe_one]
  exact le_min (prEvent_le_one _) h

end Spartan
