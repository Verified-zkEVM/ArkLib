/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.ProofSystem.Fri.Spec.LocalCompleteness
public import ArkLib.ProofSystem.Fri.Spec.HonestFolding
public import ArkLib.ProofSystem.Fri.Spec.InputRelation
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Security.RbrGame

/-!
# Completeness of the FRI oracle reduction

The honest prover preserves the supplied word and folds its polynomial witness. Only the first
queried block can contain input errors; all later commitments are exact polynomial evaluations.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleSpec OracleComp ProtocolSpec Finset
open scoped NNReal ENNReal ProbabilityTheory

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- The folding verifier's degree guard and complete output-history map. -/
private noncomputable def foldGuardedForm :
    (reductionFold k (ω := ω) s d).toReduction.verifier.GuardedForm where
  check := fun _ tr ↦ decide ((tr.snd 1).natDegree < d.val)
  out := fun stmt tr ↦ (foldPhaseChallenges s tr, foldPhaseHistory s d stmt tr)
  verify_eq := by
    intro stmt tr
    apply OptionT.ext
    change ((reductionFold k (ω := ω) s d).verifier.toVerifier.run stmt tr).run = _
    erw [reductionFold_run]
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl

namespace QueryRound

/-- Uniform sampling of the complete vector of initial-domain queries, with replacement. -/
noncomputable instance instSampleableTypeChallenge :
    ∀ j, SampleableType ((pSpec (ω := ω) l).Challenge j) := by
  rintro ⟨j, hj⟩
  have hzero : j = 0 := Fin.eq_zero j
  subst j
  change SampleableType (Fin l → (ω.subdomain 0).toFinset)
  infer_instance

/-- The query prover samples the verifier's vector and preserves all input data. -/
theorem queryProver_run
    (stmt : FinalStatement F k × ∀ j, FinalOracleStatement s ω j)
    (p : Witness F s d (Fin.last (k + 1))) :
    (queryProver s d l).run stmt p = (do
      let xs ← (pSpec (ω := ω) l).getChallenge ⟨0, rfl⟩
      pure (((default : (pSpec (ω := ω) l).Transcript 0).concat
        (m := (0 : Fin 1)) xs), stmt, p)) := by
  unfold Prover.run
  erw [Prover.runToRound_succ (0 : Fin 1)]
  erw [Prover.processRound_of_dir_eq_V_to_P (0 : Fin 1) rfl]
  simp [Prover.runToRound_zero_of_prover_first, queryProver]

/-- Simulating the query prover draws a uniform vector and preserves the shared oracle state. -/
theorem queryProver_simulate_run
    (stmt : FinalStatement F k × ∀ j, FinalOracleStatement s ω j)
    (p : Witness F s d (Fin.last (k + 1))) {σ : Type} (state : σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((queryProver s d l).run stmt p)).run state = (do
        let xs ← $ᵗ (Fin l → (ω.subdomain 0).toFinset)
        pure ((((default : (pSpec (ω := ω) l).Transcript 0).concat
          (m := (0 : Fin 1)) xs), stmt, p), state)) := by
  have hget := simulateQ_addLift_challengeQueryImpl_getChallenge
    (pSpec := pSpec (ω := ω) l) impl ⟨0, rfl⟩
  rw [queryProver_run]
  simp only [simulateQ_bind, simulateQ_pure]
  erw [hget]
  simp

/-- A guarded form of the query verifier, checking every local folding equation. -/
noncomputable def queryGuardedForm
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) :
    (queryOracleReduction (ω := ω) s d hdom l).toReduction.verifier.GuardedForm where
  check := fun stmt tr ↦ decide (∀ j i,
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) stmt.2)
      (checkRound s (round_bound hdom) (finalPolynomial s stmt.2)
        (stmt.1 i) i (tr.challenges ⟨0, by simp⟩ j))).run = true)
  out := fun stmt _ ↦ stmt
  verify_eq := by
    rintro ⟨α, o⟩ tr
    apply OptionT.ext
    change ((queryVerifier s (round_bound hdom) l).toVerifier.verify (α, o) tr).run = _
    erw [queryVerifier_toVerifier_verify]
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl

/-- Querying an honest retained history preserves its exact output witness with the radius bound. -/
theorem queryOracleReduction_completeness
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (δ : ℝ≥0)
    {σ : Type} (state : σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleReduction (ω := ω) s d hdom l).completeness (pure state) impl
      (foldCompletenessRelation s d δ) (Spec.outputRelation k s d hdom 0)
      (completenessError s δ l) := by
  change (queryOracleReduction (ω := ω) s d hdom l).toReduction.completeness _ _ _ _ _
  rw [Reduction.completeness_iff_of_guarded_verifier _ (queryGuardedForm s d l hdom)]
  rintro stmt p ⟨f, p₀, α, hdist, heq⟩
  rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
  have hprob := verifyQueries_completeness s d (round_bound hdom) f p₀ α δ l hdist
  have hout := honestHistory_mem_outputRelation s d hdom f p₀ α
  simp_rw [eval_verifyQueries_ne_none_iff s (round_bound hdom)] at hprob
  simp only [pure_bind]
  erw [queryProver_simulate_run]
  simpa [prEvent_norm, queryGuardedForm, FullTranscript.challenges, hout] using hprob

/-- Querying a fixed honest history has the sharper error given by its clean first blocks. -/
theorem queryOracleReduction_completeness_blocks
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    {σ : Type} (state : σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleReduction (ω := ω) s d hdom l).completeness (pure state) impl
      (honestOutputRelation s d f p₀) (Spec.outputRelation k s d hdom 0)
      (1 - (((cleanFirstQueries ω (s 0).val (fun z ↦ f (initialQuery z))
        (fun z ↦ p₀.val.eval (ω z))).card : ℝ≥0) / 2 ^ n) ^ l) := by
  change (queryOracleReduction (ω := ω) s d hdom l).toReduction.completeness _ _ _ _ _
  rw [Reduction.completeness_iff_of_guarded_verifier _ (queryGuardedForm s d l hdom)]
  rintro stmt p ⟨α, heq⟩
  rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
  have hprob := verifyQueries_completeness_blocks s d (round_bound hdom) f p₀ α l
  have hout := honestHistory_mem_outputRelation s d hdom f p₀ α
  simp_rw [eval_verifyQueries_ne_none_iff s (round_bound hdom)] at hprob
  have hpow := pow_le_one₀ (by positivity)
    (cleanFirstQueries_density_le_one ω (s 0).val
      (fun z ↦ f (initialQuery z)) (fun z ↦ p₀.val.eval (ω z))) (n := l)
  rw [← ENNReal.coe_one, ← ENNReal.coe_sub, tsub_tsub_cancel_of_le hpow]
  simp only [pure_bind]
  erw [queryProver_simulate_run]
  simpa [prEvent_norm, queryGuardedForm, FullTranscript.challenges, hout] using hprob

end QueryRound

/-- Uniform challenge sampling for the complete folding and query schedule. -/
noncomputable instance instSampleableTypeChallengePSpec :
    ∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

/-- The complete reduction accepts noisy inputs with the clipped first-fold completeness error,
and its transmitted final polynomial equals its honest output witness. -/
theorem reduction_completeness
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (l : ℕ) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction (ω := ω) k s d hdom l).completeness init impl
      (inputRelation k s d hdom δ) (outputRelation k s d hdom 0)
      (completenessError s δ l) := by
  simpa only [zero_add] using OracleReduction.append_completeness_of_guarded_verifiers
    (reductionFold k (ω := ω) s d) (QueryRound.queryOracleReduction s d hdom l)
    (foldGuardedForm s d) (QueryRound.queryGuardedForm s d l hdom)
    (fun _ ↦ Or.inl inferInstance)
    (reductionFold_perfectCompleteness s d hdom δ init impl)
    (fun state ↦ QueryRound.queryOracleReduction_completeness s d l hdom δ state impl)

/-- For a fixed input word and witness, completeness depends on the exact number of clean
first-fold blocks and preserves the complete honest output history. -/
theorem reduction_completeness_blocks
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (l : ℕ)
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction (ω := ω) k s d hdom l).completeness init impl
      (honestFoldRelation s d f p₀ 0) (outputRelation k s d hdom 0)
      (1 - (((cleanFirstQueries ω (s 0).val (fun z ↦ f (initialQuery z))
        (fun z ↦ p₀.val.eval (ω z))).card : ℝ≥0) / 2 ^ n) ^ l) := by
  simpa only [zero_add, Fin.castSucc_zero] using
    OracleReduction.append_completeness_of_guarded_verifiers
      (reductionFold k (ω := ω) s d) (QueryRound.queryOracleReduction s d hdom l)
      (foldGuardedForm s d) (QueryRound.queryGuardedForm s d l hdom)
      (fun _ ↦ Or.inl inferInstance)
      (reductionFold_perfectCompleteness_honest s d f p₀ init impl)
      (fun state ↦
        QueryRound.queryOracleReduction_completeness_blocks s d l hdom f p₀ state impl)

/-- Exact input evaluations give perfect completeness for every query count. -/
theorem perfect_completeness
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (l : ℕ)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction (ω := ω) k s d hdom l).perfectCompleteness init impl
      (inputRelation k s d hdom 0) (outputRelation k s d hdom 0) := by
  simpa only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    OracleReduction.completeness, completenessError_zero] using
    reduction_completeness s d hdom l 0 init impl

/-- With no queries, honest folding is perfectly complete for every input radius. -/
theorem perfect_completeness_zero_queries
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction (ω := ω) k s d hdom 0).perfectCompleteness init impl
      (inputRelation k s d hdom δ) (outputRelation k s d hdom 0) := by
  simpa only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    OracleReduction.completeness, completenessError_zero_queries] using
    reduction_completeness s d hdom 0 δ init impl

end Fri.Spec
