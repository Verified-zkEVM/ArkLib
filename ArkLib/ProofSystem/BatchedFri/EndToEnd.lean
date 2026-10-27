/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.BatchedFri.Spec.General
public import ArkLib.ProofSystem.BatchedFri.Security
public import ArkLib.ProofSystem.Fri.Spec.Soundness
public import ArkLib.ProofSystem.Fri.Spec.Completeness
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.Append.Security

/-!
# End-to-end Batched FRI security

`batchedFRI_soundness` composes the batching round and FRI bounds, charging the sum of
both errors when `0 < δ < 1 - √ρ` for the initial code rate `ρ`.

`batchedFRI_perfectCompleteness` composes perfect completeness at radius zero.
The empty ambient oracle supplies guarded forms for the induced verifiers.
Composite knowledge soundness is out of scope: the batching round has no extractor.
-/

@[expose] public section

namespace BatchedFri.Spec

open OracleSpec Domain
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}

/-- Sample the batching coefficients and FRI challenges using the component samplers. -/
noncomputable instance instSampleableTypeBatchedFRIChallenge
    (s : Fin (k + 1) → ℕ+) (l m : ℕ)
    [∀ j, SampleableType ((Fri.Spec.pSpec k (ω := ω) s l).Challenge j)] :
    ∀ j, SampleableType ((BatchingRound.batchSpec F m ++ₚ
      Fri.Spec.pSpec k (ω := ω) s l).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

/-- The batching round followed by FRI has ordinary soundness error at most the sum of
its two stage errors, for every initial ambient oracle state distribution. -/
theorem batchedFRI_soundness
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l m : ℕ) (θ : ℝ) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).val) * d)
      (ω : Fin (2 ^ n) ↪ F))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l m).verifier.soundness init impl
      (BatchingRound.inputRelation s d m δ).language
      (Fri.Spec.outputRelation k s d hdom δ).language
      (ProximityGap.errorBound δ (2 ^ (∑ i, (s i).val) * d)
        (ω : Fin (2 ^ n) ↪ F) + Fri.Spec.soundnessError (ω := ω) s d l θ δ) := by
  exact OracleVerifier.append_soundness
    (BatchingRound.batchVerifier (ω := ω) s m) (Fri.Spec.reduction k s d hdom l).verifier
    (BatchingRound.soundness s d m hdom δ hδ_pos hδ init impl)
    (fun state ↦ Fri.Spec.soundness s d l hdom θ δ (pure state) impl)

/-- Exact common input evaluations give perfect completeness for every query count. -/
theorem batchedFRI_perfectCompleteness
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l m : ℕ)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l m).perfectCompleteness init impl
      (BatchingRound.inputRelation s d m 0) (Fri.Spec.outputRelation k s d hdom 0) := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (BatchingRound.batchOracleReduction s d m) (Fri.Spec.reduction k s d hdom l)
    (BatchingRound.batchPureForm s m).toGuardedForm
    (Verifier.GuardedForm.ofEmpty _ (fun _ ↦ (fun _ ↦ 0, by
      intro i
      unfold Fri.Spec.FinalOracleStatement
      split <;> exact 0)))
    (fun _ ↦ Or.inl inferInstance)
    (BatchingRound.perfect_completeness s d m hdom 0 init impl)
    (fun state ↦ Fri.Spec.perfect_completeness s d hdom l (pure state) impl)

end BatchedFri.Spec
