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
both errors at any radius, given a bound on the generator-indexed `caError`.
Affine-space and powers corollaries use the BCIKS20 open Johnson regime, with batching
errors `errorBound` and `m * errorBound`. The multilinear corollary uses the proved
unique-decoding MCA bound and has batching error `t * n / |F|`; the `_johnson` variant
uses `t` times the proved 1.5-Johnson affine-line MCA error.

`batchedFRI_perfectCompleteness` composes perfect completeness at radius zero.
The empty ambient oracle supplies guarded forms for the induced verifiers.
Composite knowledge soundness is out of scope: the batching round has no extractor.
-/

@[expose] public section

namespace BatchedFri.Spec

open OracleSpec Domain
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {S : Type} [SampleableType S]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}

/-- Sample the batching seed and FRI challenges using the component samplers. -/
noncomputable instance instSampleableTypeBatchedFRIChallenge
    (s : Fin (k + 1) → ℕ+) (l : ℕ)
    [∀ j, SampleableType ((Fri.Spec.pSpec k (ω := ω) s l).Challenge j)] :
    ∀ j, SampleableType ((BatchingRound.batchSpec S ++ₚ
      Fri.Spec.pSpec k (ω := ω) s l).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

/-- The batching round followed by FRI has ordinary soundness error at most the sum of
its two stage errors, for every initial ambient oracle state distribution. -/
theorem batchedFRI_soundness
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l m : ℕ) (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
    (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).val) * d)).carrier δ δ ≤ ε)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l m G).verifier.soundness init impl
      (BatchingRound.inputRelation s d m δ).language
      (Fri.Spec.outputRelation k s d hdom δ).language
      (ε + Fri.Spec.soundnessError (ω := ω) s d l θ δ) := by
  exact OracleVerifier.append_soundness
    (BatchingRound.batchVerifier (ω := ω) s m G) (Fri.Spec.reduction k s d hdom l).verifier
    (BatchingRound.soundness s d m G hdom δ ε hε init impl)
    (fun state ↦ Fri.Spec.soundness s d l hdom θ δ (pure state) impl)

omit [SampleableType F] in
/-- Exact common input evaluations give perfect completeness for every query count. -/
theorem batchedFRI_perfectCompleteness
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l m : ℕ) (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l m G).perfectCompleteness init impl
      (BatchingRound.inputRelation s d m 0) (Fri.Spec.outputRelation k s d hdom 0) := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (BatchingRound.batchOracleReduction s d m G) (Fri.Spec.reduction k s d hdom l)
    (BatchingRound.batchPureForm s m G).toGuardedForm
    (Verifier.GuardedForm.ofEmpty _ (fun _ ↦ (fun _ ↦ 0, by
      intro i
      unfold Fri.Spec.FinalOracleStatement
      split <;> exact 0)))
    (fun _ ↦ Or.inl inferInstance)
    (BatchingRound.perfect_completeness s d m G hdom 0 init impl)
    (fun state ↦ Fri.Spec.perfect_completeness s d hdom l (pure state) impl)



/-- End-to-end affineSpace batching with the BCIKS20 open-Johnson error. -/
theorem batchedFRI_soundness_affineSpace
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l m : ℕ) (θ : ℝ) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).val) * d)
      (ω : Fin (2 ^ n) ↪ F))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l m (CoreDefinitions.AffineSpaceGenerator F m)
        ).verifier.soundness init impl
      (BatchingRound.inputRelation s d m δ).language
      (Fri.Spec.outputRelation k s d hdom δ).language
      (ProximityGap.errorBound δ (2 ^ (∑ i, (s i).val) * d)
        (ω : Fin (2 ^ n) ↪ F) + Fri.Spec.soundnessError (ω := ω) s d l θ δ) := by
  exact batchedFRI_soundness s d hdom l m (CoreDefinitions.AffineSpaceGenerator F m) θ δ _
    (ProximityGap.caError_affineSpace_le m (by positivity) hδ_pos hδ) init impl

/-- End-to-end powers batching with the BCIKS20 open-Johnson error. -/
theorem batchedFRI_soundness_powers
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l m : ℕ) (θ : ℝ) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).val) * d)
      (ω : Fin (2 ^ n) ↪ F))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l m (CoreDefinitions.univariatePowersGenerator F m)
        ).verifier.soundness init impl
      (BatchingRound.inputRelation s d m δ).language
      (Fri.Spec.outputRelation k s d hdom δ).language
      (m * ProximityGap.errorBound δ (2 ^ (∑ i, (s i).val) * d)
        (ω : Fin (2 ^ n) ↪ F) + Fri.Spec.soundnessError (ω := ω) s d l θ δ) := by
  exact batchedFRI_soundness s d hdom l m (CoreDefinitions.univariatePowersGenerator F m) θ δ _
    (ProximityGap.caError_powers_le m (by positivity) hδ_pos hδ) init impl



/-- End-to-end multilinear batching in the unique-decoding regime. The proved
batching error `t * n / |F|` adds to the FRI soundness error. -/
theorem batchedFRI_soundness_multilinear
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l t : ℕ) (θ : ℝ) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).val) * d)).carrier)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l (2 ^ t - 1)
      (CoreDefinitions.multilinearBatchGenerator F t)).verifier.soundness init impl
      (BatchingRound.inputRelation s d (2 ^ t - 1) δ).language
      (Fri.Spec.outputRelation k s d hdom δ).language
      (t * (2 ^ n / Fintype.card F) + Fri.Spec.soundnessError (ω := ω) s d l θ δ) := by
  exact batchedFRI_soundness s d hdom l (2 ^ t - 1)
    (CoreDefinitions.multilinearBatchGenerator F t) θ δ _
    (by simpa using ProximityGap.caError_multilinearBatch_le t hδ_pos hδ) init impl



/-- End-to-end multilinear batching with the proved 1.5-Johnson MCA error. -/
theorem batchedFRI_soundness_multilinear_johnson
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (l t : ℕ) (θ : ℝ)
    (δ_min η δ : ℝ≥0)
    (hdist : (δ_min : ℝ) = (Code.minDist
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F)
        (2 ^ (∑ i, (s i).val) * d)).carrier : ℝ) / Fintype.card (Fin (2 ^ n)))
    (hη : 0 < η) (hη_lt : η < δ_min) (hδ_pos : 0 < δ)
    (hδ : (δ : ℝ) ≤ 1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := ω) k s d hdom l (2 ^ t - 1)
      (CoreDefinitions.multilinearBatchGenerator F t)).verifier.soundness init impl
      (BatchingRound.inputRelation s d (2 ^ t - 1) δ).language
      (Fri.Spec.outputRelation k s d hdom δ).language
      (t * ProximityGap.affineLineMcaJohnsonError (2 ^ n) (Fintype.card F) δ_min η +
        Fri.Spec.soundnessError (ω := ω) s d l θ δ) := by
  exact batchedFRI_soundness s d hdom l (2 ^ t - 1)
    (CoreDefinitions.multilinearBatchGenerator F t) θ δ _
    (by
      simpa only [Fintype.card_fin, PNat.val] using
        ProximityGap.caError_multilinearBatch_le_johnson t
          (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).val) * d))
          δ_min η δ hdist hη hη_lt hδ_pos hδ) init impl

end BatchedFri.Spec
