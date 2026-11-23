/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.TranscriptMap
public import ArkLib.ProofSystem.Binius.FRIBinius.Executable.Modular
public import ArkLib.ProofSystem.Binius.FRIBinius.Executable.Unrolled

/-!
# Soundness of the executable FRI-Binius openings

Decode the batching message into a tensor and the modular prefix's sumcheck messages into
quadratic polynomials. Challenges and the Binary Basefold suffix stay unchanged. Decode each
prefix to reuse the abstract round-by-round proof with the same challenge errors, converting
extracted source polynomials back to Boolean tables.
-/

@[expose] public section

namespace Binius.FRIBinius.Executable

open Module OracleSpec OracleComp ProtocolSpec RingSwitching RingSwitching.Packing
open scoped NNReal

variable {κ ℓ ℓ' R ϑ : ℕ}
variable {K L : Type} [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Field L] [Fintype L] [DecidableEq L] [SampleableType L] [Algebra K L]
variable [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (b : Basis (Fin (2 ^ κ)) K L)
variable (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ)

local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

/-- The unrolled error at a challenge is the abstract error at the same slot. -/
noncomputable def unrolledError :
    (unrolledPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ).ChallengeIdx → ℝ≥0 :=
  Unrolled.fullError κ K b (ϑ := ϑ) hRate γ ∘
    (unrolledTranscriptMap (ϑ := ϑ) b hRate γ).challengeIdx

/-- The modular error at a challenge is the abstract error at the same slot. -/
noncomputable def modularError :
    (modularPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ).ChallengeIdx → ℝ≥0 :=
  Binius.FRIBinius.RingSwitch.fullError κ K b (ϑ := ϑ) hRate γ ∘
    (modularTranscriptMap (ϑ := ϑ) b hRate γ).challengeIdx

omit [DecidableEq K] [Fact (Fintype.card K = 2)] [NeZero R] in
/-- Reindexing the unrolled challenge errors preserves their sum. -/
theorem unrolledError_sum :
    (∑ i, unrolledError (ϑ := ϑ) b hRate γ i) =
      ∑ i, Unrolled.fullError κ K b (ϑ := ϑ) hRate γ i :=
  Equiv.sum_comp (unrolledTranscriptMap (ϑ := ϑ) b hRate γ).challengeIdxEquiv _

omit [DecidableEq K] [Fact (Fintype.card K = 2)] [NeZero R] in
/-- Reindexing the modular challenge errors preserves their sum. -/
theorem modularError_sum :
    (∑ i, modularError (ϑ := ϑ) b hRate γ i) =
      ∑ i, Binius.FRIBinius.RingSwitch.fullError κ K b (ϑ := ϑ) hRate γ i :=
  Equiv.sum_comp (modularTranscriptMap (ϑ := ϑ) b hRate γ).challengeIdxEquiv _

omit [DecidableEq K] in
private theorem unrolledError_sum_le :
    (∑ i, unrolledError (ϑ := ϑ) b hRate γ i) ≤
      Unrolled.concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ := by
  rw [unrolledError_sum]
  exact Unrolled.fullError_sum_le_concrete κ K b (ϑ := ϑ) hRate γ

omit [DecidableEq K] in
private theorem modularError_sum_le :
    (∑ i, modularError (ϑ := ϑ) b hRate γ i) ≤
      Binius.FRIBinius.RingSwitch.concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ := by
  rw [modularError_sum]
  exact Binius.FRIBinius.RingSwitch.fullError_sum_le κ K b (ϑ := ϑ) hRate γ

omit [SampleableType L] [NeZero R] in
private theorem mem_inputRelation_of_mem_tensor (hDim : ℓ = ℓ' + κ) {stmt source}
    (hRelation : (stmt, source) ∈ TensorPrefix.relIn (biniusProfile κ L K b) hDim
      (binaryBasefoldInput κ L K b ℓ' R ϑ hRate)) :
    (stmt, tableWitnessEquiv.symm source) ∈ inputRelation (ϑ := ϑ) b hRate hDim := by
  let holds (polynomial : Sumcheck.Structured.MultilinearPoly K ℓ) : Prop :=
    (stmt, polynomial) ∈ TensorPrefix.relIn (biniusProfile κ L K b) hDim
      (binaryBasefoldInput κ L K b ℓ' R ϑ hRate)
  change holds (tableWitnessEquiv (tableWitnessEquiv.symm source))
  exact (congrArg holds (tableWitnessEquiv.apply_symm_apply source)).mpr hRelation

variable [Fact (b 0 = 1)]
variable (hDim : ℓ = ℓ' + κ) (coordinates : L → (Fin κ → Fin 2) → K)
variable (hCoordinateMap : coordinates = fun x u => b.repr x (finFunctionFinEquiv u))
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The executable unrolled verifier has the original round-by-round knowledge error. -/
theorem unrolledVerifier_rbrKnowledgeSoundness :
    (((unrolledReduction (ϑ := ϑ) (⇑b) coordinates hDim hRate γ
        ⟨b, rfl, hCoordinateMap⟩).verifier
        (Oₛₒ := fun i : Empty => nomatch i)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (inputRelation (ϑ := ϑ) b hRate hDim) acceptRejectOracleRel
      (unrolledError (ϑ := ϑ) b hRate γ) := by
  refine Verifier.rbrKnowledgeSoundness_of_transcriptMap init impl
    (decoder := unrolledTranscriptMap (ϑ := ϑ) b hRate γ)
    (encodeInputWitness := tableWitnessEquiv.symm)
    (hInputRelation := fun stmt source hRelation =>
      mem_inputRelation_of_mem_tensor (ϑ := ϑ) b hRate hDim
        (stmt := stmt) (source := source) hRelation)
    (hSound := Unrolled.fullVerifier_rbrKnowledgeSoundness κ K b (ϑ := ϑ)
      hRate hDim γ init impl)
    (hVerify := ?_)
  rintro ⟨claim, inputOracles⟩ transcript
  exact unrolledReduction_verify_eq b hRate γ coordinates hCoordinateMap hDim
    claim inputOracles transcript

/-- The executable modular verifier has the original round-by-round knowledge error. -/
theorem modularVerifier_rbrKnowledgeSoundness :
    (((modularReduction (ϑ := ϑ) (⇑b) coordinates hDim hRate γ
        ⟨b, rfl, hCoordinateMap⟩).verifier
        (Oₛₒ := fun i : Empty => nomatch i)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (inputRelation (ϑ := ϑ) b hRate hDim) acceptRejectOracleRel
      (modularError (ϑ := ϑ) b hRate γ) := by
  refine Verifier.rbrKnowledgeSoundness_of_transcriptMap init impl
    (decoder := modularTranscriptMap (ϑ := ϑ) b hRate γ)
    (encodeInputWitness := tableWitnessEquiv.symm)
    (hInputRelation := fun stmt source hRelation =>
      mem_inputRelation_of_mem_tensor (ϑ := ϑ) b hRate hDim
        (stmt := stmt) (source := source) hRelation)
    (hSound := Binius.FRIBinius.RingSwitch.fullVerifier_rbrKnowledgeSoundness κ K b (ϑ := ϑ)
      hRate hDim γ init impl)
    (hVerify := ?_)
  rintro ⟨claim, inputOracles⟩ transcript
  rw [modularTranscriptMap_decodeFull]
  exact modularReduction_verify_eq b coordinates hCoordinateMap hDim hRate γ
    claim inputOracles transcript

/-- The executable unrolled verifier is knowledge sound at the original concrete bound. -/
theorem unrolledVerifier_knowledgeSoundness :
    OracleProof.knowledgeSoundness init impl (inputRelation (ϑ := ϑ) b hRate hDim)
      ((unrolledReduction (ϑ := ϑ) (⇑b) coordinates hDim hRate γ
        ⟨b, rfl, hCoordinateMap⟩).verifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (Unrolled.concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ) :=
  Verifier.knowledgeSoundness_error_mono init impl (unrolledError_sum_le (ϑ := ϑ) b hRate γ)
    (Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
      (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
      (unrolledVerifier_rbrKnowledgeSoundness (ϑ := ϑ) b hRate γ hDim coordinates
        hCoordinateMap init impl))

/-- The executable modular verifier is knowledge sound at the original concrete bound. -/
theorem modularVerifier_knowledgeSoundness :
    OracleProof.knowledgeSoundness init impl (inputRelation (ϑ := ϑ) b hRate hDim)
      ((modularReduction (ϑ := ϑ) (⇑b) coordinates hDim hRate γ
        ⟨b, rfl, hCoordinateMap⟩).verifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (Binius.FRIBinius.RingSwitch.concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ) :=
  Verifier.knowledgeSoundness_error_mono init impl (modularError_sum_le (ϑ := ϑ) b hRate γ)
    (Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
      (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
      (modularVerifier_rbrKnowledgeSoundness (ϑ := ϑ) b hRate γ hDim coordinates
        hCoordinateMap init impl))

/-- The executable unrolled verifier is sound at the original concrete bound. -/
theorem unrolledVerifier_soundness :
    OracleProof.soundness init impl (inputRelation (ϑ := ϑ) b hRate hDim).language
      ((unrolledReduction (ϑ := ϑ) (⇑b) coordinates hDim hRate γ
        ⟨b, rfl, hCoordinateMap⟩).verifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (Unrolled.concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ) :=
  Verifier.soundness_error_mono init impl
    (by exact_mod_cast unrolledError_sum_le (ϑ := ϑ) b hRate γ)
    (Verifier.GuardedForm.soundness_of_rbrSoundness
      (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
      (Verifier.rbrSoundness_of_rbrKnowledgeSoundness
        (unrolledVerifier_rbrKnowledgeSoundness (ϑ := ϑ) b hRate γ hDim coordinates
          hCoordinateMap init impl)))

/-- The executable modular verifier is sound at the original concrete bound. -/
theorem modularVerifier_soundness :
    OracleProof.soundness init impl (inputRelation (ϑ := ϑ) b hRate hDim).language
      ((modularReduction (ϑ := ϑ) (⇑b) coordinates hDim hRate γ
        ⟨b, rfl, hCoordinateMap⟩).verifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (Binius.FRIBinius.RingSwitch.concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ) :=
  Verifier.soundness_error_mono init impl
    (by exact_mod_cast modularError_sum_le (ϑ := ϑ) b hRate γ)
    (Verifier.GuardedForm.soundness_of_rbrSoundness
      (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
      (Verifier.rbrSoundness_of_rbrKnowledgeSoundness
        (modularVerifier_rbrKnowledgeSoundness (ϑ := ϑ) b hRate γ hDim coordinates
          hCoordinateMap init impl)))

end Binius.FRIBinius.Executable
