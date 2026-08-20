/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Preliminaries

/-!
# Image-fibre kernel for Claim 5.22

This file is the paper-faithful whole-table kernel behind the H₁--H₂
reparameterization.  It deliberately uses only `CodecCore`: a decoder need not
be onto the nominal verifier-challenge type.  The fibre lift is taken only at
the decoded image of the encoded table that was just sampled.

The legacy total-fibre construction remains elsewhere under `CodecTotal` for
unmigrated code.  It must not be used by the revised Lemma 5.1 route.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U]

/-- The finite encoded-table carrier used by the revised H₁/H₂ coupling.  The
instance is constructed explicitly, rather than selected through the legacy
oracle-family `SampleableType` fallback. -/
@[reducible]
noncomputable def imageFibreEncodedTableFinEnum :
    FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := by
  classical
  letI : FinEnum StmtIn := VCVCompatible.instFinEnum
  letI : FinEnum U := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum (pSpec.EncodedMessagesBefore U i.1.castSucc) := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((gSpecInterface (U := U) StmtIn pSpec δ i).Query) := by
    change FinEnum (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)
    infer_instance
  letI : FinEnum (gSpec (U := U) StmtIn pSpec δ).Domain := inferInstance
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      FinEnum ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, _⟩
    change FinEnum (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  infer_instance

/-- The canonical finite structure for complete encoded challenge tables. -/
noncomputable def imageFibreEncodedTableFintype :
    Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := by
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    imageFibreEncodedTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  exact Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm

/-- An explicit uniform encoded table with canonical finite instances. -/
noncomputable def imageFibreUniformEncodedTable :
    ProbComp (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := by
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    imageFibreEncodedTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, _⟩
    change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : SampleableType (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    SampleableType.ofFintype _
  exact $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))

/-- A joint Claim-5.22 sample.  `decoded` is exposed to H₂; `representative`
is a uniformly sampled encoded preimage of it and is exposed to H₁. -/
structure ImageFibreTablePair where
  original : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)
  representativeWitness : Preliminaries.Preimage
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ original)

/-- The encoded table used by H₁ in an `ImageFibreTablePair`. -/
def ImageFibreTablePair.representative
    (pair : ImageFibreTablePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) :=
  pair.representativeWitness.1

/-- H₁'s and H₂'s complete decoded tables agree pointwise in the joint sample. -/
theorem ImageFibreTablePair.decode_representative_eq_original
    (pair : ImageFibreTablePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    decodeEncodedChallengeTable (U := U) StmtIn pSpec δ pair.representative =
      decodeEncodedChallengeTable (U := U) StmtIn pSpec δ pair.original :=
  pair.representativeWitness.2

/-- Sample an encoded table, expose its decoded view, and sample a uniform
representative only in that witnessed image fibre. -/
noncomputable def sampleImageFibreTablePair :
    ProbComp (ImageFibreTablePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    imageFibreEncodedTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    imageFibreEncodedTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, _⟩
    change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  refine imageFibreUniformEncodedTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>= fun original => ?_
  exact do
    let decoded := decodeEncodedChallengeTable (U := U) StmtIn pSpec δ original
    let representative ← Preliminaries.uniformPreimageWitnessCompOfImage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ) decoded ⟨original, rfl⟩
    pure ⟨original, representative⟩

/-- The H₁ representative from the partial image-fibre pair is exactly a
uniform encoded table.  This is the algebraic content of revised Claim 5.22
and has no decoder-surjectivity premise. -/
theorem evalDist_sampleImageFibreTablePair_representative_eq_uniform :
    𝒟[ImageFibreTablePair.representative <$>
      sampleImageFibreTablePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] =
      𝒟[imageFibreUniformEncodedTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    imageFibreEncodedTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    imageFibreEncodedTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, _⟩
    change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : SampleableType (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    SampleableType.ofFintype _
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  have hRepresentative
      (original : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
      𝒟[do
        let witness ← Preliminaries.uniformPreimageWitnessCompOfImage
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ original) ⟨original, rfl⟩
        pure witness.1] =
        𝒟[Preliminaries.uniformPreimageCompOfImage
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ original) ⟨original, rfl⟩] := by
    change 𝒟[Subtype.val <$> Preliminaries.uniformPreimageWitnessCompOfImage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ original) ⟨original, rfl⟩] = _
    exact Preliminaries.evalDist_uniformPreimageWitnessCompOfImage_val
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ original) ⟨original, rfl⟩
  calc
    𝒟[ImageFibreTablePair.representative <$>
      sampleImageFibreTablePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] =
        𝒟[do
          let original ← imageFibreUniformEncodedTable
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          Preliminaries.uniformPreimageCompOfImage
            (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
            (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ original) ⟨original, rfl⟩] := by
      unfold sampleImageFibreTablePair ImageFibreTablePair.representative
      simp only [map_bind, map_pure, pure_bind]
      rw [evalDist_bind, evalDist_bind]
      apply bind_congr
      exact hRepresentative
    _ = 𝒟[imageFibreUniformEncodedTable
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
      simpa only [imageFibreUniformEncodedTable] using
        (Preliminaries.evalDist_uniformPreimageCompOfImage_reparameterization
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ))

/-- The representative marginal remains uniform under an arbitrary adaptive
continuation. -/
theorem evalDist_sampleImageFibreTablePair_representative_bind_eq_uniform
    {α : Type}
    (continuation : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      ProbComp α) :
    𝒟[(sampleImageFibreTablePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        fun pair => continuation pair.representative)] =
      𝒟[(imageFibreUniformEncodedTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
          continuation)] := by
  have hfactor :
      sampleImageFibreTablePair
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
          (fun pair => continuation pair.representative) =
        ((ImageFibreTablePair.representative <$>
          sampleImageFibreTablePair
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) >>=
          continuation) := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp
  rw [hfactor, evalDist_bind,
    evalDist_sampleImageFibreTablePair_representative_eq_uniform, ← evalDist_bind]

end DuplexSpongeFS.KeyLemma
