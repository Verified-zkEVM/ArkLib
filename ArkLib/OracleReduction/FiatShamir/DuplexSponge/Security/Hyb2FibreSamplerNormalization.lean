/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2FibreTableKernel

/-!
# Named fibre-table samplers for Claim 5.22

The live lazy-fibre implementation samples complete tables through local canonical finite
instances.  This module gives the corresponding uniform witnessed-preimage sampler a named
interface, so the exact table law can be used at the live-game boundary without replacing an
adaptive execution by an abstract distribution.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [Fintype U] [Nonempty U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- The eager whole-fibre table used to realize the live lazy oracle is exactly the witnessed
representative sampler used by the Claim-5.22 joint coupling.  This equality is stable under an
arbitrary continuation, hence retains adaptive control flow and the complete ordered query log. -/
theorem evalDist_decodedFibreUniformTable_equiv_bind_eq_uniformWitness
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (continuation : Preliminaries.Preimage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ) decoded → ProbComp α) :
    𝒟[do
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) decoded
      continuation
        (decodedFibreTableEquivPreimage (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) decoded table)] =
      𝒟[do
        let witness ← decodedFibreUniformWitness
          (encodedChallengeTableFintype
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          (Classical.decEq _) decoded
        continuation witness] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
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
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Fintype ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Fintype (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Fintype (OracleReduction.OracleFamily
      (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Nonempty (OracleReduction.OracleFamily
      (gSpec (U := U) StmtIn pSpec δ)) := by
    refine ⟨fun q => ?_⟩
    rcases q with ⟨i, key⟩
    change Vector U (challengeSize (pSpec := pSpec) i)
    exact Vector.replicate _ (Classical.choice (show Nonempty U from inferInstance))
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Fintype ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Nonempty ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      SampleableType ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreSampleable (pSpec := pSpec) (U := U) decoded q
  letI : Fintype (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) := by
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) := by
    refine ⟨fun q => ?_⟩
    exact Classical.choice (show Nonempty
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) from inferInstance)
  letI : SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    SampleableType.ofFintype _
  change 𝒟[do
    let table ← $ᵗ OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
    continuation
      (decodedFibreTableEquivPreimage (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) decoded table)] =
    𝒟[do
      let witness ← uniformPreimageWitnessComp
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded
      continuation witness]
  exact evalDist_uniformFibreTable_equiv_bind_eq_uniformPreimageWitness
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded continuation

/-- The live eager fibre-table sampler, after witnesses are erased, is exactly the named
encoded-table fibre kernel.  The continuation is arbitrary: this is the table-normalization
step required to lift Claim 5.22 through the whole adaptive observed game. -/
theorem evalDist_decodedFibreUniformTable_project_bind_eq_uniformEncodedFibre
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (continuation : OracleReduction.OracleFamily
      (gSpec (U := U) StmtIn pSpec δ) → ProbComp α) :
    𝒟[do
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      continuation (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table)] =
      𝒟[do
        let table ← uniformEncodedTableInDecodedFibre
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded
        continuation table] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
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
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Fintype ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Fintype (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Fintype (OracleReduction.OracleFamily
      (gSpec (U := U) StmtIn pSpec δ)) := Fintype.ofFinite _
  letI : Nonempty (OracleReduction.OracleFamily
      (gSpec (U := U) StmtIn pSpec δ)) := by
    refine ⟨fun q => ?_⟩
    rcases q with ⟨i, key⟩
    exact Vector.replicate _ (Classical.choice (show Nonempty U from inferInstance))
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Fintype ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Nonempty ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      SampleableType ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreSampleable (pSpec := pSpec) (U := U) decoded q
  letI : Fintype (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) := by
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) := by
    refine ⟨fun q => ?_⟩
    exact Classical.choice (show Nonempty
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) from inferInstance)
  letI : SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    SampleableType.ofFintype _
  change 𝒟[do
    let table ← $ᵗ OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
    continuation (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table)] =
    𝒟[do
      let table ← Preliminaries.uniformPreimageComp
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded
      continuation table]
  exact evalDist_uniformFibreTable_project_bind_eq_uniformPreimage
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded continuation

/-- Erasing the canonical witnessed representative has the named encoded-table fibre law.
This follows by factoring through the same eager fibre table on both sides, so it is immune to
the implementation choices of the two finite sampler instances. -/
theorem evalDist_decodedFibreUniformWitness_val_eq_uniformEncodedFibre
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    𝒟[Subtype.val <$> decodedFibreUniformWitness
      (encodedChallengeTableFintype
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (Classical.decEq _) decoded] =
      𝒟[uniformEncodedTableInDecodedFibre
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded] := by
  calc
    𝒟[Subtype.val <$> decodedFibreUniformWitness
        (encodedChallengeTableFintype
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (Classical.decEq _) decoded] =
        𝒟[do
          let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) decoded
          pure (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table)] := by
      rw [map_eq_bind_pure_comp]
      symm
      exact evalDist_decodedFibreUniformTable_equiv_bind_eq_uniformWitness
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded
        (fun witness => pure witness.1)
    _ = 𝒟[uniformEncodedTableInDecodedFibre
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded] := by
      simpa only [bind_pure] using
        (evalDist_decodedFibreUniformTable_project_bind_eq_uniformEncodedFibre
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded pure)

/-- Replacing the complete eager product of decoder-fibre cells by its uniformly sampled
witnessed representative is exact under a jointly sampled outer encoded table.  The
continuation may depend on that outer table, so this keeps adaptive control and the full log. -/
theorem evalDist_uniformEncodedTable_fibreEager_bind_eq_witness
    {α : Type}
    (continuation : ∀ observed : OracleReduction.OracleFamily
      (gSpec (U := U) StmtIn pSpec δ),
      Preliminaries.Preimage
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observed) → ProbComp α) :
    𝒟[do
      let observed ← uniformEncodedChallengeTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observed)
      continuation observed
        (decodedFibreTableEquivPreimage (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observed) table)] =
      𝒟[do
        let observed ← uniformEncodedChallengeTable
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        let witness ← decodedFibreUniformWitness
          (encodedChallengeTableFintype
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          (Classical.decEq _)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observed)
        continuation observed witness] := by
  rw [evalDist_bind, evalDist_bind]
  apply bind_congr
  intro observed
  exact evalDist_decodedFibreUniformTable_equiv_bind_eq_uniformWitness
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observed)
    (continuation observed)

end DuplexSpongeFS.KeyLemma
