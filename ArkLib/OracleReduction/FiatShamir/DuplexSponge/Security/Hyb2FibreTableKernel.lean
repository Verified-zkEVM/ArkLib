/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2FibreLazyEager

/-!
# Whole-table decoder-fibre kernel

This module records the one distributional step that turns a uniformly sampled complete
decoder-fibre witness table into the encoded-table fibre kernel.  It is intentionally stated for
an arbitrary continuation: Claim 5.22 needs the law after an adaptive complete execution, not
only for an individual cell.
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

/-- Equality of the distributions of sampled tables is stable under an arbitrary continuation
which receives the table.  This elementary kernel is the exact operation needed to lift a
whole-table fibre identity through an adaptive execution and its complete ordered log. -/
theorem evalDist_bind_apply_eq_of_evalDist_map_eq
    {A B α : Type} (sample : ProbComp A) (map : A → B) (target : ProbComp B)
    (continuation : B → ProbComp α)
    (h : 𝒟[map <$> sample] = 𝒟[target]) :
    𝒟[do
      let a ← sample
      continuation (map a)] =
      𝒟[do
        let b ← target
        continuation b] := by
  calc
    𝒟[do
      let a ← sample
      continuation (map a)] =
        𝒟[do
          let b ← map <$> sample
          continuation b] := by
      rw [evalDist_bind, evalDist_bind, evalDist_map]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    _ = 𝒟[do
      let b ← target
      continuation b] := by
      rw [evalDist_bind, evalDist_bind, h]

/-- A uniformly sampled complete table of decoder-fibre witnesses, after erasing the witnesses,
is the uniform encoded-table kernel in the fibre over the fixed decoded table.  The continuation
is arbitrary, so the statement already supports adaptive queries, their complete outputs, and
their ordered logs. -/
theorem evalDist_uniformFibreTable_project_bind_eq_uniformPreimage
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    [DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ)]
    [Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [Fintype (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    [Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    [SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    (continuation : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      ProbComp α) :
    𝒟[do
      let table ← $ᵗ OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
      continuation (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table)] =
      𝒟[do
        let table ← Preliminaries.uniformPreimageComp
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded
        continuation table] := by
  calc
    𝒟[do
      let table ← $ᵗ OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
      continuation (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table)] =
        𝒟[do
          let table ← projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded <$>
            ($ᵗ OracleReduction.OracleFamily
              (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
          continuation table] := by
      rw [evalDist_bind, evalDist_bind, evalDist_map]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    _ = 𝒟[do
      let table ← Preliminaries.uniformPreimageComp
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded
      continuation table] := by
      rw [evalDist_bind, evalDist_bind]
      rw [evalDist_project_uniformDecodedFibreTable_eq_uniformPreimage
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) decoded]

/-- The complete fibre table used by the lazy-realization proof and the witnessed
representative used by the joint H₁--H₂ coupling are the same finite uniform object, presented
through the canonical equivalence `decodedFibreTableEquivPreimage`.  Keeping the witness is
essential here: it is the pointwise decoded-table invariant needed to couple the two full
executions, rather than merely their output distributions. -/
private theorem pmf_map_uniformOfFintype_equiv
    {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (equiv : A ≃ B) :
    (PMF.uniformOfFintype A).map equiv = PMF.uniformOfFintype B := by
  classical
  letI : DecidableEq B := Classical.decEq _
  ext b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply,
    Fintype.card_congr equiv, tsum_fintype]
  have hsum :
      Finset.univ.sum (fun a : A =>
          if b = equiv a then (Fintype.card B : ENNReal)⁻¹ else 0) =
        Finset.univ.sum (fun b' : B =>
          if b = b' then (Fintype.card B : ENNReal)⁻¹ else 0) := by
    simpa using
      (Fintype.sum_equiv equiv
        (fun a : A => if b = equiv a then (Fintype.card B : ENNReal)⁻¹ else 0)
        (fun b' : B => if b = b' then (Fintype.card B : ENNReal)⁻¹ else 0)
        (by intro a; rfl))
  have hdelta :
      Finset.univ.sum (fun b' : B =>
          if b = b' then (Fintype.card B : ENNReal)⁻¹ else 0) =
        (Fintype.card B : ENNReal)⁻¹ := by
    simp
  exact hsum.trans hdelta

/-- **Claim 5.22 witnessed-table kernel.**  For a fixed decoded table, eager uniform sampling
of all decoder-fibre cells, transported to one complete witnessed preimage, has the same law as
the representative sampled by `sampleEncodedTableFibrePair`.  The continuation is arbitrary,
so it covers adaptive control flow, complete ordered logs, and repeated oracle occurrences. -/
theorem evalDist_uniformFibreTable_equiv_bind_eq_uniformPreimageWitness
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    [DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ)]
    [Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [Fintype (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    [Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    [SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    (continuation : Preliminaries.Preimage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ) decoded → ProbComp α) :
    𝒟[do
      let table ← $ᵗ OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
      continuation
        (decodedFibreTableEquivPreimage (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) decoded table)] =
      𝒟[do
        let witness ← uniformPreimageWitnessComp
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded
        continuation witness] := by
  letI : Nonempty (Preliminaries.Preimage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ) decoded) :=
    Preliminaries.preimageNonempty
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded
  letI : SampleableType (Preliminaries.Preimage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ) decoded) :=
    SampleableType.ofFintype _
  apply evalDist_bind_apply_eq_of_evalDist_map_eq
    ($ᵗ OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
    (decodedFibreTableEquivPreimage (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) decoded)
    (uniformPreimageWitnessComp
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded)
    continuation
  rw [evalDist_map, evalDist_uniformSample]
  unfold uniformPreimageWitnessComp
  rw [evalDist_uniformSample, ← liftM_map]
  apply congrArg liftM
  exact pmf_map_uniformOfFintype_equiv
    (decodedFibreTableEquivPreimage (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) decoded)

end DuplexSpongeFS.KeyLemma
