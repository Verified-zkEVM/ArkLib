/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2LogCoupling
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2FibreRefinement

/-!
# Whole-game H₁--H₂ coupling

The Claim-5.22 coupling samples an encoded table `g₀`, exposes its decoded view to H₂, and
samples an encoded representative `g₁` in the fibre of that view for H₁.  Keeping the fibre
membership proof in the joint sample is essential: it is the pointwise fact from which the two
line-4 trace maps agree.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [codec : Codec pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- Uniformly sample a *witnessed* preimage.  Keeping the membership proof is what permits a
whole-game coupling to retain the pointwise decoded-table invariant. -/
noncomputable def uniformPreimageWitnessComp {A B : Type} [Fintype B] [DecidableEq A]
    (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    ProbComp (Preliminaries.Preimage ψ a) := by
  classical
  letI : Nonempty (Preliminaries.Preimage ψ a) :=
    Preliminaries.preimageNonempty ψ hψ a
  letI : SampleableType (Preliminaries.Preimage ψ a) := SampleableType.ofFintype _
  exact $ᵗ Preliminaries.Preimage ψ a

/-- Forgetting a uniform preimage witness is exactly the existing executable uniform-fibre
kernel. -/
theorem evalDist_uniformPreimageWitnessComp {A B : Type} [Fintype B] [DecidableEq A]
    (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    𝒟[Subtype.val <$> uniformPreimageWitnessComp ψ hψ a] =
      𝒟[Preliminaries.uniformPreimageComp ψ hψ a] := by
  unfold uniformPreimageWitnessComp Preliminaries.uniformPreimageComp
  rfl

/-- Sampling a finite uniform value and discarding it leaves a constant computation unchanged.
This is deliberately specialized to uniform sampling: the analogous statement is false for an
arbitrary subprobability computation. -/
private theorem evalDist_uniform_bind_const {α β : Type} [Finite α] [Nonempty α]
    [SampleableType α] (x : β) :
    𝒟[do let _ ← $ᵗ α; pure x] = pure x := by
  letI : Fintype α := Fintype.ofFinite α
  rw [evalDist_bind, evalDist_uniformSample]
  simp only [evalDist_pure]
  change ((liftM (PMF.uniformOfFintype α) : SPMF α) >>=
    fun _ => (pure x : SPMF β)) = pure x
  conv_lhs =>
    enter [2, _]
    rw [← liftM_pure (m := PMF) (n := SPMF) x]
  rw [← liftM_bind]
  change (liftM ((PMF.uniformOfFintype α).bind fun _ => PMF.pure x) : SPMF β) = pure x
  rw [PMF.bind_const]
  exact liftM_pure (m := PMF) (n := SPMF) x

/-- The witnessed uniform-fibre sampler is lossless.  We use this only to forget a sampled
witness; retaining it elsewhere is what carries the pointwise decoded-table invariant. -/
private theorem evalDist_uniformPreimageWitnessComp_bind_const
    {A B β : Type} [Fintype B] [DecidableEq A]
    (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) (x : β) :
    𝒟[do let _ ← uniformPreimageWitnessComp ψ hψ a; pure x] = pure x := by
  classical
  letI : Nonempty (Preliminaries.Preimage ψ a) :=
    Preliminaries.preimageNonempty ψ hψ a
  letI : SampleableType (Preliminaries.Preimage ψ a) := SampleableType.ofFintype _
  unfold uniformPreimageWitnessComp
  exact evalDist_uniform_bind_const x

section LegacyTotalFibre

variable [CodecTotal pSpec U]

/-- A witnessed representative of one complete decoder-table fibre.  The finite table instance
is explicit at each call site, which prevents this helper from selecting the legacy sampler. -/
noncomputable def decodedFibreUniformWitness
    (tableFintype : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)))
    (decodedDecidableEq : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ))
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    ProbComp (Preliminaries.Preimage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ) decoded) := by
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := tableFintype
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := decodedDecidableEq
  exact uniformPreimageWitnessComp
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
    (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded

/-- Discarding a canonical witnessed representative is a lossless uniform draw. -/
private theorem evalDist_decodedFibreUniformWitness_bind_const
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    {β : Type} (x : β) :
    𝒟[do
      let _ ← decodedFibreUniformWitness
        (encodedChallengeTableFintype
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (Classical.decEq _) decoded
      pure x] = pure x := by
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  unfold decodedFibreUniformWitness
  exact evalDist_uniformPreimageWitnessComp_bind_const
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
    (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded x

end LegacyTotalFibre

/-- One joint Claim-5.22 sample: `observedTable` is the table exposed through H₂'s decoder and
`representativeWitness` is an encoded table in its complete decoder fibre.  This is a structure,
rather than a reducible sigma abbreviation, so the full-game coupling can retain this invariant
without repeatedly normalizing the entire finite oracle-table type. -/
structure EncodedTableFibrePair where
  observedTable : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)
  representativeWitness : Preliminaries.Preimage
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable)

/-- The paper-faithful form of the Claim-5.22 joint sample.  Its representative fibre is
sampled only over the decoded view of an already sampled encoded table, so it needs no
surjectivity of the decoder onto the nominal challenge space.  The older
`EncodedTableFibrePair` remains below for legacy total-codec clients; all revised endpoints
should use this image-fibre form. -/
structure EncodedTableImageFibrePair where
  observedTable : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)
  representativeWitness : Preliminaries.Preimage
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable)

/-- Sample the Claim-5.22 joint table pair with the partial image-fibre kernel.  In particular,
the call to `Lift` is justified by the specific sampled `observedTable`, not by a global codec
surjectivity premise. -/
noncomputable def sampleEncodedTableImageFibrePair :
    ProbComp (EncodedTableImageFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  refine uniformEncodedChallengeTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>= fun table => ?_
  exact do
    let representative ← Preliminaries.uniformPreimageWitnessCompOfImage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table) ⟨table, rfl⟩
    pure ⟨table, representative⟩

/-- H₂'s sampled encoded table in the image-fibre coupling. -/
def EncodedTableImageFibrePair.original
    (pair : EncodedTableImageFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) :=
  pair.observedTable

/-- H₁'s encoded representative table in the image-fibre coupling. -/
def EncodedTableImageFibrePair.representative
    (pair : EncodedTableImageFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) :=
  pair.representativeWitness.1

/-- The two components of the image-fibre pair have identical complete decoded tables. -/
theorem EncodedTableImageFibrePair.decode_representative_eq_original
    (pair : EncodedTableImageFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    decodeEncodedChallengeTable (U := U) StmtIn pSpec δ pair.representative =
      decodeEncodedChallengeTable (U := U) StmtIn pSpec δ pair.original :=
  pair.representativeWitness.2

/-- The representative member of the partial image-fibre pair is again an exact uniform encoded
table.  This is Claim 5.22's whole-table fibre identity with no decoder-surjectivity argument:
the target of every `Lift` is the decoded view of the table just sampled. -/
theorem evalDist_sampleEncodedTableImageFibrePair_representative_eq_uniform :
    𝒟[EncodedTableImageFibrePair.representative <$>
      sampleEncodedTableImageFibrePair
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] =
      𝒟[uniformEncodedChallengeTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : SampleableType (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    SampleableType.ofFintype _
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  have hRepresentative
      (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
      𝒟[do
        let witness ← Preliminaries.uniformPreimageWitnessCompOfImage
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table) ⟨table, rfl⟩
        pure witness.1] =
        𝒟[Preliminaries.uniformPreimageCompOfImage
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table) ⟨table, rfl⟩] := by
    change 𝒟[Subtype.val <$> Preliminaries.uniformPreimageWitnessCompOfImage
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table) ⟨table, rfl⟩] = _
    exact Preliminaries.evalDist_uniformPreimageWitnessCompOfImage_val
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table) ⟨table, rfl⟩
  calc
    𝒟[EncodedTableImageFibrePair.representative <$>
      sampleEncodedTableImageFibrePair
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] =
      𝒟[do
        let table ← uniformEncodedChallengeTable
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        Preliminaries.uniformPreimageCompOfImage
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table) ⟨table, rfl⟩] := by
        unfold sampleEncodedTableImageFibrePair EncodedTableImageFibrePair.representative
        simp only [map_bind, map_pure]
        rw [evalDist_bind, evalDist_bind]
        apply bind_congr
        exact hRepresentative
    _ = 𝒟[uniformEncodedChallengeTable
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
        simpa only [uniformEncodedChallengeTable] using
          (Preliminaries.evalDist_uniformPreimageCompOfImage_reparameterization
            (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ))

/-- A continuation of the image-fibre representative has the ordinary uniform encoded-table
marginal.  The continuation is arbitrary, hence this is the whole-table Claim-5.22 kernel for
an adaptive execution and its complete insertion-ordered log. -/
theorem evalDist_sampleEncodedTableImageFibrePair_representative_bind_eq_uniform
    {α : Type}
    (continuation : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      ProbComp α) :
    𝒟[(sampleEncodedTableImageFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        fun pair => continuation pair.representative)] =
      𝒟[(uniformEncodedChallengeTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
          continuation)] := by
  have hfactor :
      sampleEncodedTableImageFibrePair
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
          (fun pair => continuation pair.representative) =
        ((EncodedTableImageFibrePair.representative <$>
          sampleEncodedTableImageFibrePair
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) >>=
          continuation) := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp
  rw [hfactor, evalDist_bind,
    evalDist_sampleEncodedTableImageFibrePair_representative_eq_uniform, ← evalDist_bind]

section LegacyTotalFibre

variable [CodecTotal pSpec U]

/-- Sample the whole-table coupling in the order required by Claim 5.22: first H₂'s encoded
table, then H₁'s encoded representative conditioned on its decoded view. -/
noncomputable def sampleEncodedTableFibrePair :
    ProbComp (EncodedTableFibrePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  refine uniformEncodedChallengeTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>= fun table => ?_
  exact do
    let representative ← decodedFibreUniformWitness
      (encodedChallengeTableFintype
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (Classical.decEq _)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)
    pure ⟨table, representative⟩

/-- Expanding the joint table sampler exposes exactly the same ordered table-and-witness draws as
the direct witnessed-fibre presentation.  The continuation is arbitrary, so this equality can be
used at a whole adaptive game without unfolding that game. -/
theorem evalDist_uniformEncodedTable_witness_bind_eq_pair
    {α : Type}
    (continuation : ∀ table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ),
      Preliminaries.Preimage
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table) → ProbComp α) :
    𝒟[do
      let table ← uniformEncodedChallengeTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      let witness ← decodedFibreUniformWitness
        (encodedChallengeTableFintype
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (Classical.decEq _)
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)
      continuation table witness] =
      𝒟[do
        let pair ← sampleEncodedTableFibrePair
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        continuation pair.observedTable pair.representativeWitness] := by
  simp only [sampleEncodedTableFibrePair, bind_assoc, pure_bind]

/-- H₂'s table in a joint Claim-5.22 sample. -/
def EncodedTableFibrePair.original
    (pair : EncodedTableFibrePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) :=
  pair.observedTable

/-- H₁'s encoded representative table in a joint Claim-5.22 sample. -/
def EncodedTableFibrePair.representative
    (pair : EncodedTableFibrePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) :=
  pair.representativeWitness.1

/-- The observed member of the joint Claim-5.22 table sample has H₂'s exact uniform-table
marginal. -/
theorem evalDist_sampleEncodedTableFibrePair_original_eq_uniform :
    𝒟[EncodedTableFibrePair.original <$>
      sampleEncodedTableFibrePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] =
    𝒟[uniformEncodedChallengeTable
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  unfold sampleEncodedTableFibrePair EncodedTableFibrePair.original
  simp only [map_bind, map_pure]
  rw [evalDist_bind]
  simp only [evalDist_decodedFibreUniformWitness_bind_const, bind_pure]

/-- The representative member of the joint Claim-5.22 sample has H₁'s exact uniform-table
marginal.  Thus the joint sampler simultaneously supplies an honest H₂ table, an honest H₁
table, and a pointwise equality of their decoded tables. -/
theorem evalDist_sampleEncodedTableFibrePair_representative_eq_uniform :
    𝒟[EncodedTableFibrePair.representative <$>
      sampleEncodedTableFibrePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] =
    𝒟[uniformEncodedChallengeTable
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFintype (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : SampleableType (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    SampleableType.ofFintype _
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  unfold sampleEncodedTableFibrePair EncodedTableFibrePair.representative
  simp only [map_bind, map_pure]
  rw [evalDist_bind]
  let base : SPMF (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    𝒟[uniformEncodedChallengeTable
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)]
  let f : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      SPMF (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    fun table => 𝒟[do
      let representative ← decodedFibreUniformWitness
        (encodedChallengeTableFintype
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (Classical.decEq _)
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)
      pure representative.1]
  let f' : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      SPMF (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    fun table => 𝒟[Preliminaries.uniformPreimageComp
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)]
  change base >>= f = base
  calc
    base >>= f = base >>= f' := by
      apply bind_congr
      intro table
      change 𝒟[Subtype.val <$>
        decodedFibreUniformWitness
          (encodedChallengeTableFintype
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          (Classical.decEq _)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)] =
        𝒟[Preliminaries.uniformPreimageComp
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ)
          (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)]
      unfold decodedFibreUniformWitness
      exact evalDist_uniformPreimageWitnessComp
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)
    _ = 𝒟[sampleEncodedTableFromDecodedFibre
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
        change
          𝒟[uniformEncodedChallengeTable
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] >>=
              (fun table =>
                𝒟[Preliminaries.uniformPreimageComp
                  (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
                  (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ)
                  (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)]) =
            𝒟[sampleEncodedTableFromDecodedFibre
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)]
        unfold sampleEncodedTableFromDecodedFibre
        rw [evalDist_bind]
        rfl
    _ = base := by
        exact evalDist_sampleEncodedTableFromDecodedFibre_eq_uniform
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)

/-- A continuation of the observed member of the joint sample is distributed exactly as the
same continuation of a fresh H₂ uniform table. -/
theorem evalDist_sampleEncodedTableFibrePair_original_bind_eq_uniform
    {α : Type}
    (continuation : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      ProbComp α) :
    𝒟[(sampleEncodedTableFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        fun pair => continuation pair.original)] =
      𝒟[(uniformEncodedChallengeTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        continuation)] := by
  have hfactor :
      sampleEncodedTableFibrePair
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
          (fun pair => continuation pair.original) =
        ((EncodedTableFibrePair.original <$>
          sampleEncodedTableFibrePair
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) >>=
          continuation) := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp
  rw [hfactor, evalDist_bind,
    evalDist_sampleEncodedTableFibrePair_original_eq_uniform, ← evalDist_bind]

/-- A continuation of the representative member of the joint sample is distributed exactly as
the same continuation of a fresh H₁ uniform table. -/
theorem evalDist_sampleEncodedTableFibrePair_representative_bind_eq_uniform
    {α : Type}
    (continuation : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      ProbComp α) :
    𝒟[(sampleEncodedTableFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        fun pair => continuation pair.representative)] =
      𝒟[(uniformEncodedChallengeTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        continuation)] := by
  have hfactor :
      sampleEncodedTableFibrePair
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
          (fun pair => continuation pair.representative) =
        ((EncodedTableFibrePair.representative <$>
          sampleEncodedTableFibrePair
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) >>=
          continuation) := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp
  rw [hfactor, evalDist_bind,
    evalDist_sampleEncodedTableFibrePair_representative_eq_uniform, ← evalDist_bind]

/-- The two tables in a joint sample have the same complete decoded table.  This is a
value-level invariant, not a distributional approximation. -/
theorem EncodedTableFibrePair.decode_representative_eq_original
    (pair : EncodedTableFibrePair (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :
    decodeEncodedChallengeTable (U := U) StmtIn pSpec δ pair.representative =
    decodeEncodedChallengeTable (U := U) StmtIn pSpec δ pair.original :=
  pair.representativeWitness.2

/-- In the joint Claim-5.22 sample, every probabilistic continuation that depends only on the
decoded challenge table has exactly the same computation whether fed H₂'s observed table or
H₁'s fibre representative.  This is the pointwise heart of the whole-game coupling. -/
theorem sampleEncodedTableFibrePair_bind_eq_of_decodedTable_invariant
    {α : Type}
    (continuation : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) →
      ProbComp α)
    (hcontinuation : ∀ table₁ table₂,
      decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₁ =
        decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₂ →
      continuation table₁ = continuation table₂) :
    sampleEncodedTableFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        (fun pair => continuation pair.original) =
      sampleEncodedTableFibrePair
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
        (fun pair => continuation pair.representative) := by
  apply bind_congr
  intro pair
  exact hcontinuation pair.original pair.representative
    pair.decode_representative_eq_original.symm

end LegacyTotalFibre

/-- A fixed-table fibre sampler depends on its encoded-table argument only through the complete
decoded table.  This is the transport point that lets the joint coupling use H₂'s observed table
for the decoded oracle while using the fibre representative for the full-cache H₁ endpoint. -/
theorem decodedFibreSampler_eq_of_decodedTable_eq
    (table₁ table₂ : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (hdecode : decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₁ =
      decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₂) :
    decodedFibreSampler (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table₁ =
      decodedFibreSampler (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table₂ := by
  funext q
  rcases q with ⟨i, key⟩
  unfold decodedFibreSampler
  dsimp only
  have hq := congrFun hdecode ⟨i, key⟩
  change codec.decode i (table₁ ⟨i, key⟩) = codec.decode i (table₂ ⟨i, key⟩) at hq
  rw [hq]

/-- The entire fixed-table fibre stopping handler is likewise invariant under equality of
complete decoded tables.  Its auxiliary arms are table-independent, while its encoded arm uses
the preceding sampler transport. -/
theorem hyb2FibreStoppingD2SDirect_eq_of_decodedTable_eq
    (table₁ table₂ : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (hdecode : decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₁ =
      decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₂) :
    hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table₁ =
      hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table₂ := by
  have hsampler := decodedFibreSampler_eq_of_decodedTable_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table₁ table₂ hdecode
  funext query
  rcases query with query | aux
  · simp only [hyb2FibreStoppingD2SDirect]
    rw [hsampler]
  · rfl

/-- The fixed-table fibre realization of an entire ambient/D2S run depends only on the complete
decoded table.  The ambient branch is literal; the D2S branch is transported through the
stateful stopping handler above. -/
theorem hyb2FibreAmbientD2FStoppingDirectImpl_eq_of_decodedTable_eq
    {ι : Type} {oSpec : OracleSpec ι}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table₁ table₂ : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (hdecode : decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₁ =
      decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₂) :
    hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) oSpecImpl table₁ =
      hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) oSpecImpl table₂ := by
  have hinner := hyb2FibreStoppingD2SDirect_eq_of_decodedTable_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
    table₁ table₂ hdecode
  apply QueryImpl.ext
  rintro (query | request)
  · rfl
  · funext normal cache
    simp only [hyb2FibreAmbientD2FStoppingDirectImpl]
    rw [hinner]

/-- The decoded-table invariance reaches an arbitrary adaptive ambient/D2S residual, including
its normal state, cache, return value, and stopping reason.  This is the game-level transport
needed to replace H₂'s observed table by the coupled fibre representative. -/
theorem hyb2FibreAmbientD2FStoppingDirectResidual_eq_of_decodedTable_eq
    {ι : Type} {oSpec : OracleSpec ι} {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table₁ table₂ : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (hdecode : decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₁ =
      decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table₂)
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    (((simulateQ
      (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
        oSpecImpl table₁) residual).run normal).run cache).run =
      (((simulateQ
        (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl table₂) residual).run normal).run cache).run := by
  rw [hyb2FibreAmbientD2FStoppingDirectImpl_eq_of_decodedTable_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
    oSpecImpl table₁ table₂ hdecode]

/-- In the joint Claim-5.22 sample, replacing H₂'s observed encoded table by its coupled
representative changes no fibre-realized residual at all.  The representative is retained for
the later eager H₁ endpoint; the observed table is retained for H₂'s decoded-oracle execution. -/
theorem hyb2FibreAmbientD2FStoppingDirectResidual_eq_of_fibrePair
    {ι : Type} {oSpec : OracleSpec ι} {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (pair : EncodedTableFibrePair
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    (((simulateQ
      (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
        oSpecImpl pair.original) residual).run normal).run cache).run =
      (((simulateQ
        (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl pair.representative) residual).run normal).run cache).run := by
  exact hyb2FibreAmbientD2FStoppingDirectResidual_eq_of_decodedTable_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
    oSpecImpl pair.original pair.representative
    pair.decode_representative_eq_original.symm residual normal cache

end DuplexSpongeFS.KeyLemma
