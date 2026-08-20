/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.Security.OracleDistribution

/-!
# Adaptive decoded-fibre coupling

This file isolates the exact Claim 5.22 kernel needed by Lemma 5.1.  Once a decoded challenge
table is fixed, an adaptive computation may obtain one uniform encoded representative from each
decoder fibre on its first visit to that key and reuse it subsequently.  The generic lazy-random-
oracle theorem shows that this is exactly eager sampling of the complete fibre table.

The remaining endpoint refinement relates this cache representation to the live memo-list bridge
used by `hyb2Revised`; no probability loss or additional assumption is introduced here.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}

local instance : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _

/-- Caching preserves a pointwise exact distributional equality of two base query handlers.
This is the operational form needed for Claim 5.22: the first occurrence uses the equal
one-cell fibre sampler, and every later occurrence is a deterministic cache hit on both sides. -/
theorem evalDist_simulateQ_withCaching_eq_of_base
    {ι : Type} {spec : OracleSpec ι} [DecidableEq ι] [spec.DecidableEq]
    (base₁ base₂ : QueryImpl spec ProbComp)
    (hbase : ∀ q, 𝒟[base₁ q] = 𝒟[base₂ q])
    {α : Type} (oa : OracleComp spec α) (cache : spec.QueryCache) :
    𝒟[(simulateQ base₁.withCaching oa).run cache] =
      𝒟[(simulateQ base₂.withCaching oa).run cache] := by
  apply OracleComp.evalDist_simulateQ_run_eq_of_impl_evalDist_eq
  intro q cache
  cases hcache : cache q with
  | some response =>
      rw [QueryImpl.withCaching_run_some base₁ hcache]
      rw [QueryImpl.withCaching_run_some base₂ hcache]
  | none =>
      rw [QueryImpl.withCaching_run_none base₁ hcache]
      rw [QueryImpl.withCaching_run_none base₂ hcache]
      exact evalDist_map_eq_of_evalDist_eq (hbase q)
        (fun response => (response, cache.cacheQuery q response))

/-- The fully sampled outer H₂ handler after fixing its underlying encoded table.  This is
defined under `CodecCore`: decoding an encoded-table value never needs a representative of an
arbitrary decoded challenge. -/
noncomputable def decodedBridgeOuterImpl
    [VCVCompatible StmtIn] [VCVCompatible U] [SampleableType U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl
      (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
      ProbComp :=
  (D_e (U := U) StmtIn pSpec δ).toImpl table +
    (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec)

/-- Fixed-table H₂ outer handler in the presence of an arbitrary ambient oracle.  Keeping this
small definition next to the Core bridge prevents the logged Claim 5.22 refinement from
importing the legacy total-fibre development. -/
noncomputable def hyb2AmbientOuterImpl
    {ι : Type} {oSpec : OracleSpec ι}
    [VCVCompatible StmtIn] [VCVCompatible U] [SampleableType U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)) ProbComp
  | .inl query => oSpecImpl query
  | .inr query =>
      decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table query

/- Compatibility layer for the legacy total-decoder bridge.  The Core-only image-fibre route
below is the one appropriate to revised Claim 5.22. -/
/-
Legacy total-fibre bridge.  It is intentionally inactive in the revised
`CodecCore` development.  Any unmigrated client that requires decoder
surjectivity must import a separate legacy module rather than reactivating
this block in the Claim-5.22 dependency path.

variable [codecTotal : CodecTotal pSpec U]

/-- Fixing the H₁ encoded table turns the live H₂ bridge into this ordinary probabilistic
encoded-query handler. -/
noncomputable def decodedBridgeSampledImpl
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp :=
  fun q => simulateQ
    (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table)
    (d2sDecodedBridgeBaseRun (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q)

/-- The eager one-cell fibre sampler, written with the same finite-vector instance used by
`uniformDeserializePreimage`.  This is the base handler to which Claim 5.22 applies caching. -/
noncomputable def decodedFibreSampler
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp :=
  fun ⟨i, key⟩ => by
    letI : Fintype ((gSpec (U := U) StmtIn pSpec δ).Range ⟨i, key⟩) := by
      change Fintype (Vector U (challengeSize (pSpec := pSpec) i))
      exact instFintypeVector U (challengeSize (pSpec := pSpec) i)
    exact Preliminaries.uniformPreimageComp
      (codec.decode i) (codecTotal.decode_surjective i)
      (codec.decode i (table ⟨i, key⟩))

/-- Semantics of the eager one-cell fibre sampler. -/
theorem evalDist_decodedFibreSampler_eq_uniformFibre
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    𝒟[decodedFibreSampler (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q] =
      (liftM (@Preliminaries.sampleUniformPreimage
        (pSpec.Challenge q.1) (Vector U (challengeSize (pSpec := pSpec) q.1))
        (inferInstance : DecidableEq (pSpec.Challenge q.1))
        (instFintypeVector U (challengeSize (pSpec := pSpec) q.1))
        (codec.decode q.1) (codecTotal.decode_surjective q.1)
        (codec.decode q.1 (table q))) : SPMF (Vector U (challengeSize (pSpec := pSpec) q.1))) := by
  rcases q with ⟨i, key⟩
  unfold decodedFibreSampler
  dsimp only
  exact Preliminaries.evalDist_uniformPreimageComp
    (codec.decode i) (codecTotal.decode_surjective i)
    (codec.decode i (table ⟨i, key⟩))

/-- One fresh H₂ bridge step under a fixed encoded table is exactly a uniform encoded
representative of the corresponding decoder fibre. -/
theorem evalDist_decodedBridgeSampledImpl_eq_uniformFibre
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    𝒟[decodedBridgeSampledImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      table q] =
      (liftM (@Preliminaries.sampleUniformPreimage
        (pSpec.Challenge q.1) (Vector U (challengeSize (pSpec := pSpec) q.1))
        (inferInstance : DecidableEq (pSpec.Challenge q.1))
        (instFintypeVector U (challengeSize (pSpec := pSpec) q.1))
        (codec.decode q.1) (codecTotal.decode_surjective q.1)
        (codec.decode q.1 (table q))) : SPMF (Vector U (challengeSize (pSpec := pSpec) q.1))) := by
  unfold decodedBridgeSampledImpl
  have hrun :
      simulateQ
        (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table)
        (d2sDecodedBridgeBaseRun (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q) =
      simulateQ
        (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table)
        (uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (codec.decode q.1 (table q))) := by
    unfold d2sDecodedBridgeBaseRun
    simp only [HasQuery.instOfMonadLift_query]
    rw [simulateQ_bind]
    calc
      _ = decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table (.inl q) >>=
          fun challenge =>
            simulateQ
              (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table)
              (uniformDeserializePreimage challenge) := by
          exact congrArg
            (fun computation => computation >>= fun challenge =>
              simulateQ
                (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table)
                (uniformDeserializePreimage challenge))
            (simulateQ_spec_query
              (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table) (.inl q))
      _ = _ := by
        have houter :
            decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table (.inl q) =
              pure (codec.decode q.1 (table q)) := by
          change (D_e (U := U) StmtIn pSpec δ).toImpl table q =
            pure (codec.decode q.1 (table q))
          exact D_e_toImpl_apply StmtIn pSpec δ table q.1 q.2
        calc
          _ = pure (codec.decode q.1 (table q)) >>= fun challenge =>
              simulateQ
                (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table)
                (uniformDeserializePreimage challenge) :=
              congrArg
                (fun computation => computation >>= fun challenge =>
                  simulateQ
                    (decodedBridgeOuterImpl (pSpec := pSpec) (U := U) (δ := δ) table)
                    (uniformDeserializePreimage challenge))
                houter
          _ = _ := by simp only [pure_bind]
  rw [hrun]
  change 𝒟[simulateQ
    ((D_e (U := U) StmtIn pSpec δ).toImpl table +
      (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
    (uniformDeserializePreimage (codec.decode q.1 (table q)))] =
    (liftM (@Preliminaries.sampleUniformPreimage
      (pSpec.Challenge q.1) (Vector U (challengeSize (pSpec := pSpec) q.1))
      (inferInstance : DecidableEq (pSpec.Challenge q.1))
      (instFintypeVector U (challengeSize (pSpec := pSpec) q.1))
      (codec.decode q.1) (codecTotal.decode_surjective q.1)
      (codec.decode q.1 (table q))) : SPMF (Vector U (challengeSize (pSpec := pSpec) q.1)))
  exact evalDist_simulateQ_uniformDeserializePreimage
    (pSpec := pSpec) (U := U)
    (challengeSpec := eSpec (U := U) StmtIn pSpec δ) (i := q.1)
    ((D_e (U := U) StmtIn pSpec δ).toImpl table)
    (codec.decode q.1 (table q))

/-- Conditional on the encoded H₁ table, the executable H₂ bridge and the direct fibre sampler
have the same one-query distribution. -/
theorem evalDist_decodedBridgeSampledImpl_eq_decodedFibreSampler
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    𝒟[decodedBridgeSampledImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      table q] =
      𝒟[decodedFibreSampler (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        table q] := by
  calc
    _ = (liftM (@Preliminaries.sampleUniformPreimage
        (pSpec.Challenge q.1) (Vector U (challengeSize (pSpec := pSpec) q.1))
        (inferInstance : DecidableEq (pSpec.Challenge q.1))
        (instFintypeVector U (challengeSize (pSpec := pSpec) q.1))
        (codec.decode q.1) (codecTotal.decode_surjective q.1)
        (codec.decode q.1 (table q))) : SPMF (Vector U (challengeSize (pSpec := pSpec) q.1))) :=
      evalDist_decodedBridgeSampledImpl_eq_uniformFibre
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q
    _ = _ := (evalDist_decodedFibreSampler_eq_uniformFibre
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q).symm

/-- **Adaptive fixed-table Claim 5.22.**  Once the H₁ encoded table is fixed, the H₂ bridge
may be replaced by eager fibre sampling even for an adaptive sequence of repeated `g` queries.
The cache makes the first-query/reuse discipline explicit on both sides. -/
theorem evalDist_cachedDecodedBridge_eq_cachedFibreSampler
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    {α : Type} (oa : OracleComp (gSpec (U := U) StmtIn pSpec δ) α)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[(simulateQ
      (decodedBridgeSampledImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching
      oa).run cache] =
      𝒟[(simulateQ
        (decodedFibreSampler
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching
        oa).run cache] := by
  classical
  exact evalDist_simulateQ_withCaching_eq_of_base
    (decodedBridgeSampledImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
    (decodedFibreSampler (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
    (fun q => evalDist_decodedBridgeSampledImpl_eq_decodedFibreSampler
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q)
    oa cache

/-- The fixed-table bridge restricted to the complete D2S action interface.  Its `g` arm uses
the cached decoded bridge; its auxiliary arms retain their ordinary fresh-sampling semantics. -/
noncomputable def decodedBridgeD2SImpl
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache ProbComp) := by
  classical
  exact fun
    | .inl q => (decodedBridgeSampledImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching q
    | .inr q => StateT.lift <|
        (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) q

/-- The companion complete D2S action handler that samples a uniform representative from the
fixed table's decoder fibre on the first visit to an encoded `gᵢ` key. -/
noncomputable def decodedFibreD2SImpl
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache ProbComp) := by
  classical
  exact fun
    | .inl q => (decodedFibreSampler
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching q
    | .inr q => StateT.lift <|
        (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) q

/-- One complete D2S action has the same conditional distribution under the fixed-table decoded
bridge and under fixed-table fibre sampling.  In particular, this equality includes cache hits,
cache misses, and both non-cached auxiliary oracle arms. -/
theorem evalDist_decodedBridgeD2SImpl_eq_decodedFibreD2SImpl
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[(decodedBridgeD2SImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q).run cache] =
      𝒟[(decodedFibreD2SImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q).run cache] := by
  classical
  rcases q with q | q
  · simpa only [decodedBridgeD2SImpl, decodedFibreD2SImpl, simulateQ_spec_query] using
      (evalDist_simulateQ_withCaching_eq_of_base
        (decodedBridgeSampledImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        (decodedFibreSampler
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        (fun q => evalDist_decodedBridgeSampledImpl_eq_decodedFibreSampler
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q)
        (liftM ((gSpec (U := U) StmtIn pSpec δ).query q)) cache)
  · rfl

/-- **Adaptive D2S-action Claim 5.22.**  Once the H₁ encoded table is fixed, the decoded bridge
and the uniform-fibre realization have identical output-and-cache distributions for every
adaptive program over the full D2S action interface.  Thus hash/inverse/auxiliary actions may be
interleaved arbitrarily with repeated `gᵢ` keys; only a `gᵢ` cache miss samples a new fibre
point. -/
theorem evalDist_simulateQ_decodedBridgeD2SImpl_eq_decodedFibreD2SImpl
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    {α : Type}
    (oa : OracleComp
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) α)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[(simulateQ
      (decodedBridgeD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table) oa).run
      cache] =
      𝒟[(simulateQ
        (decodedFibreD2SImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table) oa).run cache] := by
  apply OracleComp.evalDist_simulateQ_run_eq_of_impl_evalDist_eq
  intro q cache
  exact evalDist_decodedBridgeD2SImpl_eq_decodedFibreD2SImpl
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q cache

/-- Fixing the H₂ encoded table commutes with the live cache implementation.  More precisely,
executing the live bridge under the fixed decoded-table handler is the abort-free lifting of the
ordinary cached probabilistic bridge.  This is the operational link from the one-cell Claim 5.22
law to an H₂ game run whose outer `D_e` table has already been sampled. -/
theorem simulateQ_decodedBridgeImplCache_run_eq_cachedSampled
    [Fintype U] [DecidableEq U] [SampleableType U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    simulateQ
      (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      ((d2sDecodedBridgeImplCache
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run cache) =
      OptionT.lift
        (((decodedBridgeSampledImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching q).run
          cache) := by
  classical
  cases hcache : cache q with
  | some response =>
      rw [d2sDecodedBridgeImplCache_run_of_hit
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q cache response hcache]
      rw [QueryImpl.withCaching_run_some
        (decodedBridgeSampledImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        hcache]
      rfl
  | none =>
      rw [d2sDecodedBridgeImplCache_run_of_miss
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q cache hcache]
      rw [QueryImpl.withCaching_run_none
        (decodedBridgeSampledImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        hcache]
      rfl

-/

/-- The Core-only fixed-table fibre sampler for revised Claim 5.22.  Its target is the fibre
of the decoded value actually obtained from `table`; hence `table q` itself is the required
image witness and no decoder-surjectivity assumption is present. -/
noncomputable def decodedFibreSamplerOfImage
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp :=
  fun q => by
    rcases q with ⟨i, key⟩
    letI : Fintype ((gSpec (U := U) StmtIn pSpec δ).Range ⟨i, key⟩) := by
      change Fintype (Vector U (challengeSize (pSpec := pSpec) i))
      exact instFintypeVector U (challengeSize (pSpec := pSpec) i)
    exact Preliminaries.uniformPreimageCompOfImage
      (codec.decode i)
      (codec.decode i (table ⟨i, key⟩))
      ⟨table ⟨i, key⟩, rfl⟩

/-- Pointwise distributional semantics of the Core-only fixed-table sampler. -/
theorem evalDist_decodedFibreSamplerOfImage_eq_uniformFibre
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    𝒟[decodedFibreSamplerOfImage (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      table q] =
      (liftM (Preliminaries.sampleUniformPreimageOfImage (codec.decode q.1)
        (codec.decode q.1 (table q)) ⟨table q, rfl⟩) :
        SPMF (Vector U (challengeSize (pSpec := pSpec) q.1))) := by
  rcases q with ⟨i, key⟩
  unfold decodedFibreSamplerOfImage
  dsimp only
  exact Preliminaries.evalDist_uniformPreimageCompOfImage
    (codec.decode i) (codec.decode i (table ⟨i, key⟩)) ⟨table ⟨i, key⟩, rfl⟩

/-- Every decoded H₂ table cell is in the image of its corresponding decoder, witnessed by the
encoded table cell from which it was decoded.  This is the exact reason the revised H₂ handler
never reaches its partial-lift failure branch. -/
lemma decodedTableCell_preimages_nonempty
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    (deserializePreimageFinset (pSpec := pSpec) (U := U)
      (codec.decode q.1 (table q))).Nonempty := by
  refine ⟨table q, ?_⟩
  simp only [deserializePreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  change (Codec.instDeserializeChallenge (pSpec := pSpec) (U := U) q.1).deserialize (table q) = _
  rfl

/-- A fixed H₂ table turns the bridge's first decoded lookup into the corresponding deterministic
decoded table cell.  This deliberately retains the `OptionT` shape of the live bridge: the
following cache/fibre lemma can therefore be applied at the real executable boundary rather than
to a separately invented oracle. -/
theorem simulateQ_decodedBridgeOuter_firstLookup_eq
    [VCVCompatible StmtIn] [VCVCompatible U] [SampleableType U]
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    simulateQ
      (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      ((do
        let challenge ← OptionT.lift (query
          (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (.inl q))
        pure (challenge, cache)) :
          OptionT (OracleComp
            (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)))
            ((pSpec.Challenge q.1) × (gSpec (U := U) StmtIn pSpec δ).QueryCache)) =
      (pure (codec.decode q.1 (table q), cache) : OptionT ProbComp _) := by
  rw [simulateQ_optionT_bind, simulateQ_optionT_lift]
  change (OptionT.lift
    (simulateQ (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) table) (liftM (OracleSpec.query (Sum.inl q)))) >>= fun challenge =>
      simulateQ (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (δ := δ) table) (pure (some (challenge, cache)))) = _
  rw [simulateQ_spec_query]
  simp only [decodedBridgeOuterImpl, simulateQ_pure]
  rfl

/-- Run the partial `Lift` sampler after a fixed implementation of the decoded challenge oracle.
The definition is intentionally table-agnostic: it is the small Core-only contract that the live
H₂ outer lookup is reduced to before any cache or adaptive-run reasoning is performed. -/
noncomputable def sampledFibreAfterDecodedLookup
    {κ : Type} {challengeSpec : OracleSpec κ}
    [SampleableType U]
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (challenge : pSpec.Challenge i)
    (hpreimages :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty) :
    ProbComp (Vector U (challengeSize (pSpec := pSpec) i)) :=
  simulateQ (challengeImpl + (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
    (uniformDeserializePreimageOfImage (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec) challenge hpreimages)

/-- Exact one-cell distribution of `sampledFibreAfterDecodedLookup`.  This is the partial,
non-surjective counterpart of the legacy total-decoder fibre law. -/
theorem evalDist_sampledFibreAfterDecodedLookup
    {κ : Type} {challengeSpec : OracleSpec κ}
    [SampleableType U]
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (challenge : pSpec.Challenge i)
    (hpreimages :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty) :
    𝒟[sampledFibreAfterDecodedLookup (pSpec := pSpec) (U := U)
      challengeImpl challenge hpreimages] =
      (liftM (Preliminaries.sampleUniformPreimageOfImage (codec.decode i) challenge (by
        rcases hpreimages with ⟨preimage, hpreimage⟩
        refine ⟨preimage, ?_⟩
        simpa [deserializePreimageFinset] using hpreimage)) :
        SPMF (Vector U (challengeSize (pSpec := pSpec) i))) := by
  exact evalDist_simulateQ_uniformDeserializePreimageOfImage
    (pSpec := pSpec) (U := U) challengeImpl challenge hpreimages

/-- The ordinary fixed-table, partial-fibre query handler underlying the live H₂ bridge.
Unlike the live handler it contains no outer `e` query: after fixing the H₂ table that query is
deterministic.  The later cache-realization proof is responsible for restoring the exact live
occurrence/log behavior. -/
noncomputable def decodedBridgeSampledImplOfImage
    [VCVCompatible StmtIn] [VCVCompatible U] [SampleableType U]
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp :=
  fun q => simulateQ
    (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
    (uniformDeserializePreimageOfImage (pSpec := pSpec) (U := U)
      (challengeSpec := eSpec (U := U) StmtIn pSpec δ)
      (codec.decode q.1 (table q))
      (decodedTableCell_preimages_nonempty (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (δ := δ) table q))

/-- The dependent encoded-response oracle obtained by taking, at each `e`-table cell, the fibre
of its decoded challenge. -/
def decodedFibreSpec
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    OracleSpec (gSpec (U := U) StmtIn pSpec δ).Domain :=
  fun q => Preliminaries.Preimage (codec.decode q.1) (decoded q)

/-- Translate a `g` query into a query to the corresponding decoded-table fibre and forget the
subtype witness. -/
def decodedFibreLiftImpl
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (OracleComp (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
  fun q => do
    let response ← query
      (spec := decodedFibreSpec (pSpec := pSpec) (U := U) decoded) q
    pure response.1

/-- Run an arbitrary adaptive encoded-challenge computation against the fibre oracle. -/
def decodedFibreLift
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    {α : Type} (oa : OracleComp (gSpec (U := U) StmtIn pSpec δ) α) :
    OracleComp (decodedFibreSpec (pSpec := pSpec) (U := U) decoded) α :=
  simulateQ (decodedFibreLiftImpl (pSpec := pSpec) (U := U) decoded) oa

/-- The lazy encoded-fibre oracle.  It caches a representative of the fibre at each encoded
key, and therefore exposes the same representative at every repeated key. -/
def decodedFibreLazyImpl
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    [∀ q, SampleableType
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)] :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (StateT
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache ProbComp) :=
  fun q => do
    let response ← OracleSpec.randomOracle
      (spec := decodedFibreSpec (pSpec := pSpec) (U := U) decoded) q
    pure response.1

/-- Translating `g` queries into fibre queries and then lazily sampling the fibre is exactly the
same stateful computation as handling `g` queries directly with the lazy fibre oracle. -/
theorem simulateQ_randomOracle_decodedFibreLift
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    [∀ q, SampleableType
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)]
    {α : Type} (oa : OracleComp (gSpec (U := U) StmtIn pSpec δ) α) :
    simulateQ
      (OracleSpec.randomOracle
        (spec := decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
      (decodedFibreLift (pSpec := pSpec) (U := U) decoded oa) =
    simulateQ (decodedFibreLazyImpl (pSpec := pSpec) (U := U) decoded) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
    simp only [decodedFibreLift, simulateQ_bind, decodedFibreLiftImpl,
      simulateQ_spec_query, simulateQ_pure, decodedFibreLazyImpl]
    rw [show simulateQ
        (OracleSpec.randomOracle
          (spec := decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
        (query (spec := decodedFibreSpec (pSpec := pSpec) (U := U) decoded) q) =
      OracleSpec.randomOracle
        (spec := decodedFibreSpec (pSpec := pSpec) (U := U) decoded) q by
          apply simulateQ_spec_query]
    apply bind_congr
    intro response
    exact ih response

/-- Eagerly evaluating the lifted fibre computation is evaluation of the original computation by
the underlying encoded representatives. -/
theorem evalWithAnswerFn_decodedFibreLift
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (encoded : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
    {α : Type} (oa : OracleComp (gSpec (U := U) StmtIn pSpec δ) α) :
    evalWithAnswerFn (QueryImpl.ofFn encoded)
      (decodedFibreLift (pSpec := pSpec) (U := U) decoded oa) =
    evalWithAnswerFn
      (QueryImpl.ofFn (spec := gSpec (U := U) StmtIn pSpec δ)
        fun q => (encoded q).1) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
    simp only [decodedFibreLift, simulateQ_bind, decodedFibreLiftImpl,
      simulateQ_spec_query, evalWithAnswerFn_bind, evalWithAnswerFn_query]
    exact ih _

/-- **Adaptive fibre realization.**  For every adaptive `g`-oracle computation, lazy uniform
sampling of an encoded representative from each decoded fibre is exactly eager sampling of the
complete fibre table. -/
theorem evalDist_decodedFibreLazyImpl_eq_eager
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    [Finite (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain]
    [∀ q, Finite
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)]
    [∀ q, Nonempty
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)]
    [∀ q, SampleableType
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)]
    [SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    {α : Type} (oa : OracleComp (gSpec (U := U) StmtIn pSpec δ) α) :
    𝒟[(simulateQ
      (decodedFibreLazyImpl (pSpec := pSpec) (U := U) decoded) oa).run' ∅] =
      𝒟[do
        let encoded ← $ᵗ OracleReduction.OracleFamily
          (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
        pure (evalWithAnswerFn
          (QueryImpl.ofFn (spec := gSpec (U := U) StmtIn pSpec δ)
            fun q => (encoded q).1) oa)] := by
  rw [← simulateQ_randomOracle_decodedFibreLift (pSpec := pSpec) (U := U) decoded oa]
  rw [OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_dependentUniformTable]
  simp_rw [evalWithAnswerFn_decodedFibreLift (pSpec := pSpec) (U := U) decoded]

end DuplexSpongeFS.ProverTransform
