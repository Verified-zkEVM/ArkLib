/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SAmbientRefinement
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadAdaptive
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadArithmetic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ExactVerifierCounting

/-!
# Exact eager/lazy coupling for Hyb₁'s encoded challenge table

This module proves the table-sampling part of the live Hyb₀--Hyb₁ coupling.
It works for the complete outer oracle, so arbitrary ambient calls stay literal
base-monad effects and need no query-count hypothesis.
-/

noncomputable section

set_option linter.style.longFile 1700

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]

/- The eager/lazy equality below must use the explicit finite-table sampler from
`D_SigmaFinite`.  Keeping it local prevents the old low-priority compatibility instance (whose
domain need not be finite) from entering this revised proof path through `$ᵗ OracleFamily`. -/
local instance : SampleableType
    (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
  sampleableEncodedChallengeOracle

/-- Resampling one coordinate and overwriting the same coordinate of a uniform dependent table
preserves its distribution.  This generic cache/table exchange is shared by the H₁ eager/lazy
coupling and the analogous H₂ decoder-fibre coupling. -/
theorem evalDist_uniformSample_bind_update_dependent_effect
    {D : Type} {R : D → Type} {α : Type}
    [Finite D] [DecidableEq D] [∀ d, Finite (R d)] [∀ d, Nonempty (R d)]
    [(d : D) → SampleableType (R d)] [SampleableType ((d : D) → R d)]
    (q : D) (ψ : ((d : D) → R d) → ProbComp α) :
    𝒟[do
      let answer ← $ᵗ R q
      let table ← $ᵗ ((d : D) → R d)
      ψ (Function.update table q answer)] =
    𝒟[do
      let table ← $ᵗ ((d : D) → R d)
      ψ table] := by
  have h := congrArg (fun μ => μ >>= fun table => 𝒟[ψ table])
    (evalDist_uniformSample_bind_update_dependent (R := R) q)
  change
    (𝒟[do
      let answer ← $ᵗ R q
      let table ← $ᵗ ((d : D) → R d)
      pure (Function.update table q answer)] >>= fun table => 𝒟[ψ table]) =
    (𝒟[$ᵗ ((d : D) → R d)] >>= fun table => 𝒟[ψ table]) at h
  rw [← evalDist_bind, ← evalDist_bind] at h
  simpa [bind_assoc] using h

private theorem evalDist_simulateQ_hyb1LazyOuterImpl_lift_step {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (z : (oSpec + D2SChallengePlusUnitOracle (U := U)
      (gSpec (U := U) StmtIn pSpec δ)).Domain)
    (base : ProbComp ((oSpec + D2SChallengePlusUnitOracle (U := U)
      (gSpec (U := U) StmtIn pSpec δ)).Range z))
    (k : (oSpec + D2SChallengePlusUnitOracle (U := U)
      (gSpec (U := U) StmtIn pSpec δ)).Range z →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (hLazy :
      (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl z).run cache =
        (fun answer => (answer, cache)) <$> base)
    (hEager : ∀ table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ),
      hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl cache table z = base)
    (ih : ∀ answer cache,
      𝒟[(simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k answer)).run' cache] =
      𝒟[do
        let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) (k answer)]) :
    𝒟[(simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
      (liftM (OracleSpec.query z) >>= k)).run' cache] =
    𝒟[do
      let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
      simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table)
        (liftM (OracleSpec.query z) >>= k)] := by
  have hred :
      (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
        (liftM (OracleSpec.query z) >>= k)).run' cache =
        ((hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl z).run cache) >>=
          fun pair =>
            (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run' pair.2 := by
    rw [simulateQ_bind, simulateQ_spec_query]
    change Prod.fst <$> (((hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl z).run cache) >>=
      fun pair =>
        (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run pair.2) = _
    rw [map_bind]
    rfl
  have heval : ∀ table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ),
      simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table)
        (liftM (OracleSpec.query z) >>= k) =
      base >>= fun answer =>
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) (k answer) := by
    intro table
    rw [simulateQ_bind, simulateQ_spec_query, hEager]
  rw [hred, hLazy]
  have hpair :
      (((fun answer => (answer, cache)) <$> base) >>= fun pair =>
        (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run' pair.2) =
      base >>= fun answer =>
        (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k answer)).run' cache := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp
  have hmid :
      𝒟[base >>= fun answer => do
        let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) (k answer)] =
      (do
        let answer ← 𝒟[base]
        let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
        𝒟[simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) (k answer)]) := by
    rw [evalDist_bind]
    refine congrArg _ (funext fun answer => ?_)
    rw [evalDist_bind]
  calc
    𝒟[((fun answer => (answer, cache)) <$> base) >>= fun pair =>
      (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run' pair.2] =
      𝒟[base >>= fun answer =>
        (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k answer)).run' cache] :=
      congrArg _ hpair
    _ = (do
      let answer ← 𝒟[base]
      let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
      𝒟[simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) (k answer)]) := by
      rw [evalDist_bind]
      refine congrArg _ (funext fun answer => ?_)
      rw [ih answer cache, evalDist_bind]
    _ = 𝒟[do
      let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
      simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table)
        (liftM (OracleSpec.query z) >>= k)] := by
      simp_rw [heval]
      simp_rw [evalDist_bind]
      ext x
      exact probOutput_bind_bind_swap
        (𝒟[base])
        (𝒟[$ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))])
        (fun answer table =>
          𝒟[simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) (k answer)]) x
  rfl

private theorem evalDist_simulateQ_hyb1LazyOuterImpl_g_step
    {α : Type} (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (k : (gSpec (U := U) StmtIn pSpec δ).Range q →
      OracleComp
        (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ)) α)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (ih : ∀ answer cache,
      𝒟[(simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k answer)).run' cache] =
      𝒟[do
        let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) (k answer)]) :
    𝒟[(simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
      (liftM (OracleSpec.query (spec := oSpec +
        D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
        (Sum.inr (Sum.inl q))) >>= k)).run' cache] =
      𝒟[do
        let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table)
          (liftM (OracleSpec.query (spec := oSpec +
            D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
            (Sum.inr (Sum.inl q))) >>= k)] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _
  letI : FinEnum StmtIn := VCVCompatible.instFinEnum
  letI : FinEnum U := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) : FinEnum (pSpec.EncodedMessagesBefore U i.1.castSucc) :=
    inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((gSpecInterface (U := U) StmtIn pSpec δ i).Query) := by
    change FinEnum (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)
    infer_instance
  letI : FinEnum (gSpec (U := U) StmtIn pSpec δ).Domain := inferInstance
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI : Finite (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.finite (by infer_instance)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Fintype ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    change Fintype (Vector U (challengeSize q.1))
    infer_instance
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Finite ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
    Fintype.finite (by infer_instance)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Nonempty ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    change Nonempty (Vector U (challengeSize q.1))
    infer_instance
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      SampleableType ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change SampleableType (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  haveI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun q => Classical.arbitrary _⟩
  have hred :
      (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k)).run' cache =
        ((hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl
          (Sum.inr (Sum.inl q))).run cache) >>= fun pair =>
            (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run' pair.2 := by
    rw [simulateQ_bind, simulateQ_spec_query]
    change Prod.fst <$> (((hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl (Sum.inr (Sum.inl q))).run cache) >>=
      fun pair => (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run pair.2) = _
    rw [map_bind]
    rfl
  have heval : ∀ table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ),
      simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k) =
      simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table)
        (k (OracleComp.dependentTableExtending cache table q)) := by
    intro table
    rw [simulateQ_bind, simulateQ_spec_query]
    rfl
  rw [hred]
  have hlazyq :
      (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl (Sum.inr (Sum.inl q))).run cache =
        (OracleSpec.randomOracle (spec := gSpec (U := U) StmtIn pSpec δ) q).run cache :=
      rfl
  rw [hlazyq]
  simp_rw [heval]
  rcases hcache : cache q with _ | answer
  · rw [show ((OracleSpec.randomOracle (spec := gSpec (U := U) StmtIn pSpec δ) q).run cache) =
        (fun answer => (answer, cache.cacheQuery q answer)) <$>
          ($ᵗ (gSpec (U := U) StmtIn pSpec δ).Range q) from
          QueryImpl.withCaching_run_none _ hcache]
    change
      𝒟[((fun answer => (answer, cache.cacheQuery q answer)) <$>
        ($ᵗ (gSpec (U := U) StmtIn pSpec δ).Range q)) >>= fun pair =>
          (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run' pair.2] = _
    rw [show (((fun answer => (answer, cache.cacheQuery q answer)) <$>
          ($ᵗ (gSpec (U := U) StmtIn pSpec δ).Range q)) >>= fun pair =>
        (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k pair.1)).run' pair.2) =
        (($ᵗ (gSpec (U := U) StmtIn pSpec δ).Range q) >>= fun answer =>
          (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k answer)).run'
              (cache.cacheQuery q answer)) from by
            rw [map_eq_bind_pure_comp]
            simp [bind_assoc]]
    set ψ : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) → ProbComp α :=
      fun table =>
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table)
          (k (OracleComp.dependentTableExtending cache table q)) with hψ
    have hfun : ∀ answer : (gSpec (U := U) StmtIn pSpec δ).Range q,
        (fun table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) =>
          simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl
            (cache.cacheQuery q answer) table) (k answer)) =
          fun table => ψ (Function.update table q answer) := by
      intro answer
      funext table
      simp only [hψ]
      rw [hyb1LazyOverlayOuterImpl_cacheQuery_eq_update
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl cache table hcache answer]
      simp [OracleComp.dependentTableExtending, hcache]
    trans 𝒟[do
      let answer ← $ᵗ (gSpec (U := U) StmtIn pSpec δ).Range q
      let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
      ψ (Function.update table q answer)]
    · rw [evalDist_bind, evalDist_bind]
      refine congrArg _ (funext fun answer => ?_)
      rw [ih answer (cache.cacheQuery q answer)]
      refine congrArg _ ?_
      apply bind_congr
      intro table
      exact congrFun (hfun answer) table
    · exact evalDist_uniformSample_bind_update_dependent_effect q ψ
  · rw [show ((OracleSpec.randomOracle (spec := gSpec (U := U) StmtIn pSpec δ) q).run cache) =
        (pure (answer, cache) : ProbComp _) from
          QueryImpl.withCaching_run_some _ hcache]
    change 𝒟[(simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) (k answer)).run' cache] = _
    rw [ih answer cache]
    refine congrArg _ ?_
    refine congrArg _ (funext fun table => ?_)
    congr 1
    have hlookup : OracleComp.dependentTableExtending cache table q = answer := by
      simp [OracleComp.dependentTableExtending, hcache]
    rw [hlookup]

theorem evalDist_simulateQ_hyb1LazyOuterImpl_run'_eq_eager
    {α : Type} (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ)) α)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[(simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) oa).run' cache] =
      𝒟[do
        let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl cache table) oa] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _
  letI : FinEnum StmtIn := VCVCompatible.instFinEnum
  letI : FinEnum U := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) : FinEnum (pSpec.EncodedMessagesBefore U i.1.castSucc) :=
    inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((gSpecInterface (U := U) StmtIn pSpec δ i).Query) := by
    change FinEnum (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)
    infer_instance
  letI : FinEnum (gSpec (U := U) StmtIn pSpec δ).Domain := inferInstance
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI : Finite (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.finite (by infer_instance)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Fintype ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    change Fintype (Vector U (challengeSize q.1))
    infer_instance
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Finite ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
    Fintype.finite (by infer_instance)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Nonempty ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    change Nonempty (Vector U (challengeSize q.1))
    infer_instance
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      SampleableType ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change SampleableType (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  haveI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun q => Classical.arbitrary _⟩
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      have hlhs :
          (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
              (pure a : OracleComp _ α)).run' cache =
            (pure a : ProbComp α) := by
        rw [simulateQ_pure]
        change (fun x => x.1) <$> (pure (a, cache) : ProbComp (α × _)) = pure a
        rw [map_pure]
      rw [hlhs]
      simp_rw [simulateQ_pure]
      symm
      refine evalDist_ext fun x => ?_
      rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one'
          (mx := $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)))
          (by simp), one_mul]
  | query_bind z k ih =>
      rcases z with z | z | z | z
      · exact evalDist_simulateQ_hyb1LazyOuterImpl_lift_step
          oSpecImpl (Sum.inl z) (oSpecImpl z) k cache
          (hyb1LazyOuterImpl_ambient oSpecImpl z cache)
          (fun _ => rfl) ih
      · exact evalDist_simulateQ_hyb1LazyOuterImpl_g_step oSpecImpl z k cache ih
      · exact evalDist_simulateQ_hyb1LazyOuterImpl_lift_step
          oSpecImpl (Sum.inr (Sum.inr (Sum.inl z)))
          (d2sUnitSampleImpl (U := U) z) k cache rfl (fun _ => rfl) ih
      · exact evalDist_simulateQ_hyb1LazyOuterImpl_lift_step
          oSpecImpl (Sum.inr (Sum.inr (Sum.inr z)))
          ((QueryImpl.id' unifSpec) z) k cache rfl (fun _ => rfl) ih

/-- One eager Hyb₁ query leaves the sampled table unchanged and agrees with the
empty-cache lazy overlay at that table. -/
private theorem hybChallengeImpl_run_eq_lazyOverlay
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (oSpec + D2SChallengePlusUnitOracle (U := U)
      (gSpec (U := U) StmtIn pSpec δ)).Domain) :
    (hybChallengeImpl (oSpec := oSpec) (U := U)
      (challengeSpec := gSpec (U := U) StmtIn pSpec δ) oSpecImpl
      (D_SigmaFinite (U := U) StmtIn pSpec δ) q).run table =
      (fun answer => (answer, table)) <$>
        hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl ∅ table q := by
  classical
  rcases q with q | q | q | q
  · simp only [hybChallengeImpl, hyb1LazyOverlayOuterImpl]
    simp
    rfl
  · simp only [hybChallengeImpl, hyb1LazyOverlayOuterImpl]
    change (do
      let kC : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) ← StateT.get
      let resp ← StateT.lift (pure (kC q))
      pure resp).run table =
      pure (OracleComp.dependentTableExtending ∅ table q, table)
    rw [OracleComp.dependentTableExtending_empty]
    rfl
  · simp only [hybChallengeImpl, hyb1LazyOverlayOuterImpl]
    simp
    rfl
  · simp only [hybChallengeImpl, hyb1LazyOverlayOuterImpl]
    simp
    rfl

/-- Running the eagerly sampled Hyb₁ table preserves that table throughout the
entire outer-oracle computation.  The result is the corresponding empty-cache
lazy overlay, paired with the unchanged table. -/
private theorem simulateQ_hybChallengeImpl_run_eq_lazyOverlay
    {α : Type} (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    (simulateQ (hybChallengeImpl (oSpec := oSpec) (U := U)
      (challengeSpec := gSpec (U := U) StmtIn pSpec δ) oSpecImpl
      (D_SigmaFinite (U := U) StmtIn pSpec δ)) oa).run table =
      (fun answer => (answer, table)) <$>
        simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl ∅ table) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      simp
      rfl
  | query_bind q k ih =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      rw [hybChallengeImpl_run_eq_lazyOverlay oSpecImpl table q]
      simp_rw [map_eq_bind_pure_comp]
      have hleft :
          ((hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl ∅ table q >>=
            pure ∘ fun answer => (answer, table)) >>=
            fun pair =>
              (simulateQ (hybChallengeImpl (oSpec := oSpec) (U := U)
                (challengeSpec := gSpec (U := U) StmtIn pSpec δ) oSpecImpl
                (D_SigmaFinite (U := U) StmtIn pSpec δ)) (k pair.1)).run pair.2) =
          (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl ∅ table q >>=
            fun answer =>
              (simulateQ (hybChallengeImpl (oSpec := oSpec) (U := U)
                (challengeSpec := gSpec (U := U) StmtIn pSpec δ) oSpecImpl
                (D_SigmaFinite (U := U) StmtIn pSpec δ)) (k answer)).run table) := by
        rw [bind_assoc]
        apply bind_congr
        intro answer
        simp
      refine hleft.trans ?_
      simp_rw [ih]
      rw [bind_assoc]
      rfl

/-- The eagerly sampled Hyb₁ game has the same output distribution as its
empty-cache lazy overlay with the same table. -/
theorem evalDist_simulateQ_hybChallengeImpl_run'_eq_lazyOverlay
    {α : Type} (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    𝒟[(simulateQ (hybChallengeImpl (oSpec := oSpec) (U := U)
      (challengeSpec := gSpec (U := U) StmtIn pSpec δ) oSpecImpl
      (D_SigmaFinite (U := U) StmtIn pSpec δ)) oa).run' table] =
      𝒟[simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl ∅ table) oa] := by
  rw [StateT.run'_eq, simulateQ_hybChallengeImpl_run_eq_lazyOverlay, evalDist_map]
  change Prod.fst <$> 𝒟[(fun answer => (answer, table)) <$>
    simulateQ (hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl ∅ table) oa] = _
  rw [evalDist_map]
  rw [SPMF.fmap_eq_map, SPMF.fmap_eq_map, PMF.map_comp]
  change PMF.map (Option.map Prod.fst ∘
    Option.map (fun answer : α => (answer, table))) _ = _
  have hfun : Option.map Prod.fst ∘
      Option.map (fun answer : α => (answer, table)) = id := by
    funext z
    cases z <;> rfl
  rw [hfun, PMF.map_id]

/-- The eager and initially-empty lazy encodings of the Hyb₁ challenge table
remain equal after any common probabilistic continuation.  In particular,
ambient-oracle calls inside `oa` and arbitrary post-processing in `post` need
no query budget. -/
theorem evalDist_hyb1Lazy_then_eq_hyb1Eager
    {α β : Type} (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α)
    (post : α → ProbComp β) :
    𝒟[do
      let answer ← (simulateQ (hyb1LazyOuterImpl (oSpec := oSpec)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) oa).run' ∅
      post answer] =
    𝒟[do
      let table ← $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
      let answer ← (simulateQ (hybChallengeImpl (oSpec := oSpec) (U := U)
        (challengeSpec := gSpec (U := U) StmtIn pSpec δ) oSpecImpl
        (D_SigmaFinite (U := U) StmtIn pSpec δ)) oa).run' table
      post answer] := by
  rw [evalDist_bind, evalDist_simulateQ_hyb1LazyOuterImpl_run'_eq_eager]
  simp_rw [evalDist_bind]
  rw [bind_assoc]
  apply bind_congr
  intro table
  rw [evalDist_simulateQ_hybChallengeImpl_run'_eq_lazyOverlay]

/-- The explicit finite `D_Σ` initialization is distributionally equal to the
canonical uniform encoded-table sampler.  The two programs use extensionally
identical finite samplers through separately constructed typeclass instances.
This Core-only endpoint adapter is used by the revised Claim-5.22 image-fibre
coupling. -/
theorem evalDist_hybChallengeInit_DSigmaFinite_eq_uniformTable :
    𝒟[hybChallengeInit (D_SigmaFinite (U := U) StmtIn pSpec δ)] =
      𝒟[$ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))] := by
  letI : Fintype StmtIn := Fintype.ofFinite StmtIn
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype pSpec.ChallengeIdx := Fintype.ofFinite pSpec.ChallengeIdx
  letI (i : pSpec.ChallengeIdx) :
      Fintype (pSpec.EncodedMessagesBefore U i.1.castSucc) := Fintype.ofFinite _
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Fintype ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Fintype (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Finite ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
    Fintype.finite (by infer_instance)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Nonempty ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change Nonempty (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    Fintype.ofFinite _
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun q => Classical.arbitrary _⟩
  simp only [hybChallengeInit, D_SigmaFinite,
    OracleReduction.OracleDistribution.uniform,
    OracleReduction.OracleDistribution.functionTable]

/-- Lossless observed form of the lazy H₁ game.  This retains the actual raw D2S execution and
the structured first stop, which are the data required by the H₀--H₁ coupling. -/
noncomputable def hyb1RevisedLazyObserved
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := by
  classical
  exact
    hybridGameDistRevisedObserved
      (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := pure ∅)
      (impl := hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl)
      (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) V
      maliciousProver
      (TraceTransform.hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Lossless observed form of the eager H₁ game.  It is deliberately kept in the live security
layer so the coupling construction can use its exact eager/lazy equality without importing the
statement layer. -/
noncomputable def hyb1RevisedObserved
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := by
  let challengeSpec := gSpec (U := U) StmtIn pSpec δ
  let D_g := D_SigmaFinite (U := U) StmtIn pSpec δ
  exact
    hybridGameDistRevisedObserved
      (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := hybChallengeInit (challengeSpec := challengeSpec) D_g)
      (impl := hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_g)
      (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) V
      maliciousProver
      (TraceTransform.hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- The executable H₁ runner is invariant under the eager versus initially
empty lazy realization of its encoded challenge table.  This is an exact
distributional equality, including arbitrary ambient-oracle calls; it has no
prover or ambient query-count premise. -/
theorem evalDist_hyb1RevisedLazy_eq_hyb1Revised
    {StmtOut Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [DecidableEq ι]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb1RevisedLazy (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) oSpecImpl V maliciousProver] =
    𝒟[hyb1Revised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) oSpecImpl V maliciousProver] := by
  simp only [hyb1RevisedLazy, hyb1Revised, hybridGameDistRevised, pure_bind]
  refine (evalDist_hyb1Lazy_then_eq_hyb1Eager (oSpecImpl := oSpecImpl) _ _).trans ?_
  rw [evalDist_bind, evalDist_bind]
  rw [← evalDist_hybChallengeInit_DSigmaFinite_eq_uniformTable]
  rfl

/-- The same eager/lazy equivalence holds before line-4 projection.  In particular, the H₀--H₁
coupling may use the lazy H₁ execution to expose table entries on demand, then recover the
actual eager observed H₁ marginal without losing raw traces or terminal-stop information. -/
theorem evalDist_hyb1RevisedLazyObserved_eq_hyb1RevisedObserved
    {StmtOut Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [DecidableEq ι]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb1RevisedLazyObserved (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) oSpecImpl V maliciousProver] =
    𝒟[hyb1RevisedObserved (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) oSpecImpl V maliciousProver] := by
  simp only [hyb1RevisedLazyObserved, hyb1RevisedObserved,
    hybridGameDistRevisedObserved, pure_bind]
  refine (evalDist_hyb1Lazy_then_eq_hyb1Eager (oSpecImpl := oSpecImpl) _ _).trans ?_
  rw [evalDist_bind, evalDist_bind]
  rw [← evalDist_hybChallengeInit_DSigmaFinite_eq_uniformTable]
  rfl

/-- Erasing the lossless H₁ observation gives the public revised H₁ experiment exactly.  This
is the endpoint adapter for a coupling proved on raw query logs and structured stops. -/
theorem hyb1RevisedObserved_map_publicOutput_eq_hyb1Revised
    {StmtOut Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [DecidableEq ι]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    (fun observation => observation.publicOutput) <$>
        hyb1RevisedObserved (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
          (U := U) oSpecImpl V maliciousProver =
      hyb1Revised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) oSpecImpl V maliciousProver := by
  exact hybridGameDistRevisedObserved_map_publicOutput_eq
    (init := hybChallengeInit
      (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
      (D_SigmaFinite (U := U) StmtIn pSpec δ))
    (impl := hybChallengeImpl
      (oSpec := oSpec) (U := U) (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
      oSpecImpl (D_SigmaFinite (U := U) StmtIn pSpec δ))
    (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    V maliciousProver
    (TraceTransform.hyb1Line4Trace
      (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

omit [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  codec [DecidableEq StmtIn] [DecidableEq U] in
/-- The three public Lemma-5.1 class budgets combine into a budget for precisely the D2S
right-summand requests.  The ambient left summand is not counted: in particular, this theorem
neither assumes nor derives any bound on ambient oracle calls. -/
theorem isLemma5_1QueryBound_isD2SRightBound
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ) :
    OracleComp.IsQueryBoundP maliciousProver (fun point => point.isRight = true)
      (tₕ + tₚ + tₚᵢ) := by
  classical
  have hHashOrForward := IsQueryBoundP.or_add hBound.1 hBound.2.1 (by
    rintro (_ | (_ | (_ | _))) ⟨hLeft, hRight⟩ <;>
      simp_all [isLemma5_1HashQuery, isLemma5_1PermQuery])
  have hAllClasses := IsQueryBoundP.or_add hHashOrForward hBound.2.2 (by
    rintro (_ | (_ | (_ | _))) ⟨hLeft, hRight⟩ <;>
      simp_all [isLemma5_1HashQuery, isLemma5_1PermQuery, isLemma5_1PermInvQuery])
  rw [isQueryBoundP_congr_pred (p' := fun point => Sum.isRight point = true)] at hAllClasses
  · exact hAllClasses
  · rintro (_ | (_ | (_ | _))) <;>
      simp [isLemma5_1HashQuery, isLemma5_1PermQuery, isLemma5_1PermInvQuery]

/-- The structural residual runner used for the ambient-safe first-bad argument.  An outer
request is executed literally through `oSpecImpl` and leaves the D2S normal state unchanged;
only a right-summand duplex request executes one revised step.  Consequently, the later
first-bad budget counts exactly right-summand requests and no ambient requests. -/
noncomputable def hyb1AmbientDirectResidualRun
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut)) :
    D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) →
      ProbComp
        (Except
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          ((Option StmtOut ×
            D2SNormalState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) :=
  OracleComp.recOn residual
    (fun value normal => pure (.ok ((value, normal), PUnit.unit)))
    (fun request _continuation ih normal =>
      match request with
      | .inl query => do
          let answer ← oSpecImpl query
          ih answer normal
      | .inr query => do
          let result ← simulateQ
            ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
              (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
            (d2sQueryStepRevised normal query)
          match result with
          | .continue answer normal' => ih answer normal'
          | .stopped normal' record => pure (.error (.monitorStop normal' record))
          | .underlyingAbort => pure (.error (.underlyingAbort normal)))

/-- The event charged by the ambient-safe first-bad execution.  An ambient query is never an
event by itself: the only charged outcome is the structured `Monitor` stop produced by a D2S
request.  Search failures and ambient-oracle failures remain distinct uncharged outcomes. -/
def hyb1AmbientStoppingResultIsMonitorStop
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    (result : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) α) : Prop :=
  match result with
  | .ok _ => False
  | .error reason => reason.isMonitorStop

@[simp] lemma hyb1AmbientStoppingResultIsMonitorStop_ok
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type} (value : α) :
    hyb1AmbientStoppingResultIsMonitorStop
      (T_H := T_H) (T_P := T_P)
      (.ok value : Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) α) = False := rfl

@[simp] lemma hyb1AmbientStoppingResultIsMonitorStop_error
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    (reason : D2SRevisedStoppingReason
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1AmbientStoppingResultIsMonitorStop
      (T_H := T_H) (T_P := T_P) (.error reason : Except _ α) = reason.isMonitorStop := rfl

/-- Unfolding an ambient head request of the residual runner.  This is deliberately an equality
of complete distributions, not merely of bad-event probabilities: the ambient answer determines
the dependent residual continuation, while the D2S normal state is preserved verbatim. -/
@[simp] lemma hyb1AmbientDirectResidualRun_ambient
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (query : oSpec.Domain)
    (continuation : oSpec.Range query → OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl kSigma
      (liftM (OracleSpec.query (spec := oSpec + duplexSpongeChallengeOracle StmtIn U)
        (Sum.inl query)) >>= continuation) normal =
      (do
        let answer ← oSpecImpl query
        hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
          oSpecImpl kSigma (continuation answer) normal) := rfl

/-- Unfolding a charged D2S head request of the residual runner.  Exactly this branch invokes
the revised `D2SQuery` step, so it is the only branch to which the first-bad capacity charge is
applied. -/
@[simp] lemma hyb1AmbientDirectResidualRun_d2s
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (query : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (continuation : (duplexSpongeChallengeOracle StmtIn U).Range query → OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl kSigma
      (liftM (OracleSpec.query (spec := oSpec + duplexSpongeChallengeOracle StmtIn U)
        (Sum.inr query)) >>= continuation) normal =
      (do
        let result ← simulateQ
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
            (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
          (d2sQueryStepRevised normal query)
        match result with
        | .continue answer normal' =>
            hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
              oSpecImpl kSigma (continuation answer) normal'
        | .stopped normal' record => pure (.error (.monitorStop normal' record))
        | .underlyingAbort => pure (.error (.underlyingAbort normal))) := rfl

/-- Ambient-safe first-bad aggregation for a complete residual program.  The hypothesis counts
only right-summand D2S requests.  The induction consequently treats a left-summand ambient call
as a zero-cost bind and charges a capacity term only at an actual revised D2S step.  This is the
missing generalization of the old `[]ₒ`-only runner: it neither bounds nor otherwise restricts
the number of ambient calls. -/
lemma hyb1AmbientDirectResidualRun_monitorStop_le
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (fuel j : ℕ)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (hBound : OracleComp.IsQueryBoundP residual (fun point => point.isRight = true) fuel) :
    Pr[ fun result => hyb1AmbientStoppingResultIsMonitorStop
      (T_H := T_H) (T_P := T_P) result |
      hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma residual normal] ≤
      ((fuel * (2 * j + fuel) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  classical
  induction residual using OracleComp.inductionOn generalizing normal fuel j with
  | pure value =>
      change Pr[ fun result => hyb1AmbientStoppingResultIsMonitorStop
        (T_H := T_H) (T_P := T_P) result |
        pure (.ok ((value, normal), PUnit.unit))] ≤ _
      simp [hyb1AmbientStoppingResultIsMonitorStop]
  | query_bind request continuation ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hBound
      cases request with
      | inl query =>
          rw [hyb1AmbientDirectResidualRun_ambient]
          apply probEvent_bind_le_of_forall_le
          intro answer _
          simpa using ih answer normal fuel j hCoherent hBaseLength (hBound.2 answer)
      | inr query =>
          have hFuelPos : 0 < fuel := hBound.1.resolve_left (by simp)
          obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hFuelPos)
          rw [hyb1AmbientDirectResidualRun_d2s]
          let next := fun result : D2SRevisedStepResult
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
              ((duplexSpongeChallengeOracle StmtIn U).Range query) =>
            match result with
            | .continue answer normal' =>
                hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (continuation answer) normal'
            | .stopped normal' record => pure (.error (.monitorStop normal' record))
            | .underlyingAbort => pure (.error (.underlyingAbort normal))
          have hStep := d2sQueryStepRevised_monitorStop_le_of_baseLength_le
            ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma)
            normal query hCoherent j hBaseLength
          have hTail := probEvent_bind_le_add
            (mx := simulateQ
              ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
              (d2sQueryStepRevised normal query))
            (my := next)
            (p := fun result => ¬ result.isMonitorStop)
            (q := fun result => ¬ hyb1AmbientStoppingResultIsMonitorStop
              (T_H := T_H) (T_P := T_P) result)
            (ε₁ := ((2 * j + 1 : ℕ) : ℝ≥0∞) /
              BadEventDS.capacitySpaceSize (U := U))
            (ε₂ := ((fuel * (2 * (j + 1) + fuel) : ℕ) : ℝ≥0∞) /
              BadEventDS.capacitySpaceSize (U := U))
            (by simpa only [not_not] using hStep) (by
              intro result hResult hNotStop
              cases result with
              | «continue» answer normal' =>
                  have hInvariant := d2sQueryStepRevised_maintainsInvariant normal hCoherent
                    query ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma)
                    (.continue answer normal') hResult
                  have hLength := d2sQueryStepRevised_continue_baseTrace_length_le normal
                    query ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma)
                    answer normal' hResult
                  have hContinuationBound := hBound.2 answer
                  have hRecursive := ih answer normal' fuel (j + 1) hInvariant.1
                    (Nat.le_trans hLength (Nat.succ_le_succ hBaseLength))
                    (by simpa using hContinuationBound)
                  simpa only [next, not_not] using hRecursive
              | stopped _ _ =>
                  simp only [D2SRevisedStepResult.isMonitorStop_stopped,
                    not_true_eq_false] at hNotStop
              | underlyingAbort =>
                  simp [next, hyb1AmbientStoppingResultIsMonitorStop,
                    D2SRevisedStoppingReason.isMonitorStop])
          rw [← ENNReal.add_div] at hTail
          simp only [not_not] at hTail
          have hCharge :
              2 * j + 1 + fuel * (2 * (j + 1) + fuel) =
                (fuel + 1) * (2 * j + (fuel + 1)) := by
            ring
          have hChargeENN :
              ((2 * j + 1 : ℕ) : ℝ≥0∞) +
                  ((fuel * (2 * (j + 1) + fuel) : ℕ) : ℝ≥0∞) =
                (((fuel + 1) * (2 * j + (fuel + 1)) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hCharge
          rw [hChargeENN] at hTail
          simpa [next] using hTail

/-- The lossless D2F interpretation corresponding to
`hyb1AmbientDirectResidualRun`.  This is an executable semantic object, not a caller-supplied
coupling assumption. -/
noncomputable def hyb1AmbientD2FStoppingDirectImpl
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT PUnit
          (ExceptT
            (D2SRevisedStoppingReason
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp)))
  | .inl query => StateT.lift (StateT.lift (ExceptT.lift (oSpecImpl query)))
  | .inr request => fun normal => do
      let result ← simulateQ
        (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma)
        (d2sQueryStepRevised normal request)
      StateT.mk fun memo => ExceptT.mk (pure (d2sRevisedStepPost normal result memo))

/-- An ambient request is transparent to the direct lossless D2F interpreter: it returns the
ambient answer, preserves both state components, and does not itself create a stopping reason.
This is the semantic reason that ambient requests need no first-bad budget. -/
lemma hyb1AmbientD2FStoppingDirectImpl_ambient_run
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (request : oSpec.Domain) :
    (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl kSigma (.inl request)).run normal).run PUnit.unit).run =
      (fun answer =>
        (Except.ok ((answer, normal), PUnit.unit) : Except
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          ((oSpec.Range request ×
            D2SNormalState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit))) <$> oSpecImpl request := by
  unfold hyb1AmbientD2FStoppingDirectImpl
  simp [ExceptT.lift]

/-- A D2S request in the ambient interpreter has exactly the same one-step result distribution
as the fixed-table H₁ dispatcher.  The outer ambient oracle does not occur in this calculation. -/
lemma hyb1AmbientD2FStoppingDirectImpl_d2s_run
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
  (request : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    @ExceptT.run
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp
        (((oSpec + duplexSpongeChallengeOracle StmtIn U).toPFunctor.B (.inr request) ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)
        (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl kSigma (.inr request)).run normal).run PUnit.unit) =
      hyb1D2SStepToStopping normal <$>
        simulateQ
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
            (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
          (d2sQueryStepRevised normal request) := by
  rw [hyb1AmbientD2FStoppingDirectImpl]
  change ExceptT.run ((do
    let result ← simulateQ
      (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma)
      (d2sQueryStepRevised normal request)
    StateT.mk fun memo => ExceptT.mk
      (pure (d2sRevisedStepPost normal result memo))).run PUnit.unit) = _
  simp only [StateT.run_bind, ExceptT.run_bind]
  conv_lhs =>
    enter [1]
    rw [hyb1StoppingD2SDirect_step_run (T_H := T_H) (T_P := T_P)
      kSigma normal request]
  rw [bind_map_left, map_eq_pure_bind]
  apply bind_congr
  intro result
  cases result <;> rfl

/- The following fixed-full-cache bridge belongs to the legacy total-fibre development.  It is
kept available for compatibility, but the revised Claim 5.22 uses the Core-only image-fibre
kernel instead. -/
/-
Legacy total-fibre bridge.  It is intentionally inactive here: revised Lemma 5.1 is
`CodecCore`-only.  If an unmigrated development still needs this bridge, move it to a
separate legacy module rather than reactivating it in this import path.

variable [codecTotal : CodecTotal pSpec U]

local instance legacyCodec : Codec pSpec U := Codec.ofCoreTotal

/-- **Fixed-table H₁--H₂ D2F-step coupling.**  Preloading the fibre interpreter with H₁'s
complete encoded table makes a full revised D2S request agree exactly with the H₁ direct
interpreter.  The result includes the successor normal state and either structured stopping
reason; H₂'s cache is retained only as the invariant complete table. -/
theorem hyb2FibreAmbientD2FStoppingDirectImpl_fullCache_restore_eq_hyb1
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (request : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    (((hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table (.inr request)).run normal).run
        (fullEncodedChallengeCache table)).run =
      restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
    (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl table (.inr request)).run normal).run PUnit.unit).run := by
  have hHyb1 :
      (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
        oSpecImpl table (.inr request)).run normal).run PUnit.unit).run =
        hyb1D2SStepToStopping normal <$>
          simulateQ
            ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl table +
              (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
            (d2sQueryStepRevised normal request) :=
    hyb1AmbientD2FStoppingDirectImpl_d2s_run (T_H := T_H) (T_P := T_P)
      oSpecImpl table normal request
  rw [hHyb1]
  let postH2 :
      Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          ((duplexSpongeChallengeOracle StmtIn U).Range request) ×
          (gSpec (U := U) StmtIn pSpec δ).QueryCache) →
      Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((((duplexSpongeChallengeOracle StmtIn U).Range request) ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
          (gSpec (U := U) StmtIn pSpec δ).QueryCache) := fun outcome =>
    match outcome with
    | .error reason => .error reason
    | .ok resultAndCache => hyb2D2SStepToStopping normal resultAndCache
  let postH1 :
      Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          ((duplexSpongeChallengeOracle StmtIn U).Range request) × PUnit) →
      Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((((duplexSpongeChallengeOracle StmtIn U).Range request) ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit) := fun outcome =>
    match outcome with
    | .error reason => .error reason
    | .ok resultAndUnit => hyb1D2SStepToStopping normal resultAndUnit.1
  have hPost : ∀ outcome,
      postH2 (restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table outcome) =
        restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table (postH1 outcome) := by
    intro outcome
    cases outcome with
    | error reason => rfl
    | ok value =>
        rcases value with ⟨result, _⟩
        cases result <;> rfl
  calc
    (((hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table (.inr request)).run normal).run
        (fullEncodedChallengeCache table)).run =
        postH2 <$>
          ExceptT.run ((simulateQ
            (hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
            (d2sQueryStepRevised normal request)).run (fullEncodedChallengeCache table)) := by
          rw [hyb2FibreAmbientD2FStoppingDirectImpl]
          change ExceptT.run ((do
            let result ← simulateQ
              (hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
              (d2sQueryStepRevised normal request)
            StateT.mk fun cache => ExceptT.mk
              (pure (d2sRevisedStepPost normal result cache))).run
                (fullEncodedChallengeCache table)) = _
          simp only [StateT.run_bind, ExceptT.run_bind]
          rw [map_eq_pure_bind]
          apply bind_congr
          intro outcome
          cases outcome with
          | error reason => rfl
          | ok resultAndCache =>
              rcases resultAndCache with ⟨result, cache⟩
              cases result <;> rfl
    _ = postH2 <$>
          (restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
            ExceptT.run ((simulateQ
              (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
              (d2sQueryStepRevised normal request)).run PUnit.unit)) := by
          rw [simulateQ_hyb2FibreStoppingD2SDirect_fullCache_restore_eq_hyb1]
    _ = restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
          (postH1 <$>
          ExceptT.run ((simulateQ
              (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
              (d2sQueryStepRevised normal request)).run PUnit.unit)) := by
          rw [Functor.map_map, Functor.map_map]
          apply congrArg (fun f => f <$>
            ExceptT.run ((simulateQ
              (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
              (d2sQueryStepRevised normal request)).run PUnit.unit))
          funext outcome
          exact hPost outcome
    _ = restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
          (hyb1D2SStepToStopping normal <$>
            simulateQ
              ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl table +
                (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
              (d2sQueryStepRevised normal request)) := by
          rw [hyb1StoppingD2SDirect_step_run (T_H := T_H) (T_P := T_P)
            table normal request]
          simp only [Functor.map_map]
          rfl

/-- The fixed-table H₁--H₂ step relation is uniform over the ambient/D2S sum interface.
Ambient requests are literally shared; D2S requests use the preceding stateful replay coupling. -/
theorem hyb2FibreAmbientD2FStoppingDirectImpl_fullCache_restore_eq_hyb1_query
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (query : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain) :
    (((hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table query).run normal).run (fullEncodedChallengeCache table)).run =
      restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
        (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl table query).run normal).run PUnit.unit).run := by
  rcases query with query | query
  · rw [hyb2FibreAmbientD2FStoppingDirectImpl_ambient_run,
      hyb1AmbientD2FStoppingDirectImpl_ambient_run]
    simp only [map_eq_bind_pure_comp, bind_assoc]
    calc
      (oSpecImpl query >>= fun answer =>
          (pure (Except.ok ((answer, normal), fullEncodedChallengeCache table)) : ProbComp _)) =
        (oSpecImpl query >>= fun answer =>
          (pure (restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table
            (Except.ok ((answer, normal), PUnit.unit))) : ProbComp _)) := by
            apply bind_congr
            intro answer
            rfl
      _ = (oSpecImpl query >>= fun answer =>
          (pure (Except.ok ((answer, normal), PUnit.unit)) : ProbComp _)) >>= fun outcome =>
          (pure (restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table outcome) : ProbComp _) := by
            simp only [bind_assoc, pure_bind]
            rfl
  · exact hyb2FibreAmbientD2FStoppingDirectImpl_fullCache_restore_eq_hyb1
      (T_H := T_H) (T_P := T_P) oSpecImpl table normal query

/-- **Whole-residual fixed-table H₁--H₂ coupling.**  An arbitrary adaptive prover--verifier
residual cannot distinguish the eager fixed-table H₁ executor from the H₂ fibre executor
started with that same complete encoded table.  The equality carries the complete normal state,
the returned verifier value, and either stopping reason; it forgets only H₂'s invariant cache. -/
theorem simulateQ_hyb2FibreAmbientD2FStoppingDirectImpl_fullCache_restore_eq_hyb1
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (((simulateQ
      (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
        oSpecImpl table) residual).run normal).run (fullEncodedChallengeCache table)).run =
      restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
        (((simulateQ
          (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
            oSpecImpl table) residual).run normal).run PUnit.unit).run := by
  induction residual using OracleComp.inductionOn generalizing normal with
  | pure value => rfl
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
      rw [simulateQ_spec_query, simulateQ_spec_query]
      rw [hyb2FibreAmbientD2FStoppingDirectImpl_fullCache_restore_eq_hyb1_query]
      rw [bind_map_left, map_eq_pure_bind, bind_assoc]
      apply bind_congr
      intro step
      cases step with
      | error reason => rfl
      | ok output =>
          rcases output with ⟨⟨answer, normal'⟩, _⟩
          simpa [restoreHyb2FibreFullCache] using ih answer normal'

/-- **Whole Figure-4 residual, fixed-table H₁--H₂ endpoint.**  If the H₂ fibre cache is
preloaded with the encoded representatives of one fixed H₁ table, then the complete
prover-then-verifier residual agrees exactly with H₁ after the H₂ cache is forgotten.  This is
the output-level form of the fixed-table coupling: it preserves the returned verifier value,
the final normal state, and both structured stopping reasons. -/
theorem hyb2FibreFullResidual_fullCache_eq_hyb1
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    forgetHyb2FibreCache (T_H := T_H) (T_P := T_P) <$>
        (((simulateQ
          (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
            oSpecImpl table)
          (hyb2FullResidual (U := U) (δ := δ) V maliciousProver)).run
            (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run
            (fullEncodedChallengeCache table)).run =
      (((simulateQ
        (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl table)
        (hyb2FullResidual (U := U) (δ := δ) V maliciousProver)).run
          (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run PUnit.unit).run := by
  rw [simulateQ_hyb2FibreAmbientD2FStoppingDirectImpl_fullCache_restore_eq_hyb1]
  simp only [Functor.map_map]
  have hforget :
      (fun outcome : Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((Option StmtOut ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit) =>
        forgetHyb2FibreCache (T_H := T_H) (T_P := T_P)
        (restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table outcome)) = id := by
    funext outcome
    cases outcome <;> rfl
  rw [hforget]
  simp

-/

/-- The ambient residual replay is definitionally the live fixed-table stopping executor.
Unlike the older empty-ambient version, its induction has an explicit left-summand case: that
case executes the same `oSpecImpl` computation and leaves the D2S state unchanged.  Hence the
equality is exact without, and deliberately without requiring, a bound on ambient queries. -/
lemma hyb1AmbientDirectResidualRun_eq_liveDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
      oSpecImpl kSigma residual normal =
      (((simulateQ
        (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) oSpecImpl kSigma)
        residual).run normal).run PUnit.unit).run := by
  induction residual using OracleComp.recOn generalizing normal with
  | pure value =>
      rfl
  | queryBind request continuation ih =>
      cases request with
      | inl request =>
          rw [hyb1AmbientDirectResidualRun]
          simp only [OracleComp.recOn, simulateQ, PFunctor.FreeM.mapM,
            StateT.run_bind, ExceptT.run_bind]
          have hStep' :
              @ExceptT.run
                (D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp
                (((oSpec + duplexSpongeChallengeOracle StmtIn U).toPFunctor.B (.inl request) ×
                  D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)
                (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (.inl request)).run normal).run PUnit.unit) =
                (fun answer =>
                  (Except.ok ((answer, normal), PUnit.unit) : Except
                    (D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
                      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
                    ((oSpec.Range request × D2SNormalState
                      (δ := δ) (T_H := T_H) (T_P := T_P)
                      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit))) <$>
                    oSpecImpl request :=
            hyb1AmbientD2FStoppingDirectImpl_ambient_run (T_H := T_H) (T_P := T_P)
              oSpecImpl kSigma normal request
          have hRhs :
              (do
                let x ← (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (.inl request)).run normal).run PUnit.unit).run
                match x with
                | .ok x =>
                    (((PFunctor.FreeM.mapM
                      (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                        oSpecImpl kSigma)
                      (continuation x.1.1)).run x.1.2).run x.2).run
                | .error e => pure (.error e)) =
              (do
                let answer ← oSpecImpl request
                hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (continuation answer) normal) := by
            calc
              (do
                let x ← (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (.inl request)).run normal).run PUnit.unit).run
                match x with
                | .ok x =>
                    (((PFunctor.FreeM.mapM
                      (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                        oSpecImpl kSigma)
                      (continuation x.1.1)).run x.1.2).run x.2).run
                | .error e => pure (.error e)) =
                (do
                  let x ← (fun answer =>
                    (Except.ok ((answer, normal), PUnit.unit) : Except
                      (D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
                        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
                      ((oSpec.Range request × D2SNormalState
                        (δ := δ) (T_H := T_H) (T_P := T_P)
                        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit))) <$>
                      oSpecImpl request
                  match x with
                  | .ok x =>
                      (((PFunctor.FreeM.mapM
                        (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                          oSpecImpl kSigma)
                        (continuation x.1.1)).run x.1.2).run x.2).run
                  | .error e => pure (.error e)) := by
                    simpa only [OracleSpec.add_apply_inr] using congrArg (fun z => z >>= fun x =>
                      match x with
                      | .ok x =>
                          (((PFunctor.FreeM.mapM
                            (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                              oSpecImpl kSigma)
                            (continuation x.1.1)).run x.1.2).run x.2).run
                      | .error e => pure (.error e)) hStep'
              _ = _ := by
                simp only [map_eq_pure_bind, bind_assoc]
                apply bind_congr
                intro answer
                simpa [simulateQ] using (ih answer normal).symm
          convert hRhs.symm using 2
          funext x
          cases x <;> rfl
      | inr request =>
          rw [hyb1AmbientDirectResidualRun]
          simp only [OracleComp.recOn, simulateQ, PFunctor.FreeM.mapM,
            StateT.run_bind, ExceptT.run_bind]
          have hStep' :
              @ExceptT.run
                (D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp
                (((oSpec + duplexSpongeChallengeOracle StmtIn U).toPFunctor.B (.inr request) ×
                  D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)
                (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (.inr request)).run normal).run PUnit.unit) =
                hyb1D2SStepToStopping normal <$>
                  simulateQ
                    ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                      (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
                    (d2sQueryStepRevised normal request) :=
            hyb1AmbientD2FStoppingDirectImpl_d2s_run (T_H := T_H) (T_P := T_P)
              oSpecImpl kSigma normal request
          let stepToAmbient :
              D2SRevisedStepResult
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                ((duplexSpongeChallengeOracle StmtIn U).Range request) →
                Except
                  (D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
                  (((oSpec + duplexSpongeChallengeOracle StmtIn U).Range (.inr request) ×
                    D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
                      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit) :=
            hyb1D2SStepToStopping normal
          have hStepAmbient :
              (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                oSpecImpl kSigma (.inr request)).run normal).run PUnit.unit).run =
                stepToAmbient <$>
                  simulateQ
                    ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                      (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
                    (d2sQueryStepRevised normal request) := by
            simpa only [stepToAmbient] using hStep'
          have hRhs :
              (do
                let x ← (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (.inr request)).run normal).run PUnit.unit).run
                match x with
                | .ok x =>
                    (((PFunctor.FreeM.mapM
                      (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                        oSpecImpl kSigma)
                      (continuation x.1.1)).run x.1.2).run x.2).run
                | .error e => pure (.error e)) =
              (do
                let result ← simulateQ
                  ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                    (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
                  (d2sQueryStepRevised normal request)
                match result with
                | .continue answer normal' =>
                    hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
                      oSpecImpl kSigma (continuation answer) normal'
                | .stopped normal' record => pure (.error (.monitorStop normal' record))
                | .underlyingAbort => pure (.error (.underlyingAbort normal))) := by
            calc
              (do
                let x ← (((hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                  oSpecImpl kSigma (.inr request)).run normal).run PUnit.unit).run
                match x with
                | .ok x =>
                    (((PFunctor.FreeM.mapM
                      (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                        oSpecImpl kSigma)
                      (continuation x.1.1)).run x.1.2).run x.2).run
                | .error e => pure (.error e)) =
                (do
                  let x ← stepToAmbient <$>
                    simulateQ
                      ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                        (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
                      (d2sQueryStepRevised normal request)
                  match x with
                  | .ok x =>
                      (((PFunctor.FreeM.mapM
                        (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                          oSpecImpl kSigma)
                        (continuation x.1.1)).run x.1.2).run x.2).run
                  | .error e => pure (.error e)) := by
                    exact congrArg (fun z => z >>= fun x =>
                      match x with
                      | .ok x =>
                          (((PFunctor.FreeM.mapM
                            (hyb1AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
                              oSpecImpl kSigma)
                            (continuation x.1.1)).run x.1.2).run x.2).run
                      | .error e => pure (.error e)) hStepAmbient
              _ = _ := by
                simp only [map_eq_pure_bind, bind_assoc]
                apply bind_congr
                intro result
                cases result with
                | «continue» answer normal' =>
                    simp only [stepToAmbient, hyb1D2SStepToStopping]
                    simpa [simulateQ] using (ih answer normal').symm
                | stopped normal' record => rfl
                | underlyingAbort => rfl
          convert hRhs.symm using 2
          funext x
          cases x <;> rfl

/-- The continuous prover--verifier residual used by the ambient-safe Hyb₁ analysis.

The residual retains the ambient oracle literally.  Its query budget is consequently stated only
for the right D2S summand; a later structural verifier-count lemma discharges the corresponding
right-summand premise at `N_𝒱 + 1`. -/
noncomputable def hyb1AmbientFullResidual
    {StmtOut : Type}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
  maliciousProver >>= fun output =>
    runForwardVerifierWide δ V output.1 output.2

/-- The public prover budget and a right-summand verifier budget compose without charging any
ambient query.  This is the exact residual budget consumed by the ambient-safe first-bad runner.
The verifier premise is deliberately local: it will be discharged by the generic exact verifier
count, not added to the public Lemma 5.1 statement. -/
lemma hyb1AmbientFullResidual_isQueryBound_right
    {StmtOut : Type}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ verifierFuel : ℕ)
    (hProver : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ)
    (hVerifier : ∀ output : StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ,
      OracleComp.IsQueryBoundP (runForwardVerifierWide δ V output.1 output.2)
        (fun point => point.isRight = true) verifierFuel) :
    OracleComp.IsQueryBoundP (hyb1AmbientFullResidual V maliciousProver)
      (fun point => point.isRight = true) (tₕ + tₚ + tₚᵢ + verifierFuel) := by
  unfold hyb1AmbientFullResidual
  refine (OracleComp.isQueryBoundP_bind
    (n := tₕ + tₚ + tₚᵢ) (m := verifierFuel)
    (isLemma5_1QueryBound_isD2SRightBound maliciousProver tₕ tₚ tₚᵢ hProver)
    (fun output _ => hVerifier output)).mono (by omega)

/-- The first-bad charge for the full ambient Hyb₁ residual.  Once the generic verifier-count
bridge supplies `verifierFuel = N_𝒱 + 1`, this is the paper's complete H₁ first-bad calculation:
ambient calls are present in the execution but contribute neither fuel nor a collision charge. -/
lemma hyb1AmbientFullResidual_monitorStop_le
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ verifierFuel j : ℕ)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (hProver : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ)
    (hVerifier : ∀ output : StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ,
      OracleComp.IsQueryBoundP (runForwardVerifierWide δ V output.1 output.2)
        (fun point => point.isRight = true) verifierFuel) :
    Pr[ fun result => hyb1AmbientStoppingResultIsMonitorStop
      (T_H := T_H) (T_P := T_P) result |
      hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma (hyb1AmbientFullResidual V maliciousProver) normal] ≤
      ((((tₕ + tₚ + tₚᵢ + verifierFuel) *
          (2 * j + (tₕ + tₚ + tₚᵢ + verifierFuel)) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U)) := by
  apply hyb1AmbientDirectResidualRun_monitorStop_le
  · exact hCoherent
  · exact hBaseLength
  · exact hyb1AmbientFullResidual_isQueryBound_right V maliciousProver
      tₕ tₚ tₚᵢ verifierFuel hProver hVerifier

/-- The ambient-safe Hyb₁ first-bad charge with the paper's exact verifier
count.  The verifier itself may issue arbitrary ambient-oracle queries, but
the exact structural count charges only its one `DS.Start` hash query and its
`N_𝒱` stateful forward-permutation calls. -/
lemma hyb1AmbientFullResidual_monitorStop_le_exact
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ j : ℕ)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (hProver : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ) :
    Pr[ fun result => hyb1AmbientStoppingResultIsMonitorStop
      (T_H := T_H) (T_P := T_P) result |
      hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma (hyb1AmbientFullResidual V maliciousProver) normal] ≤
      ((((tₕ + tₚ + tₚᵢ +
          (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) *
          (2 * j + (tₕ + tₚ + tₚᵢ +
            (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1))) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U)) := by
  apply hyb1AmbientFullResidual_monitorStop_le
    oSpecImpl kSigma V maliciousProver normal tₕ tₚ tₚᵢ
    (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) j
  · exact hCoherent
  · exact hBaseLength
  · exact hProver
  · intro output
    exact runForwardVerifierWide_right_bound_exact V output.1 output.2

/-- The exact ambient Hyb₁ first-bad charge in the paper's common `B` form.
The initial base trace has length at most `j`; the complete residual adds at
most the prover's three public budgets plus `N_𝒱 + 1` verifier-side DSFS
queries.  This is a faithful change of envelope, not a rounded-count bound. -/
lemma hyb1AmbientFullResidual_monitorStop_le_badEventBound
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ j : ℕ)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (hProver : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ) :
    Pr[ fun result => hyb1AmbientStoppingResultIsMonitorStop
      (T_H := T_H) (T_P := T_P) result |
      hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma (hyb1AmbientFullResidual V maliciousProver) normal] ≤
      ENNReal.ofReal (Statement.badEventBound U
        (j + (tₕ + tₚ + tₚᵢ +
          (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)))) := by
  exact (hyb1AmbientFullResidual_monitorStop_le_exact
    oSpecImpl kSigma V maliciousProver normal tₕ tₚ tₚᵢ j
      hCoherent hBaseLength hProver).trans
    (Statement.adaptiveD2SCharge_div_le_badEventBoundENN (U := U) j
      (tₕ + tₚ + tₚᵢ +
        (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)))

end DuplexSpongeFS.KeyLemma
