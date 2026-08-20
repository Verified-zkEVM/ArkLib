/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.AdaptiveFibreCoupling
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.RevisedHybridGame
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Fixed-table H₂ refinement

This module connects the fixed-table decoded-bridge kernel to the lossless
Eq. (16) executor used by the revised hybrid games.
-/

noncomputable section

set_option linter.style.longFile 1800

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

local instance : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _
local instance : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩

/-- Distributional state-projection for a state-threaded oracle simulation.  This is the
probabilistic counterpart of `OracleComp.map_run_simulateQ_eq_of_query_map_eq`: it permits the
refining handler to retain dependent witnesses in its state while the compared handler retains
only their observable projection. -/
theorem evalDist_map_run_simulateQ_eq_of_query_evalDist_map_eq
    {α ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      𝒟[Prod.map id proj <$> (impl₁ t).run s] = 𝒟[(impl₂ t).run (proj s)])
    (oa : OracleComp spec α) (s : σ₁) :
    𝒟[Prod.map id proj <$> (simulateQ impl₁ oa).run s] =
      𝒟[(simulateQ impl₂ oa).run (proj s)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
      simp
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [evalDist_bind, evalDist_bind]
      calc
        (do
          let x ← 𝒟[(impl₁ t).run s]
          𝒟[Prod.map id proj <$> (simulateQ impl₁ (next x.1)).run x.2]) =
          (do
            let x ← 𝒟[(impl₁ t).run s]
            𝒟[(simulateQ impl₂ (next x.1)).run (proj x.2)]) := by
              apply bind_congr
              intro x
              exact ih x.1 x.2
        _ = (do
          let x ← Prod.map id proj <$> 𝒟[(impl₁ t).run s]
          𝒟[(simulateQ impl₂ (next x.1)).run x.2]) := by
            symm
            exact bind_map_left (Prod.map id proj) (𝒟[(impl₁ t).run s])
              (fun x => 𝒟[(simulateQ impl₂ (next x.1)).run x.2])
        _ = (do
          let x ← 𝒟[(impl₂ t).run (proj s)]
          𝒟[(simulateQ impl₂ (next x.1)).run x.2]) := by
            rw [← evalDist_map]
            rw [hproj]

/-- A concrete finite enumeration of complete encoded challenge tables.  Keeping this
enumeration explicit prevents typeclass search from selecting the legacy table sampler, whose
sole purpose is compatibility with the unmigrated development. -/
@[reducible]
noncomputable def encodedChallengeTableFinEnum :
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
  letI : FinEnum ((gSpec (U := U) StmtIn pSpec δ).Domain) := inferInstance
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      FinEnum ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change FinEnum (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  infer_instance

/-- The canonical finite representation of complete encoded challenge tables.  It is passed
explicitly to the fibre witness sampler, avoiding any selection of the legacy table instance. -/
noncomputable def encodedChallengeTableFintype :
    Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := by
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  exact Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm

/-- The explicit axiom-clean uniform sampler for a complete encoded challenge table.  It avoids
the legacy low-priority table-sampling instance retained only for unmigrated code. -/
noncomputable def uniformEncodedChallengeTable :
    ProbComp (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := by
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
    by
      rcases q with ⟨i, key⟩
      change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
      infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : SampleableType (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    SampleableType.ofFintype _
  exact $ᵗ (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))

/-- Sample an encoded table, expose its complete decoded view, and then sample one uniformly
random encoded table in that view's fibre.  This is the whole-table form of the H₁--H₂
reparameterization; later results connect its lazy exposure to the live revised executor. -/
noncomputable def sampleEncodedTableFromDecodedFibre :
    ProbComp (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := by
  classical
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
    by
      rcases q with ⟨i, key⟩
      change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
      infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  exact do
    let table ← uniformEncodedChallengeTable
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    DuplexSpongeFS.Preliminaries.uniformPreimageComp
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)

/-- The table produced by `sampleEncodedTableFromDecodedFibre` is uniformly distributed.  The
proof is the executable `ProbComp` realization of the PMF identity used in Claim 5.22. -/
theorem evalDist_sampleEncodedTableFromDecodedFibre_eq_uniform :
    𝒟[sampleEncodedTableFromDecodedFibre
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] =
      𝒟[uniformEncodedChallengeTable
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)] := by
  letI : FinEnum (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    encodedChallengeTableFinEnum (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      Inhabited ((gSpec (U := U) StmtIn pSpec δ).Range q) :=
    by
      rcases q with ⟨i, key⟩
      change Inhabited (Vector U (challengeSize (pSpec := pSpec) i))
      infer_instance
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun _ => default⟩
  letI : SampleableType (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    SampleableType.ofFintype _
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  unfold sampleEncodedTableFromDecodedFibre uniformEncodedChallengeTable
  rw [evalDist_bind, evalDist_uniformSample]
  simp_rw [DuplexSpongeFS.Preliminaries.evalDist_uniformPreimageComp]
  rw [← liftM_bind]
  exact congrArg liftM
    (encodedTable_uniform_fiber_reparameterization (U := U) StmtIn pSpec δ)

/-- Forget the proof carried by each cached element of a decoded-table fibre.  This is the
state relation between the dependent lazy fibre oracle and H₂'s ordinary encoded-key cache. -/
def projectDecodedFibreCache
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache) :
    (gSpec (U := U) StmtIn pSpec δ).QueryCache :=
  fun q => (cache q).map Subtype.val

/-- Project a complete dependent fibre table to its encoded representatives.  When
`decoded = decodeEncodedChallengeTable table`, this is precisely a uniformly sampled encoded
table conditional on the decoded view of `table`. -/
def projectDecodedFibreTable
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (encoded : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :
    OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ) :=
  fun q => (encoded q).1

/-- The projected eager fibre table has precisely the decoded view from which its fibre was
formed.  This is the pointwise invariant that later identifies its H₁ line-4 answers with the
H₂ decoded-table answers. -/
@[simp]
theorem decode_projectDecodedFibreTable
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (encoded : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    codec.decode q.1
      (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded encoded q) = decoded q :=
  (encoded q).2

/-- The D2S action interpreter backed by the genuine dependent lazy fibre oracle.  Its cache
stores fibre witnesses, unlike the live H₂ cache; `projectDecodedFibreCache` is the exact
observable relation between the two representations. -/
noncomputable def decodedFibreLazyD2SImpl
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    [∀ q, SampleableType
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)] :
    QueryImpl
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache ProbComp)
  | .inl q => decodedFibreLazyImpl (pSpec := pSpec) (U := U) decoded q
  | .inr aux => StateT.lift <| (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux

@[simp] lemma projectDecodedFibreCache_empty
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    projectDecodedFibreCache (pSpec := pSpec) (U := U) decoded (∅ :
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache) = ∅ := by
  funext q
  rfl

/-- Every value retained by the dependent fibre cache decodes to the fixed decoded table.  This
is the invariant needed to compare the fibre cache with H₂'s raw encoded-key cache. -/
theorem projectDecodedFibreCache_decodes
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    {q : (gSpec (U := U) StmtIn pSpec δ).Domain}
    {response : (gSpec (U := U) StmtIn pSpec δ).Range q}
    (hresponse : projectDecodedFibreCache (pSpec := pSpec) (U := U) decoded cache q =
      some response) :
    codec.decode q.1 response = decoded q := by
  unfold projectDecodedFibreCache at hresponse
  cases hcache : cache q with
  | none => simp [hcache] at hresponse
  | some fibreResponse =>
      rw [hcache] at hresponse
      have hvalue : fibreResponse.1 = response := by
        simpa only [Option.map, Option.some.injEq] using hresponse
      rw [← hvalue]
      exact fibreResponse.2

@[simp] lemma projectDecodedFibreCache_cacheQuery
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (response : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :
    projectDecodedFibreCache (pSpec := pSpec) (U := U) decoded
      (cache.cacheQuery q response) =
      (projectDecodedFibreCache (pSpec := pSpec) (U := U) decoded cache).cacheQuery q
        response.1 := by
  funext q'
  unfold projectDecodedFibreCache
  by_cases h : q' = q
  · subst q'
    rw [QueryCache.cacheQuery_self cache q response]
    let projected : (gSpec (U := U) StmtIn pSpec δ).QueryCache :=
      fun q => Option.map Subtype.val (cache q)
    change Option.map Subtype.val (some response) = projected.cacheQuery q response.1 q
    have hprojected :
        projected.cacheQuery q response.1 q = some response.1 :=
      QueryCache.cacheQuery_self _ q response.1
    rw [hprojected]
    rfl
  · rw [QueryCache.cacheQuery_of_ne cache response h]
    exact (QueryCache.cacheQuery_of_ne
      (projectDecodedFibreCache (pSpec := pSpec) (U := U) decoded cache) response.1 h).symm

/-- The fixed-table H₂ outer handler with an arbitrary ambient oracle.  The ambient arm is
passed through literally; the D2S arm is the Eq. (52) decoded-table bridge.  This is the H₂
counterpart of `hyb1AmbientOuterImpl`, and prevents a later hybrid proof from accidentally
requiring a bound on ambient-oracle queries. -/
noncomputable def hyb2AmbientOuterImpl
    {ι : Type} {oSpec : OracleSpec ι}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)) ProbComp
  | .inl query => oSpecImpl query
  | .inr query =>
      decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table query

/-- The ambient branch of the fixed H₂ handler is definitionally unchanged. -/
@[simp]
theorem hyb2AmbientOuterImpl_ambient
    {ι : Type} {oSpec : OracleSpec ι}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (query : oSpec.Domain) :
    hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl table (Sum.inl query) = oSpecImpl query :=
  rfl

/-- The D2S branch of the fixed H₂ handler is exactly the decoded-table bridge. -/
@[simp]
theorem hyb2AmbientOuterImpl_d2s
    {ι : Type} {oSpec : OracleSpec ι}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (query : (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)).Domain) :
    hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl table (Sum.inr query) =
      decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table query :=
  rfl

/-- Extensional form of the fixed H₂ ambient handler, used when moving an `e`-only computation
through the left ambient summand. -/
theorem hyb2AmbientOuterImpl_eq_add
    {ι : Type} {oSpec : OracleSpec ι}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl table =
      oSpecImpl +
        decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table := by
  apply QueryImpl.ext
  rintro (query | query) <;> rfl

/-- Fixing an H₂ decoded table commutes with the memoized bridge even in the presence of an
arbitrary ambient oracle.  The lifted bridge itself has no ambient requests; this equality makes
that fact explicit at the exact `simulateQ` boundary used by the whole-game refinement. -/
theorem simulateQ_hyb2AmbientOuter_d2sDecodedBridgeImplCache_run_eq_cachedSampled
    {ι : Type} {oSpec : OracleSpec ι}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    simulateQ
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      (OracleComp.liftComp
        ((d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run cache).run
        (oSpec + D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))) =
      (OptionT.lift
        (((decodedBridgeSampledImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching q).run
          cache) :
        OptionT ProbComp
          ((gSpec (U := U) StmtIn pSpec δ).Range q ×
            (gSpec (U := U) StmtIn pSpec δ).QueryCache)).run := by
  have h := congrArg OptionT.run
    (simulateQ_decodedBridgeImplCache_run_eq_cachedSampled
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q cache)
  change simulateQ
      (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      ((d2sDecodedBridgeImplCache
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run cache).run =
      (OptionT.lift
        (((decodedBridgeSampledImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching q).run
          cache)).run at h
  let source :
      OracleComp
        (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
        (Option (((gSpec (U := U) StmtIn pSpec δ).Range q) ×
          (gSpec (U := U) StmtIn pSpec δ).QueryCache)) :=
    ((d2sDecodedBridgeImplCache
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run cache).run
  have hleft :
      simulateQ
        (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          oSpecImpl table)
        (OracleComp.liftComp source
          (oSpec + D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))) =
      simulateQ
        (decodedBridgeOuterImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        source := by
    rw [hyb2AmbientOuterImpl_eq_add]
    exact QueryImpl.simulateQ_add_liftComp_right
      oSpecImpl
      (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      source
  change
    (simulateQ _ (OracleComp.liftComp source _) :
      ProbComp
        (Option ((gSpec (U := U) StmtIn pSpec δ).Range q ×
          (gSpec (U := U) StmtIn pSpec δ).QueryCache))) = _
  exact hleft.trans h

/-- Convert the live bridge's optional cached answer into the stopping result used by the
fixed-table H₂ executor.  Under a fixed decoded table, the subsequent refinement shows that the
`none` arm is unreachable; keeping it explicit here preserves the live executor's exact abort
classification. -/
def hyb2OptionToStopping
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (α × (gSpec (U := U) StmtIn pSpec δ).QueryCache) →
      Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (α × (gSpec (U := U) StmtIn pSpec δ).QueryCache)
  | some output => .ok output
  | none => .error (.oracleAbort normal)

/-- The `gᵢ` arm of the live lossless D2F inner handler is precisely the bridge cache result,
lifted into the ambient oracle family and converted into the executor's explicit stopping type. -/
lemma hyb2D2fStoppingD2SInner_g_run_eq_optionToStopping
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (query : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    ExceptT.run
      ((d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
        (d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal
        (.inl query)).run cache) =
      hyb2OptionToStopping normal <$>
        OracleComp.liftComp
          ((d2sDecodedBridgeImplCache
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) query cache).run)
          (oSpec + D2SChallengePlusUnitOracle
            (U := U) (eSpec (U := U) StmtIn pSpec δ)) := by
  simp only [d2fStoppingD2SInner, StateT.run, ChallengeIdx, Challenge, add_apply_inl,
    ExceptT.run_bind, ExceptT.run_lift, bind_map_left, liftComp_eq_liftM]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro answer?
  cases answer? <;> rfl

/-- Pushing a fixed H₂ decoded table through a complete lossless revised D2F execution is exact
with an arbitrary ambient oracle.  It preserves the encoded-key cache, the complete normal
state, and the monitor/search stopping reason; in particular, the later adaptive fibre argument
may be applied to an actual H₂ prover or verifier residual rather than to a hand-isolated query.
-/
theorem hyb2AmbientD2fRawRevisedStopping_pushes_outer
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    simulateQ
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        residual normal cache) =
      (((simulateQ
        (QueryImpl.mapStateTStateTExceptTBase
          (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            oSpecImpl table)
          (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
            (d2sDecodedBridgeImplCache
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))))
        residual).run normal).run cache).run := by
  exact QueryImpl.simulateQ_mapStateTStateTExceptTBase_run
    (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl table)
    (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
      (d2sDecodedBridgeImplCache
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)))
    residual normal cache

/-- The fixed H₂ outer handler restricted to the ambient-free D2S-action layer. -/
noncomputable def hyb2D2SOuterImpl
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl
      (([]ₒ : OracleSpec PEmpty.{1}) +
        D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)) ProbComp
  | .inl query => PEmpty.elim query
  | .inr query =>
      decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table query

/-- The empty ambient branch of the fixed H₂ handler is the canonical sum handler. -/
theorem hyb2D2SOuterImpl_eq_add
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    hyb2D2SOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table =
      ((fun query : (([]ₒ : OracleSpec PEmpty.{1})).Domain => PEmpty.elim query) :
        QueryImpl ([]ₒ : OracleSpec PEmpty.{1}) ProbComp) +
        decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table := by
  apply QueryImpl.ext
  rintro (query | query)
  · exact PEmpty.elim query
  · rfl

/-- With the decoded H₂ table fixed, the live cache has no abort face: running it through the
fixed outer handler is exactly the lifted ordinary cached bridge. -/
theorem simulateQ_hyb2D2SOuter_d2sDecodedBridgeImplCache_run_eq_cachedSampled
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    simulateQ
      (hyb2D2SOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      (OracleComp.liftComp
        ((d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run cache).run
        (([]ₒ : OracleSpec PEmpty.{1}) + D2SChallengePlusUnitOracle (U := U)
          (eSpec (U := U) StmtIn pSpec δ))) =
      (OptionT.lift
        (((decodedBridgeSampledImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching q).run
          cache) :
        OptionT ProbComp
          ((gSpec (U := U) StmtIn pSpec δ).Range q ×
            (gSpec (U := U) StmtIn pSpec δ).QueryCache)).run := by
  have h := congrArg OptionT.run
    (simulateQ_decodedBridgeImplCache_run_eq_cachedSampled
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table q cache)
  change simulateQ
      (decodedBridgeOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      ((d2sDecodedBridgeImplCache
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run cache).run =
      (OptionT.lift
        (((decodedBridgeSampledImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching q).run
          cache)).run at h
  let source :
      OracleComp
        (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
        (Option (((gSpec (U := U) StmtIn pSpec δ).Range q) ×
          (gSpec (U := U) StmtIn pSpec δ).QueryCache)) :=
    ((d2sDecodedBridgeImplCache
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run cache).run
  have hleft :
      simulateQ
        (hyb2D2SOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        (OracleComp.liftComp source
          (([]ₒ : OracleSpec PEmpty.{1}) + D2SChallengePlusUnitOracle (U := U)
            (eSpec (U := U) StmtIn pSpec δ))) =
      simulateQ
        (decodedBridgeOuterImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        source := by
    rw [hyb2D2SOuterImpl_eq_add]
    rw [QueryImpl.simulateQ_add_liftComp_right]
  change
    (simulateQ _ (OracleComp.liftComp source _) :
      ProbComp
        (Option ((gSpec (U := U) StmtIn pSpec δ).Range q ×
          (gSpec (U := U) StmtIn pSpec δ).QueryCache))) = _
  exact hleft.trans h

/-- The direct fixed-table H₂ handler for one revised D2S request.  Its `gᵢ` branch samples an
encoded representative only on a cache miss; the remaining action branches are the unchanged
unit and rate-block samplers. -/
noncomputable def hyb2StoppingD2SDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache
        (ExceptT
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp)) := by
  classical
  exact fun
    | .inl gq => fun cache => ExceptT.lift
      (((decodedBridgeSampledImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching gq).run cache)
    | .inr aux => StateT.lift <| ExceptT.lift <|
      ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux)

/-- Mapping the live lossless D2F inner handler through a fixed H₂ decoded table yields the
direct stopping handler.  The optional live cache result is retained as an explicit
`oracleAbort` classification before the fixed-table simulation shows it equals the direct
cached sampler. -/
lemma hyb2D2fStoppingD2SInner_mapped_eq_direct
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl.mapStateTExceptTBase
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
        (d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal) =
      hyb2StoppingD2SDirect (T_H := T_H) (T_P := T_P) table := by
  apply QueryImpl.ext
  rintro (gq | aux | aux)
  · funext cache
    apply ExceptT.ext
    simp only [QueryImpl.mapStateTExceptTBase]
    change simulateQ
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      (ExceptT.run
        ((d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
          (d2sDecodedBridgeImplCache
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal
          (.inl gq)).run cache)) = _
    rw [hyb2D2fStoppingD2SInner_g_run_eq_optionToStopping]
    have hmap := simulateQ_map
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      (OracleComp.liftComp
        ((d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gq cache).run)
        (oSpec + D2SChallengePlusUnitOracle
          (U := U) (eSpec (U := U) StmtIn pSpec δ)))
      (hyb2OptionToStopping normal)
    refine hmap.trans ?_
    change hyb2OptionToStopping normal <$>
        simulateQ
          (hyb2AmbientOuterImpl
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
          (OracleComp.liftComp
            ((d2sDecodedBridgeImplCache
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gq).run cache).run
            (oSpec + D2SChallengePlusUnitOracle
              (U := U) (eSpec (U := U) StmtIn pSpec δ))) = _
    rw [simulateQ_hyb2AmbientOuter_d2sDecodedBridgeImplCache_run_eq_cachedSampled]
    simp [hyb2StoppingD2SDirect, hyb2OptionToStopping]
  · funext cache
    apply ExceptT.ext
    simp only [QueryImpl.mapStateTExceptTBase, d2fStoppingD2SInner,
      hyb2StoppingD2SDirect]
    calc
      (StateT.mk (fun state => ExceptT.mk
        ((fun answer => Except.ok (answer, state)) <$> d2sUnitSampleImpl aux)) cache).run =
          (fun answer => Except.ok (answer, cache)) <$> d2sUnitSampleImpl aux := rfl
      _ = (StateT.lift (ExceptT.lift (d2sUnitSampleImpl aux)) cache).run :=
        (QueryImpl.run_stateT_lift_exceptT_lift
          (ε := D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (d2sUnitSampleImpl (U := U) aux) cache).symm
  · funext cache
    apply ExceptT.ext
    simpa [QueryImpl.mapStateTExceptTBase, d2fStoppingD2SInner,
      hyb2StoppingD2SDirect, hyb2AmbientOuterImpl, decodedBridgeOuterImpl] using
      (QueryImpl.run_stateT_lift_exceptT_lift
        (ε := D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)) cache).symm

/-- The fixed-table fibre counterpart of `hyb2StoppingD2SDirect`.  It differs only on a
fresh encoded challenge request: instead of evaluating the decoded table and then sampling a
preimage, it samples directly from the same decoder fibre.  The cache, auxiliary actions, and
the stopping layer are literally shared. -/
noncomputable def hyb2FibreStoppingD2SDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache
        (ExceptT
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp)) := by
  classical
  exact fun
    | .inl gq => fun cache => ExceptT.lift
      (((decodedFibreSampler
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching gq).run cache)
    | .inr aux => StateT.lift <| ExceptT.lift <|
      ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux)

/-- Preload every encoded challenge key with the answer from a fixed H₁ table.

This cache is used only in the eager endpoint of the H₁--H₂ reparameterization: it makes the
H₂ fibre handler return the already chosen encoded representative, instead of sampling a new
one from that representative's decoder fibre. -/
def fullEncodedChallengeCache
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    (gSpec (U := U) StmtIn pSpec δ).QueryCache :=
  fun q => some (table q)

/-- The full-cache presentation of the live H₂ bridge.  It deliberately still performs the
decoded `eᵢ` query before returning the preloaded encoded representative: the cache removes only
fresh fibre sampling, never an observable oracle occurrence.  This is the local operational
form of the repeated-query convention used by the logged Claim 5.22 coupling. -/
noncomputable def hyb2FullCacheRequeryImpl
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache
        (AbortComp (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ)))) :=
  fun q => do
    let _ ← StateT.lift <| OptionT.lift <|
      (show OracleComp
          (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (pSpec.Challenge q.1) from
        query
          (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (.inl q))
    pure (table q)

/-- On a preloaded complete table, the live H₂ bridge is exactly the explicit requery handler.
The equality retains the outer decoded-oracle request, so it can later be lifted through the
logged prover and verifier executions without losing repeated-key trace multiplicity. -/
theorem d2sDecodedBridgeImplCache_run_fullCache_eq_requery
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    (d2sDecodedBridgeImplCache (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q).run
        (fullEncodedChallengeCache table) =
      (hyb2FullCacheRequeryImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        table q).run (fullEncodedChallengeCache table) := by
  simpa [hyb2FullCacheRequeryImpl] using
    d2sDecodedBridgeImplCache_run_of_hit
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q
      (fullEncodedChallengeCache table) (table q) rfl

/-- The full-cache requery equality is stable under every finite encoded-challenge computation.
Both sides retain the same cache at every continuation; the only effect is that each invocation
emits its corresponding decoded `eᵢ` request before returning the common table answer. -/
theorem simulateQ_d2sDecodedBridgeImplCache_fullCache_eq_requery
    {α : Type}
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (actions : OracleComp (gSpec (U := U) StmtIn pSpec δ) α) :
    (simulateQ
      (d2sDecodedBridgeImplCache (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      actions).run (fullEncodedChallengeCache table) =
      (simulateQ
        (hyb2FullCacheRequeryImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          table)
        actions).run (fullEncodedChallengeCache table) := by
  induction actions using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind q continuation ih =>
      simp [hyb2FullCacheRequeryImpl, d2sDecodedBridgeImplCache,
        fullEncodedChallengeCache, ih]

/-- Forget H₂'s encoded-key cache after a fixed-table stopping action.  The H₁ fixed-table
handler carries only `PUnit`, so this is the exact observation under which their eager endpoints
agree. -/
def forgetHyb2FibreCache
    {α : Type}
    (outcome : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (α × (gSpec (U := U) StmtIn pSpec δ).QueryCache)) :
    Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (α × PUnit) :=
  match outcome with
  | .error reason => .error reason
  | .ok ⟨answer, _⟩ => .ok ⟨answer, PUnit.unit⟩

/-- Restore the invariant cache after observing a fixed-table H₁ stopping action.  Together
with `forgetHyb2FibreCache`, this records the stronger fact used by the adaptive lifting below:
when H₂ starts with every encoded key preloaded, each action preserves that complete cache. -/
def restoreHyb2FibreFullCache
    {α : Type}
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (outcome : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (α × PUnit)) :
    Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (α × (gSpec (U := U) StmtIn pSpec δ).QueryCache) :=
  match outcome with
  | .error reason => .error reason
  | .ok ⟨answer, _⟩ => .ok ⟨answer, fullEncodedChallengeCache table⟩

/-- **Fixed-table H₁--H₂ encoded-query endpoint.**  Preloading H₂'s fibre cache by an encoded
table makes this `gᵢ` request a cache hit, so the H₂ handler returns precisely the H₁ table
answer.  After forgetting H₂'s cache, the two computations agree as `ProbComp`s. -/
theorem hyb2FibreStoppingD2SDirect_fullCache_g_eq_hyb1StoppingD2SDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    forgetHyb2FibreCache (T_H := T_H) (T_P := T_P) <$>
      ExceptT.run ((hyb2FibreStoppingD2SDirect
        (T_H := T_H) (T_P := T_P) table (.inl gq)).run
          (fullEncodedChallengeCache table)) =
      ExceptT.run ((hyb1StoppingD2SDirect
        (T_H := T_H) (T_P := T_P) table (.inl gq)).run PUnit.unit) := by
  simp only [hyb2FibreStoppingD2SDirect, hyb1StoppingD2SDirect]
  change forgetHyb2FibreCache (T_H := T_H) (T_P := T_P) <$>
      (Except.ok <$>
        ((decodedFibreSampler
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching gq).run
          (fullEncodedChallengeCache table)) =
    (fun answer => Except.ok (answer, PUnit.unit)) <$>
      (D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl table gq
  rw [QueryImpl.withCaching_run_some
    (decodedFibreSampler
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
    (show fullEncodedChallengeCache table gq = some (table gq) by rfl)]
  rfl

/-- **Fixed-table H₁--H₂ eager endpoint.**  If H₂'s fibre cache is preloaded by the encoded
table used in H₁, each encoded challenge request returns the H₁ table answer.  The auxiliary
D2S actions use the same canonical sampler; therefore, after forgetting H₂'s cache, the full
one-query stopping handlers agree as `ProbComp`s. -/
theorem hyb2FibreStoppingD2SDirect_fullCache_eq_hyb1StoppingD2SDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (query : (d2sQueryOracles
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)).Domain) :
    forgetHyb2FibreCache (T_H := T_H) (T_P := T_P) <$>
      ExceptT.run ((hyb2FibreStoppingD2SDirect
        (T_H := T_H) (T_P := T_P) table query).run
          (fullEncodedChallengeCache table)) =
      ExceptT.run ((hyb1StoppingD2SDirect
        (T_H := T_H) (T_P := T_P) table query).run PUnit.unit) := by
  rcases query with gq | aux
  · exact hyb2FibreStoppingD2SDirect_fullCache_g_eq_hyb1StoppingD2SDirect
      (T_H := T_H) (T_P := T_P) table gq
  · rcases aux with aux | aux
    · simp only [hyb2FibreStoppingD2SDirect, hyb1StoppingD2SDirect]
      change forgetHyb2FibreCache (T_H := T_H) (T_P := T_P) <$>
          ((StateT.lift (ExceptT.lift
            ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inl aux)))).run
              (fullEncodedChallengeCache table)).run =
        ((StateT.lift (ExceptT.lift
          ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inl aux)))).run
            PUnit.unit).run
      rw [show ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inl aux)) =
        d2sUnitSampleImpl (U := U) aux by rfl]
      simp only [QueryImpl.run_stateT_lift_exceptT_lift, map_eq_bind_pure_comp, bind_assoc]
      rfl
    · simp only [hyb2FibreStoppingD2SDirect, hyb1StoppingD2SDirect]
      change forgetHyb2FibreCache (T_H := T_H) (T_P := T_P) <$>
          ((StateT.lift (ExceptT.lift
            ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)))).run
              (fullEncodedChallengeCache table)).run =
        ((StateT.lift (ExceptT.lift
          ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)))).run
            PUnit.unit).run
      rw [show ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)) =
        (QueryImpl.id' unifSpec) aux by rfl]
      simp only [QueryImpl.run_stateT_lift_exceptT_lift, map_eq_bind_pure_comp, bind_assoc]
      rfl

/-- **Full-cache invariant for the H₁--H₂ eager endpoint.**  Starting H₂ with the complete
encoded table in its cache makes each action return the same answer as H₁ *and* leave exactly
that complete cache available to the continuation. -/
theorem hyb2FibreStoppingD2SDirect_fullCache_restore_eq_hyb1StoppingD2SDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (query : (d2sQueryOracles
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)).Domain) :
    ExceptT.run ((hyb2FibreStoppingD2SDirect
      (T_H := T_H) (T_P := T_P) table query).run
        (fullEncodedChallengeCache table)) =
      restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
        ExceptT.run ((hyb1StoppingD2SDirect
          (T_H := T_H) (T_P := T_P) table query).run PUnit.unit) := by
  rcases query with gq | aux
  · simp only [hyb2FibreStoppingD2SDirect, hyb1StoppingD2SDirect]
    change (Except.ok <$>
        ((decodedFibreSampler
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table).withCaching gq).run
            (fullEncodedChallengeCache table)) =
      restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
        (fun answer => Except.ok (answer, PUnit.unit)) <$>
          (D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl table gq
    rw [QueryImpl.withCaching_run_some
      (decodedFibreSampler
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      (show fullEncodedChallengeCache table gq = some (table gq) by rfl)]
    rfl
  · rcases aux with aux | aux
    · simp only [hyb2FibreStoppingD2SDirect, hyb1StoppingD2SDirect]
      change ((StateT.lift (ExceptT.lift
        ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inl aux)))).run
          (fullEncodedChallengeCache table)).run =
        restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
          ((StateT.lift (ExceptT.lift
            ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inl aux)))).run
              PUnit.unit).run
      rw [show ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inl aux)) =
        d2sUnitSampleImpl (U := U) aux by rfl]
      simp only [QueryImpl.run_stateT_lift_exceptT_lift, map_eq_bind_pure_comp, bind_assoc]
      rfl
    · simp only [hyb2FibreStoppingD2SDirect, hyb1StoppingD2SDirect]
      change ((StateT.lift (ExceptT.lift
        ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)))).run
          (fullEncodedChallengeCache table)).run =
        restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
          ((StateT.lift (ExceptT.lift
            ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)))).run
              PUnit.unit).run
      rw [show ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)) =
        (QueryImpl.id' unifSpec) aux by rfl]
      simp only [QueryImpl.run_stateT_lift_exceptT_lift, map_eq_bind_pure_comp, bind_assoc]
      rfl

/-- **Adaptive full-cache lifting.**  The eager H₁--H₂ endpoint is stable under every finite
D2S oracle program: the H₂ run preserves the preloaded complete cache, while its observable
answer and stopping outcome agree exactly with H₁. -/
theorem simulateQ_hyb2FibreStoppingD2SDirect_fullCache_restore_eq_hyb1
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (actions : OracleComp
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) α) :
    ExceptT.run ((simulateQ
      (hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
      actions).run (fullEncodedChallengeCache table)) =
      restoreHyb2FibreFullCache (T_H := T_H) (T_P := T_P) table <$>
        ExceptT.run ((simulateQ
          (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
          actions).run PUnit.unit) := by
  induction actions using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
      rw [simulateQ_spec_query, simulateQ_spec_query]
      rw [hyb2FibreStoppingD2SDirect_fullCache_restore_eq_hyb1StoppingD2SDirect]
      rw [bind_map_left, map_eq_pure_bind]
      rw [bind_assoc]
      apply bind_congr
      intro step
      cases step with
      | error reason => rfl
      | ok output =>
          rcases output with ⟨answer, unit⟩
          simpa [restoreHyb2FibreFullCache] using ih answer

/-- Running one fixed-table bridge action through the stopping layer leaves the encoded cache
in the outer `StateT` and adds only `Except.ok`.  This is deliberately not expressed through
`liftStateTExceptTBase`: that generic lifting has the opposite transformer order and would move
the cache below the exception layer. -/
lemma hyb2StoppingD2SDirect_query_run
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (query : (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    ExceptT.run ((hyb2StoppingD2SDirect (T_H := T_H) (T_P := T_P) table query).run cache) =
      (fun valueAndCache => Except.ok valueAndCache) <$>
        ((decodedBridgeD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          table query).run cache) := by
  rcases query with gq | aux
  · rfl
  · simpa [hyb2StoppingD2SDirect, decodedBridgeD2SImpl, StateT.run_lift] using
      (QueryImpl.run_stateT_lift_exceptT_lift
        ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux) cache)

/-- The same operational characterization holds for the fixed-table fibre handler. -/
lemma hyb2FibreStoppingD2SDirect_query_run
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (query : (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    ExceptT.run ((hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table query).run cache) =
      (fun valueAndCache => Except.ok valueAndCache) <$>
        ((decodedFibreD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          table query).run cache) := by
  rcases query with gq | aux
  · rfl
  · simpa [hyb2FibreStoppingD2SDirect, decodedFibreD2SImpl, StateT.run_lift] using
      (QueryImpl.run_stateT_lift_exceptT_lift
        ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux) cache)

/-- Simulating any complete D2S action program through the bridge direct handler is precisely
the base cached simulation, with its value/cache pair marked successful. -/
theorem simulateQ_hyb2StoppingD2SDirect_run
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    {α : Type}
    (actions : OracleComp
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) α)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    ExceptT.run ((simulateQ
      (hyb2StoppingD2SDirect (T_H := T_H) (T_P := T_P) table) actions).run cache) =
      (fun valueAndCache => Except.ok valueAndCache) <$>
        (simulateQ
          (decodedBridgeD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
          actions).run cache := by
  induction actions using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind query continuation ih =>
      simp [simulateQ_bind, StateT.run_bind, ExceptT.run_bind,
        hyb2StoppingD2SDirect_query_run, ih]

/-- The fibre direct handler has the same whole-action operational characterization. -/
theorem simulateQ_hyb2FibreStoppingD2SDirect_run
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    {α : Type}
    (actions : OracleComp
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) α)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    ExceptT.run ((simulateQ
      (hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table) actions).run cache) =
      (fun valueAndCache => Except.ok valueAndCache) <$>
        (simulateQ
          (decodedFibreD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
          actions).run cache := by
  induction actions using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind query continuation ih =>
      simp [simulateQ_bind, StateT.run_bind, ExceptT.run_bind,
        hyb2FibreStoppingD2SDirect_query_run, ih]

/-- **Fixed-table H₂ stopping-step coupling.**  A complete revised D2S step has the same
distribution under the decoded bridge and under uniform-fibre sampling, including its returned
answer, successor normal state, encoded-key cache, and the enclosing `Except.ok` value.  Since
the two direct handlers introduce no exceptions, a later residual induction may apply the same
`d2sRevisedStepPost` map to both sides and therefore preserve monitor and search stopping
reasons exactly. -/
theorem evalDist_hyb2StoppingD2SDirect_step_eq_hyb2FibreStoppingD2SDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (request : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[ExceptT.run ((simulateQ
      (hyb2StoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
      (d2sQueryStepRevised normal request)).run cache)] =
      𝒟[ExceptT.run ((simulateQ
        (hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
        (d2sQueryStepRevised normal request)).run cache)] := by
  rw [simulateQ_hyb2StoppingD2SDirect_run,
    simulateQ_hyb2FibreStoppingD2SDirect_run]
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_simulateQ_decodedBridgeD2SImpl_eq_decodedFibreD2SImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table
      (d2sQueryStepRevised normal request) cache)
    (fun resultAndCache => Except.ok resultAndCache)

/-- Classify a completed H₂ D2S step after the encoded-key cache has been threaded through it.
This is the exact boundary at which a revised step either continues the verifier residual or
returns one of its two structured stopping reasons. -/
def hyb2D2SStepToStopping
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α ×
      (gSpec (U := U) StmtIn pSpec δ).QueryCache) →
      Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((α ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
          (gSpec (U := U) StmtIn pSpec δ).QueryCache)
  | (result, cache) => d2sRevisedStepPost normal result cache

/-- The direct fixed-table H₂ D2F request handler.  It exposes the complete stopping boundary
needed for the fibre reparameterization: ambient requests are lifted verbatim, while D2S
requests run the memoized decoded bridge and then classify the returned revised step. -/
noncomputable def hyb2AmbientD2FStoppingDirectImpl
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache
          (ExceptT
            (D2SRevisedStoppingReason
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp)))
  | .inl query => StateT.lift (StateT.lift (ExceptT.lift (oSpecImpl query)))
  | .inr request => fun normal => do
      let result ← simulateQ
        (hyb2StoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
        (d2sQueryStepRevised normal request)
      StateT.mk fun cache => ExceptT.mk
        (pure (d2sRevisedStepPost normal result cache))

/-- Push the fixed H₂ ambient table through the complete lossless D2F handler.  This keeps the
ordinary ambient branch literal while interpreting the memoized decoded bridge at the exact
`StateT → StateT → ExceptT` boundary used by the live executor. -/
noncomputable def hyb2AmbientD2FStoppingMappedImpl
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
  (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    oSpecImpl table).mapStateTStateTExceptTBase
    (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
      (d2sDecodedBridgeImplCache
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)))

/-- The table-pushed H₂ D2F handler is exactly its direct fixed-table counterpart.  The ambient
case preserves both state components by calculation; the D2S case is the preceding pointwise
identification of the mapped live bridge with `hyb2StoppingD2SDirect`. -/
lemma hyb2AmbientD2FStoppingMappedImpl_eq_direct
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    hyb2AmbientD2FStoppingMappedImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) oSpecImpl table =
      hyb2AmbientD2FStoppingDirectImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (T_H := T_H) (T_P := T_P) oSpecImpl table := by
  apply QueryImpl.ext
  rintro (query | query)
  · funext normal
    funext cache
    apply ExceptT.ext
    simp only [hyb2AmbientD2FStoppingMappedImpl, QueryImpl.mapStateTStateTExceptTBase,
      d2fOuterImplRevisedStopping, hyb2AmbientD2FStoppingDirectImpl]
    let Stop := D2SRevisedStoppingReason
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    change _ =
      (((StateT.lift (StateT.lift (ExceptT.lift (ε := Stop) (oSpecImpl query))) :
        StateT (D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache (ExceptT Stop ProbComp))
        (oSpec.Range query)).run normal).run cache).run
    rw [StateT.run_lift, StateT.run_bind, StateT.run_lift]
    simp [ExceptT.lift]
    rfl
  · funext normal
    funext cache
    apply ExceptT.ext
    simp only [hyb2AmbientD2FStoppingMappedImpl, QueryImpl.mapStateTStateTExceptTBase,
      d2fOuterImplRevisedStopping, hyb2AmbientD2FStoppingDirectImpl]
    dsimp only [StateT.mk, ExceptT.mk]
    change ExceptT.run (simulateQ
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      ((do
        let result ← simulateQ
          (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
            (d2sDecodedBridgeImplCache
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal)
          (d2sQueryStepRevised normal query)
        StateT.mk fun current => ExceptT.mk
          (pure (d2sRevisedStepPost normal result current))
      ).run cache).run) = _
    refine (QueryImpl.simulateQ_mapStateTExceptTBase_bind_pure_run_unwrapped
      (m := unifSpec.toPFunctor.FreeM)
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
        (d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal)
      (d2sQueryStepRevised normal query) cache (d2sRevisedStepPost normal)).trans ?_
    let outer : QueryImpl
        (oSpec + D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
        ProbComp :=
      hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table
    change ((do
      let value ← simulateQ
        (QueryImpl.mapStateTExceptTBase outer
          (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
            (d2sDecodedBridgeImplCache
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal))
        (d2sQueryStepRevised normal query)
      StateT.mk fun current => ExceptT.mk
        (pure (d2sRevisedStepPost normal value current))).run cache).run = _
    dsimp only [outer]
    rw [hyb2D2fStoppingD2SInner_mapped_eq_direct]
    rfl

/-- Run a verifier residual after the fixed H₂ table has been pushed through its complete
lossless D2F handler.  Naming this execution separates exact executor refinement from the
subsequent probabilistic fibre reparameterization. -/
noncomputable def hyb2AmbientD2fRawRevisedStoppingMapped
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    ProbComp (Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
        (gSpec (U := U) StmtIn pSpec δ).QueryCache)) :=
  (((simulateQ
    (hyb2AmbientD2FStoppingMappedImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) oSpecImpl table)
    residual).run normal).run cache).run

/-- The table-pushed residual executor is the direct fixed-table executor, preserving the
complete output, normal state, cache, and structured stopping reason. -/
lemma hyb2AmbientD2fRawRevisedStoppingMapped_eq_direct
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    hyb2AmbientD2fRawRevisedStoppingMapped
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) oSpecImpl table residual normal cache =
      (((simulateQ
        (hyb2AmbientD2FStoppingDirectImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          (T_H := T_H) (T_P := T_P) oSpecImpl table)
        residual).run normal).run cache).run := by
  simp only [hyb2AmbientD2fRawRevisedStoppingMapped]
  rw [hyb2AmbientD2FStoppingMappedImpl_eq_direct]

/-- The live H₂ lossless residual, after its decoded table is fixed, is exactly the direct
fixed-table stopping executor.  This is an equality of computations, not a distance bound. -/
theorem hyb2AmbientD2fRawRevisedStopping_hyb2_eq_direct
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    simulateQ
      (hyb2AmbientOuterImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        residual normal cache) =
      (((simulateQ
        (hyb2AmbientD2FStoppingDirectImpl
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          (T_H := T_H) (T_P := T_P) oSpecImpl table)
        residual).run normal).run cache).run := by
  rw [hyb2AmbientD2fRawRevisedStopping_pushes_outer]
  exact hyb2AmbientD2fRawRevisedStoppingMapped_eq_direct
    (T_H := T_H) (T_P := T_P) oSpecImpl table residual normal cache

/-- On a D2S request, the fixed-table direct H₂ interpreter is precisely the ordinary cached
decoded-bridge step followed by `hyb2D2SStepToStopping`.  In particular, no cache relocation or
unmentioned exception conversion occurs at this boundary. -/
lemma hyb2AmbientD2FStoppingDirectImpl_d2s_run
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (request : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    (((hyb2AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table (.inr request)).run normal).run cache).run =
      hyb2D2SStepToStopping normal <$>
        (simulateQ
          (decodedBridgeD2SImpl
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
          (d2sQueryStepRevised normal request)).run cache := by
  rw [hyb2AmbientD2FStoppingDirectImpl]
  change ExceptT.run ((do
    let result ← simulateQ
      (hyb2StoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
      (d2sQueryStepRevised normal request)
    StateT.mk fun current => ExceptT.mk
      (pure (d2sRevisedStepPost normal result current))).run cache) = _
  simp only [StateT.run_bind, ExceptT.run_bind]
  conv_lhs =>
    enter [1]
    rw [simulateQ_hyb2StoppingD2SDirect_run (T_H := T_H) (T_P := T_P)
      table (d2sQueryStepRevised normal request) cache]
  rw [bind_map_left, map_eq_pure_bind]
  apply bind_congr
  intro resultAndCache
  rcases resultAndCache with ⟨result, cache⟩
  cases result <;> rfl

/-- Fibre-sampling counterpart of `hyb2AmbientD2FStoppingDirectImpl`.  The ambient branch,
state threading, and stop classification are intentionally identical; only a fresh encoded
challenge representative is sampled from its decoded fibre. -/
noncomputable def hyb2FibreAmbientD2FStoppingDirectImpl
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache
          (ExceptT
            (D2SRevisedStoppingReason
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp)))
  | .inl query => StateT.lift (StateT.lift (ExceptT.lift (oSpecImpl query)))
  | .inr request => fun normal => do
      let result ← simulateQ
        (hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
        (d2sQueryStepRevised normal request)
      StateT.mk fun cache => ExceptT.mk
        (pure (d2sRevisedStepPost normal result cache))

/-- An ambient request is literal in both fixed-table H₂ interpreters: it preserves the normal
state and encoded-key cache and cannot introduce a stopping reason. -/
lemma hyb2AmbientD2FStoppingDirectImpl_ambient_run
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (request : oSpec.Domain) :
    (((hyb2AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table (.inl request)).run normal).run cache).run =
      (fun answer =>
        (Except.ok ((answer, normal), cache) : Except
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          ((oSpec.Range request ×
            D2SNormalState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
            (gSpec (U := U) StmtIn pSpec δ).QueryCache))) <$> oSpecImpl request := by
  unfold hyb2AmbientD2FStoppingDirectImpl
  simp [ExceptT.lift]

/-- Fibre sampling changes only D2S requests; the ambient arm is definitionally shared. -/
lemma hyb2FibreAmbientD2FStoppingDirectImpl_ambient_run
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (request : oSpec.Domain) :
    (((hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table (.inl request)).run normal).run cache).run =
      (fun answer =>
        (Except.ok ((answer, normal), cache) : Except
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          ((oSpec.Range request ×
            D2SNormalState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
            (gSpec (U := U) StmtIn pSpec δ).QueryCache))) <$> oSpecImpl request := by
  unfold hyb2FibreAmbientD2FStoppingDirectImpl
  simp [ExceptT.lift]

/-- The fibre interpreter has the same stopping boundary, with the cached fibre sampler as its
only D2S source. -/
lemma hyb2FibreAmbientD2FStoppingDirectImpl_d2s_run
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (request : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    (((hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table (.inr request)).run normal).run cache).run =
      hyb2D2SStepToStopping normal <$>
        (simulateQ
          (decodedFibreD2SImpl
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
          (d2sQueryStepRevised normal request)).run cache := by
  rw [hyb2FibreAmbientD2FStoppingDirectImpl]
  change ExceptT.run ((do
    let result ← simulateQ
      (hyb2FibreStoppingD2SDirect (T_H := T_H) (T_P := T_P) table)
      (d2sQueryStepRevised normal request)
    StateT.mk fun current => ExceptT.mk
      (pure (d2sRevisedStepPost normal result current))).run cache) = _
  simp only [StateT.run_bind, ExceptT.run_bind]
  conv_lhs =>
    enter [1]
    rw [simulateQ_hyb2FibreStoppingD2SDirect_run (T_H := T_H) (T_P := T_P)
      table (d2sQueryStepRevised normal request) cache]
  rw [bind_map_left, map_eq_pure_bind]
  apply bind_congr
  intro resultAndCache
  rcases resultAndCache with ⟨result, cache⟩
  cases result <;> rfl

/-- **H₂ fixed-table D2F step coupling.**  Replacing decoded-bridge sampling by uniform fibre
sampling changes neither the full D2F request outcome nor its updated normal state, cache, or
structured stop.  This is the exact induction step needed by the whole-residual coupling. -/
theorem evalDist_hyb2AmbientD2FStoppingDirectImpl_d2s_eq_fibre
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (request : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[(((hyb2AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
      oSpecImpl table (.inr request)).run normal).run cache).run] =
      𝒟[(((hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
        oSpecImpl table (.inr request)).run normal).run cache).run] := by
  rw [hyb2AmbientD2FStoppingDirectImpl_d2s_run,
    hyb2FibreAmbientD2FStoppingDirectImpl_d2s_run]
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_simulateQ_decodedBridgeD2SImpl_eq_decodedFibreD2SImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table
      (d2sQueryStepRevised normal request) cache)
    (hyb2D2SStepToStopping normal)

/-- **Whole-residual H₂ fixed-table coupling.**  Replacing the decoded bridge by uniform
fibre sampling preserves the distribution of a complete adaptive verifier residual.  The result
includes its returned value, normal state, encoded-key cache, and either stopping reason.
Ambient requests are identical on both sides and therefore receive no query-budget charge. -/
theorem evalDist_hyb2AmbientD2FStoppingDirectResidual_eq_fibre
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[(((simulateQ
      (hyb2AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
        oSpecImpl table)
      residual).run normal).run cache).run] =
      𝒟[(((simulateQ
        (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl table)
        residual).run normal).run cache).run] := by
  induction residual using OracleComp.inductionOn generalizing normal cache with
  | pure value => rfl
  | query_bind request continuation ih =>
      cases request with
      | inl query =>
          simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
          rw [simulateQ_spec_query, simulateQ_spec_query]
          rw [hyb2AmbientD2FStoppingDirectImpl_ambient_run,
            hyb2FibreAmbientD2FStoppingDirectImpl_ambient_run]
          rw [evalDist_bind, evalDist_bind]
          apply bind_congr
          intro step
          cases step with
          | error reason => rfl
          | ok output =>
              rcases output with ⟨⟨answer, normal'⟩, cache'⟩
              exact ih answer normal' cache'
      | inr query =>
          simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
          rw [simulateQ_spec_query, simulateQ_spec_query]
          rw [evalDist_bind, evalDist_bind]
          rw [evalDist_hyb2AmbientD2FStoppingDirectImpl_d2s_eq_fibre]
          apply bind_congr
          intro step
          cases step with
          | error reason => rfl
          | ok output =>
              rcases output with ⟨⟨answer, normal'⟩, cache'⟩
              exact ih answer normal' cache'

/-- The single continuous H₂ residual: the malicious prover returns its salted proof and the
forward verifier consumes that exact result from the inherited D2S state and cache.  This avoids
an unsound restart between the two phases. -/
noncomputable def hyb2FullResidual
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
  maliciousProver >>= fun output => runForwardVerifierWide δ V output.1 output.2

/-- **H₂ whole-run fixed-table coupling.**  This is the prior residual coupling specialized to
the actual prover-then-verifier program.  It preserves the inherited normal state and cache
across the phase boundary, so it is suitable for the eventual Claim 5.22 game refinement. -/
theorem evalDist_hyb2FullResidual_direct_eq_fibre
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[(((simulateQ
      (hyb2AmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
        oSpecImpl table)
      (hyb2FullResidual (U := U) (δ := δ) V maliciousProver)).run
        (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run ∅).run] =
      𝒟[(((simulateQ
        (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl table)
        (hyb2FullResidual (U := U) (δ := δ) V maliciousProver)).run
          (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run ∅).run] := by
  exact evalDist_hyb2AmbientD2FStoppingDirectResidual_eq_fibre
    (T_H := T_H) (T_P := T_P) oSpecImpl table
    (hyb2FullResidual (U := U) (δ := δ) V maliciousProver)
    (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ∅

/-- The actual live H₂ full residual, with its decoded table fixed, has the same distribution as
the uniform-fibre whole-run interpreter.  The equality first pushes the fixed table through the
live lossless executor and then applies the complete adaptive residual coupling. -/
theorem evalDist_hyb2FullResidual_live_eq_fibre
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[simulateQ
      (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sDecodedBridgeImplCache
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (hyb2FullResidual (U := U) (δ := δ) V maliciousProver)
        (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ∅)] =
      𝒟[(((simulateQ
        (hyb2FibreAmbientD2FStoppingDirectImpl (T_H := T_H) (T_P := T_P)
          oSpecImpl table)
        (hyb2FullResidual (U := U) (δ := δ) V maliciousProver)).run
          (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run ∅).run] := by
  rw [hyb2AmbientD2fRawRevisedStopping_hyb2_eq_direct]
  exact evalDist_hyb2FullResidual_direct_eq_fibre
    (T_H := T_H) (T_P := T_P) oSpecImpl table V maliciousProver

/-- Evaluate a complete ambient/D2S residual while making the encoded-key cache explicit.  The
parameter `d2sImpl` is deliberately restricted to the state-threaded D2S action interface: this
prevents the H₂ fibre replacement from changing the ambient oracle, normal state, or stopping
discipline. -/
noncomputable def hyb2AmbientDirectResidualRun
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (d2sImpl : QueryImpl
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache ProbComp))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut)) :
    D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) →
    (gSpec (U := U) StmtIn pSpec δ).QueryCache →
    ProbComp (Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
        (gSpec (U := U) StmtIn pSpec δ).QueryCache)) :=
  OracleComp.recOn residual
    (fun value normal cache => pure (.ok ((value, normal), cache)))
    (fun request _continuation ih normal cache =>
      match request with
      | .inl query => do
          let answer ← oSpecImpl query
          ih answer normal cache
      | .inr query => do
          let resultAndCache ←
            (simulateQ d2sImpl (d2sQueryStepRevised normal query)).run cache
          match resultAndCache.1 with
          | .continue answer normal' => ih answer normal' resultAndCache.2
          | .stopped normal' record => pure (.error (.monitorStop normal' record))
          | .underlyingAbort => pure (.error (.underlyingAbort normal)))

/-- The explicit residual runner unfolds an ambient head request without touching either the
normal sponge state or the encoded-key cache. -/
@[simp] lemma hyb2AmbientDirectResidualRun_ambient
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (d2sImpl : QueryImpl
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache ProbComp))
    (query : oSpec.Domain)
    (continuation : oSpec.Range query → OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    hyb2AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl d2sImpl
      (liftM (OracleSpec.query (spec := oSpec + duplexSpongeChallengeOracle StmtIn U)
        (Sum.inl query)) >>= continuation) normal cache =
      (do
        let answer ← oSpecImpl query
        hyb2AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl d2sImpl
          (continuation answer) normal cache) := rfl

/-- The explicit residual runner unfolds a D2S head request through exactly one stateful revised
step and immediately preserves the returned cache when it continues. -/
@[simp] lemma hyb2AmbientDirectResidualRun_d2s
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (d2sImpl : QueryImpl
      (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache ProbComp))
    (query : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (continuation : (duplexSpongeChallengeOracle StmtIn U).Range query → OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    hyb2AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl d2sImpl
      (liftM (OracleSpec.query (spec := oSpec + duplexSpongeChallengeOracle StmtIn U)
        (Sum.inr query)) >>= continuation) normal cache =
      (do
        let resultAndCache ←
          (simulateQ d2sImpl (d2sQueryStepRevised normal query)).run cache
        match resultAndCache.1 with
        | .continue answer normal' =>
            hyb2AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl d2sImpl
              (continuation answer) normal' resultAndCache.2
        | .stopped normal' record => pure (.error (.monitorStop normal' record))
        | .underlyingAbort => pure (.error (.underlyingAbort normal))) := rfl

/-- **Whole-residual H₂ fibre coupling.**  For every adaptive verifier residual, the fixed
decoded-table bridge and the corresponding uniform-fibre sampler have the same output
distribution, including normal state, cache, monitor stop, and underlying-search stop.  Ambient
queries are carried literally and receive no collision charge. -/
theorem evalDist_hyb2AmbientDirectResidualRun_bridge_eq_fibre
    {ι : Type} {oSpec : OracleSpec ι}
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    𝒟[hyb2AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl
      (decodedBridgeD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
      residual normal cache] =
      𝒟[hyb2AmbientDirectResidualRun (T_H := T_H) (T_P := T_P) oSpecImpl
        (decodedFibreD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        residual normal cache] := by
  induction residual using OracleComp.inductionOn generalizing normal cache with
  | pure value => rfl
  | query_bind request continuation ih =>
      cases request with
      | inl query =>
          rw [hyb2AmbientDirectResidualRun_ambient,
            hyb2AmbientDirectResidualRun_ambient, evalDist_bind, evalDist_bind]
          apply bind_congr
          intro answer
          exact ih answer normal cache
      | inr query =>
          rw [hyb2AmbientDirectResidualRun_d2s,
            hyb2AmbientDirectResidualRun_d2s, evalDist_bind, evalDist_bind]
          rw [evalDist_simulateQ_decodedBridgeD2SImpl_eq_decodedFibreD2SImpl]
          apply bind_congr
          intro resultAndCache
          rcases resultAndCache with ⟨result, cache'⟩
          cases result with
          | «continue» answer normal' => exact ih answer normal' cache'
          | stopped normal' record => rfl
          | underlyingAbort => rfl


end DuplexSpongeFS.KeyLemma
