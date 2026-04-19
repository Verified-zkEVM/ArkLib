/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Lemma 5.1 of the Chiesa-Orrù paper

This file provides the Section 5 key-lemma interface:
- the DSFS and basic-FS game experiments,
- paper-facing abstractions for `D2SAlgo` and the Section 5.8 trace-reporting maps, and
- a statistical-distance theorem surface with the query-bound side condition.

The full hybrid proof from Section 5.8 is still staged across the other Section 5 files.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  -- All messages are serializable to vectors of units
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  -- All challenges are deserializable from vectors of units
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

section SecurityGames

/-- Basic-FS oracle family augmented with explicit unit-sampling randomness. -/
abbrev FSPlusUnitOracle :=
  (fsChallengeOracle StmtIn pSpec) + (Unit →ₒ U)

/-- Project out the auxiliary unit-sampling queries from logs over
`oSpec + (fsChallengeOracle + Unit →ₒ U)`. -/
def projectFSPlusUnitQueryLog
    (log : QueryLog (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr (.inl q), r⟩ => some ⟨.inr q, r⟩
    | ⟨.inr (.inr _), _⟩ => none

/-- Lift queries from `oSpec + fsChallengeOracle` into
`oSpec + (fsChallengeOracle + Unit →ₒ U)` by routing through `.inl`. -/
private def liftFSQueriesToFSPlusUnit :
    QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec)
      (OracleComp (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :=
  fun q =>
    match q with
    | .inl qShared =>
        query
          (spec := oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (Sum.inl qShared)
    | .inr qFS =>
        query
          (spec := oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (Sum.inr (Sum.inl qFS))

/-- Output of the basic Fiat-Shamir game used in Lemma 5.1. -/
abbrev BasicFiatShamirGameOutput :=
  StmtIn × StmtOut × pSpec.Messages ×
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)

/-- Output of the duplex-sponge Fiat-Shamir game used in Lemma 5.1. -/
abbrev DuplexSpongeFiatShamirGameOutput :=
  StmtIn × StmtOut × pSpec.Messages ×
    QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) ×
    QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)

/-- First game for the key lemma: the basic Fiat-Shamir transform. -/
def basicFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
  (P : OracleComp (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages))) :
    OptionT (OracleComp (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec)) := do
  let ⟨stmtAndMsgs?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtIn, messages⟩ ←
    match stmtAndMsgs? with
    | some stmtAndMsgs => pure stmtAndMsgs
    | none => failure
  let verifierComp :
      OracleComp (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (Option StmtOut) :=
    simulateQ
      (liftFSQueriesToFSPlusUnit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (V.fiatShamir.run stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run
  let ⟨stmtOut, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp).run
  let proveQueryLog :=
    projectFSPlusUnitQueryLog
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    projectFSPlusUnitQueryLog
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) verifyQueryLogRaw
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog, verifyQueryLog⟩

/-- Second game for the key lemma: the duplex-sponge Fiat-Shamir transform. -/
def duplexSpongeFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (DuplexSpongeFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) := do
  let ⟨⟨stmtIn, messages⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle
      (V.duplexSpongeFiatShamir.run
        stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog, verifyQueryLog⟩

/-- The D2S prover transform from Section 5.4 (DSFS prover to basic-FS prover). -/
abbrev D2SAlgo :=
  OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages) →
    OracleComp (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages))

/-- Generic Section 5.8 trace-reporting map used to post-process DSFS logs into the common
basic-FS output space. This is intentionally more general than the paper's single `D2STrace`
algorithm. -/
structure Section58TraceMap where
  run :
    QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) → -- `tr_P̃`
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) → -- `tr_V`
      -- `tr` is the mapped basic-FS logs; this can abort because `StdTrace` can abort, see
      -- Section 5.5.1.
      Option
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))

/-- Apply a Section 5.8 trace-reporting map to the DSFS game output so both experiments live in the
same output space. -/
def Section58TraceMap.mapOutput (traceMap : Section58TraceMap (oSpec := oSpec) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U)) :
    DuplexSpongeFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) →
      Option
        (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec)) :=
  fun output =>
    let ⟨stmtIn, stmtOut, messages, proveQueryLogDS, verifyQueryLogDS⟩ := output
    match traceMap.run proveQueryLogDS verifyQueryLogDS with
    | none => none
    | some (proveQueryLogFS, verifyQueryLogFS) =>
        some (stmtIn, stmtOut, messages, proveQueryLogFS, verifyQueryLogFS)

/-- Distribution of the basic-FS game output under a concrete oracle implementation. -/
def basicFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages))) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec)) := do
  (simulateQ impl (basicFiatShamirGame (V := V) P).run).run' (← init)

/-- Distribution of the DSFS game output under a concrete oracle implementation. -/
def duplexSpongeFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (Option <| DuplexSpongeFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) := do
  (simulateQ impl (duplexSpongeFiatShamirGame (V := V) P).run).run' (← init)

/-- Left experiment of Lemma 5.1 after applying a trace-reporting map to DSFS logs. -/
def mappedDuplexSpongeFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (traceMap : Section58TraceMap (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec)) := do
  let outputDS ← duplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
  match outputDS with
  | none => return none
  | some output =>
      return traceMap.mapOutput output

end SecurityGames

section KeyLemma

open scoped NNReal

/-- `θStar` in the paper, equal to `t_p`, the forward-permutation query budget of the malicious
prover. -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/--
Fixed-parameter codec bias profile `i ↦ ε_{cdc,i}(λ,n)` from Definition 4.1.

The paper parameters `(λ, n)` are suppressed in the Lean surface: they are assumed fixed by the
ambient protocol/oracle instantiation, and `εcodec` records only the per-round bias values used in
the Section 5 bounds.
-/
abbrev CodecBias :=
  pSpec.ChallengeIdx → ℝ≥0

/-- `ηStar` in Equation (5) of Lemma 5.1. -/
noncomputable def ηStar (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ : ℕ) (L : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  let tTotal : ℕ := (tₕ + tₚ + tₚᵢ)
  let tTotalR : ℝ := tTotal
  let LplusOneR : ℝ := (L + 1)
  let firstTermNumerator : ℝ :=
    7 * tTotalR ^ 2
      + 28 * LplusOneR * tTotalR
      + 14 * LplusOneR ^ 2
      - 3 * tTotalR
      - 13 * LplusOneR
  let firstTermDenominator : ℝ := 2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  let secondTerm : ℝ := (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
  let thirdTerm : ℝ := ∑ i, (εcodec i : ℝ)
  firstTermNumerator / firstTermDenominator + secondTerm + thirdTerm

/-- Reusable four-step hybrid composition bound. -/
theorem tvDist_hybridChain4
    {α : Type}
    (H₀ H₁ H₂ H₃ H₄ : ProbComp α)
    {e₀₁ e₁₂ e₂₃ e₃₄ : ℝ}
    (h₀₁ : tvDist H₀ H₁ ≤ e₀₁)
    (h₁₂ : tvDist H₁ H₂ ≤ e₁₂)
    (h₂₃ : tvDist H₂ H₃ ≤ e₂₃)
    (h₃₄ : tvDist H₃ H₄ ≤ e₃₄) :
    tvDist H₀ H₄ ≤ e₀₁ + e₁₂ + e₂₃ + e₃₄ := by
  have h₀₄ : tvDist H₀ H₄ ≤ tvDist H₀ H₁ + tvDist H₁ H₄ := by
    simpa using tvDist_triangle H₀ H₁ H₄
  have h₁₄ : tvDist H₁ H₄ ≤ tvDist H₁ H₂ + tvDist H₂ H₄ := by
    simpa using tvDist_triangle H₁ H₂ H₄
  have h₂₄ : tvDist H₂ H₄ ≤ tvDist H₂ H₃ + tvDist H₃ H₄ := by
    simpa using tvDist_triangle H₂ H₃ H₄
  linarith

/-- Shared state used by the canonical Section 5.8 DS experiment: ambient shared-oracle state,
the random-hash cache, and the permutation-oracle state. -/
abbrev Section58DSState
    (σShared σPerm : Type) :=
  σShared × (StmtIn →ₒ Vector U SpongeSize.C).QueryCache × σPerm

/-- Shared state used by the canonical Section 5.8 basic-FS experiment: ambient shared-oracle state
and the lazy random-function cache for FS challenges. -/
abbrev Section58FSState
    (σShared : Type) :=
  σShared × (srChallengeOracle StmtIn pSpec).QueryCache

/-- Fixed ambient shared-oracle witness used by the paper's Section 5.8 experiments. -/
class Section58SharedOracleWitness where
  σShared : Type
  initShared : ProbComp σShared
  implShared : QueryImpl oSpec (StateT σShared ProbComp)

/-- Fixed permutation-sampler witness used by the paper's `𝒟_𝔖(λ,n)` experiment. -/
class Section58PermutationWitness where
  σPerm : Type
  initPerm : ProbComp σPerm
  implPerm : QueryImpl (permutationOracle (CanonicalSpongeState U)) (StateT σPerm ProbComp)

/-- Minimal semantic law currently exposed for a Section 5.8 permutation witness: answers in the
support of the forward and backward directions must remain mutually consistent across one-step
state transitions. This does not yet capture the full random-permutation law of `𝒟_𝔖(λ,n)`, but it
at least prevents treating an arbitrary pair of unrelated forward/backward samplers as the paper's
permutation oracle. -/
def Section58PermutationWitnessLaw
    [permW : Section58PermutationWitness (U := U)] : Prop :=
  (∀ (σ : permW.σPerm) (stateIn stateOut : CanonicalSpongeState U) (σ' : permW.σPerm),
      (stateOut, σ') ∈ support ((permW.implPerm (.inl stateIn)).run σ) →
        stateIn ∈ Prod.fst '' support ((permW.implPerm (.inr stateOut)).run σ'))
    ∧
  (∀ (σ : permW.σPerm) (stateOut stateIn : CanonicalSpongeState U) (σ' : permW.σPerm),
      (stateIn, σ') ∈ support ((permW.implPerm (.inr stateOut)).run σ) →
        stateOut ∈ Prod.fst '' support ((permW.implPerm (.inl stateIn)).run σ'))

/-- Canonical Section 5.8 initializer for the DS-side experiment: keep the shared-oracle state,
start the hash oracle with an empty cache, and sample the permutation-oracle state separately. -/
def section58CanonicalDSInit
    {σShared σPerm : Type}
    (sharedInit : ProbComp σShared)
    (permInit : ProbComp σPerm) :
    ProbComp (Section58DSState (StmtIn := StmtIn) (U := U) σShared σPerm) := do
  let sharedState ← sharedInit
  let permState ← permInit
  pure (sharedState, ∅, permState)

/-- Canonical Section 5.8 implementation for the DS-side experiment: shared-oracle queries are
answered by the ambient implementation, the `h` component is a lazy random oracle, and the
permutation component is delegated to the supplied permutation sampler. -/
def section58CanonicalDSImpl
    [DecidableEq StmtIn] [SampleableType U]
    {σShared σPerm : Type}
    (sharedImpl : QueryImpl oSpec (StateT σShared ProbComp))
    (permImpl : QueryImpl (permutationOracle (CanonicalSpongeState U)) (StateT σPerm ProbComp)) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (Section58DSState (StmtIn := StmtIn) (U := U) σShared σPerm) ProbComp) :=
  fun q => do
    let ⟨sharedState, hashCache, permState⟩ ← get
    match q with
    | .inl qShared =>
        let (resp, sharedState') ← (sharedImpl qShared).run sharedState
        set (sharedState', hashCache, permState)
        pure resp
    | .inr (.inl qHash) =>
        let (resp, hashCache') ←
          ((randomOracle :
            QueryImpl (StmtIn →ₒ Vector U SpongeSize.C)
              (StateT (StmtIn →ₒ Vector U SpongeSize.C).QueryCache ProbComp)) qHash).run hashCache
        set (sharedState, hashCache', permState)
        pure resp
    | .inr (.inr qPerm) =>
        let (resp, permState') ← (permImpl qPerm).run permState
        set (sharedState, hashCache, permState')
        pure resp

/-- Canonical Section 5.8 initializer for the basic-FS experiment: keep the shared-oracle state and
start the lazy FS challenge random function with an empty cache. -/
def section58CanonicalFSInit
    {σShared : Type}
    (sharedInit : ProbComp σShared) :
    ProbComp (Section58FSState (StmtIn := StmtIn) (pSpec := pSpec) σShared) := do
  let sharedState ← sharedInit
  pure (sharedState, ∅)

/-- Canonical Section 5.8 implementation for the basic-FS experiment: shared-oracle queries are
answered by the ambient implementation, FS challenges come from the canonical lazy random
function, and explicit unit-sampling queries stay fresh via `d2sUnitSampleImpl`. -/
def section58CanonicalFSImpl
    [DecidableEq StmtIn] [SampleableType U] [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {σShared : Type}
    (sharedImpl : QueryImpl oSpec (StateT σShared ProbComp)) :
    QueryImpl (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT (Section58FSState (StmtIn := StmtIn) (pSpec := pSpec) σShared) ProbComp) :=
  fun q => do
    let ⟨sharedState, challengeCache⟩ ← get
    match q with
    | .inl qShared =>
        let (resp, sharedState') ← (sharedImpl qShared).run sharedState
        set (sharedState', challengeCache)
        pure resp
    | .inr (.inl qFS) =>
        let (resp, challengeCache') ←
          (((srChallengeQueryImpl (Statement := StmtIn) (pSpec := pSpec)).withCaching :
            QueryImpl (fsChallengeOracle StmtIn pSpec)
              (StateT (fsChallengeOracle StmtIn pSpec).QueryCache ProbComp)) qFS).run
            challengeCache
        set (sharedState, challengeCache')
        pure resp
    | .inr (.inr qUnit) =>
        let resp ← StateT.lift <| d2sUnitSampleImpl (U := U) qUnit
        pure resp

/-- Named DS-side sampler corresponding to the paper's fixed `𝒟_𝔖(λ,n)` experiment, relative to
the ambient shared-oracle and permutation witnesses. -/
abbrev paperDSInit [sharedW : Section58SharedOracleWitness (oSpec := oSpec)]
    [permW : Section58PermutationWitness (U := U)] :
    ProbComp (Section58DSState
      (StmtIn := StmtIn) (U := U)
      sharedW.σShared permW.σPerm) :=
  section58CanonicalDSInit
    (StmtIn := StmtIn) (U := U)
    sharedW.initShared permW.initPerm

/-- Named DS-side implementation corresponding to the paper's fixed `𝒟_𝔖(λ,n)` experiment,
relative to the ambient shared-oracle and permutation witnesses. -/
abbrev paperDSImpl [DecidableEq StmtIn] [SampleableType U]
    [sharedW : Section58SharedOracleWitness (oSpec := oSpec)]
    [permW : Section58PermutationWitness (U := U)] :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (Section58DSState
        (StmtIn := StmtIn) (U := U)
        sharedW.σShared permW.σPerm) ProbComp) :=
  section58CanonicalDSImpl
    (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
    sharedW.implShared permW.implPerm

/-- Named basic-FS-side sampler corresponding to the paper's fixed `𝒟_IP(λ,n)` experiment,
relative to the ambient shared-oracle witness. -/
abbrev paperIPInit [sharedW : Section58SharedOracleWitness (oSpec := oSpec)] :
    ProbComp (Section58FSState
      (StmtIn := StmtIn) (pSpec := pSpec) sharedW.σShared) :=
  section58CanonicalFSInit
    (StmtIn := StmtIn) (pSpec := pSpec)
    sharedW.initShared

/-- Named basic-FS-side implementation corresponding to the paper's fixed `𝒟_IP(λ,n)` experiment,
relative to the ambient shared-oracle witness. -/
abbrev paperIPImpl [DecidableEq StmtIn] [SampleableType U]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [sharedW : Section58SharedOracleWitness (oSpec := oSpec)] :
    QueryImpl (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT (Section58FSState
        (StmtIn := StmtIn) (pSpec := pSpec) sharedW.σShared) ProbComp) :=
  section58CanonicalFSImpl
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    sharedW.implShared

/-- `Hyb₀`: left experiment in Section 5.8 (mapped DSFS experiment). -/
abbrev hyb0Dist
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (paperD2STrace : Section58TraceMap
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    initDS implDS V maliciousProver paperD2STrace

/-- `Hyb₄`: right experiment in Section 5.8 (basic-FS experiment after `D2SAlgo`). -/
abbrev hyb4Dist
    {σFS : Type}
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  basicFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    initFS implFS V (d2sAlgo maliciousProver)
/-- Claim 5.21 bound (`Hyb₀` vs `Hyb₁`). -/
noncomputable def claim5_21Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- Claim 5.22 bound (`Hyb₁` vs `Hyb₂`). -/
noncomputable def claim5_22Bound
    (tₕ tₚ tₚᵢ : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
    + ∑ i, (εcodec i : ℝ)

/-- Claim 5.24 bound (`Hyb₃` vs `Hyb₄`). -/
noncomputable def claim5_24Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let Lr : ℝ := L
  let cardPow : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  (7 * Lr * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + Lr + 2 * (tₚᵢ : ℝ))) / (2 * cardPow)
    - (5 * (Lr + 1)) / cardPow

/-- Canonical `Hyb₁` experiment from Section 5.8. -/
abbrev section58Hyb1Dist
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (hyb1TraceMap : Section58TraceMap
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    initDS implDS V maliciousProver hyb1TraceMap

/-- Canonical `Hyb₂` experiment from Section 5.8. -/
abbrev section58Hyb2Dist
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (hyb2TraceMap : Section58TraceMap
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    initDS implDS V maliciousProver hyb2TraceMap

/-- Canonical `Hyb₃` experiment from Section 5.8. -/
abbrev section58Hyb3Dist
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (hyb3TraceMap : Section58TraceMap
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    initDS implDS V maliciousProver hyb3TraceMap

/-- The paper's single `D2STrace` algorithm, used by `Hyb₀` in the Section 5.8 proof chain.

TODO: replace this placeholder by the exact trace transform corresponding to the left experiment of
Lemma 5.1. -/
noncomputable def paperD2STrace :
    Section58TraceMap (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := by
  sorry

/-- Concrete trace-reporting map used by `Hyb₁` in the Section 5.8 proof chain.

TODO: instantiate the paper's first hybrid trace transform, including the exact line-11 sampling /
programming behavior from Section 5.8. -/
noncomputable def section58Hyb1TraceMap :
    Section58TraceMap (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := by
  sorry

/-- Concrete trace-reporting map used by `Hyb₂` in the Section 5.8 proof chain.

TODO: instantiate the paper's second hybrid trace transform, where the verifier messages are
sampled via `ψᵢ⁻¹ ∘ ψᵢ ∘ U(Σ^{ℓ_V(i)})`. -/
noncomputable def section58Hyb2TraceMap :
    Section58TraceMap (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := by
  sorry

/-- Concrete trace-reporting map used by `Hyb₃` in the Section 5.8 proof chain.

TODO: instantiate the paper's third hybrid trace transform, where verifier messages are sampled
uniformly in the verifier message space and then lifted through `ψᵢ⁻¹`. -/
noncomputable def section58Hyb3TraceMap :
    Section58TraceMap (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := by
  sorry

/-- Claim 5.21 target proposition on the canonical `Hyb₀`/`Hyb₁` experiments from Section 5.8. -/
def claim_5_21
    [Fintype U] [SampleableType U] [DecidableEq StmtIn]
    [Section58SharedOracleWitness (oSpec := oSpec)]
    [Section58PermutationWitness (U := U)]
    (securityParam instanceBound : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ) :
    Prop :=
  let _ := securityParam
  let _ := instanceBound
  tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver paperD2STrace)
      (section58Hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver section58Hyb1TraceMap)
    ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries

/-- Claim 5.22 target proposition on the canonical `Hyb₁`/`Hyb₂` experiments from Section 5.8. -/
def claim_5_22
    [SampleableType U] [DecidableEq StmtIn]
    [Section58SharedOracleWitness (oSpec := oSpec)]
    [Section58PermutationWitness (U := U)]
    (securityParam instanceBound : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : CodecBias (pSpec := pSpec)) :
    Prop :=
  let _ := securityParam
  let _ := instanceBound
  tvDist
      (section58Hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver section58Hyb1TraceMap)
      (section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver section58Hyb2TraceMap)
    ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec

/-- Claim 5.23 target proposition on the canonical `Hyb₂`/`Hyb₃` experiments from Section 5.8. -/
def claim_5_23
    [SampleableType U] [DecidableEq StmtIn]
    [Section58SharedOracleWitness (oSpec := oSpec)]
    [Section58PermutationWitness (U := U)]
    (securityParam instanceBound : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Prop :=
  let _ := securityParam
  let _ := instanceBound
  tvDist
    (section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
      (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
      V maliciousProver section58Hyb2TraceMap)
    (section58Hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
      (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
      V maliciousProver section58Hyb3TraceMap) = 0

/-- Claim 5.24 target proposition on the canonical `Hyb₃`/`Hyb₄` experiments from Section 5.8. -/
def claim_5_24
    [Fintype U] [SampleableType U] [DecidableEq StmtIn]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOracleWitness (oSpec := oSpec)]
    [Section58PermutationWitness (U := U)]
    (securityParam instanceBound : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    Prop :=
  let _ := securityParam
  let _ := instanceBound
  tvDist
      (section58Hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver section58Hyb3TraceMap)
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
        (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver d2sAlgo)
    ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries

/--
Lemma 5.1 distance component from Claims 5.21-5.24, as a statement-only bridge.

This keeps the hybrid decomposition explicit and postpones the arithmetic reconciliation with
`ηStar` to dedicated proof steps.
-/
theorem lemma_5_1_dist_from_claims
    [Fintype U] [SampleableType U] [DecidableEq StmtIn]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOracleWitness (oSpec := oSpec)]
    [Section58PermutationWitness (U := U)]
    (securityParam instanceBound : ℕ)
    (hPermWitnessLaw : Section58PermutationWitnessLaw (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : CodecBias (pSpec := pSpec))
    (h21 : claim_5_21 (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      securityParam instanceBound V maliciousProver tₕ tₚ tₚᵢ)
    (h22 : claim_5_22 (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      securityParam instanceBound V maliciousProver tₕ tₚ tₚᵢ εcodec)
    (h23 : claim_5_23 (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      securityParam instanceBound V maliciousProver)
    (h24 : claim_5_24 (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      securityParam instanceBound V maliciousProver d2sAlgo tₕ tₚ tₚᵢ)
    (hBound :
      claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        + claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec
        + 0
        + claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)) :
    tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver paperD2STrace)
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
        (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver d2sAlgo)
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ) := by
  let _ := hPermWitnessLaw
  have h23' :
      tvDist
        (section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
          (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
          V maliciousProver section58Hyb2TraceMap)
        (section58Hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
          (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
          V maliciousProver section58Hyb3TraceMap)
        ≤ (0 : ℝ) := by
    rw [h23]
  have hChain :=
    tvDist_hybridChain4
      (H₀ := hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver paperD2STrace)
      (H₁ := section58Hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver section58Hyb1TraceMap)
      (H₂ := section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver section58Hyb2TraceMap)
      (H₃ := section58Hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver section58Hyb3TraceMap)
      (H₄ := hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
        (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver d2sAlgo)
      (e₀₁ := claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
      (e₁₂ := claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec)
      (e₂₃ := 0)
      (e₃₄ := claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
      h21 h22 h23' h24
  linarith

/--
Lemma 5.1 in existential form (paper-facing statement), for the canonical Section 5.8 oracle
surface.

The statement fixes the basic-FS side to the canonical lazy random-function sampler and the
DS-side hash oracle to the canonical lazy random-function sampler, while leaving only the ambient
shared-oracle implementation and the DS permutation sampler as explicit inputs. The existential
quantifiers for `D2SAlgo` and the paper's `D2STrace` now precede the malicious prover, matching
the paper: the same transformed prover/trace algorithms must work for every malicious prover under
the stated query bound. The auxiliary hybrid trace-reporting maps used in the Section 5.8 proof
chain remain an internal proof obligation when proving this theorem from
`lemma_5_1_dist_from_claims`.
-/
theorem lemma_5_1
    [Fintype U] [SampleableType U]
    [DecidableEq StmtIn]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOracleWitness (oSpec := oSpec)]
    [Section58PermutationWitness (U := U)]
    (securityParam instanceBound : ℕ)
    (hPermWitnessLaw : Section58PermutationWitnessLaw (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : CodecBias (pSpec := pSpec))
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge) :
    ∃ (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (paperD2STrace : Section58TraceMap
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
      ∀ (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (StmtIn × pSpec.Messages)),
      OracleComp.IsTotalQueryBound maliciousProver (tₕ + tₚ + tₚᵢ) →
      tvDist
        (mappedDuplexSpongeFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
          (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
          V maliciousProver paperD2STrace)
        (basicFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec)
          (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
          (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          V (d2sAlgo maliciousProver))
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)
      ∧ OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ) := by
  let _ := securityParam
  let _ := instanceBound
  let _ := hPermWitnessLaw
  sorry

end KeyLemma

end DuplexSpongeFS
