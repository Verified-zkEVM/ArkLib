/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Lemma 5.1 of the Chiesa-Orrù paper

This file provides the Section 5 key-lemma interface:
- the DSFS and basic-FS game experiments,
- paper-facing abstractions for `D2SAlgo` and the Section 5.8 trace algorithms, and
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
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

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
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)

/-- Output of the duplex-sponge Fiat-Shamir game used in Lemma 5.1. -/
abbrev DuplexSpongeFiatShamirGameOutput :=
  StmtIn × StmtOut × pSpec.Messages ×
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
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog ++ verifyQueryLog⟩

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
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog ++ verifyQueryLog⟩

/-- The D2S prover transform from Section 5.4 (DSFS prover to basic-FS prover). -/
abbrev D2SAlgo :=
  OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages) →
    OracleComp (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages))

/-- Execute a Section 5.8 trace map inside `ProbComp` by interpreting the auxiliary unit-sampling
oracle uniformly. -/
def runSection58TraceMap
    [SampleableType U]
    (traceMap :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (fullTrace : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp
      (Option (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

/-- Project out the auxiliary unit-sampling queries from logs over
`oSpec + (challengeSpec + Unit →ₒ U)`. -/
def projectD2SChallengePlusUnitQueryLog
    {κ : Type} {challengeSpec : OracleSpec κ}
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :
    QueryLog (oSpec + challengeSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr (.inl q), r⟩ => some ⟨.inr q, r⟩
    | ⟨.inr (.inr _), _⟩ => none

/-- Execute a Section 5.8 line-4 trace map on a projected hybrid trace. -/
def runSection58ProjectedTraceMap
    [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (traceMap :
      QueryLog (oSpec + challengeSpec) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (fullTrace : QueryLog (oSpec + challengeSpec)) :
    ProbComp
      (Option (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

/-- Shared-oracle state paired with a lazy random-function cache for an explicit hybrid
challenge-oracle family. -/
abbrev Section58ChallengeState
    {κ : Type}
    (challengeSpec : OracleSpec κ)
    (σShared : Type) :=
  σShared × challengeSpec.QueryCache

/-- Canonical initializer for a shared oracle plus a lazy random-function hybrid challenge family. -/
def section58ChallengeInit
    {κ : Type} {challengeSpec : OracleSpec κ}
    {σShared : Type}
    (sharedInit : ProbComp σShared) :
    ProbComp (Section58ChallengeState challengeSpec σShared) := do
  let sharedState ← sharedInit
  pure (sharedState, ∅)

/-- Canonical implementation for a shared oracle plus a lazy random-function hybrid challenge
family, augmented with the auxiliary unit-sampling oracle used by `D2SQuery`. -/
def section58ChallengeImpl
    {κ : Type} {challengeSpec : OracleSpec κ}
    [SampleableType U]
    [DecidableEq κ]
    [∀ q : challengeSpec.Domain, SampleableType (challengeSpec.Range q)]
    {σShared : Type}
    (sharedImpl : QueryImpl oSpec (StateT σShared ProbComp)) :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT (Section58ChallengeState challengeSpec σShared) ProbComp) :=
  fun q => do
    let ⟨sharedState, challengeCache⟩ ← get
    match q with
    | .inl qShared =>
        let (resp, sharedState') ← (sharedImpl qShared).run sharedState
        set (sharedState', challengeCache)
        pure resp
    | .inr (.inl qChallenge) =>
        let (resp, challengeCache') ←
          ((randomOracle :
            QueryImpl challengeSpec (StateT challengeSpec.QueryCache ProbComp)) qChallenge).run
            challengeCache
        set (sharedState, challengeCache')
        pure resp
    | .inr (.inr (.inl qUnit)) =>
        let resp ← StateT.lift <| d2sUnitSampleImpl (U := U) qUnit
        pure resp
    | .inr (.inr (.inr qUnif)) =>
        let resp ← StateT.lift <|
          (show ProbComp (unifSpec.Range qUnif) from
            query (spec := unifSpec) qUnif)
        pure resp

/-- Common Section 5.8 hybrid game skeleton: run the malicious prover and verifier under
`D2SQuery`, exposing only the chosen external challenge-oracle family and then projecting away the
auxiliary unit-sampling randomness. -/
def section58HybridGame
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (params :
      D2SQueryParamsWithOracle
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) challengeSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OptionT (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
      (StmtIn × StmtOut × pSpec.Messages × QueryLog (oSpec + challengeSpec)) := do
  let d2sOuterImpl :
      QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StateT (D2SQueryState (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))
      (QueryImpl.id oSpec)
      (d2sQueryImplCoreWithOracle
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) params)
  let proverComp :
      OptionT
        (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        ((StmtIn × pSpec.Messages) ×
          D2SQueryState (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :=
    (simulateQ d2sOuterImpl P).run default
  let ⟨proverOut?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle proverComp.run).run
  let ⟨⟨stmtIn, messages⟩, _⟩ ←
    match proverOut? with
    | some proverOut => pure proverOut
    | none => failure
  let verifierComp :
      OptionT
        (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        (Option StmtOut ×
          D2SQueryState (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :=
    (simulateQ d2sOuterImpl
      (V.duplexSpongeFiatShamir.run
        stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run default
  let ⟨verifierOut?, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp.run).run
  let ⟨stmtOut?, _⟩ ←
    match verifierOut? with
    | some verifierOut => pure verifierOut
    | none => failure
  let proveQueryLog :=
    projectD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    projectD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) verifyQueryLogRaw
  return ⟨stmtIn, ← stmtOut?.getM, messages, proveQueryLog ++ verifyQueryLog⟩

/-- Distribution of a Section 5.8 hybrid game after applying its line-4 trace map. -/
def section58HybridGameDist
    [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT σ ProbComp))
    (params :
      D2SQueryParamsWithOracle
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) challengeSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (traceMap :
      QueryLog (oSpec + challengeSpec) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) := do
  let hybridOutput ←
    (simulateQ impl
      ((section58HybridGame
        (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        params V P).run)).run' (← init)
  match hybridOutput with
  | none => return none
  | some ⟨stmtIn, stmtOut, messages, projectedTrace⟩ => do
      let outputFS? ←
        runSection58ProjectedTraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          traceMap projectedTrace
      match outputFS? with
      | none => return none
      | some fullTraceFS =>
          return some (stmtIn, stmtOut, messages, fullTraceFS)

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

-- /--
-- fucntion fn()
--   ---
--   ---
--   ---
--   ---
-- -/

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

/-- Left experiment of Lemma 5.1 after applying a monadic trace algorithm to DSFS logs. -/
def mappedDuplexSpongeFiatShamirGameDist
    [SampleableType U]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (traceMap :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec)) := do
  let outputDS ← duplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
  match outputDS with
  | none => return none
  | some ⟨stmtIn, stmtOut, messages, fullTraceDS⟩ => do
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          traceMap fullTraceDS
      match outputFS? with
      | none => return none
      | some fullTraceFS =>
          return some (stmtIn, stmtOut, messages, fullTraceFS)

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

/-- Fixed ambient shared-oracle package used by the paper's Section 5.8 experiments. -/
class Section58SharedOraclePackage where
  σShared : Type
  initShared : ProbComp σShared
  implShared : QueryImpl oSpec (StateT σShared ProbComp)

/-- Fixed permutation-sampler package used by the paper's `𝒟_𝔖(λ,n)` experiment. -/
class Section58PermutationPackage where
  σPerm : Type
  initPerm : ProbComp σPerm
  implPerm : QueryImpl (permutationOracle (CanonicalSpongeState U)) (StateT σPerm ProbComp)

/-- Minimal semantic law currently exposed for a Section 5.8 permutation package: answers in the
support of the forward and backward directions must remain mutually consistent across one-step
state transitions. This does not yet capture the full random-permutation law of `𝒟_𝔖(λ,n)`, but it
at least prevents treating an arbitrary pair of unrelated forward/backward samplers as the paper's
permutation oracle. -/
def Section58PermutationPackageLaw
    [permPkg : Section58PermutationPackage (U := U)] : Prop :=
  (∀ (σ : permPkg.σPerm) (stateIn stateOut : CanonicalSpongeState U) (σ' : permPkg.σPerm),
      (stateOut, σ') ∈ support ((permPkg.implPerm (.inl stateIn)).run σ) →
        stateIn ∈ Prod.fst '' support ((permPkg.implPerm (.inr stateOut)).run σ'))
    ∧
  (∀ (σ : permPkg.σPerm) (stateOut stateIn : CanonicalSpongeState U) (σ' : permPkg.σPerm),
      (stateIn, σ') ∈ support ((permPkg.implPerm (.inr stateOut)).run σ) →
        stateOut ∈ Prod.fst '' support ((permPkg.implPerm (.inl stateIn)).run σ'))

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
the ambient shared-oracle and permutation packages. -/
abbrev paperDSInit [sharedPkg : Section58SharedOraclePackage (oSpec := oSpec)]
    [permPkg : Section58PermutationPackage (U := U)] :
    ProbComp (Section58DSState
      (StmtIn := StmtIn) (U := U)
      sharedPkg.σShared permPkg.σPerm) :=
  section58CanonicalDSInit
    (StmtIn := StmtIn) (U := U)
    sharedPkg.initShared permPkg.initPerm

/-- Named DS-side implementation corresponding to the paper's fixed `𝒟_𝔖(λ,n)` experiment,
relative to the ambient shared-oracle and permutation packages. -/
abbrev paperDSImpl [DecidableEq StmtIn] [SampleableType U]
    [sharedPkg : Section58SharedOraclePackage (oSpec := oSpec)]
    [permPkg : Section58PermutationPackage (U := U)] :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (Section58DSState
        (StmtIn := StmtIn) (U := U)
        sharedPkg.σShared permPkg.σPerm) ProbComp) :=
  section58CanonicalDSImpl
    (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
    sharedPkg.implShared permPkg.implPerm

/-- Named basic-FS-side sampler corresponding to the paper's fixed `𝒟_IP(λ,n)` experiment,
relative to the ambient shared-oracle package. -/
abbrev paperIPInit [sharedPkg : Section58SharedOraclePackage (oSpec := oSpec)] :
    ProbComp (Section58FSState
      (StmtIn := StmtIn) (pSpec := pSpec) sharedPkg.σShared) :=
  section58CanonicalFSInit
    (StmtIn := StmtIn) (pSpec := pSpec)
    sharedPkg.initShared

/-- Named basic-FS-side implementation corresponding to the paper's fixed `𝒟_IP(λ,n)` experiment,
relative to the ambient shared-oracle package. -/
abbrev paperIPImpl [DecidableEq StmtIn] [SampleableType U]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [sharedPkg : Section58SharedOraclePackage (oSpec := oSpec)] :
    QueryImpl (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT (Section58FSState
        (StmtIn := StmtIn) (pSpec := pSpec) sharedPkg.σShared) ProbComp) :=
  section58CanonicalFSImpl
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    sharedPkg.implShared

/-- `Hyb₀`: left experiment in Section 5.8 (mapped DSFS experiment). -/
abbrev hyb0Dist
    [SampleableType U]
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (paperD2STrace :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :
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

/-- Surjectivity side condition for the verifier-message codec used in Section 5.8:
every decoded challenge must have at least one encoded preimage under `Deserialize`. This is the
formal hook needed to interpret the paper's `ψ⁻¹` sampler on verifier challenges.
-- TODO: use standard `surjective` definition instead
-/
def ChallengeDeserializeSurjective : Prop :=
  ∀ (i : pSpec.ChallengeIdx) (challenge : pSpec.Challenge i),
    ∃ encoded : Vector U (challengeSize (pSpec := pSpec) i),
      Deserialize.deserialize encoded = challenge

private noncomputable def deserializePreimageFinset
    {i : pSpec.ChallengeIdx}
    [Fintype U] [DecidableEq U]
    [Fintype (pSpec.Challenge i)] [DecidableEq (pSpec.Challenge i)]
    (challenge : pSpec.Challenge i) :
    Finset (Vector U (challengeSize (pSpec := pSpec) i)) := by
  classical
  let _ : Fintype (Vector U (challengeSize (pSpec := pSpec) i)) :=
    Fintype.ofEquiv (Fin (challengeSize (pSpec := pSpec) i) → U) Equiv.rootVectorEquivFin.symm
  exact (Finset.univ : Finset (Vector U (challengeSize (pSpec := pSpec) i))).filter fun encoded =>
    Deserialize.deserialize encoded = challenge

private noncomputable def uniformDeserializePreimage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (hSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
    {i : pSpec.ChallengeIdx}
    (challenge : pSpec.Challenge i) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Vector U (challengeSize (pSpec := pSpec) i)) := do
  have hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty := by
    rcases hSurj i challenge with ⟨encoded, hencoded⟩
    exact ⟨encoded, by simp [deserializePreimageFinset, hencoded]⟩
  let preimages := (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).toList
  have hpreimages_ne : preimages ≠ [] := by
    simpa [preimages] using hpreimages_nonempty.toList_ne_nil
  have hlen_pos : 0 < preimages.length := List.length_pos_iff_ne_nil.mpr hpreimages_ne
  let idxRaw ←
    (show OracleComp
        (D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (Fin ((preimages.length - 1) + 1)) from
      query
        (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (.inr (.inr (preimages.length - 1))))
  have hlen_eq : (preimages.length - 1) + 1 = preimages.length := Nat.sub_add_cancel
    (Nat.succ_le_of_lt hlen_pos)
  let idx : Fin preimages.length := ⟨idxRaw.1, by simpa [hlen_eq] using idxRaw.2⟩
  pure (preimages.get idx)
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
noncomputable def section58Hyb1Dist
    [SampleableType U]
    [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) := by
  let challengeSpec := section58EncodedChallengeOracle (U := U) StmtIn pSpec
  let _ : DecidableEq challengeSpec.Domain := by
    classical infer_instance
  let _ : ∀ q : challengeSpec.Domain, SampleableType (challengeSpec.Range q) := by
    intro q
    cases q with
    | mk i qKey =>
        change SampleableType (Vector U (challengeSize (pSpec := pSpec) i))
        infer_instance
  let params :=
    defaultD2SQueryParamsWithOracle
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 absorbedRatePrefix0 =>
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (Vector U (challengeSize (pSpec := pSpec) roundIdx)) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl ⟨roundIdx, (stmt0, absorbedRatePrefix0)⟩)))
  exact
    section58HybridGameDist
      (T_H := Section52.ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (T_P := Section52.ListBacked.ListTraceTable
        (CanonicalSpongeState U) (CanonicalSpongeState U))
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := section58ChallengeInit
        (challengeSpec := challengeSpec)
        (sharedInit := Section58SharedOraclePackage.initShared
          (oSpec := oSpec)))
      (impl := section58ChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec)
        (sharedImpl := Section58SharedOraclePackage.implShared
          (oSpec := oSpec)))
      params V maliciousProver
      (section58Hyb1Line4Trace
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Canonical `Hyb₂` experiment from Section 5.8. -/
noncomputable def section58Hyb2Dist
    [Fintype U] [SampleableType U]
    [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    (hChallengeSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) := by
  let challengeSpec := section58DecodedChallengeOracle (U := U) StmtIn pSpec
  let _ : DecidableEq challengeSpec.Domain := by
    classical infer_instance
  let _ : ∀ q : challengeSpec.Domain, SampleableType (challengeSpec.Range q) := by
    intro q
    cases q with
    | mk i qKey =>
        change SampleableType (pSpec.Challenge i)
        infer_instance
  let params :=
    defaultD2SQueryParamsWithOracle
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 absorbedRatePrefix0 => do
        let challenge ←
          OptionT.lift <|
            (show OracleComp
                (D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (pSpec.Challenge roundIdx) from
              query
                (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (.inl ⟨roundIdx, (stmt0, absorbedRatePrefix0)⟩))
        OptionT.lift <|
          uniformDeserializePreimage
            (pSpec := pSpec) (U := U)
            (challengeSpec := challengeSpec) hChallengeSurj challenge)
  exact
    section58HybridGameDist
      (T_H := Section52.ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (T_P := Section52.ListBacked.ListTraceTable
        (CanonicalSpongeState U) (CanonicalSpongeState U))
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := section58ChallengeInit
        (challengeSpec := challengeSpec)
        (sharedInit := Section58SharedOraclePackage.initShared
          (oSpec := oSpec)))
      (impl := section58ChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec)
        (sharedImpl := Section58SharedOraclePackage.implShared
          (oSpec := oSpec)))
      params V maliciousProver
      (section58Hyb2Line4Trace
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Canonical `Hyb₃` experiment from Section 5.8. -/
noncomputable def section58Hyb3Dist
    [Fintype U] [SampleableType U]
    [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    (hChallengeSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) := by
  let challengeSpec := fsChallengeOracle StmtIn pSpec
  let _ : DecidableEq challengeSpec.Domain := by
    classical infer_instance
  let _ : ∀ q : challengeSpec.Domain, SampleableType (challengeSpec.Range q) := by
    intro q
    cases q with
    | mk i qKey =>
        change SampleableType (pSpec.Challenge i)
        infer_instance
  let params :=
    defaultD2SQueryParamsWithOracle
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 absorbedRatePrefix0 => do
        let messagesUpTo ←
          match section58AbsorbedPrefixMessagesUpTo?
              (pSpec := pSpec) (U := U) roundIdx absorbedRatePrefix0 with
          | some messagesUpTo => pure messagesUpTo
          | none => failure
        let challenge ←
          OptionT.lift <|
            (show OracleComp
                (D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (pSpec.Challenge roundIdx) from
              query
                (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (.inl ⟨roundIdx, (stmt0, messagesUpTo)⟩))
        OptionT.lift <|
          uniformDeserializePreimage
            (pSpec := pSpec) (U := U)
            (challengeSpec := challengeSpec) hChallengeSurj challenge)
  exact
    section58HybridGameDist
      (T_H := Section52.ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (T_P := Section52.ListBacked.ListTraceTable
        (CanonicalSpongeState U) (CanonicalSpongeState U))
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := section58ChallengeInit
        (challengeSpec := challengeSpec)
        (sharedInit := Section58SharedOraclePackage.initShared
          (oSpec := oSpec)))
      (impl := section58ChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec)
        (sharedImpl := Section58SharedOraclePackage.implShared
          (oSpec := oSpec)))
      params V maliciousProver
      (section58Hyb3Line4Trace
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))


/-- Claim 5.21 target proposition on the canonical `Hyb₀`/`Hyb₁` experiments from Section 5.8. -/
def claim_5_21
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
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
        V maliciousProver
        (paperD2STraceSingle
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (section58Hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V maliciousProver)
    ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries

/-- Claim 5.22 target proposition on the canonical `Hyb₁`/`Hyb₂` experiments from Section 5.8. -/
def claim_5_22
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    (securityParam instanceBound : ℕ)
    (hChallengeSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
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
        (pSpec := pSpec) (U := U) V maliciousProver)
      (section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver)
    ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec

/-- Claim 5.23 target proposition on the canonical `Hyb₂`/`Hyb₃` experiments from Section 5.8. -/
def claim_5_23
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    (securityParam instanceBound : ℕ)
    (hChallengeSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Prop :=
  let _ := securityParam
  let _ := instanceBound
  tvDist
    (section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver)
    (section58Hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver) = 0

/-- Claim 5.24 target proposition on the canonical `Hyb₃`/`Hyb₄` experiments from Section 5.8. -/
def claim_5_24
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    (securityParam instanceBound : ℕ)
    (hChallengeSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
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
        (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver)
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
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    (securityParam instanceBound : ℕ)
    (hPermPackageLaw : Section58PermutationPackageLaw (U := U))
    (hChallengeSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
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
      securityParam instanceBound hChallengeSurj V maliciousProver tₕ tₚ tₚᵢ εcodec)
    (h23 : claim_5_23 (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      securityParam instanceBound hChallengeSurj V maliciousProver)
    (h24 : claim_5_24 (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      securityParam instanceBound hChallengeSurj V maliciousProver d2sAlgo tₕ tₚ tₚᵢ)
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
        V maliciousProver
        (paperD2STraceSingle
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
        (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver d2sAlgo)
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ) := by
  let _ := hPermPackageLaw
  have h23' :
      tvDist
        (section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver)
        (section58Hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver)
        ≤ (0 : ℝ) := by
    rw [h23]
  have hChain :=
    tvDist_hybridChain4
      (H₀ := hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver
        (paperD2STraceSingle
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (H₁ := section58Hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V maliciousProver)
      (H₂ := section58Hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver)
      (H₃ := section58Hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) hChallengeSurj V maliciousProver)
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
the stated query bound. The auxiliary hybrid trace algorithms used in the Section 5.8 proof chain
remain an internal proof obligation when proving this theorem from
`lemma_5_1_dist_from_claims`.

TODO: upgrade the malicious-prover hypothesis from `IsTotalQueryBound (tₕ + tₚ + tₚᵢ)` to the
same per-index `(tₕ, tₚ, tₚᵢ)` query-bound surface used by `BadEvents.lemma_5_8`, so the theorem
matches the paper's Section 5 statement more closely.

TODO: reintroduce an explicit semantic assumption capturing that `(permInit, permImpl)` really
samples the paper's random permutation experiment `𝒟_𝔖(λ,n)`. The old package-level law was too
hidden for the public theorem surface, but the theorem should eventually state this requirement
directly rather than leaving the permutation sampler unconstrained.
-/
theorem lemma_5_1
    [Fintype U] [SampleableType U]
    [DecidableEq U]
    [DecidableEq StmtIn]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    {σShared σPerm : Type}
    (sharedInit : ProbComp σShared)
    (sharedImpl : QueryImpl oSpec (StateT σShared ProbComp))
    (permInit : ProbComp σPerm)
    (permImpl : QueryImpl
      (permutationOracle (CanonicalSpongeState U)) (StateT σPerm ProbComp))
      -- TODO: check p⁻¹ query impl
    (securityParam instanceBound : ℕ)
    (hChallengeSurj : ChallengeDeserializeSurjective (pSpec := pSpec) (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : CodecBias (pSpec := pSpec))
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge) :
    ∃ (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (paperD2STrace :
        QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
          OptionT (OracleComp (Unit →ₒ U))
            (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))),
      ∀ (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (StmtIn × pSpec.Messages)),
          -- TODO: fix query bound to each oracles `(tₕ, tₚ, tₚᵢ)`, via  `IsIndexQueryBound`
      OracleComp.IsTotalQueryBound maliciousProver (tₕ + tₚ + tₚᵢ) →
      tvDist -- 1/2 ∑ |p(i) - q(i)|
         -- hybrid 0
        (mappedDuplexSpongeFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          (section58CanonicalDSInit
            (StmtIn := StmtIn) (U := U) sharedInit permInit)
          (section58CanonicalDSImpl
            (oSpec := oSpec) (StmtIn := StmtIn) (U := U) sharedImpl permImpl)
          V maliciousProver paperD2STrace)
        -- hybrid 4
        (basicFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec)
          (section58CanonicalFSInit
            (StmtIn := StmtIn) (pSpec := pSpec) sharedInit)
          (section58CanonicalFSImpl
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) sharedImpl)
          V (d2sAlgo maliciousProver))
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)
      ∧ OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ) := by
  let _ := securityParam
  let _ := instanceBound
  refine ⟨?_, ?_, ?_⟩
  · exact duplexSpongeToBasicFSAlgo
      (T_H := Section52.ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (T_P := Section52.ListBacked.ListTraceTable
        (CanonicalSpongeState U) (CanonicalSpongeState U))
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  · exact paperD2STraceSingle
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  · intro maliciousProver hMaliciousBound
    let _ := hTp
    let _ := hMaliciousBound
    sorry

end KeyLemma

end DuplexSpongeFS
