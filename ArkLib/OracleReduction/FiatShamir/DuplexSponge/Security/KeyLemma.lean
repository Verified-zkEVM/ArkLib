/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Lemma 5.1 of the Chiesa-Orru paper

This file provides the Section 5 key-lemma interface:
- the DSFS and basic-FS game experiments,
- paper-facing abstractions for `D2SAlgo` and `D2STrace`, and
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

/-- The D2S trace transform from Section 5.5, mapping DSFS logs to basic-FS logs. -/
structure D2STrace where
  run :
    QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
      Option
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))

/-- Apply the trace transform to the DSFS game output so both experiments live in the same output
space. -/
def D2STrace.mapOutput (traceTransform : D2STrace (oSpec := oSpec) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U)) :
    DuplexSpongeFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) →
      Option
        (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec)) :=
  fun output =>
    let ⟨stmtIn, stmtOut, messages, proveQueryLogDS, verifyQueryLogDS⟩ := output
    match traceTransform.run proveQueryLogDS verifyQueryLogDS with
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

/-- Left experiment of Lemma 5.1 after applying `D2STrace` to DSFS logs. -/
def mappedDuplexSpongeFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (traceTransform : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec)) := do
  let outputDS ← duplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
  match outputDS with
  | none => return none
  | some output =>
      return traceTransform.mapOutput output

end SecurityGames

section KeyLemma

open scoped NNReal

/-- `θStar` in the paper, equal to `t_p`, the forward-permutation query budget of the malicious
prover. -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-- `ηStar` in Equation (5) of Lemma 5.1. -/
noncomputable def ηStar (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ : ℕ) (L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ :=
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

/-- Intermediate hybrids from Section 5.8 (`Hyb₁`, `Hyb₂`, `Hyb₃`). -/
structure Lemma51Hybrids where
  hyb1 : ProbComp (Option <| BasicFiatShamirGameOutput
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec))
  hyb2 : ProbComp (Option <| BasicFiatShamirGameOutput
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec))
  hyb3 : ProbComp (Option <| BasicFiatShamirGameOutput
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec))

/-- `Hyb₀`: left experiment in Section 5.8 (mapped DSFS experiment). -/
abbrev hyb0Dist
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    initDS implDS V maliciousProver d2sTrace

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

/-- Concrete setup for `Hyb₁` (Section 5.8). -/
structure Hyb1Setup where
  σ : Type
  init : ProbComp σ
  impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp)
  maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)
  traceTransform : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- Concrete setup for `Hyb₂` (Section 5.8). -/
structure Hyb2Setup where
  σ : Type
  init : ProbComp σ
  impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp)
  maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)
  traceTransform : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- Concrete setup for `Hyb₃` (Section 5.8). -/
structure Hyb3Setup where
  σ : Type
  init : ProbComp σ
  impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp)
  maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)
  traceTransform : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- `Hyb₁` in Section 5.8. -/
abbrev hyb1Dist
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (setup1 : Hyb1Setup (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup1.init setup1.impl V setup1.maliciousProver setup1.traceTransform

/-- `Hyb₂` in Section 5.8. -/
abbrev hyb2Dist
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (setup2 : Hyb2Setup (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup2.init setup2.impl V setup2.maliciousProver setup2.traceTransform

/-- `Hyb₃` in Section 5.8. -/
abbrev hyb3Dist
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (setup3 : Hyb3Setup (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup3.init setup3.impl V setup3.maliciousProver setup3.traceTransform

/-- Claim 5.21 bound (`Hyb₀` vs `Hyb₁`). -/
noncomputable def claim5_21Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- Claim 5.22 bound (`Hyb₁` vs `Hyb₂`). -/
noncomputable def claim5_22Bound
    (tₕ tₚ tₚᵢ : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ :=
  (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
    + ∑ i, (εcodec i : ℝ)

/-- Claim 5.24 bound (`Hyb₃` vs `Hyb₄`). -/
noncomputable def claim5_24Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let Lr : ℝ := L
  let cardPow : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  (7 * Lr * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + Lr + 2 * (tₚᵢ : ℝ))) / (2 * cardPow)
    - (5 * (Lr + 1)) / cardPow

/-- Concrete Section 5.8 experiment package with fixed `Hyb₀`..`Hyb₄` ingredients. -/
structure Section58ExactSetup where
  V : Verifier oSpec StmtIn StmtOut pSpec
  maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)
  d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  d2sTrace0 : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  d2sTrace1 : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  d2sTrace2 : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  d2sTrace3 : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  σDS : Type
  initDS : ProbComp σDS
  implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp)
  σFS : Type
  initFS : ProbComp σFS
  implFS : QueryImpl
    (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (StateT σFS ProbComp)

/-- Concrete `Hyb₀` from a fixed Section 5.8 setup. -/
abbrev Section58ExactSetup.hyb0
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup.initDS setup.implDS setup.V setup.maliciousProver setup.d2sTrace0

/-- Concrete `Hyb₁` from a fixed Section 5.8 setup. -/
abbrev Section58ExactSetup.hyb1
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup.initDS setup.implDS setup.V setup.maliciousProver setup.d2sTrace1

/-- Concrete `Hyb₂` from a fixed Section 5.8 setup. -/
abbrev Section58ExactSetup.hyb2
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup.initDS setup.implDS setup.V setup.maliciousProver setup.d2sTrace2

/-- Concrete `Hyb₃` from a fixed Section 5.8 setup. -/
abbrev Section58ExactSetup.hyb3
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup.initDS setup.implDS setup.V setup.maliciousProver setup.d2sTrace3

/-- Concrete `Hyb₄` from a fixed Section 5.8 setup. -/
abbrev Section58ExactSetup.hyb4
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)) :=
  hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    setup.initFS setup.implFS setup.V setup.maliciousProver setup.d2sAlgo

/-- Claim 5.21 on fully concrete `Hyb₀`/`Hyb₁` experiments. -/
theorem claim_5_21_exact
    [Fintype U]
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist setup.hyb0 setup.hyb1
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  sorry

/-- Claim 5.22 on fully concrete `Hyb₁`/`Hyb₂` experiments. -/
theorem claim_5_22_exact
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0) :
    tvDist setup.hyb1 setup.hyb2
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec := by
  sorry

/-- Claim 5.23 on fully concrete `Hyb₂`/`Hyb₃` experiments. -/
theorem claim_5_23_exact
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)) :
    tvDist setup.hyb2 setup.hyb3 = 0 := by
  sorry

/-- Claim 5.24 on fully concrete `Hyb₃`/`Hyb₄` experiments. -/
theorem claim_5_24_exact
    [Fintype U]
    (setup : Section58ExactSetup (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist setup.hyb3 setup.hyb4
      ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  sorry

/-- Claim 5.21: statistical distance bound between `Hyb₀` and `Hyb₁`. -/
theorem claim_5_21
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec))
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
      hybrids.hyb1
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  sorry

/-- Claim 5.22: statistical distance bound between `Hyb₁` and `Hyb₂`. -/
theorem claim_5_22
    (hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0) :
    tvDist hybrids.hyb1 hybrids.hyb2 ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec := by
  sorry

/-- Claim 5.23: `Hyb₂` and `Hyb₃` are identically distributed. -/
theorem claim_5_23
    (hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec)) :
    tvDist hybrids.hyb2 hybrids.hyb3 = 0 := by
  sorry

/-- Claim 5.24: statistical distance bound between `Hyb₃` and `Hyb₄`. -/
theorem claim_5_24
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σFS : Type}
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec))
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist hybrids.hyb3
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
      ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  sorry

/-- Claim 5.21 in concrete-hybrid form (`Hyb₀` vs explicit `Hyb₁`). -/
theorem claim_5_21_concrete
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (setup1 : Hyb1Setup (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
      (hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup1)
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  let setup2 : Hyb2Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
    { σ := setup1.σ
      init := setup1.init
      impl := setup1.impl
      maliciousProver := setup1.maliciousProver
      traceTransform := setup1.traceTransform }
  let setup3 : Hyb3Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
    { σ := setup1.σ
      init := setup1.init
      impl := setup1.impl
      maliciousProver := setup1.maliciousProver
      traceTransform := setup1.traceTransform }
  let hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) :=
    { hyb1 := hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup1
      hyb2 := hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup2
      hyb3 := hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup3 }
  have h :=
    claim_5_21
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      V maliciousProver d2sTrace initDS implDS hybrids tₕ tₚ tₚᵢ
  change
    tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
      hybrids.hyb1
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
  exact h

/-- Claim 5.22 in concrete-hybrid form (explicit `Hyb₁` vs explicit `Hyb₂`). -/
theorem claim_5_22_concrete
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (setup1 : Hyb1Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (setup2 : Hyb2Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0) :
    tvDist
      (hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup1)
      (hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup2)
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec := by
  let setup3 : Hyb3Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
    { σ := setup2.σ
      init := setup2.init
      impl := setup2.impl
      maliciousProver := setup2.maliciousProver
      traceTransform := setup2.traceTransform }
  let hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) :=
    { hyb1 := hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup1
      hyb2 := hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup2
      hyb3 := hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup3 }
  have h :=
    claim_5_22
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec)
      hybrids tₕ tₚ tₚᵢ εcodec
  change tvDist hybrids.hyb1 hybrids.hyb2 ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec
  exact h

/-- Claim 5.23 in concrete-hybrid form (explicit `Hyb₂` vs explicit `Hyb₃`). -/
theorem claim_5_23_concrete
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (setup2 : Hyb2Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (setup3 : Hyb3Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    tvDist
      (hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup2)
      (hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup3)
      = 0 := by
  let setup1 : Hyb1Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
    { σ := setup2.σ
      init := setup2.init
      impl := setup2.impl
      maliciousProver := setup2.maliciousProver
      traceTransform := setup2.traceTransform }
  let hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) :=
    { hyb1 := hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup1
      hyb2 := hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup2
      hyb3 := hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup3 }
  have h :=
    claim_5_23
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec)
      hybrids
  change tvDist hybrids.hyb2 hybrids.hyb3 = 0
  exact h

/-- Claim 5.24 in concrete-hybrid form (explicit `Hyb₃` vs `Hyb₄`). -/
theorem claim_5_24_concrete
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (setup3 : Hyb3Setup (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U))
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σFS : Type}
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist
      (hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup3)
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
      ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  let setup1 : Hyb1Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
    { σ := setup3.σ
      init := setup3.init
      impl := setup3.impl
      maliciousProver := setup3.maliciousProver
      traceTransform := setup3.traceTransform }
  let setup2 : Hyb2Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
    { σ := setup3.σ
      init := setup3.init
      impl := setup3.impl
      maliciousProver := setup3.maliciousProver
      traceTransform := setup3.traceTransform }
  let hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) :=
    { hyb1 := hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup1
      hyb2 := hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup2
      hyb3 := hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup3 }
  have h :=
    claim_5_24
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      V maliciousProver d2sAlgo initFS implFS hybrids tₕ tₚ tₚᵢ
  change
    tvDist hybrids.hyb3
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
      ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
  exact h

/--
Lemma 5.1 distance component from Claims 5.21-5.24, as a statement-only bridge.

This keeps the hybrid decomposition explicit and postpones the arithmetic reconciliation with
`ηStar` to dedicated proof steps.
-/
theorem lemma_5_1_dist_from_claims
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σDS σFS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0)
    (h21 :
      tvDist
        (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
        hybrids.hyb1
        ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
    (h22 :
      tvDist hybrids.hyb1 hybrids.hyb2
        ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec)
    (h23 : tvDist hybrids.hyb2 hybrids.hyb3 = 0)
    (h24 :
      tvDist hybrids.hyb3
        (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
        ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
    (hBound :
      claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        + claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec
        + 0
        + claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)) :
    tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
      ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ) := by
  have h23' : tvDist hybrids.hyb2 hybrids.hyb3 ≤ (0 : ℝ) := by
    simpa [h23]
  have hChain :=
    tvDist_hybridChain4
      (H₀ := hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
      (H₁ := hybrids.hyb1)
      (H₂ := hybrids.hyb2)
      (H₃ := hybrids.hyb3)
      (H₄ := hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
      (e₀₁ := claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
      (e₁₂ := claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec)
      (e₂₃ := 0)
      (e₃₄ := claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
      h21 h22 h23' h24
  linarith

/--
Lemma 5.1 distance component from concrete Section 5.8 hybrid definitions.

This is the paper-facing concrete counterpart of `lemma_5_1_dist_from_claims` where `Hyb₁`,`Hyb₂`,
and `Hyb₃` are explicit distributions, not abstract fields.
-/
theorem lemma_5_1_dist_from_claims_concrete
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σDS σFS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (setup1 : Hyb1Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (setup2 : Hyb2Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (setup3 : Hyb3Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0)
    (h21 :
      tvDist
        (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
        (hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup1)
        ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
    (h22 :
      tvDist
        (hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup1)
        (hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup2)
        ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec)
    (h23 :
      tvDist
        (hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup2)
        (hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup3)
        = 0)
    (h24 :
      tvDist
        (hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup3)
        (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
        ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
    (hBound :
      claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        + claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec
        + 0
        + claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)) :
    tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
      ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ) := by
  let hybrids : Lemma51Hybrids (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) :=
    { hyb1 := hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup1
      hyb2 := hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup2
      hyb3 := hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) V setup3 }
  simpa [hybrids] using
    (lemma_5_1_dist_from_claims (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      V maliciousProver d2sAlgo d2sTrace
      initDS implDS initFS implFS hybrids
      tₕ tₚ tₚᵢ εcodec h21 h22 h23 h24 hBound)

/--
Lemma 5.1 (paper-facing interface).

This theorem packages the two obligations that Section 6 needs from Section 5:
1. statistical closeness of the transformed DSFS experiment and the basic-FS experiment;
2. query bound of the transformed prover `D2SAlgo`.

The full proof that discharges `hDist` and `hQueryBound` from the Section 5 hybrid/abort/bad-event
analysis is staged across the remaining Section 5 files.
-/
lemma duplexSpongeToFSGameStatDist
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σDS σFS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge)
    (hDist :
      tvDist
        (mappedDuplexSpongeFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          initDS implDS V maliciousProver d2sTrace)
        (basicFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec)
          initFS implFS V (d2sAlgo maliciousProver))
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ))
    (hQueryBound :
      OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ)) :
    tvDist
      (mappedDuplexSpongeFiatShamirGameDist
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        initDS implDS V maliciousProver d2sTrace)
      (basicFiatShamirGameDist
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec)
        initFS implFS V (d2sAlgo maliciousProver))
      ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)
    ∧ OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ)
    ∧ tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge := by
  exact ⟨hDist, hQueryBound, hTp⟩

/--
Lemma 5.1 in existential form (paper-facing statement):
there exist `D2SAlgo` and `D2STrace` such that the transformed DSFS experiment and the basic-FS
experiment are `ηStar`-close, and the transformed prover respects the `θStar` query bound.
-/
theorem lemma_5_1
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    {σDS σFS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge)
    (hMaliciousQueryBound :
      OracleComp.IsTotalQueryBound maliciousProver (tₕ + tₚ + tₚᵢ)) :
    ∃ (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
      tvDist
        (mappedDuplexSpongeFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          initDS implDS V maliciousProver d2sTrace)
        (basicFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec)
          initFS implFS V (d2sAlgo maliciousProver))
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)
      ∧ OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ)
      ∧ tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge := by
  sorry

/--
Lemma 5.1 interface derived from explicit Claim 5.21-5.24 assumptions (no direct `hDist` input).
-/
lemma duplexSpongeToFSGameStatDist_from_claims
    [Fintype U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (d2sAlgo : D2SAlgo (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (d2sTrace : D2STrace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {σDS σFS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec + FSPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (StateT σFS ProbComp))
    (setup1 : Hyb1Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (setup2 : Hyb2Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (setup3 : Hyb3Setup (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (εcodec : pSpec.ChallengeIdx → ℝ≥0)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge)
    (h21 :
      tvDist
        (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) initDS implDS V maliciousProver d2sTrace)
        (hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup1)
        ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
    (h22 :
      tvDist
        (hyb1Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup1)
        (hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup2)
        ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec)
    (h23 :
      tvDist
        (hyb2Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup2)
        (hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup3)
        = 0)
    (h24 :
      tvDist
        (hyb3Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) V setup3)
        (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) initFS implFS V maliciousProver d2sAlgo)
        ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
    (hBound :
      claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        + claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec
        + 0
        + claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ))
    (hQueryBound :
      OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ)) :
    tvDist
      (mappedDuplexSpongeFiatShamirGameDist
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        initDS implDS V maliciousProver d2sTrace)
      (basicFiatShamirGameDist
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec)
        initFS implFS V (d2sAlgo maliciousProver))
      ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ)
    ∧ OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ)
    ∧ tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge := by
  have hDist :
      tvDist
        (mappedDuplexSpongeFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          initDS implDS V maliciousProver d2sTrace)
        (basicFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec)
          initFS implFS V (d2sAlgo maliciousProver))
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries εcodec : ℝ) := by
    simpa using
      (lemma_5_1_dist_from_claims_concrete (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        V maliciousProver d2sAlgo d2sTrace
        initDS implDS initFS implFS setup1 setup2 setup3
        tₕ tₚ tₚᵢ εcodec h21 h22 h23 h24 hBound)
  exact ⟨hDist, hQueryBound, hTp⟩

end KeyLemma

end DuplexSpongeFS
