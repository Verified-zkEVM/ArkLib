/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import ArkLib.OracleReduction.FiatShamir.SingleSalt
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Lemma 5.1 of the Chiesa-Orrù paper

This file provides the Section 5 key-lemma interface:
- the DSFS and basic-FS game experiments,
- paper-facing abstractions for `D2SAlgo` and the Section 5.8 trace algorithms, and
- a statistical-distance theorem surface with the query-bound side condition.

`StmtIn` is the Lean stand-in for the paper's hash-input space `{0,1}^{≤n}`. The paper's
instance-size bound is fixed by choosing this type, while `n` in this file is the protocol round
count from `pSpec : ProtocolSpec n`. Likewise, `codec.decodingBias` abstracts the paper's
`ε_cdc,i(λ,n)` values for the fixed ambient parameter instantiation.

The full hybrid proof from Section 5.8 is still staged across the other Section 5 files.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  -- Paper-facing codec (CO25 Def 4.1) — supplies sizes + Serialize/Deserialize via projections
  {codec : Codec pSpec U}
  {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

instance instSampleableSaltedFSChallengeRange [∀ i, SampleableType (pSpec.Challenge i)] :
    ∀ q : (fsChallengeOracle (Vector U δ × StmtIn) pSpec).Domain,
      SampleableType ((fsChallengeOracle (Vector U δ × StmtIn) pSpec).Range q) := by
  intro q
  cases q with
  | mk i _ =>
      change SampleableType (pSpec.Challenge i)
      infer_instance

section SecurityGames

/-- Lift salted basic-FS verifier queries into the paper `f_i` oracle plus D2S auxiliary
sampling oracles used by `D2SAlgo^f`. -/
private def liftFSSaltedQueriesToD2SChallengePlusUnit :
    QueryImpl (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)
      (OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :=
  fun q =>
    match q with
    | .inl qShared =>
        query
          (spec := oSpec +
            D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
          (Sum.inl qShared)
    | .inr qFS =>
        query
          (spec := oSpec +
            D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
          (Sum.inr (Sum.inl qFS))

private def projectPaperIPPlusUnitQueryLog
    (log : QueryLog (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :
    QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr (.inl q), r⟩ => some ⟨.inr q, r⟩
    | ⟨.inr (.inr _), _⟩ => none

/-- CO25 Theorem 5.1. Output type for the salted basic Fiat-Shamir game (`Hyb_4`):
statement-in, statement-out, salted proof (`(τ, messages)`), and combined query log over
the salted `fsChallengeOracle (Vector U δ × StmtIn) pSpec`. -/
abbrev BasicFiatShamirGameOutput :=
  StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
    QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)

/-- CO25 Theorem 5.1. Output type for the duplex-sponge Fiat-Shamir game (`Hyb_0` left-hand
experiment): statement-in, statement-out, salted proof, and combined query log over
`duplexSpongeChallengeOracle`. -/
abbrev DuplexSpongeFiatShamirGameOutput :=
  StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
    QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)

/-- CO25 Theorem 5.1. Right-hand game for Lemma 5.1: `D2SAlgo^f(𝒫̃)` produces a salted
basic-FS proof, and the standard verifier `𝒱_std^f` checks it under oracle family
`𝒟_IP(λ,n)`. -/
def basicFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
  (P : OracleComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
      (Option (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))) :
    OptionT (OracleComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec)))
      (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  let ⟨stmtAndProof?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtIn, proof⟩ ←
    match stmtAndProof? with
    | some stmtAndProof => pure stmtAndProof
    | none => failure
  let verifierComp :
      OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
        (Option StmtOut) :=
    (do
      let messages : pSpec.Messages := proof.2
      let transcript ← OptionT.lift <|
        simulateQ
          (liftFSSaltedQueriesToD2SChallengePlusUnit
            (δ := δ) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (messages.deriveTranscriptFS
            (oSpec := oSpec) (StmtIn := Vector U δ × StmtIn) (proof.1, stmtIn))
      let v ← OptionT.lift <| liftComp ((V.verify stmtIn transcript).run) _
      v.getM).run
  let ⟨stmtOut, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp).run
  let proveQueryLog :=
    projectPaperIPPlusUnitQueryLog
      (oSpec := oSpec) (U := U)
      proveQueryLogRaw
  let verifyQueryLog :=
    projectPaperIPPlusUnitQueryLog
      (oSpec := oSpec) (U := U)
      verifyQueryLogRaw
  return ⟨stmtIn, ← stmtOut.getM, proof, proveQueryLog ++ verifyQueryLog⟩

/-- CO25 Theorem 5.1. Left-hand game for Lemma 5.1: the duplex-sponge Fiat-Shamir transform under
DS oracles `h, p, p⁻¹` sampled from `𝒟_𝔖(λ,n)`. This is `Hyb_0`, before the Section 5.8
hybrid rewrite through `D2SQuery`. -/
def duplexSpongeFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (DuplexSpongeFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  let ⟨⟨stmtIn, proof⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle
      ((V.duplexSpongeFiatShamirSalted δ).run
        stmtIn (fun i => match i with | ⟨0, _⟩ => proof))).run
  return ⟨stmtIn, ← stmtOut.getM, proof, proveQueryLog ++ verifyQueryLog⟩

/-- CO25 §5.4. D2SAlgo prover transform: lifts a duplex-sponge prover into a basic-FS prover.
Eq. (16): `D2SAlgo^f(𝒫̃) = 𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}`. -/
abbrev D2SAlgo :=
  OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) →
    OracleComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
      (Option (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))

/-- CO25 §5.8. Execute a Section 5.8 line-4 trace map (e.g. D2STrace = `(φ⁻¹, ψ) ∘ StdTrace`)
inside `ProbComp` by interpreting the auxiliary unit-sampling oracle uniformly. -/
def runSection58TraceMap
    [SampleableType U]
    (traceMap :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)))
    (fullTrace : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp
      (Option (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

/-- CO25 §5.8. Project out the auxiliary unit-sampling queries from logs over
`oSpec + (challengeSpec + Unit →ₒ U)`, retaining only shared and challenge entries. -/
def projectD2SChallengePlusUnitQueryLog
    {κ : Type} {challengeSpec : OracleSpec κ}
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :
    QueryLog (oSpec + challengeSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr (.inl q), r⟩ => some ⟨.inr q, r⟩
    | ⟨.inr (.inr _), _⟩ => none

/-- CO25 §5.8. Execute a Section 5.8 line-4 trace map on a projected hybrid trace (after removing
auxiliary unit-sampling entries), interpreting remaining randomness uniformly. -/
def runSection58ProjectedTraceMap
    [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (traceMap :
      QueryLog (oSpec + challengeSpec) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)))
    (fullTrace : QueryLog (oSpec + challengeSpec)) :
    ProbComp
      (Option (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

/-- CO25 §5.8. Shared-oracle state paired with a lazy random-function cache for an explicit hybrid
challenge-oracle family.  Used in `Hyb_1` (oracles `g_i ← 𝒟_Σ`), `Hyb_2` (oracles `e_i`),
and `Hyb_3` (oracles `f_i ← 𝒟_IP`). -/
abbrev Section58ChallengeState
    {κ : Type}
    (challengeSpec : OracleSpec κ)
    (σShared : Type) :=
  σShared × challengeSpec.QueryCache

/-- CO25 §5.8. Canonical initializer for a shared oracle plus a lazy random-function hybrid
challenge family: run `sharedInit` and start with an empty challenge cache. -/
def section58ChallengeInit
    {κ : Type} {challengeSpec : OracleSpec κ}
    {σShared : Type}
    (sharedInit : ProbComp σShared) :
    ProbComp (Section58ChallengeState challengeSpec σShared) := do
  let sharedState ← sharedInit
  pure (sharedState, ∅)

/-- CO25 §5.8. Canonical query handler for a shared oracle plus a lazy random-function hybrid
challenge family, augmented with the auxiliary unit-sampling oracle used by `D2SQuery`.
Shared queries → `sharedImpl`; challenge queries → lazy random oracle; unit queries →
`d2sUnitSampleImpl`. -/
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

/-- CO25 §5.8. Common hybrid game skeleton (Figure 4 lines 2–3): run `𝒫̃^{D2SQuery^g}` and
`𝒱^{D2SQuery^g}` exposing only the chosen external challenge-oracle family, then project away
the auxiliary unit-sampling randomness.  Instantiated at `section58EncodedChallengeOracle`
for `Hyb_1`, `section58DecodedChallengeOracle` for `Hyb_2`, and `fsChallengeOracle` for
`Hyb_3`. -/
def section58HybridGame
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (params :
      D2SQueryParamsWithOracle
        (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
        challengeSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    OptionT (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
      (StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
        QueryLog (oSpec + challengeSpec)) := do
  let d2sOuterImpl :
      QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))
      (QueryImpl.id oSpec)
      (d2sQueryImplCoreWithOracle
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
        (challengeSpec := challengeSpec) params)
  let proverComp :
      OptionT
        (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        ((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
    (simulateQ d2sOuterImpl P).run default
  let ⟨proverOut?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle proverComp.run).run
  let ⟨⟨stmtIn, proof⟩, _⟩ ←
    match proverOut? with
    | some proverOut => pure proverOut
    | none => failure
  let verifierComp :
      OptionT
        (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        (Option StmtOut ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
    (simulateQ d2sOuterImpl
      ((V.duplexSpongeFiatShamirSalted δ).run
        stmtIn (fun i => match i with | ⟨0, _⟩ => proof))).run default
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
  return ⟨stmtIn, ← stmtOut?.getM, proof, proveQueryLog ++ verifyQueryLog⟩

/-- CO25 §5.8. Distribution of a Section 5.8 hybrid game after applying its line-4 trace map
(Figure 4 line 4: `tr := (φ⁻¹,ψ)(tr_𝒫̃ ‖ tr_𝒱)` or `φ⁻¹(…)` or identity).  Collapses the
hybrid game output to `BasicFiatShamirGameOutput`, enabling the TV-distance chain
of Claims 5.21–5.24. -/
def section58HybridGameDist
    [SampleableType U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT σ ProbComp))
    (params :
      D2SQueryParamsWithOracle
        (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
        challengeSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (traceMap :
      QueryLog (oSpec + challengeSpec) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) := do
  let hybridOutput ←
    (simulateQ impl
      ((section58HybridGame
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec)
        params V P).run)).run' (← init)
  match hybridOutput with
  | none => return none
  | some ⟨stmtIn, stmtOut, proof, projectedTrace⟩ => do
      let outputFS? ←
        runSection58ProjectedTraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          traceMap projectedTrace
      match outputFS? with
      | none => return none
      | some fullTraceFS =>
          return some (stmtIn, stmtOut, proof, fullTraceFS)

/-- CO25 Theorem 5.1. Distribution of the basic-FS game (`Hyb_4` right-hand side) under a
concrete oracle implementation (oracle family `𝒟_IP`). Used for `hyb4Dist`. -/
def basicFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
      (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
      (Option (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  (simulateQ impl (basicFiatShamirGame (V := V) P).run).run' (← init)

/-- CO25 Theorem 5.1. Distribution of the DSFS game (`Hyb_0` left-hand side) under a concrete
oracle implementation (oracle family `𝒟_𝔖`). Used via `mappedDuplexSpongeFiatShamirGameDist`. -/
def duplexSpongeFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    ProbComp (Option <| DuplexSpongeFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  (simulateQ impl (duplexSpongeFiatShamirGame (codec := codec) (V := V) P).run).run' (← init)

/-- CO25 Theorem 5.1. Left experiment of Lemma 5.1 (`Hyb_0`): run the DSFS game under
`𝒟_𝔖(λ,n)` and apply the line-4 trace map D2STrace = `(φ⁻¹, ψ) ∘ StdTrace` to produce a
basic-FS query log. Corresponds to `Pr[𝒱^{h,p}(𝕩, π) = 1]` in the lemma statement. -/
def mappedDuplexSpongeFiatShamirGameDist
    [SampleableType U]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (traceMap :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  let outputDS ← duplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (codec := codec) init impl V P
  match outputDS with
  | none => return none
  | some ⟨stmtIn, stmtOut, proof, fullTraceDS⟩ => do
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          traceMap fullTraceDS
      match outputFS? with
      | none => return none
      | some fullTraceFS =>
          return some (stmtIn, stmtOut, proof, fullTraceFS)

end SecurityGames

section KeyLemma

open scoped NNReal

/-- CO25 §5.8 / Eq (57). `θ★(t) := t_p` — forward-permutation query budget of `𝒫̃`, used as the
query-bound multiplier in `η★`. -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-- CO25 Definition 4.1. Per-round codec bias profile `i ↦ ε_{cdc,i}(λ,n)`.
Parameters `(λ, n)` are suppressed (assumed fixed by the ambient instantiation); `CodecBias`
carries only the per-round values `ε_{cdc,i}` used in Claims 5.22 and the `η★` formula. -/
abbrev CodecBias :=
  pSpec.ChallengeIdx → ℝ≥0

/-- CO25 Theorem 5.1 / Eq (57). Additive error bound `η★(t_h, t_p, t_{p⁻¹})`:
```
η★ := numerator / (2 · |Σ|^c) + θ★ · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}
```
where `numerator = 7(t+L)² + … − 13(L+1)` with `t = t_h + t_p + t_{p⁻¹}`, `L` the total
permutation-query count from message/challenge absorb.  Sums the four hybrid-step bounds from
Claims 5.21 (Hyb_0 → Hyb_1), 5.22 (Hyb_1 → Hyb_2), 5.23 = 0 (Hyb_2 → Hyb_3), and 5.24
(Hyb_3 → Hyb_4). -/
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

omit [SpongeSize] in
/-- CO25 §5.8. Four-step hybrid composition bound via triangle inequality.
Combines `tvDist H₀ H₁ ≤ e₀₁`, …, `tvDist H₃ H₄ ≤ e₃₄` into
`tvDist H₀ H₄ ≤ e₀₁ + e₁₂ + e₂₃ + e₃₄`. Applied in `lemma_5_1_dist_from_claims`
with the four claim bounds (Hyb_0 → Hyb_1 → Hyb_2 → Hyb_3 → Hyb_4). -/
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

/-- CO25 §5.8 Hyb_0. Shared state for the canonical DS experiment: ambient shared-oracle state,
the random-hash cache (for `h : {0,1}^{≤n} → Σ^c`), and the permutation-oracle state (for
`p, p⁻¹` sampled from `𝒟_𝔖(λ,n)`). -/
abbrev Section58DSState
    (σShared σPerm : Type) :=
  σShared × (StmtIn →ₒ Vector U SpongeSize.C).QueryCache × σPerm

/-- CO25 §5.8. Fixed ambient shared-oracle package common to all Section 5.8 experiments.
Bundles state type, initializer, and query handler for `oSpec`. -/
class Section58SharedOraclePackage where
  σShared : Type                                           -- state type for the shared oracle
  initShared : ProbComp σShared                           -- shared-oracle sampler
  implShared : QueryImpl oSpec (StateT σShared ProbComp)  -- shared-oracle query handler

/-- CO25 §5.8 Hyb_0. Permutation-sampler package for the `𝒟_𝔖(λ,n)` experiment.
Bundles state type, sampler, and query handler for `p / p⁻¹ : Σ^{r+c} → Σ^{r+c}`. -/
class Section58PermutationPackage where
  σPerm : Type   -- state type for the permutation oracle
  initPerm : ProbComp σPerm   -- permutation-oracle sampler (𝒟_𝔖)
  -- forward/backward query handler (p / p⁻¹)
  implPerm : QueryImpl (permutationOracle (CanonicalSpongeState U)) (StateT σPerm ProbComp)

/-- CO25 §5.8 Hyb_0. Partial semantic law for the permutation package: forward and backward
answers must be mutually consistent across one-step transitions.  Approximates `p⁻¹ ∘ p = id`
from `𝒟_𝔖(λ,n)` without fully capturing the random-permutation law. -/
def Section58PermutationPackageLaw
    [permPkg : Section58PermutationPackage (U := U)] : Prop :=
  (∀ (σ : permPkg.σPerm) (stateIn stateOut : CanonicalSpongeState U) (σ' : permPkg.σPerm),
      (stateOut, σ') ∈ support ((permPkg.implPerm (.inl stateIn)).run σ) →
        stateIn ∈ Prod.fst '' support ((permPkg.implPerm (.inr stateOut)).run σ'))
    ∧
  (∀ (σ : permPkg.σPerm) (stateOut stateIn : CanonicalSpongeState U) (σ' : permPkg.σPerm),
      (stateIn, σ') ∈ support ((permPkg.implPerm (.inr stateOut)).run σ) →
        stateOut ∈ Prod.fst '' support ((permPkg.implPerm (.inl stateIn)).run σ'))

/-- CO25 §5.8 Hyb_0. Forward/backward consistency law for an explicit permutation implementation.

Mirrors `Section58PermutationPackageLaw` but takes `σPerm` and `permImpl` as plain terms (no
typeclass) — used by `lemma_5_1`, which carries explicit `(permInit, permImpl)` arguments rather
than a `Section58PermutationPackage` instance.

Addresses **D2** in `audit-report.md`: `lemma_5_1` now carries an explicit semantic hypothesis
that `permImpl` behaves like a sampled `𝒟_𝔖(λ,n)` permutation. -/
def IsPermutationLaw {σPerm : Type}
    (permImpl : QueryImpl (permutationOracle (CanonicalSpongeState U)) (StateT σPerm ProbComp)) :
    Prop :=
  (∀ (σ : σPerm) (stateIn stateOut : CanonicalSpongeState U) (σ' : σPerm),
      (stateOut, σ') ∈ support ((permImpl (.inl stateIn)).run σ) →
        stateIn ∈ Prod.fst '' support ((permImpl (.inr stateOut)).run σ'))
    ∧
  (∀ (σ : σPerm) (stateOut stateIn : CanonicalSpongeState U) (σ' : σPerm),
      (stateIn, σ') ∈ support ((permImpl (.inr stateOut)).run σ) →
        stateOut ∈ Prod.fst '' support ((permImpl (.inl stateIn)).run σ'))

/-- CO25 §5.8 Hyb_0. Canonical initializer for the DS-side experiment: run `sharedInit`, start
the hash-oracle cache empty, and sample the permutation state from `permInit` (𝒟_𝔖 line 1). -/
def section58CanonicalDSInit
    {σShared σPerm : Type}
    (sharedInit : ProbComp σShared)
    (permInit : ProbComp σPerm) :
    ProbComp (Section58DSState (StmtIn := StmtIn) (U := U) σShared σPerm) := do
  let sharedState ← sharedInit
  let permState ← permInit
  pure (sharedState, ∅, permState)

/-- CO25 §5.8 Hyb_0. Canonical query handler for the DS-side experiment: shared queries →
`sharedImpl`; `h` queries → lazy random oracle; `p / p⁻¹` queries → `permImpl` (𝒟_𝔖). -/
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

/-- CO25 §5.8 Hyb_0. Named DS-side sampler for the paper's `𝒟_𝔖(λ,n)` experiment, relative to
the ambient shared-oracle and permutation packages. -/
abbrev paperDSInit [sharedPkg : Section58SharedOraclePackage (oSpec := oSpec)]
    [permPkg : Section58PermutationPackage (U := U)] :
    ProbComp (Section58DSState
      (StmtIn := StmtIn) (U := U)
      sharedPkg.σShared permPkg.σPerm) :=
  section58CanonicalDSInit
    (StmtIn := StmtIn) (U := U)
    sharedPkg.initShared permPkg.initPerm

/-- CO25 §5.8 Hyb_0. Named DS-side query handler for the paper's `𝒟_𝔖(λ,n)` experiment, relative
to the ambient shared-oracle and permutation packages. -/
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

/-- CO25 §5.8 Hyb_4. Named basic-FS-side sampler for the paper's `𝒟_IP(λ,n)` experiment, relative
to the ambient shared-oracle package. -/
abbrev paperIPInit [sharedPkg : Section58SharedOraclePackage (oSpec := oSpec)] :
    ProbComp (Section58ChallengeState
      (fsChallengeOracle (Vector U δ × StmtIn) pSpec) sharedPkg.σShared) :=
  section58ChallengeInit
    (challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec)
    (sharedInit := sharedPkg.initShared)

/-- CO25 §5.8 Hyb_4. Named salted basic-FS-side query handler for the paper's `𝒟_IP(λ,n)`
experiment, relative to the ambient shared-oracle package. -/
abbrev paperIPImpl [DecidableEq StmtIn] [SampleableType U]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [sharedPkg : Section58SharedOraclePackage (oSpec := oSpec)] :
    QueryImpl (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
      (StateT (Section58ChallengeState
        (fsChallengeOracle (Vector U δ × StmtIn) pSpec) sharedPkg.σShared) ProbComp) :=
  section58ChallengeImpl
    (oSpec := oSpec) (U := U)
    (challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec)
    (sharedImpl := sharedPkg.implShared)

/-- CO25 §5.8 Hyb_0. Left experiment of Theorem 5.1 (Figure 4 column 1): DSFS game under
`𝒟_𝔖(λ,n)` with D2STrace applied to `tr_𝒫̃ ‖ tr_𝒱`.  Corresponds to
`Pr[𝒱^{h,p}(𝕩, π) = 1]` in the lemma statement. -/
abbrev hyb0Dist
    [SampleableType U]
    {σDS : Type}
    (initDS : ProbComp σDS)
    (implDS : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σDS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (paperD2STrace :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U))
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (codec := codec)
    initDS implDS V maliciousProver paperD2STrace

/-- CO25 §5.8 Hyb_4. Right experiment of Theorem 5.1 (Figure 4 column 5): basic-FS game under
`𝒟_IP(λ,n)` with prover `D2SAlgo^f(𝒫̃)` and verifier `𝒱_std^f`.  Corresponds to
the right-hand probability `Pr[𝒱_std^f(𝕩, π) = 1]` in the lemma statement. -/
abbrev hyb4Dist
    {σFS : Type}
    (initFS : ProbComp σFS)
    (implFS : QueryImpl
      (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (Vector U δ × StmtIn) pSpec))
      (StateT σFS ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (d2sAlgo : D2SAlgo (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) :=
  basicFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    initFS implFS V (d2sAlgo maliciousProver)


/-- CO25 Claim 5.21. Statistical-distance bound for `Hyb_0` vs `Hyb_1` (Eq. from the claim):
`(7·T² − 3·T) / (2·|Σ|^c)` where `T = t_h + 1 + t_p + L + t_{p⁻¹}`. -/
noncomputable def claim5_21Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- CO25 Claim 5.22. Statistical-distance bound for `Hyb_1` vs `Hyb_2` (Eq. 53):
`θ★(t_h, t_p, t_{p⁻¹}) · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}`. -/
noncomputable def claim5_22Bound
    (tₕ tₚ tₚᵢ : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
    + ∑ i, (εcodec i : ℝ)

/-- CO25 Claim 5.24. Statistical-distance bound for `Hyb_3` vs `Hyb_4` (Eq. 55):
`(7·L·(2·t_h + 2 + 2·t_p + L + 2·t_{p⁻¹})) / (2·|Σ|^c) − 5·(L+1) / |Σ|^c`. -/
noncomputable def claim5_24Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let Lr : ℝ := L
  let cardPow : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  (7 * Lr * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + Lr + 2 * (tₚᵢ : ℝ))) / (2 * cardPow)
    - (5 * (Lr + 1)) / cardPow

/-- CO25 §5.8 Hyb_1. Canonical `Hyb_1` distribution (Figure 4, column 2): oracles
`g := (g_i)_{i ∈ [k]} ← 𝒟_Σ(λ,n)` (Eq. 45); prover `𝒫̃^{D2SQuery^g}`; verifier
`𝒱^{D2SQuery^g}`; line-4 trace `(φ⁻¹, ψ)(tr_𝒫̃ ‖ tr_𝒱)`. -/
noncomputable def section58Hyb1Dist
    [SampleableType U]
    [DecidableEq StmtIn] [DecidableEq U]
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) := by
  let challengeSpec := section58EncodedChallengeOracle (U := U) StmtIn pSpec δ
  let _ : DecidableEq challengeSpec.Domain := by
    classical infer_instance
  let _ : ∀ q : challengeSpec.Domain, SampleableType (challengeSpec.Range q) := by
    intro q
    cases q with
    | mk i qKey =>
        change SampleableType (Vector U (challengeSize (pSpec := pSpec) i))
        infer_instance
  let params :
      D2SQueryParamsWithOracle
        (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
        challengeSpec :=
    { codecBridge :=
        { evalGI := fun roundIdx stmt0 salt0 encodedMessages0 =>
            OptionT.lift <|
              (show OracleComp
                  (D2SChallengePlusUnitOracle (U := U) challengeSpec)
                  (Vector U (challengeSize (pSpec := pSpec) roundIdx)) from
                query
                  (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
                  (.inl ⟨roundIdx,
                    (stmt0, salt0,
                      EncodedMessagesUpTo.toList encodedMessages0)⟩)) } }
  exact
    section58HybridGameDist
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec)
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
        (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))

/-- CO25 §5.8 Hyb_2. Canonical `Hyb_2` distribution (Figure 4, column 3): oracles
`e := (e_i)_{i ∈ [k]} ← 𝒰(…)` (Eq. 52); prover `𝒫̃^{D2SQuery^{ψ⁻¹∘e}}`; verifier
`𝒱^{D2SQuery^{ψ⁻¹∘e}}`; line-4 trace `φ⁻¹(tr_𝒫̃ ‖ tr_𝒱)`. -/
noncomputable def section58Hyb2Dist
    [Fintype U] [SampleableType U]
    [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) := by
  let challengeSpec := section58DecodedChallengeOracle (U := U) StmtIn pSpec δ
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
      (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 salt0 encodedMessages0 =>
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (pSpec.Challenge roundIdx) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl ⟨roundIdx,
                (stmt0, salt0,
                  EncodedMessagesUpTo.toList encodedMessages0)⟩)))
  exact
    section58HybridGameDist
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec)
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
        (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))

/-- CO25 §5.8 Hyb_3. Canonical `Hyb_3` distribution (Figure 4, column 4): oracles
`f := (f_i)_{i ∈ [k]} ← 𝒰(…)` (Eq. 54); prover `𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}`; verifier
`𝒱^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}`; line-4 trace is `tr_𝒫̃ ‖ tr_𝒱` (no translation). -/
noncomputable def section58Hyb3Dist
    [Fintype U] [SampleableType U]
    [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) := by
  -- CO25 §5.8 Hyb_3 (paper-faithful): the challenge oracle is the *salted* FS oracle
  -- `f_i: ... × {0,1}^δ × M_{P,1} × ... × M_{P,i-1} → M_{V,i}`, with the salt `τ` threaded
  -- through the augmented statement `(τ, x) ∈ Vector U δ × StmtIn` (Encoding A, matching
  -- `SingleSalt.lean`). The line-4 trace map keeps the salted FS query log.
  let challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec
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
      (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 salt0 encodedMessages0 => do
        let messagesUpTo ←
          match section58EncodedMessagesUpTo?
              (pSpec := pSpec) (U := U) (codec := codec) roundIdx
              (EncodedMessagesUpTo.toList encodedMessages0) with
          | some messagesUpTo => pure messagesUpTo
          | none => failure
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (pSpec.Challenge roundIdx) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl ⟨roundIdx, ((salt0, stmt0), messagesUpTo)⟩)))
  exact
    section58HybridGameDist
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec)
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
        (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))


/-- CO25 Claim 5.21. Target proposition for the canonical `Hyb_0` / `Hyb_1` step:
`Δ(Hyb_0, Hyb_1) ≤ (7·T² − 3·T) / (2·|Σ|^c)` where `T = t_h + 1 + t_p + L + t_{p⁻¹}`.
Proof uses `Theorem 5.8` (bad-event probability bound for `E(tr)`). -/
def claim_5_21
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (tₕ tₚ tₚᵢ : ℕ) :
    Prop :=
  tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver
        (paperD2STraceSingleSalted
          (δ := δ)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)))
      (section58Hyb1Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
    ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries

/-- CO25 Claim 5.22. Target proposition for the canonical `Hyb_1` / `Hyb_2` step (Eq. 53):
`Δ(Hyb_1, Hyb_2) ≤ θ★ · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}`.
Hybrids differ in that `g_i` outputs `Σ^{ℓ_V(i)}` while `e_i` outputs `M_{V,i}`; the gap is
bounded by the codec decoding bias `ε_{cdc,i}` via the map `ψ_i`. -/
def claim_5_22
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (tₕ tₚ tₚᵢ : ℕ) :
    Prop :=
  tvDist
      (section58Hyb1Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
      (section58Hyb2Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
    ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ (εcodec := codec.decodingBias)

/-- CO25 Claim 5.23. Target proposition for the canonical `Hyb_2` / `Hyb_3` step:
`Δ(Hyb_2, Hyb_3) = 0`.
Hybrids are identically distributed: `φ_i` is injective so replacing encoded inputs by decoded
inputs changes only the query format, not the distribution. -/
def claim_5_23
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    Prop :=
  tvDist
    (section58Hyb2Dist (δ := δ) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
    (section58Hyb3Dist (δ := δ) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver) = 0

/-- CO25 Claim 5.24. Target proposition for the canonical `Hyb_3` / `Hyb_4` step (Eq. 55):
`Δ(Hyb_3, Hyb_4) ≤ (7·L·(2t_h+2+2t_p+L+2t_{p⁻¹})) / (2·|Σ|^c) − 5·(L+1) / |Σ|^c`.
The bound comes from the probability of the event `E_𝒱` (verifier D2SQuery aborts but
prover does not), which is controlled by Eq. (34). -/
def claim_5_24
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (d2sAlgo : D2SAlgo (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    Prop :=
  tvDist
      (section58Hyb3Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
        (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver d2sAlgo)
    ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [DecidableEq StmtIn] [DecidableEq U] in
/-- CO25 Theorem 5.1 (bridge lemma). Distance component from Claims 5.21–5.24.
Assembles the four-step hybrid chain `Hyb_0 → Hyb_1 → Hyb_2 → Hyb_3 → Hyb_4` via
`tvDist_hybridChain4` and concludes `Δ(Hyb_0, Hyb_4) ≤ η★`.
Keeps the hybrid decomposition explicit; arithmetic reconciliation with `ηStar` is a
separate `hBound` hypothesis. -/
theorem lemma_5_1_dist_from_claims
    [Fintype U] [SampleableType U] [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [Section58SharedOraclePackage (oSpec := oSpec)]
    [Section58PermutationPackage (U := U)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (hPermPackageLaw : Section58PermutationPackageLaw (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (d2sAlgo : D2SAlgo (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (h21 : claim_5_21 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec)
      V maliciousProver tₕ tₚ tₚᵢ)
    (h22 : claim_5_22 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec)
      V maliciousProver tₕ tₚ tₚᵢ)
    (h23 : claim_5_23 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec)
      V maliciousProver)
    (h24 : claim_5_24 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec)
      V maliciousProver d2sAlgo tₕ tₚ tₚᵢ)
    (hBound :
      claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        + claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ (εcodec := codec.decodingBias)
        + 0
        + claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
            (εcodec := codec.decodingBias) : ℝ)) :
    tvDist
      (hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver
        (paperD2STraceSingleSalted
          (δ := δ)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)))
      (hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
        (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver d2sAlgo)
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
            (εcodec := codec.decodingBias) : ℝ) := by
  let _ := hPermPackageLaw
  have h23' :
      tvDist
        (section58Hyb2Dist (δ := δ) (T_H := T_H) (T_P := T_P)
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
        (section58Hyb3Dist (δ := δ) (T_H := T_H) (T_P := T_P)
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
        ≤ (0 : ℝ) := by
    rw [h23]
  have hChain :=
    tvDist_hybridChain4
      (H₀ := hyb0Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec)
        (paperDSInit (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        (paperDSImpl (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
        V maliciousProver
        (paperD2STraceSingleSalted
          (δ := δ)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)))
      (H₁ := section58Hyb1Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
      (H₂ := section58Hyb2Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
      (H₃ := section58Hyb3Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)
      (H₄ := hyb4Dist (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        (paperIPInit (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec))
        (paperIPImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver d2sAlgo)
      (e₀₁ := claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
      (e₁₂ := claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ (εcodec := codec.decodingBias))
      (e₂₃ := 0)
      (e₃₄ := claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries)
      h21 h22 h23' h24
  linarith

/-- CO25 Theorem 5.1. Per-index query-bound predicate for the malicious prover `𝒫̃`.
`tShared` bounds queries to the ambient `oSpec`; `(t_h, t_p, t_{p⁻¹})` bound the three
DS sub-oracles `h`, `p`, `p⁻¹`. Uses `duplexSpongeQueryBudgetWithShared` from `Defs.lean`. -/
abbrev IsLemma5_1QueryBound
    [DecidableEq ι]
    (maliciousProver :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  OracleComp.IsPerIndexQueryBound maliciousProver
    (duplexSpongeQueryBudgetWithShared (StmtIn := StmtIn) (U := U) tShared tₕ tₚ tₚᵢ)

/-- CO25 §5.4 paper-facing `D2SAlgo^f` witness for the salted theorem path.
It answers `g_i` by querying the external salted FS oracle `f_i(τ, x, ·)` and lets
`d2sQueryStepWithOracle` apply the `ψ_i⁻¹` preimage sampler. -/
def paperD2SAlgoSaltedExternal
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)] :
    D2SAlgo (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := fun P =>
  let challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec
  let params :=
    defaultD2SQueryParamsWithOracle
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 salt0 encodedMessages0 => do
        let messagesUpTo ←
          match section58EncodedMessagesUpTo?
              (pSpec := pSpec) (U := U) (codec := codec) roundIdx
              (EncodedMessagesUpTo.toList encodedMessages0) with
          | some messagesUpTo => pure messagesUpTo
          | none => failure
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (pSpec.Challenge roundIdx) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl ⟨roundIdx, ((salt0, stmt0), messagesUpTo)⟩)))
  let d2sOuterImpl :
      QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))
      (QueryImpl.id oSpec)
      (d2sQueryImplCoreWithOracle
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
        (challengeSpec := challengeSpec) params)
  let outWithState :
      OptionT (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        ((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
    (simulateQ d2sOuterImpl P).run default
  do
    let out? ← outWithState.run
    pure (out?.map Prod.fst)

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- CO25 Theorem 5.1 (Main lemma §5.8, existential form). For every malicious prover `𝒫̃` making
at most `t_h` queries to `h` and `t_p` / `t_{p⁻¹}` queries to `p / p⁻¹`, there exist a
D2SAlgo prover transform and a D2STrace line-4 map such that:
```
|Pr[𝒱^{h,p}(𝕩,π)=1] − Pr[𝒱_std^f(𝕩,π)=1]| ≤ η★(t_h, t_p, t_{p⁻¹})
```
and D2SAlgo makes at most `θ★(t_h, t_p, t_{p⁻¹}) = t_p` total queries.

The statement fixes both sides to canonical lazy-random-function oracle implementations and
leaves only the ambient shared-oracle `(sharedInit, sharedImpl)` and permutation sampler
`(permInit, permImpl)` explicit.  The caller must supply `hPermLaw : IsPermutationLaw permImpl`,
which asserts forward/backward consistency — the minimal semantic requirement on `𝒟_𝔖(λ,n)`
used in the proof.  Addresses **D2** in `audit-report.md`.

## Relationship to `lemma_5_1_dist_from_claims` (C6)

The Milestone 1 deliverable is the four-step hybrid distance bound, and the **proved**
backbone is `lemma_5_1_dist_from_claims` above (line 1047). That theorem assembles
`Hyb_0 → Hyb_1 → Hyb_2 → Hyb_3 → Hyb_4` via `tvDist_hybridChain4` and concludes
`Δ(Hyb_0, Hyb_4) ≤ η★` from the four `claim_5_2{1,2,3,4}` hypotheses; **its body has no
`sorry`** — only the four claim bodies are deferred (statement-only as the plan permits).

`lemma_5_1` (this theorem) packages that bound as the paper-facing **existential**: it picks
canonical salted witnesses (`d2sAlgo := paperD2SAlgoSaltedExternal`,
`paperD2STrace := paperD2STraceSingleSalted`) and rewrites the conclusion against
`mappedDuplexSpongeFiatShamirGameDist`/`basicFiatShamirGameDist` (instead of the internal
`hyb0Dist`/`hyb4Dist` shapes used by `_dist_from_claims`). The body `sorry` (line 1231) is
exactly this **shape-bridge** between the two formulations — it is *not* the four-step
distance argument itself, which is already discharged inside `lemma_5_1_dist_from_claims`.

Per audit C6: callers needing a working M1 distance bound should invoke
`lemma_5_1_dist_from_claims` directly. `lemma_5_1` exists as the paper-facing wrapper and
its body is deferred to Milestone 2 alongside the four claim proofs. -/
theorem lemma_5_1
    [Fintype U] [SampleableType U]
    [DecidableEq U]
    [DecidableEq StmtIn]
    [DecidableEq ι]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    {σShared σPerm : Type}
    (sharedInit : ProbComp σShared)
    (sharedImpl : QueryImpl oSpec (StateT σShared ProbComp))
    (permInit : ProbComp σPerm)
    (permImpl : QueryImpl
      (permutationOracle (CanonicalSpongeState U)) (StateT σPerm ProbComp))
    (δ : Nat)
    -- `hPermLaw`: forward/backward consistency — the p/p⁻¹ semantic requirement from 𝒟_𝔖(λ,n)
    -- (.inl stateIn) queries p (forward); (.inr stateOut) queries p⁻¹ (backward)
    (hPermLaw : IsPermutationLaw (U := U) permImpl)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge) :
    ∃ (d2sAlgo : D2SAlgo (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (paperD2STrace :
        QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
          OptionT (OracleComp (Unit →ₒ U))
            (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))),
      ∀ (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)),
      IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ →
      tvDist -- 1/2 ∑ |p(i) - q(i)|
         -- hybrid 0
        (mappedDuplexSpongeFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (codec := codec)
          (section58CanonicalDSInit
            (StmtIn := StmtIn) (U := U) sharedInit permInit)
          (section58CanonicalDSImpl
            (oSpec := oSpec) (StmtIn := StmtIn) (U := U) sharedImpl permImpl)
          V maliciousProver paperD2STrace)
        -- hybrid 4
        (basicFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec)
          (section58ChallengeInit
            (challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec)
            (sharedInit := sharedInit))
          (section58ChallengeImpl
            (oSpec := oSpec) (U := U)
            (challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec)
            (sharedImpl := sharedImpl))
          V (d2sAlgo maliciousProver))
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
            (εcodec := codec.decodingBias) : ℝ)
      ∧ OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact paperD2SAlgoSaltedExternal
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
  · exact paperD2STraceSingleSalted
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
  · intro maliciousProver hMaliciousBound
    let _ := hTp
    let _ := hMaliciousBound
    sorry

end KeyLemma

end DuplexSpongeFS.KeyLemma
