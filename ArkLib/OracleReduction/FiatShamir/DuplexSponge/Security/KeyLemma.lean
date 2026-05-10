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
- canonical abstractions for `D2SAlgo` and the Section 5.8 trace algorithms, and
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
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)]
  -- CO25 Def 4.1 codec: supplies sizes and Serialize/Deserialize via projections.
  [codec : Codec pSpec U]
  {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

/-- CO25 Eq. 54 — eager full-table distribution `𝒟_IP` (symbol `f`, salted) over the
salted Fiat–Shamir challenge oracle for `Hyb₃` and `Hyb₄`.

Samples a single full random table `f : (q : Domain) → Range q` once at game start over the
salted domain `dom'_i = {0,1}^≤n × {0,1}^{δ⋆} × ℳ_{P,1} × … × ℳ_{P,i}` with range `ℳ_{V,i}`.
Per CO25 line 1784, Hyb₃ and Hyb₄ both sample from this same distribution; the difference
between hybrids lies in the prover/verifier algorithm, not the oracle. -/
noncomputable def section58SaltedFiatShamirDist :
    ArkLib.OracleReduction.OracleDistribution
      (fsChallengeOracle (Vector U δ × StmtIn) pSpec) :=
  ArkLib.OracleReduction.OracleDistribution.uniform _

/-- Bridge: `SampleableType` for `section58EncodedChallengeOracle` (Hyb₁ `g`) derived from
granular `VCVCompatible` base-type hypotheses. Eliminates verbose `SampleableType (OracleFamily
(section58EncodedChallengeOracle …))` at call sites in §5.8 hybrids. -/
noncomputable instance instSampleableTypeEncodedChallengeOracle :
    SampleableType (ArkLib.OracleReduction.OracleFamily
      (section58EncodedChallengeOracle (U := U) StmtIn pSpec δ)) := by
  sorry

/-- Bridge: `SampleableType` for `section58DecodedChallengeOracle` (Hyb₂ `e`) derived from
granular `VCVCompatible` base-type hypotheses. Eliminates verbose `SampleableType (OracleFamily
(section58DecodedChallengeOracle …))` at call sites in §5.8 hybrids. -/
noncomputable instance instSampleableTypeDecodedChallengeOracle :
    SampleableType (ArkLib.OracleReduction.OracleFamily
      (section58DecodedChallengeOracle (U := U) StmtIn pSpec δ)) := by
  sorry

section SecurityGames

/-- Lift salted basic-FS verifier queries into the external `f_i` oracle plus D2S auxiliary
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
    projectD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U)
      proveQueryLogRaw
  let verifyQueryLog :=
    projectD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U)
      verifyQueryLogRaw
  return ⟨stmtIn, ← stmtOut.getM, proof, proveQueryLog ++ verifyQueryLog⟩

/-- CO25 Theorem 5.1. Left-hand game for Lemma 5.1: the duplex-sponge Fiat-Shamir transform under
DS oracles `h, p, p⁻¹` sampled from `𝒟_𝔖(λ,n)`. This is `Hyb_0`, before the Section 5.8
hybrid rewrite through `D2SQuery`.

Type-level CO25 Figure 4 line 3: the honest verifier is invoked at the narrow forward-only spec
`oSpec + duplexSpongeForwardOracle StmtIn U` (`𝒱^{h,p}` — no `p⁻¹`); its query log is then lifted
into the wide spec used by the (adversarial) prover for log concatenation. -/
def duplexSpongeFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (DuplexSpongeFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  let ⟨⟨stmtIn, proof⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  -- Build V's verify computation at the narrow forward-only spec (`𝒱^{h,p}`) — this is the
  -- type-level CO25 Figure 4 line 3 guarantee. Then `liftComp` it into the wide spec so the
  -- subsequent `simulateQ loggingOracle` emits a wide-spec query log; by construction the
  -- wide log's `p⁻¹` slot contains no entries from V.
  let verifyCompNarrow := ((V.duplexSpongeFiatShamirSaltedForward δ).run
    stmtIn (fun i => match i with | ⟨0, _⟩ => proof))
  let verifyCompWide :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
    liftComp verifyCompNarrow (oSpec + duplexSpongeChallengeOracle StmtIn U)
  let ⟨stmtOut, verifyQueryLog⟩ ← liftM (simulateQ loggingOracle verifyCompWide).run
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
        DSAbort U
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)))
    (fullTrace : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp
      (Option (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

/-- CO25 §5.8. Execute a Section 5.8 line-4 trace map on a projected hybrid trace (after removing
auxiliary unit-sampling entries), interpreting remaining randomness uniformly. -/
def runSection58ProjectedTraceMap
    [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (traceMap :
      QueryLog (oSpec + challengeSpec) →
        DSAbort U
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)))
    (fullTrace : QueryLog (oSpec + challengeSpec)) :
    ProbComp
      (Option (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

/-- CO25 §5.8. Sampler for the §5.8 hybrid experiment carrier: draws one realization from the
chosen challenge-oracle distribution `D_chal` (paper `𝒟_Σ` / `𝒟_e` / `𝒟_IP_salted`).  The
sampled carrier is then held fixed by `section58ChallengeImpl` for the entire game run, matching
the paper's "sample at start, then answer queries deterministically" semantics. -/
def section58ChallengeInit
    {κ : Type} {challengeSpec : OracleSpec κ}
    (D_chal : ArkLib.OracleReduction.OracleDistribution challengeSpec) :
    ProbComp D_chal.Carrier :=
  D_chal.sample

/-- CO25 §5.8. Stateless 4-slot query handler for the §5.8 hybrid experiment: ambient `oSpec`
queries → caller-supplied `oSpecImpl`; challenge queries → `D_chal.toImpl k_chal` (paper
`𝒟_Σ` / `𝒟_e` / `𝒟_IP_salted`); auxiliary unit queries → `d2sUnitSampleImpl` (fresh per
call); auxiliary `unifSpec` queries → ambient `ProbComp` uniform sampling.  The `D_chal`
carrier is read from the state but never mutated — sampled once by `section58ChallengeInit`
and held fixed (CO25 Eq. 15 / Eq. 52 / Eq. 54).  The paper has no ambient distribution; we
take an arbitrary `QueryImpl oSpec ProbComp` instead, which the caller specializes (e.g. to
the empty spec for paper fidelity). -/
def section58ChallengeImpl
    [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (D_chal : ArkLib.OracleReduction.OracleDistribution challengeSpec) :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT D_chal.Carrier ProbComp) :=
  fun q => do
    let kC ← get
    match q with
    | .inl qShared =>
        let resp ← StateT.lift <| oSpecImpl qShared
        pure resp
    | .inr (.inl qChal) =>
        let resp ← StateT.lift <| D_chal.toImpl kC qChal
        pure resp
    | .inr (.inr (.inl qUnit)) =>
        let resp ← StateT.lift <| d2sUnitSampleImpl (U := U) qUnit
        pure resp
    | .inr (.inr (.inr qUnif)) =>
        let resp ← StateT.lift <|
          (show ProbComp (unifSpec.Range qUnif) from
            query (spec := unifSpec) qUnif)
        pure resp

/-- CO25 §5.8 Hyb_0. Sampler for the DSFS-side experiment carrier: draws one realization of
`(h, p)` from the duplex-sponge oracle distribution `𝒟_𝔖` (CO25 Def. 4.2).  The carrier is
held fixed by `section58Hyb0Impl` for the entire game run. -/
def section58Hyb0Init :
    ProbComp (duplexSpongeOracleDistribution StmtIn U).Carrier :=
  (duplexSpongeOracleDistribution StmtIn U).sample

/-- CO25 §5.8 Hyb_0. Stateless query handler for the DSFS-side experiment: ambient `oSpec`
queries → caller-supplied `oSpecImpl`; duplex-sponge queries (`h`, `p`, `p⁻¹`) →
`𝒟_𝔖.toImpl k_DS`.  `k_DS` is sampled once at game start by `section58Hyb0Init` and held
fixed (CO25 Def. 4.2).  The paper has no ambient distribution; we take an arbitrary
`QueryImpl oSpec ProbComp` instead. -/
def section58Hyb0Impl
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (duplexSpongeOracleDistribution StmtIn U).Carrier ProbComp) :=
  fun q => do
    let kDS ← get
    match q with
    | .inl qShared =>
        let resp ← StateT.lift <| oSpecImpl qShared
        pure resp
    | .inr qDS =>
        let resp ← StateT.lift <| (duplexSpongeOracleDistribution StmtIn U).toImpl kDS qDS
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
      D2SCodecBridgeWithOracle
        (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
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
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))
      (QueryImpl.id oSpec)
      (d2sQueryImplCoreWithOracle
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) params)
  let proverComp :
      OptionT
        (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        ((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
    (simulateQ d2sOuterImpl P).run default
  let ⟨proverOut?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle proverComp.run).run
  let ⟨⟨stmtIn, proof⟩, _⟩ ←
    match proverOut? with
    | some proverOut => pure proverOut
    | none => failure
  -- Type-level CO25 Figure 4 line 3: honest verifier runs at the narrow forward-only spec
  -- (`𝒱^{h,p}` — no `p⁻¹`), then `liftComp`-ed into the wide spec consumed by `d2sOuterImpl`.
  let verifyCompNarrow :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Option StmtOut) :=
    ((V.duplexSpongeFiatShamirSaltedForward δ).run
      stmtIn (fun i => match i with | ⟨0, _⟩ => proof)).run
  let verifyCompWide :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
    liftComp verifyCompNarrow (oSpec + duplexSpongeChallengeOracle StmtIn U)
  let verifierComp :
      OptionT
        (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        (Option StmtOut ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
    (simulateQ d2sOuterImpl verifyCompWide).run default
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
      D2SCodecBridgeWithOracle
        (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        challengeSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (traceMap :
      QueryLog (oSpec + challengeSpec) →
        DSAbort U
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
        (pSpec := pSpec) (U := U)
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
  (simulateQ impl (duplexSpongeFiatShamirGame (V := V) P).run).run' (← init)

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
        DSAbort U
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  let outputDS ← duplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
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
`tvDist H₀ H₄ ≤ e₀₁ + e₁₂ + e₂₃ + e₃₄`. This remains a generic helper; the
Section 5.8 claim statements below are exposed as public theorem surfaces. -/
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

/-- CO25 §5.8 Hyb_1. `Hyb_1` distribution sampled via
`OracleDistribution.runWith`: ambient `oSpec` answered by caller-supplied `oSpecImpl`, encoded challenge oracle
`g := (g_i)_{i ∈ [k]} ← 𝒟_Σ(λ,n)` (CO25 Eq. 15) sampled eagerly via
`section58EncodedChallengeDist`, auxiliary `(Unit →ₒ U)` and `unifSpec` slots handled
inline (fresh per call).

Line-4 trace map is `(φ⁻¹, ψ)(tr_𝒫̃ ‖ tr_𝒱)` (`section58Hyb1Line4Trace`). -/
noncomputable def section58Hyb1Dist
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) := by
  let challengeSpec := section58EncodedChallengeOracle (U := U) StmtIn pSpec δ
  let D_g := section58EncodedChallengeDist (U := U) StmtIn pSpec δ
  let params :
      D2SCodecBridgeWithOracle
        (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        challengeSpec :=
    { evalGI := fun roundIdx stmt0 salt0 encodedMessages0 =>
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (Vector U (challengeSize (pSpec := pSpec) roundIdx)) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl ⟨roundIdx,
                (stmt0, salt0, encodedMessages0)⟩)) }
  exact
    section58HybridGameDist
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := section58ChallengeInit (challengeSpec := challengeSpec) D_g)
      (impl := section58ChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_g)
      params V maliciousProver
      (section58Hyb1Line4Trace
        (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_2. `Hyb_2` distribution sampled via
`OracleDistribution.runWith`: ambient `oSpec` answered by caller-supplied `oSpecImpl`, decoded challenge oracle
`e := (e_i)_{i ∈ [k]}` (CO25 Eq. 52) sampled eagerly via `section58DecodedChallengeDist`,
auxiliary slots inline. Line-4 trace map is `φ⁻¹(tr_𝒫̃ ‖ tr_𝒱)`
(`section58Hyb2Line4Trace`). -/
noncomputable def section58Hyb2Dist
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) := by
  let challengeSpec := section58DecodedChallengeOracle (U := U) StmtIn pSpec δ
  let D_e := section58DecodedChallengeDist (U := U) StmtIn pSpec δ
  let params :=
    defaultD2SCodecBridgeWithOracle
      (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 salt0 encodedMessages0 =>
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (pSpec.Challenge roundIdx) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl ⟨roundIdx,
                (stmt0, salt0, encodedMessages0)⟩)))
  exact
    section58HybridGameDist
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := section58ChallengeInit (challengeSpec := challengeSpec) D_e)
      (impl := section58ChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_e)
      params V maliciousProver
      (section58Hyb2Line4Trace
        (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_3. `Hyb_3` distribution sampled via
`OracleDistribution.runWith`: ambient `oSpec` answered by caller-supplied `oSpecImpl`, salted Fiat–Shamir oracle
`f := (f_i)_{i ∈ [k]} ← 𝒟_IP(λ,n)` (CO25 Eq. 54) sampled eagerly via
`section58SaltedFiatShamirDist`, auxiliary slots inline. Line-4 trace map is identity
(`section58Hyb3Line4Trace`). -/
noncomputable def section58Hyb3Dist
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) := by
  let challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec
  let D_IP_salted :=
    section58SaltedFiatShamirDist (StmtIn := StmtIn) (U := U) (pSpec := pSpec) (δ := δ)
  let params :=
    defaultD2SCodecBridgeWithOracle
      (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 salt0 encodedMessages0 => do
        let messagesUpTo ←
          match section58EncodedMessagesUpTo?
              (pSpec := pSpec) (U := U) roundIdx encodedMessages0 with
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
      (pSpec := pSpec) (U := U)
      (init := section58ChallengeInit (challengeSpec := challengeSpec) D_IP_salted)
      (impl := section58ChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_IP_salted)
      params V maliciousProver
      (section58Hyb3Line4Trace
        (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_0. `Hyb_0` left-experiment distribution sampled via
`OracleDistribution.runWith`: ambient `oSpec` answered by caller-supplied `oSpecImpl`,
duplex-sponge oracle
`(h, p, p⁻¹) ← 𝒟_𝔖(λ,n)` (CO25 Def. 4.2) sampled eagerly via
`duplexSpongeOracleDistribution`. Line-4 trace map = D2STrace = `(φ⁻¹, ψ) ∘ StdTrace`.
Samples `(h, p)` eagerly at game start rather than via a lazy random-oracle cache for `h`. -/
noncomputable abbrev hyb0Dist
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (d2sTrace :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        DSAbort U
          (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) :=
  mappedDuplexSpongeFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    (init := section58Hyb0Init (StmtIn := StmtIn) (U := U))
    (impl := section58Hyb0Impl (oSpec := oSpec) (StmtIn := StmtIn) (U := U) oSpecImpl)
    V maliciousProver d2sTrace

/-- CO25 §5.8 Hyb_4. `Hyb_4` right-experiment distribution sampled via
`OracleDistribution.runWith`: ambient `oSpec` answered by caller-supplied `oSpecImpl`, salted
Fiat–Shamir oracle
`f ← 𝒟_IP(λ,n)` (CO25 line 1784) sampled eagerly via `section58SaltedFiatShamirDist`
(same distribution as Hyb_3; the difference between Hyb_3 and Hyb_4 is the prover/verifier
algorithm, not the oracle). -/
noncomputable abbrev hyb4Dist
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (d2sAlgo : D2SAlgo (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)) :=
  let challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec
  let D_IP_salted :=
    section58SaltedFiatShamirDist (StmtIn := StmtIn) (U := U) (pSpec := pSpec) (δ := δ)
  basicFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec)
    (init := section58ChallengeInit (challengeSpec := challengeSpec) D_IP_salted)
    (impl := section58ChallengeImpl
      (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_IP_salted)
    V (d2sAlgo maliciousProver)

/-- CO25 Claim 5.21.
`Δ(Hyb_0, Hyb_1) ≤ (7·T² − 3·T) / (2·|Σ|^c)` with `Hyb_0 / Hyb_1` sampled eagerly via
`hyb0Dist` / `section58Hyb1Dist`. -/
def claim_5_21
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (tₕ tₚ tₚᵢ : ℕ) :
    Prop :=
  tvDist
      (hyb0Dist (δ := δ) (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        oSpecImpl V maliciousProver
        (stdTraceSingleSalted
          (δ := δ)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (section58Hyb1Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
    ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries

/-- CO25 Claim 5.22.
`Δ(Hyb_1, Hyb_2) ≤ θ★ · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}` with `Hyb_1 / Hyb_2` sampled
eagerly via `section58Hyb1Dist` / `section58Hyb2Dist`. -/
def claim_5_22
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (tₕ tₚ tₚᵢ : ℕ) :
    Prop :=
  tvDist
      (section58Hyb1Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
      (section58Hyb2Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
    ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ (εcodec := codec.decodingBias)

/-- CO25 Claim 5.23.
`Δ(Hyb_2, Hyb_3) = 0`. The paper distinguishes encoded vs. decoded query format only;
distributions are identical (`φ_i` injective). Stated as exact equality (= 0), matching
the paper's "perfect indistinguishability" wording. -/
def claim_5_23
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    Prop :=
  tvDist
      (section58Hyb2Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
      (section58Hyb3Dist (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver) = 0

/-- CO25 Claim 5.24.
`Δ(Hyb_3, Hyb_4) ≤ (7·L·(2t_h+2+2t_p+L+2t_{p⁻¹})) / (2·|Σ|^c) − 5·(L+1) / |Σ|^c`.
`Hyb_3` and `Hyb_4` use the *same* eager salted FS oracle (`section58SaltedFiatShamirDist`,
matching CO25 line 1784); only the prover/verifier algorithm differs. -/
def claim_5_24
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
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
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
      (hyb4Dist (δ := δ) (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        oSpecImpl V maliciousProver d2sAlgo)
    ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries

/-- Public theorem surface for CO25 Claim 5.21. -/
theorem claim_5_21_holds
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (tₕ tₚ tₚᵢ : ℕ) :
    claim_5_21 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver tₕ tₚ tₚᵢ := by
  sorry

/-- Public theorem surface for CO25 Claim 5.22. -/
theorem claim_5_22_holds
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (tₕ tₚ tₚᵢ : ℕ) :
    claim_5_22 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver tₕ tₚ tₚᵢ := by
  sorry

/-- Public theorem surface for CO25 Claim 5.23. -/
theorem claim_5_23_holds
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    claim_5_23 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver := by
  sorry

/-- Public theorem surface for CO25 Claim 5.24. -/
theorem claim_5_24_holds
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
    (d2sAlgo : D2SAlgo (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    claim_5_24 (T_H := T_H) (T_P := T_P)
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver d2sAlgo tₕ tₚ tₚᵢ := by
  sorry

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

/-- CO25 §5.4 `D2SAlgo^f` witness for the salted theorem path.
It answers `g_i` by querying the external salted FS oracle `f_i(τ, x, ·)` and lets
`d2sQueryStepWithOracle` apply the `ψ_i⁻¹` preimage sampler. -/
def d2sAlgoSaltedExternal
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
    defaultD2SCodecBridgeWithOracle
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec)
      (fun roundIdx stmt0 salt0 encodedMessages0 => do
        let messagesUpTo ←
          match section58EncodedMessagesUpTo?
              (pSpec := pSpec) (U := U) roundIdx encodedMessages0 with
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
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))
      (QueryImpl.id oSpec)
      (d2sQueryImplCoreWithOracle
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) params)
  let outWithState :
      OptionT (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
        ((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
    (simulateQ d2sOuterImpl P).run default
  do
    let out? ← outWithState.run
    pure (out?.map Prod.fst)

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- CO25 Theorem 5.1 (Main lemma §5.8, canonical existential form).
For every malicious prover `𝒫̃` making at most `t_h` queries to `h` and `t_p` / `t_{p⁻¹}`
queries to `p / p⁻¹`, there exist a D2SAlgo prover transform and a D2STrace line-4 map
such that:
```
|Pr[𝒱^{h,p}(𝕩,π)=1] − Pr[𝒱_std^f(𝕩,π)=1]| ≤ η★(t_h, t_p, t_{p⁻¹})
```
and D2SAlgo makes at most `θ★(t_h, t_p, t_{p⁻¹}) = t_p` total queries.

Sampling shape (CO25 Def. 4.2 / Eqs. 15/52/54/4): both sides draw their oracles
from `OracleDistribution` carriers at game start; the ambient `oSpec` is answered by
the caller-supplied handler `oSpecImpl`. Left: `oSpecImpl` plus
`𝒟_𝔖(λ,n) = duplexSpongeOracleDistribution` for `(h, p, p⁻¹)`. Right: `oSpecImpl` plus
salted `𝒟_IP(λ,n) = section58SaltedFiatShamirDist` for `f`.

The distance component is supplied by the public claim theorem surfaces
`claim_5_21_holds`, `claim_5_22_holds`, `claim_5_23_holds`, and `claim_5_24_holds`.
The remaining `sorry` is the shape bridge from those internal hybrid-game distributions to this
`mappedDuplexSpongeFiatShamirGameDist` / `basicFiatShamirGameDist` form, plus the query-bound
component for the chosen `D2SAlgo`. -/
theorem lemma_5_1
    [DecidableEq U] [DecidableEq StmtIn] [DecidableEq ι]
    {T_H : Type} {T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge) :
    ∃ (d2sAlgo : D2SAlgo (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (d2sTrace :
        QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
          DSAbort U
            (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec))),
      ∀ (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)),
      IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ →
      tvDist -- 1/2 ∑ |p(i) - q(i)|
         -- hybrid 0 ((h, p, p⁻¹) ← 𝒟_𝔖)
        (mappedDuplexSpongeFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U)
          (init := section58Hyb0Init (StmtIn := StmtIn) (U := U))
          (impl := section58Hyb0Impl
            (oSpec := oSpec) (StmtIn := StmtIn) (U := U) oSpecImpl)
          V maliciousProver d2sTrace)
        -- hybrid 4 (f ← 𝒟_IP_salted)
        (basicFiatShamirGameDist
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec)
          (section58ChallengeInit
            (challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec)
            (section58SaltedFiatShamirDist
              (StmtIn := StmtIn) (U := U) (pSpec := pSpec) (δ := δ)))
          (section58ChallengeImpl
            (oSpec := oSpec) (U := U)
            (challengeSpec := fsChallengeOracle (Vector U δ × StmtIn) pSpec)
            oSpecImpl
            (section58SaltedFiatShamirDist
              (StmtIn := StmtIn) (U := U) (pSpec := pSpec) (δ := δ)))
          V (d2sAlgo maliciousProver))
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
            (εcodec := codec.decodingBias) : ℝ)
      ∧ OracleComp.IsTotalQueryBound (d2sAlgo maliciousProver) (θStar tₕ tₚ tₚᵢ) := by
  refine ⟨?_, ?_, ?_⟩
  · use d2sAlgoSaltedExternal
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  · use stdTraceSingleSalted
      (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  · intro maliciousProver hMaliciousBound
    let _ := hTp
    let _ := hMaliciousBound
    sorry

end KeyLemma

end DuplexSpongeFS.KeyLemma
