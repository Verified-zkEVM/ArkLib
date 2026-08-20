/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Preliminaries
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedForward
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule
import ArkLib.OracleReduction.FiatShamir.SingleSalt
import ArkLib.ToVCVio.Tactic.VCVNorm
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Lemma 5.1 of the Chiesa-Orrù paper

This file provides the legacy executable Section 5 key-lemma interface:
- the DSFS and basic-FS game experiments,
- canonical abstractions for `D2SAlgo` and the Section 5.8 trace algorithms, and
- a statistical-distance theorem surface used by the existing Section 6 interfaces.

The authoritative revised Section 5 statements are in
`Security.Statement.ConcreteHybrids`: they carry the explicit `Section5Nonempty` scope and use
the stateful verifier count `N_𝒱 = verifierPermCallCount pSpec δ`.  This legacy file remains a
compatibility surface while the executable hybrid refinements are migrated.  In particular, its
open proof bodies are not evidence that the revised paper claims have been proved here.

`StmtIn` is the Lean stand-in for the paper's hash-input space `{0,1}^{≤n}`. The paper's
instance-size bound is fixed by choosing this type, while `n` in this file is the protocol round
count from `pSpec : ProtocolSpec n`. Likewise, `codec.decodingBias` abstracts the paper's
`ε_cdc,i(λ,n)` values for the fixed ambient parameter instantiation.

The full hybrid proof from Section 5.8 is still staged across the other Section 5 files.

## Reading guide (CO25 Section 5.8 hybrid chain)

The file follows the paper's Section 5.8 layout. The five hybrid distributions, the four
claims bounding consecutive TV distances, and the main lemma appear in the same order as
in the paper:

```
Hyb_0  DSFS               (h,p,p⁻¹) ← 𝒟_𝔖           ── Claim 5.21 ─▶
Hyb_1  encoded  `g`       g ← 𝒟_Σ                   ── Claim 5.22 ─▶
Hyb_2  decoded  `e`       e ← 𝒟_e                   ── Claim 5.23 ─▶ (= 0)
Hyb_3  salted FS `f`      f ← 𝒟_IP_salted           ── Claim 5.24 ─▶
Hyb_4  basic FS           f ← 𝒟_IP_salted (same f, different algos)
```

Triangle-inequality sum of the four claim bounds gives `η★` (CO25 Eq. 57), the headline
error bound of `lemma_5_1`.

**Stateful-replay correction.** Every permutation-side caller in this file supplies the canonical
exact count `verifierPermCallCount pSpec δ = N_𝒱`, not a rounded salted schedule budget.  The
obsolete lower bound `tₚ ≥ max{Lₚ,Lᵥ}` has been removed: the transformed prover's standard-oracle
queries are charged directly to source forward-permutation queries.

## Section map (top-to-bottom)

1. **Setup** — universe-quantified variable block, `SampleableType` bridge instances.
2. **`section SecurityGames`** — the experiment shells:
   - `liftFSSaltedQueriesToD2SChallengePlusUnit`, `filterD2SChallengePlusUnitQueryLog` —
     spec plumbing between basic-FS and wide D2S spec.
   - `BasicFiatShamirGameOutput`, `DSFSGameOutput` — output types.
   - `basicFiatShamirGame`, `dsfsGame` — paper game bodies.
   - `D2SAlgo`, `runSection58TraceMap` — §5.4 reduction and §5.8 line-4 trace map runners.
   - `hybChallengeInit` / `hybChallengeImpl` — common eager-sample challenge
     handler shared by `Hyb_1`/`Hyb_2`/`Hyb_3`/`Hyb_4`.
   - `hyb0Init` / `hyb0Impl` — DSFS-side `(h,p,p⁻¹)` handler for `Hyb_0`.
   - `hybridGame` — the common Figure 4 skeleton (lines 2–3).
   - `hybridGameDist`, `basicFiatShamirGameDist`, `dsfsGameDist`,
     `mappedDSFSGameDist` — game-to-`ProbComp` distribution wrappers.
3. **`section KeyLemma`** — numerical bounds, hybrid chain interleaved with per-step claims,
   main lemma:
   - **Bounds**: `θ★`, `CodecBias`, `η★`, `tvDist_hybridChain4` (triangle helper),
     `claim5_2{1,2,4}Bound`.
   - **Hybrid chain (paper order)**: `hyb_0` → `hyb_1` → `claim_5_21` → `hyb_2` →
     `claim_5_22` → `hyb_3` → `claim_5_23` → `hyb_4` → `claim_5_24`.
   - **Main lemma**: `IsLemma5_1QueryBound`, `lemma_5_1`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction.OracleDistribution

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)]
  -- Revised CO25 Def 4.1 interface: the Section 5 game surface needs only encoding, decoding,
  -- and the stated decoding-bias condition.  Total decoder fibres are isolated in legacy
  -- lemmas below and are not an assumption of the revised games or Lemma 5.1.
  [codec : CodecCore pSpec U]
  {δ : Nat}
  -- Pre-encoded salt type used by FS-standard side (paper's `{0,1}^{δ⋆}`); bridged from the
  -- on-sponge `Vector U δ` salt via `SaltCodec.encode = bin` (CO25 line 1188 / line 1729).
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section SecurityGames

/-! ### Spec plumbing — lift verifier queries and project auxiliary log entries -/

/-- Simple query impl lift:
Lift salted basic-FS verifier queries into the external `f_i` oracle plus D2S auxiliary
sampling oracles used by `D2SAlgo^f`.  Salt is the pre-encoded type `{0,1}^{δ⋆}` (paper). -/
def liftFSSaltedQueriesToD2SChallengePlusUnit :
    QueryImpl (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      (OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  fun q =>
    match q with
    | .inl qShared =>
        query
          (spec := oSpec +
            D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
          (Sum.inl qShared)
    | .inr qFS =>
        query
          (spec := oSpec +
            D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
          (Sum.inr (Sum.inl qFS))

/-- CO25 §5.8. Project out the auxiliary unit-sampling queries from logs over
`oSpec + (challengeSpec + Unit →ₒ U)`, retaining only shared and challenge entries. -/
def filterD2SChallengePlusUnitQueryLog
    {κ : Type} {challengeSpec : OracleSpec κ}
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :
    QueryLog (oSpec + challengeSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr (.inl q), r⟩ => some ⟨.inr q, r⟩
    | ⟨.inr (.inr _), _⟩ => none

/-! ### Game output types and game bodies (`Hyb_0` / `Hyb_4`) -/

/-- CO25 Theorem 5.1. Output type for the salted basic Fiat-Shamir game (`Hyb_4`):
`(b, 𝕩, π = (τ̌, messages), tr)` where
- `τ̌ = bin (τ) ∈ {0,1}^{δ⋆}`
- `tr` is the combined query log over the salted `fsChallengeOracle (StmtIn × Salt) pSpec`
-/
abbrev BasicFiatShamirGameOutput :=
  StmtIn × StmtOut × FSSaltedProof pSpec Salt ×
    TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)

/-- CO25 Theorem 5.1. Output type for the duplex-sponge Fiat-Shamir game (`Hyb_0` left-hand
experiment): statement-in, statement-out, salted proof, and combined query log over
`duplexSpongeChallengeOracle`. -/
abbrev DSFSGameOutput :=
  StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
    TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)

/-- CO25 Theorem 5.1. The basic-FS verifier `𝒱_std^f` as a standalone computation: derive the FS
transcript from the salted proof — routing `fsChallengeOracle` queries into the wide
`D2SChallengePlusUnitOracle` spec via `liftFSSaltedQueriesToD2SChallengePlusUnit`, lifting the
`V.verify` call (which uses only `oSpec`) the same way — and return the optional output statement.
Factored out of `basicFiatShamirGame` so the `hyb4_eq` log-strip treats it opaquely; it equals
the FS-NARG verifier `fsSaltedVerify` routed through the same lift (the `hyb4_eq` verifier part). -/
def basicFSVerifierComp (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtAndProof : StmtIn × FSSaltedProof pSpec Salt) :
    OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (Option StmtOut) :=
  -- `𝒱_std^f` IS the FS-NARG verifier `fsSaltedVerify`, with ALL its queries (the
  -- `deriveTranscriptFS` challenge queries AND the `oSpec`-only `V.verify` queries) routed into the
  -- wide spec by the single relabel `liftFSSaltedQueriesToD2SChallengePlusUnit`.  Defining it this
  -- way (not routing `deriveTranscriptFS` and `V.verify` separately) makes the `hyb4_eq` verifier
  -- collapse a one-liner: `simulateQ Hyb₄ (basicFSVerifierComp V p) = simulateQ ⟨Hyb₄ ∘ₛ liftFS⟩
  -- (fsSaltedVerify …).run` by `simulateQ_compose` + infra lemma 2.
  simulateQ
    (liftFSSaltedQueriesToD2SChallengePlusUnit
      (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    ((fsSaltedVerify (Salt := Salt) V stmtAndProof.1 stmtAndProof.2).run)

/-- CO25 Theorem 5.1. Right-hand game for Lemma 5.1 (the basic-FS game).
Runs `𝒱_std^f` against the compiled prover `D2SAlgo^f(𝒫̃~)`.
- Prover outputs `(𝕩, (τ̌, messages))`
- Verifier queries `f` at `(𝕩, τ̌, messages)`
-/
def basicFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
  (P : AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt)) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  let ⟨stmtAndProof?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle P).run
  -- De-aborted via `getD default` bound to a *single, non-destructured* `let` (project with
  -- `.1`/`.2` below) — crucially NOT `let ⟨stmtIn, proof⟩ := …`, since the pair-destructure floats
  -- `getD`'s `some/none` match out and duplicates the verifier into both branches, blocking the
  -- `hyb4_eq` log-strip.  A failed compiled prover yields `default` statement+proof; the same
  -- `default` is used by the induced SR prover (`nargInducedProver`); acceptance on it is in `η★`.
  let stmtAndProof := stmtAndProof?.getD default
  let verifierComp :
      OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (Option StmtOut) := basicFSVerifierComp V stmtAndProof
  let ⟨stmtOut, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp).run
  let proveQueryLog :=
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) verifyQueryLogRaw
  let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
  let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
  return ⟨stmtAndProof.1, ← stmtOut.getM, stmtAndProof.2, taggedP ++ taggedV⟩

/-- Revised Section 5 absorbing basic-FS endpoint.

Unlike the legacy `basicFiatShamirGame`, a failure of the compiled D2S prover is not replaced by
a default statement/proof.  The game stops before constructing or running the standard verifier.
This is the endpoint required by the revised Claims 5.23--5.24: an out-of-image codec answer or
an underlying D2S search failure cannot create later verifier-oracle occurrences.  The legacy
game remains available for older soundness developments whose error accounting explicitly uses
the default-proof convention. -/
def basicFiatShamirGameAbsorbing (V : Verifier oSpec StmtIn StmtOut pSpec)
  (P : AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt)) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  let ⟨stmtAndProof?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle P).run
  let stmtAndProof ← stmtAndProof?.getM
  let verifierComp :
      OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (Option StmtOut) := basicFSVerifierComp V stmtAndProof
  let ⟨stmtOut, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp).run
  let proveQueryLog :=
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) verifyQueryLogRaw
  let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
  let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
  return ⟨stmtAndProof.1, ← stmtOut.getM, stmtAndProof.2, taggedP ++ taggedV⟩

/-- CO25 Theorem 5.1. Left-hand game for Lemma 5.1 (the DSFS game).
Runs `𝒱^{h,p}` against the malicious prover `𝒫̃~` (this is `Hyb_0`).
- Prover outputs `(𝕩, (τ, messages))`
- Verifier queries `h, p` only (no `p⁻¹` per Figure 4 line 3)
-/
def dsfsGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  let ⟨⟨stmtIn, proof⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  -- Type-level CO25 Figure 4 line 3 (`𝒱^{h,p}`): the narrow forward-only verifier is built and
  -- `liftComp`-ed to the wide spec via `runForwardVerifierWide`; the subsequent
  -- `simulateQ loggingOracle` emits a wide-spec query log with no `p⁻¹` entries from `V`.
  let verifyCompWide := runForwardVerifierWide δ V stmtIn proof
  let ⟨stmtOut, verifyQueryLog⟩ ← liftM (simulateQ loggingOracle verifyCompWide).run
  let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
  let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
  return ⟨stmtIn, ← stmtOut.getM, proof, taggedP ++ taggedV⟩

/-- CO25 §5.8. Execute a Section 5.8 line-4 trace map (e.g. D2STrace = `(φ⁻¹, ψ) ∘ StdTrace`)
inside `ProbComp` by interpreting the auxiliary unit-sampling oracle uniformly. -/
def runSection58TraceMap
    [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) challengeSpec)
    (fullTrace : TaggedQueryLog (oSpec + challengeSpec)) :
    ProbComp
      (Option (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U] in
/-- The unit-sampled public D2STrace is the output projection of its lossless execution.  This
is the local Hyb₀ line-4 refinement; it uses the same fiber samples on both sides. -/
lemma runD2sTraceSaltedObserved_map_output_eq_runSection58TraceMap
    [SampleableType U]
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    Option.map (fun observation : TraceTransform.D2STraceSaltedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) (Salt := Salt) => observation.output) <$>
        simulateQ (d2sUnitSampleImpl (U := U))
          ((TraceTransform.d2sTraceSaltedObserved
            (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log).run) =
      runSection58TraceMap
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (TraceTransform.d2sTraceSalted
          (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) log := by
  rw [← ToVCVio.VCVNorm.simulateQ_optionT_map]
  rfl

/-! ### Common eager-sample handler for `Hyb_1` / `Hyb_2` / `Hyb_3` / `Hyb_4` -/

/-- CO25 §5.8. Sampler for the §5.8 hybrid experiment carrier: draws one realization from the
chosen challenge-oracle distribution `D_chal` (paper `𝒟_Σ` / `𝒟_e` / `𝒟_IP_salted`).  The
sampled carrier is then held fixed by `hybChallengeImpl` for the entire game run, matching
the paper's "sample at start, then answer queries deterministically" semantics. -/
def hybChallengeInit
    {κ : Type} {challengeSpec : OracleSpec κ}
    (D_chal : OracleReduction.OracleDistribution challengeSpec) :
    ProbComp D_chal.Carrier :=
  D_chal.sample

/-- CO25 §5.8. Stateless 4-slot query handler for the §5.8 hybrid experiment: ambient `oSpec`
queries → caller-supplied `oSpecImpl`; challenge queries → `D_chal.toImpl k_chal` (paper
`𝒟_Σ` / `𝒟_e` / `𝒟_IP_salted`); auxiliary unit queries → `d2sUnitSampleImpl` (fresh per
call); auxiliary `unifSpec` queries → ambient `ProbComp` uniform sampling.  The `D_chal`
carrier is read from the state but never mutated — sampled once by `hybChallengeInit`
and held fixed (CO25 Eq. 15 / Eq. 52 / Eq. 54).  The paper has no ambient distribution; we
take an arbitrary `QueryImpl oSpec ProbComp` instead, which the caller specializes (e.g. to
the empty spec for paper fidelity). -/
def hybChallengeImpl
    [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (D_chal : OracleReduction.OracleDistribution challengeSpec) :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT D_chal.Carrier ProbComp) :=
      -- the sampled oracle function is embedded into StateT as `D_chal.Carrier` type
  fun q => do
    let kC : D_chal.Carrier ← get
    match q with
    | .inl (qShared : ι) =>
        let resp ← StateT.lift <| oSpecImpl qShared
        pure resp
    | .inr (.inl (qChal : κ)) => -- `κ`
        let resp ← StateT.lift <| D_chal.toImpl kC qChal
        pure resp
    | .inr (.inr (.inl (qUnit : Unit))) => -- (Unit →ₒ U) => alphabet sampling, e.g. in LookAhead
        let resp ← StateT.lift <| d2sUnitSampleImpl (U := U) qUnit
        pure resp
    | .inr (.inr (.inr (qUnif : ℕ))) => -- unifSpec => default from ProbComp, we adopt it for `ψ⁻¹`
        let resp ← StateT.lift <|
          (show ProbComp (unifSpec.Range qUnif) from
            query (spec := unifSpec) qUnif)
        pure resp

/-! ### DSFS-side handler for `Hyb_0` -/

/-- CO25 §5.8 Hyb_0. Sampler for the DSFS-side experiment carrier: draws one realization of
`(h, p)` from the duplex-sponge oracle distribution `𝒟_𝔖` (CO25 Def. 4.2).  The carrier is
held fixed by `hyb0Impl` for the entire game run. -/
def hyb0Init :
    ProbComp (duplexSpongeOracleDistribution StmtIn U).Carrier :=
  (duplexSpongeOracleDistribution StmtIn U).sample

/-- CO25 §5.8 Hyb_0. Stateless query handler for the DSFS-side experiment: ambient `oSpec`
queries → caller-supplied `oSpecImpl`; duplex-sponge queries (`h`, `p`, `p⁻¹`) →
`𝒟_𝔖.toImpl k_DS`.  `k_DS` is sampled once at game start by `hyb0Init` and held
fixed (CO25 Def. 4.2).  The paper has no ambient distribution; we take an arbitrary
`QueryImpl oSpec ProbComp` instead. -/
def hyb0Impl
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (duplexSpongeOracleDistribution StmtIn U).Carrier ProbComp) :=
  fun q =>
    match q with
    | .inl qShared => do
        let resp ← StateT.lift <| oSpecImpl qShared
        pure resp
    | .inr qDS =>
        (D_𝔖 StmtIn U).eagerImpl qDS

/-! ### Common hybrid game skeleton (Figure 4 lines 2–3) -/

/-- CO25 §5.8. Common hybrid game skeleton (Figure 4 lines 2–3): run `𝒫̃^{D2SQuery^g}` and
`𝒱^{D2SQuery^g}` exposing only the chosen external challenge-oracle family, then project
away the auxiliary unit-sampling randomness. Polymorphic over the **inner state type `M`**
that `gImpl` carries beneath `D2SQuery`'s own `StateT (D2SQueryState …)` layer:

- `Hyb_1` / `Hyb_2`: trivial inner state `M := PUnit` (no memo — pass `StateT.lift ∘ oldGImpl`).
- `Hyb_3` (paper §5.4 D2SAlgo Item 3): `M := D2SAlgoMemo …`. The `tr_i` memo is
  **initialized fresh at the start of the prover run** and **passed forward to the verifier
  run** (same `d2fRaw` pipeline), so a repeated encoded `gᵢ` key reuses the
  cached `ρ̂_i` — paper's "`tr_i` is global to a single run of `D2SAlgo`".

For `M := PUnit`, the threaded state is vacuous and the body collapses to the plain
no-memo skeleton; for `M := D2SAlgoMemo …`, threading realizes the paper's
`𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper Eq. 16 RHS), mirroring `D2FQueryProver` in
`ProverTransform.lean`. -/
def hybridGame
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
        TaggedQueryLog (oSpec + challengeSpec)) := do
  -- D2SQuery wraps gImpl, layering `StateT (D2SQueryState …)` on top. Built once via the
  -- Prover: fresh `D2SQueryState`, fresh inner state `M`. The post-run inner state is
  -- exposed via the outer `StateT M` layer so it can be threaded into the verifier.
  let proverComp := d2fRaw (T_H := T_H) (T_P := T_P) gImpl P default
  let ⟨proverTriple?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle proverComp.run).run
  -- De-aborted (consistent with `basicFiatShamirGame`): on `gImpl` compilation failure, take a
  -- `default` statement/proof and inner state instead of aborting.  We extract only the *needed*
  -- components (each `Inhabited`) — the full `d2fRaw` triple is not `Inhabited`, so `pure default`
  -- on the whole triple would not typecheck (`default : AbortComp …` is `OptionT.fail`, an abort).
  let ⟨stmtIn, proof, memo₁⟩ :=
    match proverTriple? with
    | some ⟨⟨⟨stmtIn, proof⟩, _⟩, memo₁⟩ => (stmtIn, proof, memo₁)
    | none => (default, default, default)
  -- Type-level CO25 Figure 4 line 3 (`𝒱^{h,p}`): the narrow forward-only verifier is built and
  -- `liftComp`-ed to the wide spec, via `runForwardVerifierWide`.
  let rawVerifierComp := runForwardVerifierWide δ V stmtIn proof
  -- Verifier: fresh `D2SQueryState` (independent run) but **shares inner state `memo₁`**
  -- with the prover (CO25 §5.4 D2SAlgo Item 3 — paper `tr_i` is global to a single run;
  -- for `M := PUnit` this threading is vacuous). Uses `d2fRaw` to share the same monadic
  -- pipeline as the prover (only differing in `initM`).
  let verifierComp := d2fRaw (T_H := T_H) (T_P := T_P) gImpl rawVerifierComp memo₁
  -- V has same simulated (h,p,p⁻¹) oracle access via `D2SQuery^{gImpl}` as P~.
  let ⟨verifierTriple?, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp.run).run
  -- De-aborted likewise: on verifier-side compilation failure, treat it as a verifier *reject*
  -- (`stmtOut? := none`) rather than aborting the game. `Option StmtOut` is `Inhabited` (`none`),
  -- so this needs no `Inhabited StmtOut`. The genuine verifier-reject is still the `getM` below.
  let stmtOut? :=
    match verifierTriple? with
    | some ⟨⟨stmtOut?, _⟩, _⟩ => stmtOut?
    | none => none
  let proveQueryLog :=
    filterD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    filterD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) verifyQueryLogRaw
  let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
  let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
  return ⟨stmtIn, ← stmtOut?.getM, proof, taggedP ++ taggedV⟩

/-! ### Distribution wrappers (game → `ProbComp`) -/

/-- CO25 §5.8. Distribution of a Section 5.8 hybrid game after applying its line-4 trace map
(Figure 4 line 4: `tr := (φ⁻¹,ψ)(tr_𝒫̃ ‖ tr_𝒱)` or `φ⁻¹(…)` or identity).  Collapses the
hybrid game output to `BasicFiatShamirGameOutput`, enabling the TV-distance chain of
Claims 5.21–5.24. Polymorphic over the **inner state type `M`** that `gImpl` carries
(trivial `PUnit` for `Hyb_1` / `Hyb_2`; `D2SAlgoMemo …` for `Hyb_3`'s `tr_i` table —
see `hybridGame`). -/
def hybridGameDist -- apply traceMap into output of `hybridGame`
    [SampleableType U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT σ ProbComp))
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) challengeSpec) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := do
  let hybridOutput ←
    (simulateQ impl
      ((hybridGame
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        gImpl V P).run)).run' (← init)
  match hybridOutput with
  | none => return none
  | some (⟨stmtIn, stmtOut, proof, projectedTrace⟩ : (StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ × TaggedQueryLog (oSpec + challengeSpec))) => do
      -- Paper Items 4-6: bridge on-sponge `Vector U δ` salt → FS-std `Salt` via
      -- `SaltCodec.encode = bin` at the hybrid game boundary.
      let π : FSSaltedProof pSpec Salt :=
        (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Salt := Salt)
          traceMap projectedTrace
      match outputFS? with
      | none => -- NOTE: this is for consistency with `mappedDSFSGameDist`,
        -- even though this branch won't be reached in `Hyb₂, Hyb₃, Hyb₄`
        return some (stmtIn, stmtOut, π, [])
      | some fullTraceFS =>
          return some (stmtIn, stmtOut, π, fullTraceFS)

/-- CO25 Theorem 5.1. Distribution of the basic-FS game (`Hyb_4` right-hand side) under a
concrete oracle implementation (oracle family `𝒟_IP`). Used for `hyb_4`. -/
def basicFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt)) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  (simulateQ impl (basicFiatShamirGame (V := V) (Salt := Salt) P)).run' (← init)

/-- Distribution wrapper for the revised absorbing basic-FS endpoint.  It has the same sampler
and result type as `basicFiatShamirGameDist`; only a failed source prover now returns `none`
without evaluating `basicFSVerifierComp`. -/
def basicFiatShamirGameAbsorbingDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt)) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  (simulateQ impl (basicFiatShamirGameAbsorbing (V := V) (Salt := Salt) P)).run' (← init)

/-- CO25 Theorem 5.1. Distribution of the DSFS game (`Hyb_0` left-hand side) under a concrete
oracle implementation (oracle family `𝒟_𝔖`). Used via `mappedDSFSGameDist`. -/
def dsfsGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  (simulateQ impl (dsfsGame (V := V) P)).run' (← init)

/-- CO25 Theorem 5.1. Left experiment of Lemma 5.1 (`Hyb_0`): run the DSFS game under
`𝒟_𝔖(λ,n)` and apply the line-4 trace map D2STrace = `(φ⁻¹, ψ) ∘ StdTrace` to produce a
basic-FS query log. Corresponds to `Pr[𝒱^{h,p}(𝕩, π) = 1]` in the lemma statement. -/
def mappedDSFSGameDist
    [SampleableType U]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  let outputDS ← dsfsGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
  -- should run D2STrace directly in dsfsGameDist?
  match outputDS with
  | none => return none
  | some ⟨stmtIn, stmtOut, proof, fullTraceDS⟩ => do
      -- Paper Items 4-6: bridge on-sponge `Vector U δ` salt → FS-std `Salt` via
      -- `SaltCodec.encode = bin` at the DS→FS boundary on the LHS experiment.
      let π : FSSaltedProof pSpec Salt :=
        (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          traceMap fullTraceDS
      match outputFS? with
      -- Trace-synthesis abort (a sponge bad event) is a distinguished bad-trace value, NOT a
      -- suppressed acceptance: the verifier's `(𝕩, stmtOut)` decision survives. Matches CO25
      -- Hyb₀, where a `tr = ⊥` bad event keeps the acceptance bit `b`; the abort then lives only
      -- in the trace component, inside `tvDist(Hyb₀, Hyb₄) ≤ η★` (Claims 5.21–5.24), rather than
      -- wrongly zeroing the soundness event.
      | none => return some (stmtIn, stmtOut, π, [])
      | some fullTraceFS => return some (stmtIn, stmtOut, π, fullTraceFS)

/-- A lossless observation of the left-hand Section 5.8 experiment.  The existing
`mappedDSFSGameDist` deliberately exposes only the basic-FS output after `D2STrace`; that is the
right public distribution, but it discards the raw duplex trace on which the Hyb₀--Hyb₁
lazy-sampling coupling stops.  This observation keeps that source result while computing exactly
the same public output and applying exactly the same trace-map-abort convention.

The raw source trace is not resampled or reconstructed: when `sourceOutput = some ...`, its
tagged query log is the one actual `dsfsGame` run whose image is `publicOutput`.  Thus a future
coupling can derive its Hyb₀ base trace from this observation without changing the public
experiment. -/
structure MappedDSFSGameObservation where
  sourceOutput : Option (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ))
  publicOutput : Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt))

/-- The raw duplex-sponge base trace of an observed Hyb₀ run.  `sourceOutput` retains the
actual tagged Figure-4 log; this projection discards only ambient-oracle entries and source tags,
exactly as `D2STrace` does before running `StdTrace`.  A source-game abort has no base trace. -/
def MappedDSFSGameObservation.baseTrace
    (observation : MappedDSFSGameObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  match observation.sourceOutput with
  | none => []
  | some ⟨_, _, _, taggedLog⟩ =>
      TraceTransform.dsTraceOfLog
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
        (TaggedQueryLog.untagged taggedLog)

/-- Instrumented Hyb₀ line-4 wrapper.  Projecting `publicOutput` is definitionally the same
control flow as `mappedDSFSGameDist`; the additional `sourceOutput` field retains the actual
pre-`D2STrace` DSFS execution for the stateful lazy-sampling coupling. -/
def mappedDSFSGameDistObserved
    [SampleableType U]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp (MappedDSFSGameObservation (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) := do
  let sourceOutput ← dsfsGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
  match sourceOutput with
  | none => return ⟨none, none⟩
  | some source@⟨stmtIn, stmtOut, proof, fullTraceDS⟩ => do
      let π : FSSaltedProof pSpec Salt :=
        (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (Salt := Salt) traceMap fullTraceDS
      let publicOutput :=
        match outputFS? with
        | none => some (stmtIn, stmtOut, π, [])
        | some fullTraceFS => some (stmtIn, stmtOut, π, fullTraceFS)
      return ⟨some source, publicOutput⟩

/-- Fully instrumented Hyb₀ observation for the concrete corrected `D2STrace` map.  In addition
to the raw source result and public basic-FS output, this retains the exact encoded StdTrace
entries produced with the same random-fiber samples as the public output. -/
structure MappedDSFSGameD2STraceObservation where
  sourceOutput : Option (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ))
  traceObservation : Option (TraceTransform.D2STraceSaltedObservation
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (δ := δ) (Salt := Salt))
  publicOutput : Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt))

/-- The direct duplex trace retained by the lossless Hyb₀ observation.  It is extracted from the
same tagged source-game log that produced the observed transformed output; no trace is recovered
from a decoded standard-FS output. -/
def MappedDSFSGameD2STraceObservation.baseTrace
    (observation : MappedDSFSGameD2STraceObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  match observation.sourceOutput with
  | none => []
  | some ⟨_, _, _, taggedLog⟩ =>
      TraceTransform.dsTraceOfLog
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
        (TaggedQueryLog.untagged taggedLog)

/-- Lossless Hyb₀ wrapper specialized to the public corrected `D2STrace` implementation.  The
branch returning an empty standard trace on transformation abort is deliberately identical to
`mappedDSFSGameDist`; only the successful branch retains `traceObservation.encodedTrace` and
`traceObservation.lookAheadMemo` before projecting its `output`. -/
def mappedDSFSGameDistD2STraceObserved
    [SampleableType U]
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (MappedDSFSGameD2STraceObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) := do
  let sourceOutput ← dsfsGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
  match sourceOutput with
  | none => return ⟨none, none, none⟩
  | some source@⟨stmtIn, stmtOut, proof, fullTraceDS⟩ => do
      let π : FSSaltedProof pSpec Salt :=
        (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
      let traceObservation? ←
        simulateQ
          (d2sUnitSampleImpl (U := U))
          ((TraceTransform.d2sTraceSaltedObserved
            (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            fullTraceDS).run)
      let publicOutput :=
        match traceObservation? with
        | none => some (stmtIn, stmtOut, π, [])
        | some observation => some (stmtIn, stmtOut, π, observation.output)
      return ⟨some source, traceObservation?, publicOutput⟩

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U] in
/-- The fully observed Hyb₀ wrapper is lossless: projecting away its raw source trace and
encoded StdTrace witness recovers the ordinary Hyb₀ line-4 distribution exactly. -/
lemma mappedDSFSGameDistD2STraceObserved_map_publicOutput_eq
    [SampleableType U]
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    (fun observation => observation.publicOutput) <$>
        mappedDSFSGameDistD2STraceObserved
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
          init impl V P =
      mappedDSFSGameDist
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) init impl V P
        (TraceTransform.d2sTraceSalted
          (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  simp only [mappedDSFSGameDistD2STraceObserved, mappedDSFSGameDist, map_eq_pure_bind,
    bind_assoc]
  apply bind_congr
  intro sourceOutput
  cases sourceOutput with
  | none => rfl
  | some source =>
      rcases source with ⟨stmtIn, stmtOut, proof, fullTraceDS⟩
      simp only
      simp only [runSection58TraceMap]
      have hTrace := runD2sTraceSaltedObserved_map_output_eq_runSection58TraceMap
        (δ := δ) (T_H := T_H) (T_P := T_P) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) fullTraceDS
      unfold runSection58TraceMap at hTrace
      have hPost := congrArg (fun traceDistribution =>
        traceDistribution >>= fun outputFS? =>
          match outputFS? with
          | none => pure (some (stmtIn, stmtOut,
              (SaltCodec.encode (Salt := Salt) proof.1, proof.2), []))
          | some fullTraceFS => pure (some (stmtIn, stmtOut,
              (SaltCodec.encode (Salt := Salt) proof.1, proof.2), fullTraceFS))) hTrace
      dsimp at hPost
      rw [bind_map_left] at hPost
      refine Eq.trans ?_ hPost
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro traceObservation?
      cases traceObservation? <;> rfl

end SecurityGames

section KeyLemma

open scoped NNReal

/-! ### Numerical bounds: `θ★`, `CodecBias`, `η★`, per-claim bounds -/

/-- CO25 §5.8 / Eq (57). `θ★(t) := t_p` — forward-permutation query budget of `𝒫̃`, used as the
query-bound multiplier in `η★`. -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-- Select exactly the standard-FS challenge-oracle calls made by the transformed prover.
The outer `oSpec` calls and the auxiliary unit-sampling calls are deliberately excluded: D2SAlgo
passes both through, so a bound on *all* target-spec queries by `thetaStar = t_p` would be false.
This is the Lean formulation of CO25's query bound, which counts calls to the programmed
challenge oracle rather than unrelated ambient or sampling oracles. -/
def isD2SAlgoChallengePoint :
    (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)).Domain → Prop
  | .inl _ => False
  | .inr point => isD2SChallengePoint
      (U := U) (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) point

instance : DecidablePred
    (isD2SAlgoChallengePoint (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (Salt := Salt)) :=
  fun point =>
    match point with
    | .inl _ => isFalse (fun h => h)
    | .inr (.inl _) => isTrue trivial
    | .inr (.inr _) => isFalse (fun h => h)

/-- The query-bound half of Lemma 5.1: D2SAlgo makes at most `thetaStar = t_p`
standard-FS challenge queries.  It intentionally is not a total-query bound over the enlarged
implementation oracle surface. -/
abbrev IsD2SAlgoChallengeQueryBound
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  OracleComp.IsQueryBoundP (d2sAlgoTransform maliciousProver)
    (isD2SAlgoChallengePoint (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (Salt := Salt))
    (θStar tₕ tₚ tₚᵢ)

/-- CO25 Definition 4.1. Per-round codec bias profile `i ↦ ε_{cdc,i}(λ,n)`.
Parameters `(λ, n)` are suppressed (assumed fixed by the ambient instantiation); `CodecBias`
carries only the per-round values `ε_{cdc,i}` used in Claims 5.22 and the `η★` formula. -/
abbrev CodecBias :=
  pSpec.ChallengeIdx → ℝ≥0

/-- CO25 Theorem 5.1 / Eq (57). Additive error bound `η★(t_h, t_p, t_{p⁻¹})`:
```
η★ := numerator / (2 · |Σ|^c) + θ★ · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}
```
where `numerator = 7(t+L)² + … − 13(L+1)` with `t = t_h + t_p + t_{p⁻¹}` and `L` the
**exact** stateful verifier-side forward-permutation count `N_𝒱`.  It is not a rounded salted
schedule ceiling: the stateful replay construction counts actual calls after salt absorption and
partial-rate-block carries.  Sums the four hybrid-step bounds from
Claim 5.21 (Hyb_0 → Hyb_1), the exact reparameterization in Claim 5.22
(Hyb_1 → Hyb_2), and the joint codec/permutation coupling of Claim 5.24
(Hyb_2 → Hyb_4). -/
def ηStar (U : Type) [SpongeUnit U] [Fintype U]
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

/-! ### Triangle-inequality helper for the four-step hybrid chain -/

omit [SpongeSize] in
/-- CO25 §5.8. Four-step hybrid composition bound via triangle inequality.
Combines `tvDist H₀ H₁ ≤ e₀₁`, …, `tvDist H₃ H₄ ≤ e₃₄` into
`tvDist H₀ H₄ ≤ e₀₁ + e₁₂ + e₂₃ + e₃₄`. This remains a generic helper; the
Section 5.8 claim statements below are exposed as public lemma surfaces. -/
lemma tvDist_hybridChain4
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
def claim5_21Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- The codec-mismatch contribution paid once by the joint Claim 5.23/5.24 coupling:
`θ★(t_h, t_p, t_{p⁻¹}) · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}`.

Claim 5.22 itself is the exact Hyb₁/Hyb₂ reparameterization and has distance zero. -/
def claim5_codecBound
    (tₕ tₚ tₚᵢ : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
    + ∑ i, (εcodec i : ℝ)

/-- CO25 Claim 5.24.  The stateful stopped-extension contribution
`D(T,L) = (14(L+1)T + 7(L+1)^2 - 10(L+1))/(2·|Σ|^c)`, where
`T = t_h + t_p + t_{p⁻¹}`.

This is the exact revised-paper quantity.  The former static-offset formula was smaller by
`7T + 7/2` and therefore did not add with Claim 5.21 to `η★`. -/
def claim5_24Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tTotal : ℝ := (tₕ + tₚ + tₚᵢ : ℕ)
  let LplusOne : ℝ := (L + 1 : ℕ)
  let cardPow : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  (14 * LplusOne * tTotal + 7 * LplusOne ^ 2 - 10 * LplusOne) / (2 * cardPow)

/-- The exact arithmetic identity used at the end of the revised Lemma 5.1 proof. -/
lemma claim5_bounds_sum_eq_etaStar
    (tₕ tₚ tₚᵢ L : ℕ) :
    claim5_21Bound U tₕ tₚ tₚᵢ L +
        claim5_codecBound (pSpec := pSpec) tₕ tₚ tₚᵢ codec.decodingBias +
        claim5_24Bound U tₕ tₚ tₚᵢ L =
      ηStar U tₕ tₚ tₚᵢ L codec.decodingBias := by
  simp only [claim5_21Bound, claim5_codecBound, claim5_24Bound, ηStar, θStar]
  push_cast
  ring

/-- DS hash queries in the combined Lemma 5.1 prover surface. -/
def isLemma5_1HashQuery :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

/-- DS forward-permutation queries in the combined Lemma 5.1 prover surface. -/
def isLemma5_1PermQuery :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inr (.inl _)) => True
  | _ => False

/-- DS inverse-permutation queries in the combined Lemma 5.1 prover surface. -/
def isLemma5_1PermInvQuery :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inr (.inr _)) => True
  | _ => False

/-- CO25 Theorem 5.1 query-bound predicate for the malicious prover `𝒫̃`.
The three DS oracle families have aggregate bounds; ambient-oracle queries are unconstrained. -/
abbrev IsLemma5_1QueryBound
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  by
    classical
    exact OracleComp.IsQueryBoundP maliciousProver
        (isLemma5_1HashQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₕ ∧
      OracleComp.IsQueryBoundP maliciousProver
        (isLemma5_1PermQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₚ ∧
      OracleComp.IsQueryBoundP maliciousProver
        (isLemma5_1PermInvQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₚᵢ

/-! ### Hybrid distributions `Hyb_0` … `Hyb_4` and per-step claims 5.21–5.24 (CO25 §5.8)

Each `Hyb_X` is defined immediately before the claim that bounds `Δ(Hyb_X, Hyb_{X+1})`,
mirroring the paper's narrative: introduce both endpoints, bound the gap, advance to the next
hybrid. -/

/-- CO25 §5.8 Hyb_0. `Hyb_0` left-experiment distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
duplex-sponge oracle `(h, p, p⁻¹) ← 𝒟_𝔖(λ,n)` (CO25 Def. 4.2) sampled eagerly via
`duplexSpongeOracleDistribution`. Line-4 trace map = D2STrace = `(φ⁻¹, ψ) ∘ StdTrace`.
Samples `(h, p)` eagerly at game start rather than via a lazy random-oracle cache for `h`. -/
def hyb_0
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) -- (x, π)
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  mappedDSFSGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (Salt := Salt)
    (init := hyb0Init (StmtIn := StmtIn) (U := U))
    (impl := hyb0Impl (oSpec := oSpec) (StmtIn := StmtIn) (U := U) oSpecImpl)
    V maliciousProver (traceMap := traceMap)

/-- CO25 §5.8 Hyb_1. `Hyb_1` distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
encoded challenge oracle
`g := (g_i)_{i ∈ [k]} ← 𝒟_Σ(λ,n)` (CO25 Eq. 15) sampled eagerly via
`D_Sigma`, auxiliary `(Unit →ₒ U)` and `unifSpec` slots handled
inline (fresh per call).

Line-4 trace map is `(φ⁻¹, ψ)(tr_𝒫̃ ‖ tr_𝒱)` (`hyb1Line4Trace`). -/
def hyb_1
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := gSpec (U := U) StmtIn pSpec δ -- implemented via using `g ← D_g`
  let D_g := D_Sigma (U := U) StmtIn pSpec δ
  -- `Hyb_1` `gᵢ`-realization: forward each `gSpec` query straight into the encoded challenge
  -- oracle exposed by `challengeSpec`.  No `ψᵢ⁻¹` step is needed since `challengeSpec`
  -- already returns the encoded `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`.  Trivial inner state `M := PUnit` —
  -- `StateT.lift` adds the vacuous `StateT PUnit` layer required by the unified
  -- `hybridGameDist` skeleton (paper's `tr_i` memo collapses to `()` here).
  let gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec PUnit :=
    fun q =>
      StateT.lift <|
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (Vector U (challengeSize (pSpec := pSpec) q.1)) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl q))
  exact
    hybridGameDist
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := hybChallengeInit (challengeSpec := challengeSpec) D_g)
      (impl := hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_g)
      (gImpl := gImpl) V maliciousProver
      (hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_2. `Hyb_2` distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
decoded challenge oracle
`e := (e_i)_{i ∈ [k]}` (CO25 Eq. 52) sampled eagerly via `section58DecodedChallengeDist`,
auxiliary slots inline. Line-4 trace map is `φ⁻¹(tr_𝒫̃ ‖ tr_𝒱)`
(`hyb2Line4Trace`). -/
def hyb_2
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := eSpec (U := U) StmtIn pSpec δ
  let D_e := D_e (U := U) StmtIn pSpec δ
  letI : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩
  -- `Hyb_2` `gᵢ`-realization: query `eᵢ`, check that its value is in the decoder image, and
  -- sample a uniform partial-fibre representative only on a cache miss.  Under `D_e` that
  -- image test always succeeds; writing it explicitly keeps the executable game faithful to
  -- Claim 5.22 and preserves the repeated-key memo invariant.
  let gImpl := d2sDecodedBridgeImplCacheOfImage
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact
    hybridGameDist
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := hybChallengeInit (challengeSpec := challengeSpec) D_e)
      (impl := hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_e)
      gImpl V maliciousProver
      (hyb2Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_3. `Hyb_3` distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
salted Fiat–Shamir oracle
`f := (f_i)_{i ∈ [k]} ← 𝒟_IP(λ,n)` (CO25 Eq. 54) sampled eagerly via
`D_IP_salted`, auxiliary slots inline. Line-4 trace map is identity
(`hyb3Line4Trace`). -/
def hyb_3
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec
  let D_IP_salted :=
    D_IP_salted (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
  -- `Hyb_3` `gᵢ`-realization (CO25 Eq. 16): `φ⁻¹` parse encoded prefix → query salted
  -- `fᵢ` oracle (keyed at `StmtIn × Salt`, with the on-sponge `Vector U δ` salt
  -- bridged via `SaltCodec.encode = bin`) → `ψᵢ⁻¹` uniform preimage.  The `OptionT`
  -- abort layer carries `φ⁻¹` parse failure (⊥ on malformed encoded-message prefixes).
  -- CO25 §5.4 D2SAlgo Item 3 — paper's `𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` threads a `tr_i` memo
  -- (`d2sCodecBridgeImplMemo`) so repeated encoded `gᵢ` keys reuse the cached `ρ̂_i`; the
  -- unified `hybridGameDist` instantiated at `M := D2SAlgoMemo …` shares that memo between
  -- prover and verifier within one game run (Item 3: `tr_i` is global to a single run of
  -- `D2SAlgo`).
  let gImpl := d2sCodecBridgeImplMemo (δ := δ) (Salt := Salt)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact
    hybridGameDist
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := hybChallengeInit (challengeSpec := challengeSpec) D_IP_salted)
      (impl := hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_IP_salted)
      gImpl V maliciousProver
      (traceMap := hyb3Line4Trace (Salt := Salt) (oSpec := oSpec)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_4. `Hyb_4` right-experiment distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`, salted
Fiat–Shamir oracle `f ← 𝒟_IP(λ,n)` (CO25 line 1784) sampled eagerly via `D_IP_salted` —
the **same** distribution as `Hyb_3`. The proof type `DSSaltedProof = Vector U δ ×
pSpec.Messages` is identical on both sides; the on-sponge `Vector U δ` salt is bridged to
the paper's `{0,1}^{δ⋆}` via `SaltCodec.encode = bin` at the FS-oracle query boundary.

**What actually changes Hyb_3 → Hyb_4 is the verifier's interpretation of `(𝕩, π)`:**

- `Hyb_3` (`hybridGame` instantiated at `M := D2SAlgoMemo …` with
  `gImpl := d2sCodecBridgeImplMemo`): verifier surface is `V.toDSFS δ` (paper `𝒱^{h,p}`)
  reading `π` as a **DSFS proof**, then `liftComp` wide and `d2fRaw` wraps
  its `(h, p)` queries through `D2SQuery^{ψ⁻¹∘f∘φ⁻¹}`.
- `Hyb_4` (`basicFiatShamirGame`): verifier surface is `V.verify` directly on a
  `deriveTranscriptFS`-derived transcript, reading `π` as a **standard FS proof** with
  oracle keyed at `(𝕩, SaltCodec.encode τ)`; queries `f` directly with **no D2SQuery wrap**.

The prover surface is **identical** on both sides (paper Eq. 16): `Hyb_3` uses
`𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` = `D2FQueryProver` (`d2sQueryImpl` composed with the
`tr_i`-memoized bridge `d2sCodecBridgeImplMemo` from CO25 §5.4 D2SAlgo Item 3); `Hyb_4`
uses `D2SAlgo^f(𝒫̃)` = `d2sAlgo`, which is `D2FQueryProver` post-processed by
`SaltCodec.encode` on the salt component (Items 4-6). Both run the same memo-threaded
inner loop, so the response distribution is identical at the prover surface.

The non-zero Claim 5.24 bound comes from the verifier asymmetry only: `Hyb_3`'s verifier
can abort via `D2SQuery` parse failure; `Hyb_4`'s `𝒱_std^f` cannot (no D2SQuery wrap on
V path). The gap is exactly the paper's `Pr[E_𝒱]`. -/
def hyb_4
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Salt := Salt)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  let challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec
  let D_IP_salted :=
    D_IP_salted (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
  basicFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (Salt := Salt)
    (init := hybChallengeInit (challengeSpec := challengeSpec) D_IP_salted)
    (impl := hybChallengeImpl
      (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_IP_salted)
    V (d2sAlgoTransform maliciousProver)

/-- Absorbing basic-FS endpoint parameterized by the compiled prover.  This is the revised-paper
Hyb₄ game: a source-side failure ends the game before the basic verifier is called.  It is kept
separate from legacy `hyb_4`, whose default-proof convention is used by older Section 6
compatibility theorems. -/
def hyb4Absorbing
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Salt := Salt)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  let challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec
  let D_IP_salted :=
    D_IP_salted (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
  basicFiatShamirGameAbsorbingDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (Salt := Salt)
    (init := hybChallengeInit (challengeSpec := challengeSpec) D_IP_salted)
    (impl := hybChallengeImpl
      (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_IP_salted)
    V (d2sAlgoTransform maliciousProver)

/-- Canonical revised-paper Hyb₄ endpoint with `d2sAlgoRevised` as compiled prover. -/
noncomputable def hyb4RevisedAbsorbing
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
    (ProverTransform.d2sAlgoRevised
      (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

end KeyLemma

end DuplexSpongeFS.KeyLemma
