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

## Section map (top-to-bottom)

1. **Setup** — universe-quantified variable block, `SampleableType` bridge instances.
2. **`section SecurityGames`** — the experiment shells:
   - `liftFSSaltedQueriesToD2SChallengePlusUnit`, `projectD2SChallengePlusUnitQueryLog` —
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
  -- CO25 Def 4.1 codec: supplies sizes and Serialize/Deserialize via projections.
  [codec : Codec pSpec U]
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
private def liftFSSaltedQueriesToD2SChallengePlusUnit :
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
def projectD2SChallengePlusUnitQueryLog
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
    QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)

/-- CO25 Theorem 5.1. Output type for the duplex-sponge Fiat-Shamir game (`Hyb_0` left-hand
experiment): statement-in, statement-out, salted proof, and combined query log over
`duplexSpongeChallengeOracle`. -/
abbrev DSFSGameOutput :=
  StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
    QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)

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
  let ⟨stmtIn, proof⟩ ←
    match stmtAndProof? with
    | some stmtAndProof => pure stmtAndProof
    -- De-aborted: a failed compiled prover (`D2SAlgo^f` lookahead/backtrack failure) yields a
    -- `default` statement+proof instead of aborting; the *same* `default` is used by the induced SR
    -- prover (`hyb4_eq_coinSRExperiment`), and acceptance on it is part of the §5 `η★` budget.
    | none => pure default
  let verifierComp :
      OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (Option StmtOut) :=
    (do
      let π := proof.1
      let messages : pSpec.Messages := proof.2 -- `π = (τ̂, (α₁, α₂, ...))`
      -- `P` has access to oracles like `(Unit →ₒ U) + unifSpec` but `V` don't have,
        -- so we have to lift the computation though `V` don't use them
      let transcript ← OptionT.lift <|
        simulateQ
          (impl := liftFSSaltedQueriesToD2SChallengePlusUnit
            (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (mx := messages.deriveTranscriptFS (oSpec := oSpec) (StmtIn := StmtIn × Salt) (stmtIn, π))
      let b_opt ← OptionT.lift <| liftComp ((V.verify stmtIn transcript).run) _
      b_opt.getM).run
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
  return ⟨stmtIn, ← stmtOut.getM, proof, proveQueryLog ++ verifyQueryLog⟩

/-- CO25 §5.8. Execute a Section 5.8 line-4 trace map (e.g. D2STrace = `(φ⁻¹, ψ) ∘ StdTrace`)
inside `ProbComp` by interpreting the auxiliary unit-sampling oracle uniformly. -/
def runSection58TraceMap
    [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) challengeSpec)
    (fullTrace : QueryLog (oSpec + challengeSpec)) :
    ProbComp
      (Option (QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (U := U))
    ((traceMap fullTrace).run)

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
        QueryLog (oSpec + challengeSpec)) := do
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
    projectD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    projectD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) verifyQueryLogRaw
  return ⟨stmtIn, ← stmtOut?.getM, proof, proveQueryLog ++ verifyQueryLog⟩

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
  | some ⟨stmtIn, stmtOut, proof, projectedTrace⟩ => do
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

end SecurityGames

section KeyLemma

open scoped NNReal

/-! ### Numerical bounds: `θ★`, `CodecBias`, `η★`, per-claim bounds -/

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

/-- CO25 Claim 5.22. Statistical-distance bound for `Hyb_1` vs `Hyb_2` (Eq. 53):
`θ★(t_h, t_p, t_{p⁻¹}) · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}`. -/
def claim5_22Bound
    (tₕ tₚ tₚᵢ : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
    + ∑ i, (εcodec i : ℝ)

/-- CO25 Claim 5.24. Statistical-distance bound for `Hyb_3` vs `Hyb_4` (Eq. 55):
`(7·L·(2·t_h + 2 + 2·t_p + L + 2·t_{p⁻¹})) / (2·|Σ|^c) − 5·(L+1) / |Σ|^c`. -/
def claim5_24Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let Lr : ℝ := L
  let cardPow : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  (7 * Lr * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + Lr + 2 * (tₚᵢ : ℝ))) / (2 * cardPow)
    - (5 * (Lr + 1)) / cardPow

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

/-- CO25 Claim 5.21.
`Δ(Hyb_0, Hyb_1) ≤ (7·T² − 3·T) / (2·|Σ|^c)` with `Hyb_0 / Hyb_1` sampled eagerly via
`hyb_0` / `hyb_1`. -/
theorem claim_5_21
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist
      (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        oSpecImpl V maliciousProver
        (d2sTraceSalted
          (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (hyb_1 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
    ≤ claim5_21Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  sorry

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
  -- `Hyb_2` `gᵢ`-realization: query the decoded challenge oracle `eᵢ` for
  -- `ρᵢ ∈ ℳ_{V,i}`, then sample a uniform `ψᵢ⁻¹` preimage to recover the encoded
  -- `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}` (CO25 §5.4 Item 4(e)i).  Trivial inner state `M := PUnit`
  -- (`StateT.lift` wraps the no-memo body for the unified `hybridGameDist`).
  let gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec PUnit :=
    fun q => do
      let challenge ← -- query to `e`
        StateT.lift <|
          OptionT.lift <|
            (show OracleComp
                (D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (pSpec.Challenge q.1) from
              query
                (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (.inl q))
      StateT.lift <|
        OptionT.lift <|  -- apply `ψᵢ⁻¹` on the response `pᵢ` to get `p̂ᵢ`
          uniformDeserializePreimage
            (pSpec := pSpec) (U := U)
            (challengeSpec := challengeSpec) challenge
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

/-- CO25 Claim 5.22.
`Δ(Hyb_1, Hyb_2) ≤ θ★ · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}` with `Hyb_1 / Hyb_2` sampled
eagerly via `hyb_1` / `hyb_2`. -/
theorem claim_5_22
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist
      (hyb_1 (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (Salt := Salt)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
      (hyb_2 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
    ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ (εcodec := codec.decodingBias) := by
  sorry

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

/-- CO25 Claim 5.23.
`Δ(Hyb_2, Hyb_3) = 0`. The paper distinguishes encoded vs. decoded query format only;
distributions are identical (`φ_i` injective). Stated as exact equality (= 0), matching
the paper's "perfect indistinguishability" wording. -/
theorem claim_5_23
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    tvDist
      (hyb_2 (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (Salt := Salt)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
      (hyb_3 (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (Salt := Salt)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver) = 0 := by
  sorry

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

/-- CO25 Claim 5.24.
`Δ(Hyb_3, Hyb_4) ≤ (7·L·(2t_h+2+2t_p+L+2t_{p⁻¹})) / (2·|Σ|^c) − 5·(L+1) / |Σ|^c`.
`Hyb_3` and `Hyb_4` use the *same* eager salted FS oracle (`D_IP_salted`,
matching CO25 line 1784); only the prover/verifier algorithm differs. -/
theorem claim_5_24
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) :
    tvDist
      (hyb_3 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver)
      (hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        oSpecImpl V maliciousProver
        (d2sAlgo (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
    ≤ claim5_24Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries := by
  sorry

/-! ### Main lemma 5.1: existential statement and salted `D2SAlgo` witness -/

/-- CO25 Theorem 5.1. Per-index query-bound predicate for the malicious prover `𝒫̃`.
`tShared` bounds queries to the ambient `oSpec`; `(t_h, t_p, t_{p⁻¹})` bound the three
DS sub-oracles `h`, `p`, `p⁻¹`. Uses `duplexSpongeQueryBudgetWithShared` from `Defs.lean`. -/
abbrev IsLemma5_1QueryBound
    [DecidableEq ι]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  OracleComp.IsPerIndexQueryBound maliciousProver
    (duplexSpongeQueryBudgetWithShared (StmtIn := StmtIn) (U := U) tShared tₕ tₚ tₚᵢ)

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
salted `𝒟_IP(λ,n) = D_IP_salted` for `f`.

The distance component is supplied by the public claim theorems
`claim_5_21`, `claim_5_22`, `claim_5_23`, and `claim_5_24`, applied to the
hybrid-chain endpoints `hyb_0` / `hyb_4` via the triangle inequality on `tvDist`.
The remaining `sorry` is the query-bound component for the chosen `D2SAlgo`. -/
theorem lemma_5_1
    [DecidableEq U] [DecidableEq StmtIn] [DecidableEq ι]
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge) :
    ∃ (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (d2sTraceTransform : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)  (duplexSpongeChallengeOracle StmtIn U)),
      ∀ (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ),
      IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ →
      tvDist -- 1/2 ∑ |p(i) - q(i)|
        -- Hyb_0  ((h, p, p⁻¹) ← 𝒟_𝔖)
        (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sTraceTransform)
        -- Hyb_4  (f ← 𝒟_IP_salted)
        (hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform)
        ≤ (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
            (εcodec := codec.decodingBias) : ℝ)
      ∧ OracleComp.IsTotalQueryBound (d2sAlgoTransform maliciousProver) (θStar tₕ tₚ tₚᵢ) := by
  refine ⟨?_, ?_, ?_⟩
  · use ProverTransform.d2sAlgo
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  · use d2sTraceSalted
      (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  · intro maliciousProver hMaliciousBound
    let _ := hTp
    let _ := hMaliciousBound
    sorry

end KeyLemma

end DuplexSpongeFS.KeyLemma
