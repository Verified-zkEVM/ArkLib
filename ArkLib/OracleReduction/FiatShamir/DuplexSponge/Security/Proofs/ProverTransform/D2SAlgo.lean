/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ProverTransform.Query
public import Mathlib.Data.List.Sigma
public import VCVio.EvalDist.FiniteSupport
public import ArkLib.VCVioStaging.OracleComp.Constructions.SampleableType
import all VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Prover transformation: codec bridge, `D2SAlgo` and query counting

[CO25, §5.4]: the codec bridge `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`, its `tr_i` memo, the `D2FQueryProver` /
`d2sAlgo` split (paper Eq. (19)), the `gSpec`-query counting for `d2sQueryStep`, and the
distribution of the unit samplers.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open Backtrack Lookahead DSTraceStorage TraceTransform

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]
  {δ : Nat}

local instance : Inhabited U := ⟨0⟩

noncomputable section

/-! ## Codec bridge `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`

[CO25, §5.4, Eq. (19)] — Translates `d2sQueryOracles` into `fsChallengeOracle`-based queries:
- `.inl` (`gSpec`): `φ⁻¹` (decode prefix) → `f` (query FS oracle) → `ψ⁻¹` (uniform preimage)
- `.inr` (`(Unit →ₒ U) + unifSpec`): identity passthrough

The `OptionT` layer models `φ⁻¹` parse failure (⊥ on malformed encoded-message prefixes). -/

section CodecBridge

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- Steps 1–2 of the codec bridge (`fᵢ ∘ φᵢ⁻¹`): parse the encoded prover prefix and issue
the `fᵢ`-query at the decoded key, returning the decoded verifier message `ρᵢ`.

Given the components of a `gSpec` query `(i, 𝕩, τ̂, α̂₁, …, α̂ᵢ)` (salt already binarized to
`τ̌ : Salt`):
1. `φ⁻¹`: parse `α̂_{<i}` → `α_{<i}` via `hybEncodedProverMessagesBefore?` (⊥ on failure)
2. `f`: query `fᵢ(𝕩, τ̌, α₁, …, αᵢ)` → `ρᵢ ∈ ℳ_{V,i}` via `fsChallengeOracle`
   keyed at the pre-encoded salt `Salt` (paper's `{0,1}^{δ⋆}`; bridge =
   `SaltCodec.encode = bin`)

Shared by `d2sCodecBridgeImpl` (which follows it with the `ψ⁻¹` preimage sampling) and by
`d2sCodecBridgeImplMemo`'s hit path (which discards the — fixed-table, hence identical —
answer and returns the cached `ρ̂ᵢ`), so that every `gᵢ`-call issues exactly one logged
`fᵢ`-query regardless of memo state. -/
noncomputable def d2sCodecBridgeParseAndQueryF
    (roundIdx : pSpec.ChallengeIdx) (stmt : StmtIn) (encodedSalt : Salt)
    (encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc) :
    OptionT (OracleComp
      (D2SVerifierMessagePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)))
      (pSpec.Challenge roundIdx) := do
  -- Step 1 (`φ⁻¹`) — decode prover prefix: `(α_1, …, α_{i-1}) := φ⁻¹(α̂_1, …, α̂_{i-1})`;
  -- abort if any block lies outside `Im(φ_ι)`.
  let messagesBefore ←
    match hybEncodedProverMessagesBefore?
        (pSpec := pSpec) (U := U) roundIdx encodedProverMessages with
    | some messagesBefore => pure messagesBefore
    | none => failure
  -- Step 2 (`f`) — query the FS oracle at the binarized salt:
  --   `ρ_i := f_i(𝕩, τ̌, α_1, …, α_{i-1}) ∈ ℳ_{V,i}`.
  OptionT.lift <|
    (show OracleComp
        (D2SVerifierMessagePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec))
        (pSpec.Challenge roundIdx) from
      query
        (spec := D2SVerifierMessagePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec))
        (.inl ⟨roundIdx, ((stmt, encodedSalt), messagesBefore)⟩))

/-- **[CO25, Eq. (19)]** `gᵢ`-summand of the codec bridge: `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`.

Given a `gSpec` query `(i, 𝕩, τ̂, α̂₁, …, α̂ᵢ)`:
1. `φ⁻¹`: parse `α̂_{<i}` → `α_{<i}` via `hybEncodedProverMessagesBefore?` (⊥ on failure)
2. `f`: query `fᵢ(𝕩, bin(τ̂), α₁, …, αᵢ)` → `ρᵢ ∈ ℳ_{V,i}` via `fsChallengeOracle`
   keyed at the pre-encoded salt `Salt` (paper's `{0,1}^{δ⋆}`; bridge =
   `SaltCodec.encode = bin`)
3. `ψ⁻¹`: sample `ρ̂ᵢ ← 𝒰(ψᵢ⁻¹(ρᵢ))` via `uniformDeserializePreimage`

Steps 1–2 are `d2sCodecBridgeParseAndQueryF`. -/
noncomputable def d2sCodecBridgeImpl :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (OptionT (OracleComp
        (D2SVerifierMessagePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)))) :=
  fun q =>
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    do
      -- Steps 1–2 (`f ∘ φ⁻¹`) — parse the prefix and query the FS oracle.
      let verifierMessage ←
        d2sCodecBridgeParseAndQueryF
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (Salt := Salt)
          roundIdx stmt (SaltCodec.encode (Salt := Salt) salt) encodedProverMessages
      -- Step 3 (`ψ⁻¹`) — uniform preimage: `ρ̂_i ←$ ψ_i⁻¹(ρ_i) ⊆ Σ^{ℓ_V(i)}`.
      OptionT.lift <|
        uniformDeserializePreimage
          (pSpec := pSpec) (U := U)
          (verifierMessageSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
          verifierMessage

end CodecBridge

/-! ## `D2SAlgoMemo` — `tr_i` memo for the codec bridge [CO25, §5.4 D2SAlgo Item 3]

The unconditional `gᵢ` query in `D2SQuery` Item 4(e)i (see `d2sHandleBacktrackSome`) means
that two adversary queries with the same `BacktrackOutput` produce two `gᵢ` queries with the
same encoded key in the resulting `OracleComp` tree. Without a memo at the bridge layer, the
randomness in `uniformDeserializePreimage` (the `ψ⁻¹` step) would give them different
answers, violating the determinism of [CO25, §5.4 D2SAlgo Item 3] on repeat keys.

`D2SAlgoMemo` is the `tr_i : (i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i` table the paper threads through
the bridge as a `StateT` layer over `d2sCodecBridge`. On a cache hit, the `f`-query is still
issued (per-call trace granularity — see `d2sCodecBridgeImplMemo`'s docstring) but the stored
`ρ̂_i` is returned; on a miss, `d2sCodecBridgeImpl` is invoked and the result is appended. -/

section D2SAlgoMemo

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- **[CO25, §5.4]** D2SAlgo Item 3 — entry of the bridge-layer memo `tr_i`, keyed on the
encoded `gᵢ` query `(i, 𝕩, τ̂, α̂_1, …, α̂_i)` with **binarized** salt `τ̂ := bin(τ) ∈ Salt`
(paper `{0,1}^{δ⋆}`; see Item 3c/3f), carrying the sampled encoded answer
`ρ̂_i ∈ Σ^{ℓ_V(i)}` (the `ψ⁻¹` preimage of the basic-FS verifier message). -/
structure D2SAlgoMemoEntry
    (StmtIn : Type) (U : Type) (δ : ℕ) (Salt : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Salt
  encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc
  response : Vector U (verifierMessageSize (pSpec := pSpec) roundIdx)

/-- **[CO25, §5.4]** D2SAlgo Item 3: the `tr_i` table, indexed by `gᵢ`-query keys with binarized
salt. -/
abbrev D2SAlgoMemo (StmtIn : Type) (U : Type) (δ : ℕ) (Salt : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] :=
  List (D2SAlgoMemoEntry StmtIn U δ Salt pSpec)

instance {StmtIn' U' Salt' : Type} {δ' n' : ℕ} {pSpec' : ProtocolSpec n'}
    [HasProverMessageSize pSpec'] [HasVerifierMessageSize pSpec'] :
    Inhabited (D2SAlgoMemo StmtIn' U' δ' Salt' pSpec') := ⟨[]⟩

open Classical in
/-- **[CO25, §5.4]** D2SAlgo Item 3 — `tr_i[(i, 𝕩, τ̂, α̂_1, …, α̂_i)]`, returning `some ρ̂_i` if
the encoded key was previously stored. Salt key is the **binarized** `τ̂ : Salt` (paper Item 3c). -/
noncomputable def lookupD2SAlgoMemo
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Salt)
    (encodedProverMessages : pSpec.EncodedProverMessagesBefore U i.1.castSucc) :
    Option (Vector U (verifierMessageSize (pSpec := pSpec) i)) :=
  memo.foldl (init := none) fun acc entry =>
    acc.orElse fun _ =>
      if hRound : entry.roundIdx = i then by
        subst hRound
        exact
          if entry.stmt = stmt ∧ entry.salt = salt ∧
              entry.encodedProverMessages = encodedProverMessages
            then some entry.response
            else none
      else none

/-- **[CO25, §5.4]** D2SAlgo Item 3 — append a fresh `(key, ρ̂_i)` entry to `tr_i`. -/
def insertD2SAlgoMemo
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (entry : D2SAlgoMemoEntry StmtIn U δ Salt pSpec) :
    D2SAlgoMemo StmtIn U δ Salt pSpec :=
  memo ++ [entry]

/-- **[CO25, §5.4]** D2SAlgo Item 3 — memoized `gᵢ`-summand of the codec bridge.

Wraps `d2sCodecBridgeImpl` in a `StateT (D2SAlgoMemo …)` layer. On `lookupD2SAlgoMemo` hit,
re-runs the deterministic `φ⁻¹` parse and **re-issues the `fᵢ`-query at the decoded key**
(via `d2sCodecBridgeParseAndQueryF`; the answer — from the same fixed table — is discarded)
and returns the stored `ρ̂ᵢ` without resampling `ψ⁻¹` and without touching the memo; on miss,
invokes the unmemoized bridge and appends the result via `insertD2SAlgoMemo`.

**Logging rationale.** The paper's Item 3a stores-and-skips: a repeated key is answered from
`tr_i` with no new `f`-query. The formalization's §5.8 traces are `List`-valued query logs
with order and multiplicity, and `Hyb_1`/`Hyb_2` realize `gᵢ` by querying their fixed table
`g`/`e` **on every call** — one logged verifier message entry per `gᵢ`-call. If the hit path here
skipped the `f`-query, `Hyb_3`/`Hyb_4` (both of which use this bridge) would log one entry
per *distinct* key instead, and a replay adversary distinguishes the hybrids through trace
multiplicity alone (Claim 5.23 becomes false as formalized). Re-issuing the `f`-query on a
hit keeps per-call trace granularity uniform across `Hyb_1`–`Hyb_4` while the cached `ρ̂ᵢ` still
enforces Item 3's answer determinism — the observable answer behavior is exactly the paper's,
since `f` is a fixed table.

This is also exactly the convention of D2SAlgo Steps 1–2: the Step-1 oracle query is made even
when the key is already memoized, so every invocation of the callback — repeated complete
encoded keys included — issues its `fᵢ` oracle query. -/
noncomputable def d2sCodecBridgeImplMemo :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (fsChallengeOracle (StmtIn × Salt) pSpec)
      (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun q =>
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    -- Paper Item 3c — binarize `τ̂ := bin(τ) ∈ Salt` once before memo lookup/insert.
    let encodedSalt : Salt := SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) salt
    do
      let memo ← get
      match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
          memo roundIdx stmt encodedSalt encodedProverMessages with
      -- Item 3 cache hit: `tr_i[(i, 𝕩, τ̂, α̂_1, …, α̂_i)] = some ρ̂_i` ⇒ re-issue the `f`-query
      -- (deterministic `φ⁻¹` parse + fixed-table `f`; answer discarded, no `ψ⁻¹` resample,
      -- no memo update) and return the stored `ρ̂_i` — see the docstring's logging rationale.
      | some response => do
          let _ ←
            (d2sCodecBridgeParseAndQueryF
                (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (Salt := Salt)
                roundIdx stmt encodedSalt encodedProverMessages :
              OptionT (OracleComp _) _)
          pure response
      | none =>
          -- Item 3 cache miss: invoke `ψ⁻¹∘f∘φ⁻¹` to sample `ρ̂_i`,
          --   then `tr_i := tr_i ∪ {(i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i}`.
          let response ←
            (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
              (Salt := Salt) q :
              OptionT (OracleComp _) _)
          modify (fun m =>
            insertD2SAlgoMemo
              (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec) m
              { roundIdx := roundIdx, stmt := stmt, salt := encodedSalt,
                encodedProverMessages := encodedProverMessages, response := response })
          pure response

end D2SAlgoMemo

/-! ## `d2fProverRaw` — shared `𝒜^{D2SQuery^{gImpl}}` inner pipeline

Raw post-`simulateQ` shape of the paper Eq. (19) RHS prover loop, keeping the two state layers
(`D2SQueryState`, inner `M`) so different call sites can project differently:
- `D2FQueryProver` projects via `Prod.fst ∘ Prod.fst` — drops both states, used by Hyb_4.
- `KeyLemma.hybridGame` keeps the triple — uses `D2SQueryState` for the verifier-half
  continuation and threads `M` (paper Item 3 `tr_i`) from prover to verifier, matching
  [CO25, §5.4 D2SAlgo Item 3] ("`tr_i` is global to a single run").

Polymorphic over `M` (`PUnit` for Hyb_1;
`D2SAlgoMemo …` for Hyb_2 / Hyb_3 / Hyb_4's memoized replies) and `verifierMessageSpec` (`gSpec` /
`eSpec` / `fsChallengeOracle (StmtIn × Salt) pSpec` per-hybrid). Single source of truth for
the `outerImpl := QueryImpl.addLift (QueryImpl.id oSpec) (d2sQueryImpl gImpl auxImpl)`
construction. -/

section D2FProverRaw

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- **[CO25, §5.4]** Outer-spec `QueryImpl` for the paper Eq. (19) RHS oracle wrapper:
`id_oSpec ⊕ D2SQuery^{gImpl}`. Reused by `d2fProverRaw` and by `KeyLemma.hybridGame`'s
verifier-half (which re-runs the same `QueryImpl` against the honest verifier with the
shared `M` state threaded in — paper §5.4 D2SAlgo Item 3, `tr_i` global to a single run). -/
noncomputable def d2fOuterImpl
    {κ : Type} {verifierMessageSpec : OracleSpec κ}
    {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) verifierMessageSpec M) :
    QueryImpl (oSpec + duplexSpongeOracle StmtIn U)
      (StateT (D2SQueryState StmtIn pSpec U δ T_H T_P)
        (StateT M
          (OptionT
            (OracleComp
              (oSpec + D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec))))) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := gImpl)
      (auxImpl := fun aux =>
        query
          (spec := D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec)
          (Sum.inr aux)))

/-- Run a simulated computation from explicit outer D2SQuery and inner oracle states.
The verifier phase resumes both states returned by the prover. -/
noncomputable def d2fRawFrom
    {α : Type}
    {κ : Type} {verifierMessageSpec : OracleSpec κ}
    {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) verifierMessageSpec M)
    (comp : OracleComp (oSpec + duplexSpongeOracle StmtIn U) α)
    (initD2S : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (initM : M) :
    AbortComp (oSpec + D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec)
        ((α × D2SQueryState StmtIn pSpec U δ T_H T_P) ×
          M) :=
  (((simulateQ (d2fOuterImpl (T_H := T_H) (T_P := T_P) gImpl) comp).run initD2S).run initM)

/-- Fresh-outer-state wrapper for standalone computations and the initial prover phase. -/
noncomputable def d2fRaw
    {α : Type}
    {κ : Type} {verifierMessageSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) verifierMessageSpec M)
    (comp : OracleComp (oSpec + duplexSpongeOracle StmtIn U) α)
    (initM : M) :
    AbortComp (oSpec + D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec)
        ((α × D2SQueryState StmtIn pSpec U δ T_H T_P) ×
          M) :=
  d2fRawFrom (T_H := T_H) (T_P := T_P) gImpl comp default initM

end D2FProverRaw

/-! ## `D2FQueryProver` + `d2sAlgo` — paper Eq. (19) split

[CO25, §5.4] D2SAlgo decomposes into two structurally distinct pieces:

- **Items 1-3** = the inner prover loop running `𝒜^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper Eq. (19)
  RHS). Output salt stays on the DS side (`Vector U δ`, paper `Σ^δ`). Mirrored in Lean by
  `D2FQueryProver` returning `DSFSTypedNARGString`.
- **Items 4-6** = parse `(τ, αᵢ)`, set `τ̌ := bin(τ) ∈ {0,1}^{δ⋆}`, repackage as
  `π̌ := (τ̌, αᵢ)`. This is a pure post-processing wrapper that re-encodes the salt to the
  FS-standard side. Mirrored in Lean by `d2sAlgo`, which applies `SaltCodec.encode = bin`
  to the salt-component of `D2FQueryProver`'s output, returning `FSSaltedNARGString`.

The split makes paper Figure 4 lines 2-3 explicit at the type level:
- Hyb_3 prover surface `𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` outputs DS-form salt → `D2FQueryProver`.
- Hyb_4 prover surface `D2SAlgo^f(𝒫̃)` outputs FS-std-form salt → `d2sAlgo`.

Both share the same oracle-first pipeline:
1. `d2sQueryImpl` simulates the duplex-sponge verifier message oracle into the encoded spec
   `d2sQueryOracles = gSpec + (Unit + unifSpec)`.
2. `d2sCodecBridgeImplMemo` translates `gSpec` queries into basic-FS `fsChallengeOracle` queries
   with `uniformDeserializePreimage`, threading the `tr_i` memo [CO25, §5.4 D2SAlgo Item 3] so
   that repeat encoded keys reuse the cached `ρ̂_i`; the `(Unit + unifSpec)` summand passes
   through unchanged.
3. The result lives in the basic-FS target spec
   `oSpec + D2SVerifierMessagePlusUnitOracle fsChallengeOracle`, matching `D2SAlgo`'s return monad.
   Both intermediate states (`D2SQueryState`, `D2SAlgoMemo`) are discarded. -/

section D2SAlgo

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- **[CO25, Eq. (19)]** The inner prover surface `𝒜^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper
D2SAlgo Items 1-3); "D2F" abbreviates duplex-to-FS. Runs `𝒜` with its duplex-sponge
`(h, p, p⁻¹)` queries answered by `D2SQuery` under the codec-bridged oracle `ψ⁻¹∘f∘φ⁻¹`, where
`f` is the salted FS verifier message oracle keyed at `(StmtIn × Salt)`. Salt is bridged via
`SaltCodec.encode = bin` inside `d2sCodecBridgeImpl` at every `gᵢ`-query; the `tr_i` memo
(Item 3) is threaded via `d2sCodecBridgeImplMemo`.
**Output salt stays on the DS side (`Vector U δ`, paper `Σ^δ`)** — this is the paper-Hyb_3
prover surface, before the bin-repackaging of D2SAlgo Items 4-6. -/
noncomputable def D2FQueryProver
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SVerifierMessagePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :=
  -- Shared raw pipeline: id_oSpec ⊕ D2SQuery^{tr_i-memoized ψ⁻¹∘f∘φ⁻¹}, single `simulateQ`,
  -- both states `default`-initialized. Strip `D2SQueryState` and `D2SAlgoMemo` at the
  -- boundary; `none` propagates as `OptionT` abort.
  Prod.fst <$> Prod.fst <$> -- DTOP the states (from the two nested StateT)
    (d2fRaw (T_H := T_H) (T_P := T_P)
      (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt))
      𝒜 default)

/-- **[CO25, Eq. (19)]** Full `D2SAlgo^f(𝒜)` (paper Items 1-6). Thin
wrapper over `D2FQueryProver` (Items 1-3) that applies the paper's Items 4-6 post-processing:
parse the inner output `(τ, αᵢ)` with `τ ∈ Σ^δ`, set `τ̌ := bin(τ) = SaltCodec.encode τ`,
and repackage as `(τ̌, αᵢ) : FSSaltedNARGString`.
**Output salt is the pre-encoded FS-std type `Salt` (paper `{0,1}^{δ⋆}`)** — this is the
paper-Hyb_4 prover surface, ready to be consumed by `𝒱_std^f` (`Verifier.compileFiatShamir`)
without any further bin step. -/
noncomputable def d2sAlgo
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SVerifierMessagePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedNARGString pSpec Salt) := do
  -- Items 1-3 — run inner prover to obtain `(𝕩, (τ, (α̂_1, …, α̂_n))) ∈ StmtIn ×
  -- DSFSTypedNARGString`.
  let ⟨stmt, ⟨τ, msgs⟩⟩ ← D2FQueryProver (Salt := Salt) (T_H := T_H) (T_P := T_P) 𝒜
  -- Items 4-6 — re-encode salt: `τ̌ := bin(τ) ∈ {0,1}^{δ⋆}`; emit `(𝕩, (τ̌, α̂))`.
  return ⟨stmt, ⟨SaltCodec.encode (Salt := Salt) τ, msgs⟩⟩

end D2SAlgo

/-! ## `gSpec`-query counting for `d2sQueryStep` ([CO25, Lemma 5.1] `θ★` accounting)

[CO25, §5.4] emits a `gᵢ`-query only at Item 4(e)i, i.e. only while handling a
**permutation** query whose `BackTrack` fired `.some` with an in-image tuple.  The lemmas
below make that structural fact available to the Claim 5.22 / Lemma 5.1 query accounting:
`d2sQueryStep` makes at most one `gSpec` query per permutation query and none for
hash or inverse-permutation queries. -/

section QueryCounting

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]

/-- `gSpec`-slot queries of the `d2sQueryOracles` surface ([CO25, Item 4(e)i] emissions). -/
def isGSpecQuery :
    (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred
    (isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := fun t =>
  match t with
  | .inl _ => Decidable.isTrue trivial
  | .inr _ => Decidable.isFalse fun h => h

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [SpongeSize] in
@[simp]
lemma isGSpecQuery_inl (t : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) (.inl t) := trivial

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [SpongeSize] in
@[simp]
lemma not_isGSpecQuery_inr (t : ((Unit →ₒ U) + unifSpec).Domain) :
    ¬ isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) (.inr t) :=
  fun h => h

/-- Permutation queries of the duplex-sponge verifier message surface (`dsPermQuery`). -/
def isDSForwardPermQuery : (duplexSpongeOracle StmtIn U).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

instance : DecidablePred (isDSForwardPermQuery (StmtIn := StmtIn) (U := U)) := fun t =>
  match t with
  | .inl _ => Decidable.isFalse fun h => h
  | .inr (.inl _) => Decidable.isTrue trivial
  | .inr (.inr _) => Decidable.isFalse fun h => h

section StepCount

-- Specialize the shared masked-query induction from `Query` to count `gSpec` slots.

open OracleComp

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [DecidableEq StmtIn] [DecidableEq U] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [∀ i, Fintype (pSpec.Message i)] [SpongeSize] in
lemma isG_d2sSampleVector (m : ℕ) :
    IsQueryBoundP
      (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)
      (isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) 0 :=
  isQueryBoundP_d2sSampleVector_of_aux _ not_isGSpecQuery_inr m

omit [DecidableEq StmtIn] [DecidableEq U] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [∀ i, Fintype (pSpec.Message i)] in
lemma isG_d2sSampleCapacity :
    IsQueryBoundP
      (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) 0 :=
  isG_d2sSampleVector _

omit [DecidableEq StmtIn] [DecidableEq U] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [∀ i, Fintype (pSpec.Message i)] in
lemma isG_d2sRateBlocksFromVerifierMessage
    {i : pSpec.ChallengeIdx} (verifierMessage : Vector U (verifierMessageSize (pSpec := pSpec) i)) :
    IsQueryBoundP
      (d2sRateBlocksFromVerifierMessage (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        verifierMessage)
      (isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) 0 :=
  isQueryBoundP_d2sRateBlocksFromVerifierMessage_of_aux _ not_isGSpecQuery_inr verifierMessage

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U] in
/-- **[CO25, §5.4]** Per-step `gᵢ`-query count: one `d2sQueryStep` makes at most one
`gSpec`-query, and only when dispatching a permutation query (Item 4(e)i); hash and
inverse-permutation queries never reach the `gᵢ` oracle. -/
theorem isQueryBoundP_gSpec_run_d2sQueryStep
    (q : (duplexSpongeOracle StmtIn U).Domain)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P) :
    IsQueryBoundP
      (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)
      (isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (if isDSForwardPermQuery (StmtIn := StmtIn) (U := U) q then 1 else 0) := by
  have h := isQueryBoundP_d2sQueryStep_mask
    (isGSpecQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    not_isGSpecQuery_inr 1 (fun out _ => by
      unfold d2sQueryG
      exact isQueryBoundP_liftM_query' _ fun _ => one_pos) q st
  rcases q with _ | _ | _ <;> exact h

end StepCount

end QueryCounting

/-! ## §5.4 unit-sampler shape and distribution

`d2sSampleCapacity` (Item 2(b)) and `d2sSampleState` (Items 3(b)/4(d)ii) draw their units one at
a time through the `Unit →ₒ U` slot, sampling the head unit **first** and `push`ing it as the
**last** vector entry — the opposite order to the `SampleableType (Vector U m)` instance.  The
lemmas below expose that shape and show the resulting distribution is nevertheless exactly
uniform on `Vector U m`.

They live in this file because `d2sSampleVector` / `d2sSampleArrayExact` are `private`.

Consumer: `hyb3_hyb4_indistinguishability`'s per-index freshness budgets
(`probEvent_uniformSample_vector_mem`
and friends) are stated for `$ᵗ (Vector U m)`; `evalDist_simulateQ_d2sSampleCapacity` /
`_d2sSampleState` transport them onto the actual §5.4 samplers. -/

section SamplerDistribution

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [SampleableType U]

open OracleComp

/-- The §5.4 unit-vector sampler, head-first / push-last, as a public recursion. -/
def d2sIidVector :
    (m : Nat) →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (Vector U m)
  | 0 => pure #v[]
  | m + 1 => do
      let u ← query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (Sum.inr (Sum.inl ()))
      let v ← d2sIidVector m
      pure (v.push u)

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [SampleableType U] [SpongeSize] in
/-- The §5.4 vector sampler is the head-first/push-last iid unit sampler. -/
lemma d2sSampleVector_eq_d2sIidVector (m : Nat) :
    d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m
      = d2sIidVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [d2sSampleVector, d2sSampleArrayExact, d2sIidVector, bind_assoc, pure_bind,
        d2sSampleUnit] at *
      rw [← ih]
      simp only [bind_assoc, pure_bind]
      rfl

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [SampleableType U] in
/-- **[CO25, §5.4]** Item 2(b) — the capacity sampler is the head-first/push-last iid unit
sampler. -/
theorem d2sSampleCapacity_eq_d2sIidVector :
    d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      = d2sIidVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.C :=
  d2sSampleVector_eq_d2sIidVector _

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [SampleableType U] in
/-- **[CO25, §5.4]** Items 3(b)/4(d)ii — the state sampler is the head-first/push-last iid unit
sampler. -/
theorem d2sSampleState_eq_d2sIidVector :
    d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      = d2sIidVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.N :=
  d2sSampleVector_eq_d2sIidVector _

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [SpongeSize] in
/-- **The §5.4 unit-vector sampler is uniform.**  Under any `ProbComp` realization that answers
the `Unit →ₒ U` slot uniformly, `d2sIidVector m` is distributed exactly as `$ᵗ (Vector U m)`,
despite drawing its units in the opposite order to the `SampleableType` instance.
Definitional unfolding of the VCVio `SampleableType (Vector α (m+1))` sampler gives the
tail-vector-first order; the shared uniformity law handles the reversed draw order. -/
theorem evalDist_simulateQ_d2sIidVector
    (impl : QueryImpl (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      ProbComp)
    (hunit : impl (Sum.inr (Sum.inl ())) = ($ᵗ U : ProbComp U)) (m : ℕ) :
    (letI : MeasurableSpace (Vector U m) := ⊤;
      𝒟[simulateQ impl (d2sIidVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)]
        = 𝒟[($ᵗ (Vector U m) : ProbComp _)]) := by
  have hsampler : ∀ k, d2sIidVector (U := U) (StmtIn := StmtIn)
      (pSpec := pSpec) (δ := δ) k = Vector.replicateRevM
        (query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ)) (Sum.inr (Sum.inl ()))) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [d2sIidVector, Vector.replicateRevM, ih]
      rfl
  rw [hsampler]
  let : MeasurableSpace (Vector U m) := ⊤
  let : MeasurableSpace (Vector
      ((d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Range
        (Sum.inr (Sum.inl ()))) m) := ⊤
  change 𝒟[simulateQ' impl (Vector.replicateRevM
    (query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn)
      (pSpec := pSpec) (δ := δ)) (Sum.inr (Sum.inl ()))) m)] = _
  rw [Vector.map_replicateRevM]
  simpa only [simulateQ'_apply, simulateQ_HasQuery_query, hunit] using
    (OracleComp.evalDist_replicateRevM_uniform (U := U) m)

end SamplerDistribution

end

end DuplexSpongeFS.ProverTransform

/-! ## Native first-match memo correspondence -/

namespace DuplexSpongeFS.ProverTransform

variable {StmtIn U Salt : Type} {n δ : ℕ} {pSpec : ProtocolSpec n}
  [Codec pSpec U]

/-- The complete encoded bridge key with its binarized salt. -/
abbrev D2SAlgoMemoKey (StmtIn U Salt : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [HasProverMessageSize pSpec] :=
  (i : pSpec.ChallengeIdx) × StmtIn × Salt × pSpec.EncodedProverMessagesBefore U i.1.castSucc

/-- A memo entry viewed as a native dependent association-list entry. -/
def D2SAlgoMemoEntry.toSigma (entry : D2SAlgoMemoEntry StmtIn U δ Salt pSpec) :
    (key : D2SAlgoMemoKey StmtIn U Salt pSpec) × Vector U (verifierMessageSize key.1) :=
  ⟨⟨entry.roundIdx, entry.stmt, entry.salt, entry.encodedProverMessages⟩, entry.response⟩

variable [DecidableEq StmtIn] [DecidableEq U]

open Classical in
/-- The unchanged left-biased runtime fold is the native dependent first-match lookup. -/
theorem lookupD2SAlgoMemo_eq_dlookup (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Salt)
    (msgs : pSpec.EncodedProverMessagesBefore U i.1.castSucc) :
    lookupD2SAlgoMemo memo i stmt salt msgs =
      (memo.map D2SAlgoMemoEntry.toSigma).dlookup ⟨i, stmt, salt, msgs⟩ := by
  classical
  induction memo using List.reverseRecOn with
  | nil => rfl
  | append_singleton memo entry ih =>
    simp only [lookupD2SAlgoMemo, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_append, List.map_cons, List.map_nil, List.dlookup_append]
    change (lookupD2SAlgoMemo memo i stmt salt msgs).orElse _ = _
    rw [ih]
    cases (memo.map D2SAlgoMemoEntry.toSigma).dlookup ⟨i, stmt, salt, msgs⟩ with
    | some response => rfl
    | none =>
      rcases entry with ⟨j, stmt', salt', msgs', response⟩
      by_cases hround : j = i
      · subst j
        simp only [Option.orElse_none, Option.none_or, D2SAlgoMemoEntry.toSigma,
          List.dlookup, ↓reduceDIte]
        by_cases hkey : stmt' = stmt ∧ salt' = salt ∧ msgs' = msgs
        · obtain ⟨rfl, rfl, rfl⟩ := hkey
          simp
        · simp [hkey]
      · have hkey : (⟨j, stmt', salt', msgs'⟩ : D2SAlgoMemoKey StmtIn U Salt pSpec) ≠
            ⟨i, stmt, salt, msgs⟩ := fun h => hround (congrArg Sigma.fst h)
        simp [hround, D2SAlgoMemoEntry.toSigma, List.dlookup, hkey]

/-- Successful lookup identifies a complete stored entry without requiring distinct keys. -/
theorem mem_of_lookupD2SAlgoMemo_eq_some
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    {i : pSpec.ChallengeIdx} {stmt : StmtIn} {salt : Salt}
    {msgs : pSpec.EncodedProverMessagesBefore U i.1.castSucc}
    {response : Vector U (verifierMessageSize (pSpec := pSpec) i)}
    (hlookup : lookupD2SAlgoMemo memo i stmt salt msgs = some response) :
    (⟨i, stmt, salt, msgs, response⟩ : D2SAlgoMemoEntry StmtIn U δ Salt pSpec) ∈ memo := by
  classical
  rw [lookupD2SAlgoMemo_eq_dlookup] at hlookup
  have hmem := List.of_mem_dlookup (a := (⟨i, stmt, salt, msgs⟩ :
      D2SAlgoMemoKey StmtIn U Salt pSpec))
    (l := memo.map D2SAlgoMemoEntry.toSigma) hlookup
  obtain ⟨entry, he, hs⟩ := List.mem_map.mp hmem
  cases entry
  cases hs
  exact he

end DuplexSpongeFS.ProverTransform
