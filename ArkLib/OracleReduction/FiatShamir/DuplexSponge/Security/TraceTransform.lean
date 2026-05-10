/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead

/-!
# Trace Transformations

This file contains the trace transformations for duplex sponge Fiat-Shamir, following CO25
Section 5.5.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.TraceTransform

open Backtrack Lookahead DSTraceStorage

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} [DecidableEq StmtIn]
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)]
  {δ : Nat}

noncomputable section

/-- Section 5.8 `Hyb₁` challenge-oracle surface: encoded prover-prefix queries, encoded verifier
responses.

Per CO25 Eq. 15: `dom_i = {0,1}^≤n × Σ^δ × Σ^{ℓ_P(1)} × … × Σ^{ℓ_P(i)}` — the prover prefix is
*exactly* `i` encoded messages, not an unbounded list. We model this as
`pSpec.EncodedMessagesUpTo U i.1.castSucc`, the dependent function indexed by message rounds
strictly before `i`. With `Fintype` instances for the components this Query is also `Fintype`,
which is required for the eager full-table `OracleDistribution.uniform _` realization. -/
@[inline, reducible]
def section58EncodedChallengeOracleInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    ∀ i, OracleInterface (Vector U (challengeSize (pSpec := pSpec) i)) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedMessagesUpTo U i.1.castSucc
    toOC.spec := fun _ => Vector U (challengeSize (pSpec := pSpec) i)
    toOC.impl := fun _ => read }

/-- Oracle family for the `gᵢ` queries in Section 5.8 `Hyb₁`. -/
@[inline, reducible]
def section58EncodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (section58EncodedChallengeOracleInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [fun i => Vector U (challengeSize (pSpec := pSpec) i)]ₒ'
    (section58EncodedChallengeOracleInterface (U := U) StmtIn pSpec δ)

/-- Section 5.8 `Hyb₂` challenge-oracle surface: encoded prover-prefix queries, decoded verifier
responses.

Same CO25 Eq. 52 prefix shape as `section58EncodedChallengeOracleInterface` (encoded messages
indexed by rounds `< i`); only the response type differs (decoded `pSpec.Challenge i`). -/
@[inline, reducible]
def section58DecodedChallengeOracleInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : Nat) [HasMessageSize pSpec] :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedMessagesUpTo U i.1.castSucc
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

/-- Oracle family for the `eᵢ` queries in Section 5.8 `Hyb₂`. -/
@[inline, reducible]
def section58DecodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) (δ : Nat) [HasMessageSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (section58DecodedChallengeOracleInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [pSpec.Challenge]ₒ'
    (section58DecodedChallengeOracleInterface (U := U) StmtIn pSpec δ)

/-- CO25 Eq. 15 — eager full-table distribution `𝒟_Σ` (symbol `g`) over the encoded
challenge-oracle family for `Hyb₁`.

Samples a single full random table `g : (q : Domain) → Range q` once at game start; all subsequent
queries deterministically index into this fixed table. The `[SampleableType (OracleFamily _)]`
hypothesis matches CO25: with a fixed-length round-indexed prefix (see `EncodedMessagesUpTo`), the
oracle's domain is finite, and uniform sampling of the function table is the canonical realization
of `g ← 𝒰((dom_i → Σ^{ℓ_V(i)})_{i∈[k]})`. -/
def section58EncodedChallengeDist
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec]
    [SampleableType
      (ArkLib.OracleReduction.OracleFamily
        (section58EncodedChallengeOracle (U := U) StmtIn pSpec δ))] :
    ArkLib.OracleReduction.OracleDistribution
      (section58EncodedChallengeOracle (U := U) StmtIn pSpec δ) :=
  ArkLib.OracleReduction.OracleDistribution.uniform _

/-- CO25 Eq. 52 — eager full-table distribution `e` over the decoded challenge-oracle family
for `Hyb₂`.

Same eager full-table semantics as `section58EncodedChallengeDist`, with the response type swapped
from `Σ^{ℓ_V(i)}` to the decoded `pSpec.Challenge i`. Realizes
`e ← 𝒰((dom_i → ℳ_{V,i})_{i∈[k]})`. -/
def section58DecodedChallengeDist
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec]
    [SampleableType
      (ArkLib.OracleReduction.OracleFamily
        (section58DecodedChallengeOracle (U := U) StmtIn pSpec δ))] :
    ArkLib.OracleReduction.OracleDistribution
      (section58DecodedChallengeOracle (U := U) StmtIn pSpec δ) :=
  ArkLib.OracleReduction.OracleDistribution.uniform _

/-- Key for `StdTrace` memoized `gᵢ`-style entries (CO25 §5.2 Step 4.D output; strict shape
`BacktrackOutput`). -/
private abbrev StdTraceQuery :=
  Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

-- TODO(section5-cleanup): parallel to ProverTransform.D2SStdEntry but stores deserialized challenge
-- vectors instead of rate blocks. Consider a shared key plus two response wrappers later.
/-- One query-answer pair in `tr_std` / `tr_std^LA`. -/
private structure StdTraceEntry where
  query : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  response : Vector U (challengeSize query.roundIdx)

private abbrev StdTraceEntries :=
  List (StdTraceEntry
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Internal accumulator for `StdTrace`.
Stores synthesized entries plus memoized LookAhead results. -/
private structure StdTraceState where
  trStd : StdTraceEntries (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

  trStdLA : StdTraceEntries (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- Project DS-oracle entries from a mixed `oSpec + DS` log. -/
private def dsTraceOfLog
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl _, _⟩ => none
    | ⟨.inr q, r⟩ => some ⟨q, r⟩

/-- Lookup of a prior `tr_std^LA` entry with the same query key. -/
private def lookupStdTraceMemo
    (memo : List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec)
                                (U := U)))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Vector U (challengeSize q.roundIdx)) := by
  classical
  exact memo.findSome? fun entry =>
    if hEq : entry.query = q then
      some (hEq ▸ entry.response)
    else
      none

/-- Insert a fresh query-answer pair into `tr_std^LA` order. -/
private def insertStdTraceMemo
    (memo : List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec)
                                (U := U)))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (response : Vector U (challengeSize q.roundIdx)) :
    List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec)
                        (U := U)) :=
  memo ++ [{ query := q, response := response }]

/-! ## StdTrace helpers (CO25 §5.5.1)

These helpers implement CO25's exact `∀ι, α̂_ι ∈ Im(φ_ι)` codec-image predicate and the
deterministic `e_i := ψ_i(ρ̂_i)` entry remap. They are forward-declared here so that the
single `StdTrace` pipeline (and its abort analysis) can use them without exposing a free
predicate/function field. -/

private noncomputable def chooseSerializedMessage?
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (messageSize msgIdx)) :
    Option (pSpec.Message msgIdx) := by
  classical
  exact ((Finset.univ : Finset (pSpec.Message msgIdx)).toList.find? fun msg =>
    Serialize.serialize msg = encoded
  )

private def lookupEncodedMessage?
    (encodedMessages :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)))
    (msgIdx : pSpec.MessageIdx) :
    Option (Vector U (messageSize msgIdx)) := by
  classical
  exact encodedMessages.findSome? fun entry =>
    match entry with
    | ⟨idx, encoded⟩ =>
        if hEq : idx = msgIdx then
          some (hEq ▸ encoded)
        else
          none

private noncomputable def encodedMessagesUpTo?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedMessages : pSpec.EncodedMessagesUpTo U roundIdx.1.castSucc) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) := by
  classical
  -- Internal algorithm reuses the list-based lookup; we flatten via `toList` here so the
  -- structured CO25 Eq. 15 prefix surface is honored at the boundary, while the existing
  -- per-round walk stays unchanged.
  let encodedList :=
    EncodedMessagesUpTo.toList (pSpec := pSpec) (U := U) encodedMessages
  let build : (k : Fin (n + 1)) → Option (pSpec.MessagesUpTo k) :=
    Fin.induction
      (some default)
      (fun j ih =>
        match ih with
        | none => none
        | some messages =>
            match hDir : pSpec.dir j with
            | .P_to_V =>
                let msgIdx : pSpec.MessageIdx := ⟨j, hDir⟩
                match lookupEncodedMessage? (pSpec := pSpec) encodedList msgIdx with
                | none => none
                | some encodedMsg =>
                    match chooseSerializedMessage?
                        (pSpec := pSpec) (U := U) msgIdx encodedMsg with
                    | none => none
                    | some msg =>
                        some
                          (ProtocolSpec.MessagesUpTo.concat
                            (pSpec := pSpec) messages hDir msg)
            | .V_to_P =>
                some (ProtocolSpec.MessagesUpTo.extend (pSpec := pSpec) messages hDir))
  exact build roundIdx.1.castSucc

private noncomputable def stdTraceMessagesUpTo?
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (pSpec.MessagesUpTo q.roundIdx.1.castSucc) :=
  encodedMessagesUpTo? (pSpec := pSpec) (U := U)
    q.roundIdx q.encodedMessages

/-- CO25 §5.5.1 Item 4(a)iii — `∀ι, α̂_ι ∈ Im(φ_ι)` codec-image predicate over
StdTrace backtrack outputs. This is the canonical inCodecImage check baked into `stdTraceEntries`
in place of the previous free `BacktrackOutput → Bool` parameter. -/
private noncomputable def stdTraceInCodecImage
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let stdQuery : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := out
  match stdTraceMessagesUpTo?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stdQuery with
  | some _ => true
  | none => false

/-- CO25 §5.5.1 Item 4(a)v — `e_i := ψ_i(ρ̂_i)` entry remap. Partial because the codec-image
preimage may not exist; callers compose with `stdTraceInCodecImage` to guarantee `some`. -/
private noncomputable def stdTraceEntryToFSQuery?
    (entry : StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Sigma (fsChallengeOracle StmtIn pSpec)) := do
  let messagesUpTo ←
    stdTraceMessagesUpTo?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      entry.query
  let challenge : pSpec.Challenge entry.query.roundIdx :=
    Deserialize.deserialize entry.response
  pure ⟨⟨entry.query.roundIdx, (entry.query.stmt, messagesUpTo)⟩, challenge⟩

/-- StdTrace Step 3: build `tr_∇` from the DS trace, keeping `h` and forward `p` entries. -/
private def stdTraceDelta
    (dsTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    TraceNabla
      (ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
      StmtIn U :=
  TraceNabla.ofQueryLogForwardOnly dsTrace

private def StdTraceState.appendEntry
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize q.roundIdx)) :
    StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      :=
  { st with trStd := st.trStd ++ [{ query := q, response := rhoHat }] }

private def StdTraceState.appendMemoAndEntry
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize q.roundIdx)) :
    StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      :=
  { trStd := st.trStd ++ [{ query := q, response := rhoHat }]
    trStdLA := insertStdTraceMemo
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      st.trStdLA q rhoHat }

/-- StdTrace Item 4(a)iv-v.
Reuse memoized LookAhead output or call LookAhead and append `tr_std`. -/
private def stdTraceLookupOrLookAhead
    (trΔp : ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
    (stateIn : CanonicalSpongeState U)
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    DSAbort U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := do
  match lookupStdTraceMemo
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st.trStdLA q with
  | some rhoHat =>
      pure (st.appendEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat)
  | none =>
      let rhoHat? ← lookAhead (pSpec := pSpec) (U := U) trΔp stateIn q.roundIdx
      match rhoHat? with
      | .err =>
          -- CO25 `err`: multiple lookahead chains found (unexpected after backtrack).
          failure
      | .noResult =>
          -- CO25 §5.5.1 Item 4(a)ivB-D: once BackTrack returns a valid tuple for the
          -- current `p` entry, LookAhead should find the matching successor in `tr`.
          failure
      | .some rhoHat =>
          pure (st.appendMemoAndEntry
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat)

/-- StdTrace Item 4(a)iii-v: check codec image, then memo/lookahead and append an entry. -/
private noncomputable def stdTraceHandleBacktrackTuple
    (trΔp : ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    DSAbort U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  if stdTraceInCodecImage
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) backtrackOut then
    let stdQuery : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
      backtrackOut
    stdTraceLookupOrLookAhead
      (δ := δ)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) trΔp stateIn stdQuery st
  else
    pure st

/-- StdTrace Item 4(a): process one forward `p` entry using BackTrack and LookAhead. -/
private noncomputable def stdTraceHandlePQuery
    (dsTrΔ :
      TraceNabla
        (ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
        (ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
        StmtIn U)
    (depthBound : Nat)
    (stateIn : CanonicalSpongeState U)
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    DSAbort U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match
      backTrack (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        dsTrΔ depthBound stateIn with
  | .err =>
      failure
  | .noResult =>
      pure st
  | .some backtrackOut =>
      stdTraceHandleBacktrackTuple (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        dsTrΔ.p stateIn backtrackOut st

/-- StdTrace Item 4 loop body: ignore non-forward-`p` entries; process forward `p` entries. -/
private noncomputable def stdTraceHandleEntry
    (dsTrΔ :
      TraceNabla
        (ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
        (ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
        StmtIn U)
    (depthBound : Nat)
    (entry : Sigma (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    DSAbort U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match entry with
  | ⟨.inr (.inr (.inl stateIn)), _stateOut⟩ =>
      stdTraceHandlePQuery (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        dsTrΔ depthBound stateIn st
  | _ =>
      pure st

/-- Public wrapper for the Section 5.8 `φ⁻¹` parser from the encoded-message tuple returned by
`BackTrack` to basic-FS message prefixes.

CO25 Eq. 15 prefix shape: the input is `pSpec.EncodedMessagesUpTo U roundIdx.1.castSucc`
(exactly `i` encoded messages indexed by message rounds `< i`). -/
noncomputable def section58EncodedMessagesUpTo?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedMessages : pSpec.EncodedMessagesUpTo U roundIdx.1.castSucc) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) :=
  encodedMessagesUpTo?
    (pSpec := pSpec) (U := U)
    roundIdx encodedMessages

/-- Keep only shared-oracle entries from a DSFS query log, and reinterpret them as basic-FS
query-log entries. Needed in `stdTraceSingle`, where the output is `sharedLog ++ remappedLog`. -/
def projectSharedQueryLog
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
    | ⟨.inr _, _⟩ => none

/-- Compute `StdTrace` query-answer entries (`tr_std`) from a full mixed log.

This implements Section 5.5.1 Item 4(a) control-flow over the DS entries:
- abort on `backTrack = err` or `lookAhead = err`,
- skip on `backTrack = none` or non-challenge backtrack tuples,
- skip when `stdTraceInCodecImage` rejects the backtrack output (CO25 §5.5.1 Item 4(a)iii),
- memoize `LookAhead` outputs in `tr_std^LA` keyed by backtrack tuples.

The codec-image predicate is now baked in as `stdTraceInCodecImage` rather than a free
`BacktrackOutput → Bool` parameter, eliminating the prior non-canonical adversarial instantiation
surface. -/
private noncomputable def stdTraceEntries
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    DSAbort U
      (List (StdTraceEntry
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) := do
  let dsTrace := dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U) log
  let dsTrΔ := stdTraceDelta (StmtIn := StmtIn) (U := U) dsTrace
  let depthBound := dsTrace.length + 1
  let rec go
      (remaining : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (st : StdTraceState
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      DSAbort U
        (StdTraceState
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := do
    match remaining with
    | [] =>
        pure st
    | entry :: rest =>
        let st' ←
          stdTraceHandleEntry (δ := δ)
            (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
            dsTrΔ depthBound entry st
        go rest st'
  let st ← go log { trStd := [], trStdLA := [] }
  pure st.trStd

/-- Map synthesized `StdTrace` entries to basic-FS challenge-log entries via
`stdTraceEntryToFSQuery?` (CO25 §5.5.1 Item 4(a)v). Entries whose codec preimage is missing are
dropped; under `stdTraceEntries`'s baked-in `stdTraceInCodecImage` filter, every entry that
survives has `stdTraceMessagesUpTo? entry.query = some _`, so the remap returns `some` on every
input in practice. This replaces the prior free `mapEntry` field. -/
private noncomputable def remapStdTraceEntries
    (entries : List (StdTraceEntry
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) :=
  entries.filterMap fun entry =>
    match stdTraceEntryToFSQuery?
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) entry with
    | none => none
    | some mapped => some ⟨.inr mapped.1, mapped.2⟩

/-- §5.5.1 `StdTrace` single-log surface (Item 4(a) control flow).

Synthesized `StdTrace` entries are remapped into FS challenge-log entries via
`stdTraceEntryToFSQuery?` (Item 4(a)v) and appended to the shared-oracle projection,
implementing CO25's single-log `tr_std` transform. The codec-image predicate (Item 4(a)iii) is
baked into `stdTraceEntries` directly via `stdTraceInCodecImage`; no free remap field is exposed. -/
noncomputable def stdTraceSingle
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    DSAbort U
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let entries ←
    stdTraceEntries (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  let sharedLog :=
    projectSharedQueryLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log
  let remappedLog :=
    remapStdTraceEntries (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) entries
  pure (sharedLog ++ remappedLog)

/-! ## Salted FS variants (CO25 §5.5.1 Item 4(a)v)

CO25's `f_i(x, τ, α_1, …, α_i)` query keeps the public salt `τ ∈ Σ^δ` threaded through the
augmented statement, matching the encoding-A oracle `fsChallengeOracle (Vector U δ × StmtIn) pSpec`
already used in `SingleSalt.lean`. The salted variants below are consumed by `KeyLemma`'s Section
5.8 hybrids. -/

/-- Salted variant of `stdTraceEntryToFSQuery?` — preserves the BackTrack salt
`out.salt : Vector U δ` in the augmented statement of the salted FS oracle query. -/
private noncomputable def stdTraceEntryToFSQuerySalted?
    (entry : StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Sigma (fsChallengeOracle (Vector U δ × StmtIn) pSpec)) := do
  let messagesUpTo ←
    stdTraceMessagesUpTo?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      entry.query
  let challenge : pSpec.Challenge entry.query.roundIdx :=
    Deserialize.deserialize entry.response
  pure ⟨⟨entry.query.roundIdx, ((entry.query.salt, entry.query.stmt), messagesUpTo)⟩, challenge⟩

/-- Salted variant of `remapStdTraceEntries` — produces a salted-FS query log. -/
private noncomputable def remapStdTraceEntriesSalted
    (entries : List (StdTraceEntry
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :
    QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec) :=
  entries.filterMap fun entry =>
    match stdTraceEntryToFSQuerySalted?
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) entry with
    | none => none
    | some mapped => some ⟨.inr mapped.1, mapped.2⟩

/-- Salted variant of `projectSharedQueryLog` — keeps `oSpec` shared entries, reinterpreted as
salted-FS log entries. -/
def projectSharedQueryLogSalted
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
    | ⟨.inr _, _⟩ => none

/-- Salted variant of `stdTraceSingle` — produces a salted-FS query log per Encoding A. -/
noncomputable def stdTraceSingleSalted
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    DSAbort U
      (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)) := do
  let entries ←
    stdTraceEntries (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  let sharedLog :=
    projectSharedQueryLogSalted (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) log
  let remappedLog :=
    remapStdTraceEntriesSalted (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) entries
  pure (sharedLog ++ remappedLog)

section Line4Trace

/-- Section 5.8 `Hyb₁` line-4 trace translation.

This is the explicit `(φ⁻¹, ψ)(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def section58Hyb1Line4Trace
    (log : QueryLog (oSpec + section58EncodedChallengeOracle (U := U) StmtIn pSpec δ)) :
    DSAbort U
      (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)) := do
  let remappedLog := log.filterMap fun entry =>
    match entry with
    | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
    | ⟨.inr query, response⟩ =>
        match query with
        | ⟨roundIdx, (stmt, salt, encodedMessages)⟩ =>
            match section58EncodedMessagesUpTo?
                (pSpec := pSpec) (U := U) roundIdx encodedMessages with
            | none => none
            | some messagesUpTo =>
                let responseVec :
                    Vector U (challengeSize (pSpec := pSpec) roundIdx) := response
                let challenge : pSpec.Challenge roundIdx :=
                  Deserialize.deserialize responseVec
                some ⟨.inr ⟨roundIdx, ((salt, stmt), messagesUpTo)⟩, challenge⟩
  pure remappedLog

/-- Section 5.8 `Hyb₂` line-4 trace translation.

This is the explicit `φ⁻¹(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def section58Hyb2Line4Trace
    (log : QueryLog (oSpec + section58DecodedChallengeOracle (U := U) StmtIn pSpec δ)) :
    DSAbort U
      (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)) := do
  let remappedLog := log.filterMap fun entry =>
    match entry with
    | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
    | ⟨.inr ⟨roundIdx, (stmt, salt, encodedMessages)⟩, challenge⟩ =>
        match section58EncodedMessagesUpTo?
            (pSpec := pSpec) (U := U) roundIdx encodedMessages with
        | none => none
        | some messagesUpTo =>
            some ⟨.inr ⟨roundIdx, ((salt, stmt), messagesUpTo)⟩, challenge⟩
  pure remappedLog

/-- Section 5.8 `Hyb₃` line-4 trace translation.

This is the identity-on-line-4 trace surface, viewed through the common single-log Section 5
interface used by `KeyLemma`. -/
noncomputable def section58Hyb3Line4Trace
    (log : QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)) :
    DSAbort U
      (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)) :=
  pure log

end Line4Trace

end

end DuplexSpongeFS.TraceTransform

-- TODO: move core defs to outer file
