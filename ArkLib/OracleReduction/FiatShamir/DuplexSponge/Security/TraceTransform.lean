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

/-- Key for `StdTrace` memoized `gᵢ`-style entries (CO25 §5.2 Step 4.D output; strict shape
`BacktrackOutput`). -/
private abbrev StdTraceQuery :=
  Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

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
def dsTraceOfLog
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

/-- Implements the deterministic inverse codec map `φ_i⁻¹ : Im(φ_i) → ℳ_{P,i}`.
Because `φ_i` (via `instSerializeMessageInjective`) is strictly injective and the message domain
is finite, we can invert the serialization computationally via brute-force search.
-/
private def decodeMessagePhiInv?
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (messageSize msgIdx)) :
    Option (pSpec.Message msgIdx) := by
  exact ((Finset.univ : Finset (pSpec.Message msgIdx)).toList.find? fun msg =>
    Serialize.serialize msg = encoded)

/-- Looks up the encoded message block `α̂_j` from the flat list of extracted sponge queries. -/
private def lookupEncodedMessageAlphaHat?
    (encodedMessages :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)))
    (msgIdx : pSpec.MessageIdx) :
    Option (Vector U (messageSize msgIdx)) := by
  exact encodedMessages.findSome? fun entry =>
    match entry with
    | ⟨idx, encoded⟩ =>
        if hEq : idx = msgIdx then
          some (hEq ▸ encoded)
        else
          none

/-- One step of the `decodeMessagesPrefixPhiInv?` walk: extend the partial `MessagesUpTo` prefix
by one round. On a `P_to_V` round, extract the encoded message `α̂_j` and apply `φ_j⁻¹`
(`decodeMessagePhiInv?`); on a `V_to_P` round, extend the prefix with no payload. -/
private noncomputable def decodeMessagesPrefixStepPhiInv
    (encodedList :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)))
    (j : Fin n) (messages : pSpec.MessagesUpTo j.castSucc) :
    Option (pSpec.MessagesUpTo j.succ) := by
  exact
    match hDir : pSpec.dir j with
    | .P_to_V =>
        let msgIdx : pSpec.MessageIdx := ⟨j, hDir⟩
        match lookupEncodedMessageAlphaHat? (pSpec := pSpec) encodedList msgIdx with
        | none => none
        | some encodedMsg =>
            match decodeMessagePhiInv?
                (pSpec := pSpec) (U := U) msgIdx encodedMsg with
            | none => none
            | some msg =>
                some
                  (ProtocolSpec.MessagesUpTo.concat
                    (pSpec := pSpec) messages hDir msg)
    | .V_to_P =>
        some (ProtocolSpec.MessagesUpTo.extend (pSpec := pSpec) messages hDir)

/-- Implements the full `φ⁻¹` map over a structured prefix of encoded messages up to round `i`.
Walks the rounds `0..i-1` and iteratively applies `decodeMessagesPrefixStepPhiInv` to return
the unencoded message sequence `α_{<i}`. -/
private noncomputable def decodeMessagesPrefixPhiInv?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) := by
  -- Internal algorithm reuses the list-based lookup; we flatten via `toList` here so the
  -- structured CO25 Eq. 15 prefix surface is honored at the boundary, while the existing
  -- per-round walk stays unchanged.
  let encodedList :=
    EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) encodedMessages
  let build : (k : Fin (n + 1)) → Option (pSpec.MessagesUpTo k) :=
    Fin.induction
      (some default)
      (fun j ih =>
        match ih with
        | none => none
        | some messages =>
            decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) encodedList j messages)
  exact build roundIdx.1.castSucc

private noncomputable def stdTraceMessagesBefore?
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (pSpec.MessagesUpTo q.roundIdx.1.castSucc) :=
  decodeMessagesPrefixPhiInv? (pSpec := pSpec) (U := U)
    q.roundIdx q.encodedMessages

/-- CO25 §5.5.1 Item 4(a)iii — `∀ι, α̂_ι ∈ Im(φ_ι)` codec-image predicate over
StdTrace backtrack outputs. This is the canonical inCodecImage check baked into `stdTraceEntries`
in place of the previous free `BacktrackOutput → Bool` parameter. -/
private noncomputable def stdTraceInCodecImage
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let stdQuery : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := out
  match stdTraceMessagesBefore?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stdQuery with
  | some _ => true
  | none => false

/-- StdTrace Step 3: build `tr_∇` from the DS trace, keeping `h` and forward `p` entries.

Kept polymorphic in the trace-table implementations `T_H`/`T_P` (with a `LawfulTraceNablaImpl`
instance) so callers stay blackbox over the concrete data structure. -/
private def stdTraceDelta
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (dsTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    TraceNabla T_H T_P StmtIn U :=
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
    -- cache `((i, 𝕩, τ, α̂_{<i}), ρ̂_i)` into `tr_std^LA`
    trStdLA := insertStdTraceMemo
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      st.trStdLA q rhoHat }

/-- StdTrace Item 4(a)iv-v — reuse memoized LookAhead output or call LookAhead and append
`tr_std`.

Blackbox over the permutation trace-table implementation: only `[LawfulTraceTable T_P
(CanonicalSpongeState U) (CanonicalSpongeState U)]` is assumed, matching `lookAhead`. -/
private def stdTraceLookupOrLookAhead
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (stateIn : CanonicalSpongeState U)
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    UnitSampleM U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := do
  match lookupStdTraceMemo
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st.trStdLA q with
  | some rhoHat =>
      -- Item 4(a)ivA — `tr_std^LA` hit on key `(i, 𝕩, τ, α̂_{<i})`: reuse cached `ρ̂_i`.
      pure (st.appendEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat)
  | none =>
      -- Item 4(a)ivB — `tr_std^LA` miss on `(i, 𝕩, τ, α̂_{<i})`: call `LookAhead(tr_∇.p, s_in, i)`.
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
          -- Item 4(a)ivD — append `((i, 𝕩, τ, α̂_{<i}), ρ̂_i)` to `tr_std^LA` and `tr_std`.
          pure (st.appendMemoAndEntry
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat)

/-- StdTrace Item 4(a)iii-v — check codec image, then memo/lookahead and append an entry.

Blackbox over `T_P` (the permutation trace table). -/
private noncomputable def stdTraceHandleBacktrackTuple
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    UnitSampleM U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  -- Item 4(a)iii — codec-image check: accept iff `(α̂_1, …, α̂_{i-1}) ∈ Image(φ)`; else skip.
  if stdTraceInCodecImage
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) backtrackOut then
    let stdQuery : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
      backtrackOut
    -- Items 4(a)iv-v — dispatch into LookAhead memo / fresh call + append to `tr_std`.
    stdTraceLookupOrLookAhead
      (δ := δ)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) trΔp stateIn stdQuery st
  else
    pure st

/-- StdTrace Item 4(a) — process one forward `p` entry using BackTrack and LookAhead.

Blackbox over `T_H T_P` via `[LawfulTraceNablaImpl …]`; the `tr_∇` value flows into `backTrack`
(which is itself polymorphic in `T_H T_P`) and `dsTrΔ.p` flows into `lookAhead`. -/
private noncomputable def stdTraceHandlePQuery
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (dsTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (dsTrΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : dsTrΔ.IsSubsetOfQueryLog dsTrace)
    (depthBound : Nat)
    (stateIn : CanonicalSpongeState U)
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    UnitSampleM U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  -- Item 4(a)i-ii — call `BackTrack(tr, tr_∇, s_in)` to recover `(i, 𝕩, α̂_{<i}, τ̂)` ∈ Σ★.
  match
      backTrack (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        dsTrace dsTrΔ h_trΔ stateIn depthBound with
  | .err =>
      failure
  | .noResult =>
      -- `BackTrack = ⊥` (no valid ancestor): skip this forward `p` entry per Item 4(a)ii.
      pure st
  | .some backtrackOut =>
      -- Items 4(a)iii-v — image check then memo/lookahead + append to `tr_std`.
      stdTraceHandleBacktrackTuple (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        dsTrΔ.p stateIn backtrackOut st

/-- Public wrapper for the Section 5.8 `φ⁻¹` parser from the encoded-message tuple returned by
`BackTrack` to basic-FS message prefixes.

CO25 Eq. 15 prefix shape: the input is `pSpec.EncodedMessagesBefore U roundIdx.1.castSucc`
(exactly `i` encoded messages indexed by message rounds `< i`). -/
noncomputable def hybEncodedMessagesBefore?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) :=
  decodeMessagesPrefixPhiInv?
    (pSpec := pSpec) (U := U)
    roundIdx encodedMessages

/-! ## Salted FS variants (CO25 §5.5.1 Item 4(a)v)

CO25's standard FS reduction `R_FS` keeps the public *pre-encoded* salt `τ̌ ∈ {0,1}^{δ★}` threaded
through the augmented statement of the FS-standard oracle (paper line 1187-1192, Eq. 54-55).
We model this as the abstract type `Salt`, bridged from the on-sponge `Vector U δ` salt via
`SaltCodec.encode = bin`. The salted variants below feed into `KeyLemma`'s `Hyb₃`/`Hyb₄`. -/

/-- Salted variant of `stdTraceEntryToFSQuery?` — projects the BackTrack salt
`out.salt : Vector U δ` to the FS-standard side via `bin = SaltCodec.encode` before placing it
in the augmented statement of the salted FS oracle query (paper line 1188). -/
private noncomputable def stdTraceEntryToFSQuerySalted?
    {Salt : Type} [SaltCodec U δ Salt]
    (entry : StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Sigma (fsChallengeOracle (StmtIn × Salt) pSpec)) := do
  let messagesBefore ←
    stdTraceMessagesBefore?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      entry.query
  let challenge : pSpec.Challenge entry.query.roundIdx :=
    Deserialize.deserialize entry.response
  pure ⟨⟨entry.query.roundIdx,
    ((entry.query.stmt, SaltCodec.encode entry.query.salt), messagesBefore)⟩, challenge⟩

/-- §5.5.2 `D2STrace` — the single D2STrace engine.  Processes a `TaggedQueryLog` iteratively to
map DSFS traces to FS-standard traces while preserving the `SourceTag` and exact ordering.

Because this map is stateful and traverses the combined trace sequentially, the prover's
sponge state seamlessly threads into the verifier's queries, correctly building the
global `TraceNabla` graph. `oSpec` queries are forwarded in-place. -/
noncomputable def d2sTraceSalted
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) := do
  let combinedRaw := TaggedQueryLog.untagged log
  let dsTrace := dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U) combinedRaw
  let dsTrΔ : TraceNabla T_H T_P StmtIn U :=
    stdTraceDelta (StmtIn := StmtIn) (U := U) dsTrace
  have h_trΔ : dsTrΔ.IsSubsetOfQueryLog dsTrace := TraceNabla.ofQueryLogForwardOnly_isSubset dsTrace
  let depthBound := dsTrace.length + 1
  let rec go
      (remaining : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (out : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
      UnitSampleM U (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) := do
    match remaining with
    | [] => pure out
    | (tag, entry) :: rest =>
        match entry with
        | ⟨.inl query, response⟩ =>
            -- Forward oSpec entries verbatim, preserving their tag (C1)
            let outEntry : Sigma (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) :=
              ⟨.inl query, response⟩
            go rest st (out ++ [(tag, outEntry)])
        | ⟨.inr (.inr (.inl stateIn)), _stateOut⟩ =>
            let st' ← stdTraceHandlePQuery (δ := δ) (StmtIn := StmtIn) (n := n)
              (pSpec := pSpec) (U := U) dsTrace dsTrΔ h_trΔ depthBound stateIn st
            -- Extract newly synthesized basic-FS challenge queries
            let newEntries := st'.trStd.drop st.trStd.length
            -- Apply line-4 transform to them
            let mappedNewEntries := newEntries.filterMap fun e =>
              match stdTraceEntryToFSQuerySalted? (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Salt := Salt) e with
              | none => none
              | some mapped => some (tag, ⟨.inr mapped.1, mapped.2⟩)
            go rest st' (out ++ mappedNewEntries)
        | _ => go rest st out
  go log { trStd := [], trStdLA := [] } []

section Line4Trace

/-- Section 5.8 `Hyb₁` line-4 per-entry remap. Encoded prover-prefix + encoded verifier response
↦ decoded prover-prefix + decoded challenge. Salt is projected `Σ^δ → Salt` via
`SaltCodec.encode = bin` (paper line 1188). `oSpec` entries are forwarded verbatim. -/
private noncomputable def hyb1RemapEntry?
    {Salt : Type} [SaltCodec U δ Salt]
    (entry : Sigma (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    Option (Sigma (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  match entry with
  | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
  | ⟨.inr ⟨roundIdx, (stmt, salt, encodedMessages)⟩, response⟩ =>
      -- `Hyb₁` line 4 — `φ⁻¹`: decode `(α_1, …, α_{i-1}) := φ⁻¹(α̂_1, …, α̂_{i-1})`; abort on `⊥`.
      match hybEncodedMessagesBefore?
          (pSpec := pSpec) (U := U) roundIdx encodedMessages with
      | none => none
      | some messagesBefore =>
          let responseVec :
              Vector U (challengeSize (pSpec := pSpec) roundIdx) := response
          -- `Hyb₁` line 4 — `ψ`: `ρ_i := ψ_i(ρ̂_i)`; salt projected `τ̌ := bin(τ̂)`.
          let challenge : pSpec.Challenge roundIdx :=
            Deserialize.deserialize responseVec
          some ⟨.inr ⟨roundIdx, ((stmt, SaltCodec.encode salt), messagesBefore)⟩, challenge⟩

/-- Section 5.8 `Hyb₁` line-4 trace translation.

This is the explicit `(φ⁻¹, ψ)(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def hyb1Line4Trace
    {Salt : Type} [SaltCodec U δ Salt]
    (log : TaggedQueryLog (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  pure (log.filterMap fun ⟨tag, entry⟩ =>
    match hyb1RemapEntry? (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) entry with
    | some mapped => some (tag, mapped)
    | none => none)

/-- Section 5.8 `Hyb₂` line-4 per-entry remap. Encoded prover-prefix + decoded verifier response
↦ decoded prover-prefix + decoded challenge. Salt is projected `Σ^δ → Salt` via
`SaltCodec.encode = bin` (paper line 1188). `oSpec` entries are forwarded verbatim. -/
private noncomputable def hyb2RemapEntry?
    {Salt : Type} [SaltCodec U δ Salt]
    (entry : Sigma (oSpec + eSpec (U := U) StmtIn pSpec δ)) :
    Option (Sigma (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  match entry with
  | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
  | ⟨.inr ⟨roundIdx, (stmt, salt, encodedMessages)⟩, challenge⟩ =>
      -- `Hyb₂` line 4 — `φ⁻¹` only: decode `(α_1, …, α_{i-1}) := φ⁻¹(α̂_1, …, α̂_{i-1})`;
      --   challenge `ρ_i` already on FS-side; salt projected `τ̌ := bin(τ̂)`.
      match hybEncodedMessagesBefore?
          (pSpec := pSpec) (U := U) roundIdx encodedMessages with
      | none => none
      | some messagesBefore =>
          some ⟨.inr ⟨roundIdx, ((stmt, SaltCodec.encode salt), messagesBefore)⟩, challenge⟩

/-- Section 5.8 `Hyb₂` line-4 trace translation.

This is the explicit `φ⁻¹(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def hyb2Line4Trace
    {Salt : Type} [SaltCodec U δ Salt]
    (log : TaggedQueryLog (oSpec + eSpec (U := U) StmtIn pSpec δ)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  pure (log.filterMap fun ⟨tag, entry⟩ =>
    match hyb2RemapEntry? (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) entry with
    | some mapped => some (tag, mapped)
    | none => none)

/-- Section 5.8 `Hyb₃` line-4 trace translation.

This is the identity-on-line-4 trace surface, viewed through the common single-log Section 5
interface used by `KeyLemma`. -/
noncomputable def hyb3Line4Trace
    {Salt : Type}
    (log : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  -- `Hyb₃` line 4 — identity: trace already lives on the salted-FS oracle; no remap needed.
  pure log

end Line4Trace

end

end DuplexSpongeFS.TraceTransform
