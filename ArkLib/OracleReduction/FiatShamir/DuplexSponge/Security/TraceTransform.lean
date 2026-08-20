/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventDefs

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
  [codec : CodecCore pSpec U]
  [∀ i, Fintype (pSpec.Message i)]
  {δ : Nat}


noncomputable section

/-- Key for `StdTrace` memoized `gᵢ`-style entries (CO25 §5.2 Step 4.D output; strict shape
`BacktrackOutput`). -/
abbrev StdTraceQuery :=
  Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- One query-answer pair in `tr_std` / `tr_std^LA`. -/
structure StdTraceEntry where
  query : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  response : Vector U (challengeSize query.roundIdx)

abbrev StdTraceEntries :=
  List (StdTraceEntry
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Internal accumulator for `StdTrace`.
Stores synthesized entries plus memoized LookAhead results. -/
structure StdTraceState where
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

/-- View a global message index before `k` as an index of the `MessagesUpTo k` prefix. -/
private def messageIdxUpToOfBefore
    {k : Fin (n + 1)} (j : MessageIdxBefore k pSpec) :
    pSpec.MessageIdxUpTo k :=
  ⟨j.1.1.castLT j.2, by
    simpa only [Fin.castLT, Fin.castLE] using j.1.2⟩

/-- CO25's componentwise prefix encoding `φ_{<i}`. -/
def encodeMessagesBefore
    {k : Fin (n + 1)} (messages : pSpec.MessagesUpTo k) :
    pSpec.EncodedMessagesBefore U k := fun j => by
  let j' : pSpec.MessageIdxUpTo k := messageIdxUpToOfBefore (pSpec := pSpec) j
  apply codec.encode j.1
  change pSpec.«Type» j.1.1
  have hIndex : (j'.1.castLE (by omega) : Fin n) = j.1.1 := Fin.ext rfl
  rw [← hIndex]
  exact messages j'

/-- Implements the partial inverse `φ_{<i}^{-1}` by searching the finite decoded prefix space.
It returns the unique prefix whose componentwise encoding is the supplied key, or `none` when
the key is outside the image. -/
private noncomputable def decodeMessagesPrefixPhiInv?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) := by
  letI : ∀ i : pSpec.MessageIdxUpTo roundIdx.1.castSucc,
      Fintype (pSpec.MessageUpTo roundIdx.1.castSucc i) := fun i => by
    exact inferInstanceAs (Fintype (pSpec.Message ⟨i.1.castLE (by omega), i.2⟩))
  exact ((Finset.univ : Finset (pSpec.MessagesUpTo roundIdx.1.castSucc)).toList.find? fun messages =>
    encodeMessagesBefore (pSpec := pSpec) (U := U) messages = encodedMessages)

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

/-- StdTrace Algorithm 5.5 Step 3, full lookup pass: build the normalized full `tr_∇` from the
whole DS trace. Both forward and inverse permutation occurrences contribute their normalized
forward pair to `p`; this is the table supplied to LookAhead. -/
private def stdTraceDelta
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (dsTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    TraceNabla T_H T_P StmtIn U :=
  TraceNabla.ofQueryLog dsTrace

/-- StdTrace Algorithm 5.5 Step 4 strict-prefix table: the same normalized construction over the
already processed DS prefix. This table is supplied only to Backtrack, so the current forward
occurrence remains the uninserted sentinel. -/
private def stdTracePrefixDelta
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (processed : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    TraceNabla T_H T_P StmtIn U :=
  TraceNabla.ofQueryLog processed

private def StdTraceState.appendEntry
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat_i : Vector U (challengeSize q.roundIdx)) :
    StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      :=
  { st with trStd := st.trStd ++ [{ query := q, response := rhoHat_i }] }

private def StdTraceState.appendMemoAndEntry
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat_i : Vector U (challengeSize q.roundIdx)) :
    StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      :=
  { trStd := st.trStd ++ [{ query := q, response := rhoHat_i }]
    -- cache `((i, 𝕩, τ, α̂_{<i}), ρ̂_i)` into `tr_std^LA`
    trStdLA := insertStdTraceMemo
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      st.trStdLA q rhoHat_i }

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
  | some rhoHat_i =>
      -- Item 4(a)ivA — `tr_std^LA` hit on key `(i, 𝕩, τ, α̂_{<i})`: reuse cached `ρ̂_i`.
      pure (st.appendEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat_i)
  | none =>
      -- Item 4(a)ivB — `tr_std^LA` miss on `(i, 𝕩, τ, α̂_{<i})`: call `LookAhead(tr_∇.p, s_in, i)`.
      let rhoHat_i? ← lookAhead (pSpec := pSpec) (U := U) trΔp stateIn q.roundIdx
      match rhoHat_i? with
      | .err =>
          -- CO25 `err`: multiple lookahead chains found (unexpected after backtrack).
          failure
      | .noResult =>
          -- CO25 §5.5.1 Item 4(a)ivB-D: once BackTrack returns a valid tuple for the
          -- current `p` entry, LookAhead should find the matching successor in `tr`.
          failure
      | .some rhoHat_i =>
          -- Item 4(a)ivD — append `((i, 𝕩, τ, α̂_{<i}), ρ̂_i)` to `tr_std^LA` and `tr_std`.
          pure (st.appendMemoAndEntry
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat_i)

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

Backtrack receives the strict processed prefix, while LookAhead receives the independently built
full normalized table. Both tables remain polymorphic in `T_H T_P`. -/
private noncomputable def stdTraceHandlePQuery
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (processedTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (prefixTrΔ : TraceNabla T_H T_P StmtIn U)
    (h_prefixTrΔ : prefixTrΔ.IsSubsetOfQueryLog processedTrace)
    (fullTrΔp : T_P)
    (depthBound : Nat)
    (stateIn : CanonicalSpongeState U)
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    UnitSampleM U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  -- Item 4(a)i-ii — call Backtrack on the strict prefix. The current forward entry is absent
  -- from `processedTrace`; `fullTrΔp` below remains the complete table for LookAhead.
  match
      backTrack (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        processedTrace prefixTrΔ h_prefixTrΔ stateIn depthBound with
  | .err =>
      failure
  | .noResult =>
      -- `BackTrack = ⊥` (no valid ancestor): skip this forward `p` entry per Item 4(a)ii.
      pure st
  | .some backtrackOut =>
      -- Items 4(a)iii-v — image check then memo/lookahead + append to `tr_std`.
      stdTraceHandleBacktrackTuple (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        fullTrΔp stateIn backtrackOut st

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

/-- Reindex one encoded `e`-oracle key to the salted basic-FS key used after the Section 5.8
`φ⁻¹` check.  It is undefined precisely for malformed encoded message prefixes. -/
noncomputable def hybEncodedToSaltedFSKey?
    {Salt : Type} [SaltCodec U δ Salt]
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain) :
    Option ((fsChallengeOracle (StmtIn × Salt) pSpec).Domain) :=
  match q with
  | ⟨roundIdx, (stmt, salt, encodedMessages)⟩ =>
      match hybEncodedMessagesBefore?
          (pSpec := pSpec) (U := U) roundIdx encodedMessages with
      | none => none
      | some messagesBefore =>
          some ⟨roundIdx, ((stmt, SaltCodec.encode salt), messagesBefore)⟩

/-- The subdomain of encoded `e`-oracle coordinates which pass CO25's `φ⁻¹` image check. -/
def HybValidEncodedKey {Salt : Type} [SaltCodec U δ Salt] : Type :=
  {q : (eSpec (U := U) StmtIn pSpec δ).Domain //
    ∃ key : (fsChallengeOracle (StmtIn × Salt) pSpec).Domain,
      hybEncodedToSaltedFSKey? (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        q = some key}

/-- The total reindexing map from valid encoded coordinates to salted basic-FS coordinates. -/
noncomputable def hybValidEncodedToSaltedFSKey
    {Salt : Type} [SaltCodec U δ Salt]
    (q : HybValidEncodedKey (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) :
    (fsChallengeOracle (StmtIn × Salt) pSpec).Domain :=
  q.2.choose

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

/-- Lossless result of the corrected `StdTrace`/`D2STrace` pipeline.  `encodedTrace` is the
insertion-ordered encoded `gᵢ` trace produced by `StdTrace` (including repeated keys), while
`lookAheadMemo` is its lexicographically keyed lookup table.  `output` is exactly the public
decoded basic-FS trace returned by Algorithm 5.6.

Keeping `encodedTrace` is necessary for the Hyb₀↔Hyb₁ coupling: decoding through `ψᵢ` need not be
injective, so the encoded trace cannot be reconstructed from `output` afterward. -/
structure D2STraceSaltedObservation {Salt : Type} where
  encodedTrace : StdTraceEntries (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  lookAheadMemo : StdTraceEntries (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  output : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)

/-- Lossless §5.5.2 `D2STrace` execution.  It runs the same `StdTrace` state machine as the
public transformation and returns the exact encoded insertion trace and LookAhead memo alongside
the public decoded trace.  No additional sampling is performed. -/
noncomputable def d2sTraceSaltedObserved
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    UnitSampleM U
      (D2STraceSaltedObservation (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) := do
  let combinedRaw := TaggedQueryLog.untagged log
  let dsTrace := dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U) combinedRaw
  let dsTrΔ : TraceNabla T_H T_P StmtIn U :=
    stdTraceDelta (StmtIn := StmtIn) (U := U) dsTrace
  -- Algorithm 5.5 Step 3 is the complete `PrefixUpdate`/`Monitor` pass. If its normalized
  -- insertion trace is bad, StdTrace aborts before any Backtrack/LookAhead result is exposed.
  letI : Decidable (BadEventDS.E dsTrace) := Classical.propDecidable _
  if BadEventDS.E dsTrace then failure else
  let rec go
      (remaining : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (processed : QueryLog (duplexSpongeChallengeOracle StmtIn U))
      (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (out : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
      UnitSampleM U (D2STraceSaltedObservation (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) := do
    match remaining with
    | [] => pure ⟨st.trStd, st.trStdLA, out⟩
    | (tag, entry) :: rest =>
        match entry with
        | ⟨.inl query, response⟩ =>
            -- Forward oSpec entries verbatim, preserving their tag (C1)
            let outEntry : Sigma (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) :=
              ⟨.inl query, response⟩
            go rest processed st (out ++ [(tag, outEntry)])
        | ⟨.inr (.inl stmt), cap⟩ =>
            -- Hash occurrences participate in the strict prefix and in the full normalized table,
            -- but do not themselves produce a standard challenge-table entry.
            go rest (processed ++ [⟨.inl stmt, cap⟩]) st out
        | ⟨.inr (.inr (.inl stateIn)), stateOut⟩ =>
            let prefixTrΔ : TraceNabla T_H T_P StmtIn U :=
              stdTracePrefixDelta (StmtIn := StmtIn) (U := U) processed
            have h_prefixTrΔ : prefixTrΔ.IsSubsetOfQueryLog processed :=
              TraceNabla.ofQueryLog_isSubset processed
            let st' ← stdTraceHandlePQuery (δ := δ) (StmtIn := StmtIn) (n := n)
              (pSpec := pSpec) (U := U) processed prefixTrΔ h_prefixTrΔ dsTrΔ.p
              (processed.length + 1) stateIn st
            -- Extract newly synthesized basic-FS challenge queries
            let newEntries := st'.trStd.drop st.trStd.length
            -- Apply line-4 transform to them
            let mappedNewEntries := newEntries.filterMap fun e =>
              match stdTraceEntryToFSQuerySalted? (δ := δ) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (Salt := Salt) e with
              | none => none
              | some mapped => some (tag, ⟨.inr mapped.1, mapped.2⟩)
            -- The just-classified forward occurrence becomes visible only to later Backtrack
            -- calls; it was deliberately absent from the strict-prefix call above.
            go rest (processed ++ [⟨.inr (.inl stateIn), stateOut⟩]) st'
              (out ++ mappedNewEntries)
        | ⟨.inr (.inr (.inr stateOut)), stateIn⟩ =>
            -- Normalize an inverse occurrence into the raw prefix for all later Backtrack calls.
            go rest (processed ++ [⟨.inr (.inr stateOut), stateIn⟩]) st out
  go log [] { trStd := [], trStdLA := [] } []

/-- §5.5.2 `D2STrace` public projection.  This is intentionally defined by projection from the
lossless execution above, so the public trace and the coupling-visible encoded trace are produced
by one run with one sequence of random-fiber samples. -/
noncomputable def d2sTraceSalted
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) := do
  let observation ← d2sTraceSaltedObserved
    (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log
  pure observation.output

section Line4Trace

/-- Decode just the encoded-challenge responses in a tagged H₁ log.  Ambient entries, tags,
and encoded query keys are retained verbatim.  This is the log-level Eq. (52) projection used
by the exact H₁--H₂ reparameterization. -/
def decodeTaggedGLog
    (log : TaggedQueryLog (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    TaggedQueryLog (oSpec + eSpec (U := U) StmtIn pSpec δ) :=
  log.map fun ⟨tag, entry⟩ =>
    match entry with
    | ⟨.inl query, response⟩ => ⟨tag, ⟨.inl query, response⟩⟩
    | ⟨.inr ⟨roundIdx, key⟩, response⟩ =>
        ⟨tag, ⟨.inr ⟨roundIdx, key⟩, codec.decode roundIdx response⟩⟩

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

/-- The H₁ line-4 map factors through the decoded tagged log: `Hyb₁` performs the response
decode itself, while `Hyb₂` receives that decoded response from its Eq. (52) oracle.  Thus the
two post-processing maps are exactly equal once the raw H₁ log is projected by
`decodeTaggedGLog`. -/
theorem hyb1Line4Trace_eq_hyb2Line4Trace_decodeTaggedGLog
    {Salt : Type} [SaltCodec U δ Salt]
    (log : TaggedQueryLog (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    hyb1Line4Trace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (Salt := Salt) log =
      hyb2Line4Trace (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (Salt := Salt)
        (decodeTaggedGLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (δ := δ) log) := by
  unfold hyb1Line4Trace hyb2Line4Trace decodeTaggedGLog
  simp only [List.filterMap_map]
  congr
  funext entry
  rcases entry with ⟨tag, entry⟩
  rcases entry with ⟨query, response⟩
  cases query with
  | inl query => rfl
  | inr query =>
      rcases query with ⟨roundIdx, key⟩
      simp only [hyb1RemapEntry?, hyb2RemapEntry?]
      all_goals
        dsimp [Function.comp_def]
        aesop

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
