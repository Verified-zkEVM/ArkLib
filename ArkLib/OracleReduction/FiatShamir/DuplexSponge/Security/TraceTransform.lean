/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead

/-!
# Trace Transformations

This file contains the trace transformations for duplex sponge Fiat-Shamir, following Section 5.5 in
the paper.
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
responses. -/
@[inline, reducible]
def section58EncodedChallengeOracleInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    ∀ i, OracleInterface (Vector U (challengeSize (pSpec := pSpec) i)) := fun i =>
  { Query :=
      StmtIn × List U ×
        List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))
    toOC.spec := fun _ => Vector U (challengeSize (pSpec := pSpec) i)
    toOC.impl := fun _ => read }

/-- Oracle family for the `gᵢ` queries in Section 5.8 `Hyb₁`. -/
@[inline, reducible]
def section58EncodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (section58EncodedChallengeOracleInterface (U := U) StmtIn pSpec i).Query)) :=
  [fun i => Vector U (challengeSize (pSpec := pSpec) i)]ₒ'
    (section58EncodedChallengeOracleInterface (U := U) StmtIn pSpec)

/-- Section 5.8 `Hyb₂` challenge-oracle surface: encoded prover-prefix queries, decoded verifier
responses. -/
@[inline, reducible]
def section58DecodedChallengeOracleInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) [HasMessageSize pSpec] :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query :=
      StmtIn × List U ×
        List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

/-- Oracle family for the `eᵢ` queries in Section 5.8 `Hyb₂`. -/
@[inline, reducible]
def section58DecodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) [HasMessageSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (section58DecodedChallengeOracleInterface (U := U) StmtIn pSpec i).Query)) :=
  [pSpec.Challenge]ₒ'
    (section58DecodedChallengeOracleInterface (U := U) StmtIn pSpec)

/-- Paper-facing key for `StdTrace` memoized `gᵢ`-style entries (CO25 §5.2 Step 4.D output;
strict shape `BacktrackOutput`). -/
private abbrev StdTraceQuery :=
  Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

-- TODO(section5-cleanup): parallel to ProverTransform.D2SStdEntry but stores deserialized challenge
-- vectors instead of rate blocks. Consider a shared key plus two response wrappers later.
/-- One query-answer pair in `tr_std` / `tr_std^LA`. -/
private structure StdTraceEntry where
  query : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  response : Vector U (challengeSize query.roundIdx)

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
                                (U := U) (codec := codec)))
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
                                (U := U) (codec := codec)))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (response : Vector U (challengeSize q.roundIdx)) :
    List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec)
                        (U := U) (codec := codec)) :=
  memo ++ [{ query := q, response := response }]

/-! ## Paper-faithful StdTrace helpers (CO25 §5.5.1)

These helpers implement the paper's exact `∀ι, α̂_ι ∈ Im(φ_ι)` codec-image predicate and the
deterministic `e_i := ψ_i(ρ̂_i)` entry remap. They are forward-declared here so that the
single `StdTrace` pipeline (and its abort analysis) can use them without exposing a free
predicate/function field. -/

-- TODO(section5-cleanup): duplicate of the Backtrack.lean helper. Consider moving to a shared
-- small utility module once the parser/projection APIs stop changing.
private def vectorOfListExact
    (len : Nat) (xs : List U) : Option (Vector U len) := by
  let ys := xs.take len
  if hLen : ys.length = len then
    exact some ⟨ys.toArray, by simpa using hLen⟩
  else
    exact none

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
    (encodedMessages :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) := by
  classical
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
                match lookupEncodedMessage? (pSpec := pSpec) encodedMessages msgIdx with
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

private def encodedMessageAtOffset?
    (absorbedRatePrefix : List (Vector U SpongeSize.R))
    (offsetBlocks : Nat)
    (msgIdx : pSpec.MessageIdx) :
    Option (Vector U (messageSize msgIdx)) := by
  let rateBlocks := (absorbedRatePrefix.drop offsetBlocks).take (pSpec.Lₚᵢ msgIdx)
  let unitBlocks := rateBlocks.foldl (fun acc block => acc ++ block.toList) []
  exact vectorOfListExact (U := U) (messageSize msgIdx) unitBlocks

/-- Recover the basic-FS prover-message prefix encoded by a Section 5.8 absorbed-prefix query key.

This walks the protocol round structure in order and slices the absorbed-rate prefix according to
the message/challenge block counts `Lₚ(i)` / `Lᵥ(i)`. Message blocks are turned back into
`pSpec.Message` values by choosing a preimage under `Serialize` when one exists. -/
private noncomputable def absorbedPrefixMessagesUpTo?
    (roundIdx : pSpec.ChallengeIdx)
    (absorbedRatePrefix : List (Vector U SpongeSize.R)) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) := by
  classical
  let build : (k : Fin (n + 1)) → Option (pSpec.MessagesUpTo k × Nat) :=
    Fin.induction
      (some (default, 0))
      (fun j ih =>
        match ih with
        | none => none
        | some (messages, offsetBlocks) =>
            match hDir : pSpec.dir j with
            | .P_to_V =>
                let msgIdx : pSpec.MessageIdx := ⟨j, hDir⟩
                match encodedMessageAtOffset?
                    (pSpec := pSpec) (U := U)
                    absorbedRatePrefix offsetBlocks msgIdx with
                | none => none
                | some encodedMsg =>
                    match chooseSerializedMessage?
                        (pSpec := pSpec) (U := U) msgIdx encodedMsg with
                    | none => none
                    | some msg =>
                        some
                          (ProtocolSpec.MessagesUpTo.concat
                            (pSpec := pSpec) messages hDir msg,
                            offsetBlocks + pSpec.Lₚᵢ msgIdx)
            | .V_to_P =>
                let chalIdx : pSpec.ChallengeIdx := ⟨j, hDir⟩
                some
                  (ProtocolSpec.MessagesUpTo.extend
                    (pSpec := pSpec) messages hDir,
                    offsetBlocks + pSpec.Lᵥᵢ chalIdx))
  exact (build roundIdx.1.castSucc).map Prod.fst

private noncomputable def stdTraceMessagesUpTo?
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (pSpec.MessagesUpTo q.roundIdx.1.castSucc) :=
  encodedMessagesUpTo? (codec := codec) (pSpec := pSpec) (U := U)
    q.roundIdx (EncodedMessagesUpTo.toList q.encodedMessages)

/-- CO25 §5.5.1 Item 4(a)iii — paper-faithful `∀ι, α̂_ι ∈ Im(φ_ι)` codec-image predicate over
StdTrace backtrack outputs. This is the canonical inCodecImage check baked into `stdTraceEntries`
in place of the previous free `BacktrackOutput → Bool` parameter (see D5.2 in audit-report.md). -/
private noncomputable def paperStdTraceInCodecImage
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let stdQuery : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := out
  match stdTraceMessagesUpTo? (codec := codec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stdQuery with
  | some _ => true
  | none => false

/-- CO25 §5.5.1 Item 4(a)v — paper-faithful `e_i := ψ_i(ρ̂_i)` entry remap. Partial because
the codec-image preimage may not exist; callers compose with `paperStdTraceInCodecImage` to
guarantee `some`. -/
private noncomputable def paperStdTraceEntryToFSQuery?
    (entry : StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    Option (Sigma (fsChallengeOracle StmtIn pSpec)) := do
  let messagesUpTo ←
    stdTraceMessagesUpTo? (codec := codec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      entry.query
  let challenge : pSpec.Challenge entry.query.roundIdx :=
    Deserialize.deserialize entry.response
  pure ⟨⟨entry.query.roundIdx, (entry.query.stmt, messagesUpTo)⟩, challenge⟩

/-- Public wrapper for the Section 5.8 `φ⁻¹` parser from absorbed-rate prefixes to basic-FS
message prefixes. This is the prover-prefix recovery used both by the line-4 trace maps and by the
canonical Section 5.8 hybrid experiments. -/
noncomputable def section58AbsorbedPrefixMessagesUpTo?
    (roundIdx : pSpec.ChallengeIdx)
    (absorbedRatePrefix : List (Vector U SpongeSize.R)) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) :=
  absorbedPrefixMessagesUpTo? (codec := codec)
    (pSpec := pSpec) (U := U)
    roundIdx absorbedRatePrefix

/-- Public wrapper for the Section 5.8 `φ⁻¹` parser from the paper-facing encoded-message tuple
returned by `BackTrack` to basic-FS message prefixes. -/
noncomputable def section58EncodedMessagesUpTo?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedMessages :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) :=
  encodedMessagesUpTo? (codec := codec)
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

/-- Compute paper-facing `StdTrace` query-answer entries (`tr_std`) from a full mixed log.

This implements Section 5.5.1 Item 4(a) control-flow over the DS entries:
- abort on `backTrack = err` or `lookAhead = err`,
- skip on `backTrack = none` or non-challenge backtrack tuples,
- skip when `paperStdTraceInCodecImage` rejects the backtrack output (CO25 §5.5.1 Item 4(a)iii),
- memoize `LookAhead` outputs in `tr_std^LA` keyed by backtrack tuples.

D5.2 (audit-report.md): the codec-image predicate is now baked in as
`paperStdTraceInCodecImage` rather than a free `BacktrackOutput → Bool` parameter, eliminating
the prior non-paper-faithful adversarial instantiation surface. -/
private noncomputable def stdTraceEntries
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (List (StdTraceEntry
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))) :=
  let dsTrace := dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U) log
  -- Paper StdTrace step 3 (lines 1146–1149): bulk-init `tr_∇` once over `dsTrace`.
  -- Built via generic `TraceNabla.ofQueryLog` with explicit list-backed instantiation; the
  -- generic helper `stdTraceEntriesGeneric` (below) is the parameterized surface for Phase D.
  let dsTrΔ :
      TraceNabla
        (ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
        (ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
        StmtIn U :=
    TraceNabla.ofQueryLog dsTrace
  let rec go
      (remaining : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (trStd trStdLA : List (StdTraceEntry
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))) :
      OptionT (OracleComp (Unit →ₒ U))
        (List (StdTraceEntry
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))) := do
    match remaining with
    | [] =>
        pure trStd
    | entry :: rest =>
        match entry with
        | ⟨.inl _, _⟩ =>
            go rest trStd trStdLA
        | ⟨.inr (.inl _), _⟩ =>
            go rest trStd trStdLA
        | ⟨.inr (.inr (.inr _)), _⟩ =>
            go rest trStd trStdLA
        | ⟨.inr (.inr (.inl stateIn)), _stateOut⟩ =>
            match
                (backTrack (δ := δ)
                  (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
                  dsTrΔ (dsTrace.length + 1) stateIn).run with
            | none =>
                failure
            | some none =>
                go rest trStd trStdLA
            | some (some backtrackOut) =>
                if paperStdTraceInCodecImage (codec := codec)
                    (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
                    backtrackOut then
                  let roundIdx := backtrackOut.roundIdx
                  let stdQuery :
                      StdTraceQuery
                        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
                    backtrackOut
                  match lookupStdTraceMemo
                      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                      trStdLA stdQuery with
                  | some rhoHat =>
                      let stdEntry :
                          StdTraceEntry
                            (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                            (codec := codec) :=
                        { query := stdQuery, response := rhoHat }
                      go rest (trStd ++ [stdEntry]) trStdLA
                  | none => do
                      let rhoHat? ←
                        lookAhead (pSpec := pSpec) (U := U)
                          dsTrΔ.p stateIn roundIdx
                      match rhoHat? with
                      | none =>
                          go rest trStd trStdLA
                      | some rhoHat =>
                          let stdEntry :
                              StdTraceEntry
                                (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                                (codec := codec) :=
                            { query := stdQuery, response := rhoHat }
                          let trStdLA' :=
                            insertStdTraceMemo
                              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                              trStdLA stdQuery rhoHat
                          go rest (trStd ++ [stdEntry]) trStdLA'
                else
                  go rest trStd trStdLA
  go log [] []

/-- Map synthesized `StdTrace` entries to basic-FS challenge-log entries via the paper-faithful
`paperStdTraceEntryToFSQuery?` (CO25 §5.5.1 Item 4(a)v). Entries whose codec preimage is missing
are dropped; under `stdTraceEntries`'s baked-in `paperStdTraceInCodecImage` filter, every entry
that survives has `stdTraceMessagesUpTo? entry.query = some _`, so the remap returns `some` on
every input in practice. D5.2 (audit-report.md): replaces the prior free `mapEntry` field. -/
private noncomputable def remapStdTraceEntries
    (entries : List (StdTraceEntry
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))) :
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) :=
  entries.filterMap fun entry =>
    match paperStdTraceEntryToFSQuery? (codec := codec)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) entry with
    | none => none
    | some mapped => some ⟨.inr mapped.1, mapped.2⟩

/-- §5.5.1 `StdTrace` single-log surface (Item 4(a) control flow).

Synthesized `StdTrace` entries are remapped into FS challenge-log entries via the paper-faithful
`paperStdTraceEntryToFSQuery?` (Item 4(a)v) and appended to the shared-oracle projection,
implementing the paper's single-log `tr_std` transform. The codec-image predicate
(Item 4(a)iii) is baked into `stdTraceEntries` directly via `paperStdTraceInCodecImage`;
no free remap field is exposed. -/
noncomputable def stdTraceSingle
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let entries ←
    stdTraceEntries (δ := δ) (codec := codec)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  let sharedLog :=
    projectSharedQueryLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log
  let remappedLog :=
    remapStdTraceEntries (δ := δ) (codec := codec)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) entries
  pure (sharedLog ++ remappedLog)

/-- §5.5 / §5.8 single-log `D2STrace` surface — paper-faithful alias for `stdTraceSingle`.

CO25 §5.5.1 Item 4(a)iii (`∀ι, α̂_ι ∈ Im(φ_ι)` codec-image filter) and Item 4(a)v
(`e_i := ψ_i(ρ̂_i)` entry remap) are both baked in via `paperStdTraceInCodecImage` /
`paperStdTraceEntryToFSQuery?`. Used by KeyLemma at the §5.8 hybrid distance bounds. -/
noncomputable def paperD2STraceSingle
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  stdTraceSingle (codec := codec) (δ := δ)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) log

/-! ## Salted FS variants (CO25 §5.5.1 Item 4(a)v paper-faithful)

The paper's `f_i(x, τ, α_1, …, α_i)` query keeps the public salt `τ ∈ Σ^δ` threaded through the
augmented statement, matching the encoding-A oracle `fsChallengeOracle (Vector U δ × StmtIn) pSpec`
already used in `SingleSalt.lean`. The salted variants below are net-new surfaces consumed by
`KeyLemma`'s Section 5.8 hybrids; the unsalted helpers above are kept for compatibility. -/

/-- Salted variant of `paperStdTraceEntryToFSQuery?` — preserves the BackTrack salt
`out.salt : Vector U δ` in the augmented statement of the salted FS oracle query. -/
private noncomputable def paperStdTraceEntryToFSQuerySalted?
    (entry : StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    Option (Sigma (fsChallengeOracle (Vector U δ × StmtIn) pSpec)) := do
  let messagesUpTo ←
    stdTraceMessagesUpTo? (codec := codec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      entry.query
  let challenge : pSpec.Challenge entry.query.roundIdx :=
    Deserialize.deserialize entry.response
  pure ⟨⟨entry.query.roundIdx, ((entry.query.salt, entry.query.stmt), messagesUpTo)⟩, challenge⟩

/-- Salted variant of `remapStdTraceEntries` — produces a salted-FS query log. -/
private noncomputable def remapStdTraceEntriesSalted
    (entries : List (StdTraceEntry
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))) :
    QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec) :=
  entries.filterMap fun entry =>
    match paperStdTraceEntryToFSQuerySalted? (codec := codec)
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
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)) := do
  let entries ←
    stdTraceEntries (δ := δ) (codec := codec)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  let sharedLog :=
    projectSharedQueryLogSalted (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) log
  let remappedLog :=
    remapStdTraceEntriesSalted (δ := δ) (codec := codec)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) entries
  pure (sharedLog ++ remappedLog)

/-- Salted variant of `paperD2STraceSingle` — output is keyed by the salted FS oracle. Used by
`KeyLemma`'s Section 5.8 Hyb₁/Hyb₂/Hyb₃ to keep the salt on every challenge query. -/
noncomputable def paperD2STraceSingleSalted
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle (Vector U δ × StmtIn) pSpec)) :=
  stdTraceSingleSalted (codec := codec) (δ := δ)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) log

/-- Projection-only compatibility conversion for a single DSFS log.

This keeps the legacy behavior: execute `StdTrace` abort checks, but export only shared-oracle log
entries. -/
-- TODO(section5-cleanup): legacy projection-only wrapper. Reassess after BadEvents.lean is settled;
-- delete it if no external compatibility need remains.
noncomputable def stdTraceSingleProjected
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let _ ←
    stdTraceEntries (δ := δ) (codec := codec)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  pure <| projectSharedQueryLog
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log

/-- §5.5 projection-only single-log `D2STrace`: runs abort check but exports only shared-oracle
entries (no FS-challenge remap). -/
-- TODO(section5-cleanup): projection-only compatibility alias. Prefer `paperD2STraceSingle` for
-- paper-facing Section 5.8 statements.
noncomputable def d2STraceSingleProjected
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  stdTraceSingleProjected (δ := δ) (codec := codec)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    log

section PaperTrace

/-- Section 5.8 `Hyb₁` line-4 trace translation.

This is the explicit `(φ⁻¹, ψ)(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def section58Hyb1Line4Trace
    (log : QueryLog (oSpec + section58EncodedChallengeOracle (U := U) StmtIn pSpec)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let remappedLog := log.filterMap fun entry =>
    match entry with
    | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
    | ⟨.inr query, response⟩ =>
        match query with
        | ⟨roundIdx, (stmt, _salt, encodedMessages)⟩ =>
            match section58EncodedMessagesUpTo? (codec := codec)
                (pSpec := pSpec) (U := U) roundIdx encodedMessages with
            | none => none
            | some messagesUpTo =>
                let responseVec :
                    Vector U (challengeSize (pSpec := pSpec) roundIdx) := response
                let challenge : pSpec.Challenge roundIdx :=
                  Deserialize.deserialize responseVec
                some ⟨.inr ⟨roundIdx, (stmt, messagesUpTo)⟩, challenge⟩
  pure remappedLog

/-- Section 5.8 `Hyb₂` line-4 trace translation.

This is the explicit `φ⁻¹(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def section58Hyb2Line4Trace
    (log : QueryLog (oSpec + section58DecodedChallengeOracle (U := U) StmtIn pSpec)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let remappedLog := log.filterMap fun entry =>
    match entry with
    | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
    | ⟨.inr ⟨roundIdx, (stmt, _salt, encodedMessages)⟩, challenge⟩ =>
        match section58EncodedMessagesUpTo? (codec := codec)
            (pSpec := pSpec) (U := U) roundIdx encodedMessages with
        | none => none
        | some messagesUpTo =>
            some ⟨.inr ⟨roundIdx, (stmt, messagesUpTo)⟩, challenge⟩
  pure remappedLog

/-- Section 5.8 `Hyb₃` line-4 trace translation.

This is the identity-on-line-4 trace surface from the paper, viewed through the common
single-log Section 5 interface used by `KeyLemma`. -/
noncomputable def section58Hyb3Line4Trace
    (log : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  pure log

end PaperTrace

/-- Optional `StdTrace` two-log wrapper (Section 5.5.1 shape); returns `none` on abort. -/
noncomputable def duplexSpongeToBasicFSTrace?
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let proveLogFS ←
    stdTraceSingle (codec := codec)
      (δ := δ) (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      proveQueryLog
  let verifyLogFS ←
    stdTraceSingle (codec := codec) (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      verifyQueryLog
  pure (proveLogFS, verifyLogFS)

-- TODO(section5-cleanup): projection-only compatibility wrapper; likely removable if no downstream
-- code still depends on the old projected-trace behavior.
/-- §5.5 projection-only two-log compatibility wrapper; returns `none` on abort. -/
noncomputable def duplexSpongeToBasicFSTraceProjected?
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let proveLogFS ← stdTraceSingleProjected (δ := δ)
    (codec := codec)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec)
    (U := U) proveQueryLog
  let verifyLogFS ← stdTraceSingleProjected (δ := δ)
    (codec := codec)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec)
    (U := U) verifyQueryLog
  pure (proveLogFS, verifyLogFS)

/-- The trace transformation in Section 5.5, from DSFS logs to basic-FS logs.
Returns `none` when `StdTrace` aborts. -/
noncomputable def duplexSpongeToBasicFSTrace
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTrace? (δ := δ) (codec := codec)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    proveQueryLog verifyQueryLog

-- TODO(section5-cleanup): projection-only compatibility wrapper; keep out of new Section 5 proofs
-- unless the projected trace is explicitly required.
/-- §5.5 projection-only two-log trace transformation. -/
noncomputable def duplexSpongeToBasicFSTraceProjected
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTraceProjected? (δ := δ) (codec := codec)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    proveQueryLog verifyQueryLog

/-- §5.5 `D2STrace` two-log surface (prover + verifier logs). -/
noncomputable def d2STrace
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTrace (δ := δ) (codec := codec)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    proveQueryLog verifyQueryLog

-- TODO(section5-cleanup): projection-only alias retained for compatibility. Prefer `d2STrace` for
-- paper-faithful trace transformation once BadEvents.lean cleanup is complete.
/-- §5.5 projection-only `D2STrace` two-log surface (no FS-challenge remap). -/
noncomputable def d2STraceProjected
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTraceProjected (δ := δ) (codec := codec)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    proveQueryLog verifyQueryLog

end

end DuplexSpongeFS.TraceTransform

-- TODO: move core defs to outer file
