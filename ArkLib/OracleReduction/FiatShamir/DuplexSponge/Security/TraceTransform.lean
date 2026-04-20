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

namespace DuplexSpongeFS

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [HasChallengeSize pSpec]

noncomputable section

/-- Section 5.8 `Hyb₁` challenge-oracle surface: encoded prover-prefix queries, encoded verifier
responses. -/
@[inline, reducible]
def section58EncodedChallengeOracleInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) [HasChallengeSize pSpec] :
    ∀ i, OracleInterface (Vector U (challengeSize (pSpec := pSpec) i)) := fun i =>
  { Query := StmtIn × List (Vector U SpongeSize.R)
    toOC.spec := fun _ => Vector U (challengeSize (pSpec := pSpec) i)
    toOC.impl := fun _ => read }

/-- Oracle family for the `gᵢ` queries in Section 5.8 `Hyb₁`. -/
@[inline, reducible]
def section58EncodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) [HasChallengeSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (section58EncodedChallengeOracleInterface (U := U) StmtIn pSpec i).Query)) :=
  [fun i => Vector U (challengeSize (pSpec := pSpec) i)]ₒ'
    (section58EncodedChallengeOracleInterface (U := U) StmtIn pSpec)

/-- Section 5.8 `Hyb₂` challenge-oracle surface: encoded prover-prefix queries, decoded verifier
responses. -/
@[inline, reducible]
def section58DecodedChallengeOracleInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query := StmtIn × List (Vector U SpongeSize.R)
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

/-- Oracle family for the `eᵢ` queries in Section 5.8 `Hyb₂`. -/
@[inline, reducible]
def section58DecodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (section58DecodedChallengeOracleInterface (U := U) StmtIn pSpec i).Query)) :=
  [pSpec.Challenge]ₒ'
    (section58DecodedChallengeOracleInterface (U := U) StmtIn pSpec)

/-- Paper-facing key for `StdTrace` memoized `gᵢ`-style entries (Section 5.5.1 Item 4(a)iv). -/
private structure StdTraceQuery where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  absorbedRatePrefix : List (Vector U SpongeSize.R)

/-- One query-answer pair in `tr_std` / `tr_std^LA`. -/
private structure StdTraceEntry where
  query : StdTraceQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  response : Vector U (challengeSize query.roundIdx)

/-- Project DS-oracle entries from a mixed `oSpec + DS` log. -/
private def dsTraceOfLog
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl _, _⟩ => none
    | ⟨.inr q, r⟩ => some ⟨q, r⟩

/-- Forward-permutation projection `tr.p` of a DS trace. -/
private def forwardPermTraceOfDS
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (forwardPermutationOracle (CanonicalSpongeState U)) :=
  trace.filterMap fun entry =>
    match entry with
    | ⟨.inr (.inl stateIn), stateOut⟩ => some ⟨stateIn, stateOut⟩
    | _ => none

/-- Recover the challenge-round index (if any) from a `BackTrack` output. -/
private def challengeIdxOfBacktrackOutput
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) :
    Option pSpec.ChallengeIdx := by
  if hRound : out.round.1 < n then
    let roundFin : Fin n := ⟨out.round.1, hRound⟩
    if hDir : pSpec.dir roundFin = Direction.V_to_P then
      exact some ⟨roundFin, hDir⟩
    else
      exact none
  else
    exact none

/-- Lookup of a prior `tr_std^LA` entry with the same query key. -/
private def lookupStdTraceMemo
    (memo : List (StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
    (q : StdTraceQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Vector U (challengeSize q.roundIdx)) := by
  classical
  exact memo.findSome? fun entry =>
    if hEq : entry.query = q then
      some (hEq ▸ entry.response)
    else
      none

/-- Insert a fresh query-answer pair into `tr_std^LA` order. -/
private def insertStdTraceMemo
    (memo : List (StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
    (q : StdTraceQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (response : Vector U (challengeSize q.roundIdx)) :
    List (StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  memo ++ [{ query := q, response := response }]

/-- Keep only shared-oracle entries from a DSFS query log, and reinterpret them as basic-FS
query-log entries. Needed in `stdTraceSingleWithRemap`,
where the output is `sharedLog ++ remappedLog`. -/
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
- memoize `LookAhead` outputs in `tr_std^LA` keyed by backtrack tuples. -/
private def stdTraceEntries
    (inCodecImage :
      BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Bool := fun _ => true)
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (List (StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :=
  let dsTrace := dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U) log
  let fwdPermTrace := forwardPermTraceOfDS (StmtIn := StmtIn) (U := U) dsTrace
  let rec go
      (remaining : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (trStd trStdLA : List (StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :
      OptionT (OracleComp (Unit →ₒ U))
        (List (StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) := do
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
                (backTrack
                  (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
                  dsTrace stateIn).run with
            | none =>
                failure
            | some none =>
                go rest trStd trStdLA
            | some (some backtrackOut) =>
                if inCodecImage backtrackOut then
                  match challengeIdxOfBacktrackOutput
                      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) backtrackOut with
                  | none =>
                      go rest trStd trStdLA
                  | some roundIdx =>
                      let stdQuery :
                          StdTraceQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
                        { roundIdx := roundIdx
                          stmt := backtrackOut.stmt
                          absorbedRatePrefix := backtrackOut.absorbedRatePrefix }
                      match lookupStdTraceMemo
                          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                          trStdLA stdQuery with
                      | some rhoHat =>
                          let stdEntry :
                              StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
                            { query := stdQuery, response := rhoHat }
                          go rest (trStd ++ [stdEntry]) trStdLA
                      | none => do
                          let rhoHat? ←
                            lookAhead (pSpec := pSpec) (U := U) fwdPermTrace stateIn roundIdx
                          match rhoHat? with
                          | none =>
                              go rest trStd trStdLA
                          | some rhoHat =>
                              let stdEntry :
                                  StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
                                { query := stdQuery, response := rhoHat }
                              let trStdLA' :=
                                insertStdTraceMemo
                                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                                  trStdLA stdQuery rhoHat
                              go rest (trStd ++ [stdEntry]) trStdLA'
                else
                  go rest trStd trStdLA
  go log [] []

/-- Explicit remap from synthesized `StdTrace` entries to basic-FS challenge-log entries. -/
structure StdTraceToFSRemap where
  /-- Codec-image test for backtrack outputs used to model Item 4(a)iii in `StdTrace`. -/
  inCodecImage :
    BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Bool := fun _ => true
  mapEntry :
    StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U) →
      Sigma (fsChallengeOracle StmtIn pSpec)

private def remapStdTraceEntries
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entries : List (StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :
    QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) :=
  entries.map fun entry =>
    let mapped := remap.mapEntry entry
    ⟨.inr mapped.1, mapped.2⟩

/-- `StdTrace` conversion with an explicit FS challenge-log remap of synthesized entries. -/
def stdTraceSingleWithRemap
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let entries ←
    stdTraceEntries
      (inCodecImage := remap.inCodecImage)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  let sharedLog :=
    projectSharedQueryLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log
  let remappedLog :=
    remapStdTraceEntries (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      remap entries
  pure (sharedLog ++ remappedLog)

/-- `StdTrace`-style conversion for a single DSFS log, with explicit remap.

This is the paper-primary surface: synthesized `StdTrace` entries are remapped into FS challenge-log
entries and appended to the shared-oracle projection. -/
def stdTraceSingle
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  stdTraceSingleWithRemap
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap log

/-- Projection-only compatibility conversion for a single DSFS log.

This keeps the legacy behavior: execute `StdTrace` abort checks, but export only shared-oracle log
entries. -/
def stdTraceSingleProjected
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let _ ←
    stdTraceEntries
      (inCodecImage := fun _ => true)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  pure <| projectSharedQueryLog
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log

/-- Single-log remap-aware `D2STrace` surface for Section 5.5 / 5.8. -/
def d2STraceSingleWithRemap
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  stdTraceSingleWithRemap
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap log

/-- Single-log `D2STrace` surface for Section 5.5 / 5.8. -/
def d2STraceSingle
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  stdTraceSingle
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap log

/-- Projection-only single-log `D2STrace` compatibility surface. -/
def d2STraceSingleProjected
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  stdTraceSingleProjected
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    log

section PaperTrace

variable [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]
  [∀ i, Fintype (pSpec.Message i)]

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

/-- Public wrapper for the Section 5.8 `φ⁻¹` parser from absorbed-rate prefixes to basic-FS
message prefixes. This is the prover-prefix recovery used both by the line-4 trace maps and by the
canonical Section 5.8 hybrid experiments. -/
noncomputable def section58AbsorbedPrefixMessagesUpTo?
    (roundIdx : pSpec.ChallengeIdx)
    (absorbedRatePrefix : List (Vector U SpongeSize.R)) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) :=
  absorbedPrefixMessagesUpTo?
    (pSpec := pSpec) (U := U)
    roundIdx absorbedRatePrefix

private noncomputable def stdTraceMessagesUpTo?
    (q : StdTraceQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (pSpec.MessagesUpTo q.roundIdx.1.castSucc) :=
  absorbedPrefixMessagesUpTo? q.roundIdx q.absorbedRatePrefix

private noncomputable def paperStdTraceInCodecImage
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) : Bool :=
  match challengeIdxOfBacktrackOutput
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) out with
  | none => false
  | some roundIdx =>
      let stdQuery :
          StdTraceQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
        { roundIdx := roundIdx
          stmt := out.stmt
          absorbedRatePrefix := out.absorbedRatePrefix }
      match stdTraceMessagesUpTo?
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stdQuery with
      | some _ => true
      | none => false

private noncomputable def paperStdTraceEntryToFSQuery?
    (entry : StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Sigma (fsChallengeOracle StmtIn pSpec)) := do
  let messagesUpTo ←
    stdTraceMessagesUpTo?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      entry.query
  let challenge : pSpec.Challenge entry.query.roundIdx :=
    Deserialize.deserialize entry.response
  pure ⟨⟨entry.query.roundIdx, (entry.query.stmt, messagesUpTo)⟩, challenge⟩

/-- Exact paper-facing single-log `D2STrace` witness.

Unlike `stdTraceSingleProjected`, this reconstructs the Fiat-Shamir challenge-log entries produced
by `StdTrace` and appends them to the shared-oracle projection, matching the paper's single-log
`tr'` surface. The remapping is defined directly here because, under the current ArkLib codec
surface, the exact remap is naturally partial until the codec-image check succeeds. -/
noncomputable def paperD2STraceSingle
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let entries ←
    stdTraceEntries
      (inCodecImage := paperStdTraceInCodecImage
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      log
  let sharedLog :=
    projectSharedQueryLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log
  let remappedLog :=
    entries.filterMap fun entry =>
      match paperStdTraceEntryToFSQuery?
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) entry with
      | some mapped => some ⟨.inr mapped.1, mapped.2⟩
      | none => none
  pure (sharedLog ++ remappedLog)

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
        | ⟨roundIdx, (stmt, absorbedRatePrefix)⟩ =>
            match absorbedPrefixMessagesUpTo?
                roundIdx absorbedRatePrefix with
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
    | ⟨.inr ⟨roundIdx, (stmt, absorbedRatePrefix)⟩, challenge⟩ =>
        match absorbedPrefixMessagesUpTo?
            roundIdx absorbedRatePrefix with
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

/-- Optional `StdTrace` wrapper with explicit remap for synthesized challenge entries. -/
def duplexSpongeToBasicFSTraceWithRemap?
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let proveLogFS ←
    stdTraceSingleWithRemap
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap proveQueryLog
  let verifyLogFS ←
    stdTraceSingleWithRemap
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap verifyQueryLog
  pure (proveLogFS, verifyLogFS)

/-- Optional `StdTrace` wrapper (Section 5.5.1 shape): returns `none` on abort. -/
def duplexSpongeToBasicFSTrace?
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTraceWithRemap?
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap proveQueryLog verifyQueryLog

/-- Projection-only compatibility wrapper: returns `none` on abort. -/
def duplexSpongeToBasicFSTraceProjected?
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let proveLogFS ← stdTraceSingleProjected
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec)
    (U := U) proveQueryLog
  let verifyLogFS ← stdTraceSingleProjected
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec)
    (U := U) verifyQueryLog
  pure (proveLogFS, verifyLogFS)

/-- The remap-aware trace transformation in Section 5.5, from DSFS logs to basic-FS logs. -/
def duplexSpongeToBasicFSTraceWithRemap
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTraceWithRemap?
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap proveQueryLog verifyQueryLog

/-- The trace transformation in Section 5.5, from DSFS logs to basic-FS logs.
Returns `none` when `StdTrace` aborts. -/
def duplexSpongeToBasicFSTrace
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTrace?
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap proveQueryLog verifyQueryLog

/-- Projection-only compatibility trace transformation. -/
def duplexSpongeToBasicFSTraceProjected
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTraceProjected?
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    proveQueryLog verifyQueryLog

noncomputable def d2STraceWithRemap
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTraceWithRemap
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap proveQueryLog verifyQueryLog

noncomputable def d2STrace
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTrace
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    remap proveQueryLog verifyQueryLog

noncomputable def d2STraceProjected
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (verifyQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
      OptionT (OracleComp (Unit →ₒ U))
        (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec) ×
          QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  duplexSpongeToBasicFSTraceProjected
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    proveQueryLog verifyQueryLog

end

end DuplexSpongeFS

-- TODO: move core defs to outer file
