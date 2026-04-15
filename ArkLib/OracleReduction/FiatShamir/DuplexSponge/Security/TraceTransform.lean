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
query-log entries. -/
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
