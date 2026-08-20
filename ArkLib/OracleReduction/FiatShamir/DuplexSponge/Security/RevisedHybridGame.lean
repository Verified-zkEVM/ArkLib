/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SecurityGames
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedForward
import ArkLib.ToVCVio.OracleComp.SimSemantics.ExceptT.Basic
import ArkLib.ToVCVio.ToMathlib.Control.StateT

/-!
# Stateful Section 5 hybrid-game executor

This module is the executable migration boundary for CO25 Section 5.8.  It keeps the existing
Figure-4 game shape and eager challenge-family sampling, but replaces the legacy
`D2SQueryState` interpreter by the stateful `D2SNormalState` interpreter from
`d2fRawRevised`.  Therefore every successful prover or verifier segment has passed `Monitor`,
while a first bad occurrence or a search/parser failure takes the existing abort path.

The legacy `KeyLemma.hybridGame` remains available for comparison only.  New revised Hyb₁--Hyb₃
instances must use `hybridGameRevised` below; this prevents the obsolete Step 4.d table-or-fresh
handler from silently re-entering the updated Lemma 5.8 path.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction.OracleDistribution

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : CodecCore pSpec U]
  {δ : Nat} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]

/-- The two legal Figure-4 phase outcomes under the revised D2SQuery executor.

The old observation stored separate prover and verifier `Except` values, which admitted an
impossible state: a stopped prover followed by a verifier run on default inputs and a fresh D2S
state.  This inductive type makes the paper's absorbing-stop rule structural.  In its `verifier`
case, the verifier begins from the successful prover result's exact normal state and memo. -/
inductive HybridGameRevisedPhase
    {κ : Type} (oSpec : OracleSpec ι) (challengeSpec : OracleSpec κ) (T_H T_P M : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U] where
  | proverStopped
      (reason : D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (proverRawLog : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))
  | verifier
      (proverRun : (((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M))
      (verifierResult : Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((Option StmtOut ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M))
      (proverRawLog verifierRawLog :
        QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))

/-- The same legal prover/verifier phase boundary with its outer log carrier made explicit.

This is the reusable coupling form of `HybridGameRevisedPhase`: the game result, normal state,
and memo are unchanged, while a proof may choose a log representation different from the oracle
specification being executed.  In particular, the fixed-table H₂ proof records the encoded H₁
representative for each decoded H₂ request and later decodes that log back to the ordinary H₂
log. -/
inductive HybridGameRevisedPhaseWithLog
    {κ : Type} (oSpec : OracleSpec ι) (challengeSpec : OracleSpec κ) (T_H T_P M Log : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U] where
  | proverStopped
      (reason : D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (proverRawLog : Log)
  | verifier
      (proverRun : (((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M))
      (verifierResult : Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((Option StmtOut ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M))
      (proverRawLog verifierRawLog : Log)

/-- Reinterpret a generic-log phase as the ordinary raw-query-log phase. -/
def HybridGameRevisedPhaseWithLog.toPhase
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (phase : HybridGameRevisedPhaseWithLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec challengeSpec T_H T_P M
      (QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))) :
    HybridGameRevisedPhase
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec challengeSpec T_H T_P M :=
  match phase with
  | .proverStopped reason proverRawLog => .proverStopped reason proverRawLog
  | .verifier proverRun verifierResult proverRawLog verifierRawLog =>
      .verifier proverRun verifierResult proverRawLog verifierRawLog

/-- The log-erased outcome of the revised Figure-4 prover/verifier execution.  This is the
value marginal of `HybridGameRevisedPhase`: it retains the exact stopping reason and the exact
normal/memo state threaded into the verifier, but deliberately discards query logs.  Keeping it
separate lets probability arguments about a stopped execution use ordinary `OracleComp`
equalities, while the later Hyb₀--Hyb₁ coupling still uses the richer logged phase. -/
inductive HybridGameRevisedResult
    {κ : Type} (oSpec : OracleSpec ι) (challengeSpec : OracleSpec κ) (T_H T_P M : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U] where
  | proverStopped
      (reason : D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
  | verifier
      (proverRun : (((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M))
      (verifierResult : Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((Option StmtOut ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M))

/-- The lossless observation of Figure 4 lines 2--3 under the revised D2SQuery executor.  The
tagged phase result is the only dynamic field: its shape rules out a verifier execution after a
prover stop, while retaining every raw query log that a successful phase actually issued. -/
structure HybridGameRevisedObservation
    {κ : Type} (oSpec : OracleSpec ι) (challengeSpec : OracleSpec κ) (T_H T_P M : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U] where
  phase : HybridGameRevisedPhase
    (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) oSpec challengeSpec T_H T_P M

/-- Forget precisely the query logs from a lossless revised-game observation. -/
def HybridGameRevisedObservation.result
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    HybridGameRevisedResult
      (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) oSpec challengeSpec T_H T_P M :=
  match observation.phase with
  | .proverStopped reason _ => .proverStopped reason
  | .verifier proverRun verifierResult _ _ => .verifier proverRun verifierResult

/-- The prover's exact completed D2S trace.  On a successful prover phase it is a prefix of the
global verifier trace; on a stop it is the final trace because the verifier is never invoked. -/
def HybridGameRevisedObservation.proverTrace
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  match observation.phase with
  | .proverStopped reason _ => reason.trace
  | .verifier proverRun _ _ _ => proverRun.1.2.state.trace

/-- The complete global D2S trace at the terminal phase boundary.  In contrast with the legacy
observation this is not `proverTrace ++ verifierTrace`: the verifier inherits the prover's normal
state, so its returned trace already contains the prover prefix exactly once. -/
def HybridGameRevisedObservation.baseTrace
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  match observation.phase with
  | .proverStopped reason _ => reason.trace
  | .verifier _ (.ok ⟨⟨_, normal⟩, _⟩) _ _ => normal.state.trace
  | .verifier _ (.error reason) _ _ => reason.trace

/-- The raw outer-oracle log of the prover phase. -/
def HybridGameRevisedObservation.proverRawLog
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) :=
  match observation.phase with
  | .proverStopped _ rawLog => rawLog
  | .verifier _ _ rawLog _ => rawLog

/-- The raw outer-oracle log of the verifier phase, if the prover succeeded. -/
def HybridGameRevisedObservation.verifierRawLog?
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    Option (QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :=
  match observation.phase with
  | .proverStopped _ _ => none
  | .verifier _ _ _ rawLog => some rawLog

/-- All raw outer-oracle requests that the legal phase outcome actually issued, in temporal
order.  A prover stop contributes only its prover log; a successful prover contributes its log
followed by the verifier log. -/
def HybridGameRevisedObservation.rawQueryLog
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) :=
  match observation.phase with
  | .proverStopped _ proverRawLog => proverRawLog
  | .verifier _ _ proverRawLog verifierRawLog => proverRawLog ++ verifierRawLog

/-- The exact post-occurrence `Monitor` witness, if the global Figure-4 execution stopped for
the Lemma-5.8 bad event.  Search/parser and ambient-oracle aborts deliberately return `none`:
they have no final monitored occurrence and are discharged by the no-abort/replay lemmas instead.
The dependent pair retains the record's own pre-occurrence normal state, so it cannot be confused
with a reusable post-stop state. -/
def HybridGameRevisedObservation.monitorStop?
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    Option (Sigma fun normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) =>
      D2SPostOccurrenceStopRecord
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :=
  match observation.phase with
  | .proverStopped (.monitorStop normal record) _ => some ⟨normal, record⟩
  | .proverStopped _ _ => none
  | .verifier _ (.error (.monitorStop normal record)) _ _ => some ⟨normal, record⟩
  | .verifier _ _ _ _ => none

/-- The same first-bad witness on the log-erased phase result.  Its type retains the exact
pre-occurrence normal state, so the stopped result is still not mistaken for a continuation. -/
def HybridGameRevisedResult.monitorStop?
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (result : HybridGameRevisedResult
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    Option (Sigma fun normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) =>
      D2SPostOccurrenceStopRecord
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :=
  match result with
  | .proverStopped (.monitorStop normal record) => some ⟨normal, record⟩
  | .proverStopped _ => none
  | .verifier _ (.error (.monitorStop normal record)) => some ⟨normal, record⟩
  | .verifier _ _ => none

/-- The terminal base trace of the log-erased revised-game result.  It is still available because
every successful normal state and every stopping reason retains its D2S insertion trace. -/
def HybridGameRevisedResult.baseTrace
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (result : HybridGameRevisedResult
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  match result with
  | .proverStopped reason => reason.trace
  | .verifier _ (.ok ⟨⟨_, normal⟩, _⟩) => normal.state.trace
  | .verifier _ (.error reason) => reason.trace

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The log-erased result is bad exactly when it retains the unique post-occurrence monitor
record.  Thus an event bound on `monitorStop?` is a bound on `E` of the actual terminal trace. -/
theorem HybridGameRevisedResult.badEvent_iff_monitorStop?_ne_none
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (result : HybridGameRevisedResult
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    BadEventDS.E result.baseTrace ↔ result.monitorStop? ≠ none := by
  constructor
  · intro hBad
    cases result with
    | proverStopped reason =>
        cases reason with
        | monitorStop state record => simp [HybridGameRevisedResult.monitorStop?]
        | underlyingAbort state =>
            exact False.elim (state.monitorPassed (by
              simpa [HybridGameRevisedResult.baseTrace] using hBad))
        | oracleAbort state =>
            exact False.elim (state.monitorPassed (by
              simpa [HybridGameRevisedResult.baseTrace] using hBad))
    | verifier proverRun verifierResult =>
        cases verifierResult with
        | ok verifierRun =>
            rcases verifierRun with ⟨⟨output, state⟩, memo⟩
            exact False.elim (state.monitorPassed (by
              simpa [HybridGameRevisedResult.baseTrace] using hBad))
        | error reason =>
            cases reason with
            | monitorStop state record => simp [HybridGameRevisedResult.monitorStop?]
            | underlyingAbort state =>
                exact False.elim (state.monitorPassed (by
                  simpa [HybridGameRevisedResult.baseTrace] using hBad))
            | oracleAbort state =>
                exact False.elim (state.monitorPassed (by
                  simpa [HybridGameRevisedResult.baseTrace] using hBad))
  · intro hStop
    cases hMonitor : result.monitorStop? with
    | none => exact False.elim (hStop hMonitor)
    | some witness =>
        rcases witness with ⟨normal, record⟩
        cases result with
        | proverStopped reason =>
            cases reason with
            | monitorStop state stopRecord =>
                simpa [HybridGameRevisedResult.baseTrace,
                  HybridGameRevisedResult.monitorStop?] using stopRecord.monitorFails
            | underlyingAbort state => simp [HybridGameRevisedResult.monitorStop?] at hMonitor
            | oracleAbort state => simp [HybridGameRevisedResult.monitorStop?] at hMonitor
        | verifier proverRun verifierResult =>
            cases verifierResult with
            | ok verifierRun => simp [HybridGameRevisedResult.monitorStop?] at hMonitor
            | error reason =>
                cases reason with
                | monitorStop state stopRecord =>
                    simpa [HybridGameRevisedResult.baseTrace,
                      HybridGameRevisedResult.monitorStop?] using stopRecord.monitorFails
                | underlyingAbort state => simp [HybridGameRevisedResult.monitorStop?] at hMonitor
                | oracleAbort state => simp [HybridGameRevisedResult.monitorStop?] at hMonitor

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- Transport any first-stop probability bound to the concrete terminal bad event.  This small
bridge is deliberately independent of the particular Hyb₁ sampler and avoids redoing the
stopping calculation when a proof needs the paper's `Pr[E]` spelling. -/
theorem HybridGameRevisedResult.probBadEvent_le_of_monitorStop
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (exp : ProbComp (HybridGameRevisedResult
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M))
    {b : ENNReal}
    (hStop : Pr[ fun result => result.monitorStop? ≠ none | exp] ≤ b) :
    Pr[ fun result => BadEventDS.E result.baseTrace | exp] ≤ b := by
  calc
    Pr[ fun result => BadEventDS.E result.baseTrace | exp] =
        Pr[ fun result => result.monitorStop? ≠ none | exp] := by
      apply probEvent_congr'
      · intro result _
        exact result.badEvent_iff_monitorStop?_ne_none
      · rfl
    _ ≤ b := hStop

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- A monitored stop of the global revised Figure-4 game witnesses the concrete `E` event on its
terminal global trace.  This is the direct bridge from the lossless hybrid observation to the
first-bad-event side of Lemma 5.8; no concatenation of independent prover/verifier traces occurs.
-/
theorem HybridGameRevisedObservation.monitorStop?_eq_some_imp_badEvent
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M)
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal}
    (hStop : observation.monitorStop? = some ⟨normal, record⟩) :
    BadEventDS.E observation.baseTrace := by
  rcases observation with ⟨phase⟩
  cases phase with
  | proverStopped reason rawLog =>
      cases reason with
      | monitorStop state stopRecord =>
          simpa [HybridGameRevisedObservation.baseTrace] using stopRecord.monitorFails
      | underlyingAbort _ =>
          simp [HybridGameRevisedObservation.monitorStop?] at hStop
      | oracleAbort _ =>
          simp [HybridGameRevisedObservation.monitorStop?] at hStop
  | verifier proverRun verifierResult proverRawLog verifierRawLog =>
      cases verifierResult with
      | ok verifierRun =>
          simp [HybridGameRevisedObservation.monitorStop?] at hStop
      | error reason =>
          cases reason with
          | monitorStop state stopRecord =>
              simpa [HybridGameRevisedObservation.baseTrace] using stopRecord.monitorFails
          | underlyingAbort _ =>
              simp [HybridGameRevisedObservation.monitorStop?] at hStop
          | oracleAbort _ =>
              simp [HybridGameRevisedObservation.monitorStop?] at hStop

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- Conversely, a terminal revised Figure-4 trace can satisfy the bad event only at the
post-occurrence `Monitor` stop.  Every other terminal face retains a `D2SNormalState`, whose
trace is monitor-passing by construction.  Together with
`monitorStop?_eq_some_imp_badEvent`, this identifies the global `E` event with the unique
first-stop event required by Lemma 5.8. -/
theorem HybridGameRevisedObservation.badEvent_imp_monitorStop?_ne_none
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M)
    (hBad : BadEventDS.E observation.baseTrace) :
    observation.monitorStop? ≠ none := by
  rcases observation with ⟨phase⟩
  cases phase with
  | proverStopped reason rawLog =>
      cases reason with
      | monitorStop state stopRecord => simp [HybridGameRevisedObservation.monitorStop?]
      | underlyingAbort state =>
          exact False.elim (state.monitorPassed (by
            simpa [HybridGameRevisedObservation.baseTrace] using hBad))
      | oracleAbort state =>
          exact False.elim (state.monitorPassed (by
            simpa [HybridGameRevisedObservation.baseTrace] using hBad))
  | verifier proverRun verifierResult proverRawLog verifierRawLog =>
      cases verifierResult with
      | ok verifierRun =>
          rcases verifierRun with ⟨⟨output, state⟩, memo⟩
          exact False.elim (state.monitorPassed (by
            simpa [HybridGameRevisedObservation.baseTrace] using hBad))
      | error reason =>
          cases reason with
          | monitorStop state stopRecord => simp [HybridGameRevisedObservation.monitorStop?]
          | underlyingAbort state =>
              exact False.elim (state.monitorPassed (by
                simpa [HybridGameRevisedObservation.baseTrace] using hBad))
          | oracleAbort state =>
              exact False.elim (state.monitorPassed (by
                simpa [HybridGameRevisedObservation.baseTrace] using hBad))

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The global revised Figure-4 terminal trace is bad exactly when its unique retained
post-occurrence monitor record exists.  This is the event-level form used to replace a public
abort probability by the proof runner's first-stop probability. -/
theorem HybridGameRevisedObservation.badEvent_iff_monitorStop?_ne_none
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    BadEventDS.E observation.baseTrace ↔ observation.monitorStop? ≠ none := by
  constructor
  · exact observation.badEvent_imp_monitorStop?_ne_none
  · intro hStop
    cases hMonitor : observation.monitorStop? with
    | none => exact False.elim (hStop hMonitor)
    | some witness =>
        rcases witness with ⟨normal, record⟩
        exact observation.monitorStop?_eq_some_imp_badEvent hMonitor

/-- The public abort-erasing output of a revised Figure-4 observation.  It is computed from the
legal phase outcome, rather than stored independently and therefore unable to disagree with it. -/
def HybridGameRevisedObservation.publicOutput
    {κ : Type} {challengeSpec : OracleSpec κ} {T_H T_P M : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (observation : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :
    Option (StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
      TaggedQueryLog (oSpec + challengeSpec)) :=
  match observation.phase with
  | .proverStopped _ _ => none
  | .verifier ⟨⟨⟨stmtIn, proof⟩, _⟩, _⟩ (.ok ⟨⟨some stmtOut, _⟩, _⟩) proverRawLog verifierRawLog =>
      let proveQueryLog := filterD2SChallengePlusUnitQueryLog
        (oSpec := oSpec) (U := U) proverRawLog
      let verifyQueryLog := filterD2SChallengePlusUnitQueryLog
        (oSpec := oSpec) (U := U) verifierRawLog
      some ⟨stmtIn, stmtOut, proof,
        (proveQueryLog.map fun entry => (SourceTag.prover, entry)) ++
          (verifyQueryLog.map fun entry => (SourceTag.verifier, entry))⟩
  | .verifier _ _ _ _ => none

/-- The result-only Figure-4 execution under the revised global D2S state discipline.  It is the
canonical unlogged phase boundary: a prover stop is absorbing, and a successful verifier starts
from the prover's exact returned normal state and memo. -/
noncomputable def hybridGameRevisedResult
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (HybridGameRevisedResult (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) oSpec challengeSpec T_H T_P M) := do
  let proverResult ← d2fRawRevisedStopping (T_H := T_H) (T_P := T_P) gImpl P default
  match proverResult with
  | .error reason => return .proverStopped reason
  | .ok proverRun =>
      let stmtIn := proverRun.1.1.1
      let proof := proverRun.1.1.2
      let normal := proverRun.1.2
      let memo := proverRun.2
      let rawVerifierComp := runForwardVerifierWide δ V stmtIn proof
      let verifierResult ← d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        gImpl rawVerifierComp normal memo
      return .verifier proverRun verifierResult

/-- Execute the revised Figure-4 prover/verifier boundary under an arbitrary response-dependent
outer logger.  This is the semantic hook for trace couplings: it preserves the ordinary game
control flow and the exact prover-to-verifier normal/memo handoff, but leaves the recorded log
carrier explicit. -/
noncomputable def hybridGameRevisedPhaseWithLoggerFrom
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    {Log : Type} [EmptyCollection Log] [Append Log] {m : Type → Type} [Monad m]
    (logger : QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) (WriterT Log m))
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (initialMemo : M) :
    m (HybridGameRevisedPhaseWithLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec challengeSpec T_H T_P M Log) := do
  let proverComp := d2fRawRevisedStopping (T_H := T_H) (T_P := T_P) gImpl P initialMemo
  let ⟨proverResult, proveQueryLogRaw⟩ ← (simulateQ logger proverComp).run
  match proverResult with
  | .error reason =>
      return .proverStopped reason proveQueryLogRaw
  | .ok proverRun =>
      let stmtIn := proverRun.1.1.1
      let proof := proverRun.1.1.2
      let normal := proverRun.1.2
      let memo := proverRun.2
      let rawVerifierComp := runForwardVerifierWide δ V stmtIn proof
      let verifierComp := d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        gImpl rawVerifierComp normal memo
      let ⟨verifierResult, verifyQueryLogRaw⟩ ← (simulateQ logger verifierComp).run
      return .verifier proverRun verifierResult proveQueryLogRaw verifyQueryLogRaw

/-- Instrumented Figure 4 lines 2--3, started from an explicitly supplied D2S memo.  The
explicit form is used only for semantic couplings such as the full-cache H₂ realization; the
ordinary game below instantiates it with `default`.  A prover stop is absorbing, and a successful
verifier inherits both the prover's exact normal state and its returned memo. -/
noncomputable def hybridGameRevisedObservedFrom
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (initialMemo : M) :
    OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (HybridGameRevisedObservation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) := do
  let proverComp := d2fRawRevisedStopping (T_H := T_H) (T_P := T_P) gImpl P initialMemo
  let ⟨proverResult, proveQueryLogRaw⟩ ← (simulateQ loggingOracle proverComp).run
  match proverResult with
  | .error reason =>
      return ⟨.proverStopped reason proveQueryLogRaw⟩
  | .ok proverRun =>
      let stmtIn := proverRun.1.1.1
      let proof := proverRun.1.1.2
      let normal := proverRun.1.2
      let memo := proverRun.2
      let rawVerifierComp := runForwardVerifierWide δ V stmtIn proof
      let verifierComp := d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        gImpl rawVerifierComp normal memo
      let ⟨verifierResult, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp).run
      return ⟨.verifier proverRun verifierResult proveQueryLogRaw verifyQueryLogRaw⟩

/-- Instantiating the explicit-log executor with the ordinary query logger recovers the existing
lossless observation exactly. -/
theorem hybridGameRevisedObservedFrom_eq_phaseWithLogger
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (initialMemo : M) :
    hybridGameRevisedObservedFrom (T_H := T_H) (T_P := T_P) gImpl V P initialMemo =
      (fun phase => ⟨phase.toPhase⟩) <$>
        hybridGameRevisedPhaseWithLoggerFrom
          (T_H := T_H) (T_P := T_P) (logger := loggingOracle) gImpl V P initialMemo := by
  simp only [hybridGameRevisedObservedFrom, hybridGameRevisedPhaseWithLoggerFrom,
    HybridGameRevisedPhaseWithLog.toPhase, map_bind]
  apply bind_congr
  rintro ⟨proverResult, proverLog⟩
  cases proverResult with
  | error reason => rfl
  | ok proverRun =>
      rw [map_eq_bind_pure_comp, bind_assoc]
      simp

/-- Instrumented Figure 4 lines 2--3 with the revised global D2S state discipline.  This is the
ordinary fresh-memo game, definitionally the explicit-start executor at `default`. -/
noncomputable def hybridGameRevisedObserved
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (HybridGameRevisedObservation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) :=
  hybridGameRevisedObservedFrom (T_H := T_H) (T_P := T_P) gImpl V P default

/-- The fresh-memo observed executor is exactly the explicit-start executor at `default`. -/
theorem hybridGameRevisedObserved_eq_from_default
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    hybridGameRevisedObserved (T_H := T_H) (T_P := T_P) gImpl V P =
      hybridGameRevisedObservedFrom (T_H := T_H) (T_P := T_P) gImpl V P default := rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The distribution-level logged phase endpoint started from a supplied inner memo.  This is
the semantic form used by full-cache couplings: both the prover and the verifier retain the
same explicit memo across their legal phase boundary, while the outer oracle table is still
sampled exactly once by `init`. -/
noncomputable def hybridGameRevisedPhaseDistFrom
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
    (initialMemo : M) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) := do
  (simulateQ impl
    (hybridGameRevisedObservedFrom (δ := δ) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) gImpl V P initialMemo)).run' (← init)

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The distribution-level logged phase endpoint, before line-4 trace mapping.  It is the
trace-sensitive endpoint for the Hyb₀--Hyb₁ coupling. -/
noncomputable def hybridGameRevisedPhaseDist
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
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) := do
  (simulateQ impl
    (hybridGameRevisedObserved (δ := δ) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) gImpl V P)).run' (← init)

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The ordinary logged phase endpoint is the explicit-memo form at the default memo. -/
theorem hybridGameRevisedPhaseDist_eq_from_default
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
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    hybridGameRevisedPhaseDist (δ := δ) (T_H := T_H) (T_P := T_P)
      init impl gImpl V P =
      hybridGameRevisedPhaseDistFrom (δ := δ) (T_H := T_H) (T_P := T_P)
        init impl gImpl V P default := rfl

/-- The result-only distribution-level endpoint.  It is intentionally defined independently of
the logged endpoint, so a probability proof does not depend on a trace projection or a later
line-4 map. -/
noncomputable def hybridGameRevisedResultDist
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
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedResult
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M) := do
  (simulateQ impl
    (hybridGameRevisedResult (δ := δ) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) gImpl V P)).run' (← init)

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- Figure 4 lines 2--3 with the live revised D2SQuery executor.  The prover starts from the
fresh initial state; a successful verifier then starts from the prover's exact normal state and
memo.  Any abort is absorbing, so no verifier query is made after a prover stop.  The public
output and tagged-log type remain the legacy game's type for the surrounding hybrid wrappers. -/
noncomputable def hybridGameRevised
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
        TaggedQueryLog (oSpec + challengeSpec)) :=
  OptionT.mk do
    let observation ← hybridGameRevisedObserved
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) gImpl V P
    pure observation.publicOutput

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] in
/-- Distribution wrapper for `hybridGameRevised`.  It is definitionally the same outer sampling
and line-4 codec process as `hybridGameDist`; only the live transition interpreter differs.
Keeping this wrapper separate makes a later coupling theorem state exactly the intended
legacy-versus-revised boundary rather than re-proving the game plumbing. -/
noncomputable def hybridGameDistRevised
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
      ((hybridGameRevised
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        gImpl V P).run)).run' (← init)
  match hybridOutput with
  | none => return none
  | some (⟨stmtIn, stmtOut, proof, projectedTrace⟩ :
      (StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
        TaggedQueryLog (oSpec + challengeSpec))) => do
      let π : FSSaltedProof pSpec Salt :=
        (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Salt := Salt)
          traceMap projectedTrace
      match outputFS? with
      | none => return some (stmtIn, stmtOut, π, [])
      | some fullTraceFS => return some (stmtIn, stmtOut, π, fullTraceFS)

/-- The lossless, line-4-mapped observation of a revised Figure-4 game.  Its `game` field keeps
the prover/verifier raw D2S executions, their raw query logs, and any structured first-bad stop;
`publicOutput` applies precisely the same codec/trace-map convention as `hybridGameDistRevised`.

This is the Hyb₁-side carrier of the lazy-sampling coupling.  In particular, the direct
insertion-ordered `gᵢ` requests remain observable in `game.rawQueryLog` instead of being
projected away before the coupling can relate them to Hyb₀'s offline `StdTrace` requests. -/
structure HybridGameRevisedMappedObservation
    {κ : Type} (challengeSpec : OracleSpec κ) (T_H T_P M : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U] where
  game : HybridGameRevisedObservation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M
  publicOutput : Option
    (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt))

/-- Finish one explicitly logged revised prover--verifier phase with exactly the public
line-4 postprocessing used by `hybridGameDistRevisedObserved`.  Keeping this adapter separate
lets hybrid couplings change only the phase/log representation and then invoke one common public
output calculation. -/
noncomputable def finishRevisedGamePhase
    [SampleableType U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type}
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) challengeSpec)
    (phase : HybridGameRevisedPhaseWithLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec challengeSpec T_H T_P M
      (QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))) :
    ProbComp (HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) challengeSpec T_H T_P M) := do
  let game : HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M :=
    ⟨phase.toPhase⟩
  let publicOutput ←
    match game.publicOutput with
    | none => pure none
    | some ⟨stmtIn, stmtOut, proof, projectedTrace⟩ => do
        let π : FSSaltedProof pSpec Salt :=
          (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
        let outputFS? ←
          runSection58TraceMap
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (Salt := Salt) traceMap projectedTrace
        match outputFS? with
        | none => pure (some (stmtIn, stmtOut, π, []))
        | some fullTraceFS => pure (some (stmtIn, stmtOut, π, fullTraceFS))
  return ⟨game, publicOutput⟩

/-- Distribution-level lossless counterpart of `hybridGameDistRevised`.  It samples the same
outer oracle-family carrier and runs the same revised Figure-4 game, but retains the actual
pre-line-4 observation needed to state the Hyb₀↔Hyb₁ coupling. -/
noncomputable def hybridGameDistRevisedObserved
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
    ProbComp (HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) challengeSpec T_H T_P M) := do
  let game ←
    (simulateQ impl
      (hybridGameRevisedObserved
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) gImpl V P)).run' (← init)
  let publicOutput ←
    match game.publicOutput with
    | none => pure none
    | some ⟨stmtIn, stmtOut, proof, projectedTrace⟩ => do
        let π : FSSaltedProof pSpec Salt :=
          (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
        let outputFS? ←
          runSection58TraceMap
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (Salt := Salt) traceMap projectedTrace
        match outputFS? with
        | none => pure (some (stmtIn, stmtOut, π, []))
        | some fullTraceFS => pure (some (stmtIn, stmtOut, π, fullTraceFS))
  return ⟨game, publicOutput⟩

/-- The lossless revised-game wrapper is equivalently: sample the outer table, run the
explicitly logged phase, then apply `finishRevisedGamePhase`.  This is an equality of full
distributions, including both a prover stop and the inherited-state verifier branch. -/
theorem hybridGameDistRevisedObserved_eq_finishRevisedGamePhase
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
    hybridGameDistRevisedObserved
        (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) init impl gImpl V P traceMap =
      (do
        let initial ← init
        let phase ←
          (simulateQ impl
            (hybridGameRevisedPhaseWithLoggerFrom
              (T_H := T_H) (T_P := T_P) (logger := loggingOracle) gImpl V P default)).run'
            initial
        finishRevisedGamePhase
          (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) traceMap phase) := by
  unfold hybridGameDistRevisedObserved
  apply bind_congr
  intro initial
  have hPhase :
      (simulateQ impl
        (hybridGameRevisedObservedFrom (T_H := T_H) (T_P := T_P)
          gImpl V P default)).run' initial =
        (simulateQ impl
          ((fun phase =>
            ({ phase := phase.toPhase } : HybridGameRevisedObservation
              (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) challengeSpec T_H T_P M)) <$>
            hybridGameRevisedPhaseWithLoggerFrom
              (T_H := T_H) (T_P := T_P) (logger := loggingOracle)
              gImpl V P default)).run' initial :=
    congrArg (fun computation => (simulateQ impl computation).run' initial)
      (hybridGameRevisedObservedFrom_eq_phaseWithLogger
        (T_H := T_H) (T_P := T_P) gImpl V P default)
  rw [hybridGameRevisedObserved, hPhase]
  rw [simulateQ_map]
  rw [StateT.run'_map_comm]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro phase
  rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [VCVCompatible Salt] in
/-- Projecting the lossless revised-game distribution to its public output gives precisely the
ordinary revised-game distribution.  This only reassociates the common sampler and line-4
post-processing; it is not a Hyb₀--Hyb₁ coupling claim. -/
lemma hybridGameDistRevisedObserved_map_publicOutput_eq
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
    (fun observation => observation.publicOutput) <$>
        hybridGameDistRevisedObserved
          (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
          (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) init impl gImpl V P traceMap =
      hybridGameDistRevised
        (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) init impl gImpl V P traceMap := by
  simp only [hybridGameDistRevised, hybridGameDistRevisedObserved, hybridGameRevised,
    OptionT.run_mk, map_eq_pure_bind, simulateQ_bind, simulateQ_pure, StateT.run'_eq,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro initial
  apply bind_congr
  rintro ⟨observation, finalState⟩
  cases hOutput : observation.publicOutput
  · simp
  · simp only
    simp only [bind_assoc]
    apply bind_congr
    intro outputFS
    cases outputFS <;> rfl

/-- The Hyb₁ `gᵢ` handler before the outer eager finite-table sampler is installed.

This deliberately forwards only the encoded challenge query.  Naming it removes the anonymous
handler from `hyb1Revised` and gives the live-to-adaptive refinement a concrete atomic target:
after `hybChallengeImpl` is installed, this query is exactly
`D_SigmaFinite.toImpl kSigma`. -/
noncomputable def hyb1GImpl :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) PUnit :=
  fun q =>
    StateT.lift <|
      OptionT.lift <|
        (show OracleComp
            (D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
            (Vector U (challengeSize (pSpec := pSpec) q.1)) from
          query
            (spec := D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
            (.inl q))

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
/-- The full three-slot D2S handler seen after fixing Hyb₁'s eagerly sampled finite table.

The definition retains the outer-handler presentation used by the real game, while its next
lemma identifies it exactly with the direct handler used by the adaptive runner. -/
noncomputable def hyb1D2SOuterAfterSampleImpl
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) ProbComp
  | .inl q =>
      (hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
        oSpecImpl (D_SigmaFinite (U := U) StmtIn pSpec δ)
        (Sum.inr (Sum.inl q))).run' kSigma
  | .inr (.inl q) =>
      (hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
        oSpecImpl (D_SigmaFinite (U := U) StmtIn pSpec δ)
        (Sum.inr (Sum.inr (Sum.inl q)))).run' kSigma
  | .inr (.inr q) =>
      (hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
        oSpecImpl (D_SigmaFinite (U := U) StmtIn pSpec δ)
        (Sum.inr (Sum.inr (Sum.inr q)))).run' kSigma

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
/-- The exact result projection used by the lossless outer D2F interpreter for one Hyb₁ D2S
query.  A continuation retains the vacuous `PUnit` memo; a monitored stop and an underlying
search failure become the corresponding structured stopping reasons at the *input* normal state.
This is the terminal-result target of the live-to-adaptive residual-program induction. -/
def hyb1D2SStepToStopping
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {q : (duplexSpongeChallengeOracle StmtIn U).Domain} :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      ((duplexSpongeChallengeOracle StmtIn U).Range q) →
      Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((((duplexSpongeChallengeOracle StmtIn U).Range q) ×
          D2SNormalState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)
  | .continue answer normal' => .ok ((answer, normal'), PUnit.unit)
  | .stopped normal' record => .error (.monitorStop normal' record)
  | .underlyingAbort => .error (.underlyingAbort normal)

/-- The fixed pure-Hyb₁ interpretation of the ambient-oracle-free verifier interface.  It is
the outer table used when the lossless D2F executor is compared with the adaptive one-step
runner. -/
noncomputable def hyb1VerifierOuterImpl
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl ([]ₒ + d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ)) ProbComp
  | .inl query => PEmpty.elim query
  | .inr query =>
      ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
        (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec)) query

/-- The inner one-query handler used by the live lossless D2F executor at a fixed normal state.
It retains the original oracle stack so that pushing `hyb1VerifierOuterImpl` through it is an
exact semantic operation. -/
noncomputable def hyb1StoppingD2SInner
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    QueryImpl (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT PUnit
        (ExceptT
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (OracleComp ([]ₒ + d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ))))) :=
  d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := []ₒ)
    (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal

/-- The same one-query handler after fixing the Hyb₁ verifier oracle table. -/
noncomputable def hyb1StoppingD2SDirect
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (StateT PUnit
        (ExceptT
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp)) := by
  classical
  exact fun
    | .inl gq => fun memo => do
      let answer ← ExceptT.lift ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma gq)
      pure (answer, memo)
    | .inr aux => StateT.lift <| ExceptT.lift <|
      ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux)

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The direct Hyb₁ one-query handler is precisely the generic lossless lifting of the fixed
finite-table D2S oracle implementation. -/
lemma hyb1StoppingD2SDirect_eq_lift
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma =
      QueryImpl.liftStateTExceptTBase
        ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
          (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec)) := by
  apply QueryImpl.ext
  rintro (gq | aux | aux)
  · rfl
  · rfl
  · rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The direct fixed-table D2S handler executes a revised step by sampling exactly the ordinary
step result, pairing it with the unchanged `PUnit` memo, and never raising an exception itself.
The outer D2F interpreter alone decides whether that result is a continuation or a stop. -/
lemma hyb1StoppingD2SDirect_step_run
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (request : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    ExceptT.run ((simulateQ
      (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma)
      (d2sQueryStepRevised normal request)).run PUnit.unit) =
      (fun result => Except.ok (result, PUnit.unit)) <$>
        simulateQ
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
            (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
          (d2sQueryStepRevised normal request) := by
  rw [hyb1StoppingD2SDirect_eq_lift]
  exact QueryImpl.simulateQ_liftStateTExceptTBase_run
    ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
      (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
    (d2sQueryStepRevised normal request) PUnit.unit

/-- The direct fixed-table lossless D2F handler.  This is the form of a Hyb₁ verifier request
used by the adaptive residual runner: it dispatches one revised D2S step and converts exactly
the two absorbing step results into the paper's structured stopping reasons. -/
noncomputable def hyb1D2FStoppingDirectImpl
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT PUnit
          (ExceptT
            (D2SRevisedStoppingReason
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp)))
  | .inl query => PEmpty.elim query
  | .inr request => fun normal => do
      let result ← simulateQ
        (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma)
        (d2sQueryStepRevised normal request)
      StateT.mk fun memo => ExceptT.mk (pure (d2sRevisedStepPost normal result memo))

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)] in
/-- Fixing the Hyb₁ table before executing one D2S step agrees exactly with pushing that table
through the live inner handler.  This bridges the real D2F executor to the adaptive first-bad
runner without losing its `PUnit` memo or structured stopping reason. -/
lemma hyb1StoppingD2SInner_mapped_eq_direct
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl.mapStateTExceptTBase (hyb1VerifierOuterImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma)
      (hyb1StoppingD2SInner (T_H := T_H) (T_P := T_P) normal) =
    hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma := by
  apply QueryImpl.ext
  rintro (gq | aux | aux)
  · funext memo
    apply ExceptT.ext
    simpa [QueryImpl.mapStateTExceptTBase, hyb1StoppingD2SInner,
      hyb1StoppingD2SDirect, hyb1GImpl] using
      (QueryImpl.run_stateT_lift_exceptT_lift
        (ε := D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma gq) memo).symm
  · funext memo
    apply ExceptT.ext
    simp only [QueryImpl.mapStateTExceptTBase, hyb1StoppingD2SInner,
      hyb1StoppingD2SDirect]
    calc
      (StateT.mk (fun state => ExceptT.mk
          ((fun answer => Except.ok (answer, state)) <$> d2sUnitSampleImpl aux)) memo).run =
          (fun answer => Except.ok (answer, memo)) <$> d2sUnitSampleImpl aux := rfl
      _ = (StateT.lift (ExceptT.lift (d2sUnitSampleImpl aux)) memo).run :=
        (QueryImpl.run_stateT_lift_exceptT_lift
          (ε := D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (d2sUnitSampleImpl (U := U) aux) memo).symm
  · funext memo
    apply ExceptT.ext
    simpa [QueryImpl.mapStateTExceptTBase, hyb1StoppingD2SInner,
      hyb1StoppingD2SDirect] using
      (QueryImpl.run_stateT_lift_exceptT_lift
        (ε := D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)) memo).symm

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The preceding equality in the exact generic Eq. (16) inner-handler presentation. -/
lemma hyb1D2fStoppingD2SInner_mapped_eq_direct
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl.mapStateTExceptTBase (hyb1VerifierOuterImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma)
      (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := []ₒ)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal) =
    hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma := by
  simpa [hyb1StoppingD2SInner] using
    hyb1StoppingD2SInner_mapped_eq_direct (T_H := T_H) (T_P := T_P) normal kSigma

/-- The direct, fixed-table realization of the full outer D2F handler used by a pure Hyb₁
verifier residual.  It is not a second D2F semantics: it is obtained by pushing the fixed
outer oracle implementation through the exact `StateT → StateT → ExceptT` handler stack.
Keeping this mapped implementation named makes the live-to-adaptive refinement state its
semantic boundary without erasing a monitored stop into `Option`. -/
noncomputable def hyb1D2FStoppingMappedImpl
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (direct : QueryImpl
      ([]ₒ + d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) ProbComp) :
    QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT PUnit
          (ExceptT
            (D2SRevisedStoppingReason
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp))) :=
  direct.mapStateTStateTExceptTBase
    (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P)
      (oSpec := []ₒ)
      (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)))

/-- Pushing the fixed Hyb₁ table through the complete lossless D2F request handler is exactly
the direct fixed-table handler.  Both sides run the same revised D2S step, thread the same
`PUnit` memo, and classify its result through `d2sRevisedStepPost`; the only non-definitional
part is the already-proved inner-oracle naturality law. -/
lemma hyb1D2FStoppingMappedImpl_eq_direct
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    hyb1D2FStoppingMappedImpl (T_H := T_H) (T_P := T_P)
      (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma) =
    hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma := by
  apply QueryImpl.ext
  rintro (query | query)
  · exact PEmpty.elim query
  · funext normal
    funext memo
    apply ExceptT.ext
    simp only [hyb1D2FStoppingMappedImpl, QueryImpl.mapStateTStateTExceptTBase,
      d2fOuterImplRevisedStopping, hyb1D2FStoppingDirectImpl]
    dsimp only [StateT.mk, ExceptT.mk]
    change ExceptT.run (simulateQ
      (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma)
      ((do
        let result ← simulateQ
          (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := []ₒ)
            (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal)
          (d2sQueryStepRevised normal query)
        StateT.mk fun current => ExceptT.mk
          (pure (d2sRevisedStepPost normal result current))
      ).run memo).run) = _
    refine (QueryImpl.simulateQ_mapStateTExceptTBase_bind_pure_run_unwrapped
      (m := unifSpec.toPFunctor.FreeM)
      (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma)
      (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := []ₒ)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal)
      (d2sQueryStepRevised normal query) memo (d2sRevisedStepPost normal)).trans ?_
    let outer : QueryImpl
        ([]ₒ + d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        ProbComp :=
      hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma
    change ((do
      let value ← simulateQ
        (QueryImpl.mapStateTExceptTBase outer
          (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := []ₒ)
            (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal))
        (d2sQueryStepRevised normal query)
      StateT.mk fun current => ExceptT.mk
        (pure (d2sRevisedStepPost normal value current))).run memo).run = _
    dsimp only [outer]
    rw [hyb1D2fStoppingD2SInner_mapped_eq_direct]
    rfl

/-- Execute a pure Hyb₁ verifier residual after its fixed outer oracle table has been pushed
through the lossless D2F handler.  This is definitionally the right-hand side of the exact
simulation theorem below; the next refinement only has to relate this named mapped execution to
the adaptive residual runner. -/
noncomputable def hyb1D2fRawRevisedStoppingMapped
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (direct : QueryImpl
      ([]ₒ + d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) ProbComp)
    (residual : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) :=
  (((simulateQ
      (hyb1D2FStoppingMappedImpl (T_H := T_H) (T_P := T_P) direct)
      residual).run normal).run PUnit.unit).run

/-- The mapped residual executor is the direct fixed-table lossless executor, for every finite
verifier residual program.  This lifts `hyb1D2FStoppingMappedImpl_eq_direct` from one request to
the complete residual without changing its normal state, `PUnit` memo, or structured stop. -/
lemma hyb1D2fRawRevisedStoppingMapped_eq_direct
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1D2fRawRevisedStoppingMapped (T_H := T_H) (T_P := T_P)
      (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma)
      residual normal =
    (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
      residual).run normal).run PUnit.unit).run := by
  simp only [hyb1D2fRawRevisedStoppingMapped]
  rw [hyb1D2FStoppingMappedImpl_eq_direct]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U] in
/-- Pushing a fixed pure-Hyb₁ oracle interpretation through a lossless D2F execution is exact.

The left side is the live evaluator followed by the fixed outer table.  The right side is the
same evaluator with that table already at its base.  Therefore this theorem performs no
coupling and loses neither the normal state nor the structured monitor/search stop. -/
theorem hyb1D2fRawRevisedStopping_pushes_outer
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (direct : QueryImpl
      ([]ₒ + d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) ProbComp)
    (residual : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    simulateQ direct
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        residual normal PUnit.unit) =
      hyb1D2fRawRevisedStoppingMapped (T_H := T_H) (T_P := T_P) direct residual normal := by
  exact QueryImpl.simulateQ_mapStateTStateTExceptTBase_run direct
    (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P)
      (oSpec := []ₒ)
      (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))) residual normal
    PUnit.unit

/-- The live pure-Hyb₁ verifier residual, after its fixed outer table is installed, is exactly
the direct fixed-`D_Σ` stopping execution.  This composes the generic transformer naturality
law with the pointwise identification of the revised D2S handler.  In particular it preserves
the returned verifier value, normal state, unit memo, and the distinction between monitor and
underlying-search stops; it is not a lossy distributional coupling. -/
theorem hyb1D2fRawRevisedStopping_hyb1_eq_direct
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    simulateQ
      (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        residual normal PUnit.unit) =
      (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
        residual).run normal).run PUnit.unit).run := by
  rw [hyb1D2fRawRevisedStopping_pushes_outer]
  exact hyb1D2fRawRevisedStoppingMapped_eq_direct
    (T_H := T_H) (T_P := T_P) kSigma residual normal

/-- CO25 Hyb₁ over the live revised D2SQuery executor.  This has exactly the challenge-family
sampling and line-4 trace map of `KeyLemma.hyb_1`; unlike that legacy definition, both the prover
and verifier invoke `d2fRawRevised`. -/
noncomputable def hyb1Revised
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := gSpec (U := U) StmtIn pSpec δ
  -- Use the explicit finite-table realization.  Under the local `VCVCompatible`
  -- hypotheses this is the intended eager `D_Σ` distribution, but it avoids the
  -- legacy fallback sampler and agrees with the axiom-clean first-bad runner.
  let D_g := D_SigmaFinite (U := U) StmtIn pSpec δ
  exact
    hybridGameDistRevised
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := hybChallengeInit (challengeSpec := challengeSpec) D_g)
      (impl := hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_g)
      (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) V maliciousProver
      (hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 Hyb₂ over the live revised D2SQuery executor.  The decoded-table oracle is lifted only
on its decoder image: a decoded-table cell is sampled as the decoding of an encoded cell, so the
partial fibre sampler is always called at a witnessed image point.  This is the Claim 5.22
normal form; only the duplex interpreter differs from the original Figure-4 game. -/
noncomputable def hyb2Revised
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
  let gImpl := d2sDecodedBridgeImplCacheOfImage
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact
    hybridGameDistRevised
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

/-- Expose the concrete game expression underlying revised H₂ without unfolding it through
later coupling goals.  Keeping this one-step definition equality named avoids elaborator-heavy
reduction of the image-fibre bridge at each endpoint transport. -/
theorem hyb2Revised_eq_hybridGameDistRevised
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    hyb2Revised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver =
      letI : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩
      hybridGameDistRevised
        (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (init := hybChallengeInit
          (challengeSpec := eSpec (U := U) StmtIn pSpec δ)
          (D_e (U := U) StmtIn pSpec δ))
        (impl := hybChallengeImpl
          (oSpec := oSpec) (U := U) (challengeSpec := eSpec (U := U) StmtIn pSpec δ)
          oSpecImpl (D_e (U := U) StmtIn pSpec δ))
        (d2sDecodedBridgeImplCacheOfImage
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V maliciousProver
        (hyb2Line4Trace
          (δ := δ) (Salt := Salt)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  rfl

/-- CO25 Hyb₃ over the live revised D2SQuery executor.  Its one-run `D2SAlgoMemo` is shared by
the prover and verifier exactly as in the paper, so repeated encoded keys are reissued and retain
their insertion-trace multiplicity. -/
noncomputable def hyb3Revised
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
  let gImpl := d2sCodecBridgeImplMemo (δ := δ) (Salt := Salt)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact
    hybridGameDistRevised
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

end DuplexSpongeFS.KeyLemma
