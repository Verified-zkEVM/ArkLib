/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.EventsAndAnalysis

/-!
# Abort analysis for the revised stateful D2S transformation

This file is the proof-facing home of Section 5.7's abort-analysis theorems for the revised
stateful replay construction.  It deliberately names the current stateful operators and their
actual outcomes:

- Claims 5.19 and 5.20 concern the real `Backtrack.backTrack` and `Lookahead.lookAhead` `.err`
  branches;
- Lemma 5.17 concerns a whole corrected `StdTrace.Run` execution; and
- Lemma 5.18 concerns a whole revised `D2SQueryRun` execution, whose terminal outcome is either
  finished, a monitored stop, or an underlying search abort.

The proofs are intentionally left as explicit obligations while the executable stateful handlers
are refined to these relations.  In particular, this file does not revive the obsolete pre-replay
`d2fRaw`/`d2sTraceSalted` abort model.
-/

namespace DuplexSpongeFS.AbortAnalysis

open OracleComp OracleSpec ProtocolSpec DSTraceStorage
open DuplexSpongeFS.Statement

/-! ## Revised whole-execution completion predicates -/

/-- The trace visible at the terminal outcome of a revised D2SQuery run.  A monitored stop exposes
the stop record's post-occurrence trace; an underlying search abort exposes the unchanged normal
trace at which it occurred. -/
def terminalTrace {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : Codec pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (terminal : D2SQuery.D2SRunTerminal StmtIn pSpec U δ T_H T_P) :
    Trace StmtIn U :=
  match terminal with
  | .finished normal => normal.state.trace
  | .stopped _ record => record.trace
  | .aborted normal => normal.state.trace

/-- The `Program` contexts in a query stream, in the exact order and multiplicity in which revised
D2SQuery invokes the encoded challenge oracle. -/
def programContexts {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : Codec pSpec U]
    (stream : D2SQuery.QueryStream StmtIn pSpec U) : List (D2SQuery.ProgramContext pSpec) :=
  stream.filterMap fun occurrence => occurrence.programContext

/-- One complete semantic execution of an arbitrary algorithm using revised D2SQuery.  Its
`memo` is a total family of encoded functions `gᵢ`; every Program occurrence is represented by
one ordered `ProgramInvocation`, whose `memo_answer` field ties its concrete encoded key and answer
to that very function.  Thus repeated keys are functional while repeated invocations remain in the
list and retain their order/multiplicity.  The genuine fold-style D2SQuery run relates the sponge
occurrences to its terminal outcome.  The later live-executor refinement identifies an `OracleComp`
adversary's query log with this `stream`. -/
structure D2SQueryExecution (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n)
    (U : Type) [SpongeUnit U] [SpongeSize] [codec : Codec pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] where
  initial : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P
  stream : D2SQuery.QueryStream StmtIn pSpec U
  memo : (i : pSpec.ChallengeIdx) →
    (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i)
  programInvocations : List (D2SAlgo.ProgramInvocation (pSpec := pSpec) (U := U) (δ := δ)
    (T_H := T_H) (T_P := T_P) memo)
  program_invocations_are_stream :
    programInvocations.map D2SAlgo.ProgramInvocation.context = programContexts stream
  terminal : D2SQuery.D2SRunTerminal StmtIn pSpec U δ T_H T_P
  run : D2SQuery.D2SQueryRun initial stream terminal

/-- The full trace resulting from a revised D2SQuery execution. -/
abbrev D2SQueryExecution.trace {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : Codec pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (execution : D2SQueryExecution StmtIn pSpec U δ T_H T_P) : Trace StmtIn U :=
  terminalTrace execution.terminal

/-- A revised D2SQuery execution completes normally exactly when its real three-way terminal
outcome is `.finished`; both `.stopped` and `.underlyingAbort` are excluded. -/
def D2SQueryExecution.completes {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : Codec pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (execution : D2SQueryExecution StmtIn pSpec U δ T_H T_P) : Prop :=
  ∃ normal, execution.terminal = .finished normal

/-- The raw query-answer trace represented by an offline StdTrace input stream.  This is just its
insertion order, with every dependent query-answer pair preserved. -/
abbrev rawTraceOfStream {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (stream : List (StdTrace.RawOccurrence StmtIn U)) : Trace StmtIn U :=
  stream

/-- The empty two-table view from which the paper's `StdTrace(tr)` starts. -/
def initialStdTraceView (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : StdTrace.View StmtIn U :=
  ⟨[], [], [], List.nil_prefix⟩

/-- A corrected StdTrace run completes normally exactly when it consumes the whole supplied raw
stream.  This is independent of `E`: the assertion that an `E`-good input has this form is the
substantive content of Lemma 5.17. -/
def StdTraceCompletes {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
    (initial final : StdTrace.View StmtIn U)
    (stream : List (StdTrace.RawOccurrence StmtIn U)) : Prop :=
  StdTrace.Run initial stream final ∧
    final.insertionTrace = initial.insertionTrace ++ rawTraceOfStream stream

/-- One concrete execution of the paper's corrected `StdTrace(tr)`: it starts from the empty
two-table view and processes its entire supplied raw trace through the real whole-trace relation. -/
structure StdTraceExecution (StmtIn U : Type) [SpongeUnit U] [SpongeSize] [DecidableEq U] where
  stream : List (StdTrace.RawOccurrence StmtIn U)
  final : StdTrace.View StmtIn U
  run : StdTrace.Run (initialStdTraceView StmtIn U) stream final

/-- The input trace of a corrected StdTrace execution. -/
abbrev StdTraceExecution.trace {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
    (execution : StdTraceExecution StmtIn U) : Trace StmtIn U :=
  rawTraceOfStream execution.stream

/-- A corrected StdTrace execution completes normally iff its final trace contains every supplied
occurrence, rather than ending at the first monitored conflict. -/
def StdTraceExecution.completes {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
    (execution : StdTraceExecution StmtIn U) : Prop :=
  StdTraceCompletes (initialStdTraceView StmtIn U) execution.final execution.stream

/-! ## Claims 5.19 / 5.20 and Lemmas 5.17 / 5.18 -/

/-- **Claim 5.19 (revised).** Outside the combined bad event, the real stateful Backtrack search
on every state of the current trace cannot return its `.err` outcome. -/
theorem claim_5_19_backTrack_noAbort
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec]
    [HasChallengeSize pSpec]
    (trace : Trace StmtIn U) (state : CanonicalSpongeState U) (hE : ¬ BadEvent trace) :
    Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ) trace
      (TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) trace)
      (TraceNabla.ofQueryLog_isSubset (T_H := T_H) (T_P := T_P) trace) state ≠
      ExperimentOutput.err := by
  sorry

/-- **Claim 5.20 (revised).** Outside the combined bad event, the real LookAhead search cannot
return `.err` at a state and round actually accepted by the canonical Backtrack parser. -/
theorem claim_5_20_lookAhead_noAbort
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec]
    [HasChallengeSize pSpec]
    (trace : Trace StmtIn U) (round : pSpec.ChallengeIdx) (state : CanonicalSpongeState U)
    (hE : ¬ BadEvent trace)
    (hMarker : ∃ out : Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U),
      Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ) trace
        (TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) trace)
        (TraceNabla.ofQueryLog_isSubset (T_H := T_H) (T_P := T_P) trace) state =
          ExperimentOutput.some out ∧ out.roundIdx = round) :
    Lookahead.lookAhead (pSpec := pSpec)
      (TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) trace).p state round ≠
      (pure ExperimentOutput.err : OracleComp (Unit →ₒ U)
        (ExperimentOutput (Vector U (challengeSize round)))) := by
  sorry

/-- **Corollary 5.20a (revised).** The stateful Backtrack/LookAhead no-abort facts hold at every
actual trace prefix and every certified Program marker.  The canonical normalized lookup is rebuilt
from that prefix, rather than supplied as an arbitrary subset table. -/
theorem corollary_5_20a_revisedD2SNoAbort
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec]
    [HasChallengeSize pSpec]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trace : Trace StmtIn U) (hE : ¬ BadEvent trace) :
    ∀ trPrefix : Trace StmtIn U, trPrefix.IsPrefix trace →
      ∀ context : D2SQuery.ProgramContext pSpec,
        RevisedD2SNoAbort (δ := δ) trPrefix
          (TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) trPrefix)
          (TraceNabla.ofQueryLog_isSubset (T_H := T_H) (T_P := T_P) trPrefix) context := by
  sorry

/-- **Lemma 5.17 (revised).** If the full input trace is free of the combined bad event, then
corrected StdTrace consumes the whole input stream and returns a normal completed view. -/
theorem lemma_5_17_stdTrace_noAbort
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
    (execution : StdTraceExecution StmtIn U) (hE : ¬ BadEvent execution.trace) :
    execution.completes := by
  sorry

/-- **Lemma 5.18 (revised).** For every complete execution of an algorithm using revised
`D2SQuery`, if the execution's resulting trace is free of the combined bad event, then the
execution has the real normal `.finished` terminal outcome. -/
theorem lemma_5_18_d2sQuery_noAbort
    {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : Codec pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (execution : D2SQueryExecution StmtIn pSpec U δ T_H T_P)
    (hE : ¬ BadEvent execution.trace) :
    execution.completes := by
  sorry

end DuplexSpongeFS.AbortAnalysis
