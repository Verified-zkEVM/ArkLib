/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.EventsAndAnalysis
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PrefixEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.MonitoredD2SQuery
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Section5Nonempty

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
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
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
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U]
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
    (U : Type) [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
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
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (execution : D2SQueryExecution StmtIn pSpec U δ T_H T_P) : Trace StmtIn U :=
  terminalTrace execution.terminal

/-- A revised D2SQuery execution completes normally exactly when its real three-way terminal
outcome is `.finished`; both `.stopped` and `.underlyingAbort` are excluded. -/
def D2SQueryExecution.completes {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
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

/-- A forward-first normalized pair has its forward representative in the base trace.  This is
the bridge behind the paper's `p.fwdcapoutlu`: its reverse-capacity candidates are charged to
forward permutation answers, rather than to arbitrary inverse-origin table pairs. -/
private lemma forwardFirst_mem_getBaseTrace
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) (sIn sOut : CanonicalSpongeState U)
    (hFirst : Backtrack.ForwardFirst trace sIn sOut) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
      getBaseTrace trace := by
  rcases hFirst with ⟨k, hget, hEarlier⟩
  apply permFwd_mem_getBaseTrace trace hget
  · intro hmem
    rw [List.mem_take_iff_getElem] at hmem
    obtain ⟨j, hj, hEntry⟩ := hmem
    have hjk : j < k := lt_of_lt_of_le hj (Nat.min_le_left _ _)
    have hjLen : j < trace.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    exact (hEarlier j hjk).1 (by
      rw [List.getElem?_eq_getElem hjLen]
      exact congrArg some hEntry)
  · intro hmem
    rw [List.mem_take_iff_getElem] at hmem
    obtain ⟨j, hj, hEntry⟩ := hmem
    have hjk : j < k := lt_of_lt_of_le hj (Nat.min_le_left _ _)
    have hjLen : j < trace.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    exact (hEarlier j hjk).2 (by
      rw [List.getElem?_eq_getElem hjLen]
      exact congrArg some hEntry)

/-- The reusable monitored state supplies exactly the normalized-table invariant needed by the
forward-first BackTrack walk.  Inverse-origin entries need not be reverse-capacity unique; they
are deliberately excluded by `ForwardFirst`. -/
private lemma searchUnambiguous_of_normal
    {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Backtrack.SearchUnambiguous normal.state.trace normal.state.trΔ := by
  constructor
  · rw [← Multiset.coe_nodup, LawfulTraceTable.toMultiSet_ofEntries]
    exact normal.permutationNodup
  constructor
  · rw [← Multiset.coe_nodup, LawfulTraceTable.toMultiSet_ofEntries]
    exact normal.hashNodup
  constructor
  · rintro ⟨sIn₁, sOut₁⟩ hPair₁ ⟨sIn₂, sOut₂⟩ hPair₂ hFirst₁ hFirst₂ hCap
    have hBase₁ := forwardFirst_mem_getBaseTrace normal.state.trace sIn₁ sOut₁ hFirst₁
    have hBase₂ := forwardFirst_mem_getBaseTrace normal.state.trace sIn₂ sOut₂ hFirst₂
    have hEq :
        (⟨.inr (.inl sIn₁), sOut₁⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) =
          ⟨.inr (.inl sIn₂), sOut₂⟩ := by
      apply BadEventDS.eq_of_answerCap_eq normal.state.trace
        (BadEventDS.not_E_dup_of_not_E normal.state.trace normal.monitorPassed) hBase₁ hBase₂
      simpa [BadEventDS.answerCap] using hCap
    exact Prod.ext (BadEventDS.fwdEntry_inj hEq).1 (BadEventDS.fwdEntry_inj hEq).2
  · rintro ⟨stmt₁, cap₁⟩ hPair₁ ⟨stmt₂, cap₂⟩ hPair₂ hCap
    have hRaw₁ : (⟨.inl stmt₁, cap₁⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
        normal.state.trace :=
      (normal.state.h_mirror.1 stmt₁ cap₁).mpr hPair₁
    have hRaw₂ : (⟨.inl stmt₂, cap₂⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
        normal.state.trace :=
      (normal.state.h_mirror.1 stmt₂ cap₂).mpr hPair₂
    have hBase₁ := hash_pair_mem_getBaseTrace_of_mem normal.state.trace hRaw₁
    have hBase₂ := hash_pair_mem_getBaseTrace_of_mem normal.state.trace hRaw₂
    have hEq :
        (⟨.inl stmt₁, cap₁⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) =
          ⟨.inl stmt₂, cap₂⟩ := by
      apply BadEventDS.eq_of_answerCap_eq normal.state.trace
        (BadEventDS.not_E_dup_of_not_E normal.state.trace normal.monitorPassed) hBase₁ hBase₂
      simpa [BadEventDS.answerCap] using hCap
    cases hEq
    rfl

/-- The same monitored state supplies LookAhead's simpler forward-search invariant: table input
functionality gives one successor per full input, and `¬E_dup` rules out a capacity self-loop for
either a forward- or inverse-origin normalized pair. -/
private lemma lookaheadSearchUnambiguous_of_normal
    {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Lookahead.SearchUnambiguous normal.state.trΔ.p := by
  constructor
  · rw [← Multiset.coe_nodup, LawfulTraceTable.toMultiSet_ofEntries]
    exact normal.permutationNodup
  constructor
  · exact normal.table_inputFunctional
  · rintro ⟨sIn, sOut⟩ hPair
    have hRaw :
        (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          normal.state.trace ∨
        ⟨.inr (.inr sOut), sIn⟩ ∈ normal.state.trace :=
      (normal.state.h_mirror.2 sIn sOut).mpr hPair
    rcases normalizedPermPair_mem_getBaseTrace_of_mem normal.state.trace sIn sOut hRaw with
      hBase | hBase
    · obtain ⟨j, hGet⟩ := List.mem_iff_getElem?.mp hBase
      obtain ⟨hj, hEntry⟩ := List.getElem?_eq_some_iff.mp hGet
      have hEntryFin : List.get (getBaseTrace normal.state.trace) ⟨j, hj⟩ =
          (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        simpa only [List.get_eq_getElem] using hEntry
      have hQueryCap : BadEventDS.queryCap
          (List.get (getBaseTrace normal.state.trace) ⟨j, hj⟩) =
          some sIn.capacitySegment := by
        rw [hEntryFin]
        rfl
      have hNe := BadEventDS.answerCap_ne_queryCap_le normal.state.trace
        (BadEventDS.not_E_dup_of_not_E normal.state.trace normal.monitorPassed)
        (i := ⟨j, hj⟩) (j := ⟨j, hj⟩) le_rfl (c := sIn.capacitySegment) hQueryCap
      change BadEventDS.answerCap (List.get (getBaseTrace normal.state.trace) ⟨j, hj⟩) ≠
        sIn.capacitySegment at hNe
      rw [hEntryFin] at hNe
      simpa [BadEventDS.answerCap] using hNe.symm
    · obtain ⟨j, hGet⟩ := List.mem_iff_getElem?.mp hBase
      obtain ⟨hj, hEntry⟩ := List.getElem?_eq_some_iff.mp hGet
      have hEntryFin : List.get (getBaseTrace normal.state.trace) ⟨j, hj⟩ =
          (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        simpa only [List.get_eq_getElem] using hEntry
      have hQueryCap : BadEventDS.queryCap
          (List.get (getBaseTrace normal.state.trace) ⟨j, hj⟩) =
          some sOut.capacitySegment := by
        rw [hEntryFin]
        rfl
      have hNe := BadEventDS.answerCap_ne_queryCap_le normal.state.trace
        (BadEventDS.not_E_dup_of_not_E normal.state.trace normal.monitorPassed)
        (i := ⟨j, hj⟩) (j := ⟨j, hj⟩) le_rfl (c := sOut.capacitySegment) hQueryCap
      change BadEventDS.answerCap (List.get (getBaseTrace normal.state.trace) ⟨j, hj⟩) ≠
        sOut.capacitySegment at hNe
      rw [hEntryFin] at hNe
      simpa [BadEventDS.answerCap] using hNe

/-- A `StdTrace.Run` that is supplied with an `E`-good complete raw trace cannot take one of its
conflict branches.  The proof is a structural induction over the input stream: every continuing
branch appends exactly its current occurrence, while a conflict exposes `E` on that prefix; raw
prefix monotonicity transports the latter witness to the complete input, contradicting goodness.
This is the deterministic core of revised Lemma 5.17. -/
private lemma stdTrace_run_insertionTrace_eq_of_not_E
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
    (pre final : StdTrace.View StmtIn U)
    (stream : List (StdTrace.RawOccurrence StmtIn U))
    (hRun : StdTrace.Run pre stream final)
    (hGood : ¬ BadEvent (pre.insertionTrace ++ stream)) :
    final.insertionTrace = pre.insertionTrace ++ stream := by
  induction stream generalizing pre final with
  | nil =>
      simp only [StdTrace.Run] at hRun
      rcases hRun with ⟨_, rfl⟩
      simp
  | cons occurrence rest ih =>
      rcases occurrence with ⟨query, answer⟩
      cases query with
      | inl hashQuery =>
          simp only [StdTrace.Run] at hRun
          rcases hRun with ⟨_, hRun⟩
          rcases hRun with hContinue | hConflict
          · rcases hContinue with ⟨post, hTrace, _, _, hPostGood, _, hRest⟩
            have hRestGood : ¬ BadEvent (post.insertionTrace ++ rest) := by
              simpa only [hTrace, List.append_assoc] using hGood
            have hFinal := ih post final hRest hRestGood
            simpa only [hTrace, List.append_assoc] using hFinal
          · rcases hConflict with ⟨hTrace, _, _, hBad, _⟩
            exfalso
            apply hGood
            apply BadEventDS.E_mono_of_raw_prefix
              (trace := final.insertionTrace)
              (trace' := pre.insertionTrace ++ ⟨.inl hashQuery, answer⟩ :: rest)
            · simpa only [hTrace, List.append_assoc] using
                (List.prefix_append final.insertionTrace rest)
            · exact hBad
      | inr permutationQuery =>
          cases permutationQuery with
          | inl stateIn =>
              simp only [StdTrace.Run] at hRun
              rcases hRun with ⟨_, hRun⟩
              rcases hRun with hContinue | hConflict
              · rcases hContinue with ⟨post, _, hStep, hRest⟩
                have hTrace := hStep.2.2.2.1
                have hRestGood : ¬ BadEvent (post.insertionTrace ++ rest) := by
                  simpa only [hTrace, List.append_assoc] using hGood
                have hFinal := ih post final hRest hRestGood
                simpa only [hTrace, List.append_assoc] using hFinal
              · rcases hConflict with ⟨post, _, hStep, _⟩
                exfalso
                apply hGood
                apply BadEventDS.E_mono_of_raw_prefix
                  (trace := post.insertionTrace)
                  (trace' := pre.insertionTrace ++ ⟨.inr (.inl stateIn), answer⟩ :: rest)
                · have hTrace := hStep.2.2.2.1
                  simpa only [hTrace, List.append_assoc] using
                    (List.prefix_append post.insertionTrace rest)
                · exact hStep.2.2.2.2
          | inr stateOut =>
              simp only [StdTrace.Run] at hRun
              rcases hRun with ⟨_, hRun⟩
              rcases hRun with hContinue | hConflict
              · rcases hContinue with ⟨post, _, hStep, hRest⟩
                have hTrace := hStep.2.2.2.1
                have hRestGood : ¬ BadEvent (post.insertionTrace ++ rest) := by
                  simpa only [hTrace, List.append_assoc] using hGood
                have hFinal := ih post final hRest hRestGood
                simpa only [hTrace, List.append_assoc] using hFinal
              · rcases hConflict with ⟨post, _, hStep, _⟩
                exfalso
                apply hGood
                apply BadEventDS.E_mono_of_raw_prefix
                  (trace := post.insertionTrace)
                  (trace' := pre.insertionTrace ++ ⟨.inr (.inr stateOut), answer⟩ :: rest)
                · have hTrace := hStep.2.2.2.1
                  simpa only [hTrace, List.append_assoc] using
                    (List.prefix_append post.insertionTrace rest)
                · exact hStep.2.2.2.2

/-- **Claim 5.19 (revised).** The real stateful Backtrack call is made only from a reusable
monitored D2S state.  Its exact mirrored normalized table, together with `Monitor`'s `¬E`
invariant, makes each forward-first reverse lookup and each hash-anchor lookup unambiguous; the
search therefore cannot return `.err`.  This deliberately does not rebuild a table with
`TraceNabla.ofQueryLog`: that raw fold retains harmless duplicate occurrences and is not the
live table on which the algorithm runs. -/
theorem claim_5_19_backTrack_noAbort
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec]
    [HasChallengeSize pSpec] {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    [codec : CodecCore pSpec U] [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (state : CanonicalSpongeState U) :
    Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ) normal.state.trace
      normal.state.trΔ normal.state.h_inv state ≠
      ExperimentOutput.err := by
  apply Backtrack.backTrack_ne_err_of_searchUnambiguous
  exact searchUnambiguous_of_normal normal

/-- **Claim 5.20 (revised).** On the full normalized table carried by a reusable D2S state,
LookAhead's computation has no `.err` value in its support.  This is stronger than the marker-only
paper invocation, while correctly retaining the fact that the successful branch is randomized. -/
theorem claim_5_20_lookAhead_noAbort
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec]
    [HasChallengeSize pSpec] {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    [codec : CodecCore pSpec U] [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (round : pSpec.ChallengeIdx) (state : CanonicalSpongeState U) :
    Lookahead.NoErr round
      (Lookahead.lookAhead (pSpec := pSpec) normal.state.trΔ.p state round) := by
  apply Lookahead.lookAhead_noErr_of_searchUnambiguous
  exact lookaheadSearchUnambiguous_of_normal normal

/-- **Lemma 5.17 marker-success bridge.** At a certified nonempty verifier phase, the full
normalized table contains the current forward mapping.  LookAhead therefore has neither of its
two non-success outcomes: Claim 5.20 excludes `.err`, while the present forward mapping excludes
`.noResult`.  This is the exact fact consumed by the live StdTrace replay after Backtrack has
returned a tuple for the current forward occurrence. -/
theorem claim_5_20_lookAhead_support_some_of_forward_mem
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec]
    [HasChallengeSize pSpec] [Section5Nonempty pSpec] {StmtIn U : Type} [SpongeUnit U]
    [SpongeSize] [codec : CodecCore pSpec U] [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (round : pSpec.ChallengeIdx) (stateIn stateOut : CanonicalSpongeState U)
    (hForward : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p)
    (result : ExperimentOutput (Vector U (challengeSize round)))
    (hResult : result ∈ support
      (Lookahead.lookAhead (pSpec := pSpec) normal.state.trΔ.p stateIn round)) :
    ∃ rhoHat, result = .some rhoHat := by
  cases result with
  | err =>
      have hNoErr := claim_5_20_lookAhead_noAbort (pSpec := pSpec) normal round stateIn
      exact False.elim (hNoErr hResult)
  | noResult =>
      have hNoResult := Lookahead.lookAhead_noNoResult_of_forward_mem
        normal.state.trΔ.p stateIn stateOut round
        (Section5Nonempty.challenge_block_count_pos (pSpec := pSpec) round) hForward
      exact False.elim (hNoResult hResult)
  | some rhoHat => exact ⟨rhoHat, rfl⟩

/-- **Corollary 5.20a (revised).** The stateful Backtrack/LookAhead no-abort facts hold at every
actual *reusable monitored state* and every certified Program marker.  A reusable normal state is
the live representation of an `E`-good trace prefix together with its incrementally maintained
normalized tables; rebuilding a table with `TraceNabla.ofQueryLog` would retain duplicate raw
occurrences and is therefore not the state on which D2SQuery calls either search procedure. -/
theorem corollary_5_20a_revisedD2SNoAbort
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec]
    [HasChallengeSize pSpec] [codec : CodecCore pSpec U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (context : D2SQuery.ProgramContext pSpec) :
    RevisedD2SNoAbort (δ := δ) normal.state.trace normal.state.trΔ normal.state.h_inv context := by
  intro _
  constructor
  · intro state
    exact claim_5_19_backTrack_noAbort (pSpec := pSpec) normal state
  · intro state _ hEq
    have hNoErr := claim_5_20_lookAhead_noAbort (pSpec := pSpec) normal context.round state
    rw [hEq] at hNoErr
    simpa [Lookahead.NoErr] using hNoErr

/-- **Lemma 5.17 (revised).** If the full input trace is free of the combined bad event, then
corrected StdTrace consumes the whole input stream and returns a normal completed view. -/
theorem lemma_5_17_stdTrace_noAbort
    {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
    (execution : StdTraceExecution StmtIn U) (hE : ¬ BadEvent execution.trace) :
    execution.completes := by
  refine ⟨execution.run, ?_⟩
  apply stdTrace_run_insertionTrace_eq_of_not_E
    (initialStdTraceView StmtIn U) execution.final execution.stream execution.run
  simpa only [initialStdTraceView, StdTraceExecution.trace, rawTraceOfStream,
    List.nil_append] using hE

/-- A semantic branch witness cannot manufacture the `underlyingAbort` result on a reusable
normal state.  Every ordinary branch rules that result out by its exact `D2SStep` contract; the
sole explicit abort branch is the real Backtrack `.err`, excluded by Claim 5.19. -/
private theorem d2sBranchStep_ne_underlyingAbort
    {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (context : Option (D2SQuery.ProgramContext pSpec))
    (query : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    ¬ D2SQuery.D2SBranchStep normal context query .underlyingAbort := by
  intro hStep
  cases hStep with
  | hash _ h =>
      simpa [D2SQuery.BranchHashQuery] using h
  | inverse _ _ _ _ h =>
      simpa [D2SQuery.BranchInverseQuery, D2SQuery.InverseBranchOutcome] using h
  | tailHit _ _ _ _ _ h =>
      rcases h with ⟨_, _, h⟩
      simpa [D2SQuery.ForwardBranchOutcome] using h
  | tableHit _ _ _ _ h =>
      rcases h with ⟨_, h⟩
      simpa [D2SQuery.ForwardBranchOutcome] using h
  | freshMiss _ _ _ _ h =>
      rcases h with ⟨_, _, h⟩
      simpa [D2SQuery.ForwardBranchOutcome] using h
  | program _ _ _ _ _ _ h =>
      rcases h with ⟨_, _, h | h⟩
      · simpa [D2SQuery.ProgramExistingMapping, D2SQuery.ForwardBranchOutcome] using h
      · rcases h with ⟨_, h⟩
        simpa [D2SQuery.ProgramMaterialization, D2SQuery.ForwardBranchOutcome] using h
  | backtrackAbort state h =>
      rcases h with ⟨state', hAbort⟩
      exact (claim_5_19_backTrack_noAbort (pSpec := pSpec) normal state') hAbort

/-- A whole semantic D2SQuery run whose exposed terminal trace is `E`-good must consume its
complete stream.  A monitor stop carries `E` of precisely that terminal trace, and the only
pre-occurrence abort is ruled out by `d2sBranchStep_ne_underlyingAbort`. -/
private theorem d2sQueryRun_completes_of_terminal_not_E
    {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (stream : D2SQuery.QueryStream StmtIn pSpec U)
    (terminal : D2SQuery.D2SRunTerminal StmtIn pSpec U δ T_H T_P)
    (hRun : D2SQuery.D2SQueryRun normal stream terminal)
    (hE : ¬ BadEvent (terminalTrace terminal)) :
    ∃ finalNormal, terminal = .finished finalNormal := by
  induction stream generalizing normal terminal with
  | nil =>
      cases terminal <;> simp [D2SQuery.D2SQueryRun] at hRun
      · exact ⟨_, rfl⟩
  | cons occurrence rest ih =>
      simp only [D2SQuery.D2SQueryRun] at hRun
      rcases hRun with ⟨result, hStep, hRun⟩
      exact match result with
      | .continue _ newNormal => by
          exact ih newNormal terminal hRun hE
      | .stopped state record => by
          rcases hRun with ⟨_, hTerminal⟩
          subst terminal
          apply False.elim
          apply hE
          simpa [terminalTrace] using record.monitorFails
      | .underlyingAbort => by
          exact (d2sBranchStep_ne_underlyingAbort normal occurrence.programContext
            occurrence.query hStep).elim

/-- **Lemma 5.18 (revised).** For every complete execution of an algorithm using revised
`D2SQuery`, if the execution's resulting trace is free of the combined bad event, then the
execution has the real normal `.finished` terminal outcome. -/
theorem lemma_5_18_d2sQuery_noAbort
    {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
    {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
    [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (execution : D2SQueryExecution StmtIn pSpec U δ T_H T_P)
    (hE : ¬ BadEvent execution.trace) :
    execution.completes := by
  exact d2sQueryRun_completes_of_terminal_not_E execution.initial execution.stream
    execution.terminal execution.run hE

end DuplexSpongeFS.AbortAnalysis
